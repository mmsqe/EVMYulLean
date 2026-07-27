import EvmYul.Venom.Solvency

/-!
# A complete ERC-20 token, and its verification flow

`EvmYul/Venom/Solvency.lean` already gives the **balance half** of ERC-20 —
`transfer`, `mint`, and the solvency invariant `Σ balances = totalSupply`, with
Vyper-style safe-math preconditions, and conserved *end-to-end* down to the real
`EVM.step` (`EvmYul/Venom/TransferSolvency.lean`).

This file adds the **allowance half** — `approve` / `transferFrom` — in the same
`UInt256` safe-math style, and bundles balances + allowances + supply into a
single `Token` with the standard ERC-20 surface. The verification flow has four
stages:

  1. **Model**  — the allowance map and the three state transitions.
  2. **Spec**   — the safety properties, stated as theorems.
  3. **Proof**  — discharged with tactics; conservation/solvency are *inherited*
                  from `Solvency.lean` because `transferFrom`'s balance effect is
                  literally the existing `transfer` (no re-proof).
  4. **Run**    — a concrete `approve`+`transferFrom` scenario, executed by `#eval`.

No `sorry`; standard axioms only.
-/

namespace EvmYul.Venom

open EvmYul

/-! ## 1. Model — the allowance map

Allowances are a two-key map `owner → spender → amount`, updated with `upd2`
(built from the balance layer's `upd`). -/

/-- Two-key point update of the allowance map. -/
def upd2 (A : UInt256 → UInt256 → UInt256) (o sp v : UInt256) :
    UInt256 → UInt256 → UInt256 :=
  fun x => if x = o then upd (A o) sp v else A x

@[simp] theorem upd2_self (A : UInt256 → UInt256 → UInt256) (o sp v : UInt256) :
    upd2 A o sp v o sp = v := by
  simp [upd2, upd]

theorem upd2_other_owner (A : UInt256 → UInt256 → UInt256) (o sp v x : UInt256)
    (h : x ≠ o) : upd2 A o sp v x = A x := by
  simp [upd2, h]

theorem upd2_other_spender (A : UInt256 → UInt256 → UInt256) (o sp v sp' : UInt256)
    (h : sp' ≠ sp) : upd2 A o sp v o sp' = A o sp' := by
  simp [upd2, upd, h]

/-- Read an allowance. -/
def allowanceOf (A : UInt256 → UInt256 → UInt256) (o sp : UInt256) : UInt256 := A o sp

/-- `approve` sets the allowance `o → sp` to `v` (ERC-20 `approve`). -/
def approve (A : UInt256 → UInt256 → UInt256) (o sp v : UInt256) :
    UInt256 → UInt256 → UInt256 := upd2 A o sp v

/-! ## The bundled token -/

/-- A complete ERC-20 token state: balances, allowances, total supply, and the
finite set of accounts the supply is summed over. -/
structure Token where
  bal    : UInt256 → UInt256
  allow  : UInt256 → UInt256 → UInt256
  supply : UInt256
  accts  : Finset UInt256

namespace Token

/-- The token is **solvent** when its balances sum to the total supply. -/
def Solvent (t : Token) : Prop := EvmYul.Venom.Solvent t.bal t.supply t.accts

/-- `t.allowance o sp` — how much `sp` may pull from `o`. -/
def allowance (t : Token) (o sp : UInt256) : UInt256 := t.allow o sp

/-- ERC-20 `approve`: owner `o` authorizes spender `sp` for `v`. -/
def doApprove (t : Token) (o sp v : UInt256) : Token :=
  { t with allow := approve t.allow o sp v }

/-- ERC-20 `transfer`: `frm` sends `amt` to `dst`, or reverts (`none`) if `frm`
is short or `dst` would overflow. -/
def doTransfer (t : Token) (frm dst amt : UInt256) : Option Token :=
  if amt ≤ t.bal frm ∧ (t.bal dst).toNat + amt.toNat < UInt256.size then
    some { t with bal := transfer t.bal frm dst amt }
  else
    none

/-- ERC-20 `transferFrom`: spender `sp` moves `amt` from `frm` to `dst`,
debiting the allowance `frm → sp`. Reverts unless the balance **and** the
allowance cover `amt` (and `dst` does not overflow). -/
def doTransferFrom (t : Token) (sp frm dst amt : UInt256) : Option Token :=
  if amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
      ∧ (t.bal dst).toNat + amt.toNat < UInt256.size then
    some { t with bal   := transfer t.bal frm dst amt
                , allow := upd2 t.allow frm sp (t.allow frm sp - amt) }
  else
    none

/-! ## 2. Spec + ## 3. Proof -/

/-- **A1 — approve sets the allowance** to exactly `v`. -/
theorem doApprove_allowance (t : Token) (o sp v : UInt256) :
    (t.doApprove o sp v).allowance o sp = v := by
  simp [doApprove, allowance, approve]

/-- **A2 — approve touches no other (owner, spender) pair.** -/
theorem doApprove_frame (t : Token) (o sp v o' sp' : UInt256)
    (h : o' ≠ o ∨ sp' ≠ sp) :
    (t.doApprove o sp v).allowance o' sp' = t.allowance o' sp' := by
  rcases h with h | h
  · simp [doApprove, allowance, approve, upd2_other_owner _ _ _ _ _ h]
  · by_cases ho : o' = o
    · subst ho; simp [doApprove, allowance, approve, upd2_other_spender _ _ _ _ _ h]
    · simp [doApprove, allowance, approve, upd2_other_owner _ _ _ _ _ ho]

/-- **A3 — approve preserves solvency** (it never moves a balance). -/
theorem doApprove_solvent (t : Token) (o sp v : UInt256) (h : t.Solvent) :
    (t.doApprove o sp v).Solvent := h

/-- **B1 — transfer precondition.** A `transfer` succeeds *iff* the sender can
afford it and the recipient does not overflow. -/
theorem doTransfer_isSome_iff (t : Token) (frm dst amt : UInt256) :
    (t.doTransfer frm dst amt).isSome ↔
      (amt ≤ t.bal frm ∧ (t.bal dst).toNat + amt.toNat < UInt256.size) := by
  unfold doTransfer
  by_cases hg : amt ≤ t.bal frm ∧ (t.bal dst).toNat + amt.toNat < UInt256.size <;>
    simp [hg]

/-- **B2 — transfer preserves solvency.** Between two distinct accounts in the
carrier, a successful `transfer` keeps `Σ balances = supply` — inherited from
`transfer_preserves_solvent`. -/
theorem doTransfer_solvent (t t' : Token) (frm dst amt : UInt256)
    (hne : frm ≠ dst) (hfrm : frm ∈ t.accts) (hdst : dst ∈ t.accts)
    (hok : t.doTransfer frm dst amt = some t') (hsol : t.Solvent) :
    t'.Solvent := by
  unfold doTransfer at hok
  by_cases hg : amt ≤ t.bal frm ∧ (t.bal dst).toNat + amt.toNat < UInt256.size
  · rw [if_pos hg] at hok
    injection hok with hok; subst hok
    obtain ⟨hbal, hovf⟩ := hg
    exact transfer_preserves_solvent t.bal frm dst amt t.supply t.accts
      hfrm hdst hne hbal hovf hsol
  · rw [if_neg hg] at hok; exact Option.noConfusion hok

/-- **C1 — transferFrom precondition.** Succeeds *iff* the balance **and** the
allowance cover `amt` (and `dst` does not overflow). -/
theorem doTransferFrom_isSome_iff (t : Token) (sp frm dst amt : UInt256) :
    (t.doTransferFrom sp frm dst amt).isSome ↔
      (amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
        ∧ (t.bal dst).toNat + amt.toNat < UInt256.size) := by
  unfold doTransferFrom
  by_cases hg : amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
      ∧ (t.bal dst).toNat + amt.toNat < UInt256.size <;> simp [hg]

/-- **C2 — the spender's allowance is consumed** by exactly `amt`. -/
theorem doTransferFrom_consumes (t t' : Token) (sp frm dst amt : UInt256)
    (hok : t.doTransferFrom sp frm dst amt = some t') :
    t'.allowance frm sp = t.allow frm sp - amt := by
  unfold doTransferFrom at hok
  by_cases hg : amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
      ∧ (t.bal dst).toNat + amt.toNat < UInt256.size
  · rw [if_pos hg] at hok
    injection hok with hok; subst hok
    show upd2 t.allow frm sp (t.allow frm sp - amt) frm sp = t.allow frm sp - amt
    exact upd2_self _ _ _ _
  · rw [if_neg hg] at hok; exact Option.noConfusion hok

/-- **C3 — transferFrom's balance effect is the verified `transfer`.** Everything
proved about `transfer` (conservation, frame, no self-mint) therefore applies. -/
theorem doTransferFrom_bal (t t' : Token) (sp frm dst amt : UInt256)
    (hok : t.doTransferFrom sp frm dst amt = some t') :
    t'.bal = transfer t.bal frm dst amt := by
  unfold doTransferFrom at hok
  by_cases hg : amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
      ∧ (t.bal dst).toNat + amt.toNat < UInt256.size
  · rw [if_pos hg] at hok; injection hok with hok; subst hok; rfl
  · rw [if_neg hg] at hok; exact Option.noConfusion hok

/-- **C4 — transferFrom preserves solvency** between two distinct accounts —
inherited from `transfer_preserves_solvent` via C3. -/
theorem doTransferFrom_solvent (t t' : Token) (sp frm dst amt : UInt256)
    (hne : frm ≠ dst) (hfrm : frm ∈ t.accts) (hdst : dst ∈ t.accts)
    (hok : t.doTransferFrom sp frm dst amt = some t') (hsol : t.Solvent) :
    t'.Solvent := by
  unfold doTransferFrom at hok
  by_cases hg : amt ≤ t.bal frm ∧ amt ≤ t.allow frm sp
      ∧ (t.bal dst).toNat + amt.toNat < UInt256.size
  · rw [if_pos hg] at hok
    injection hok with hok; subst hok
    obtain ⟨hbal, _, hovf⟩ := hg
    exact transfer_preserves_solvent t.bal frm dst amt t.supply t.accts
      hfrm hdst hne hbal hovf hsol
  · rw [if_neg hg] at hok; exact Option.noConfusion hok

/-! ## 4. Run — a concrete scenario, executed

Alice (addr 1) holds 100; Bob (2) and Carol (3) hold 0; total supply 100 over the
three accounts. Alice approves Carol for 40, Carol pulls 30 from Alice to Bob. -/

def genesis : Token :=
  { bal    := upd (fun _ => UInt256.ofNat 0) (UInt256.ofNat 1) (UInt256.ofNat 100)
  , allow  := fun _ _ => UInt256.ofNat 0
  , supply := UInt256.ofNat 100
  , accts  := {UInt256.ofNat 1, UInt256.ofNat 2, UInt256.ofNat 3} }

/-- The scenario: `approve` then `transferFrom`. -/
def scenario : Option Token :=
  (genesis.doApprove (UInt256.ofNat 1) (UInt256.ofNat 3) (UInt256.ofNat 40)).doTransferFrom
    (UInt256.ofNat 3) (UInt256.ofNat 1) (UInt256.ofNat 2) (UInt256.ofNat 30)

-- balances (Alice, Bob, Carol) = (70, 30, 0); supply invariant 70+30+0 = 100
#eval scenario.map fun t =>
  ((t.bal (UInt256.ofNat 1)).toNat, (t.bal (UInt256.ofNat 2)).toNat, (t.bal (UInt256.ofNat 3)).toNat)
-- Carol's remaining allowance from Alice = 40 - 30 = 10
#eval scenario.map fun t => (t.allow (UInt256.ofNat 1) (UInt256.ofNat 3)).toNat
-- total over the carrier is unchanged
#eval scenario.map fun t =>
  (t.bal (UInt256.ofNat 1)).toNat + (t.bal (UInt256.ofNat 2)).toNat + (t.bal (UInt256.ofNat 3)).toNat

end Token

end EvmYul.Venom

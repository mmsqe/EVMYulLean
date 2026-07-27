import EvmYul.Venom.SlotAbstraction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Balance-sum / solvency invariant

On the abstract balance map `B : address → word` (the `SlotAbstraction`
layer), the total of all balances over a finite address set is conserved by a
`transfer` and tracked by `mint` — i.e. no tokens are silently created or
destroyed, and `Σ balances = totalSupply` is maintained.

To avoid `ℕ` subtraction when value moves, the sum is taken in `ℤ`
(`balSumZ`). The arithmetic preconditions match Vyper's safe-math: a transfer
needs `amt ≤ balance[from]` (no underflow) and `balance[dst] + amt < 2^256`
(no overflow) — exactly the checks Vyper inserts (and that revert otherwise).
`transfer` uses the sequential read-modify-write semantics (the `+=` reads the
balance *after* the `-=`), so a self-transfer is a no-op.

This is the same balance map the `~addr` peephole rewrites the *slots* of, so
the optimization (which preserves the abstract balances, by `orig_opt_agree`)
preserves solvency too. No `sorry`.
-/

namespace EvmYul.Venom
open EvmYul Finset

/-- Total of all balances over a finite address set, in `ℤ`. -/
def balSumZ (B : UInt256 → UInt256) (S : Finset UInt256) : ℤ :=
  ∑ a ∈ S, ((B a).toNat : ℤ)

/-- Updating one balance shifts the total by the signed delta. -/
theorem balSumZ_update (B : UInt256 → UInt256) (S : Finset UInt256)
    (k : UInt256) (hk : k ∈ S) (v : UInt256) :
    balSumZ (upd B k v) S = balSumZ B S - ((B k).toNat : ℤ) + (v.toNat : ℤ) := by
  unfold balSumZ
  rw [← Finset.add_sum_erase S (fun a => ((upd B k v a).toNat : ℤ)) hk,
      ← Finset.add_sum_erase S (fun a => ((B a).toNat : ℤ)) hk]
  have hcong : (∑ a ∈ S.erase k, ((upd B k v a).toNat : ℤ))
             = ∑ a ∈ S.erase k, ((B a).toNat : ℤ) :=
    Finset.sum_congr rfl (fun a ha => by rw [upd_other B k v a (Finset.ne_of_mem_erase ha)])
  rw [hcong]
  simp only [upd_self]
  ring

/-! ## Transfer — conservation -/

/-- A `transfer` of `amt` from `frm` to `dst`, read-modify-write
(safe-math): subtract from `frm`, then add to `dst` reading the updated map. -/
def transfer (B : UInt256 → UInt256) (frm dst amt : UInt256) : UInt256 → UInt256 :=
  upd (upd B frm (B frm - amt)) dst ((upd B frm (B frm - amt)) dst + amt)

/-- **Conservation.** A `transfer` between distinct parties preserves the total
balance over any finite set containing both — no tokens are created or
destroyed — under safe-math preconditions. -/
theorem balSumZ_transfer (B : UInt256 → UInt256) (frm dst amt : UInt256)
    (S : Finset UInt256) (hfrm : frm ∈ S) (hdst : dst ∈ S) (hne : frm ≠ dst)
    (hbal : amt ≤ B frm)
    (hovf : (B dst).toNat + amt.toNat < UInt256.size) :
    balSumZ (transfer B frm dst amt) S = balSumZ B S := by
  have hbal' : amt.toNat ≤ (B frm).toNat := hbal
  have hB1 : (upd B frm (B frm - amt)) dst = B dst :=
    upd_other B frm (B frm - amt) dst (Ne.symm hne)
  unfold transfer
  rw [balSumZ_update _ S dst hdst, hB1, balSumZ_update _ S frm hfrm,
      UInt256.sub_toNat_of_le hbal, UInt256.add_toNat_of_lt hovf]
  push_cast [Nat.cast_sub hbal']
  ring

/-- A `transfer` to oneself is a no-op (so the total is trivially conserved). -/
theorem transfer_self (B : UInt256 → UInt256) (a amt : UInt256) (hbal : amt ≤ B a) :
    transfer B a a amt = B := by
  funext x
  unfold transfer upd
  by_cases hx : x = a
  · subst hx
    simp only [↓reduceIte]
    exact UInt256.sub_add_cancel_of_le hbal
  · simp [hx]

/-! ## Mint — supply tracking & solvency -/

/-- `mint` adds `amt` to `dst`'s balance. -/
def mint (B : UInt256 → UInt256) (dst amt : UInt256) : UInt256 → UInt256 :=
  upd B dst (B dst + amt)

/-- `mint` increases the total balance by exactly `amt`. -/
theorem balSumZ_mint (B : UInt256 → UInt256) (dst amt : UInt256) (S : Finset UInt256)
    (hdst : dst ∈ S) (hovf : (B dst).toNat + amt.toNat < UInt256.size) :
    balSumZ (mint B dst amt) S = balSumZ B S + (amt.toNat : ℤ) := by
  unfold mint
  rw [balSumZ_update _ S dst hdst, UInt256.add_toNat_of_lt hovf]
  push_cast
  ring

/-- The contract is **solvent** when the tracked balances sum to the total
supply. -/
def Solvent (B : UInt256 → UInt256) (ts : UInt256) (S : Finset UInt256) : Prop :=
  balSumZ B S = (ts.toNat : ℤ)

/-- `transfer` preserves solvency (total supply unchanged). -/
theorem transfer_preserves_solvent (B : UInt256 → UInt256) (frm dst amt ts : UInt256)
    (S : Finset UInt256) (hfrm : frm ∈ S) (hdst : dst ∈ S) (hne : frm ≠ dst)
    (hbal : amt ≤ B frm) (hovf : (B dst).toNat + amt.toNat < UInt256.size)
    (h : Solvent B ts S) :
    Solvent (transfer B frm dst amt) ts S := by
  unfold Solvent at *
  rw [balSumZ_transfer B frm dst amt S hfrm hdst hne hbal hovf]; exact h

/-- `mint` preserves solvency when the total supply is bumped by the same
`amt`. -/
theorem mint_preserves_solvent (B : UInt256 → UInt256) (dst amt ts : UInt256)
    (S : Finset UInt256) (hdst : dst ∈ S) (hovf : (B dst).toNat + amt.toNat < UInt256.size)
    (hts : ts.toNat + amt.toNat < UInt256.size) (h : Solvent B ts S) :
    Solvent (mint B dst amt) (ts + amt) S := by
  unfold Solvent at *
  rw [balSumZ_mint B dst amt S hdst hovf, h, UInt256.add_toNat_of_lt hts]
  push_cast
  ring

end EvmYul.Venom

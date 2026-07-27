import EvmYul.Data.RBMap
import EvmYul.Data.RBMap.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List

import EvmYul.Maps.AccountMap
import EvmYul.State.Account

/-!
# `AccountMap` projections

Upstream projection operators so frame lemmas can speak about balance and
code in a single uniform way. `balanceOf` returns 0 for absent accounts;
`codeOf` returns `.empty`.

Also ships the one build-block we need everywhere: `find?_insert_ne`.
Fold-erase and increaseBalance-frame lemmas live downstream for now.
-/

namespace EvmYul
namespace Frame

open Batteries

/-- `ℕ`-valued balance lookup. Returns `0` for unknown accounts. -/
def balanceOf {τ} (σ : AccountMap τ) (a : AccountAddress) : ℕ :=
  (σ.find? a).elim 0 (·.balance.toNat)

/-- Code lookup (EVM only). Returns `.empty` for unknown accounts. -/
def codeOf (σ : AccountMap .EVM) (a : AccountAddress) : ByteArray :=
  (σ.find? a).elim .empty (·.code)

/-- If two maps agree on `find? a`, they agree on `balanceOf a`. -/
theorem balanceOf_of_find?_eq
    {τ} {σ σ' : AccountMap τ} {a : AccountAddress}
    (h : σ'.find? a = σ.find? a) :
    balanceOf σ' a = balanceOf σ a := by
  unfold balanceOf; rw [h]

/-- If two maps agree on `find? a`, they agree on `codeOf a`. -/
theorem codeOf_of_find?_eq
    {σ σ' : AccountMap .EVM} {a : AccountAddress}
    (h : σ'.find? a = σ.find? a) :
    codeOf σ' a = codeOf σ a := by
  unfold codeOf; rw [h]

/-- Inserting at `k ≠ a` leaves `σ.find? a` unchanged. -/
theorem find?_insert_ne
    {τ} (σ : AccountMap τ) (k a : AccountAddress) (acc : Account τ)
    (hne : k ≠ a) :
    (σ.insert k acc).find? a = σ.find? a := by
  have hcmp : compare a k ≠ .eq := by
    intro h
    exact hne (Std.LawfulEqCmp.compare_eq_iff_eq.mp h).symm
  exact RBMap.find?_insert_of_ne σ hcmp

/-- Inserting at `k = a` yields `find? a = some acc`. -/
theorem find?_insert_self
    {τ} (σ : AccountMap τ) (a : AccountAddress) (acc : Account τ) :
    (σ.insert a acc).find? a = some acc := by
  exact RBMap.find?_insert_of_eq σ Std.ReflCmp.compare_self

/-! ## Real-world well-formedness predicate (T1)

`StateWF σ` bundles the real-world ETH-supply bound:

  `totalETH σ < UInt256.size`

In practice ETH supply is ≈ 2^87 wei, so the 2^256 headroom is vast.
Maintained by Υ: gas-burn, beneficiary-credit and same-tx
SELFDESTRUCT-to-self only decrease totalETH; value-transfers are net
zero. Clients thread `hWF : StateWF σ` through every frame lemma.

From `StateWF` we derive the key consequence for the balance frame
proofs: the sum of any two accounts' balances fits in `UInt256.size`,
so `σ[a].balance + σ[b].balance` doesn't wrap.
-/

/-- Sum of balances across all accounts, in ℕ. -/
def totalETH (σ : AccountMap .EVM) : ℕ :=
  σ.foldl (fun acc _ v => acc + v.balance.toNat) 0

/-- Real-world well-formedness: total ETH supply is bounded below
half of `UInt256.size`.

The `< 2^255` (vs the naïve `< 2^256`) is still real-world valid —
ETH supply is ≈ 120M ETH ≈ 2^87 wei, many orders of magnitude below
2^255. The half-bound is needed to handle self-call (r = s = codeOwner)
no-wrap: `σ[s].balance + v ≤ 2·σ[s].balance ≤ 2·totalETH < 2^256`.

For consumers wanting only `< 2^256`, we provide `boundedTotal'` as a
weaker form derived from `boundedTotal`. -/
structure StateWF (σ : AccountMap .EVM) : Prop where
  boundedTotal : totalETH σ < UInt256.size / 2

/-- Weaker form of `boundedTotal`: the sum is below `UInt256.size` —
trivially derived. Used by most frame-lemma consumers that only need
the full-width bound. -/
theorem StateWF.boundedTotal' {σ : AccountMap .EVM} (h : StateWF σ) :
    totalETH σ < UInt256.size :=
  Nat.lt_of_lt_of_le h.boundedTotal (Nat.div_le_self _ _)

/-- Double-bound: `2·totalETH σ < UInt256.size`. Used for self-call
no-wrap reasoning. -/
theorem StateWF.boundedTotalDouble {σ : AccountMap .EVM} (h : StateWF σ) :
    2 * totalETH σ < UInt256.size := by
  have := h.boundedTotal
  have hUsize : (2 : ℕ) ∣ UInt256.size := by decide
  calc 2 * totalETH σ
      < 2 * (UInt256.size / 2) := by omega
    _ = UInt256.size := by
        rw [Nat.mul_div_cancel' hUsize]

/-! ## `totalETH` membership bounds

These connect `totalETH σ` to individual balances. Both are standard
RBMap-fold lemmas — parallel to `EvmSmith/Lemmas/RBMapSum.lean`'s
`findD_toNat_le_totalBalance`. We keep the machinery self-contained
here (EvmYul can't depend on EvmSmith) but the proof strategy is the
same: reduce `foldl` to `List.sum` over `toList`, then apply
list-membership bounds. -/

/-- Fold ↔ `List.sum` bridge for `totalETH`. -/
private theorem totalETH_eq_sum (σ : AccountMap .EVM) :
    totalETH σ = (σ.toList.map (fun p => p.2.balance.toNat)).sum := by
  show σ.foldl (fun acc _k v => acc + v.balance.toNat) 0
     = (σ.toList.map (fun p => p.2.balance.toNat)).sum
  rw [RBMap.foldl_eq_foldl_toList]
  generalize σ.toList = L
  clear σ
  suffices h : ∀ (init : ℕ),
      L.foldl (fun init p => init + p.2.balance.toNat) init
        = init + (L.map (fun p => p.2.balance.toNat)).sum by
    simpa using h 0
  intro init
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- If `σ.find? a = some acc`, then some pair `(a', acc)` with
`compare a a' = .eq` is an element of `σ.toList`. -/
private theorem find?_some_mem_toList_pair
    (σ : AccountMap .EVM) (a : AccountAddress) (acc : Account .EVM)
    (h : σ.find? a = some acc) :
    ∃ a', (a', acc) ∈ σ.toList ∧ compare a a' = .eq :=
  RBMap.find?_some_mem_toList h

/-- Any single account's balance is at most `totalETH`. -/
theorem balance_toNat_le_totalETH
    (σ : AccountMap .EVM) (a : AccountAddress) (acc : Account .EVM)
    (h : σ.find? a = some acc) :
    acc.balance.toNat ≤ totalETH σ := by
  obtain ⟨a', hMem, _⟩ := find?_some_mem_toList_pair σ a acc h
  rw [totalETH_eq_sum]
  -- `acc.balance.toNat = ((a', acc).2.balance.toNat)` is in the mapped list
  have hIn : acc.balance.toNat ∈ σ.toList.map (fun p => p.2.balance.toNat) :=
    List.mem_map.mpr ⟨(a', acc), hMem, rfl⟩
  exact List.le_sum_of_mem hIn

/-- Sum of any two distinct accounts' balances is at most `totalETH`.

We split `σ.toList` around the first key. Since `a ≠ b`, the second
key's entry is distinct from the first, so it still appears in the
remainder `L ++ R`; its balance therefore fits inside the sum of the
remainder, and the full list-sum is the remainder's sum plus the
first account's balance. -/
theorem balance_pair_toNat_le_totalETH
    (σ : AccountMap .EVM) (a b : AccountAddress) (σa σb : Account .EVM)
    (ha : σ.find? a = some σa) (hb : σ.find? b = some σb) (hab : a ≠ b) :
    σa.balance.toNat + σb.balance.toNat ≤ totalETH σ := by
  -- Get witnesses in toList with compare-eq.
  obtain ⟨a', haMem, haEq⟩ := find?_some_mem_toList_pair σ a σa ha
  obtain ⟨b', hbMem, hbEq⟩ := find?_some_mem_toList_pair σ b σb hb
  -- Since `compare` on AccountAddress is LawfulEq, `a = a'` and `b = b'`.
  have haEq' : a = a' := Std.LawfulEqCmp.compare_eq_iff_eq.mp haEq
  have hbEq' : b = b' := Std.LawfulEqCmp.compare_eq_iff_eq.mp hbEq
  subst haEq'
  subst hbEq'
  -- `(a, σa)` and `(b, σb)` both ∈ toList; they're distinct because a ≠ b.
  have hneq : (a, σa) ≠ (b, σb) := by
    intro hEq
    have : a = b := by
      have := congrArg Prod.fst hEq
      simpa using this
    exact hab this
  -- Split toList at the position of `(a, σa)`.
  obtain ⟨L, R, hSplit⟩ := List.append_of_mem haMem
  -- `(b, σb)` must be in `L ++ R`: if it were equal to `(a, σa)` in
  -- the middle, we'd have `a = b`, contradicting `hab`.
  have hbMem' : (b, σb) ∈ L ++ R := by
    have hbIn : (b, σb) ∈ L ++ (a, σa) :: R := by rw [← hSplit]; exact hbMem
    rcases List.mem_append.mp hbIn with hL | hR
    · exact List.mem_append_left _ hL
    · rcases List.mem_cons.mp hR with heq | hR'
      · exact absurd heq.symm hneq
      · exact List.mem_append_right _ hR'
  -- Sum-decompose: `totalETH σ = Σ_L + σa.balance + Σ_R ≥ σa.balance + σb.balance`.
  rw [totalETH_eq_sum, hSplit]
  have hbIn :
      σb.balance.toNat ∈ (L ++ R).map (fun p => p.2.balance.toNat) :=
    List.mem_map.mpr ⟨(b, σb), hbMem', rfl⟩
  have hb_le : σb.balance.toNat ≤ ((L ++ R).map (fun p => p.2.balance.toNat)).sum :=
    List.le_sum_of_mem hbIn
  -- Compute: sum of mapped `L ++ (a, σa) :: R` = sum_L + σa.balance + sum_R
  --                                            = sum_(L++R) + σa.balance
  have hsum :
      ((L ++ (a, σa) :: R).map (fun p => p.2.balance.toNat)).sum
        = ((L ++ R).map (fun p => p.2.balance.toNat)).sum + σa.balance.toNat := by
    simp [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  rw [hsum]
  omega

/-! ## No-wrap lemmas derived from `StateWF` -/

/-- Single-account no-wrap: any one balance is `< UInt256.size`. -/
theorem no_wrap_one
    (σ : AccountMap .EVM) (hWF : StateWF σ)
    (a : AccountAddress) (acc : Account .EVM) (h : σ.find? a = some acc) :
    acc.balance.toNat < UInt256.size :=
  Nat.lt_of_le_of_lt (balance_toNat_le_totalETH σ a acc h) hWF.boundedTotal'

/-- Two-account no-wrap: sum of any two distinct balances is `< UInt256.size`. -/
theorem no_wrap_pair
    (σ : AccountMap .EVM) (hWF : StateWF σ)
    (a b : AccountAddress) (σa σb : Account .EVM)
    (ha : σ.find? a = some σa) (hb : σ.find? b = some σb) (hab : a ≠ b) :
    σa.balance.toNat + σb.balance.toNat < UInt256.size :=
  Nat.lt_of_le_of_lt (balance_pair_toNat_le_totalETH σ a b σa σb ha hb hab)
    hWF.boundedTotal'

/-- Helper: UInt256 addition agrees with ℕ addition under no-wrap. -/
theorem UInt256_add_toNat_of_no_wrap
    (x y : UInt256) (hNoWrap : x.toNat + y.toNat < UInt256.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  show ((x.val + y.val : Fin _)).val = _
  rw [Fin.val_add]
  apply Nat.mod_eq_of_lt
  show x.val.val + y.val.val < UInt256.size
  have h1 : x.val.val = x.toNat := rfl
  have h2 : y.val.val = y.toNat := rfl
  rw [h1, h2]; exact hNoWrap

/-- StateWF is preserved under accountMap equality. -/
theorem StateWF_of_accountMap_eq
    {σ σ' : AccountMap .EVM} (h : σ' = σ) (hWF : StateWF σ) :
    StateWF σ' := h ▸ hWF

end Frame
end EvmYul

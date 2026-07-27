import EvmYul.Venom.BalanceSlot

/-!
# No-aliasing safety of the `~addr` balance slot (Lean level)

The peephole replaces the balance slot `keccak256(slot ++ addr)` with
`UInt256.lnot addr` (`~addr`). For that to be sound, the opt-side slot
function must be **injective** (distinct addresses ⇒ distinct slots, so no
two users alias) and its image must **avoid the contract's named low slots**
(`owner`, `totalSupply`, …) — otherwise a small-address user's balance would
collide with named state.

Both were previously checked only at the test level (pydefi / Foundry
no-aliasing invariants, and the corpus sweep's `0x01/0x02/0x04` probes). Here
they are *proved*:

* `UInt256.lnot_injective` — `~` is injective (ported from the evm-smith
  demo's `EvmSmith.Lemmas.UInt256Order`).
* `distinct_addresses_distinct_opt_slots` — the corollary for the demo.
* `lnot_above_named_slot` — `~addr` for a 160-bit address never equals a
  named slot below `2^256 - 2^160`, so the low named slots are safe.

No `sorry`.
-/

namespace EvmYul.UInt256

open EvmYul (UInt256)

/-- `(ofNat (size - 1)).toNat = size - 1`. -/
private lemma ofNat_size_pred_toNat :
    (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
  show (UInt256.size - 1) % UInt256.size = UInt256.size - 1
  apply Nat.mod_eq_of_lt
  unfold UInt256.size; omega

/-- Every value is `≤ ofNat (size - 1)` (the max representable). -/
private lemma le_ofNat_size_pred (a : UInt256) :
    a ≤ UInt256.ofNat (UInt256.size - 1) := by
  show a.val.val ≤ (UInt256.ofNat (UInt256.size - 1)).val.val
  rw [show (UInt256.ofNat (UInt256.size - 1)).val.val = UInt256.size - 1
        from ofNat_size_pred_toNat]
  exact Nat.le_sub_one_of_lt a.val.isLt

/-- `(a - b).toNat = a.toNat - b.toNat` when `b ≤ a` (no underflow). -/
theorem sub_toNat_of_le {a b : UInt256} (h : b ≤ a) :
    (a - b).toNat = a.toNat - b.toNat := by
  show ((a.val - b.val : Fin _)).val = a.val.val - b.val.val
  exact Fin.sub_val_of_le h

/-- `(a + b).toNat = a.toNat + b.toNat` when the sum stays below `2^256`
(no overflow). -/
theorem add_toNat_of_lt {a b : UInt256} (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  show ((a.val + b.val : Fin _)).val = a.val.val + b.val.val
  rw [Fin.val_add]
  exact Nat.mod_eq_of_lt h

/-- Subtraction round-trip: `a - b + b = a` when `b ≤ a`. -/
theorem sub_add_cancel_of_le {a b : UInt256} (h : b ≤ a) : a - b + b = a := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  show (⟨(a - b) + b⟩ : UInt256) = ⟨a⟩
  congr 1
  apply Fin.eq_of_val_eq
  show ((a - b) + b).val = a.val
  rw [Fin.val_add, Fin.sub_val_of_le h, Nat.sub_add_cancel h, Nat.mod_eq_of_lt a.isLt]

/-- `(lnot a).toNat = size - 1 - a.toNat`. -/
theorem lnot_toNat (a : UInt256) :
    (UInt256.lnot a).toNat = UInt256.size - 1 - a.toNat := by
  show (UInt256.ofNat (UInt256.size - 1) - a).toNat = UInt256.size - 1 - a.toNat
  rw [sub_toNat_of_le (le_ofNat_size_pred a), ofNat_size_pred_toNat]

/-- `lnot` is injective: distinct 256-bit values get distinct complements. -/
theorem lnot_injective : Function.Injective (UInt256.lnot) := by
  intro a b h
  have h_toNat : (UInt256.lnot a).toNat = (UInt256.lnot b).toNat := congrArg UInt256.toNat h
  rw [lnot_toNat, lnot_toNat] at h_toNat
  have ha : a.toNat < UInt256.size := a.val.isLt
  have hb : b.toNat < UInt256.size := b.val.isLt
  have h_eq : a.toNat = b.toNat := by omega
  obtain ⟨⟨av, hav⟩⟩ := a
  obtain ⟨⟨bv, hbv⟩⟩ := b
  congr 1
  exact Fin.ext h_eq

/-- `~addr` for a 160-bit address lands at or above `2^256 - 2^160`, so it
never collides with a named slot below that bound (in particular every low
named slot like `owner@1`, `totalSupply@4`). -/
theorem lnot_above_named_slot (addr slot : UInt256)
    (haddr : addr.toNat < 2 ^ 160)
    (hslot : slot.toNat < UInt256.size - 2 ^ 160) :
    UInt256.lnot addr ≠ slot := by
  intro habs
  have h := congrArg UInt256.toNat habs
  rw [lnot_toNat] at h
  have hsz : (2 : ℕ) ^ 160 < UInt256.size := by unfold UInt256.size; omega
  omega

end EvmYul.UInt256

namespace EvmYul.Venom

open EvmYul

/-- **No aliasing.** Distinct addresses map to distinct `~addr` balance
slots — the soundness condition for the peephole (so two users never share a
slot). -/
theorem distinct_addresses_distinct_opt_slots {a b : UInt256} (hne : a ≠ b) :
    UInt256.lnot a ≠ UInt256.lnot b :=
  fun habs => hne (UInt256.lnot_injective habs)

end EvmYul.Venom

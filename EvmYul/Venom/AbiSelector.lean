import EvmYul.Venom.Asm
import EvmYul.Venom.AbiBridge

/-!
# Venom IR — ABI selector-extraction bridge

The dispatch-key half of the ABI calldata decode (companion to
`AbiBridge`'s arg-decode bridge). A real dispatcher reads the 4-byte
selector with `shr 224 (calldataload 0)`; this proves that recovers the
selector from calldata `selectorBytes sel ++ args`, with no dependence on
`keccak256` (opaque; its *value* is covered by `scripts/abi_crossval.sh`).

Together with `AbiBridge.calldataload_transfer_*`, this closes the calldata
*decode* side of the ABI interface (selector + arguments), and supplies the
`selVar = sel` fact the dispatch routing (`AbiDispatch`) consumes.
-/

set_option maxRecDepth 4000

namespace EvmYul

open EvmYul

/-! ## Byte-list arithmetic -/

/-- The little-endian value of a byte list is bounded by its bit width. -/
theorem fromBytes'_lt (bs : List UInt8) : fromBytes' bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [fromBytes']
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub (Nat.one_le_pow _ _ (by decide)) (Nat.le_sub_one_of_lt ih)
    linarith

/-- Splitting a little-endian value at an append point. -/
theorem fromBytes'_append (a b : List UInt8) :
    fromBytes' (a ++ b) = fromBytes' a + 2 ^ (8 * a.length) * fromBytes' b := by
  induction a with
  | nil => simp [fromBytes']
  | cons x xs ih =>
    simp only [List.cons_append, fromBytes', ih, List.length_cons, Nat.mul_succ, Nat.pow_add]
    ring

/-- Big-endian value is bounded by its bit width. -/
theorem fromBytesBigEndian_lt (bs : List UInt8) : fromBytesBigEndian bs < 2 ^ (8 * bs.length) := by
  unfold fromBytesBigEndian
  simpa [Function.comp, List.length_reverse] using fromBytes'_lt bs.reverse

/-- Splitting a big-endian value at an append point: the high part `hi`
carries a factor of `2 ^ (8 * lo.length)`. -/
theorem fromBytesBigEndian_append (hi lo : List UInt8) :
    fromBytesBigEndian (hi ++ lo)
      = fromBytesBigEndian lo + 2 ^ (8 * lo.length) * fromBytesBigEndian hi := by
  unfold fromBytesBigEndian
  simp only [Function.comp, List.reverse_append, fromBytes'_append, List.length_reverse]

namespace Venom
namespace Abi

/-! ## UInt256 / shift facts -/

/-- `ofNat` inverts `toNat`. -/
theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  cases a with | mk v => cases v with | mk n hn =>
  simp only [UInt256.ofNat, UInt256.toNat, Id.run]
  congr 1
  exact Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt hn])

/-- `shr 224` on an in-range word is division by `2 ^ 224`. -/
theorem shiftRight_ofNat_224 (V : Nat) (h : V < 2 ^ 256) :
    (UInt256.shiftRight (UInt256.ofNat V) (UInt256.ofNat 224)).toNat = V / 2 ^ 224 := by
  have hlt : V < UInt256.size := by
    have e : (2 : Nat) ^ 256 = UInt256.size := by decide
    omega
  unfold UInt256.shiftRight
  rw [if_neg (by decide)]
  simp only [UInt256.toNat, HShiftRight.hShiftRight, ShiftRight.shiftRight, Fin.shiftRight]
  show ((UInt256.ofNat V).val.val >>> (UInt256.ofNat 224).val.val) % 2 ^ 256 = V / 2 ^ 224
  have hv : (UInt256.ofNat V).val.val = V := by
    simp only [UInt256.ofNat, Fin.ofNat, Id.run]; exact Nat.mod_eq_of_lt hlt
  have h224 : (UInt256.ofNat 224).val.val = 224 := by decide
  rw [hv, h224, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by calc V / 2 ^ 224 ≤ V := Nat.div_le_self _ _
                                  _ < 2 ^ 256 := h)

/-! ## Selector extraction -/

/-- The 4-byte big-endian selector prefix of a call (the first 4 calldata
bytes). -/
def selectorBytes (sel : UInt256) : Mem := Asm.beBytesN 4 sel

/-- The selector the dispatcher extracts: `shr 224 (calldataload 0)` (exactly
what `AbiDispatch.entryBlock` computes into `selVar`). -/
def calldataSelector (s : VenomState) : UInt256 :=
  UInt256.shiftRight (s.calldataload (UInt256.ofNat 0)) (UInt256.ofNat 224)

/-- The 4-byte selector prefix decodes back to the selector value. -/
theorem fromBytesBigEndian_selectorBytes (sel : UInt256) (h : sel.toNat < 2 ^ 32) :
    fromBytesBigEndian (selectorBytes sel) = sel.toNat := by
  unfold selectorBytes
  have h256 : sel.toNat < 256 ^ 4 := by
    have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    omega
  have hrt := Asm.fromBytes32_beBytesN 4 sel h256
  have hbound : fromBytesBigEndian (Asm.beBytesN 4 sel) < UInt256.size := by
    have hb := fromBytesBigEndian_lt (Asm.beBytesN 4 sel)
    have hlen : (Asm.beBytesN 4 sel).length = 4 := Asm.beBytesN_length 4 sel (by decide)
    rw [hlen] at hb
    have : (2 : Nat) ^ (8 * 4) ≤ UInt256.size := by decide
    omega
  have hc := congrArg UInt256.toNat hrt
  simp only [Mem.fromBytes32, UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat] at hc
  rw [Nat.mod_eq_of_lt hbound] at hc
  exact hc

/-- Reading 32 bytes at offset 0 of `selectorBytes sel ++ args` yields the
selector prefix followed by the first 28 argument bytes (`args` has ≥ 28
bytes, so no zero padding). -/
theorem readBytes_selector (sel : UInt256) (args : Mem) (hargs : 28 ≤ args.length) :
    (selectorBytes sel ++ args).readBytes 0 32 = selectorBytes sel ++ args.take 28 := by
  have hlen : (selectorBytes sel).length = 4 := Asm.beBytesN_length 4 sel (by decide)
  simp only [Mem.readBytes, Nat.zero_add, List.drop_zero]
  rw [Mem.expand_of_length_le _ _ (by rw [List.length_append, hlen]; omega), List.take_append,
     List.take_of_length_le (show (selectorBytes sel).length ≤ 32 by rw [hlen]; omega), hlen]

/-- **Selector-extraction bridge.** With calldata `selectorBytes sel ++ args`
(selector fitting 4 bytes, at least one full 32-byte arg word so ≥ 28 bytes),
`shr 224 (calldataload 0)` recovers `sel`. -/
theorem calldataSelector_selectorBytes (s : VenomState) (sel : UInt256) (args : Mem)
    (hsel : sel.toNat < 2 ^ 32) (hargs : 28 ≤ args.length)
    (hcd : s.calldata = selectorBytes sel ++ args) :
    calldataSelector s = sel := by
  have hlen28 : (args.take 28).length = 28 := by rw [List.length_take]; omega
  -- the loaded word is  L + 2^224 * sel.toNat  with  L < 2^224
  have hLlt : fromBytesBigEndian (args.take 28) < 2 ^ 224 := by
    have hb := fromBytesBigEndian_lt (args.take 28); rw [hlen28] at hb; simpa using hb
  have hload : s.calldataload (UInt256.ofNat 0)
      = UInt256.ofNat (fromBytesBigEndian (args.take 28) + 2 ^ 224 * sel.toNat) := by
    unfold VenomState.calldataload
    rw [hcd, show (UInt256.ofNat 0).toNat = 0 by decide, readBytes_selector sel args hargs]
    unfold Mem.fromBytes32
    congr 1
    have hpow : 8 * (args.take 28).length = 224 := by rw [hlen28]
    rw [fromBytesBigEndian_append, fromBytesBigEndian_selectorBytes sel hsel, hpow]
  have hVlt : fromBytesBigEndian (args.take 28) + 2 ^ 224 * sel.toNat < 2 ^ 256 := by
    have h1 : 2 ^ 224 * (sel.toNat + 1) ≤ 2 ^ 256 := by
      calc 2 ^ 224 * (sel.toNat + 1) ≤ 2 ^ 224 * 2 ^ 32 := by gcongr; omega
        _ = 2 ^ 256 := by rw [← Nat.pow_add]
    have h2 : 2 ^ 224 * (sel.toNat + 1) = 2 ^ 224 * sel.toNat + 2 ^ 224 := by ring
    omega
  have key : (calldataSelector s).toNat = sel.toNat := by
    unfold calldataSelector
    rw [hload, shiftRight_ofNat_224 _ hVlt,
       Nat.add_comm (fromBytesBigEndian (args.take 28)) (2 ^ 224 * sel.toNat),
       Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hLlt, Nat.add_zero]
  calc calldataSelector s = UInt256.ofNat (calldataSelector s).toNat := (ofNat_toNat _).symm
    _ = UInt256.ofNat sel.toNat := by rw [key]
    _ = sel := ofNat_toNat sel

end Abi
end Venom
end EvmYul

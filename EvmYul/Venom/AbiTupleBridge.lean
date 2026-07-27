import EvmYul.Venom.AbiArrayBridge

/-!
# Venom IR — ABI arg-decode bridge for a TUPLE / struct argument

Completes the dynamic-ABI-front-end decode story: `AbiBridge` handles a
primitive word, `AbiArrayBridge` a dynamic array, and this file a tuple/struct.
An ABI tuple is a **head area** followed by a **tail area**: a static field is
inlined in the head; a dynamic field contributes a 32-byte offset *pointer* in
the head that points into the tail.

* **static tuple / struct** (all fields single-word) — the head IS the whole
  encoding, fields inlined consecutively: field `i` decodes at `pre + 32·i`
  (`calldataload_tuple_field`, over arbitrary field values).
* **mixed static + dynamic** (`(uintN, uintN[])`, the head/tail shape) — the
  static field decodes in the head, and the dynamic array via its head pointer
  into the tail (`mixed_arg_decode`), composing the primitive and array
  bridges. This is the general form of `AbiCrossval.abiLean_mixed_sum`'s
  concrete `(7, [10,20,30])`.
-/

namespace EvmYul.Venom

open EvmYul

/-! ## Static tuple / struct: fields inlined in the head -/

/-- **Static tuple field decode.** A struct/tuple whose fields are all single
words is encoded as the fields concatenated (no length prefix); field `i`
decodes at `pre.length + 32·i` — the tuple analogue of the array-element
bridge, without the array's leading length word. -/
theorem calldataload_tuple_field (s : VenomState) (pre suf : Mem)
    (fields : List UInt256) (i : Nat) (hi : i < fields.length)
    (hb : pre.length + 32 * i < 2 ^ 256)
    (hcd : s.calldata = pre ++ arrayBytes fields ++ suf) :
    s.calldataload (UInt256.ofNat (pre.length + 32 * i)) = fields[i] := by
  refine VenomState.calldataload_append_toBytes32 s
    (pre ++ arrayBytes (fields.take i)) (arrayBytes (fields.drop (i + 1)) ++ suf)
    fields[i] (UInt256.ofNat (pre.length + 32 * i)) ?_ ?_
  · rw [hcd, arrayBytes_split hi]; simp only [List.append_assoc]
  · rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt hb, List.length_append,
      arrayBytes_length, List.length_take, Nat.min_eq_left (le_of_lt hi)]

/-- A worked 2-field static struct (e.g. `Payment { to: address, amount:
uint256 }`) argument: both fields decode from the head, over arbitrary values. -/
theorem struct2_arg_decode (s : VenomState) (sel f0 f1 : UInt256)
    (hb : (Abi.selectorBytes sel).length + 32 * 1 < 2 ^ 256)
    (hcd : s.calldata = Abi.selectorBytes sel ++ arrayBytes [f0, f1] ++ []) :
    s.calldataload (UInt256.ofNat (Abi.selectorBytes sel).length) = f0
  ∧ s.calldataload (UInt256.ofNat ((Abi.selectorBytes sel).length + 32)) = f1 := by
  have hb0 : (Abi.selectorBytes sel).length + 32 * 0 < 2 ^ 256 := by omega
  have h0 := calldataload_tuple_field s (Abi.selectorBytes sel) [] [f0, f1] 0 (by simp) hb0
  have h1 := calldataload_tuple_field s (Abi.selectorBytes sel) [] [f0, f1] 1 (by simp) hb
  simp only [List.append_nil, List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one] at h0 h1 ⊢
  exact ⟨h0 hcd, h1 hcd⟩

/-! ## Mixed static + dynamic: head field inline, array via head pointer -/

/-- **Mixed tuple argument `(u : uintN, arr : uintN[])`.** The ABI head is
`u ++ ptr` (`ptr = 0x40`, the two-word head size); the tail is
`len ++ elements`. The static field decodes inline in the head, and array
element `i` from the pointer-followed tail offset — the primitive and array
bridges composed. Generalizes `AbiCrossval.abiLean_mixed_sum`'s concrete
`(7, [10, 20, 30])` (no `native_decide`). -/
theorem mixed_arg_decode (s : VenomState) (sel u : UInt256) (arr : List UInt256)
    (i : Nat) (hi : i < arr.length)
    (hbe : elemOffset ((Abi.selectorBytes sel).length + 64) i < 2 ^ 256)
    (hcd : s.calldata = Abi.selectorBytes sel
      ++ (Mem.toBytes32 u ++ Mem.toBytes32 (UInt256.ofNat 0x40))
      ++ (Mem.toBytes32 (UInt256.ofNat arr.length) ++ arrayBytes arr) ++ []) :
    s.calldataload (UInt256.ofNat (Abi.selectorBytes sel).length) = u
  ∧ s.calldataload (UInt256.ofNat (elemOffset ((Abi.selectorBytes sel).length + 64) i)) = arr[i] := by
  have hsel : (Abi.selectorBytes sel).length = 4 := Asm.beBytesN_length 4 sel (by decide)
  -- static field u at the head, right after the selector
  have hu : s.calldataload (UInt256.ofNat (Abi.selectorBytes sel).length) = u := by
    refine VenomState.calldataload_append_toBytes32 s (Abi.selectorBytes sel)
      (Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ (Mem.toBytes32 (UInt256.ofNat arr.length) ++ arrayBytes arr) ++ []) u
      (UInt256.ofNat (Abi.selectorBytes sel).length) ?_ ?_
    · rw [hcd]; simp only [List.append_assoc]
    · rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt (by rw [hsel]; omega)]
  -- array element i via the head pointer (pre = selector ++ u ++ ptr, len 4+32+32=68)
  have harr : s.calldataload
      (UInt256.ofNat (elemOffset ((Abi.selectorBytes sel).length + 64) i)) = arr[i] := by
    have hpre : (Abi.selectorBytes sel ++ Mem.toBytes32 u ++ Mem.toBytes32 (UInt256.ofNat 0x40)).length
        = (Abi.selectorBytes sel).length + 64 := by
      rw [List.length_append, List.length_append, Mem.toBytes32_length, Mem.toBytes32_length]
    have := calldataload_dynarray_elem s
      (Abi.selectorBytes sel ++ Mem.toBytes32 u ++ Mem.toBytes32 (UInt256.ofNat 0x40)) []
      arr (UInt256.ofNat arr.length) i hi (by rw [hpre]; exact hbe)
      (by rw [hcd]; simp only [List.append_assoc])
    rwa [hpre] at this
  exact ⟨hu, harr⟩

end EvmYul.Venom

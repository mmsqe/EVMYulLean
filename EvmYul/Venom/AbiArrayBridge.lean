import EvmYul.Venom.AbiBridge
import EvmYul.Venom.AbiSelector

/-!
# Venom IR — ABI arg-decode bridge for a DYNAMIC ARRAY argument

`AbiBridge.calldataload_append_toBytes32` links the ABI encoder to Venom's
`CALLDATALOAD` for a *primitive* (single 32-byte word) argument. This file is
the dynamic-array analogue: for a `uintN[]` / `address[]` argument whose ABI
tail is `len ++ elem₀ ++ elem₁ ++ …` (each a 32-byte word), it proves that
following the ABI head pointer with `CALLDATALOAD` recovers the length and
every element — for **arbitrary** element values, not just a concrete
`native_decide` witness (`AbiCrossval.abiLean_dynarray_sum` is the concrete,
cross-validated instance; this is the reusable property).

The tail is modelled as `arrayBytes elems = elems.flatMap toBytes32`. Reading
element `i` is `calldataload_append_toBytes32` applied after splitting the flat
element region around index `i`.
-/

namespace EvmYul.Venom

open EvmYul

/-- The ABI element region of a dynamic array: each element's 32-byte word,
concatenated (the data that follows the 32-byte length word). -/
def arrayBytes (elems : List UInt256) : Mem :=
  elems.flatMap Mem.toBytes32

@[simp] theorem arrayBytes_length (elems : List UInt256) :
    (arrayBytes elems).length = 32 * elems.length := by
  induction elems with
  | nil => simp [arrayBytes]
  | cons x xs ih =>
      rw [arrayBytes, List.flatMap_cons, List.length_append, Mem.toBytes32_length,
        ← arrayBytes, ih, List.length_cons]
      ring

/-- Split the element region around index `i`: everything before `i`, then
element `i`'s word, then everything after. -/
theorem arrayBytes_split {elems : List UInt256} {i : Nat} (h : i < elems.length) :
    arrayBytes elems
      = arrayBytes (elems.take i) ++ Mem.toBytes32 elems[i] ++ arrayBytes (elems.drop (i + 1)) := by
  unfold arrayBytes
  conv_lhs => rw [← List.take_append_drop i elems, List.drop_eq_getElem_cons h,
    List.flatMap_append, List.flatMap_cons]
  rw [List.append_assoc]

/-- The byte position of element `i`'s word: the length word (32) plus `i`
element words, past the argument's `pre`. -/
def elemOffset (preLen i : Nat) : Nat := preLen + 32 + 32 * i

/-- **Dynamic-array length decode.** With the array tail placed at byte
`pre.length`, `calldataload` there returns the length word. -/
theorem calldataload_dynarray_len (s : VenomState) (pre suf : Mem)
    (elems : List UInt256) (len : UInt256)
    (hb : pre.length < 2 ^ 256)
    (hcd : s.calldata = pre ++ Mem.toBytes32 len ++ arrayBytes elems ++ suf) :
    s.calldataload (UInt256.ofNat pre.length) = len := by
  apply VenomState.calldataload_append_toBytes32 s pre (arrayBytes elems ++ suf) len
    (UInt256.ofNat pre.length)
  · rw [hcd]; simp only [List.append_assoc]
  · rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt hb]

/-- **Dynamic-array element decode.** Element `i` of a `uintN[]`/`address[]`
argument decodes from `elemOffset pre.length i` — the array analogue of the
primitive `calldataload_append_toBytes32`, over arbitrary element values. -/
theorem calldataload_dynarray_elem (s : VenomState) (pre suf : Mem)
    (elems : List UInt256) (len : UInt256) (i : Nat) (hi : i < elems.length)
    (hb : elemOffset pre.length i < 2 ^ 256)
    (hcd : s.calldata = pre ++ Mem.toBytes32 len ++ arrayBytes elems ++ suf) :
    s.calldataload (UInt256.ofNat (elemOffset pre.length i)) = elems[i] := by
  refine VenomState.calldataload_append_toBytes32 s
    (pre ++ Mem.toBytes32 len ++ arrayBytes (elems.take i))
    (arrayBytes (elems.drop (i + 1)) ++ suf) elems[i]
    (UInt256.ofNat (elemOffset pre.length i)) ?_ ?_
  · rw [hcd, arrayBytes_split hi]; simp only [List.append_assoc]
  · rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt hb, elemOffset,
      List.length_append, List.length_append, Mem.toBytes32_length,
      arrayBytes_length, List.length_take, Nat.min_eq_left (le_of_lt hi)]

/-! ## Demo: the general bridge subsumes the concrete cross-validation shape -/

/-- A `uintN[]` argument encoded at the standard single-dynamic-arg layout —
head pointer `0x20`, then the tail (length ++ elements) — decodes element `i`
back to `elems[i]`, purely from the general bridge (no `native_decide`). This
is the property `AbiCrossval.abiLean_dynarray_sum` exercises on one concrete
`[10, 20, 30]`. -/
theorem dynarray_arg_decode (s : VenomState) (sel : UInt256) (elems : List UInt256)
    (i : Nat) (hi : i < elems.length)
    (hb : elemOffset (Abi.selectorBytes sel).length i < 2 ^ 256)
    (hcd : s.calldata =
      Abi.selectorBytes sel ++ Mem.toBytes32 (UInt256.ofNat elems.length)
        ++ arrayBytes elems ++ []) :
    s.calldataload (UInt256.ofNat (elemOffset (Abi.selectorBytes sel).length i)) = elems[i] :=
  calldataload_dynarray_elem s (Abi.selectorBytes sel) [] elems
    (UInt256.ofNat elems.length) i hi hb (by simpa using hcd)

/-- A worked 3-element instance for ARBITRARY elements: each of the three
`calldataload`s that `AbiCrossval.abiLean_dynarray_sum` performs on the concrete
`[10, 20, 30]` recovers the corresponding element `a`/`b`/`c` — so their sum is
`a + b + c`, with no concrete encoding or `native_decide`. -/
theorem dynarray_sum3 (s : VenomState) (sel a b c : UInt256)
    (hb : elemOffset (Abi.selectorBytes sel).length 2 < 2 ^ 256)
    (hcd : s.calldata = Abi.selectorBytes sel ++ Mem.toBytes32 (UInt256.ofNat 3)
      ++ arrayBytes [a, b, c] ++ []) :
    s.calldataload (UInt256.ofNat (elemOffset (Abi.selectorBytes sel).length 0))
  + s.calldataload (UInt256.ofNat (elemOffset (Abi.selectorBytes sel).length 1))
  + s.calldataload (UInt256.ofNat (elemOffset (Abi.selectorBytes sel).length 2))
    = a + b + c := by
  have hb0 : elemOffset (Abi.selectorBytes sel).length 0 < 2 ^ 256 := by
    simp only [elemOffset] at hb ⊢; omega
  have hb1 : elemOffset (Abi.selectorBytes sel).length 1 < 2 ^ 256 := by
    simp only [elemOffset] at hb ⊢; omega
  have h0 := dynarray_arg_decode s sel [a, b, c] 0 (by simp) hb0 hcd
  have h1 := dynarray_arg_decode s sel [a, b, c] 1 (by simp) hb1 hcd
  have h2 := dynarray_arg_decode s sel [a, b, c] 2 (by simp) hb hcd
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  rw [h0, h1, h2]

end EvmYul.Venom

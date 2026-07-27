import EvmYul.Wheels
import EvmYul.Venom.FFIMemory

/-!
# ByteArray ↔ List laws for the vendored Venom (`Hol`) stack

`ByteArray` is a thin wrapper around `Array UInt8`. In Lean 4.22 its `copySlice`
/ `extract` / `append` all unfold to `Array.extract` / `++` on the underlying
`.data` (see `Init.Data.ByteArray.Basic`), and `Array` *does* carry the relevant
`size_extract` / `getElem_extract` / `getElem?_append_*` lemmas. So the facts the
vendored stack needs are no longer opaque: the `toList` / `toByteArray` codec laws
below are **proven** by induction over the (well-founded) read/write loops, lifting
everything to the `Array` layer.

What remains genuinely irreducible is `ffi.ByteArray.zeroes` (opaque FFI), already
isolated in `EvmYul/Venom/FFIMemory.lean` as the M1 axioms `ffi_zeroes_size` /
`ffi_zeroes_get`. The `ByteArray.write` laws (still axioms here, discharged in later
batches) bottom out in those two and `Array` stdlib — i.e. the whole stack converges
onto a *single* trust boundary: the two M1 `ffi.zeroes` axioms.

These live in `namespace EvmYul` so the vendored proofs (nested under
`EvmYul.Venom.Hol`) reach them unqualified, exactly as on the upstream `venom` branch.
They are deliberately kept **out** of the shared core `EvmYul/Wheels.lean` so the
`venom_ir` trust boundary is unaffected.
-/

namespace ByteArray

/-- `ByteArray.get!` is the underlying-array list indexing. -/
theorem get!_eq_data_getElem (bs : ByteArray) (i : Nat) (h : i < bs.size) :
    bs.get! i = bs.data.toList[i]'(by rw [Array.length_toList]; exact h) := by
  cases bs with
  | mk d =>
    simp only [ByteArray.get!]
    rw [Array.getElem_toList]
    exact getElem!_pos d i h

/-- Loop invariant for `ByteArray.toList`: it reverses the prefix already read onto `r`. -/
theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = (((bs.data.toList).drop i).reverse ++ r).reverse := by
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop.eq_def, if_pos h, ih]
    have hlen : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.drop_eq_getElem_cons hlen, ← get!_eq_data_getElem bs i h]
    simp [List.reverse_cons, List.append_assoc]
  | case2 i r h =>
    rw [ByteArray.toList.loop.eq_def, if_neg h]
    have hle : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le hle]
    simp

/-- `ByteArray.toList` is the underlying array as a list. -/
theorem toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]
  simp

/-- `ByteArray.size` is the size of the underlying array. -/
theorem size_eq (ba : ByteArray) : ba.size = ba.data.size := rfl

/-- Size of a `copySlice`: prefix `[0,dstOff)` of `dst`, the copied `len` bytes,
    then the suffix of `dst`. Lifted from `Array.size_extract`/`size_append`. -/
theorem size_copySlice (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff len : Nat) (e : Bool) :
    (src.copySlice srcOff dst dstOff len e).size
      = (min dstOff dst.size) + (min len (src.size - srcOff))
        + (dst.size - (dstOff + min len (src.size - srcOff))) := by
  show (src.copySlice srcOff dst dstOff len e).data.size = _
  simp only [ByteArray.copySlice, Array.size_append, Array.size_extract]
  have hs : src.size = src.data.size := rfl
  have hd : dst.size = dst.data.size := rfl
  omega

-- `ByteArray.size_append` / `ByteArray.data_append` are now in core Lean v4.31.

theorem getElem?_eq_data (ba : ByteArray) (i : Nat) : ba[i]? = ba.data[i]? := rfl

theorem getElem?_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]? = a[i]? := by
  rw [getElem?_eq_data, data_append, Array.getElem?_append_left h]; rfl

theorem getElem?_append_right (a b : ByteArray) (i : Nat) (h : a.size ≤ i) :
    (a ++ b)[i]? = b[i - a.size]? := by
  rw [getElem?_eq_data, data_append, Array.getElem?_append_right h]; rfl

/-- Appending an empty `zeroes ⟨0⟩` block is a no-op on the data. -/
theorem append_zeroes0_data (X : ByteArray) :
    (X ++ ffi.ByteArray.zeroes ⟨(0:Nat)⟩).data = X.data := by
  rw [data_append]
  have hz : (ffi.ByteArray.zeroes ⟨(0:Nat)⟩).size = 0 := by
    rw [EvmYul.M1.ffi_zeroes_size]; rfl
  have : (ffi.ByteArray.zeroes ⟨(0:Nat)⟩).data = #[] :=
    Array.eq_empty_of_size_eq_zero hz
  rw [this, Array.append_empty]

/-- **`ByteArray.write` as a splice** (when the target already covers the start,
    `off ≤ dest.size`, so no zero-gap padding is created — `destPadding = zeroes ⟨0⟩`
    and the FFI length never wraps). The result is `dest` with `[off, off+source.size)`
    overwritten by `source`, keeping the prefix `[0,off)` and the suffix. -/
theorem write_data_of_le (source dest : ByteArray) (off : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size) :
    (source.write 0 dest off source.size).data
      = dest.data.extract 0 off ++ source.data
        ++ dest.data.extract (off + source.size) dest.data.size := by
  unfold ByteArray.write
  rw [if_neg (show ¬ source.size = 0 by omega), if_neg (show ¬ 0 ≥ source.size by omega)]
  simp only []
  have e1 : off - dest.size = 0 := by omega
  have e2 : min source.size (source.size - 0) = source.size := by omega
  have e3 : min dest.size (off + source.size) - (off + source.size) = 0 := by omega
  rw [e1, e2, e3, Nat.add_zero]
  simp only [ByteArray.copySlice]
  rw [append_zeroes0_data source, append_zeroes0_data dest]
  simp only [Nat.zero_add, Nat.sub_zero, ByteArray.size_eq, Nat.min_self, Array.extract_size]

/-- **`ByteArray.write` as a splice, general `off`.** Like `write_data_of_le` but
    keeps the zero-pad block `zeroes ⟨off - dest.size⟩` explicit, so it holds for
    *any* `off` (the pad extends `dest` to length `≥ off`, hence the leading
    `extract 0 off` always has size exactly `off`). -/
theorem write_data_padded (source dest : ByteArray) (off : Nat) (hpos : 0 < source.size) :
    (source.write 0 dest off source.size).data
      = (dest ++ ffi.ByteArray.zeroes ⟨(off - dest.size : Nat)⟩).data.extract 0 off
        ++ source.data
        ++ (dest ++ ffi.ByteArray.zeroes ⟨(off - dest.size : Nat)⟩).data.extract (off + source.size)
             (dest ++ ffi.ByteArray.zeroes ⟨(off - dest.size : Nat)⟩).data.size := by
  unfold ByteArray.write
  rw [if_neg (show ¬ source.size = 0 by omega), if_neg (show ¬ 0 ≥ source.size by omega)]
  simp only []
  have e2 : min source.size (source.size - 0) = source.size := by omega
  rw [e2, show min dest.size (off + source.size) - (off + source.size) = 0 by omega, Nat.add_zero]
  simp only [ByteArray.copySlice]
  rw [append_zeroes0_data source]
  simp only [Nat.zero_add, Nat.sub_zero, ByteArray.size_eq, Nat.min_self, Array.extract_size]

/-- **Disjoint frame (byte level).** With `off ≤ dest.size` (so no zero gap is
    written), a byte outside the written region is exactly the original. -/
theorem write_getElem?_disjoint (source dest : ByteArray) (off i : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size)
    (hdisj : i < off ∨ off + source.size ≤ i) :
    (source.write 0 dest off source.size)[i]? = dest[i]? := by
  rw [getElem?_eq_data, write_data_of_le source dest off hpos hoff, getElem?_eq_data]
  have hds : dest.data.size = dest.size := rfl
  have hss : source.data.size = source.size := rfl
  have hoff' : off ≤ dest.data.size := by omega
  have hPsize : (dest.data.extract 0 off).size = off := by rw [Array.size_extract]; omega
  have hPSsize : (dest.data.extract 0 off ++ source.data).size = off + source.size := by
    rw [Array.size_append, hPsize]; omega
  rcases hdisj with hlt | hge
  · rw [Array.getElem?_append_left (by rw [hPSsize]; omega),
        Array.getElem?_append_left (by rw [hPsize]; omega),
        Array.getElem?_extract]
    rw [if_pos (by omega)]; congr 1; omega
  · rw [Array.getElem?_append_right (by rw [hPSsize]; omega), hPSsize,
        Array.getElem?_extract, Nat.min_self]
    have hidx : off + source.size + (i - (off + source.size)) = i := by omega
    rw [hidx]
    by_cases hi : i < dest.data.size
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega)]
      exact (Array.getElem?_eq_none (by omega)).symm

/-- **In-window read (byte level).** With `off ≤ dest.size` (no zero gap), a byte
    *inside* the written region `[off, off+source.size)` reads back from `source`
    (offset by `off`). The complement of `write_getElem?_disjoint`; together they
    pin down every byte of a `write`. -/
theorem write_getElem?_inWindow (source dest : ByteArray) (off i : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size)
    (hwin : off ≤ i ∧ i < off + source.size) :
    (source.write 0 dest off source.size)[i]? = source[i - off]? := by
  rw [getElem?_eq_data, write_data_of_le source dest off hpos hoff]
  have hss : source.data.size = source.size := rfl
  have hPsize : (dest.data.extract 0 off).size = off := by
    rw [Array.size_extract]; have : dest.data.size = dest.size := rfl; omega
  rw [Array.getElem?_append_left (by rw [Array.size_append, hPsize, hss]; omega),
      Array.getElem?_append_right (by rw [hPsize]; omega), hPsize, getElem?_eq_data]

/-- Extracting exactly the middle block `S` out of `P ++ S ++ Q` (when `P.size = off`). -/
theorem arr_extract_middle (P S Q : Array UInt8) (off : Nat) (hP : P.size = off) :
    (P ++ S ++ Q).extract off (off + S.size) = S := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_extract]
  by_cases hj : j < S.size
  · rw [if_pos (by rw [Array.size_append, Array.size_append, hP]; omega),
        Array.getElem?_append_left (by rw [Array.size_append, hP]; omega),
        Array.getElem?_append_right (by rw [hP]; omega), hP]
    congr 1; omega
  · rw [if_neg (by rw [Array.size_append, Array.size_append, hP]; omega), eq_comm,
        Array.getElem?_eq_none (by omega)]

theorem data_extract_of_le (x : ByteArray) (b e : Nat) (h : b ≤ e) :
    (x.extract b e).data = x.data.extract b e := by
  unfold ByteArray.extract
  simp only [ByteArray.copySlice]
  have he : (ByteArray.empty).data = #[] := Array.eq_empty_of_size_eq_zero rfl
  rw [he, show b + (e - b) = e by omega]
  simp

/-- **Spill roundtrip (core).** Writing `source` at `off` and reading the same
    `source.size`-byte window back returns `source`. Holds for *any* `off` as long as
    the pad length does not wrap the machine word (`off - dest.size < USize.size`);
    `source.size < 2^64` keeps `readWithPadding` out of its panic branch. The read
    window lands exactly on the spliced block. -/
theorem write_read (source dest : ByteArray) (off : Nat)
    (hpos : 0 < source.size) (hwrap : off - dest.size < USize.size) (hsz : source.size < 2 ^ 64) :
    (source.write 0 dest off source.size).readWithPadding off source.size = source := by
  have hdpad : (ffi.ByteArray.zeroes ⟨(off - dest.size : Nat)⟩).size = off - dest.size := by
    rw [EvmYul.M1.ffi_zeroes_size,
        show (⟨(off - dest.size : Nat)⟩ : USize).toNat = (off - dest.size) % USize.size from by
          simp [USize.toNat]]
    exact Nat.mod_eq_of_lt hwrap
  have hss : source.data.size = source.size := rfl
  set DP := dest ++ ffi.ByteArray.zeroes ⟨(off - dest.size : Nat)⟩ with hDP
  have hDPd : DP.data.size = dest.size + (off - dest.size) := by
    show DP.size = _; rw [hDP, ByteArray.size_append, hdpad]
  have hRdata := write_data_padded source dest off hpos
  rw [← hDP] at hRdata
  have hTerm1 : (DP.data.extract 0 off).size = off := by rw [Array.size_extract]; omega
  have hRsize : off + source.size ≤ (source.write 0 dest off source.size).size := by
    show off + source.size ≤ (source.write 0 dest off source.size).data.size
    rw [hRdata, Array.size_append, Array.size_append, hTerm1, hss]; omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega : ¬ source.size ≥ 2 ^ 64)]
  have hread : (source.write 0 dest off source.size).readWithoutPadding off source.size = source := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by omega : ¬ off ≥ (source.write 0 dest off source.size).size),
        show min source.size (source.write 0 dest off source.size).size = source.size by omega]
    apply ByteArray.ext
    rw [data_extract_of_le _ off (off + source.size) (by omega), hRdata,
        show off + source.size = off + source.data.size by rw [hss]]
    exact arr_extract_middle (DP.data.extract 0 off) source.data _ off hTerm1
  rw [hread]
  show source ++ ffi.ByteArray.zeroes ⟨source.size - source.size⟩ = source
  apply ByteArray.ext
  rw [data_append]
  have hz : (ffi.ByteArray.zeroes ⟨source.size - source.size⟩).data = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    show (ffi.ByteArray.zeroes ⟨source.size - source.size⟩).size = 0
    rw [EvmYul.M1.ffi_zeroes_size]; simp
  rw [hz, Array.append_empty]

/-- Size of `zeroes` built from a `BitVec` subtraction (the form `readWithPadding`
    uses for its trailing zero-pad), assuming the difference does not wrap. -/
theorem zeroes_bvsub_size (a b : Nat) (hb : b ≤ a) (ha : a < USize.size) :
    (ffi.ByteArray.zeroes ⟨(↑a - ↑b : BitVec System.Platform.numBits)⟩).size = a - b := by
  rw [EvmYul.M1.ffi_zeroes_size]
  simp only [USize.toNat, BitVec.toNat_sub]
  have ha' : a < 2 ^ System.Platform.numBits := ha
  have ha2 : (↑a : BitVec System.Platform.numBits).toNat = a := Nat.mod_eq_of_lt ha'
  have hb2 : (↑b : BitVec System.Platform.numBits).toNat = b := Nat.mod_eq_of_lt (by omega)
  rw [ha2, hb2,
      show 2 ^ System.Platform.numBits - b + a = 2 ^ System.Platform.numBits + (a - b) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- Every byte of `ffi.ByteArray.zeroes` reads back as `0` (the `getElem?` form of the
    M1 `ffi_zeroes_get` axiom). -/
theorem zeroes_getElem? (n : USize) (j : Nat) (hj : j < (ffi.ByteArray.zeroes n).size) :
    (ffi.ByteArray.zeroes n)[j]? = some 0 := by
  rw [getElem?_eq_data, Array.getElem?_eq_getElem hj]
  congr 1
  have h1 : (ffi.ByteArray.zeroes n).data[j]! = 0 := EvmYul.M1.ffi_zeroes_get n j
  rwa [getElem!_pos _ j hj] at h1

theorem readWithoutPadding_size_le (ba : ByteArray) (addr len : Nat) :
    (ba.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  by_cases h : addr ≥ ba.size
  · rw [if_pos h, show (ByteArray.empty).size = 0 from rfl]; exact Nat.zero_le _
  · rw [if_neg h, ByteArray.size_eq, data_extract_of_le _ _ _ (by omega), Array.size_extract]
    omega

theorem readWithoutPadding_getElem?_lt (ba : ByteArray) (addr len k : Nat)
    (hk : k < (ba.readWithoutPadding addr len).size) :
    (ba.readWithoutPadding addr len)[k]? = ba[addr + k]? := by
  unfold ByteArray.readWithoutPadding at hk ⊢
  by_cases h : addr ≥ ba.size
  · rw [if_pos h] at hk; simp [show (ByteArray.empty).size = 0 from rfl] at hk
  · rw [if_neg h] at hk ⊢
    rw [getElem?_eq_data, getElem?_eq_data, data_extract_of_le _ _ _ (by omega),
        Array.getElem?_extract]
    rw [ByteArray.size_eq, data_extract_of_le _ _ _ (by omega), Array.size_extract] at hk
    rw [if_pos (by omega)]

/-- `readWithPadding` always returns exactly `len` bytes (for `len < USize.size`). -/
theorem readWithPadding_size (ba : ByteArray) (addr len : Nat) (hlen : len < USize.size) :
    (ba.readWithPadding addr len).size = len := by
  have hle := readWithoutPadding_size_le ba addr len
  have h264 : len < 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega : ¬ len ≥ 2 ^ 64), ByteArray.size_append,
      zeroes_bvsub_size len (ba.readWithoutPadding addr len).size hle hlen]
  omega

/-- **Per-byte characterization of `readWithPadding`.** Byte `k` of the window is the
    source byte at `addr+k`, defaulting to `0` past the end (`.getD 0`). -/
theorem readWithPadding_getElem? (ba : ByteArray) (addr len : Nat) (hlen : len < USize.size)
    (k : Nat) (hk : k < len) :
    (ba.readWithPadding addr len)[k]? = some ((ba[addr + k]?).getD 0) := by
  have hle := readWithoutPadding_size_le ba addr len
  have h264 : len < 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega : ¬ len ≥ 2 ^ 64)]
  by_cases hkr : k < (ba.readWithoutPadding addr len).size
  · rw [getElem?_append_left _ _ k hkr, readWithoutPadding_getElem?_lt ba addr len k hkr]
    have heq := readWithoutPadding_getElem?_lt ba addr len k hkr
    have hsome : (ba[addr + k]?).isSome := by
      rw [← heq, getElem?_eq_data, Array.getElem?_eq_getElem (by rw [← ByteArray.size_eq]; exact hkr)]
      rfl
    rcases hv : ba[addr + k]? with _ | v
    · rw [hv] at hsome; simp at hsome
    · simp
  · rw [getElem?_append_right _ _ k (by omega)]
    have hpadsize : (ffi.ByteArray.zeroes ⟨(↑len - ↑(ba.readWithoutPadding addr len).size : BitVec System.Platform.numBits)⟩).size
                    = len - (ba.readWithoutPadding addr len).size :=
      zeroes_bvsub_size len (ba.readWithoutPadding addr len).size hle hlen
    rw [zeroes_getElem? _ _ (by rw [hpadsize]; omega)]
    have hnone : ba[addr + k]? = none := by
      rw [getElem?_eq_data, Array.getElem?_eq_none]
      rw [readWithoutPadding] at hkr
      by_cases h : addr ≥ ba.size
      · show ba.data.size ≤ addr + k
        have : ba.size = ba.data.size := rfl; omega
      · rw [if_neg h, ByteArray.size_eq, data_extract_of_le _ _ _ (by omega), Array.size_extract] at hkr
        show ba.data.size ≤ addr + k
        have hbs : ba.size = ba.data.size := rfl
        omega
    simp [hnone]

/-- **Disjoint frame, window granularity.** A `readWithPadding` window disjoint from
    the written region is unaffected by the write (with `off ≤ dest.size`). Derived
    byte-by-byte from `write_getElem?_disjoint` + the `readWithPadding` characterization. -/
theorem readWithPadding_write_disjoint (source dest : ByteArray) (off addr len : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size) (hlen : len < USize.size)
    (hdisj : addr + len ≤ off ∨ off + source.size ≤ addr) :
    (source.write 0 dest off source.size).readWithPadding addr len
      = dest.readWithPadding addr len := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro k
  rw [← getElem?_eq_data, ← getElem?_eq_data]
  by_cases hk : k < len
  · rw [readWithPadding_getElem? _ addr len hlen k hk,
        readWithPadding_getElem? _ addr len hlen k hk,
        write_getElem?_disjoint source dest off (addr + k) hpos hoff
          (by rcases hdisj with h | h <;> omega)]
  · rw [getElem?_eq_data, getElem?_eq_data,
        Array.getElem?_eq_none (by rw [← ByteArray.size_eq, readWithPadding_size _ addr len hlen]; omega),
        Array.getElem?_eq_none (by rw [← ByteArray.size_eq, readWithPadding_size _ addr len hlen]; omega)]

/-- **`readWithPadding` slice congruence.** Two byte arrays whose bytes agree (up to the
    zero-default past the end, `(·[i]?).getD 0`) on the whole window `[addr, addr+len)` read
    the same window. The window read depends only on those `getD 0` byte values
    (`readWithPadding_getElem?`), so this is exactly the hypothesis it needs — strictly weaker
    than `getElem?` equality (it collapses `none` vs `some 0`). The `memoryRel` slice fact a
    `RETURN`/`REVERT` returndata match reduces to. -/
theorem readWithPadding_congr (m1 m2 : ByteArray) (addr len : Nat) (hlen : len < USize.size)
    (hb : ∀ k, k < len → (m1[addr + k]?).getD (0 : UInt8) = (m2[addr + k]?).getD 0) :
    m1.readWithPadding addr len = m2.readWithPadding addr len := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro k
  rw [← getElem?_eq_data, ← getElem?_eq_data]
  by_cases hk : k < len
  · rw [readWithPadding_getElem? _ addr len hlen k hk,
        readWithPadding_getElem? _ addr len hlen k hk, hb k hk]
  · rw [getElem?_eq_data, getElem?_eq_data,
        Array.getElem?_eq_none (by rw [← ByteArray.size_eq, readWithPadding_size _ addr len hlen]; omega),
        Array.getElem?_eq_none (by rw [← ByteArray.size_eq, readWithPadding_size _ addr len hlen]; omega)]

end ByteArray

namespace List

/-- Loop invariant for `List.toByteArray`: it pushes the list onto the accumulator. -/
theorem toByteArray_loop_data (l : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop l acc).data = acc.data ++ l.toArray := by
  induction l generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih =>
    simp only [List.toByteArray.loop, ih]
    cases acc with
    | mk d =>
      show d.push b ++ bs.toArray = d ++ (b :: bs).toArray
      rw [List.toArray_cons, ← Array.append_assoc]
      rfl

/-- `List.toByteArray` is the list as an underlying array. -/
theorem toByteArray_data (l : List UInt8) : (List.toByteArray l).data = l.toArray := by
  rw [List.toByteArray, toByteArray_loop_data]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

end List

namespace EvmYul

/-- `List.toByteArray` followed by `ByteArray.toList` recovers the original list. -/
theorem toByteArray_toList (l : List UInt8) : (List.toByteArray l).toList = l := by
  rw [ByteArray.toList_eq_data, List.toByteArray_data]

/-- `List.toByteArray` preserves size. -/
theorem byteArray_size_toByteArray (l : List UInt8) : (List.toByteArray l).size = l.length := by
  show (List.toByteArray l).data.size = _
  rw [List.toByteArray_data]; simp

/-- Writing bytes to a destination and then reading the same region returns the source.
    Needs the pad length not to wrap the machine word (`offset - dest.size < USize.size`)
    and `source.size < 2^64` (`readWithPadding` is panic-free). -/
theorem byteArray_write_read (source dest : ByteArray) (offset : ℕ)
    (hpos : 0 < source.size) (hwrap : offset - dest.size < USize.size) (hsz : source.size < 2 ^ 64) :
    (source.write 0 dest offset source.size).readWithPadding offset source.size = source :=
  ByteArray.write_read source dest offset hpos hwrap hsz

/-- `ByteArray.write` never shrinks the destination: the result keeps the whole of
    `dest ++ padding` as the `copySlice` target, and padding size is ≥ 0. (No
    `< 2^64` side condition is needed — the bound only uses `dst.size ≥ dest.size`.) -/
theorem byteArray_write_size (source dest : ByteArray) (offset : ℕ) :
    dest.size ≤ (source.write 0 dest offset source.size).size := by
  unfold ByteArray.write
  by_cases h0 : source.size = 0
  · simp [h0]
  · rw [if_neg h0, if_neg (show ¬ (0 ≥ source.size) by omega)]
    simp only []
    rw [ByteArray.size_copySlice, ByteArray.size_append]
    omega

/-- **Disjoint frame.** A byte outside the written region `[offset, offset+source.size)`
    is left untouched by `ByteArray.write`. Needs `offset ≤ dest.size`: otherwise the
    write zero-fills the gap `[dest.size, offset)`, so `result[i]? = some 0 ≠ none`
    there — the reason the previous unconditional `getElem?`-level axiom was unsound.
    At every real call site `dest` is the expanded memory, so `offset ≤ dest.size`. -/
theorem byteArray_write_getElem?_disjoint (source dest : ByteArray) (offset i : ℕ)
    (hpos : 0 < source.size) (hoff : offset ≤ dest.size)
    (hdisj : i < offset ∨ offset + source.size ≤ i) :
    (source.write 0 dest offset source.size)[i]? = dest[i]? :=
  ByteArray.write_getElem?_disjoint source dest offset i hpos hoff hdisj

/-- **Disjoint frame, window granularity.** Reading a window `[addr, addr+len)`
    disjoint from the written region is unaffected by the write. Now a theorem
    (proven byte-by-byte from `write_getElem?_disjoint` + the `readWithPadding`
    characterization); needs `off ≤ dest.size` (no zero gap) and `len < USize.size`
    (the read window does not wrap). Consumed by `planSpillRel`. -/
theorem byteArray_readWithPadding_write_disjoint (source dest : ByteArray) (off addr len : ℕ)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size) (hlen : len < USize.size)
    (hdisj : addr + len ≤ off ∨ off + source.size ≤ addr) :
    (source.write 0 dest off source.size).readWithPadding addr len
      = dest.readWithPadding addr len :=
  ByteArray.readWithPadding_write_disjoint source dest off addr len hpos hoff hlen hdisj

/-- **In-window frame.** A byte inside the written region reads back from `source`
    (offset by `off`). The complement of `byteArray_write_getElem?_disjoint`. -/
theorem byteArray_write_getElem?_inWindow (source dest : ByteArray) (off i : ℕ)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size)
    (hwin : off ≤ i ∧ i < off + source.size) :
    (source.write 0 dest off source.size)[i]? = source[i - off]? :=
  ByteArray.write_getElem?_inWindow source dest off i hpos hoff hwin

end EvmYul

import EvmYul.Venom.MemInvariant
import EvmYul.Venom.FFIMemory
import EvmYul.MachineStateOps

/-!
# Bridging the memory invariant layer to the real `ByteArray` machine

`MemInvariant` proves the memory laws (read-after-write, the frame / no-aliasing
law) on the proof-friendly `Mem` (`List UInt8`) model. This file transports them
to EVMYulLean's *real* machine memory (`ByteArray`) by **refinement**.

The crux is `ByteArray.toList`, which is a custom accumulator loop rather than
`data.toList`, with no characterization lemmas in core. We prove that keystone
(`toList_eq_data`) by loop induction, which lets every `ByteArray.toList` goal be
discharged through the `Array`/`data` API (`data_append`, `data_extract`,
`Array.toList_*`). On top of it the machine **read** side is then *proved*, not
assumed:

* `readWithPadding_toList` — a padded `ByteArray` read realizes `Mem.readBytes`
  on the byte list, and hence `load_agrees_discharged`: a machine word-load
  agrees with the `Mem` word-load under refinement. This was previously the
  `load_agrees` hypothesis of `MachineMemSpec`; it is now a theorem (resting only
  on the M1 `ffi_zeroes_*` axioms for the zero padding).

The machine **store** side (`ByteArray.write`, a `copySlice`-with-padding into a
growing buffer) turned out *not* to be a wall: `copySlice` is a pure
`extract ++ extract ++ extract`, so it too is characterized. The one new
ingredient is the **encoding bridge** — relating the EVM word encoding
`UInt256.toByteArray` (yet another custom loop, `List.toByteArray` of the
big-endian bytes left-zero-padded to 32) to the model's `Mem.toBytes32`. With it,
`store_refines_discharged` is *proved* (under the realistic machine-address bound
`a.toNat < USize.size`, without which the dest padding would wrap).

So **both** halves are discharged and the whole `Mem` invariant layer transfers to
the real `ByteArray` machine outright — `machine_load_store_self`
(read-after-write) and `machine_load_store_disjoint` (no-aliasing) carry *no*
interface hypothesis, resting only on the M1 `ffi_zeroes_*` axioms. The base case
(`refines_empty`: fresh memory agrees) is proved outright. The only public
additions outside Venom are two `UInt256` codec companions
(`fromBytesBigEndian_toBytesBigEndian`, `toBytesBigEndian_length_le`).
-/

namespace EvmYul.Venom.MemBridge
open EvmYul EvmYul.Venom

/-- Byte accessor for the machine's `ByteArray` memory (`0` past the end). -/
def baByte (ba : ByteArray) (i : Nat) : UInt8 := ba.data.getD i 0

/-- **Refinement:** the List `Mem` model and the machine `ByteArray` agree byte
for byte — the relation the bridge maintains. -/
def MemRefines (m : Mem) (ba : ByteArray) : Prop := ∀ i, Mem.getByte m i = baByte ba i

/-- **Base case (proved):** fresh (empty) memory refines — both read `0`
everywhere. -/
theorem refines_empty : MemRefines [] ByteArray.empty := by
  intro i
  rw [Mem.getByte_past (by simp)]; exact UInt8.toNat_inj.mp rfl

/-- The machine's word store (mirrors `MachineState.writeWord`): `v`'s 32
big-endian bytes written at `a` via `ByteArray.write`. -/
def machineStore (ba : ByteArray) (a v : UInt256) : ByteArray :=
  v.toByteArray.write 0 ba a.toNat 32

/-- The machine's word load (mirrors `lookupMemory`'s content read). -/
def machineLoad (ba : ByteArray) (a : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ba.readWithPadding a.toNat 32))

/-! ## The `ByteArray.toList` keystone

`ByteArray.toList` is a custom accumulator loop (`toList.loop`, prepending
`get!`-bytes from the front then reversing), with no `data.toList`
characterization in core. We prove it by a loop-invariant induction. From here,
all `toList` reasoning goes through the `Array`/`data` API. -/

/-- Loop invariant: `toList.loop bs i r = r.reverse ++ bs.data.toList.drop i`. -/
theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct (bs := bs) with
  | case1 i r hlt ih =>
    rw [ByteArray.toList.loop, if_pos hlt, ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    have hi : i < bs.data.toList.length := by simpa [Array.length_toList] using hlt
    rw [← List.getElem_cons_drop hi]; congr 2
    show bs.data.getD i 0 = bs.data.toList[i]
    rw [Array.getElem_toList]; exact dif_pos hlt
  | case2 i r hge =>
    rw [ByteArray.toList.loop, if_neg hge,
        List.drop_eq_nil_of_le (by simpa [Array.length_toList] using Nat.le_of_not_lt hge),
        List.append_nil]

/-- **Keystone:** `ByteArray.toList` equals `bs.data.toList`. -/
theorem toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]; simp

/-- The byte list has length `ba.size`. -/
theorem toList_length (ba : ByteArray) : ba.toList.length = ba.size := by
  rw [toList_eq_data, Array.length_toList]; rfl

/-! ## `baByte` as `Mem.getByte` on the byte list

This connects machine memory to the whole `getByte` invariant layer: every law
proved in `MemInvariant` about `Mem.getByte` applies to `ba.data.toList`. -/

/-- `baByte` is `Mem.getByte` on the underlying byte array (`data`). -/
theorem baByte_eq_getByte (ba : ByteArray) (i : Nat) :
    baByte ba i = Mem.getByte ba.data.toList i := by
  rw [baByte, Mem.getByte, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]

/-- `baByte` as `Mem.getByte` on `ba.toList` — the form the `getByte` laws use
(every `MemInvariant` lemma about `Mem.getByte` applies to `ba.toList`). -/
theorem baByte_toList (ba : ByteArray) (i : Nat) : baByte ba i = Mem.getByte ba.toList i := by
  rw [baByte_eq_getByte, ← toList_eq_data]

/-- A zero-padding region reads `0` at the byte level — the M1 axiom, in the
bridge's accessor. -/
theorem baByte_zeroes (n : USize) (i : Nat) : baByte (ffi.ByteArray.zeroes n) i = 0 :=
  EvmYul.M1.ffi_zeroes_get n i

/-- ByteArray append, on the byte list. -/
theorem append_toList (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [toList_eq_data, toList_eq_data, toList_eq_data, ByteArray.data_append, Array.toList_append]

/-- A zero-padding region's byte list reads `0` everywhere (M1). -/
theorem getByte_zeroes_toList (n : USize) (i : Nat) :
    Mem.getByte (ffi.ByteArray.zeroes n).toList i = 0 := by
  rw [← baByte_toList]; exact baByte_zeroes n i

/-! ## The machine read realizes `Mem.readBytes`

`readWithPadding` is `readWithoutPadding ++ zeroes` (an `extract` plus M1 zero
padding). Through the keystone and `data_append`/`data_extract`, its byte list is
characterized exactly, and shown to equal the model's `Mem.readBytes`. -/

/-- `readWithoutPadding`'s size, uniformly (the empty branch is `ba.size - off = 0`). -/
theorem readWithoutPadding_size (ba : ByteArray) (off len : Nat) :
    (ba.readWithoutPadding off len).size = min (off + min len ba.size) ba.size - off := by
  rw [ByteArray.readWithoutPadding]
  by_cases h : off ≥ ba.size
  · rw [if_pos h]; show (0 : Nat) = _; omega
  · rw [if_neg h, ByteArray.size_extract]

/-- Reading byte `i` of an `extract` is byte `s+i` of the source (in range). -/
theorem getByte_extract_toList (ba : ByteArray) (s e i : Nat) (h : i < e - s) :
    Mem.getByte (ba.extract s e).toList i = Mem.getByte ba.data.toList (s + i) := by
  rw [toList_eq_data, ByteArray.data_extract, Array.toList_extract, Mem.take_getByte h,
      Mem.drop_getByte]

/-- **Master byte equation.** Byte `i` (`i < len`) of a padded read at `off` is
byte `off+i` of the source list — uniformly: in-range bytes come from the
`extract`, out-of-range bytes are `0` on both sides (zero padding vs. reading
past the end). -/
theorem getByte_readWithPadding_toList (ba : ByteArray) (off len i : Nat)
    (hi : i < len) (hlen : len < 2 ^ 64) :
    Mem.getByte (ba.readWithPadding off len).toList i = Mem.getByte ba.data.toList (off + i) := by
  rw [ByteArray.readWithPadding, if_neg (by omega), append_toList]
  have hrlen : (ba.readWithoutPadding off len).toList.length
      = min (off + min len ba.size) ba.size - off := by
    rw [toList_length, readWithoutPadding_size]
  have hLlen : ba.data.toList.length = ba.size := by rw [Array.length_toList]; rfl
  by_cases hin : off + i < ba.size
  · have hlt : i < (ba.readWithoutPadding off len).toList.length := by rw [hrlen]; omega
    rw [Mem.append_getByte_left hlt, ByteArray.readWithoutPadding, if_neg (by omega)]
    exact getByte_extract_toList ba off (off + min len ba.size) i (by omega)
  · have hge : (ba.readWithoutPadding off len).toList.length ≤ i := by rw [hrlen]; omega
    rw [Mem.append_getByte_right hge, getByte_zeroes_toList,
        Mem.getByte_past (by rw [hLlen]; omega)]

/-- The `⟨a - b⟩ : USize` literal that `readWithPadding` builds for its zero
padding reads back as `a - b` when `a < USize.size` and `b ≤ a` (no wraparound). -/
theorem usize_sub_toNat (a b : Nat) (ha : a < USize.size) (hba : b ≤ a) :
    (⟨a - b⟩ : USize).toNat = a - b := by
  show (BitVec.toNat _) = _
  simp only [BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [show (2 : ℕ) ^ System.Platform.numBits = USize.size from rfl]
  rcases USize.size_eq with hs | hs <;> rw [hs] at ha ⊢
  · rw [Nat.mod_eq_of_lt (show b < 4294967296 by omega),
        Nat.mod_eq_of_lt (show a < 4294967296 by omega)]; omega
  · rw [Nat.mod_eq_of_lt (show b < 18446744073709551616 by omega),
        Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega)]; omega

/-- A padded read produces exactly `len` bytes (`len < USize.size`). -/
theorem readWithPadding_size (ba : ByteArray) (off len : Nat) (hlen : len < USize.size) :
    (ba.readWithPadding off len).size = len := by
  have h264 : len < 2 ^ 64 := lt_of_lt_of_le hlen (by rcases USize.size_eq with h | h <;> omega)
  have hle : (ba.readWithoutPadding off len).size ≤ len := by rw [readWithoutPadding_size]; omega
  rw [ByteArray.readWithPadding, if_neg (by omega), ByteArray.size_append,
      EvmYul.M1.ffi_zeroes_size, usize_sub_toNat len _ hlen hle]; omega

/-- The machine load decodes the byte *list* with the very same
`fromBytesBigEndian` the `Mem` model uses (`fromByteArrayBigEndian` is that ∘
`toList`, definitionally). -/
theorem machineLoad_eq (ba : ByteArray) (a : UInt256) :
    machineLoad ba a
      = UInt256.ofNat (fromBytesBigEndian (ba.readWithPadding a.toNat 32).toList) := rfl

/-- **The machine read realizes `Mem.readBytes`** (`len < USize.size`): the
bridge's padded read agrees, byte for byte, with the model's read. -/
theorem readWithPadding_toList {m : Mem} {ba : ByteArray} (hr : MemRefines m ba)
    (off len : Nat) (hlen : len < USize.size) :
    (ba.readWithPadding off len).toList = m.readBytes off len := by
  have h264 : len < 2 ^ 64 := lt_of_lt_of_le hlen (by rcases USize.size_eq with h | h <;> omega)
  have hsz : (ba.readWithPadding off len).toList.length = len := by
    rw [toList_length, readWithPadding_size ba off len hlen]
  apply Mem.ext_getByte
  · rw [hsz, Mem.readBytes_length]
  · intro i
    by_cases hi : i < len
    · rw [getByte_readWithPadding_toList ba off len i hi h264, Mem.readBytes_getByte, if_pos hi,
          ← baByte_eq_getByte]
      exact (hr (off + i)).symm
    · rw [Mem.getByte_past (by rw [hsz]; omega), Mem.readBytes_getByte, if_neg hi]

/-- **`load_agrees`, proved** (formerly a `MachineMemSpec` hypothesis). A machine
word-load agrees with the `Mem` word-load under refinement — the read half of the
bridge, now resting only on the M1 `ffi_zeroes_*` axioms. -/
theorem load_agrees_discharged {m : Mem} {ba : ByteArray} (hr : MemRefines m ba) (a : UInt256) :
    m.loadWord a = machineLoad ba a := by
  rw [machineLoad_eq, Mem.loadWord, Mem.fromBytes32,
      readWithPadding_toList hr a.toNat 32 (lt_of_lt_of_le (by norm_num) USize.le_size)]

/-! ## The machine store realizes `Mem.storeWord`

`load_agrees` is proved. The machine **store** (`machineStore = ByteArray.write`,
a `copySlice`-with-padding into a growing buffer) is harder but *not* a wall:
`copySlice` is a pure `extract ++ extract ++ extract`, so it too is characterized.
The one new ingredient is relating the EVM word encoding `UInt256.toByteArray` to
the model's `Mem.toBytes32` — the **encoding bridge** below.

`UInt256.toByteArray` is `List.toByteArray` (another custom loop) of the
big-endian bytes, left-zero-padded to 32. We characterize that loop, show the
encoding decodes to `v.toNat` (`fromByteArrayBigEndian_toByteArray`), and conclude
`v.toByteArray.toList = toBytes32 v` by injectivity of the little-endian decoder
`fromBytes'` on equal-length lists. -/

/-- `List.toByteArray`'s accumulator loop builds `r.data ++ l.toArray`. -/
theorem ltba_loop (l : List UInt8) (r : ByteArray) :
    List.toByteArray.loop l r = ⟨r.data ++ l.toArray⟩ := by
  induction l generalizing r with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih =>
    rw [List.toByteArray.loop, ih]; congr 1
    show (r.push b).data ++ bs.toArray = r.data ++ (b :: bs).toArray
    rw [List.toArray_cons]
    show r.data.push b ++ bs.toArray = r.data ++ (#[b] ++ bs.toArray)
    rw [← Array.append_assoc]; congr 1

theorem ltba_toList (l : List UInt8) : l.toByteArray.toList = l := by
  rw [toList_eq_data, List.toByteArray, ltba_loop]; simp

theorem ltba_size (l : List UInt8) : l.toByteArray.size = l.length := by
  rw [← toList_length, ltba_toList]

/-- A zero region's byte list is `replicate n.toNat 0`. -/
theorem zeroes_toList_eq (n : USize) :
    (ffi.ByteArray.zeroes n).toList = List.replicate n.toNat 0 := by
  apply Mem.ext_getByte
  · rw [toList_length, EvmYul.M1.ffi_zeroes_size, List.length_replicate]
  · intro i; rw [getByte_zeroes_toList, Mem.replicate_zero_getByte]

/-- The `⟨k⟩ : USize` literal reads back as `k` (no wraparound, `k < USize.size`). -/
theorem usize_mk_toNat (k : Nat) (h : k < USize.size) : (⟨k⟩ : USize).toNat = k := by
  show (BitVec.toNat _) = _
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [show (2 : ℕ) ^ System.Platform.numBits = USize.size from rfl]
  rcases USize.size_eq with hs | hs <;> rw [hs] at h ⊢ <;> exact Nat.mod_eq_of_lt (by omega)

/-- The `⟨32 - m⟩ : USize` literal (`32` an `OfNat` BitVec literal) reads back as
`32 - m` for `m ≤ 32` — the form `ByteArray.write` builds for its padding.
Reduces to `usize_sub_toNat` after normalizing the `32` literal. -/
theorem usize_32_sub_toNat (m : Nat) (h : m ≤ 32) : (⟨32 - m⟩ : USize).toNat = 32 - m := by
  rw [show (⟨32 - m⟩ : USize) = ⟨(32 : Nat) - m⟩ from by congr 1]
  exact usize_sub_toNat 32 m (lt_of_le_of_lt (by norm_num) USize.le_size) h

/-! ### The little-endian decoder `fromBytes'` -/

theorem fromBytes'_replicate_zero (k : Nat) : fromBytes' (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, fromBytes', ih]; simp

theorem fromBytes'_append_zeros (xs : List UInt8) (k : Nat) :
    fromBytes' (xs ++ List.replicate k 0) = fromBytes' xs := by
  induction xs with
  | nil => rw [List.nil_append]; exact fromBytes'_replicate_zero k
  | cons b bs ih => rw [List.cons_append, fromBytes', fromBytes', ih]

/-- `fromBytes'` is injective on equal-length byte lists (mod 256 recovers the
head, `/256` the tail). -/
theorem fromBytes'_inj : ∀ (l1 l2 : List UInt8), l1.length = l2.length →
    fromBytes' l1 = fromBytes' l2 → l1 = l2
  | [], [], _, _ => rfl
  | b1 :: bs1, b2 :: bs2, hlen, heq => by
    rw [fromBytes', fromBytes'] at heq
    have hb1 : b1.toFin.val < 256 := by have := b1.toFin.isLt; simpa using this
    have hb2 : b2.toFin.val < 256 := by have := b2.toFin.isLt; simpa using this
    have hbv : b1.toFin.val = b2.toFin.val := by omega
    have hrest : fromBytes' bs1 = fromBytes' bs2 := by omega
    rw [UInt8.toNat_inj.mp hbv, fromBytes'_inj bs1 bs2 (by simpa using hlen) hrest]

/-! ### The encoding bridge: `v.toByteArray.toList = toBytes32 v` -/

theorem toNat_lt (v : UInt256) : v.toNat < 2 ^ 256 := by
  have := v.val.isLt; simp only [UInt256.toNat, UInt256.size] at this ⊢; exact this

theorem blen_le (v : UInt256) : (toBytesBigEndian v.toNat).length ≤ 32 :=
  toBytesBigEndian_length_le (by have := toNat_lt v; simpa using this)

/-- The EVM word encoding is the big-endian bytes left-zero-padded to 32. -/
theorem toByteArray_toList (v : UInt256) :
    v.toByteArray.toList
      = List.replicate (32 - (toBytesBigEndian v.toNat).length) 0 ++ toBytesBigEndian v.toNat := by
  show (ffi.ByteArray.zeroes ⟨32 - (BE v.toNat).size⟩ ++ BE v.toNat).toList = _
  rw [append_toList, zeroes_toList_eq,
      show (BE v.toNat).size = (toBytesBigEndian v.toNat).length from ltba_size _,
      usize_32_sub_toNat _ (blen_le v),
      show BE v.toNat = (toBytesBigEndian v.toNat).toByteArray from rfl, ltba_toList]

theorem toByteArray_size (v : UInt256) : v.toByteArray.size = 32 := by
  rw [← toList_length, toByteArray_toList, List.length_append, List.length_replicate]
  have := blen_le v; omega

theorem fromByteArrayBigEndian_toByteArray (v : UInt256) :
    fromByteArrayBigEndian v.toByteArray = v.toNat := by
  rw [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp_apply, toByteArray_toList,
      List.reverse_append, List.reverse_replicate, fromBytes'_append_zeros,
      show fromBytes' (toBytesBigEndian v.toNat).reverse
        = fromBytesBigEndian (toBytesBigEndian v.toNat) from rfl,
      fromBytesBigEndian_toBytesBigEndian]

/-- **Encoding bridge:** the EVM word encoding (`UInt256.toByteArray`) agrees,
byte for byte, with the model's `Mem.toBytes32`. Both decode to `v.toNat` under
the length-32-injective `fromBytes'`. -/
theorem toByteArray_toList_eq_toBytes32 (v : UInt256) :
    v.toByteArray.toList = Mem.toBytes32 v := by
  apply List.reverse_injective
  apply fromBytes'_inj
  · rw [List.length_reverse, List.length_reverse, Mem.toBytes32_length, toList_length,
        toByteArray_size]
  · rw [show fromBytes' (v.toByteArray.toList).reverse = fromByteArrayBigEndian v.toByteArray
          from rfl,
        show fromBytes' (Mem.toBytes32 v).reverse = fromBytesBigEndian (Mem.toBytes32 v) from rfl,
        fromByteArrayBigEndian_toByteArray, Mem.fromBytesBigEndian_toBytes32]

/-- The encoding bridge, in the `baByte` accessor. -/
theorem baByte_toByteArray (v : UInt256) (j : Nat) :
    baByte v.toByteArray j = Mem.getByte (Mem.toBytes32 v) j := by
  rw [baByte_toList, toByteArray_toList_eq_toBytes32]

/-! ### `copySlice` and `ByteArray.write` byte characterization -/

/-- `copySlice` is a pure `extract ++ extract ++ extract` — not opaque. -/
theorem copySlice_eq (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) :
    src.copySlice srcOff dest destOff len
      = dest.extract 0 destOff ++ src.extract srcOff (srcOff + len)
        ++ dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  apply ByteArray.ext
  rw [ByteArray.data_append, ByteArray.data_append, ByteArray.data_extract,
      ByteArray.data_extract, ByteArray.data_extract]; rfl

theorem baByte_past (X : ByteArray) (i : Nat) (h : X.size ≤ i) : baByte X i = 0 := by
  rw [baByte_toList, Mem.getByte_past (by rw [toList_length]; exact h)]

/-- Byte `i` of a prefix `extract 0 e` (`i < e`) is byte `i` of the source. -/
theorem baByte_extract_prefix (X : ByteArray) (e i : Nat) (h : i < e) :
    baByte (X.extract 0 e) i = baByte X i := by
  rw [baByte_toList, getByte_extract_toList X 0 e i (by omega), Nat.zero_add, baByte_eq_getByte]

/-- Byte `i` of a suffix `extract s X.size` is byte `s+i` of the source (`0` past
the end on both sides). -/
theorem baByte_extract_suffix (X : ByteArray) (s i : Nat) :
    baByte (X.extract s X.size) i = baByte X (s + i) := by
  rw [baByte_toList]
  by_cases h : i < X.size - s
  · rw [getByte_extract_toList X s X.size i h, baByte_eq_getByte]
  · rw [Mem.getByte_past (by rw [toList_length, ByteArray.size_extract]; omega),
        baByte_past X (s + i) (by omega)]

theorem baByte_append (X Y : ByteArray) (i : Nat) :
    baByte (X ++ Y) i = if i < X.size then baByte X i else baByte Y (i - X.size) := by
  rw [baByte_eq_getByte, ← toList_eq_data, append_toList]
  by_cases h : i < X.size
  · rw [Mem.append_getByte_left (by rw [toList_length]; exact h), if_pos h,
        baByte_eq_getByte, toList_eq_data]
  · rw [Mem.append_getByte_right (by rw [toList_length]; omega), if_neg h, toList_length,
        baByte_eq_getByte, toList_eq_data]

/-- Appending a zero region is invisible to `baByte` (the source already reads
`0` past its end). -/
theorem baByte_append_zeroes (X : ByteArray) (n : USize) (i : Nat) :
    baByte (X ++ ffi.ByteArray.zeroes n) i = baByte X i := by
  rw [baByte_append]
  by_cases h : i < X.size
  · rw [if_pos h]
  · rw [if_neg h, baByte_zeroes, baByte_past X i (by omega)]

/-- The machine word store as a `copySlice` (`source.size = 32`, the source
padding length collapses to `0`). -/
theorem machineStore_eq (ba : ByteArray) (a v : UInt256) :
    machineStore ba a v
      = (v.toByteArray ++ ffi.ByteArray.zeroes ⟨(0 : ℕ)⟩).copySlice 0
          (ba ++ ffi.ByteArray.zeroes ⟨(a.toNat - ba.size : ℕ)⟩) a.toNat 32 := by
  rw [machineStore, ByteArray.write, if_neg (by decide), if_neg (by rw [toByteArray_size]; omega)]
  simp only [toByteArray_size, Nat.sub_zero, Nat.min_self,
    Nat.sub_eq_zero_of_le (Nat.min_le_right ba.size (a.toNat + 32)), Nat.add_zero]

/-- **The store grows memory to cover its slot**: `MSTORE`'s `ByteArray.write`
extends memory to at least `a + 32` (the physical `memory.size` half of the spill
zero-guard). Rests on the M1 `ffi_zeroes_*` (the dest padding). -/
theorem machineStore_size_ge (ba : ByteArray) (a v : UInt256) (ha : a.toNat < USize.size) :
    a.toNat + 32 ≤ (machineStore ba a v).size := by
  rw [machineStore_eq, copySlice_eq]
  have hsrc : (v.toByteArray ++ ffi.ByteArray.zeroes ⟨(0 : ℕ)⟩).size = 32 := by
    rw [ByteArray.size_append, toByteArray_size, EvmYul.M1.ffi_zeroes_size,
        usize_mk_toNat 0 (by have := USize.le_size; omega)]
  have hdest : (ba ++ ffi.ByteArray.zeroes ⟨(a.toNat - ba.size : ℕ)⟩).size = max ba.size a.toNat := by
    rw [ByteArray.size_append, EvmYul.M1.ffi_zeroes_size, usize_mk_toNat _ (by omega)]; omega
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, hsrc, hdest]
  omega

/-- **The machine store characterized** (`a.toNat < USize.size`, so the dest
padding does not wrap): the `[a, a+32)` window holds `toBytes32 v`, everything
else is unchanged from `ba`. The three `copySlice` segments — `dest`-prefix,
`src`-window, `dest`-suffix — realize exactly the `Mem.writeBytes` splice. -/
theorem machineStore_char (ba : ByteArray) (a v : UInt256) (i : Nat) (ha : a.toNat < USize.size) :
    baByte (machineStore ba a v) i
      = if a.toNat ≤ i ∧ i < a.toNat + 32 then Mem.getByte (Mem.toBytes32 v) (i - a.toNat)
        else baByte ba i := by
  rw [machineStore_eq, copySlice_eq]
  have hsrc : (v.toByteArray ++ ffi.ByteArray.zeroes ⟨(0 : ℕ)⟩).size = 32 := by
    rw [ByteArray.size_append, toByteArray_size, EvmYul.M1.ffi_zeroes_size,
        usize_mk_toNat 0 (by have := USize.le_size; omega)]
  have hdest : (ba ++ ffi.ByteArray.zeroes ⟨(a.toNat - ba.size : ℕ)⟩).size = max ba.size a.toNat := by
    rw [ByteArray.size_append, EvmYul.M1.ffi_zeroes_size, usize_mk_toNat _ (by omega)]; omega
  rw [hsrc, Nat.sub_zero, Nat.min_self]
  set destBA := ba ++ ffi.ByteArray.zeroes ⟨(a.toNat - ba.size : ℕ)⟩ with hdef
  set srcBA := v.toByteArray ++ ffi.ByteArray.zeroes ⟨(0 : ℕ)⟩ with hsdef
  have hs1 : (destBA.extract 0 a.toNat).size = a.toNat := by
    rw [ByteArray.size_extract, hdest]; omega
  have hs2 : (srcBA.extract 0 (0 + 32)).size = 32 := by rw [ByteArray.size_extract, hsrc]; omega
  rw [baByte_append, baByte_append, ByteArray.size_append, hs1, hs2]
  by_cases h1 : i < a.toNat
  · rw [if_pos (by omega), if_pos h1, baByte_extract_prefix _ _ _ h1, hdef, baByte_append_zeroes,
        if_neg (by omega)]
  · by_cases h2 : i < a.toNat + 32
    · rw [if_pos (by omega), if_neg h1, baByte_extract_prefix _ _ _ (by omega),
          hsdef, baByte_append_zeroes, baByte_toByteArray, if_pos (by omega)]
    · rw [if_neg h2, baByte_extract_suffix,
          show a.toNat + 32 + (i - (a.toNat + 32)) = i from by omega,
          hdef, baByte_append_zeroes, if_neg (by omega)]

/-- **`store_refines`, proved** (`a.toNat < USize.size`, the machine address
bound) — formerly the `MachineMemSpec` hypothesis. A machine word-store realizes
the `Mem` word-store under refinement. With `load_agrees_discharged`, the whole
`MachineMemSpec` interface is discharged; the bridge rests only on the M1
`ffi_zeroes_*` axioms. -/
theorem store_refines_discharged {m : Mem} {ba : ByteArray} (a v : UInt256)
    (ha : a.toNat < USize.size) (hr : MemRefines m ba) :
    MemRefines (m.storeWord a v) (machineStore ba a v) := by
  intro i
  rw [Mem.storeWord, Mem.writeBytes_getByte, Mem.toBytes32_length, machineStore_char ba a v i ha]
  by_cases hw : a.toNat ≤ i ∧ i < a.toNat + 32
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw]; exact hr i

/-! ## The `Mem` invariant layer transfers to the real machine (axiom-only)

Both halves are proved, so the `Mem` laws hold on the real `ByteArray` machine
outright — no interface hypothesis, resting only on the M1 `ffi_zeroes_*` axioms
(and the realistic machine-address bound `a.toNat < USize.size`). -/

/-- **Machine read-after-write** — reading back the word just stored returns it,
on the real machine, unconditionally. -/
theorem machine_load_store_self {m : Mem} {ba : ByteArray} (a v : UInt256)
    (ha : a.toNat < USize.size) (hr : MemRefines m ba) :
    machineLoad (machineStore ba a v) a = v := by
  rw [← load_agrees_discharged (store_refines_discharged a v ha hr) a,
      Mem.loadWord_storeWord_self']

/-- **Machine no-aliasing** — a store to `a` does not disturb a disjoint word `b`,
on the real machine, unconditionally. -/
theorem machine_load_store_disjoint {m : Mem} {ba : ByteArray} (a v b : UInt256)
    (ha : a.toNat < USize.size) (hr : MemRefines m ba)
    (hdisj : a.toNat + 32 ≤ b.toNat ∨ b.toNat + 32 ≤ a.toNat) :
    machineLoad (machineStore ba a v) b = machineLoad ba b := by
  rw [← load_agrees_discharged (store_refines_discharged a v ha hr) b,
      ← load_agrees_discharged hr b, Mem.loadWord_storeWord_disjoint m a v b hdisj]

/-! ## The real EVM `MachineState` memory (M4 spill, machine level)

The machine laws above transfer to the *actual* EVM memory ops: `MachineState`'s
`writeWord` (what `MSTORE` runs) IS `machineStore`, and `lookupMemory` (what
`MLOAD` runs), off its zero-guard, IS `machineLoad`. So a value `MSTORE`d to a
slot and `MLOAD`ed back returns it — register spilling, on the real machine —
given the slot is active (which `MSTORE` ensures by expanding `activeWords`) and
the address fits a machine word. -/

/-- Any `ByteArray` is refined by its own byte list (the canonical refinement). -/
theorem memRefines_self (ba : ByteArray) : MemRefines ba.data.toList ba :=
  fun i => (baByte_eq_getByte ba i).symm

/-- `MachineState.writeWord` (the `MSTORE` memory effect) is `machineStore`. -/
theorem writeWord_memory (self : MachineState) (a v : UInt256) :
    (self.writeWord a v).memory = machineStore self.memory a v := rfl

/-- **The real EVM memory round-trips (M4 spill at the MachineState level).** A
value `v` stored to slot `a` via `MSTORE` (`writeWord`) and read back via `MLOAD`
(`lookupMemory`) returns `v` — given the slot is *active* (past the zero-guard)
and the address fits a machine word. Rests on the discharged
`machine_load_store_self`. -/
theorem lookupMemory_writeWord_self (self : MachineState) (a v : UInt256)
    (ha : a.toNat < USize.size)
    (hguard : ¬ (a.toNat ≥ (self.writeWord a v).memory.size
                 ∨ a ≥ (self.writeWord a v).activeWords * ⟨32⟩)) :
    (self.writeWord a v).lookupMemory a = v := by
  rw [MachineState.lookupMemory, if_neg hguard]
  show machineLoad (self.writeWord a v).memory a = v
  rw [writeWord_memory]
  exact machine_load_store_self a v ha (memRefines_self self.memory)

/-- **EVM spill survives a disjoint write (M4 frame, MachineState level).** A
value spilled to `spill` survives a later `MSTORE` to a disjoint slot `other`. -/
theorem lookupMemory_writeWord_frame (self : MachineState) (spill other v w : UInt256)
    (ha : spill.toNat < USize.size) (hb : other.toNat < USize.size)
    (hdisj : spill.toNat + 32 ≤ other.toNat ∨ other.toNat + 32 ≤ spill.toNat)
    (hguard : ¬ (spill.toNat ≥ ((self.writeWord spill v).writeWord other w).memory.size
                 ∨ spill ≥ ((self.writeWord spill v).writeWord other w).activeWords * ⟨32⟩)) :
    ((self.writeWord spill v).writeWord other w).lookupMemory spill = v := by
  rw [MachineState.lookupMemory, if_neg hguard]
  show machineLoad ((self.writeWord spill v).writeWord other w).memory spill = v
  rw [writeWord_memory, writeWord_memory,
      machine_load_store_disjoint other w spill hb (memRefines_self _) (by omega)]
  exact machine_load_store_self spill v ha (memRefines_self _)

end EvmYul.Venom.MemBridge

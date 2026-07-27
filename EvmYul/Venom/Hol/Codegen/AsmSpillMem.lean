/-
Asm Spill Memory Laws — Stage 2 of the spill/restore infrastructure

Derives the asm-level memory frame laws needed by `doSpillAt_sim` / `doRestore_sim`
from the `ByteArray` frame axioms in `Hol/CoreAxioms.lean`:
  - `readByte_write_disjoint`  — single-byte frame  (for `memoryRel`)
  - `readWithPadding_write_disjoint` re-export      (for `planSpillRel`)
  - `asmExpandMemory` preservation                  (expansion is a disjoint write)
-/

import EvmYul.Venom.Hol.CoreAxioms
import EvmYul.Venom.Hol.VenomMemProps
import EvmYul.Venom.Hol.Codegen.AsmSem
import EvmYul.Venom.Hol.Codegen.CodegenRel
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/-- `readByte` written in `getElem?` form, so the primitive frame axiom applies. -/
theorem readByte_eq_getElem?_getD (i : Nat) (mem : ByteArray) :
    readByte i mem = (mem[i]?).getD 0 := by
  unfold readByte
  split
  · next h => rw [getElem?_pos mem i h]; rfl
  · next h => rw [getElem?_neg mem i h]; rfl

/-- **Single-byte disjoint frame.** A `readByte` outside the written region is
    untouched by `ByteArray.write` (derived from `byteArray_write_getElem?_disjoint`).
    This is the `memoryRel` building block. Needs `off ≤ dest.size` (target covers the
    write start — true at every call site, where `dest` is the expanded memory). -/
theorem readByte_write_disjoint (source dest : ByteArray) (off i : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size)
    (hdisj : i < off ∨ off + source.size ≤ i) :
    readByte i (source.write 0 dest off source.size) = readByte i dest := by
  rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD,
      EvmYul.byteArray_write_getElem?_disjoint source dest off i hpos hoff hdisj]

/-! ### Spill roundtrip + expansion no-op -/

/-- **Spill roundtrip.** Writing `wordToBytes v` at `off` and reading the same
    32-byte window straight back recovers `v`. This is the `planSpillRel` fact
    for a freshly-spilled value: `asmMstore` leaves exactly this written memory,
    and `planSpillRel` reads it directly (no re-expansion involved). -/
theorem asm_spill_roundtrip (v : bytes32) (dest : ByteArray) (off : Nat) (hoff : off ≤ dest.size) :
    wordOfBytes (((wordToBytes v).write 0 dest off 32).readWithPadding off 32) = v := by
  have hlen : (wordToBytes v).size = 32 := length_wordToBytes v
  rw [← hlen, EvmYul.byteArray_write_read (wordToBytes v) dest off (by rw [hlen]; norm_num)
        (by rcases USize.size_eq with h | h <;> omega) (by rw [hlen]; norm_num)]
  exact wordOfBytes_wordToBytes v

/-- **MSTORE disjoint frame.** Writing a word at slot `off` leaves a disjoint
    32-byte window at `off'` unchanged (size-bridged form of the window frame
    axiom, with `(wordToBytes value).size = 32`). -/
theorem mstore_readWithPadding_frame (value : bytes32) (mem : ByteArray) (off off' : Nat)
    (hoff : off ≤ mem.size) (hdisj : off' + 32 ≤ off ∨ off + 32 ≤ off') :
    ((wordToBytes value).write 0 mem off 32).readWithPadding off' 32
      = mem.readWithPadding off' 32 := by
  have hsz : (wordToBytes value).size = 32 := length_wordToBytes value
  have h := EvmYul.byteArray_readWithPadding_write_disjoint (wordToBytes value) mem off off' 32
    (by rw [hsz]; norm_num) hoff (by rcases USize.size_eq with h | h <;> omega) (by rw [hsz]; exact hdisj)
  rwa [hsz] at h

/-- **MSTORE single-byte frame.** Writing a word at `off` leaves byte `i` (outside
    `[off, off+32)`) unchanged — the `memoryRel` building block for spill. -/
theorem mstore_readByte_frame (value : bytes32) (mem : ByteArray) (off i : Nat)
    (hoff : off ≤ mem.size) (hdisj : i < off ∨ off + 32 ≤ i) :
    readByte i ((wordToBytes value).write 0 mem off 32) = readByte i mem := by
  have hsz : (wordToBytes value).size = 32 := length_wordToBytes value
  have h := readByte_write_disjoint (wordToBytes value) mem off i
    (by rw [hsz]; norm_num) hoff (by rw [hsz]; exact hdisj)
  rwa [hsz] at h

/-- **Write congruence (byte level).** Two memories agreeing at index `i` still agree
    at `i` after the *same* `source` is written at the *same* `off` (both covering the
    write start, `off ≤ size`). In-window bytes come from `source` (identical on both
    sides via `byteArray_write_getElem?_inWindow`); out-window bytes come from the
    underlying memories (equal by hypothesis via `readByte_write_disjoint`). This is the
    `memoryRel` building block for a user `MSTORE`: the Venom and asm memories, equal
    outside the spill region, stay equal there after the identical store. -/
theorem readByte_write_congr (source m1 m2 : ByteArray) (off i : Nat)
    (hpos : 0 < source.size) (h1 : off ≤ m1.size) (h2 : off ≤ m2.size)
    (hcongr : readByte i m1 = readByte i m2) :
    readByte i (source.write 0 m1 off source.size)
      = readByte i (source.write 0 m2 off source.size) := by
  by_cases hwin : off ≤ i ∧ i < off + source.size
  · rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD,
        EvmYul.byteArray_write_getElem?_inWindow source m1 off i hpos h1 hwin,
        EvmYul.byteArray_write_getElem?_inWindow source m2 off i hpos h2 hwin]
  · push Not at hwin
    have hdisj : i < off ∨ off + source.size ≤ i := by
      rcases Nat.lt_or_ge i off with h | h
      · exact Or.inl h
      · exact Or.inr (hwin h)
    rw [readByte_write_disjoint source m1 off i hpos h1 hdisj,
        readByte_write_disjoint source m2 off i hpos h2 hdisj]
    exact hcongr

/-- **MSTORE memory congruence (32-byte specialisation).** The `memoryRel`-shaped form
    of `readByte_write_congr` for a word store: writing `wordToBytes value` at `off` to
    two `i`-agreeing memories keeps them agreeing at `i`. -/
theorem mstore_readByte_congr (value : bytes32) (m1 m2 : ByteArray) (off i : Nat)
    (h1 : off ≤ m1.size) (h2 : off ≤ m2.size)
    (hcongr : readByte i m1 = readByte i m2) :
    readByte i ((wordToBytes value).write 0 m1 off 32)
      = readByte i ((wordToBytes value).write 0 m2 off 32) := by
  have hsz : (wordToBytes value).size = 32 := length_wordToBytes value
  have h := readByte_write_congr (wordToBytes value) m1 m2 off i (by rw [hsz]; norm_num) h1 h2 hcongr
  rwa [hsz] at h

/-- **`memoryRel` window read agreement (below the spill region).** If the Venom and asm
    memories agree outside the spill region (`memoryRel`) and the window `[off, off+len)` lies
    below `fnEom` (so every byte of it is outside `[fnEom, nextOffset)`), they read the same
    `len`-byte window. The `returndata = memory-slice` half of the `RETURN`/`REVERT` terminal
    sim: the returned slice is user memory below the spill region, so it matches byte-for-byte. -/
theorem memoryRel_readWithPadding_slice {alloc : SpillAlloc} {m1 m2 : ByteArray} {off len : Nat}
    (hmem : memoryRel alloc m1 m2)
    (hbelow : off + len ≤ alloc.fnEom)
    (hlen : len < USize.size) :
    m1.readWithPadding off len = m2.readWithPadding off len := by
  apply ByteArray.readWithPadding_congr m1 m2 off len hlen
  intro k hk
  have hb := hmem (off + k) (by rintro ⟨h1, _⟩; omega)
  rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at hb
  exact hb

/-- When memory already covers the rounded request, `asmExpandMemory` is a no-op. -/
theorem asmExpandMemory_of_covered (needed : Nat) (mem : ByteArray)
    (h : ((needed + 31) / 32) * 32 ≤ mem.size) :
    asmExpandMemory needed mem = mem := by
  simp [asmExpandMemory, h]

/-- **Expansion is `readByte`-invariant**: `asmExpandMemory` only appends zero bytes, and
    `readByte` zero-pads past the end anyway. -/
theorem readByte_asmExpandMemory (i n : Nat) (mem : ByteArray)
    (hro : ((n + 31) / 32) * 32 < USize.size) :
    readByte i (asmExpandMemory n mem) = readByte i mem := by
  unfold asmExpandMemory
  by_cases h : ((n + 31) / 32) * 32 ≤ mem.size
  · simp only [h, if_true]
  · simp only [h, if_false]
    have hpadsz : (ffi.ByteArray.zeroes ⟨(↑((n + 31) / 32 * 32) - ↑mem.size : BitVec System.Platform.numBits)⟩).size
        = (n + 31) / 32 * 32 - mem.size :=
      ByteArray.zeroes_bvsub_size ((n + 31) / 32 * 32) mem.size (by omega) hro
    set pad := ffi.ByteArray.zeroes ⟨(↑((n + 31) / 32 * 32) - ↑mem.size : BitVec System.Platform.numBits)⟩ with hpad
    have hkpos : 0 < pad.size := by rw [hpadsz]; omega
    have hlen : pad.write 0 mem mem.size ((n + 31) / 32 * 32 - mem.size)
        = pad.write 0 mem mem.size pad.size := by rw [hpadsz]
    rw [hlen, readByte_eq_getElem?_getD, readByte_eq_getElem?_getD]
    by_cases hi : i < mem.size
    · rw [EvmYul.byteArray_write_getElem?_disjoint pad mem mem.size i hkpos (Nat.le_refl _) (Or.inl hi)]
    · by_cases hi2 : i < mem.size + pad.size
      · rw [EvmYul.byteArray_write_getElem?_inWindow pad mem mem.size i hkpos (Nat.le_refl _) ⟨by omega, hi2⟩,
            ByteArray.zeroes_getElem? _ _ (by rw [hpadsz]; omega),
            getElem?_neg mem i (by omega)]
        rfl
      · rw [EvmYul.byteArray_write_getElem?_disjoint pad mem mem.size i hkpos (Nat.le_refl _) (Or.inr (by omega))]

/-- A 32-aligned offset rounds `off + 32` exactly: `⌈(off+32)/32⌉·32 = off + 32`. -/
theorem rounded_add_32_of_aligned {off : Nat} (halign : 32 ∣ off) :
    ((off + 32 + 31) / 32) * 32 = off + 32 := by
  obtain ⟨k, rfl⟩ := halign
  omega

/-- **Restore read.** Restoring from a 32-aligned, in-range spill slot reads back
    exactly what `planSpillRel` recorded: the `asmExpandMemory` in `asmMload`
    is a no-op here (the slot is already covered), so the value is unchanged. -/
theorem asm_restore_read (mem : ByteArray) (off : Nat)
    (halign : 32 ∣ off) (hcov : off + 32 ≤ mem.size) :
    wordOfBytes ((asmExpandMemory (off + 32) mem).readWithPadding off 32)
      = wordOfBytes (mem.readWithPadding off 32) := by
  rw [asmExpandMemory_of_covered (off + 32) mem
        (by rw [rounded_add_32_of_aligned halign]; exact hcov)]

/-! ### S3 — spill allocator well-formedness

`allocSpillSlot` hands out either `nextOffset` (then bumps it by 32) or reuses the
last free slot. `SpillAllocWf` is the invariant making every handed-out offset
32-aligned and inside the spill region `[fnEom, nextOffset)`. Disjointness of the
fresh slot from the *currently-spilled* set is an S4 concern (it needs the
`spilled` map, not just the allocator); here we establish alignment + region. -/

/-- Spill-allocator well-formedness: aligned base/top, ordered, and every free
    slot 32-aligned and inside the spill region. -/
structure SpillAllocWf (alloc : SpillAlloc) : Prop where
  align_fnEom : 32 ∣ alloc.fnEom
  align_next  : 32 ∣ alloc.nextOffset
  fnEom_le    : alloc.fnEom ≤ alloc.nextOffset
  free_aligned : ∀ s ∈ alloc.freeSlots, 32 ∣ s
  free_region  : ∀ s ∈ alloc.freeSlots, alloc.fnEom ≤ s ∧ s + 32 ≤ alloc.nextOffset

/-- `getLastD` of a non-empty list is a member. -/
theorem getLastD_mem {α} {l : List α} (d : α) (h : l ≠ []) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?]
  cases hl : l.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; exact absurd hl h
  | some a => exact List.mem_of_getLast? hl

/-- The offset `allocSpillSlot` hands out is 32-aligned. -/
theorem allocSpillSlot_aligned {alloc} (hwf : SpillAllocWf alloc) :
    32 ∣ (allocSpillSlot alloc).1 := by
  rcases hfs : alloc.freeSlots with _ | ⟨a, t⟩
  · simp only [allocSpillSlot, hfs]; exact hwf.align_next
  · simp only [allocSpillSlot, hfs]
    apply hwf.free_aligned
    rw [hfs]; exact getLastD_mem 0 (by simp)

/-- The offset `allocSpillSlot` hands out lies in the spill region of the
    *updated* allocator: `fnEom ≤ off` and `off + 32 ≤ newNextOffset`. -/
theorem allocSpillSlot_region {alloc} (hwf : SpillAllocWf alloc) :
    alloc.fnEom ≤ (allocSpillSlot alloc).1 ∧
    (allocSpillSlot alloc).1 + 32 ≤ (allocSpillSlot alloc).2.nextOffset := by
  rcases hfs : alloc.freeSlots with _ | ⟨a, t⟩
  · simp only [allocSpillSlot, hfs]; exact ⟨hwf.fnEom_le, by omega⟩
  · simp only [allocSpillSlot, hfs]
    have hmem : (a :: t).getLastD 0 ∈ alloc.freeSlots := by rw [hfs]; exact getLastD_mem 0 (by simp)
    exact hwf.free_region _ hmem

/-- `allocSpillSlot` preserves well-formedness. -/
theorem allocSpillSlot_wf {alloc} (hwf : SpillAllocWf alloc) :
    SpillAllocWf (allocSpillSlot alloc).2 := by
  rcases hfs : alloc.freeSlots with _ | ⟨a, t⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [allocSpillSlot, hfs]
    · exact hwf.align_fnEom
    · exact Dvd.dvd.add hwf.align_next ⟨1, rfl⟩
    · have := hwf.fnEom_le; omega
    · simp [hfs]
    · simp [hfs]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [allocSpillSlot, hfs]
    · exact hwf.align_fnEom
    · exact hwf.align_next
    · exact hwf.fnEom_le
    · intro s hs
      exact hwf.free_aligned s (hfs ▸ List.mem_of_mem_dropLast (hfs ▸ hs))
    · intro s hs
      exact hwf.free_region s (hfs ▸ List.mem_of_mem_dropLast (hfs ▸ hs))

/-- `allocSpillSlot` leaves `fnEom` unchanged. -/
theorem allocSpillSlot_fnEom (alloc : SpillAlloc) :
    (allocSpillSlot alloc).2.fnEom = alloc.fnEom := by
  rcases hfs : alloc.freeSlots with _ | ⟨a, t⟩ <;> simp [allocSpillSlot, hfs]

/-- `allocSpillSlot` never lowers `nextOffset`. -/
theorem allocSpillSlot_nextOffset_ge (alloc : SpillAlloc) :
    alloc.nextOffset ≤ (allocSpillSlot alloc).2.nextOffset := by
  rcases hfs : alloc.freeSlots with _ | ⟨a, t⟩ <;> simp [allocSpillSlot, hfs]

/-! ### S4a — the pushed offset denotes the right slot

`SOSpill off` / `SORestore off` lower to `PUSH (encodeNumBytes off); MSTORE/MLOAD`.
After the AsmPush fix, the pushed word's `.toNat` is exactly `off` (for `off < 2^256`),
so `MSTORE`/`MLOAD` hit the slot `planSpillRel` records. -/

/-- `fromBytesBigEndian (E ++ [b]) = b + 2^8 · fromBytesBigEndian E`. -/
theorem fromBytesBigEndian_append_singleton (E : List UInt8) (b : UInt8) :
    EvmYul.fromBytesBigEndian (E ++ [b]) = b.toNat + 2 ^ 8 * EvmYul.fromBytesBigEndian E := by
  unfold EvmYul.fromBytesBigEndian
  simp only [Function.comp_apply, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, EvmYul.fromBytes']
  rfl

/-- `encodeNumBytes` round-trips through `fromBytesBigEndian`. -/
theorem fromBytesBigEndian_encodeNumBytes (n : Nat) :
    EvmYul.fromBytesBigEndian (encodeNumBytes n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encodeNumBytes]
    split
    · next h => subst h; rfl
    · next h =>
      have hpos : 0 < n := Nat.pos_of_ne_zero h
      rw [fromBytesBigEndian_append_singleton,
          ih (n / 256) (Nat.div_lt_self hpos (by norm_num))]
      have hb : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
        have : n % 256 < 256 := Nat.mod_lt _ (by norm_num)
        simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt this]
      have h256 : (2 : Nat) ^ 8 = 256 := by norm_num
      rw [hb, h256]; omega

/-- Zero-padding a big-endian byte list on the **left** preserves its value. -/
theorem fromBytesBigEndian_zero_prefix (k : Nat) (E : List UInt8) :
    EvmYul.fromBytesBigEndian (List.replicate k 0 ++ E) = EvmYul.fromBytesBigEndian E := by
  unfold EvmYul.fromBytesBigEndian
  simp only [Function.comp_apply, List.reverse_append, List.reverse_replicate]
  rw [EvmYul.extend_bytes_zero]

/-- **The pushed offset is faithful.** `AsmPush (encodeNumBytes off)` (left-padded
    to 32 bytes by the fixed `asmStep`) pushes a word whose `.toNat` is exactly
    `off`, for any `off < 2^256`. This is what makes `SOSpill`/`SORestore` hit the
    slot that `planSpillRel` records. -/
theorem pushed_offset_toNat (off : Nat) (hoff : off < 2 ^ 256) :
    (wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes off).length) 0
                    ++ encodeNumBytes off))).toNat = off := by
  unfold wordOfBytes
  rw [EvmYul.uint256_ofNat_toNat, EvmYul.toByteArray_toList,
      fromBytesBigEndian_zero_prefix, fromBytesBigEndian_encodeNumBytes]
  exact Nat.mod_eq_of_lt hoff

/-! ### S4b — `planStackRel` is preserved by pushing an operand

Pushing operand `op` (value `v`) on the plan stack (LAST=TOS, so append) and the
matching value `v` on the asm stack (HD=TOS, so cons) preserves `planStackRel`. -/

theorem planStackRel_push {labelOffsets vs stk A op v}
    (h : planStackRel labelOffsets vs stk A)
    (hv : operandVal vs labelOffsets op = some v) :
    planStackRel labelOffsets vs (stackPush op stk) (v :: A) := by
  obtain ⟨hlen, hrel⟩ := h
  refine ⟨by simp [stackPush, hlen], ?_⟩
  intro i hi
  have hilen : i < stk.length + 1 := by simpa [stackPush] using hi
  rw [stackPush, List.reverse_append, List.reverse_singleton, List.singleton_append]
  rcases i with _ | j
  · simpa using hv
  · have hj : j < stk.length := by omega
    simpa using hrel j hj

/-- `planStackRel` is preserved by a `DUP` at distance `dist`: venom `stackDup dist`
    (copy the element at depth `dist` to TOS) corresponds to asm pushing `asmStack[dist]`
    (HD = TOS). The DUP analog of `planStackRel_swap`, built from `planStackRel_peek`
    (the duplicated operand evaluates to `asmStack[dist]`) and `planStackRel_push`. -/
theorem planStackRel_dup {labelOffsets vs psStack asmStack dist}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (hdist : dist < psStack.length) :
    planStackRel labelOffsets vs (stackDup dist psStack)
      (asmStack[dist]! :: asmStack) := by
  have hpeek : operandVal vs labelOffsets (stackPeek dist psStack) = some (asmStack[dist]!) :=
    planStackRel_peek hrel hdist
  have h_push := planStackRel_push hrel hpeek
  simpa [stackDup, stackPush] using h_push

/-- Clean dual of `planStackRel_push`: dropping the just-pushed `op`/`v` pair. -/
theorem planStackRel_pop' {labelOffsets vs stk op v A}
    (h : planStackRel labelOffsets vs (stk ++ [op]) (v :: A)) :
    planStackRel labelOffsets vs stk A := by
  obtain ⟨hlen, hrel⟩ := h
  have hlen' : stk.length = A.length := by simpa using hlen
  refine ⟨hlen', ?_⟩
  intro i hi
  have hib : i + 1 < (stk ++ [op]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hpair := hrel (i + 1) hib
  rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at hpair
  simpa using hpair

/-- `planStackRel` is preserved by popping the top of the stack
    (plan `stackPop 1` ↔ asm cons-tail). -/
theorem planStackRel_pop {labelOffsets vs stk a A}
    (h : planStackRel labelOffsets vs stk (a :: A)) :
    planStackRel labelOffsets vs (stackPop 1 stk) A := by
  have hlen := h.1
  have hne : stk ≠ [] := by intro he; rw [he] at hlen; simp at hlen
  have hpop : stackPop 1 stk = stk.dropLast := by rw [stackPop, List.dropLast_eq_take]
  rw [hpop]
  apply planStackRel_pop' (op := stk.getLast hne) (v := a)
  rwa [List.dropLast_append_getLast hne]

/-- `get!` commutes with `drop` by an index shift. -/
theorem getI_drop_add {α : Type} [Inhabited α] (l : List α) (n i : Nat) :
    (l.drop n)[i]! = l[i + n]! := by
  rw [List_get!_eq_getElem?_getD, List_get!_eq_getElem?_getD, List.getElem?_drop, add_comm]

/-- `planStackRel` is preserved by popping the top `n` (the general-`n` companion of
    `planStackRel_pop`): venom `stackPop n` (drop the top `n`) matches asm `drop n`
    (HD = TOS). The plan-side stack-shrink for a regular instruction's consumed inputs. -/
theorem planStackRel_popN {labelOffsets vs psStack asmStack n}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (hn : n ≤ psStack.length) :
    planStackRel labelOffsets vs (stackPop n psStack) (asmStack.drop n) := by
  rcases hrel with ⟨hlen, hget⟩
  have hlen' : (stackPop n psStack).length = (asmStack.drop n).length := by
    simp [stackPop, hlen]
  refine ⟨hlen', fun i hi => ?_⟩
  have h_rev : (psStack.take (psStack.length - n)).reverse = psStack.reverse.drop n := by
    rw [List.reverse_take]
    have : psStack.length - (psStack.length - n) = n := by omega
    rw [this]
  have hi_ps : i + n < psStack.length := by
    rw [stackPop] at hi
    have hi_len : i < (psStack.take (psStack.length - n)).length := hi
    rw [List.length_take] at hi_len; omega
  rw [stackPop, h_rev]
  rw [getI_drop_add psStack.reverse n i, getI_drop_add asmStack n i]
  exact hget (i + n) hi_ps

/-- `planStackRel` after a binary-op emit: the asm pops two and pushes the result `r`
    (`r :: asmStack.drop 2`), while the plan pops the two consumed operands and pushes the
    output var (which evaluates to `r`). Composes `planStackRel_popN` + `planStackRel_push`.
    The stack-rel half of the compute step for a 2-input regular opcode (ADD, …). -/
theorem planStackRel_binop {labelOffsets vs psStack asmStack out r}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (h2 : 2 ≤ psStack.length)
    (hout : operandVal vs labelOffsets (Operand.Var out) = some r) :
    planStackRel labelOffsets vs (stackPush (Operand.Var out) (stackPop 2 psStack))
      (r :: asmStack.drop 2) :=
  planStackRel_push (planStackRel_popN hrel h2) hout

/-- `planStackRel` after a unary-op emit: pop one, push the output var (evaluating to the
    result `r`). The 1-input companion of `planStackRel_binop` (ISZERO, NOT, …). -/
theorem planStackRel_unop {labelOffsets vs psStack asmStack out r}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (h1 : 1 ≤ psStack.length)
    (hout : operandVal vs labelOffsets (Operand.Var out) = some r) :
    planStackRel labelOffsets vs (stackPush (Operand.Var out) (stackPop 1 psStack))
      (r :: asmStack.drop 1) :=
  planStackRel_push (planStackRel_popN hrel h1) hout

/-- `planStackRel` after a ternary-op emit: pop three, push the output var (evaluating to the
    result `r`). The 3-input companion of `planStackRel_binop` (ADDMOD, MULMOD). -/
theorem planStackRel_ternop {labelOffsets vs psStack asmStack out r}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (h3 : 3 ≤ psStack.length)
    (hout : operandVal vs labelOffsets (Operand.Var out) = some r) :
    planStackRel labelOffsets vs (stackPush (Operand.Var out) (stackPop 3 psStack))
      (r :: asmStack.drop 3) :=
  planStackRel_push (planStackRel_popN hrel h3) hout

end EvmYul.Venom.Hol.Codegen

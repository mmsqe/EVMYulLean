import EvmYul.Venom.VenomMemProps

/-!
# A higher-level memory invariant layer (byte-function abstraction)

`VenomMemProps` proves the point facts of the `Mem` (`List UInt8`) model
(read-after-write *at the same address*, overwrite, the adjacent-write keccak
preimage). This file lifts the model to a **byte-function abstraction** and the
algebraic laws of memory, which the point facts are then instances of:

* `getByte m i` — memory as a total byte map (`0` past the written end);
* `writeBytes_getByte` / `readBytes_getByte` — the *characterizations*: a write
  changes exactly its `[offset, offset+len)` window and nothing else, and a read
  is that window of the byte map. Every memory law follows from these two.

The headline new invariant is the **frame / no-aliasing law**
(`readBytes_writeBytes_disjoint`, `loadWord_storeWord_disjoint`): writes to
disjoint regions do not interfere — the memory analogue of the storage `~addr`
no-aliasing (`NoAlias`), and exactly what a compositional memory semantics needs.
Read-after-write (`loadWord_storeWord_self'`) is re-derived here from the same
characterizations, so the two fundamental laws share one foundation.

## Scope

This is the **`Mem`-model** invariant layer — proof-friendly and complete on its
own. Transporting it to the real `ByteArray` machine is the remaining bridge: it
rests on the `M1` FFI axioms (`EvmYul/Venom/FFIMemory.lean`) for the zero-padding
and on `ByteArray.write`/`readWithPadding` (a `copySlice`-with-padding) read/write
characterization — the natural next step, isolated exactly as the SSTORE-erase
(`RBMapEraseSpec`) and M1 boundaries are.
-/

namespace EvmYul.Venom.Mem
open EvmYul.Venom

/-- **Memory as a byte function:** byte `i`, reading `0` past the written end. The
abstraction the whole invariant layer is phrased over. -/
def getByte (m : Mem) (i : Nat) : UInt8 := m.getD i 0

/-- Normal form: `getByte` as `getElem?` then `getD` — the single rewrite all the
foundational lemmas push through. -/
theorem getByte_eq (m : Mem) (i : Nat) : getByte m i = (m[i]?).getD 0 := by
  rw [getByte, List.getD_eq_getElem?_getD]

theorem getByte_past {m : Mem} {i : Nat} (h : m.length ≤ i) : getByte m i = 0 := by
  simp [getByte_eq, List.getElem?_eq_none h]

@[simp] theorem replicate_zero_getByte (k j : Nat) :
    getByte (List.replicate k (0 : UInt8)) j = 0 := by
  rw [getByte_eq]
  rcases Nat.lt_or_ge j k with h | h
  · rw [List.getElem?_replicate]; simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem append_getByte_right {l₁ l₂ : Mem} {i : Nat} (h : l₁.length ≤ i) :
    getByte (l₁ ++ l₂) i = getByte l₂ (i - l₁.length) := by
  simp only [getByte_eq, List.getElem?_append_right h]

theorem append_getByte_left {l₁ l₂ : Mem} {i : Nat} (h : i < l₁.length) :
    getByte (l₁ ++ l₂) i = getByte l₁ i := by
  simp only [getByte_eq, List.getElem?_append_left h]

theorem expand_getByte (m : Mem) (n i : Nat) : getByte (m.expand n) i = getByte m i := by
  rcases Nat.lt_or_ge i m.length with h | h
  · rw [Mem.expand, append_getByte_left h]
  · rw [getByte_past h, Mem.expand, append_getByte_right h, replicate_zero_getByte]

theorem take_getByte {l : Mem} {n i : Nat} (h : i < n) :
    getByte (l.take n) i = getByte l i := by
  simp only [getByte_eq, List.getElem?_take_of_lt h]

theorem drop_getByte (l : Mem) (n i : Nat) : getByte (l.drop n) i = getByte l (n + i) := by
  simp only [getByte_eq, List.getElem?_drop]

/-! ## The two characterizations — every memory law follows from these -/

/-- **A write changes exactly its window.** Byte `j` after `writeBytes off wb` is
`wb`'s byte if `j ∈ [off, off+|wb|)`, else the original memory's byte. -/
theorem writeBytes_getByte (m : Mem) (off : Nat) (wb : Mem) (j : Nat) :
    getByte (m.writeBytes off wb) j
      = if off ≤ j ∧ j < off + wb.length then getByte wb (j - off) else getByte m j := by
  set E := m.expand (off + wb.length) with hE
  have hlen : (E.take off).length = off := by
    rw [List.length_take, hE, expand_length]; omega
  rw [Mem.writeBytes, ← hE, List.append_assoc]
  by_cases h1 : j < off
  · rw [append_getByte_left (by rw [hlen]; omega), take_getByte h1, hE, expand_getByte]
    simp [Nat.not_le.mpr h1]
  · rw [append_getByte_right (by rw [hlen]; omega), hlen]
    by_cases h2 : j < off + wb.length
    · rw [append_getByte_left (by omega)]; simp [Nat.le_of_not_lt h1, h2]
    · rw [append_getByte_right (by omega), drop_getByte, hE, expand_getByte]
      rw [show off + wb.length + (j - off - wb.length) = j from by omega]
      simp [Nat.le_of_not_lt h1, h2]

/-- **A read is a window of the byte map.** Byte `i` of `readBytes off len` is
byte `off+i` of memory (zero past the read length). -/
theorem readBytes_getByte (m : Mem) (off len i : Nat) :
    getByte (m.readBytes off len) i = if i < len then getByte m (off + i) else 0 := by
  rw [Mem.readBytes]
  by_cases h : i < len
  · rw [take_getByte h, drop_getByte, expand_getByte]; simp [h]
  · rw [getByte_past (by rw [List.length_take, List.length_drop]; omega)]; simp [h]

theorem readBytes_length (m : Mem) (off len : Nat) : (m.readBytes off len).length = len := by
  rw [Mem.readBytes, List.length_take, List.length_drop, expand_length]; omega

/-- Byte-function extensionality: equal length + equal bytes ⇒ equal memory. -/
theorem ext_getByte {l₁ l₂ : Mem} (hlen : l₁.length = l₂.length)
    (h : ∀ i, getByte l₁ i = getByte l₂ i) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i
  rw [getByte_eq, getByte_eq, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      Option.getD_some, Option.getD_some] at this
  exact this

/-! ## The memory laws (instances of the characterizations) -/

/-- **Read-after-write** (re-derived through `getByte`): reading back the word
just stored returns it. The same-address law, now from the byte characterization. -/
theorem loadWord_storeWord_self' (m : Mem) (a v : UInt256) :
    (m.storeWord a v).loadWord a = v := by
  unfold Mem.loadWord Mem.storeWord
  have hread : (m.writeBytes a.toNat (toBytes32 v)).readBytes a.toNat 32 = toBytes32 v := by
    apply ext_getByte (by rw [readBytes_length, toBytes32_length])
    intro i
    rw [readBytes_getByte]
    by_cases hi : i < 32
    · rw [if_pos hi, writeBytes_getByte, toBytes32_length,
          if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · rw [if_neg hi, getByte_past (by rw [toBytes32_length]; omega)]
  rw [hread, fromBytes32_toBytes32]

/-- **Memory frame / no-aliasing (byte level).** A write to `[woff, woff+|wb|)`
leaves any read from a disjoint region unchanged — memory regions are
independent. -/
theorem readBytes_writeBytes_disjoint (m : Mem) (woff : Nat) (wb : Mem) (roff rlen : Nat)
    (hdisj : roff + rlen ≤ woff ∨ woff + wb.length ≤ roff) :
    (m.writeBytes woff wb).readBytes roff rlen = m.readBytes roff rlen := by
  apply ext_getByte (by rw [readBytes_length, readBytes_length])
  intro i
  rw [readBytes_getByte, readBytes_getByte]
  by_cases hi : i < rlen
  · simp only [hi, if_true, writeBytes_getByte]
    have : ¬ (woff ≤ roff + i ∧ roff + i < woff + wb.length) := by
      rcases hdisj with h | h <;> omega
    simp [this]
  · simp [hi]

/-- **Memory no-aliasing (word level).** Storing a word at `a` does not disturb a
word read from a disjoint slot `b` (the 32-byte ranges don't overlap) — the
memory analogue of the storage `~addr` no-aliasing. -/
theorem loadWord_storeWord_disjoint (m : Mem) (a v b : UInt256)
    (hdisj : a.toNat + 32 ≤ b.toNat ∨ b.toNat + 32 ≤ a.toNat) :
    (m.storeWord a v).loadWord b = m.loadWord b := by
  unfold Mem.loadWord Mem.storeWord
  congr 1
  exact readBytes_writeBytes_disjoint m a.toNat (toBytes32 v) b.toNat 32
    (by rw [toBytes32_length]; omega)

/-! ## Byte store (`mstore8`) -/

/-- **`mstore8` read-back.** A byte store writes `v`'s low byte at `addr`;
reading that byte returns it. -/
theorem getByte_storeByte_self (mem : Mem) (a v : UInt256) :
    getByte (mem.storeByte a v) a.toNat = UInt8.ofNat (v.toNat % 256) := by
  rw [Mem.storeByte, writeBytes_getByte]; simp [getByte]

/-- **`mstore8` frame.** A byte store leaves every *other* byte unchanged. -/
theorem getByte_storeByte_ne (mem : Mem) (a v : UInt256) (j : Nat) (h : j ≠ a.toNat) :
    getByte (mem.storeByte a v) j = getByte mem j := by
  rw [Mem.storeByte, writeBytes_getByte]
  simp only [List.length_singleton]
  rw [if_neg]; omega

/-! ## Register spilling (M4 substrate)

When the SSA stack exceeds the EVM's `SWAP16` reach, the scheduler **spills**
live values to memory and reloads them later. The value-preservation core is the
word memory laws above: a spilled value round-trips, and — crucially — *survives
other memory activity* as long as the allocator keeps the spill slots disjoint
(the no-aliasing law). The remaining M4 work is the `Sim`-level bookkeeping of
which variables are currently spilled. -/

/-- **Spill / reload round-trip.** A value spilled to slot `spill` and reloaded
returns it — read-after-write, as register spilling. -/
theorem spill_reload_self (m : Mem) (spill v : UInt256) :
    (m.storeWord spill v).loadWord spill = v :=
  loadWord_storeWord_self' m spill v

/-- **Spill survives a disjoint write.** A value spilled to slot `spill` survives
a later store to a *disjoint* slot `other` (another spill, or any memory the
allocator keeps disjoint): reloading `spill` still yields it — the memory frame
law, as spill-slot non-interference. -/
theorem spill_reload_frame (m : Mem) (spill other v w : UInt256)
    (hdisj : spill.toNat + 32 ≤ other.toNat ∨ other.toNat + 32 ≤ spill.toNat) :
    ((m.storeWord spill v).storeWord other w).loadWord spill = v := by
  rw [loadWord_storeWord_disjoint (m.storeWord spill v) other w spill (by omega),
      loadWord_storeWord_self']

/-- **Two independent spills.** Two values spilled to disjoint slots are both
recoverable — the scheduler can spill many registers without interference. -/
theorem two_spills (m : Mem) (s1 s2 v1 v2 : UInt256)
    (hdisj : s1.toNat + 32 ≤ s2.toNat ∨ s2.toNat + 32 ≤ s1.toNat) :
    ((m.storeWord s1 v1).storeWord s2 v2).loadWord s1 = v1
    ∧ ((m.storeWord s1 v1).storeWord s2 v2).loadWord s2 = v2 :=
  ⟨spill_reload_frame m s1 s2 v1 v2 hdisj, by rw [loadWord_storeWord_self']⟩

/-- Apply a sequence of word stores left-to-right (the rest of a computation's
memory activity, as a list of `(slot, value)` writes). -/
def storeWords (m : Mem) (ws : List (UInt256 × UInt256)) : Mem :=
  ws.foldl (fun m p => m.storeWord p.1 p.2) m

/-- **Load survives a sequence of disjoint writes.** Loading `spill` is unchanged
by *any* number of stores to slots all disjoint from it (frame, iterated). -/
theorem loadWord_storeWords_disjoint (spill : UInt256) :
    ∀ (ws : List (UInt256 × UInt256)) (m : Mem),
      (∀ p ∈ ws, spill.toNat + 32 ≤ p.1.toNat ∨ p.1.toNat + 32 ≤ spill.toNat) →
      (storeWords m ws).loadWord spill = m.loadWord spill
  | [], _, _ => rfl
  | p :: ps, m, h => by
    rw [storeWords, List.foldl_cons, ← storeWords,
        loadWord_storeWords_disjoint spill ps (m.storeWord p.1 p.2)
          (fun q hq => h q (List.mem_cons_of_mem p hq)),
        loadWord_storeWord_disjoint m p.1 p.2 spill (by have := h p (by simp); omega)]

/-- **A spill survives the whole live range.** A value spilled to `spill` and then
subjected to *any* sequence of stores to disjoint slots (the allocator keeps
spill slots mutually disjoint) reloads to the original value — register spilling
is safe across an entire computation, not just a single intervening write. -/
theorem spill_survives_writes (m : Mem) (spill v : UInt256) (ws : List (UInt256 × UInt256))
    (hdisj : ∀ p ∈ ws, spill.toNat + 32 ≤ p.1.toNat ∨ p.1.toNat + 32 ≤ spill.toNat) :
    (storeWords (m.storeWord spill v) ws).loadWord spill = v := by
  rw [loadWord_storeWords_disjoint spill ws (m.storeWord spill v) hdisj, loadWord_storeWord_self']

/-! ## The spill-slot allocator (discharges the disjointness guard) -/

/-- A word-aligned spill slot for register index `i`, above a base offset. -/
def spillSlot (base i : ℕ) : UInt256 := UInt256.ofNat (base + i * 32)

theorem spillSlot_toNat (base i : ℕ) (h : base + i * 32 < 2 ^ 256) :
    (spillSlot base i).toNat = base + i * 32 := by
  simp only [spillSlot, UInt256.ofNat, UInt256.toNat, Id.run]; exact Nat.mod_eq_of_lt h

/-- **Distinct registers get disjoint slots.** The allocator invariant the spill
frame laws need: distinct indices map to non-overlapping 32-byte slots. -/
theorem spillSlot_disjoint (base i j : ℕ) (hij : i ≠ j)
    (hi : base + i * 32 + 32 ≤ 2 ^ 256) (hj : base + j * 32 + 32 ≤ 2 ^ 256) :
    (spillSlot base i).toNat + 32 ≤ (spillSlot base j).toNat
    ∨ (spillSlot base j).toNat + 32 ≤ (spillSlot base i).toNat := by
  rw [spillSlot_toNat base i (by omega), spillSlot_toNat base j (by omega)]; omega

/-- **Two registers spilled to distinct allocator slots are both recoverable** —
the frame disjointness discharged by the allocator scheme, not assumed. -/
theorem two_spills_alloc (m : Mem) (base i j : ℕ) (v1 v2 : UInt256) (hij : i ≠ j)
    (hi : base + i * 32 + 32 ≤ 2 ^ 256) (hj : base + j * 32 + 32 ≤ 2 ^ 256) :
    ((m.storeWord (spillSlot base i) v1).storeWord (spillSlot base j) v2).loadWord (spillSlot base i)
      = v1 :=
  spill_reload_frame m (spillSlot base i) (spillSlot base j) v1 v2 (spillSlot_disjoint base i j hij hi hj)

/-! ## Whole register-file spilling (the M4 allocator capstone)

`two_spills_alloc` recovers a register spilled alongside ONE other. These lift it
to an arbitrary set of allocated registers: a value survives spilling every other
register (`spill_recover_across_allocator`), and — for a register file with
pairwise-distinct indices — every spilled register reloads to its stored value
(`allocator_spill_all_recover`). Disjointness is discharged by `spillSlot_disjoint`
from the allocation scheme, never assumed. -/

/-- **One write to `slot` among otherwise-disjoint writes wins.** In a store
sequence `pre ++ (slot, v) :: post` where every write in `post` targets a slot
disjoint from `slot`, loading `slot` yields `v` — `pre` is irrelevant (overwritten
by the `slot` write), `post` cannot disturb it (frame). -/
theorem loadWord_storeWords_single (slot v : UInt256)
    (pre post : List (UInt256 × UInt256)) (m : Mem)
    (hpost : ∀ q ∈ post, slot.toNat + 32 ≤ q.1.toNat ∨ q.1.toNat + 32 ≤ slot.toNat) :
    (storeWords m (pre ++ (slot, v) :: post)).loadWord slot = v := by
  have key : storeWords m (pre ++ (slot, v) :: post)
      = storeWords ((storeWords m pre).storeWord slot v) post := by
    unfold storeWords
    rw [List.foldl_append, List.foldl_cons]
  rw [key, loadWord_storeWords_disjoint slot post ((storeWords m pre).storeWord slot v) hpost,
      loadWord_storeWord_self']

/-- **A spilled register survives spilling every other allocated register.** For a
target register `i` spilled to its allocator slot and a list of `(index, value)`
writes for OTHER registers (`p.1 ≠ i`), all spilled to their own allocator slots,
reloading register `i` recovers its value. The N-register generalization of
`two_spills_alloc`; slot disjointness is discharged per-write by
`spillSlot_disjoint`. -/
theorem spill_recover_across_allocator (m : Mem) (base i : ℕ) (v : UInt256)
    (writes : List (ℕ × UInt256))
    (hne : ∀ p ∈ writes, p.1 ≠ i)
    (hi : base + i * 32 + 32 ≤ 2 ^ 256)
    (hb : ∀ p ∈ writes, base + p.1 * 32 + 32 ≤ 2 ^ 256) :
    (storeWords (m.storeWord (spillSlot base i) v)
        (writes.map (fun p => (spillSlot base p.1, p.2)))).loadWord (spillSlot base i) = v := by
  refine spill_survives_writes m (spillSlot base i) v _ ?_
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact spillSlot_disjoint base i p.1 (fun h => hne p hp h.symm) hi (hb p hp)

/-- **The whole register file spills correctly.** Given registers with pairwise
distinct indices, all spilled to their allocator slots in one store sequence,
EVERY register reloads to exactly its stored value — the full-allocator
generalization: distinct indices ⇒ disjoint slots ⇒ each recovered independently. -/
theorem allocator_spill_all_recover (m : Mem) (base : ℕ) (regs : List (ℕ × UInt256))
    (hnd : regs.Pairwise (fun p q => p.1 ≠ q.1))
    (hb : ∀ p ∈ regs, base + p.1 * 32 + 32 ≤ 2 ^ 256) :
    ∀ p ∈ regs, (storeWords m
        (regs.map (fun r => (spillSlot base r.1, r.2)))).loadWord (spillSlot base p.1) = p.2 := by
  intro p hp
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hp
  subst hsplit
  -- pairwise gives p distinct from everything after it (in post)
  have hpost_ne : ∀ r ∈ post, p.1 ≠ r.1 :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hnd).2.1).1
  have hbp : base + p.1 * 32 + 32 ≤ 2 ^ 256 := hb p (by simp)
  -- the mapped store list splits at p's slot
  have hmap : (pre ++ p :: post).map (fun r => (spillSlot base r.1, r.2))
      = pre.map (fun r => (spillSlot base r.1, r.2))
        ++ (spillSlot base p.1, p.2) :: post.map (fun r => (spillSlot base r.1, r.2)) := by
    simp [List.map_append]
  rw [hmap]
  refine loadWord_storeWords_single (spillSlot base p.1) p.2 _ _ m ?_
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact spillSlot_disjoint base p.1 r.1 (hpost_ne r hr) hbp
    (hb r (by simp [List.mem_append, List.mem_cons]; tauto))

end EvmYul.Venom.Mem

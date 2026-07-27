import EvmYul.Venom.Asm
import EvmYul.Venom.MemBridge

/-!
# M5.4 — the ByteArray bridge: list decoder ↔ the real `EVM.decode`

`Asm.lean` proves fetch-decode correctness against the reducible *list* mirror
`decodeAtL`. This file discharges the gap to the **real** `ByteArray` decoder the
EVM driver `EVM.X` actually calls (`EVM.decode`), so every list-level M5 result
lifts to genuine bytecode.

The keystone is `decode_toByteArray` — `EVM.decode` on the assembled bytecode
equals `decodeAtL` on the underlying list, for any PC within a realistic
code-size bound (so `ByteArray.extract'` takes its fast path and the address
fits a machine word). It rests on three primitives bridged through the
`MemBridge` keystone `toList_eq_data` / `ltba_toList`:

* `get?_toByteArray` — `ByteArray.get?` of an assembled list is plain list indexing;
* `extract'_toList` — `extract'` (fast path) is list slicing;
* `uInt256OfByteArray_eq` — `uInt256OfByteArray` is `Mem.fromBytes32` of the bytes
  (definitional).

`decode_emit_offset` is the capstone: the real decoder, fetching at item `i`'s
program counter, sees exactly item `i`'s own bytes.
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation EvmYul.Venom.MemBridge

/-! ## Indexing / slicing primitives on assembled bytecode -/

/-- `ByteArray.get?` is `getElem?` on the underlying array. -/
theorem ba_get?_eq (ba : ByteArray) (n : Nat) : ba.get? n = ba.data[n]? := by
  unfold ByteArray.get?
  split
  · next h => rw [Array.getElem?_eq_getElem h]; rfl
  · next h => rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- `ByteArray.get?` of an assembled list is plain list indexing. -/
theorem get?_toByteArray (code : List UInt8) (n : Nat) :
    (List.toByteArray code).get? n = code[n]? := by
  have hdata : (List.toByteArray code).data.toList = code := by rw [← toList_eq_data, ltba_toList]
  rw [ba_get?_eq, ← Array.getElem?_toList, hdata]

/-- `uInt256OfByteArray` is `Mem.fromBytes32` of the byte list (both are
`UInt256.ofNat ∘ fromBytesBigEndian`). -/
theorem uInt256OfByteArray_eq (arr : ByteArray) :
    uInt256OfByteArray arr = Mem.fromBytes32 arr.data.toList := rfl

/-- `extract'` of an assembled list (on the fast path) is list slicing. -/
theorem extract'_toList (code : List UInt8) (s e : Nat) (hs : s < 2 ^ 64) (he : e < 2 ^ 64) :
    ((List.toByteArray code).extract' s e).data.toList = (code.drop s).take (e - s) := by
  have hdata : (List.toByteArray code).data.toList = code := by rw [← toList_eq_data, ltba_toList]
  unfold ByteArray.extract'
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hs, he⟩),
    ByteArray.data_extract, Array.toList_extract, hdata]

/-- Every PUSH carries at most 32 immediate bytes. -/
theorem argOnNBytesOfInstr_le (o : Operation .EVM) : argOnNBytesOfInstr o ≤ 32 := by
  cases o <;> rename_i a <;> cases a <;> decide

/-! ## The decode bridge and the M5 capstone -/

/-- **Decode bridge.** The real `ByteArray` decoder `EVM.decode` on assembled
bytecode agrees with the reducible list mirror `decodeAtL`, for any PC within a
realistic code-size bound (so `extract'` takes its fast path and the address does
not wrap). This lifts every list-level M5 result to the bytecode `EVM.X` fetches. -/
theorem decode_toByteArray (code : List UInt8) (pc : UInt256) (hpc : pc.toNat + 33 < 2 ^ 64) :
    decode (List.toByteArray code) pc = decodeAtL code pc.toNat := by
  unfold decode decodeAtL
  rw [get?_toByteArray]
  cases hb : code[pc.toNat]? with
  | none => simp
  | some b =>
    simp only [bind, Option.bind]
    cases hp : parseInstr b with
    | none => simp
    | some instr =>
      dsimp only
      have hw : argOnNBytesOfInstr instr ≤ 32 := argOnNBytesOfInstr_le instr
      by_cases hz : argOnNBytesOfInstr instr = 0
      · simp [hz]
      · rw [if_neg (by simpa using hz), if_neg (by simpa using hz)]
        rw [uInt256OfByteArray_eq,
          extract'_toList code (pc.toNat).succ ((pc.toNat).succ + argOnNBytesOfInstr instr)
            (by omega) (by omega),
          show (pc.toNat).succ + argOnNBytesOfInstr instr - (pc.toNat).succ
             = argOnNBytesOfInstr instr from by omega]

/-- **M5 capstone.** The *real* EVM decoder `EVM.decode`, fetching the assembled
program at item `i`'s program counter, sees exactly item `i`'s own bytes — so the
driver `EVM.X` executes the instruction the backend placed there. Composes the
decode bridge with list-level fetch-decode correctness; the only side conditions
are well-formedness and a realistic code-size bound. -/
theorem decode_emit_offset (lm : Label → UInt256) (prog : List Item) (i : Nat)
    (hi : i < prog.length) (hwf : (prog[i]'hi).WF)
    (hpc : offsetOf lm prog i + 33 < 2 ^ 64) :
    decode (List.toByteArray (emit lm prog)) (UInt256.ofNat (offsetOf lm prog i))
      = decodeAtL ((prog[i]'hi).encode1 lm) 0 := by
  have hlt : offsetOf lm prog i < 2 ^ 256 := by
    have : (2 : ℕ) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have htoNat : (UInt256.ofNat (offsetOf lm prog i)).toNat = offsetOf lm prog i := by
    simp only [UInt256.ofNat, UInt256.toNat, Id.run]; exact Nat.mod_eq_of_lt hlt
  rw [decode_toByteArray _ _ (by rw [htoNat]; omega), htoNat, decodeAtL_offset lm prog i hi hwf]

end EvmYul.Venom.Asm

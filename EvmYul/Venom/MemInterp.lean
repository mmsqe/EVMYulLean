import EvmYul.Venom.Semantics
import EvmYul.Venom.MemInvariant

/-!
# Interpreter-level memory laws (closing the oracle ↔ proof loop)

The differential suite (`scripts/venom_differential.sh`) validates the
*interpreter* — `execInstr` / `venom_run` — behaviorally against a real EVM. The
`Mem`-model laws (`MemInvariant`: read-after-write, frame / no-aliasing) are
proved about the underlying `Mem` operations. This file connects the two: it
lifts the `Mem` laws onto the **actual `execInstr` interpreter** the oracle runs,
so the memory behavior the differential tests confirm is also *formally proved*.

`execInstr` lowers each memory opcode to exactly the `Mem` operation —
`mstore`→`storeWord`, `mload`→`loadWord`, `mcopy`→`writeBytes ∘ readBytes` — so
each law is the corresponding `Mem` lemma threaded through the interpreter's
operand evaluation and output binding.
-/

namespace EvmYul.Venom
open EvmYul

/-- **Interpreter read-after-write.** Running `mstore %addr, %val` then
`%out = mload %addr` binds `%out` to the stored value (`loadWord_storeWord_self'`
on the real `execInstr`). -/
theorem execInstr_mstore_mload (s : VenomState) (addrOp valOp : Operand) (out : VarName) :
    ((execInstr ((execInstr s {opcode := .mstore, operands := [addrOp, valOp]}).1)
        {opcode := .mload, output := some out, operands := [addrOp]}).1).env out
      = Operand.evalEnv s.env valOp := by
  simp only [execInstr, List.map_cons, List.map_nil]
  rw [VenomState.mstore_env]
  show (VenomState.setOutput _ (some out) _).env out = _
  rw [VenomState.setOutput, VenomState.set_env_self]
  show ((s.mstore _ _).memory.loadWord _) = _
  rw [VenomState.mstore_memory, Mem.loadWord_storeWord_self']

/-- **Interpreter no-aliasing.** An `mstore %a, %v` does not disturb an
`mload %b` from a disjoint word (`|a-b| ≥ 32`) — `loadWord_storeWord_disjoint` on
the real `execInstr`. -/
theorem execInstr_mstore_mload_frame (s : VenomState) (aOp vOp bOp : Operand) (out : VarName)
    (hdisj : (Operand.evalEnv s.env aOp).toNat + 32 ≤ (Operand.evalEnv s.env bOp).toNat
           ∨ (Operand.evalEnv s.env bOp).toNat + 32 ≤ (Operand.evalEnv s.env aOp).toNat) :
    ((execInstr ((execInstr s {opcode := .mstore, operands := [aOp, vOp]}).1)
        {opcode := .mload, output := some out, operands := [bOp]}).1).env out
      = ((execInstr s {opcode := .mload, output := some out, operands := [bOp]}).1).env out := by
  simp only [execInstr, List.map_cons, List.map_nil]
  rw [VenomState.mstore_env]
  show (VenomState.setOutput _ (some out) _).env out
     = (VenomState.setOutput _ (some out) _).env out
  rw [VenomState.setOutput, VenomState.setOutput, VenomState.set_env_self,
      VenomState.set_env_self]
  show (s.mstore _ _).memory.loadWord _ = s.memory.loadWord _
  rw [VenomState.mstore_memory, Mem.loadWord_storeWord_disjoint _ _ _ _ hdisj]

/-- **Interpreter `mcopy` correctness.** After `mcopy %dst, %src, %len`, reading
`len` bytes at `dst` returns exactly the `len` bytes that were at `src`
(`readBytes_writeBytes_self` on the real `execInstr`). -/
theorem execInstr_mcopy (s : VenomState) (dstOp srcOp lenOp : Operand) :
    ((execInstr s {opcode := .mcopy, operands := [dstOp, srcOp, lenOp]}).1).memory.readBytes
        (Operand.evalEnv s.env dstOp).toNat (Operand.evalEnv s.env lenOp).toNat
      = s.memory.readBytes (Operand.evalEnv s.env srcOp).toNat
          (Operand.evalEnv s.env lenOp).toNat := by
  simp only [execInstr, List.map_cons, List.map_nil]
  have h := Mem.readBytes_writeBytes_self s.memory (Operand.evalEnv s.env dstOp).toNat
    (s.memory.readBytes (Operand.evalEnv s.env srcOp).toNat (Operand.evalEnv s.env lenOp).toNat)
  rw [Mem.readBytes_length] at h
  exact h

/-- **Interpreter `mstore8`.** Running `mstore8 %addr, %val` writes `%val`'s low
byte at `addr` (`getByte_storeByte_self` on the real `execInstr`). -/
theorem execInstr_mstore8 (s : VenomState) (aOp vOp : Operand) :
    Mem.getByte ((execInstr s {opcode := .mstore8, operands := [aOp, vOp]}).1).memory
        (Operand.evalEnv s.env aOp).toNat
      = UInt8.ofNat ((Operand.evalEnv s.env vOp).toNat % 256) := by
  simp only [execInstr, List.map_cons, List.map_nil]
  exact Mem.getByte_storeByte_self s.memory _ _

end EvmYul.Venom

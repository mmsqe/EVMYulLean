/-
Plan Executor — Venom Codegen Layer 5

Port of vyper-hol/venom/codegen/defs/planExecScript.sml

Mechanical translation: stack_op → asm_inst.
No intelligence — just maps each stack plan operation to assembly instructions.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Codegen.AsmIR
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/- ===== Byte Encoding Utilities ===== -/

/-- Encode a number as minimal big-endian byte list.
    0 → [], 42 → [42], 256 → [1,0], etc. -/
def encodeNumBytes (n : Nat) : List byte :=
  if n = 0 then []
  else
    let b : byte := UInt8.ofNat (n % 256)
    encodeNumBytes (n / 256) ++ [b]

/- ===== SWAP/DUP Name Tables ===== -/

def swapName (n : Nat) : String :=
  if n = 1 then "SWAP1" else if n = 2 then "SWAP2"
  else if n = 3 then "SWAP3" else if n = 4 then "SWAP4"
  else if n = 5 then "SWAP5" else if n = 6 then "SWAP6"
  else if n = 7 then "SWAP7" else if n = 8 then "SWAP8"
  else if n = 9 then "SWAP9" else if n = 10 then "SWAP10"
  else if n = 11 then "SWAP11" else if n = 12 then "SWAP12"
  else if n = 13 then "SWAP13" else if n = 14 then "SWAP14"
  else if n = 15 then "SWAP15" else if n = 16 then "SWAP16"
  else "SWAP?"

def dupName (n : Nat) : String :=
  if n = 1 then "DUP1" else if n = 2 then "DUP2"
  else if n = 3 then "DUP3" else if n = 4 then "DUP4"
  else if n = 5 then "DUP5" else if n = 6 then "DUP6"
  else if n = 7 then "DUP7" else if n = 8 then "DUP8"
  else if n = 9 then "DUP9" else if n = 10 then "DUP10"
  else if n = 11 then "DUP11" else if n = 12 then "DUP12"
  else if n = 13 then "DUP13" else if n = 14 then "DUP14"
  else if n = 15 then "DUP15" else if n = 16 then "DUP16"
  else "DUP?"

/- ===== Execute Single Stack Operation ===== -/

/-- Convert a single stack_op to asm_inst list. -/
def execStackOp : StackOp → List AsmInst
  | StackOp.SOPush (Operand.Lit v) =>
    [AsmInst.AsmPush (encodeNumBytes v.toNat)]
  | StackOp.SOPush (Operand.Var _) => []
  | StackOp.SOPush (Operand.Label l) => [AsmInst.AsmPushLabel l]
  | StackOp.SOPop n =>
    List.replicate n (AsmInst.AsmOp "POP")
  | StackOp.SOSwap n =>
    [AsmInst.AsmOp (swapName n)]
  | StackOp.SODup n =>
    [AsmInst.AsmOp (dupName n)]
  | StackOp.SOPoke _ _ => []
  | StackOp.SOSpill off =>
    [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"]
  | StackOp.SORestore off =>
    [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"]
  | StackOp.SOEmit opc =>
    [AsmInst.AsmOp opc]
  | StackOp.SOLabel lbl =>
    [AsmInst.AsmLabel lbl]
  | StackOp.SOPushLabel lbl =>
    [AsmInst.AsmPushLabel lbl]
  | StackOp.SOPushOfst lbl off =>
    [AsmInst.AsmPushOfst lbl off]

/-- Execute full plan: convert stack_op list to asm_inst list. -/
def executePlan (ops : List StackOp) : List AsmInst :=
  ops >>= execStackOp

end EvmYul.Venom.Hol.Codegen

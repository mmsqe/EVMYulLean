/-
Assembly Encoding (Symbol Resolution) — Property Definitions

Port of vyper-hol/venom/codegen/defs/symbolResolveScript.sml

Defines:
  - EVM opcode byte table
  - asm_inst_size: instruction → byte count
  - compute_label_offsets: compute label → byte offset map
  - assemble: asm_inst list → byte list

NO proofs — property definitions only.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.PlanExec
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/- ===== EVM Opcode Byte Table ===== -/

def evmOpcodeTable : List (String × byte) := [
  ("STOP", 0x00), ("ADD", 0x01), ("MUL", 0x02), ("SUB", 0x03),
  ("DIV", 0x04), ("SDIV", 0x05), ("MOD", 0x06), ("SMOD", 0x07),
  ("ADDMOD", 0x08), ("MULMOD", 0x09), ("EXP", 0x0A),
  ("SIGNEXTEND", 0x0B),
  ("LT", 0x10), ("GT", 0x11), ("SLT", 0x12), ("SGT", 0x13),
  ("EQ", 0x14), ("ISZERO", 0x15),
  ("AND", 0x16), ("OR", 0x17), ("XOR", 0x18), ("NOT", 0x19),
  ("BYTE", 0x1A), ("SHL", 0x1B), ("SHR", 0x1C), ("SAR", 0x1D),
  ("SHA3", 0x20),
  ("ADDRESS", 0x30), ("BALANCE", 0x31), ("ORIGIN", 0x32),
  ("CALLER", 0x33), ("CALLVALUE", 0x34),
  ("CALLDATALOAD", 0x35), ("CALLDATASIZE", 0x36), ("CALLDATACOPY", 0x37),
  ("CODESIZE", 0x38), ("CODECOPY", 0x39), ("GASPRICE", 0x3A),
  ("EXTCODESIZE", 0x3B), ("EXTCODECOPY", 0x3C),
  ("RETURNDATASIZE", 0x3D), ("RETURNDATACOPY", 0x3E), ("EXTCODEHASH", 0x3F),
  ("BLOCKHASH", 0x40), ("COINBASE", 0x41), ("TIMESTAMP", 0x42),
  ("NUMBER", 0x43), ("PREVRANDAO", 0x44), ("GASLIMIT", 0x45),
  ("CHAINID", 0x46), ("SELFBALANCE", 0x47), ("BASEFEE", 0x48),
  ("BLOBHASH", 0x49), ("BLOBBASEFEE", 0x4A),
  ("POP", 0x50), ("MLOAD", 0x51), ("MSTORE", 0x52), ("MSTORE8", 0x53),
  ("SLOAD", 0x54), ("SSTORE", 0x55),
  ("JUMP", 0x56), ("JUMPI", 0x57), ("MSIZE", 0x59), ("GAS", 0x5A),
  ("JUMPDEST", 0x5B), ("TLOAD", 0x5C), ("TSTORE", 0x5D), ("MCOPY", 0x5E),
  ("PUSH0", 0x5F),
  ("DUP1", 0x80), ("DUP2", 0x81), ("DUP3", 0x82), ("DUP4", 0x83),
  ("DUP5", 0x84), ("DUP6", 0x85), ("DUP7", 0x86), ("DUP8", 0x87),
  ("DUP9", 0x88), ("DUP10", 0x89), ("DUP11", 0x8A), ("DUP12", 0x8B),
  ("DUP13", 0x8C), ("DUP14", 0x8D), ("DUP15", 0x8E), ("DUP16", 0x8F),
  ("SWAP1", 0x90), ("SWAP2", 0x91), ("SWAP3", 0x92), ("SWAP4", 0x93),
  ("SWAP5", 0x94), ("SWAP6", 0x95), ("SWAP7", 0x96), ("SWAP8", 0x97),
  ("SWAP9", 0x98), ("SWAP10", 0x99), ("SWAP11", 0x9A), ("SWAP12", 0x9B),
  ("SWAP13", 0x9C), ("SWAP14", 0x9D), ("SWAP15", 0x9E), ("SWAP16", 0x9F),
  ("LOG0", 0xA0), ("LOG1", 0xA1), ("LOG2", 0xA2), ("LOG3", 0xA3), ("LOG4", 0xA4),
  ("CREATE", 0xF0), ("CALL", 0xF1), ("RETURN", 0xF3),
  ("DELEGATECALL", 0xF4), ("CREATE2", 0xF5),
  ("STATICCALL", 0xFA), ("REVERT", 0xFD),
  ("INVALID", 0xFE), ("SELFDESTRUCT", 0xFF)
]

def evmOpcodeByte (name : String) : Option byte :=
  evmOpcodeTable.lookup name

/- ===== Fixed Symbol Size ===== -/

def symbolSize : Nat := 2

/- ===== Instruction Size Computation ===== -/

def asmInstSize : AsmInst → Nat
  | AsmInst.AsmOp _         => 1
  | AsmInst.AsmPush []      => 1   -- PUSH0
  | AsmInst.AsmPush bytes   => 1 + bytes.length
  | AsmInst.AsmPushLabel _  => 1 + symbolSize
  | AsmInst.AsmPushOfst _ _ => 1 + symbolSize
  | AsmInst.AsmLabel _      => 1
  | AsmInst.AsmDataHeader _ => 0
  | AsmInst.AsmDataItem bs  => bs.length
  | AsmInst.AsmDataLabel _  => symbolSize

/- ===== Label Offset Computation ===== -/

/-- Scan asm_inst list, computing byte offset for each label.
    Returns (total_size, label_offsets). -/
def computeLabelOffsets (asm : List AsmInst) : Nat × AssocList String Nat :=
  asm.foldl (λ (pc, labels) inst =>
    let labels' := match inst with
      | AsmInst.AsmLabel lbl      => AssocList.insert String Nat labels lbl pc
      | AsmInst.AsmDataHeader lbl => AssocList.insert String Nat labels lbl pc
      | _ => labels
    (pc + asmInstSize inst, labels'))
    (0, [])

/- ===== Bytecode Encoding ===== -/

/-- Pad a byte list to exactly n bytes (left-pad with zeros). -/
def padBytes (n : Nat) (bytes : List byte) : List byte :=
  if bytes.length ≥ n then bytes
  else List.replicate (n - bytes.length) (0 : byte) ++ bytes

/-- Encode a single asm_inst to byte list, using resolved label offsets. -/
def encodeInst (offsets : AssocList String Nat) : AsmInst → List byte
  | AsmInst.AsmOp name =>
    match evmOpcodeByte name with
    | some b => [b]
    | none => []
  | AsmInst.AsmPush [] => [0x5F]
  | AsmInst.AsmPush bytes =>
    (UInt8.ofNat (0x5F + bytes.length)) :: bytes
  | AsmInst.AsmPushLabel lbl =>
    match AssocList.lookup String Nat offsets lbl with
    | some off =>
      let bytes := padBytes symbolSize (encodeNumBytes off)
      (0x61 : byte) :: bytes
    | none => (0x61 : byte) :: List.replicate symbolSize (0 : byte)
  | AsmInst.AsmPushOfst lbl delta =>
    match AssocList.lookup String Nat offsets lbl with
    | some off =>
      let bytes := padBytes symbolSize (encodeNumBytes (off + delta))
      (0x61 : byte) :: bytes
    | none => (0x61 : byte) :: List.replicate symbolSize (0 : byte)
  | AsmInst.AsmLabel _ => [0x5B]  -- JUMPDEST
  | AsmInst.AsmDataHeader _ => []
  | AsmInst.AsmDataItem bs => bs
  | AsmInst.AsmDataLabel lbl =>
    match AssocList.lookup String Nat offsets lbl with
    | some off => padBytes symbolSize (encodeNumBytes off)
    | none => List.replicate symbolSize (0 : byte)

/- ===== Top-Level Assembly ===== -/

/-- Assemble asm_inst list to EVM bytecode (byte list).
    Two-pass: first compute label offsets, then encode. -/
def assemble (asm : List AsmInst) : List byte :=
  let (_, offsets) := computeLabelOffsets asm
  asm.map (encodeInst offsets) |>.flatten

/- ===== runAsm-level resolution (AsmInst → AsmInst + offsetToPc) =====

   The byte-level `assemble` is for emitting final bytecode. The asm-IR interpreter
   (`runAsm` over `List AsmInst`) instead needs label *pushes* turned into concrete value
   pushes and a byte-offset → list-index map for `JUMP`/`JUMPI`. `resolveInst` replaces
   `AsmPushLabel`/`AsmPushOfst` with `AsmPush <byte offset>`; `buildOffsetToPc` maps each
   label's byte offset to its list index (`runAsm`'s `pc`). -/

/-- Replace a label/offset push with a concrete value push (the label's resolved byte
    offset). All other instructions are unchanged, so the resolved program has no
    `AsmPushLabel`/`AsmPushOfst` for `asmStep` to error on. -/
def resolveInst (offsets : AssocList String Nat) : AsmInst → AsmInst
  | AsmInst.AsmPushLabel lbl =>
    match AssocList.lookup String Nat offsets lbl with
    | some off => AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes off))
    | none     => AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 0))
  | AsmInst.AsmPushOfst lbl delta =>
    match AssocList.lookup String Nat offsets lbl with
    | some off => AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes (off + delta)))
    | none     => AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes delta))
  | other => other

/-- Map each label's byte offset to its list index in `asm` (the `pc` `runAsm` uses, and the
    target `JUMP`/`JUMPI` resolve to via `offsetToPc`). Threads `(byteOffset, listIndex)`. -/
def buildOffsetToPc (asm : List AsmInst) : AssocList Nat Nat :=
  (asm.zipIdx.foldl (fun (acc : Nat × AssocList Nat Nat) (instI : AsmInst × Nat) =>
    let (off, m) := acc
    let m' := match instI.1 with
      | AsmInst.AsmLabel _ => AssocList.insert Nat Nat m off instI.2
      | _ => m
    (off + asmInstSize instI.1, m'))
    (0, [])).2

/-- runAsm-level resolution: replace label pushes with value pushes, and build the
    byte-offset → list-index `offsetToPc`. The output `(prog, offsetToPc)` is what
    `runAsm` executes (no `AsmPushLabel`; `JUMP`/`JUMPI` resolvable). -/
def asmResolve (asm : List AsmInst) : List AsmInst × AssocList Nat Nat :=
  let offsets := (computeLabelOffsets asm).2
  (asm.map (resolveInst offsets), buildOffsetToPc asm)

end EvmYul.Venom.Hol.Codegen

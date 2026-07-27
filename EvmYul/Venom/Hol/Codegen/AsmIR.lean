/-
Assembly IR Types — Venom Codegen Layer 1

Port of vyper-hol/venom/codegen/defs/asmIRScript.sml

Defines:
  - asm_inst: assembly instruction type
  - stack_op: stack plan operation type
  - venom_to_evm_name: opcode → EVM name mapping
-/

import EvmYul.Venom.Hol.Types
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol.Codegen

/- ===== Assembly Instructions ===== -/

inductive AsmInst where
  | AsmOp      : String → AsmInst          -- EVM opcode: "ADD", "SWAP3", etc.
  | AsmPush    : List byte → AsmInst       -- PUSH<n> with literal bytes
  | AsmPushLabel : String → AsmInst         -- push label address (resolved later)
  | AsmPushOfst : String → Nat → AsmInst    -- push (label_address + offset)
  | AsmLabel   : String → AsmInst          -- JUMPDEST marker
  | AsmDataHeader : String → AsmInst        -- data section start
  | AsmDataItem : List byte → AsmInst       -- data section content
  | AsmDataLabel : String → AsmInst         -- data section label reference
  deriving Inhabited

/- ===== Stack Plan Operations ===== -/

inductive StackOp where
  | SOPush      : Operand → StackOp        -- push literal/label onto stack
  | SOPop       : Nat → StackOp            -- pop n items from TOS
  | SOSwap      : Nat → StackOp            -- SWAP: 1-based distance (1..16)
  | SODup       : Nat → StackOp            -- DUP: 1-based distance (1..16)
  | SOPoke      : Nat → Operand → StackOp   -- update stack model at dist (phi)
  | SOSpill     : Nat → StackOp            -- spill TOS to memory offset
  | SORestore   : Nat → StackOp            -- restore from memory offset to TOS
  | SOEmit      : String → StackOp          -- EVM opcode name
  | SOLabel     : String → StackOp          -- JUMPDEST label
  | SOPushLabel : String → StackOp          -- push label address
  | SOPushOfst  : String → Nat → StackOp    -- push (label + offset)
  deriving Inhabited

/- ===== Venom Opcode → EVM Name Mapping ===== -/

def opcodeToEvmName : Opcode → Option String
  | Opcode.ADD        => some "ADD"
  | Opcode.SUB        => some "SUB"
  | Opcode.MUL        => some "MUL"
  | Opcode.Div        => some "DIV"
  | Opcode.SDIV       => some "SDIV"
  | Opcode.Mod        => some "MOD"
  | Opcode.SMOD       => some "SMOD"
  | Opcode.Exp        => some "EXP"
  | Opcode.ADDMOD     => some "ADDMOD"
  | Opcode.MULMOD     => some "MULMOD"
  | Opcode.EQ         => some "EQ"
  | Opcode.LT         => some "LT"
  | Opcode.GT         => some "GT"
  | Opcode.SLT        => some "SLT"
  | Opcode.SGT        => some "SGT"
  | Opcode.ISZERO     => some "ISZERO"
  | Opcode.AND        => some "AND"
  | Opcode.OR         => some "OR"
  | Opcode.XOR        => some "XOR"
  | Opcode.NOT        => some "NOT"
  | Opcode.SHL        => some "SHL"
  | Opcode.SHR        => some "SHR"
  | Opcode.SAR        => some "SAR"
  | Opcode.SIGNEXTEND => some "SIGNEXTEND"
  | Opcode.BYTE       => some "BYTE"
  | Opcode.MLOAD      => some "MLOAD"
  | Opcode.MSTORE     => some "MSTORE"
  | Opcode.MSTORE8    => some "MSTORE8"
  | Opcode.MCOPY      => some "MCOPY"
  | Opcode.MEMTOP     => some "MSIZE"
  | Opcode.SLOAD      => some "SLOAD"
  | Opcode.SSTORE     => some "SSTORE"
  | Opcode.TLOAD      => some "TLOAD"
  | Opcode.TSTORE     => some "TSTORE"
  | Opcode.CALLER     => some "CALLER"
  | Opcode.CALLVALUE  => some "CALLVALUE"
  | Opcode.CALLDATALOAD => some "CALLDATALOAD"
  | Opcode.CALLDATASIZE => some "CALLDATASIZE"
  | Opcode.CALLDATACOPY => some "CALLDATACOPY"
  | Opcode.ADDRESS    => some "ADDRESS"
  | Opcode.ORIGIN     => some "ORIGIN"
  | Opcode.GASPRICE   => some "GASPRICE"
  | Opcode.GAS        => some "GAS"
  | Opcode.GASLIMIT   => some "GASLIMIT"
  | Opcode.COINBASE   => some "COINBASE"
  | Opcode.TIMESTAMP  => some "TIMESTAMP"
  | Opcode.NUMBER     => some "NUMBER"
  | Opcode.PREVRANDAO => some "PREVRANDAO"
  | Opcode.CHAINID    => some "CHAINID"
  | Opcode.SELFBALANCE => some "SELFBALANCE"
  | Opcode.BALANCE    => some "BALANCE"
  | Opcode.BLOCKHASH  => some "BLOCKHASH"
  | Opcode.BASEFEE    => some "BASEFEE"
  | Opcode.BLOBHASH   => some "BLOBHASH"
  | Opcode.BLOBBASEFEE => some "BLOBBASEFEE"
  | Opcode.CODESIZE   => some "CODESIZE"
  | Opcode.CODECOPY   => some "CODECOPY"
  | Opcode.EXTCODESIZE => some "EXTCODESIZE"
  | Opcode.EXTCODEHASH => some "EXTCODEHASH"
  | Opcode.EXTCODECOPY => some "EXTCODECOPY"
  | Opcode.RETURNDATASIZE => some "RETURNDATASIZE"
  | Opcode.RETURNDATACOPY => some "RETURNDATACOPY"
  | Opcode.SHA3       => some "SHA3"
  | Opcode.CALL       => some "CALL"
  | Opcode.STATICCALL => some "STATICCALL"
  | Opcode.DELEGATECALL => some "DELEGATECALL"
  | Opcode.CREATE     => some "CREATE"
  | Opcode.CREATE2    => some "CREATE2"
  | Opcode.SELFDESTRUCT => some "SELFDESTRUCT"
  | Opcode.INVALID    => some "INVALID"
  | Opcode.REVERT     => some "REVERT"
  | Opcode.STOP       => some "STOP"
  -- Special cases
  | Opcode.ILOAD      => some "MLOAD"
  | Opcode.RETURN     => some "RETURN"
  -- Non-1:1 mappings
  | Opcode.ISTORE     => none
  | Opcode.PHI        => none
  | Opcode.PARAM      => none
  | Opcode.ASSIGN     => none
  | Opcode.NOP        => none
  | Opcode.JMP        => none
  | Opcode.JNZ        => none
  | Opcode.DJMP       => none
  | Opcode.INVOKE     => none
  | Opcode.RET        => none
  | Opcode.LOG        => none
  | Opcode.ASSERT     => none
  | Opcode.ASSERT_UNREACHABLE => none
  | Opcode.ALLOCA     => none
  | Opcode.OFFSET     => none
  | Opcode.SINK       => none
  | Opcode.DLOAD      => none
  | Opcode.DLOADBYTES => none

/- ===== Operand Helpers ===== -/

def isVarOperand : Operand → Bool
  | Operand.Var _ => true
  | _ => false

def isLabelOperand : Operand → Bool
  | Operand.Label _ => true
  | _ => false

def getNonLabelOperands (inst : Instruction) : List Operand :=
  inst.operands.filter (λ op => !isLabelOperand op)

/- ===== Data Section Assembly ===== -/

def dataItemAsm (di : DataItem) : AsmInst :=
  match di with
  | DataItem.DataBytes bs => AsmInst.AsmDataItem bs
  | DataItem.DataLabel l => AsmInst.AsmDataLabel l

def dataSectionAsm (ds : DataSection) : List AsmInst :=
  AsmInst.AsmDataHeader ds.label :: ds.items.map dataItemAsm

end EvmYul.Venom.Hol.Codegen

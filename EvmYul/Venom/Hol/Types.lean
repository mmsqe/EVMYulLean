/-
Venom IR Type Definitions (ported to EVMYulLean)

This module defines the core types for the Venom intermediate representation,
adapted to use EVMYulLean's UInt256, AccountAddress, Keccak, and map infrastructure.

Original: vyper-hol/venom/defs/venomStateScript.sml, venomInstScript.sml
-/

import EvmYul.Wheels
import EvmYul.UInt256

namespace EvmYul.Venom.Hol

/- ===== Association List (finite map) ===== -/

abbrev AssocList (α : Type) (β : Type) : Type := List (α × β)

/-- Lookup a key in an association list. Returns `none` if not found. -/
def AssocList.lookup (α β : Type) [BEq α] (al : AssocList α β) (k : α) : Option β :=
  match al with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else rest.lookup k

/-- Insert or update a key-value pair in an association list. -/
def AssocList.insert (α β : Type) [BEq α] (al : AssocList α β) (k : α) (v : β) : AssocList α β :=
  (k, v) :: al.filter (λ (k', _) => k' != k)

/- ===== EVM Primitive Types ===== -/

-- Re-export from EvmYul for convenience
abbrev bytes32 := UInt256
abbrev address := AccountAddress
abbrev byte := UInt8

/- ===== Call Context ===== -/

structure CallContext where
  caller    : address
  contract  : address
  callvalue : bytes32
  calldata  : List byte
  gas       : Nat
  static    : Bool
  deriving Inhabited

/- ===== Transaction Context ===== -/

structure TxContext where
  origin     : address
  gasprice   : bytes32
  chainid    : bytes32
  blobhashes : List bytes32
  deriving Inhabited

/- ===== Block Context ===== -/

structure BlockContext where
  coinbase    : address
  timestamp   : bytes32
  number      : bytes32
  prevrandao  : bytes32
  gaslimit    : bytes32
  basefee     : bytes32
  blobbasefee : bytes32
  blockhash   : Nat → bytes32
  deriving Inhabited

/- ===== Storage (Venom-specific, using AssocList) ===== -/

abbrev Storage := AssocList bytes32 bytes32
abbrev TransientStorage := AssocList address Storage

/- ===== Accounts (Venom-specific simple model) ===== -/

structure VenomAccount where
  balance : Nat
  code    : List byte
  storage : Storage
  nonce   : Nat
  deriving Inhabited

abbrev Accounts := AssocList address VenomAccount

/- ===== Event/Log ===== -/

structure Event where
  logger : address
  topics : List bytes32
  data   : List byte
  deriving Inhabited

/- ===== Operands ===== -/

inductive Operand where
  | Lit   : bytes32 → Operand
  | Var   : String → Operand
  | Label : String → Operand
  deriving Inhabited, BEq, DecidableEq

/- ===== Venom Execution State ===== -/

structure VenomState where
  memory      : ByteArray
  transient   : TransientStorage
  vars        : AssocList String bytes32
  prevBb      : Option String
  currentBb   : String
  instIdx     : Nat
  returndata  : ByteArray
  halted      : Bool
  accounts    : Accounts
  callCtx     : CallContext
  txCtx       : TxContext
  blockCtx    : BlockContext
  logs        : List Event
  immutables  : AssocList Nat bytes32
  dataSection : List byte
  labels      : AssocList String bytes32
  code        : List byte
  params      : List bytes32
  prevHashes  : List bytes32
  allocas     : AssocList Nat (Nat × Nat)
  allocaNext  : Nat
  deriving Inhabited

/- ===== Instruction Opcodes ===== -/

inductive Opcode where
  -- Arithmetic
  | ADD | SUB | MUL | Div | SDIV | Mod | SMOD | Exp
  | ADDMOD | MULMOD
  -- Comparison
  | EQ | LT | GT | SLT | SGT | ISZERO
  -- Bitwise
  | AND | OR | XOR | NOT | SHL | SHR | SAR | SIGNEXTEND | BYTE
  -- Memory
  | MLOAD | MSTORE | MSTORE8 | MCOPY | MEMTOP
  -- Storage
  | SLOAD | SSTORE
  -- Transient storage
  | TLOAD | TSTORE
  -- Immutables (Vyper-specific)
  | ILOAD | ISTORE
  -- Control flow
  | JMP | JNZ | DJMP | RET | RETURN | REVERT | STOP | SINK
  -- SSA/IR-specific
  | PHI | PARAM | ASSIGN | NOP
  -- Allocation
  | ALLOCA
  -- Internal function calls
  | INVOKE
  -- Environment
  | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY
  | ADDRESS | ORIGIN | GASPRICE | GAS | GASLIMIT
  | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | CHAINID
  | SELFBALANCE | BALANCE | BLOCKHASH | BASEFEE
  | CODESIZE | CODECOPY | EXTCODESIZE | EXTCODEHASH | EXTCODECOPY
  | RETURNDATASIZE | RETURNDATACOPY
  | BLOBHASH | BLOBBASEFEE
  -- Hashing
  | SHA3
  -- External calls
  | CALL | STATICCALL | DELEGATECALL | CREATE | CREATE2
  -- Logging
  | LOG
  -- Other
  | SELFDESTRUCT | INVALID
  -- Assertions (Vyper-specific)
  | ASSERT | ASSERT_UNREACHABLE
  -- Data section access (Vyper-specific)
  | DLOAD | DLOADBYTES | OFFSET
  deriving Inhabited, DecidableEq

/- ===== Opcode Classification ===== -/

def isEffectFreeOp : Opcode → Bool
  | Opcode.ADD | Opcode.SUB | Opcode.MUL | Opcode.Div | Opcode.SDIV
  | Opcode.Mod | Opcode.SMOD | Opcode.Exp | Opcode.ADDMOD | Opcode.MULMOD
  | Opcode.EQ | Opcode.LT | Opcode.GT | Opcode.SLT | Opcode.SGT | Opcode.ISZERO
  | Opcode.AND | Opcode.OR | Opcode.XOR | Opcode.NOT
  | Opcode.SHL | Opcode.SHR | Opcode.SAR | Opcode.SIGNEXTEND | Opcode.BYTE
  | Opcode.ASSIGN | Opcode.PHI | Opcode.PARAM | Opcode.NOP | Opcode.OFFSET
  | Opcode.MLOAD | Opcode.SLOAD | Opcode.TLOAD | Opcode.ILOAD | Opcode.DLOAD
  | Opcode.MEMTOP | Opcode.SHA3 | Opcode.CALLER | Opcode.ADDRESS
  | Opcode.CALLVALUE | Opcode.GAS | Opcode.ORIGIN | Opcode.GASPRICE | Opcode.CHAINID
  | Opcode.COINBASE | Opcode.TIMESTAMP | Opcode.NUMBER | Opcode.PREVRANDAO
  | Opcode.GASLIMIT | Opcode.BASEFEE | Opcode.BLOBBASEFEE
  | Opcode.BLOCKHASH | Opcode.BLOBHASH | Opcode.BALANCE | Opcode.SELFBALANCE
  | Opcode.CALLDATASIZE | Opcode.CALLDATALOAD | Opcode.RETURNDATASIZE
  | Opcode.CODESIZE | Opcode.EXTCODESIZE | Opcode.EXTCODEHASH => true
  | _ => false

def isMemWriteOp : Opcode → Bool
  | Opcode.MSTORE | Opcode.MSTORE8 | Opcode.MCOPY
  | Opcode.CALLDATACOPY | Opcode.RETURNDATACOPY
  | Opcode.CODECOPY | Opcode.EXTCODECOPY | Opcode.DLOADBYTES => true
  | _ => false

/- ===== Instruction ===== -/

structure Instruction where
  id       : Nat
  opcode   : Opcode
  operands : List Operand
  outputs  : List String
  deriving Inhabited

/- ===== Basic Block ===== -/

structure BasicBlock where
  label        : String
  instructions : List Instruction
  deriving Inhabited

/- ===== IR Function ===== -/

structure IrFunction where
  name   : String
  blocks : List BasicBlock
  deriving Inhabited

/- ===== Data Section Types ===== -/

inductive DataItem where
  | DataBytes : List byte → DataItem
  | DataLabel : String → DataItem
  deriving Inhabited

structure DataSection where
  label : String
  items : List DataItem
  deriving Inhabited

/- ===== Venom Context (whole program) ===== -/

structure VenomContext where
  functions : List IrFunction
  entry     : Option String
  deriving Inhabited

/- ===== Execution Result Type ===== -/

inductive AbortType where
  | RevertAbort
  | ExHaltAbort
  deriving Inhabited

inductive ExecResult where
  | OK      : VenomState → ExecResult
  | Halt    : VenomState → ExecResult
  | Abort   : AbortType → VenomState → ExecResult
  | IntRet  : List bytes32 → VenomState → ExecResult
  | Error   : String → ExecResult
  deriving Inhabited

end EvmYul.Venom.Hol

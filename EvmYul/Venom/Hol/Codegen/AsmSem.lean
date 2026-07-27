/-
Assembly Semantics — Venom Codegen Layer 6

Port of vyper-hol/venom/codegen/defs/asmSemScript.sml

EVM assembly execution model: stack-based machine with memory, storage,
accounts, transient storage, and external calls.

Defines: asm_state, asm_result, asm_step (single instruction step),
and the opcode execution logic.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.SubEvm
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.UInt256
import EvmYul.Wheels
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen
open EvmYul (UInt256 AccountAddress)

namespace EvmYul.Venom.Hol.Codegen

/- ===== Types ===== -/

/-- Assembly execution state — stack-based EVM machine. -/
structure AsmState where
  stack     : List bytes32
  memory    : ByteArray
  accounts  : Accounts
  transient : TransientStorage
  returndata : ByteArray
  logs      : List Event
  pc        : Nat
  callCtx   : CallContext
  txCtx     : TxContext
  blockCtx  : BlockContext
  code      : List byte               -- Own bytecode
  prevHashes : List bytes32
  deriving Inhabited

/-- Assembly execution result. -/
inductive AsmResult where
  | AsmOK     : AsmState → AsmResult
  | AsmHalt   : AsmState → AsmResult
  | AsmRevert : AsmState → AsmResult
  | AsmFault  : AsmState → AsmResult
  | AsmError  : String → AsmResult
  deriving Inhabited

/- ===== Helpers ===== -/

def asmNext (s : AsmState) : AsmState :=
  { s with pc := s.pc + 1 }

def asmExpandMemory (needed : Nat) (mem : ByteArray) : ByteArray :=
  let rounded := ((needed + 31) / 32) * 32
  if rounded ≤ mem.size then mem
  else
    let pad := ffi.ByteArray.zeroes ⟨rounded - mem.size⟩
    pad.write 0 mem mem.size (rounded - mem.size)

def asmPushVal (v : bytes32) (s : AsmState) : AsmResult :=
  AsmResult.AsmOK ({ asmNext s with stack := v :: s.stack })

def asmPop (s : AsmState) : AsmResult :=
  match s.stack with
  | _ :: stk => AsmResult.AsmOK ({ asmNext s with stack := stk })
  | _ => AsmResult.AsmError "POP: stack underflow"

def asmBinop (f : bytes32 → bytes32 → bytes32) (s : AsmState) : AsmResult :=
  match s.stack with
  | a :: b :: stk => AsmResult.AsmOK ({ asmNext s with stack := f a b :: stk })
  | _ => AsmResult.AsmError "stack underflow"

def asmUnop (f : bytes32 → bytes32) (s : AsmState) : AsmResult :=
  match s.stack with
  | a :: stk => AsmResult.AsmOK ({ asmNext s with stack := f a :: stk })
  | _ => AsmResult.AsmError "stack underflow"

def asmTernop (f : bytes32 → bytes32 → bytes32 → bytes32) (s : AsmState) : AsmResult :=
  match s.stack with
  | a :: b :: c :: stk => AsmResult.AsmOK ({ asmNext s with stack := f a b c :: stk })
  | _ => AsmResult.AsmError "stack underflow"

def asmStateUnop (f : bytes32 → AsmState → bytes32) (s : AsmState) : AsmResult :=
  match s.stack with
  | a :: stk => AsmResult.AsmOK ({ asmNext s with stack := f a s :: stk })
  | _ => AsmResult.AsmError "stack underflow"

/-- Convert AsmState to VenomState for shared operations (SLOAD/SSTORE/TLOAD/TSTORE). -/
def AsmState.toVenomState (s : AsmState) : VenomState := {
  memory := s.memory, transient := s.transient, vars := []
  prevBb := none, currentBb := "", instIdx := 0, returndata := s.returndata
  halted := false, accounts := s.accounts, callCtx := s.callCtx
  txCtx := s.txCtx, blockCtx := s.blockCtx, logs := s.logs
  immutables := [], dataSection := [], labels := [], code := s.code
  params := [], prevHashes := s.prevHashes, allocas := [], allocaNext := 0
}

/- ===== DUP/SWAP Tables ===== -/

def dupTable : List (String × Nat) :=
  [("DUP1",0),("DUP2",1),("DUP3",2),("DUP4",3),("DUP5",4),("DUP6",5),("DUP7",6),("DUP8",7),
   ("DUP9",8),("DUP10",9),("DUP11",10),("DUP12",11),("DUP13",12),("DUP14",13),("DUP15",14),("DUP16",15)]

def swapTable : List (String × Nat) :=
  [("SWAP1",1),("SWAP2",2),("SWAP3",3),("SWAP4",4),("SWAP5",5),("SWAP6",6),("SWAP7",7),("SWAP8",8),
   ("SWAP9",9),("SWAP10",10),("SWAP11",11),("SWAP12",12),("SWAP13",13),("SWAP14",14),("SWAP15",15),("SWAP16",16)]

def logTable : List (String × Nat) :=
  [("LOG0",0),("LOG1",1),("LOG2",2),("LOG3",3),("LOG4",4)]

def assocLookup {α β : Type} [BEq α] (al : List (α × β)) (k : α) : Option β :=
  match al with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else assocLookup rest k

def asmDup (n : Nat) (s : AsmState) : AsmResult :=
  if h : n < s.stack.length then
    AsmResult.AsmOK ({ asmNext s with stack := s.stack.get ⟨n, h⟩ :: s.stack })
  else AsmResult.AsmError "DUP: stack underflow"

def asmSwap (n : Nat) (s : AsmState) : AsmResult :=
  if h₀ : 0 < n then
    if hₙ : n < s.stack.length then
      let stk := s.stack
      let top := stk.head?.getD (EvmYul.UInt256.ofNat 0)
      let nth := stk.get ⟨n, hₙ⟩
      let stk' := stk.set 0 nth |>.set n top
      AsmResult.AsmOK ({ asmNext s with stack := stk' })
    else AsmResult.AsmError "SWAP: stack underflow"
  else AsmResult.AsmError "SWAP: invalid n"

/- ===== Memory/Storage Operations ===== -/

def asmMload (s : AsmState) : AsmResult :=
  match s.stack with
  | offset :: stk =>
    let off := offset.toNat
    let mem := asmExpandMemory (off + 32) s.memory
    let bytes := mem.readWithPadding off 32
    let v := wordOfBytes bytes
    AsmResult.AsmOK ({ asmNext s with stack := v :: stk, memory := mem })
  | _ => AsmResult.AsmError "MLOAD: stack underflow"

def asmMstore (s : AsmState) : AsmResult :=
  match s.stack with
  | offset :: value :: stk =>
    let off := offset.toNat
    let bytes := wordToBytes value
    let mem := asmExpandMemory (off + 32) s.memory
    let newmem := bytes.write 0 mem off 32
    AsmResult.AsmOK ({ asmNext s with stack := stk, memory := newmem })
  | _ => AsmResult.AsmError "MSTORE: stack underflow"

def asmMstore8 (s : AsmState) : AsmResult :=
  match s.stack with
  | offset :: value :: stk =>
    let off := offset.toNat
    let b : byte := UInt8.ofNat (value.toNat % 256)
    let mem := asmExpandMemory (off + 1) s.memory
    let newmem := (⟨#[b]⟩ : ByteArray).write 0 mem off 1
    AsmResult.AsmOK ({ asmNext s with stack := stk, memory := newmem })
  | _ => AsmResult.AsmError "MSTORE8: stack underflow"

/- ===== External calls (asm side): delegate to the shared sub-EVM (`evmCall`/`evmCreate`) =====

These mirror the Venom-side `stepExternalCall` exactly — same `evmCall`/`evmCreate` arguments, same
calldata read (`readWithPadding`) and returndata writeback (`bytes.write`, matching
`writeMemoryWithExpansion`) — over the *shared* `Accounts`/memory model. So on corresponding states
(asm stack top = the Venom operands, equal memory/accounts) both sides produce the same effect, which
is what the per-block CALL correspondence needs. The pushed success flag / new address is the EVM
stack result. -/

/-- Writeback shared by the message-call arms: record `returndata`, copy the first `retSize` bytes to
    memory at `retOff` (matching `writeMemoryWithExpansion`), push `success`, install new accounts. -/
def asmCallWriteback (rOff rSz : Nat) (success : bytes32) (newAccs : Accounts) (ret : List byte)
    (stk : List bytes32) (s : AsmState) : AsmResult :=
  let retBytes : ByteArray := ⟨(ret.take rSz).toArray⟩
  let newmem := retBytes.write 0 s.memory rOff retBytes.size
  let s' := { asmNext s with stack := success :: stk, accounts := newAccs }
  AsmResult.AsmOK { s' with returndata := ⟨ret.toArray⟩, memory := newmem }

/-- `CALL` (asm): pop `gas addr value argsOff argsSize retOff retSize`, run the sub-EVM, push success. -/
def asmCall (s : AsmState) : AsmResult :=
  match s.stack with
  | gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk =>
    let calldata := (s.memory.readWithPadding aOff.toNat aSz.toNat).toList
    let (success, newAccs, ret) := evmCall subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value calldata
      s.txCtx.gasprice 0 (!s.callCtx.static)
    asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s
  | _ => AsmResult.AsmError "CALL: stack underflow"

/-- `STATICCALL` (asm): pop `gas addr argsOff argsSize retOff retSize`, run the sub-EVM (no value,
    `perm = false`), push success. -/
def asmStaticCall (s : AsmState) : AsmResult :=
  match s.stack with
  | gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk =>
    let calldata := (s.memory.readWithPadding aOff.toNat aSz.toNat).toList
    let (success, newAccs, ret) := evmCall subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩ calldata
      s.txCtx.gasprice 0 false
    asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s
  | _ => AsmResult.AsmError "STATICCALL: stack underflow"

/-- `DELEGATECALL` (asm): pop `gas addr argsOff argsSize retOff retSize`, run `addr`'s code in the
    caller's own context (recipient = self, sender = caller's caller, apparent value = own callvalue). -/
def asmDelegateCall (s : AsmState) : AsmResult :=
  match s.stack with
  | gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk =>
    let calldata := (s.memory.readWithPadding aOff.toNat aSz.toNat).toList
    let (success, newAccs, ret) := evmCall subEvmFuel s.accounts s.callCtx.caller s.txCtx.origin
      s.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ s.callCtx.callvalue calldata
      s.txCtx.gasprice 0 (!s.callCtx.static)
    asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s
  | _ => AsmResult.AsmError "DELEGATECALL: stack underflow"

/-- `CREATE` (asm): pop `value off size`, run the sub-EVM creation, push the new address (0 on fail). -/
def asmCreate (s : AsmState) : AsmResult :=
  match s.stack with
  | value :: off :: size :: stk =>
    let initCode := (s.memory.readWithPadding off.toNat size.toNat).toList
    let (addrOrZero, newAccs, _ret) := evmCreate subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      value initCode s.txCtx.gasprice 0 none
    AsmResult.AsmOK { asmNext s with stack := addrOrZero :: stk, accounts := newAccs }
  | _ => AsmResult.AsmError "CREATE: stack underflow"

/-- `CREATE2` (asm): pop `value off size salt`, run the sub-EVM creation with salt, push the address. -/
def asmCreate2 (s : AsmState) : AsmResult :=
  match s.stack with
  | value :: off :: size :: salt :: stk =>
    let initCode := (s.memory.readWithPadding off.toNat size.toNat).toList
    let (addrOrZero, newAccs, _ret) := evmCreate subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      value initCode s.txCtx.gasprice 0 (some (wordToBytes salt).toList)
    AsmResult.AsmOK { asmNext s with stack := addrOrZero :: stk, accounts := newAccs }
  | _ => AsmResult.AsmError "CREATE2: stack underflow"

def asmSload (s : AsmState) : AsmResult :=
  match s.stack with
  | key :: stk =>
    let v := sload key s.toVenomState
    AsmResult.AsmOK ({ asmNext s with stack := v :: stk })
  | _ => AsmResult.AsmError "SLOAD: stack underflow"

def asmSstore (s : AsmState) : AsmResult :=
  match s.stack with
  | key :: value :: stk =>
    let s' := sstore key value s.toVenomState
    let sNext := asmNext s
    AsmResult.AsmOK ({ sNext with stack := stk, accounts := s'.accounts })
  | _ => AsmResult.AsmError "SSTORE: stack underflow"

/- ===== Control Flow ===== -/

/-- JUMP: pop destination from stack, jump to PC. -/
def asmJump (offsetToPc : AssocList Nat Nat) (s : AsmState) : AsmResult :=
  match s.stack with
  | dest :: stk =>
    match AssocList.lookup Nat Nat offsetToPc dest.toNat with
    | some pc => AsmResult.AsmOK ({ s with stack := stk, pc := pc })
    | none => AsmResult.AsmError "JUMP: invalid destination"
  | _ => AsmResult.AsmError "JUMP: stack underflow"

/-- JUMPI: conditional jump. -/
def asmJumpi (offsetToPc : AssocList Nat Nat) (s : AsmState) : AsmResult :=
  match s.stack with
  | dest :: cond :: stk =>
    if cond = (EvmYul.UInt256.ofNat 0) then
      AsmResult.AsmOK ({ asmNext s with stack := stk })
    else
      match AssocList.lookup Nat Nat offsetToPc dest.toNat with
      | some pc => AsmResult.AsmOK ({ s with stack := stk, pc := pc })
      | none => AsmResult.AsmError "JUMPI: invalid destination"
  | _ => AsmResult.AsmError "JUMPI: stack underflow"

/-- RETURN: halt with returndata. -/
def asmReturnOp (s : AsmState) : AsmResult :=
  match s.stack with
  | off :: sz :: stk =>
    let o := off.toNat; let siz := sz.toNat
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (o + siz) s.memory
    let rd := mem.readWithPadding o siz
    AsmResult.AsmHalt ({ s with stack := stk, returndata := rd, memory := mem })
  | _ => AsmResult.AsmError "RETURN: stack underflow"

/-- REVERT: abort with returndata. -/
def asmRevertOp (s : AsmState) : AsmResult :=
  match s.stack with
  | off :: sz :: stk =>
    let o := off.toNat; let siz := sz.toNat
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (o + siz) s.memory
    let rd := mem.readWithPadding o siz
    AsmResult.AsmRevert ({ s with stack := stk, returndata := rd, memory := mem })
  | _ => AsmResult.AsmError "REVERT: stack underflow"

/-- SELFDESTRUCT: pop the beneficiary address and halt after transferring the contract's
    balance to it (reusing the Venom `selfdestruct` on the converted state — same account
    effect, mirroring how `asmSstore` reuses `sstore`). -/
def asmSelfdestruct (s : AsmState) : AsmResult :=
  match s.stack with
  | addr :: stk =>
    let s' := selfdestruct addr s.toVenomState
    AsmResult.AsmHalt ({ asmNext s with stack := stk, accounts := s'.accounts })
  | _ => AsmResult.AsmError "SELFDESTRUCT: stack underflow"

/- ===== Logging ===== -/

def asmLog (n : Nat) (s : AsmState) : AsmResult :=
  if s.stack.length < n + 2 then AsmResult.AsmError "LOG: stack underflow"
  else
    let offset := s.stack.head?.getD (EvmYul.UInt256.ofNat 0)
    let sz := s.stack[1]!
    let topics := s.stack.drop 2 |>.take n
    let stk := s.stack.drop (n + 2)
    let o := offset.toNat; let siz := sz.toNat
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (o + siz) s.memory
    let data := (mem.readWithPadding o siz).toList
    let ev : Event := { logger := s.callCtx.contract, topics := topics, data := data }
    let sNext := asmNext s
    AsmResult.AsmOK ({ sNext with stack := stk, memory := mem, logs := s.logs ++ [ev] })

/- ===== SHA3 ===== -/

def asmSha3 (s : AsmState) : AsmResult :=
  match s.stack with
  | off :: sz :: stk =>
    let o := off.toNat; let siz := sz.toNat
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (o + siz) s.memory
    let bs := mem.readWithPadding o siz
    let h := keccak256 bs
    AsmResult.AsmOK ({ asmNext s with stack := h :: stk, memory := mem })
  | _ => AsmResult.AsmError "SHA3: stack underflow"

/- ===== Copy Operations ===== -/

/-- Copy from source to memory (CALLDATACOPY, CODECOPY style). -/
def asmCopyToMem (src : List byte) (s : AsmState) : AsmResult :=
  match s.stack with
  | destOff :: srcOff :: sz :: stk =>
    let doff := destOff.toNat; let soff := srcOff.toNat; let siz := sz.toNat
    let srcBA : ByteArray := ⟨src.toArray⟩
    let bytes := srcBA.readWithPadding soff siz
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (doff + siz) s.memory
    let newmem := bytes.write 0 mem doff siz
    AsmResult.AsmOK ({ asmNext s with stack := stk, memory := newmem })
  | _ => AsmResult.AsmError "COPY: stack underflow"

/-- EXTCODECOPY: pop the address, then copy the referenced account's code into memory (delegates to
    `asmCopyToMem` with the account code as the source, on the remaining 3-input stack). -/
def asmExtcodecopy (s : AsmState) : AsmResult :=
  match s.stack with
  | addr :: rest =>
    asmCopyToMem (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code { s with stack := rest }
  | _ => AsmResult.AsmError "EXTCODECOPY: stack underflow"

/-- RETURNDATACOPY with OOB check. -/
def asmReturndatacopy (s : AsmState) : AsmResult :=
  match s.stack with
  | destOff :: srcOff :: sz :: stk =>
    let soff := srcOff.toNat; let siz := sz.toNat
    if soff + siz > s.returndata.size then
      AsmResult.AsmFault ({ s with returndata := ByteArray.empty })
    else
      let doff := destOff.toNat
      let bytes := s.returndata.readWithPadding soff siz
      let mem := if siz = 0 then s.memory
                 else asmExpandMemory (doff + siz) s.memory
      let newmem := bytes.write 0 mem doff siz
      AsmResult.AsmOK ({ asmNext s with stack := stk, memory := newmem })
  | _ => AsmResult.AsmError "RETURNDATACOPY: stack underflow"

/-- MCOPY: memory-to-memory copy with single expansion. -/
def asmMcopy (s : AsmState) : AsmResult :=
  match s.stack with
  | destOff :: srcOff :: sz :: stk =>
    let doff := destOff.toNat; let soff := srcOff.toNat; let siz := sz.toNat
    let mem := if siz = 0 then s.memory
               else asmExpandMemory (max (soff + siz) (doff + siz)) s.memory
    let bytes := mem.readWithPadding soff siz
    let newmem := bytes.write 0 mem doff siz
    AsmResult.AsmOK ({ asmNext s with stack := stk, memory := newmem })
  | _ => AsmResult.AsmError "MCOPY: stack underflow"

/- ===== Full Instruction Step ===== -/

/-- Execute a single assembly instruction.
    `offsetToPc` maps byte offsets to PC indices (for JUMP/JUMPI).
    `instructions` is the full program (for PC-based lookup). -/
def asmStep (offsetToPc : AssocList Nat Nat) (instructions : List AsmInst) (s : AsmState) : AsmResult :=
  if h : s.pc < instructions.length then
    let inst := instructions.get ⟨s.pc, h⟩
    match inst with
    -- Stack ops
    | AsmInst.AsmOp "POP"    => asmPop s
    | AsmInst.AsmOp "ADD"    => asmBinop (. + .) s
    | AsmInst.AsmOp "SUB"    => asmBinop (. - .) s
    | AsmInst.AsmOp "MUL"    => asmBinop (. * .) s
    | AsmInst.AsmOp "DIV"    => asmBinop safeDiv s
    | AsmInst.AsmOp "MOD"    => asmBinop safeMod s
    | AsmInst.AsmOp "SDIV"   => asmBinop safeSdiv s
    | AsmInst.AsmOp "SMOD"   => asmBinop safeSmod s
    | AsmInst.AsmOp "EXP"    => asmBinop UInt256.exp s
    | AsmInst.AsmOp "ADDMOD" => asmTernop addmod s
    | AsmInst.AsmOp "MULMOD" => asmTernop mulmod s
    | AsmInst.AsmOp "EQ"     => asmBinop (λ x y => boolToWord (x = y)) s
    | AsmInst.AsmOp "LT"     => asmBinop (λ x y => boolToWord (x.toNat < y.toNat)) s
    | AsmInst.AsmOp "GT"     => asmBinop (λ x y => boolToWord (x.toNat > y.toNat)) s
    | AsmInst.AsmOp "SLT"    => asmBinop UInt256.slt s
    | AsmInst.AsmOp "SGT"    => asmBinop UInt256.sgt s
    | AsmInst.AsmOp "ISZERO" => asmUnop UInt256.isZero s
    | AsmInst.AsmOp "AND"    => asmBinop (. &&& .) s
    | AsmInst.AsmOp "OR"     => asmBinop (. ||| .) s
    | AsmInst.AsmOp "XOR"    => asmBinop (. ^^^ .) s
    | AsmInst.AsmOp "NOT"    => asmUnop (~~~ .) s
    | AsmInst.AsmOp "SHL"    => asmBinop (λ a b => b <<< a) s
    | AsmInst.AsmOp "SHR"    => asmBinop (λ a b => b >>> a) s
    | AsmInst.AsmOp "SAR"    => asmBinop UInt256.sar s
    | AsmInst.AsmOp "SIGNEXTEND" => asmBinop signExtend s
    | AsmInst.AsmOp "BYTE"   => asmBinop evmByte s
    -- Memory / Storage
    | AsmInst.AsmOp "MLOAD"  => asmMload s
    | AsmInst.AsmOp "MSTORE" => asmMstore s
    | AsmInst.AsmOp "MSTORE8"=> asmMstore8 s
    | AsmInst.AsmOp "SLOAD"  => asmSload s
    | AsmInst.AsmOp "SSTORE" => asmSstore s
    | AsmInst.AsmOp "TLOAD"  => asmStateUnop (λ k s => tload k s.toVenomState) s
    | AsmInst.AsmOp "CALLDATALOAD" =>
      asmStateUnop (λ offset s =>
        wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s
    | AsmInst.AsmOp "TSTORE" =>
      match s.stack with
      | key :: value :: stk =>
        let s' := tstore key value s.toVenomState
        AsmResult.AsmOK ({ asmNext s with stack := stk, transient := s'.transient })
      | _ => AsmResult.AsmError "TSTORE: stack underflow"
    -- Account queries
    | AsmInst.AsmOp "BALANCE" =>
      asmStateUnop (λ addr s =>
        EvmYul.UInt256.ofNat
          (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).balance) s
    | AsmInst.AsmOp "EXTCODESIZE" =>
      asmStateUnop (λ addr s =>
        EvmYul.UInt256.ofNat
          (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).code.length) s
    | AsmInst.AsmOp "EXTCODEHASH" =>
      asmStateUnop (λ addr s =>
        let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts
        if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) s
    | AsmInst.AsmOp "SELFBALANCE" =>
      asmPushVal (EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance) s
    -- Environment
    | AsmInst.AsmOp "CALLER"    => asmPushVal (addressToWord s.callCtx.caller) s
    | AsmInst.AsmOp "ADDRESS"   => asmPushVal (addressToWord s.callCtx.contract) s
    | AsmInst.AsmOp "CALLVALUE" => asmPushVal s.callCtx.callvalue s
    | AsmInst.AsmOp "GAS"       => asmPushVal (EvmYul.UInt256.ofNat s.callCtx.gas) s
    | AsmInst.AsmOp "ORIGIN"    => asmPushVal (addressToWord s.txCtx.origin) s
    | AsmInst.AsmOp "GASPRICE"  => asmPushVal s.txCtx.gasprice s
    | AsmInst.AsmOp "CHAINID"   => asmPushVal s.txCtx.chainid s
    | AsmInst.AsmOp "COINBASE"  => asmPushVal (addressToWord s.blockCtx.coinbase) s
    | AsmInst.AsmOp "TIMESTAMP" => asmPushVal s.blockCtx.timestamp s
    | AsmInst.AsmOp "NUMBER"    => asmPushVal s.blockCtx.number s
    | AsmInst.AsmOp "GASLIMIT"  => asmPushVal s.blockCtx.gaslimit s
    | AsmInst.AsmOp "BASEFEE"   => asmPushVal s.blockCtx.basefee s
    | AsmInst.AsmOp "MSIZE"     => asmPushVal (EvmYul.UInt256.ofNat ((s.memory.size + 31) / 32 * 32)) s
    -- Copy ops
    | AsmInst.AsmOp "CALLDATACOPY"  => asmCopyToMem s.callCtx.calldata s
    | AsmInst.AsmOp "CODECOPY"      => asmCopyToMem s.code s
    | AsmInst.AsmOp "EXTCODECOPY"   => asmExtcodecopy s
    | AsmInst.AsmOp "RETURNDATACOPY"=> asmReturndatacopy s
    | AsmInst.AsmOp "MCOPY"         => asmMcopy s
    | AsmInst.AsmOp "CALLDATASIZE"  => asmPushVal (EvmYul.UInt256.ofNat s.callCtx.calldata.length) s
    | AsmInst.AsmOp "RETURNDATASIZE"=> asmPushVal (EvmYul.UInt256.ofNat s.returndata.size) s
    | AsmInst.AsmOp "CODESIZE"      => asmPushVal (EvmYul.UInt256.ofNat s.code.length) s
    -- Hashing
    | AsmInst.AsmOp "SHA3" => asmSha3 s
    -- Control flow
    | AsmInst.AsmOp "JUMP"     => asmJump offsetToPc s
    | AsmInst.AsmOp "JUMPI"    => asmJumpi offsetToPc s
    | AsmInst.AsmOp "JUMPDEST" => AsmResult.AsmOK (asmNext s)
    | AsmInst.AsmOp "RETURN"   => asmReturnOp s
    | AsmInst.AsmOp "REVERT"   => asmRevertOp s
    | AsmInst.AsmOp "STOP"     => AsmResult.AsmHalt (asmNext s)
    | AsmInst.AsmOp "INVALID"  => AsmResult.AsmFault { asmNext s with returndata := ByteArray.empty }
    | AsmInst.AsmOp "SELFDESTRUCT" => asmSelfdestruct s
    -- Push
    | AsmInst.AsmPush bytes =>
      -- EVM `PUSH` right-aligns its immediate: the bytes are the low-order end of
      -- the 256-bit word, so zero-pad on the LEFT (matching `wordToBytes`). Built
      -- via `List.toByteArray` so the `toByteArray_toList` codec law applies.
      let v := wordOfBytes (List.toByteArray (List.replicate (32 - bytes.length) (0 : byte) ++ bytes))
      asmPushVal v s
    -- Labels (resolved at assembly time; JUMPDEST generated)
    | AsmInst.AsmLabel _ => AsmResult.AsmOK (asmNext s)
    -- Unresolved labels (should not appear after resolution)
    | AsmInst.AsmPushLabel _ => AsmResult.AsmError "unresolved PUSH label"
    | AsmInst.AsmPushOfst _ _ => AsmResult.AsmError "unresolved PUSH ofst"
    -- Data section
    | AsmInst.AsmDataHeader _ => AsmResult.AsmOK (asmNext s)
    | AsmInst.AsmDataItem _   => AsmResult.AsmOK (asmNext s)
    | AsmInst.AsmDataLabel _  => AsmResult.AsmError "unresolved data label"
    -- External calls (delegate to the shared sub-EVM)
    | AsmInst.AsmOp "CALL"         => asmCall s
    | AsmInst.AsmOp "STATICCALL"   => asmStaticCall s
    | AsmInst.AsmOp "DELEGATECALL" => asmDelegateCall s
    | AsmInst.AsmOp "CREATE"       => asmCreate s
    | AsmInst.AsmOp "CREATE2"      => asmCreate2 s
    -- DUP/SWAP via table
    | AsmInst.AsmOp name =>
      match assocLookup dupTable name with
      | some n => asmDup n s
      | none =>
        match assocLookup swapTable name with
        | some n => asmSwap n s
        | none =>
          match assocLookup logTable name with
          | some n => asmLog n s
          | none => AsmResult.AsmError s!"unknown opcode: {name}"
  else AsmResult.AsmError "PC out of bounds"

/- ===== Step-Counted Execution ===== -/

/-- Execute exactly `n` steps from the current PC in the program.
    Mirrors HOL `asm_steps`: 0 steps = success (`AsmOK s`, NOT out-of-fuel),
    so simulation lemmas can discharge the empty-plan / 0-step base case.
    A non-`AsmOK` result from `asmStep` (halt/revert/fault/error) is returned
    immediately and propagates unchanged through the remaining steps. -/
def runAsm (n : Nat) (offsetToPc : AssocList Nat Nat)
    (instructions : List AsmInst) (s : AsmState) : AsmResult :=
  match n with
  | 0 => AsmResult.AsmOK s
  | n' + 1 =>
    match asmStep offsetToPc instructions s with
    | AsmResult.AsmOK s' => runAsm n' offsetToPc instructions s'
    | other => other

/- ===== Program Placement ===== -/

/-- `asmBlockAt prog pc insts`: the instruction slice `insts` is placed at
    `prog[pc .. pc + insts.length)`. Mirrors HOL `asm_block_at`.
    Used as a precondition of simulation lemmas so that `asmStep` (which
    fetches `instructions.get s.pc`) actually sees the planned ops.
    Stated with `[i]?` to avoid embedding `Fin` proof terms in the
    definition; the `asmBlockAt_get` lemma lifts this to `get` for use in
    proofs. -/
def asmBlockAt (prog : List AsmInst) (pc : Nat) (insts : List AsmInst) : Prop :=
  pc + insts.length ≤ prog.length ∧
  ∀ j, j < insts.length → prog[pc + j]? = insts[j]?

/-- `asmBlockAt` projects to the instruction at offset `j` within the block,
    in `get` (Fin-indexed) form. -/
theorem asmBlockAt_get {prog pc insts j}
    (h : asmBlockAt prog pc insts) (hj : j < insts.length) :
    prog.get ⟨pc + j, by rcases h with ⟨hlen, _⟩; omega⟩ = insts.get ⟨j, by omega⟩ := by
  rcases h with ⟨hlen, hget⟩
  have h1 := hget j hj
  have hA : pc + j < prog.length := by omega
  have hB : j < insts.length := hj
  rw [List.getElem?_eq_getElem hA, List.getElem?_eq_getElem hB] at h1
  simp only [List.get_eq_getElem]
  exact Option.some.inj h1

/-- `asmBlockAt` gives a length bound: `pc < prog.length` whenever the block
    is non-empty. -/
theorem asmBlockAt_pc_lt {prog pc insts}
    (h : asmBlockAt prog pc insts) (hne : 0 < insts.length) : pc < prog.length := by
  rcases h with ⟨hlen, _⟩
  omega

/-- `asmBlockAt (inst :: insts)` splits into: the head instruction at `pc`
    and the tail placed at `pc + 1`. -/
theorem asmBlockAt_cons_drop {prog pc inst insts}
    (h : asmBlockAt prog pc (inst :: insts)) :
    prog[pc]? = some inst ∧ asmBlockAt prog (pc + 1) insts := by
  rcases h with ⟨hlen, hget⟩
  have hlen' : (inst :: insts).length = insts.length + 1 := rfl
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · -- prog[pc]? = some inst
    have h0 := hget 0 (by rw [hlen']; omega)
    rwa [show (inst :: insts)[0]? = some inst from rfl, Nat.add_zero] at h0
  · -- length: pc + 1 + insts.length ≤ prog.length
    have heq : pc + (inst :: insts).length = pc + 1 + insts.length := by
      rw [hlen', Nat.add_assoc, Nat.add_comm 1 insts.length]
    omega
  · -- body: ∀ j < insts.length, prog[pc + 1 + j]? = insts[j]?
    intro j hj
    have hlt : j + 1 < (inst :: insts).length := by rw [hlen']; omega
    have h1 := hget (j + 1) hlt
    -- (inst :: insts)[j+1]? = insts[j]?
    rw [show pc + (j + 1) = pc + 1 + j from by omega] at h1
    have hC : (j + 1) < (inst :: insts).length := hlt
    have hD : j < insts.length := hj
    have heq : (inst :: insts)[j + 1]? = insts[j]? := List.getElem?_cons_succ
    rw [heq] at h1
    exact h1

/-- **Asm `CALL` step dispatch.** `asmStep` on a `CALL` opcode runs `asmCall` (the shared sub-EVM),
    mirroring the Venom-side `stepExternalCall`. The asm-side step-correctness building block for the
    per-block CALL correspondence. -/
theorem asmStep_call_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hg : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALL") :
    asmStep offsetToPc prog s = asmCall s := by
  simp only [asmStep, hg]
  split
  · rfl
  · rename_i h; exact absurd hpc h

/-- **Asm `STATICCALL` step dispatch.** `asmStep` on a `STATICCALL` opcode runs `asmStaticCall`
    (the shared sub-EVM), mirroring the Venom-side `stepExternalCall`. -/
theorem asmStep_staticcall_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hg : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "STATICCALL") :
    asmStep offsetToPc prog s = asmStaticCall s := by
  simp only [asmStep, hg]
  split
  · rfl
  · rename_i h; exact absurd hpc h

/-- **Asm `DELEGATECALL` step dispatch.** `asmStep` on a `DELEGATECALL` opcode runs `asmDelegateCall`
    (the shared sub-EVM), mirroring the Venom-side `stepExternalCall`. -/
theorem asmStep_delegatecall_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hg : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "DELEGATECALL") :
    asmStep offsetToPc prog s = asmDelegateCall s := by
  simp only [asmStep, hg]
  split
  · rfl
  · rename_i h; exact absurd hpc h

/-- **Asm `CREATE` step dispatch.** `asmStep` on a `CREATE` opcode runs `asmCreate` (the shared
    sub-EVM creation), mirroring the Venom-side `stepExternalCall`. -/
theorem asmStep_create_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hg : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CREATE") :
    asmStep offsetToPc prog s = asmCreate s := by
  simp only [asmStep, hg]
  split
  · rfl
  · rename_i h; exact absurd hpc h

/-- **Asm `CREATE2` step dispatch.** `asmStep` on a `CREATE2` opcode runs `asmCreate2` (the shared
    sub-EVM creation), mirroring the Venom-side `stepExternalCall`. -/
theorem asmStep_create2_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hg : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CREATE2") :
    asmStep offsetToPc prog s = asmCreate2 s := by
  simp only [asmStep, hg]
  split
  · rfl
  · rename_i h; exact absurd hpc h

/-- **CALL correspondence core: both interpreters run the identical sub-EVM.** Given corresponding
    states (the Venom `CALL` operands evaluate to the same 7 words the compiled asm has on its stack
    top, and the shared `accounts`/`memory`/`callCtx`/`txCtx` agree), the Venom driver step
    `stepExternalCall` and the asm step `asmCall` both reduce to their *writeback* parameterised by the
    **same** `evmCall` result `(success, newAccs, ret)` — i.e. both invoke the identical sub-EVM
    (`evmCall subEvmFuel` on the shared accounts, equal args, equal calldata) and structure the
    writeback identically. Composed with `callWriteback_asmCallWriteback_agree`, this is the sub-EVM
    half of a `venomAsmRel`-preserving CALL block sim (the remaining half being the plan-side
    `planStackRel`/`memoryRel` bookkeeping over the compiled operand pushes). -/
theorem asmCall_stepExternalCall_same_evmCall {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {gas addr value aOff aSz rOff rSz : bytes32} {stk : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : s.stack = gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = s.accounts) (hmem : vs.memory = s.memory)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcall : evmCall subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (s.memory.readWithPadding aOff.toNat aSz.toNat).toList s.txCtx.gasprice 0 (!s.callCtx.static)
      = (success, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmCall s = asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s := by
  have hcallV : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (readMemory aOff.toNat aSz.toNat vs).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hmem]; exact hcall
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcallV]
  · unfold asmCall; rw [hstk]; simp only [hcall]

/-- **CALL writeback agreement.** For the same `evmCall` result and equal memories, the Venom
    `callWriteback` state and the asm `asmCallWriteback` state agree on every shared field
    (`accounts`/`memory`/`returndata`), the Venom output var reads back the success flag the asm side
    pushes, and the residual stack is `stk`. Composes with `asmCall_stepExternalCall_same_evmCall` to
    give the full shared-state CALL correspondence. -/
theorem callWriteback_asmCallWriteback_agree (out : String) (rOff rSz : Nat) (success : bytes32)
    (newAccs : Accounts) (ret : List byte) (stk : List bytes32) (vs : VenomState) (s : AsmState)
    (hmem : vs.memory = s.memory) :
    ∃ s'', asmCallWriteback rOff rSz success newAccs ret stk s = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff rSz success newAccs ret vs).accounts = s''.accounts
      ∧ (callWriteback out rOff rSz success newAccs ret vs).memory = s''.memory
      ∧ (callWriteback out rOff rSz success newAccs ret vs).returndata = s''.returndata
      ∧ lookupVar out (callWriteback out rOff rSz success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · show (callWriteback _ _ _ _ _ _ _).accounts = newAccs
    simp only [callWriteback, updateVar, writeMemoryWithExpansion]
  · show (callWriteback _ _ _ _ _ _ _).memory = _
    simp only [callWriteback, updateVar, writeMemoryWithExpansion, hmem]
  · show (callWriteback _ _ _ _ _ _ _).returndata = ⟨ret.toArray⟩
    simp only [callWriteback, updateVar, writeMemoryWithExpansion]
  · simp only [callWriteback, updateVar, writeMemoryWithExpansion, lookupVar, alookup, ainsert,
      AssocList.insert, AssocList.lookup, beq_self_eq_true, if_true]

/-- **CALL step: full shared-state correspondence.** Composing the two CALL-core lemmas
    (`asmCall_stepExternalCall_same_evmCall` + `callWriteback_asmCallWriteback_agree`) with the
    environment-field preservation of both writebacks: for corresponding states (the 7 CALL operands
    evaluate to the 7 asm stack-top words and every shared field agrees), the Venom `stepExternalCall`
    and asm `asmCall` reach states agreeing on **all** shared `venomAsmRel` fields — accounts, memory,
    returndata, transient, logs, callCtx, txCtx, blockCtx, code, prevHashes — with the output var
    reading back the pushed success flag over the residual stack `stk`. (Both writebacks leave the
    environment fields untouched, so they carry through from the input equalities.) Memory-agreement is
    an explicit hypothesis, exactly as the store disjuncts carry `hmemsafe`; the residual for a full
    per-block capstone is the plan-level `planStackRel`/`planSpillRel` bookkeeping over the operand-emit
    plus the user-memory write-safety establishing that agreement. -/
theorem call_step_stateAgree {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {gas addr value aOff aSz rOff rSz : bytes32}
    {stk : List bytes32} {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : as.stack = gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = as.accounts) (hmem : vs.memory = as.memory)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcall : evmCall subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as.memory.readWithPadding aOff.toNat aSz.toNat).toList as.txCtx.gasprice 0 (!as.callCtx.static)
      = (success, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmCall as = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory = s''.memory
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).transient = s''.transient
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).logs = s''.logs
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).callCtx = s''.callCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).txCtx = s''.txCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).blockCtx = s''.blockCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).code = s''.code
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).prevHashes = s''.prevHashes
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmCall_stepExternalCall_same_evmCall hopc heval hout hstk hacc hmem hcc htx hcall
  obtain ⟨s'', hs''eq, hacc', hmem', hrd', hout', hstk'⟩ :=
    callWriteback_asmCallWriteback_agree out rOff.toNat rSz.toNat success newAccs ret stk vs as hmem
  -- expose s'' fields by unfolding asmCallWriteback
  have hconcrete := hs''eq
  simp only [asmCallWriteback] at hconcrete
  injection hconcrete with hc
  refine ⟨s'', hstep, by rw [hasmeq]; exact hs''eq, hacc', hmem', hrd', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout', hstk'⟩
  · show (callWriteback _ _ _ _ _ _ _).transient = s''.transient
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htr
  · show (callWriteback _ _ _ _ _ _ _).logs = s''.logs
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hlg
  · show (callWriteback _ _ _ _ _ _ _).callCtx = s''.callCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcc
  · show (callWriteback _ _ _ _ _ _ _).txCtx = s''.txCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htx
  · show (callWriteback _ _ _ _ _ _ _).blockCtx = s''.blockCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hbc
  · show (callWriteback _ _ _ _ _ _ _).code = s''.code
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcode
  · show (callWriteback _ _ _ _ _ _ _).prevHashes = s''.prevHashes
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hph

end EvmYul.Venom.Hol.Codegen

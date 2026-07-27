/-
Venom IR Instruction Semantics (ported to EVMYulLean)

This module defines the single-instruction stepper stepInstBase for
Venom IR, using EVMYulLean's UInt256, Keccak-256 (FFI), and operations.

Original: vyper-hol/venom/defs/venomExecSemanticsScript.sml
-/

import EvmYul.Venom.Hol.Types
import EvmYul.UInt256
import EvmYul.FFI.ffi

open EvmYul (UInt256 AccountAddress fromByteArrayBigEndian)
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol

/- ===== Helper abbreviations ===== -/

def alookup {α β : Type} [BEq α] (al : AssocList α β) (k : α) : Option β := AssocList.lookup α β al k
def ainsert {α β : Type} [BEq α] (al : AssocList α β) (k : α) (v : β) : AssocList α β := AssocList.insert α β al k v

/- ===== Address Conversion ===== -/

/-- Convert an AccountAddress to UInt256 (widening, zero-extend). -/
def addressToWord (a : address) : bytes32 :=
  UInt256.ofNat a.val

/- ===== Variable Operations ===== -/

def updateVar (x : String) (v : bytes32) (s : VenomState) : VenomState :=
  { s with vars := ainsert s.vars x v }

def lookupVar (x : String) (s : VenomState) : Option bytes32 :=
  alookup s.vars x

/- ===== Byte / Word Conversion Helpers (big-endian, EVM style) ===== -/

/-- Convert a byte list to a 256-bit word (big-endian). -/
def wordOfBytes (bytes : ByteArray) : bytes32 :=
  UInt256.ofNat (fromBytesBigEndian bytes.toList)

/-- Convert a 256-bit word to a byte array (big-endian, 32 bytes). -/
def wordToBytes (w : bytes32) : ByteArray :=
  let be := toBytesBigEndian w.toNat
  List.toByteArray (List.replicate (32 - be.length) 0 ++ be)

/-- Convert a ByteArray to a 256-bit word (big-endian, first 32 bytes). -/
def byteArrayToWord (ba : ByteArray) : bytes32 :=
  wordOfBytes ba

/- ===== Operand Evaluation ===== -/

def evalOperand (op : Operand) (s : VenomState) : Option bytes32 :=
  match op with
  | Operand.Lit v => some v
  | Operand.Var x => lookupVar x s
  | Operand.Label lbl => alookup s.labels lbl

def evalOperands (ops : List Operand) (s : VenomState) : Option (List bytes32) :=
  match ops with
  | [] => some []
  | op :: ops' =>
    match evalOperand op s with
    | none => none
    | some v =>
      match evalOperands ops' s with
      | none => none
      | some vs => some (v :: vs)

/- ===== Arithmetic/Logic Operations ===== -/

def safeDiv (x y : bytes32) : bytes32 :=
  if y.toNat == 0 then ⟨0⟩ else x / y

def safeMod (x y : bytes32) : bytes32 :=
  if y.toNat == 0 then ⟨0⟩ else x % y

def safeSdiv (x y : bytes32) : bytes32 :=
  if y.toNat == 0 then ⟨0⟩ else UInt256.sdiv x y

def safeSmod (x y : bytes32) : bytes32 :=
  UInt256.smod x y  -- Already handles zero internally

def addmod (a b n : bytes32) : bytes32 :=
  UInt256.addMod a b n

def mulmod (a b n : bytes32) : bytes32 :=
  UInt256.mulMod a b n

/-- EVM byte operation: extract n-th byte (big-endian) from value. -/
def evmByte (n x : bytes32) : bytes32 :=
  UInt256.byteAt n x

/-- EVM sign extension. -/
def signExtend (n w : bytes32) : bytes32 :=
  UInt256.signextend n w

def boolToWord (b : Bool) : bytes32 :=
  if b then ⟨1⟩ else ⟨0⟩

/- ===== Memory Operations ===== -/

def readMemory (offset size : Nat) (s : VenomState) : ByteArray :=
  s.memory.readWithPadding offset size

def writeMemoryWithExpansion (offset : Nat) (bytes : ByteArray) (s : VenomState) : VenomState :=
  let newmem := bytes.write 0 s.memory offset bytes.size
  { s with memory := newmem }

def mload (offset : Nat) (s : VenomState) : bytes32 :=
  let bytes := readMemory offset 32 s
  wordOfBytes bytes

def mstore (offset : Nat) (value : bytes32) (s : VenomState) : VenomState :=
  let bytes := wordToBytes value
  writeMemoryWithExpansion offset bytes s

def mstore8 (offset : Nat) (value : bytes32) (s : VenomState) : VenomState :=
  let b : byte := UInt8.ofNat (value.toNat % 256)
  writeMemoryWithExpansion offset ⟨#[b]⟩ s

def mcopy (dst src sz : Nat) (s : VenomState) : VenomState :=
  let data := readMemory src sz s
  writeMemoryWithExpansion dst data s

/- ===== Storage Operations ===== -/

def contractStorage (s : VenomState) : Storage :=
  match alookup s.accounts s.callCtx.contract with
  | some acct => acct.storage
  | none => []

def sload (key : bytes32) (s : VenomState) : bytes32 :=
  match alookup (contractStorage s) key with
  | some v => v
  | none => ⟨0⟩

def sstore (key value : bytes32) (s : VenomState) : VenomState :=
  let addr := s.callCtx.contract
  let acct := alookup s.accounts addr
    |>.getD { balance := 0, code := [], storage := [], nonce := 0 : VenomAccount }
  let newStorage := ainsert acct.storage key value
  let newAcct := { acct with storage := newStorage }
  { s with accounts := ainsert s.accounts addr newAcct }

/- ===== Transient Storage Operations ===== -/

def contractTransient (s : VenomState) : Storage :=
  match alookup s.transient s.callCtx.contract with
  | some st => st
  | none => []

def tload (key : bytes32) (s : VenomState) : bytes32 :=
  match alookup (contractTransient s) key with
  | some v => v
  | none => ⟨0⟩

def tstore (key value : bytes32) (s : VenomState) : VenomState :=
  let addr := s.callCtx.contract
  let ts := alookup s.transient addr |>.getD []
  let newTs := ainsert ts key value
  { s with transient := ainsert s.transient addr newTs }

/- ===== Control Flow ===== -/

def jumpTo (lbl : String) (s : VenomState) : VenomState :=
  { s with prevBb := some s.currentBb, currentBb := lbl, instIdx := 0 }

def haltState (s : VenomState) : VenomState :=
  { s with halted := true }

def revertState (s : VenomState) : VenomState :=
  { s with halted := true }

def setReturndata (rd : ByteArray) (s : VenomState) : VenomState :=
  { s with returndata := rd }

/- ===== PHI and Label Helpers ===== -/

def resolvePhi (prevBb : String) (ops : List Operand) : Option Operand :=
  match ops with
  | [] => none
  | [_] => none
  | Operand.Label lbl :: valOp :: rest =>
    if lbl == prevBb then some valOp else resolvePhi prevBb rest
  | _ :: _ :: rest => resolvePhi prevBb rest

def extractLabels (ops : List Operand) : Option (List String) :=
  match ops with
  | [] => some []
  | Operand.Label lbl :: rest =>
    match extractLabels rest with
    | some lbls => some (lbl :: lbls)
    | none => none
  | _ => none

/- ===== Instruction Classification ===== -/

def isTerminator : Opcode → Bool
  | Opcode.JMP | Opcode.JNZ | Opcode.DJMP | Opcode.RET
  | Opcode.RETURN | Opcode.REVERT | Opcode.STOP | Opcode.SINK
  | Opcode.SELFDESTRUCT | Opcode.INVALID => true
  | _ => false

/- ===== Account Helpers ===== -/

def lookupAccount (addr : address) (accounts : Accounts) : VenomAccount :=
  alookup accounts addr |>.getD { balance := 0, code := [], storage := [], nonce := 0 }

/-- `SELFDESTRUCT`: transfer the executing contract's whole balance to `beneficiary` (the operand,
    as an address) and zero the contract's own balance. Pure function of `accounts` and the executing
    contract (`callCtx.contract`) — extracted verbatim from the inline `stepInstBase` arm so the asm
    side can reuse it. -/
def selfdestruct (addr : bytes32) (s : VenomState) : VenomState :=
  let self := s.callCtx.contract
  let selfAcct := lookupAccount self s.accounts
  let bal := selfAcct.balance
  let beneficiary := AccountAddress.ofUInt256 addr
  let benAcct := lookupAccount beneficiary s.accounts
  let newAccounts := ainsert s.accounts self { selfAcct with balance := 0 }
  let newAccounts := ainsert newAccounts beneficiary { benAcct with balance := benAcct.balance + bal }
  { s with accounts := newAccounts }

/- ===== Instruction Execution Helpers ===== -/

def execPure1 (f : bytes32 → bytes32) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands, inst.outputs with
  | [op1], [out] =>
    match evalOperand op1 s with
    | some v => ExecResult.OK (updateVar out (f v) s)
    | none => ExecResult.Error "undefined operand"
  | _, _ => ExecResult.Error "pure1 requires 1 operand and single output"

def execPure2 (f : bytes32 → bytes32 → bytes32) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands, inst.outputs with
  | [op1, op2], [out] =>
    match evalOperand op1 s, evalOperand op2 s with
    | some v1, some v2 => ExecResult.OK (updateVar out (f v1 v2) s)
    | _, _ => ExecResult.Error "undefined operand"
  | _, _ => ExecResult.Error "pure2 requires 2 operands and single output"

def execPure3 (f : bytes32 → bytes32 → bytes32 → bytes32) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands, inst.outputs with
  | [op1, op2, op3], [out] =>
    match evalOperand op1 s, evalOperand op2 s, evalOperand op3 s with
    | some v1, some v2, some v3 => ExecResult.OK (updateVar out (f v1 v2 v3) s)
    | _, _, _ => ExecResult.Error "undefined operand"
  | _, _ => ExecResult.Error "pure3 requires 3 operands and single output"

def execRead0 (f : VenomState → bytes32) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.outputs with
  | [out] => ExecResult.OK (updateVar out (f s) s)
  | _ => ExecResult.Error "read0 requires single output"

def execRead1 (f : bytes32 → VenomState → bytes32) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands, inst.outputs with
  | [op1], [out] =>
    match evalOperand op1 s with
    | some v => ExecResult.OK (updateVar out (f v s) s)
    | none => ExecResult.Error "undefined operand"
  | _, _ => ExecResult.Error "read1 requires 1 operand and single output"

def execWrite2 (f : bytes32 → bytes32 → VenomState → VenomState) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands with
  | [op1, op2] =>
    match evalOperand op1 s, evalOperand op2 s with
    | some v1, some v2 => ExecResult.OK (f v1 v2 s)
    | _, _ => ExecResult.Error "undefined operand"
  | _ => ExecResult.Error "write2 requires 2 operands"

/- ===== Keccak-256 (real FFI) ===== -/

/-- Keccak-256 hash via FFI. Takes a byte array, returns a 256-bit word. -/
def keccak256 (data : ByteArray) : bytes32 :=
  let hashBa := ffi.KEC data
  byteArrayToWord hashBa

/- ===== Single Instruction Step ===== -/

/--
Step a single instruction. This is the core of the Venom IR semantics.
Uses EVMYulLean's UInt256 operations and Keccak-256 FFI.
-/
def stepInstBase (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.opcode with
  -- Arithmetic
  | Opcode.ADD    => execPure2 (. + .) inst s
  | Opcode.SUB    => execPure2 (. - .) inst s
  | Opcode.MUL    => execPure2 (. * .) inst s
  | Opcode.Div    => execPure2 safeDiv inst s
  | Opcode.Mod    => execPure2 safeMod inst s
  | Opcode.SDIV   => execPure2 safeSdiv inst s
  | Opcode.SMOD   => execPure2 safeSmod inst s
  | Opcode.Exp    => execPure2 UInt256.exp inst s
  | Opcode.ADDMOD => execPure3 addmod inst s
  | Opcode.MULMOD => execPure3 mulmod inst s

  -- Comparison
  | Opcode.EQ     => execPure2 (λ x y => boolToWord (x = y)) inst s
  | Opcode.LT     => execPure2 (λ x y => boolToWord (x < y)) inst s
  | Opcode.GT     => execPure2 (λ x y => boolToWord (x > y)) inst s
  | Opcode.SLT    => execPure2 UInt256.slt inst s
  | Opcode.SGT    => execPure2 UInt256.sgt inst s
  | Opcode.ISZERO => execPure1 UInt256.isZero inst s

  -- Bitwise
  | Opcode.AND        => execPure2 (. &&& .) inst s
  | Opcode.OR         => execPure2 (. ||| .) inst s
  | Opcode.XOR        => execPure2 (. ^^^ .) inst s
  | Opcode.NOT        => execPure1 (~~~ .) inst s
  -- SHL/SHR are shift-first (`op1` = shift amount, `op2` = value), matching vyper-hol's
  -- `exec_pure2 (\n w. word_lsl w (w2n n))` and the EVM (shift on top). NOT `(· <<< ·)`, which
  -- would be value-first and miscompile (the asm `SHL` is `λ a b => b <<< a`, EVM-faithful).
  | Opcode.SHL        => execPure2 (fun n w => w <<< n) inst s
  | Opcode.SHR        => execPure2 (fun n w => w >>> n) inst s
  | Opcode.SAR        => execPure2 UInt256.sar inst s
  | Opcode.SIGNEXTEND => execPure2 signExtend inst s
  | Opcode.BYTE       => execPure2 evmByte inst s

  -- Memory
  | Opcode.MLOAD =>
    execRead1 (λ addr s => mload addr.toNat s) inst s
  | Opcode.MSTORE =>
    execWrite2 (λ addr val s => mstore addr.toNat val s) inst s
  | Opcode.MSTORE8 =>
    execWrite2 (λ addr val s => mstore8 addr.toNat val s) inst s
  | Opcode.MCOPY =>
    match inst.operands with
    | [opDst, opSrc, opSize] =>
      match evalOperand opDst s, evalOperand opSrc s, evalOperand opSize s with
      | some dst, some src, some sz =>
        ExecResult.OK (mcopy dst.toNat src.toNat sz.toNat s)
      | _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "mcopy requires 3 operands"

  -- Storage
  | Opcode.SLOAD  => execRead1 (λ key s => sload key s) inst s
  | Opcode.SSTORE => execWrite2 (λ key val s => sstore key val s) inst s

  -- Transient storage
  | Opcode.TLOAD  => execRead1 (λ key s => tload key s) inst s
  | Opcode.TSTORE => execWrite2 (λ key val s => tstore key val s) inst s

  -- Control flow - JMP
  | Opcode.JMP =>
    match inst.operands with
    | [Operand.Label lbl] => ExecResult.OK (jumpTo lbl s)
    | _ => ExecResult.Error "jmp requires label operand"

  -- Control flow - JNZ (conditional)
  | Opcode.JNZ =>
    match inst.operands with
    | [condOp, Operand.Label ifNonzero, Operand.Label ifZero] =>
      match evalOperand condOp s with
      | some cond =>
        if cond != ⟨0⟩ then ExecResult.OK (jumpTo ifNonzero s)
        else ExecResult.OK (jumpTo ifZero s)
      | none => ExecResult.Error "undefined condition"
    | _ => ExecResult.Error "jnz requires cond and 2 labels"

  -- Control flow - DJMP (dynamic jump)
  | Opcode.DJMP =>
    match inst.operands with
    | selectorOp :: labelOps =>
      match evalOperand selectorOp s, extractLabels labelOps with
      | some idx, some labels =>
        let i := idx.toNat
        if h : i < labels.length then
          ExecResult.OK (jumpTo (labels.get ⟨i, h⟩) s)
        else ExecResult.Error "djmp: index out of range"
      | _, _ => ExecResult.Error "djmp: undefined operand or invalid labels"
    | _ => ExecResult.Error "djmp requires selector and labels"

  -- Function parameter access
  | Opcode.PARAM =>
    match inst.operands with
    | [Operand.Lit idx] =>
      let i := idx.toNat
      if h : i < s.params.length then
        match inst.outputs with
        | [out] => ExecResult.OK (updateVar out (s.params.get ⟨i, h⟩) s)
        | _ => ExecResult.Error "param requires single output"
      else ExecResult.Error "param: index out of range"
    | _ => ExecResult.Error "param requires literal index"

  -- Return from internal function
  | Opcode.RET =>
    match evalOperands inst.operands s with
    | some retVals => ExecResult.IntRet retVals s
    | none => ExecResult.Error "ret: undefined return value"

  -- Termination
  | Opcode.STOP => ExecResult.Halt (haltState s)

  | Opcode.RETURN =>
    match inst.operands with
    | [offOp, szOp] =>
      match evalOperand offOp s, evalOperand szOp s with
      | some off, some sz =>
        let rd := readMemory off.toNat sz.toNat s
        ExecResult.Halt (haltState (setReturndata rd s))
      | _, _ => ExecResult.Error "return: undefined operand"
    | _ => ExecResult.Error "return requires 2 operands"

  | Opcode.REVERT =>
    match inst.operands with
    | [offOp, szOp] =>
      match evalOperand offOp s, evalOperand szOp s with
      | some off, some sz =>
        let rd := readMemory off.toNat sz.toNat s
        ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata rd s))
      | _, _ => ExecResult.Error "revert: undefined operand"
    | _ => ExecResult.Error "revert requires 2 operands"

  | Opcode.SINK => ExecResult.Halt (haltState s)

  -- Assertions
  | Opcode.ASSERT =>
    match inst.operands with
    | [condOp] =>
      match evalOperand condOp s with
      | some cond =>
        if cond = ⟨0⟩ then
          ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata ByteArray.empty s))
        else ExecResult.OK s
      | none => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "assert requires 1 operand"

  | Opcode.ASSERT_UNREACHABLE =>
    match inst.operands with
    | [condOp] =>
      match evalOperand condOp s with
      | some cond =>
        if cond = ⟨0⟩ then
          ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s))
        else ExecResult.OK s
      | none => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "assert_unreachable requires 1 operand"

  -- SSA
  | Opcode.PHI => ExecResult.Error "phi outside prefix"
  | Opcode.ASSIGN =>
    match inst.operands, inst.outputs with
    | [op1], [out] =>
      match evalOperand op1 s with
      | some v => ExecResult.OK (updateVar out v s)
      | none => ExecResult.Error "undefined operand"
    | _, _ => ExecResult.Error "assign requires 1 operand and single output"
  | Opcode.NOP => ExecResult.OK s

  -- Environment - Call context
  | Opcode.CALLER =>
    execRead0 (λ s => addressToWord s.callCtx.caller) inst s
  | Opcode.ADDRESS =>
    execRead0 (λ s => addressToWord s.callCtx.contract) inst s
  | Opcode.CALLVALUE =>
    execRead0 (λ s => s.callCtx.callvalue) inst s
  | Opcode.GAS =>
    execRead0 (λ s => UInt256.ofNat s.callCtx.gas) inst s

  -- Environment - Transaction context
  | Opcode.ORIGIN =>
    execRead0 (λ s => addressToWord s.txCtx.origin) inst s
  | Opcode.GASPRICE =>
    execRead0 (λ s => s.txCtx.gasprice) inst s
  | Opcode.CHAINID =>
    execRead0 (λ s => s.txCtx.chainid) inst s

  -- Environment - Block context
  | Opcode.COINBASE =>
    execRead0 (λ s => addressToWord s.blockCtx.coinbase) inst s
  | Opcode.TIMESTAMP =>
    execRead0 (λ s => s.blockCtx.timestamp) inst s
  | Opcode.NUMBER =>
    execRead0 (λ s => s.blockCtx.number) inst s
  | Opcode.PREVRANDAO =>
    execRead0 (λ s => s.blockCtx.prevrandao) inst s
  | Opcode.GASLIMIT =>
    execRead0 (λ s => s.blockCtx.gaslimit) inst s
  | Opcode.BASEFEE =>
    execRead0 (λ s => s.blockCtx.basefee) inst s
  | Opcode.BLOBBASEFEE =>
    execRead0 (λ s => s.blockCtx.blobbasefee) inst s
  | Opcode.BLOCKHASH =>
    execRead1 (λ v s => s.blockCtx.blockhash v.toNat) inst s
  | Opcode.BLOBHASH =>
    execRead1 (λ v s =>
      let idx := v.toNat
      if h : idx < s.txCtx.blobhashes.length then
        s.txCtx.blobhashes.get ⟨idx, h⟩
      else ⟨0⟩) inst s

  -- Environment - Balance
  | Opcode.BALANCE =>
    execRead1 (λ addr s =>
      UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).balance) inst s
  | Opcode.SELFBALANCE =>
    execRead0 (λ s =>
      UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance) inst s

  -- Calldata
  | Opcode.CALLDATASIZE =>
    execRead0 (λ s => UInt256.ofNat s.callCtx.calldata.length) inst s
  | Opcode.CALLDATALOAD =>
    execRead1 (λ offset s =>
      let data := s.callCtx.calldata
      let srcBA : ByteArray := ⟨data.toArray⟩
      let bytes := srcBA.readWithPadding offset.toNat 32
      wordOfBytes bytes) inst s

  | Opcode.CALLDATACOPY =>
    match inst.operands with
    | [opDestOffset, opOffset, opSize] =>
      match evalOperand opDestOffset s, evalOperand opOffset s, evalOperand opSize s with
      | some destOffset, some offset, some sizeVal =>
        let data := s.callCtx.calldata
        let size := sizeVal.toNat
        let srcOffset := offset.toNat
        let srcBA : ByteArray := ⟨data.toArray⟩
        let bytes := srcBA.readWithPadding srcOffset size
        ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s)
      | _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "calldatacopy requires 3 operands"

  -- Return data
  | Opcode.RETURNDATASIZE =>
    execRead0 (λ s => UInt256.ofNat s.returndata.size) inst s

  | Opcode.RETURNDATACOPY =>
    match inst.operands with
    | [opDestOffset, opOffset, opSize] =>
      match evalOperand opDestOffset s, evalOperand opOffset s, evalOperand opSize s with
      | some destOffset, some offset, some sizeVal =>
        let size := sizeVal.toNat
        let srcOffset := offset.toNat
        if srcOffset + size > s.returndata.size then
          ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s))
        else
          let bytes := s.returndata.readWithPadding srcOffset size
          ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s)
      | _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "returndatacopy requires 3 operands"

  -- Memory top
  | Opcode.MEMTOP =>
    execRead0 (λ s =>
      let size := s.memory.size
      let words := (size + 31) / 32
      UInt256.ofNat (words * 32)) inst s

  -- Hashing (real Keccak-256 via FFI)
  | Opcode.SHA3 =>
    match inst.operands with
    | [opOffset, opSize] =>
      match evalOperand opOffset s, evalOperand opSize s with
      | some offset, some sizeVal =>
        match inst.outputs with
        | [out] =>
          let bytes := readMemory offset.toNat sizeVal.toNat s
          let hash := keccak256 bytes
          ExecResult.OK (updateVar out hash s)
        | _ => ExecResult.Error "sha3 requires single output"
      | _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "sha3 requires 2 operands"

  -- Code introspection
  | Opcode.CODESIZE =>
    execRead0 (λ s => UInt256.ofNat s.code.length) inst s
  | Opcode.EXTCODESIZE =>
    execRead1 (λ addr s =>
      UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code.length) inst s
  | Opcode.EXTCODEHASH =>
    execRead1 (λ addr s =>
      let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.accounts
      if acct.code.isEmpty then ⟨0⟩
      else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) inst s

  -- Immutables
  | Opcode.ILOAD =>
    execRead1 (λ off s =>
      match alookup s.immutables off.toNat with
      | some v => v
      | none => ⟨0⟩) inst s
  | Opcode.ISTORE =>
    match inst.operands with
    | [offsetOp, valOp] =>
      match evalOperand offsetOp s, evalOperand valOp s with
      | some off, some v =>
        ExecResult.OK { s with immutables := ainsert s.immutables off.toNat v }
      | _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "istore requires 2 operands"

  -- Data section reads
  | Opcode.DLOAD =>
    execRead1 (λ off s =>
      let srcBA : ByteArray := ⟨s.dataSection.toArray⟩
      let bytes := srcBA.readWithPadding off.toNat 32
      wordOfBytes bytes) inst s

  | Opcode.DLOADBYTES =>
    match inst.operands with
    | [opDst, opSrc, opSize] =>
      match evalOperand opDst s, evalOperand opSrc s, evalOperand opSize s with
      | some dst, some src, some sizeVal =>
        let size := sizeVal.toNat
        let srcBA : ByteArray := ⟨s.dataSection.toArray⟩
        let bytes := srcBA.readWithPadding src.toNat size
        ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s)
      | _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "dloadbytes requires 3 operands"

  -- Code access
  | Opcode.CODECOPY =>
    match inst.operands with
    | [opDst, opSrc, opSize] =>
      match evalOperand opDst s, evalOperand opSrc s, evalOperand opSize s with
      | some dst, some src, some sizeVal =>
        let srcBA : ByteArray := ⟨s.code.toArray⟩
        let size := sizeVal.toNat
        let bytes := srcBA.readWithPadding src.toNat size
        ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s)
      | _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "codecopy requires 3 operands"

  | Opcode.EXTCODECOPY =>
    match inst.operands with
    | [opAddr, opDst, opSrc, opSize] =>
      match evalOperand opAddr s, evalOperand opDst s, evalOperand opSrc s, evalOperand opSize s with
      | some addr, some dst, some src, some sizeVal =>
        let code := (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code
        let size := sizeVal.toNat
        let srcBA : ByteArray := ⟨code.toArray⟩
        let bytes := srcBA.readWithPadding src.toNat size
        ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s)
      | _, _, _, _ => ExecResult.Error "undefined operand"
    | _ => ExecResult.Error "extcodecopy requires 4 operands"

  -- Label offset computation (semantically ADD)
  | Opcode.OFFSET => execPure2 (. + .) inst s

  -- Logging
  | Opcode.LOG =>
    match inst.operands with
    | Operand.Lit tc :: rest =>
      let n := tc.toNat
      if rest.length != n + 2 then ExecResult.Error "log: wrong operand count"
      else
        let offsetOp := rest[0]!
        let sizeOp := rest[1]!
        let topicOps := rest.drop 2
        match evalOperand offsetOp s, evalOperand sizeOp s, evalOperands topicOps s with
        | some off, some sz, some topics =>
          let data := (readMemory off.toNat sz.toNat s).toList
          let ev : Event := {
            logger := s.callCtx.contract
            topics := topics
            data := data }
          ExecResult.OK { s with logs := s.logs ++ [ev] }
        | _, _, _ => ExecResult.Error "log: undefined operand"
    | _ => ExecResult.Error "log requires Lit topic_count as first operand"

  -- Selfdestruct
  | Opcode.SELFDESTRUCT =>
    match inst.operands with
    | [addrOp] =>
      match evalOperand addrOp s with
      | some addr =>
        let self := s.callCtx.contract
        let selfAcct := lookupAccount self s.accounts
        let bal := selfAcct.balance
        let beneficiary := AccountAddress.ofUInt256 addr
        let benAcct := lookupAccount beneficiary s.accounts
        let newAccounts := ainsert s.accounts self { selfAcct with balance := 0 }
        let newAccounts := ainsert newAccounts beneficiary { benAcct with balance := benAcct.balance + bal }
        ExecResult.Halt (haltState { s with accounts := newAccounts })
      | none => ExecResult.Error "selfdestruct: undefined operand"
    | _ => ExecResult.Error "selfdestruct requires 1 operand"

  -- Invalid opcode
  | Opcode.INVALID =>
    ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s))

  -- Memory Allocation: ALLOCA
  | Opcode.ALLOCA =>
    match inst.operands with
    | [Operand.Lit allocSize] =>
      match inst.outputs with
      | [out] =>
        match alookup s.allocas inst.id with
        | some (offset, _sz) =>
          ExecResult.OK (updateVar out (UInt256.ofNat offset) s)
        | none =>
          let offset := s.allocaNext
          let sz := allocSize.toNat
          let s' := { s with
            allocas := ainsert s.allocas inst.id (offset, sz)
            allocaNext := offset + sz }
          ExecResult.OK (updateVar out (UInt256.ofNat offset) s')
      | _ => ExecResult.Error "alloca requires single output"
    | _ => ExecResult.Error "alloca requires 1 literal operand"

  -- External calls — deferred
  | Opcode.CALL => ExecResult.Error "external calls not yet implemented"
  | Opcode.STATICCALL => ExecResult.Error "external calls not yet implemented"
  | Opcode.DELEGATECALL => ExecResult.Error "external calls not yet implemented"
  | Opcode.CREATE => ExecResult.Error "external calls not yet implemented"
  | Opcode.CREATE2 => ExecResult.Error "external calls not yet implemented"

  -- INVOKE — deferred
  | Opcode.INVOKE =>
    ExecResult.Error "invoke not yet implemented (requires run_block)"

end EvmYul.Venom.Hol

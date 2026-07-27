/-
Venom external calls — sub-EVM model

`stepInstBase` defers CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 to `Error` because a single
instruction step cannot run a callee contract. This module gives them a *full* sub-EVM semantics by
bridging the Venom.Hol simplified account model into the authoritative Yellow-Paper EVM interpreter
(`EvmYul.EVM.Θ` / `Λ`) and bridging the resulting world state back. It is the faithful sub-execution
engine external calls need — value transfer, callee code execution (via `Ξ`/`X`, including nested
calls and revert rollback), address derivation and code deposit for creates.

This is the sub-EVM **model**, verified standalone (reduction lemmas below). Wiring it into
`stepInstBase`/`execBlock` (Venom side) and `asmStep` (asm side) — both of which share the same
`Accounts` type, so a single shared sub-EVM keeps the two sides in correspondence — is the follow-up,
mirroring how INVOKE was modelled first and then wired.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.EVM.Semantics

open EvmYul EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol

/-! ## Account bridge: Venom.Hol simplified model ↔ authoritative EVM account map -/

/-- Venom account → authoritative EVM account (`Nat`→`UInt256`, `List byte`→`ByteArray`,
    `AssocList`→`RBMap` storage). -/
def toEvmAccount (a : VenomAccount) : Account .EVM :=
  { (default : Account .EVM) with
      nonce := UInt256.ofNat a.nonce
      balance := UInt256.ofNat a.balance
      code := ⟨a.code.toArray⟩
      storage := Batteries.RBMap.ofList a.storage compare }

/-- Venom accounts → EVM `AccountMap`. -/
def toAccountMap (accs : Accounts) : AccountMap .EVM :=
  Batteries.RBMap.ofList (accs.map (fun p => (p.1, toEvmAccount p.2))) compare

/-- Authoritative EVM account → Venom account. -/
def fromEvmAccount (a : Account .EVM) : VenomAccount :=
  { balance := a.balance.toNat
    code := a.code.toList
    storage := a.storage.toList
    nonce := a.nonce.toNat }

/-- EVM `AccountMap` → Venom accounts. -/
def fromAccountMap (σ : AccountMap .EVM) : Accounts :=
  σ.foldl (fun acc addr a => (addr, fromEvmAccount a) :: acc) []

/-- `List byte` → `ByteArray`. -/
def bytesToByteArray (bs : List byte) : ByteArray := ⟨bs.toArray⟩

/-! ## External message call — delegated to the authoritative Yellow-Paper EVM (`Θ`) -/

/-- **`evmCall`: a full sub-EVM message call.** Bridges the Venom account model into the authoritative
    EVM `AccountMap`, invokes `EvmYul.EVM.Θ` (the Yellow-Paper message-call function — value transfer,
    callee code execution via `Ξ`/`X`, nested calls, revert rollback), and bridges the resulting state
    back. Returns `(success, newAccounts, returndata)`. `STATICCALL`/`DELEGATECALL` are this same
    function with specialised arguments (`perm := false` / caller-context recipient + retained value). -/
def evmCall (fuel : Nat) (accs : Accounts) (sender origin recipient codeAddr : address)
    (gas value apparentValue : bytes32) (calldata : List byte) (gasprice : bytes32) (depth : Nat)
    (perm : Bool) : bytes32 × Accounts × List byte :=
  let σ := toAccountMap accs
  match EvmYul.EVM.Θ fuel [] default default default σ σ default
      sender origin recipient (toExecute .EVM σ codeAddr)
      gas gasprice value apparentValue (bytesToByteArray calldata) depth default perm with
  | Except.ok (_, σ', _, _, z, out) => (if z then ⟨1⟩ else ⟨0⟩, fromAccountMap σ', out.toList)
  | Except.error _ => (⟨0⟩, accs, [])

/-- **`evmCreate`: a full sub-EVM contract creation.** Delegates to the Yellow-Paper `Λ` (address
    derivation, init-code execution, EIP-3860/170 checks, code deposit). `salt = none` for `CREATE`,
    `some s` for `CREATE2`. Returns `(newAddressOrZero, newAccounts, returndata)` — the new address on
    success (`0` on failure), matching the EVM `CREATE`/`CREATE2` stack result. -/
def evmCreate (fuel : Nat) (accs : Accounts) (sender origin : address) (value : bytes32)
    (initCode : List byte) (gasprice : bytes32) (depth : Nat) (salt : Option (List byte)) :
    bytes32 × Accounts × List byte :=
  let σ := toAccountMap accs
  match EvmYul.EVM.Lambda fuel [] default default default σ σ default
      sender origin gasprice gasprice value (bytesToByteArray initCode) (UInt256.ofNat depth)
      (salt.map bytesToByteArray) default false with
  | Except.ok (addr, _, σ', _, _, z, out) =>
      (if z then UInt256.ofNat addr.val else ⟨0⟩, fromAccountMap σ', out.toList)
  | Except.error _ => (⟨0⟩, accs, [])

/-! ## Reduction lemmas (the model behaves as intended) -/

/-- **`evmCall` success reduction.** When `Θ` succeeds with status `z` and output `out`, `evmCall`
    returns the corresponding success flag, the bridged-back accounts, and the output bytes. -/
theorem evmCall_ok {fuel : Nat} {accs : Accounts} {sender origin recipient codeAddr : address}
    {gas value apparentValue : bytes32} {calldata : List byte} {gasprice : bytes32} {depth : Nat}
    {perm : Bool} {cA} {σ' : AccountMap .EVM} {g' : UInt256} {A'} {z : Bool} {out : ByteArray}
    (h : EvmYul.EVM.Θ fuel [] default default default (toAccountMap accs) (toAccountMap accs) default
      sender origin recipient (toExecute .EVM (toAccountMap accs) codeAddr)
      gas gasprice value apparentValue (bytesToByteArray calldata) depth default perm
      = Except.ok (cA, σ', g', A', z, out)) :
    evmCall fuel accs sender origin recipient codeAddr gas value apparentValue calldata gasprice depth perm
      = (if z then ⟨1⟩ else ⟨0⟩, fromAccountMap σ', out.toList) := by
  simp only [evmCall, h]

/-- **`evmCall` failure reduction.** When `Θ` raises an execution exception, `evmCall` reports failure
    (`0`) and leaves the accounts untouched (the whole call is rolled back). -/
theorem evmCall_error {fuel : Nat} {accs : Accounts} {sender origin recipient codeAddr : address}
    {gas value apparentValue : bytes32} {calldata : List byte} {gasprice : bytes32} {depth : Nat}
    {perm : Bool} {e : EVM.ExecutionException}
    (h : EvmYul.EVM.Θ fuel [] default default default (toAccountMap accs) (toAccountMap accs) default
      sender origin recipient (toExecute .EVM (toAccountMap accs) codeAddr)
      gas gasprice value apparentValue (bytesToByteArray calldata) depth default perm
      = Except.error e) :
    evmCall fuel accs sender origin recipient codeAddr gas value apparentValue calldata gasprice depth perm
      = (⟨0⟩, accs, []) := by
  simp only [evmCall, h]

/-! ## External-call dispatch (interpreter-facing) -/

/-- A generous fuel budget for the sub-EVM: the callee sub-execution is bounded by this constant
    (a single instruction/asm step carries no fuel of its own to thread). -/
def subEvmFuel : Nat := 2 ^ 24

/-- The opcodes handled by `stepExternalCall`. -/
def isExternalCall (o : Opcode) : Bool :=
  o = Opcode.CALL || o = Opcode.STATICCALL || o = Opcode.DELEGATECALL ||
  o = Opcode.CREATE || o = Opcode.CREATE2

/-- No external-call opcode is a terminator (they sit mid-body, and `execBlock` continues past them). -/
theorem isExternalCall_not_terminator {o : Opcode} (h : isExternalCall o = true) :
    isTerminator o = false := by
  unfold isExternalCall at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> decide

/-- No external-call opcode is `INVOKE`. -/
theorem isExternalCall_ne_invoke {o : Opcode} (h : isExternalCall o = true) : o ≠ Opcode.INVOKE := by
  unfold isExternalCall at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> decide

/-- Every external-call opcode is deferred to `Error` by `stepInstBase` (the single-step interpreter
    cannot run a callee) — `execBlock` intercepts it in the `Error` arm. -/
theorem stepInstBase_extcall_error {inst : Instruction} {s : VenomState}
    (h : isExternalCall inst.opcode = true) : ∃ e, stepInstBase inst s = ExecResult.Error e := by
  unfold isExternalCall at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> (simp only [stepInstBase, h]; exact ⟨_, rfl⟩)

/-- Common message-call writeback: record the returned bytes as `returndata`, copy the first
    `retSize` of them to memory at `retOff`, and bind the success flag to `out`. -/
def callWriteback (out : String) (retOff retSize : Nat) (success : bytes32) (newAccs : Accounts)
    (ret : List byte) (s : VenomState) : VenomState :=
  let s1 := { s with accounts := newAccs, returndata := ⟨ret.toArray⟩ }
  let s2 := writeMemoryWithExpansion retOff ⟨(ret.take retSize).toArray⟩ s1
  updateVar out success s2

/-- **External-call step (Venom side).** Dispatches CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 to the
    sub-EVM (`evmCall`/`evmCreate`) over the shared account map, threading calldata/returndata through
    memory and binding the result to the instruction's output; `none` on malformed operands. Wired at
    the `execBlock` driver level (which supplies fuel), mirroring `stepInvoke`. Operand order is
    EVM-stack-top-first, matching the Venom-IR convention (cf. `MCOPY`/`MSTORE`). -/
def stepExternalCall (fuel : Nat) (inst : Instruction) (s : VenomState) : Option VenomState := do
  let vals ← evalOperands inst.operands s
  match inst.opcode, vals, inst.outputs with
  | Opcode.CALL, [gas, addr, value, aOff, aSz, rOff, rSz], [out] =>
    let calldata := (readMemory aOff.toNat aSz.toNat s).toList
    let (success, newAccs, ret) := evmCall fuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value calldata
      s.txCtx.gasprice 0 (!s.callCtx.static)
    some (callWriteback out rOff.toNat rSz.toNat success newAccs ret s)
  | Opcode.STATICCALL, [gas, addr, aOff, aSz, rOff, rSz], [out] =>
    let calldata := (readMemory aOff.toNat aSz.toNat s).toList
    let (success, newAccs, ret) := evmCall fuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩ calldata
      s.txCtx.gasprice 0 false
    some (callWriteback out rOff.toNat rSz.toNat success newAccs ret s)
  | Opcode.DELEGATECALL, [gas, addr, aOff, aSz, rOff, rSz], [out] =>
    -- runs `addr`'s code in the caller's own context (recipient = self, sender = caller's caller,
    -- apparent value = caller's callvalue)
    let calldata := (readMemory aOff.toNat aSz.toNat s).toList
    let (success, newAccs, ret) := evmCall fuel s.accounts s.callCtx.caller s.txCtx.origin
      s.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ s.callCtx.callvalue calldata
      s.txCtx.gasprice 0 (!s.callCtx.static)
    some (callWriteback out rOff.toNat rSz.toNat success newAccs ret s)
  | Opcode.CREATE, [value, off, size], [out] =>
    let initCode := (readMemory off.toNat size.toNat s).toList
    let (addrOrZero, newAccs, _ret) := evmCreate fuel s.accounts s.callCtx.contract s.txCtx.origin
      value initCode s.txCtx.gasprice 0 none
    some (updateVar out addrOrZero { s with accounts := newAccs })
  | Opcode.CREATE2, [value, off, size, salt], [out] =>
    let initCode := (readMemory off.toNat size.toNat s).toList
    let (addrOrZero, newAccs, _ret) := evmCreate fuel s.accounts s.callCtx.contract s.txCtx.origin
      value initCode s.txCtx.gasprice 0 (some (wordToBytes salt).toList)
    some (updateVar out addrOrZero { s with accounts := newAccs })
  | _, _, _ => none

end EvmYul.Venom.Hol

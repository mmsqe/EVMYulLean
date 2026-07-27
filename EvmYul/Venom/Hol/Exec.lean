/-
Venom Multi-Instruction Execution

Port of vyper-hol/venom/defs/venomExecSemanticsScript.sml (execution section)

Provides fuel-based block and function execution.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol

/- ===== Helpers ===== -/

def lookupBlock (lbl : String) (bbs : List BasicBlock) : Option BasicBlock :=
  bbs.find? (λ bb => bb.label = lbl)

def lookupFunction (name : String) (fns : List IrFunction) : Option IrFunction :=
  fns.find? (λ f => f.name = name)

def getInstruction (bb : BasicBlock) (idx : Nat) : Option Instruction :=
  if h : idx < bb.instructions.length then some (bb.instructions.get ⟨idx, h⟩) else none

def fnEntryLabel (fn : IrFunction) : Option String :=
  match fn.blocks.head? with
  | some bb => some bb.label
  | none => none

/- ===== PHI Evaluation ===== -/

def evalOnePhi (s : VenomState) (inst : Instruction) : Option (String × bytes32) :=
  match inst.outputs, s.prevBb with
  | [out], some prev =>
    match resolvePhi prev inst.operands with
    | some valOp => evalOperand valOp s |>.map (λ v => (out, v))
    | none => none
  | _, _ => none

def evalPhis (s : VenomState) : List Instruction → ExecResult
  | [] => ExecResult.OK s
  | inst :: rest =>
    if inst.opcode ≠ Opcode.PHI then ExecResult.OK s
    else
      match evalOnePhi s inst with
      | none => ExecResult.Error "phi evaluation failed"
      | some (out, v) =>
        match evalPhis s rest with
        | ExecResult.OK s' => ExecResult.OK (updateVar out v s')
        | err => err

def phiPrefixLength : List Instruction → Nat
  | [] => 0
  | inst :: rest => if inst.opcode = Opcode.PHI then 1 + phiPrefixLength rest else 0

def getParams : List Instruction → List Instruction
  | [] => []
  | inst :: rest => if inst.opcode = Opcode.PARAM then inst :: getParams rest else []

/- ===== execBlock ===== -/

def execBlock (fuel : Nat) (_ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : ExecResult :=
  match fuel with
  | 0 => ExecResult.Error "out of fuel"
  | fuel' + 1 =>
    match getInstruction bb s.instIdx with
    | none => ExecResult.Error "block not terminated"
    | some inst =>
      match stepInstBase inst s with
      | ExecResult.OK s' =>
        if isTerminator inst.opcode then
          if s'.halted then ExecResult.Halt s' else ExecResult.OK s'
        else execBlock fuel' _ctx bb { s' with instIdx := s.instIdx + 1 }
      | ExecResult.IntRet vals s' => ExecResult.IntRet vals s'
      | ExecResult.Halt s' => ExecResult.Halt s'
      | ExecResult.Abort a s' => ExecResult.Abort a s'
      | ExecResult.Error e => ExecResult.Error e

/- ===== runBlock ===== -/

def runBlock (fuel : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : ExecResult :=
  match evalPhis s bb.instructions with
  | ExecResult.OK sPhi =>
    execBlock fuel ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
  | err => err

/- ===== runBlocks (iterate blocks) ===== -/

def runBlocks (fuel : Nat) (ctx : VenomContext) (fn : IrFunction) (s : VenomState) : ExecResult :=
  match fuel with
  | 0 => ExecResult.Error "out of fuel"
  | fuel' + 1 =>
    match lookupBlock s.currentBb fn.blocks with
    | none => ExecResult.Error "block not found"
    | some bb =>
      match runBlock fuel' ctx bb s with
      | ExecResult.OK s' =>
        if s'.halted then ExecResult.Halt s'
        else runBlocks fuel' ctx fn s'
      | ExecResult.IntRet vals s' => ExecResult.IntRet vals s'
      | other => other

/- ===== runFunction ===== -/

def runFunction (fuel : Nat) (ctx : VenomContext) (fn : IrFunction) (s : VenomState) : ExecResult :=
  match fnEntryLabel fn with
  | none => ExecResult.Error "no entry block"
  | some lbl =>
    runBlocks fuel ctx fn { s with currentBb := lbl, instIdx := 0 }

/- ===== runContext ===== -/

def runContext (fuel : Nat) (ctx : VenomContext) (s : VenomState) : ExecResult :=
  match ctx.entry with
  | none => ExecResult.Error "no entry function"
  | some entryName =>
    match lookupFunction entryName ctx.functions with
    | none => ExecResult.Error "entry function not found"
    | some entryFn =>
      runFunction fuel ctx entryFn { s with prevBb := none }

end EvmYul.Venom.Hol

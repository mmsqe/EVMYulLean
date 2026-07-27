/-
Venom Multi-Instruction Execution

Port of vyper-hol/venom/defs/venomExecSemanticsScript.sml (execution section)

Provides fuel-based block and function execution.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.SubEvm
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

/- ===== INVOKE call helpers (pure) ===== -/

/-- Find the function whose entry block carries label `lbl` — the callee an `INVOKE`/`JUMP l`
    targets (the compiled `JUMP` lands on the callee's entry label). -/
def lookupFunctionByEntry (lbl : String) (fns : List IrFunction) : Option IrFunction :=
  fns.find? (fun f => fnEntryLabel f == some lbl)

/-- Bind a callee's internal-return values positionally to the caller's output vars. Later writes
    shadow earlier ones (matching `updateVar`/`ainsert`); on arity mismatch the extra side is
    dropped (`stepInvoke` guards arity separately). -/
def bindOutputs : List String → List bytes32 → VenomState → VenomState
  | [], _, s => s
  | _, [], s => s
  | out :: outs, v :: vs, s => bindOutputs outs vs (updateVar out v s)

/- ===== Block / function execution =====

`execBlock`, `stepInvoke`, `runBlock`, `runBlocks`, `runFunction` are mutually recursive so that
`INVOKE` (an intra-contract call) can run a whole callee via `runFunction` from inside `execBlock`.
Fuel threading is unchanged from the earlier non-mutual defs (`runBlock`/`runFunction` pass fuel
through; `execBlock`/`runBlocks` decrement); the `INVOKE` call spends one fuel. Termination is by the
single measure `10*fuel + tag` (tags: execBlock 0, runBlock 1, runBlocks 2, runFunction 3,
stepInvoke 4), which strictly decreases on every call (fuel drop dominates the ≤4 tag spread). -/

mutual

/-- Execute the instructions of a single block from `s.instIdx` to its terminator. `INVOKE` is wired
    in the `Error` arm — `stepInstBase` defers `INVOKE` to `Error`, and there `execBlock` runs the
    callee via `stepInvoke` (mutual) and continues past the call. Placing it in the `Error` arm keeps
    the `OK`/`Halt`/`Abort` arms (the ones the block-simulation proofs case on) byte-for-byte. -/
def execBlock (fuel : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : ExecResult :=
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
        else execBlock fuel' ctx bb { s' with instIdx := s.instIdx + 1 }
      | ExecResult.IntRet vals s' => ExecResult.IntRet vals s'
      | ExecResult.Halt s' => ExecResult.Halt s'
      | ExecResult.Abort a s' => ExecResult.Abort a s'
      | ExecResult.Error e =>
        if inst.opcode = Opcode.INVOKE then
          match stepInvoke fuel' ctx inst s with
          | ExecResult.OK s' => execBlock fuel' ctx bb { s' with instIdx := s.instIdx + 1 }
          | ExecResult.IntRet vals s' => ExecResult.IntRet vals s'
          | ExecResult.Halt s' => ExecResult.Halt s'
          | ExecResult.Abort a s' => ExecResult.Abort a s'
          | ExecResult.Error e' => ExecResult.Error e'
        else if isExternalCall inst.opcode then
          -- external call: run the sub-EVM (`stepExternalCall`, self-contained via `Θ`/`Λ`, no
          -- recursion back into `execBlock`), then continue past the call
          match stepExternalCall subEvmFuel inst s with
          | some s' => execBlock fuel' ctx bb { s' with instIdx := s.instIdx + 1 }
          | none => ExecResult.Error e
        else ExecResult.Error e
  termination_by 10 * fuel
  decreasing_by all_goals omega

/-- **INVOKE step.** Operand `[0]` is the callee's entry `Label l`, the rest are argument operands.
    Evaluate the args, install them as the callee's `params`, run the callee to its internal `RET`
    (`IntRet`), and bind the returned values to `INVOKE`'s outputs; callee `Halt`/`Abort` propagate.

    **Divergence from upstream HOL (documented decision, 2026-07-24).** HOL's
    `setup_callee`/`merge_callee_state` give the callee a FRESH frame (`vars := FEMPTY`,
    `allocas := FEMPTY`, `halted := F`) and restore the caller's vars/params/allocas on return,
    merging back only heap effects; the callee is resolved by *function name*. Here the callee
    inherits the caller's `vars`/`allocas`, the caller continues in the callee's final state
    (params not restored), and resolution is by *entry label* (`lookupFunctionByEntry`). For
    SSA-wf Venom (globally unique var names, `PARAM` only before any `INVOKE`, allocas hoisted)
    the two disciplines are observationally equal; they differ only off the wf path (callee reads
    of caller-locals succeed here / error in HOL; re-INVOKE of an ALLOCA-using callee reuses
    offsets here / gets a fresh frame in HOL). Both systems' correctness theorems assume wf, so
    no proven result depends on the difference; kept because changing it would rework the whole
    invoke-simulation layer for no wf-path gain. See hol-port-audit.md (D2). -/
def stepInvoke (fuel : Nat) (ctx : VenomContext) (inst : Instruction) (s : VenomState) : ExecResult :=
  match inst.operands with
  | Operand.Label l :: argOps =>
    match evalOperands argOps s with
    | some argVals =>
      match lookupFunctionByEntry l ctx.functions with
      | some callee =>
        match runFunction fuel ctx callee { s with params := argVals, prevBb := none } with
        | ExecResult.IntRet retVals s' =>
          if inst.outputs.length = retVals.length then
            ExecResult.OK (bindOutputs inst.outputs retVals s')
          else ExecResult.Error "invoke: return arity mismatch"
        | ExecResult.Halt s' => ExecResult.Halt s'
        | ExecResult.Abort a s' => ExecResult.Abort a s'
        | ExecResult.Error e => ExecResult.Error e
        | ExecResult.OK _ => ExecResult.Error "invoke: callee did not RET"
      | none => ExecResult.Error "invoke: unknown callee"
    | none => ExecResult.Error "invoke: undefined argument"
  | _ => ExecResult.Error "invoke: missing target label"
  termination_by 10 * fuel + 4
  decreasing_by all_goals omega

/-- Run a block including its phi-prefix evaluation. -/
def runBlock (fuel : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : ExecResult :=
  match evalPhis s bb.instructions with
  | ExecResult.OK sPhi =>
    execBlock fuel ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
  | err => err
  termination_by 10 * fuel + 1
  decreasing_by all_goals omega

/-- Iterate blocks following control flow until halt/return. -/
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
  termination_by 10 * fuel + 2
  decreasing_by all_goals omega

/-- Run a function from its entry block. -/
def runFunction (fuel : Nat) (ctx : VenomContext) (fn : IrFunction) (s : VenomState) : ExecResult :=
  match fnEntryLabel fn with
  | none => ExecResult.Error "no entry block"
  | some lbl =>
    runBlocks fuel ctx fn { s with currentBb := lbl, instIdx := 0 }
  termination_by 10 * fuel + 3
  decreasing_by all_goals omega

end

/- ===== runContext ===== -/

def runContext (fuel : Nat) (ctx : VenomContext) (s : VenomState) : ExecResult :=
  match ctx.entry with
  | none => ExecResult.Error "no entry function"
  | some entryName =>
    match lookupFunction entryName ctx.functions with
    | none => ExecResult.Error "entry function not found"
    | some entryFn =>
      runFunction fuel ctx entryFn { s with prevBb := none }

/-! ## INVOKE step lemmas

`INVOKE` (intra-contract call) is now wired into `execBlock` via the mutual `stepInvoke` above. These
lemmas characterise `stepInvoke`'s reductions on the successful-call and callee-halt paths, and the
single-result read-back. -/

/-- **INVOKE success path.** When the callee (found by entry label) runs to an internal return
    `IntRet retVals s'` with matching output arity, `stepInvoke` yields `OK` with the returns bound to
    the caller's outputs — the model reduces as intended on a successful call. -/
theorem stepInvoke_ok_of_intRet {fuel : Nat} {ctx : VenomContext} {inst : Instruction} {s : VenomState}
    {l : String} {argOps : List Operand} {argVals retVals : List bytes32}
    {callee : IrFunction} {s' : VenomState}
    (hops : inst.operands = Operand.Label l :: argOps)
    (hargs : evalOperands argOps s = some argVals)
    (hlk : lookupFunctionByEntry l ctx.functions = some callee)
    (hrun : runFunction fuel ctx callee { s with params := argVals, prevBb := none }
      = ExecResult.IntRet retVals s')
    (harity : inst.outputs.length = retVals.length) :
    stepInvoke fuel ctx inst s = ExecResult.OK (bindOutputs inst.outputs retVals s') := by
  unfold stepInvoke
  rw [hops]
  simp only [hargs, hlk, hrun, if_pos harity]

/-- **INVOKE propagates a callee halt.** A callee that `RETURN`/`STOP`s (`Halt`) surfaces the halt to
    the caller unchanged. -/
theorem stepInvoke_halt_of_calleeHalt {fuel : Nat} {ctx : VenomContext} {inst : Instruction}
    {s : VenomState} {l : String} {argOps : List Operand} {argVals : List bytes32}
    {callee : IrFunction} {s' : VenomState}
    (hops : inst.operands = Operand.Label l :: argOps)
    (hargs : evalOperands argOps s = some argVals)
    (hlk : lookupFunctionByEntry l ctx.functions = some callee)
    (hrun : runFunction fuel ctx callee { s with params := argVals, prevBb := none }
      = ExecResult.Halt s') :
    stepInvoke fuel ctx inst s = ExecResult.Halt s' := by
  unfold stepInvoke
  rw [hops]
  simp only [hargs, hlk, hrun]

/-- **Single-output INVOKE reads back its return value.** For one output var, `bindOutputs` binds it
    to the single returned value, and the caller reads it back — the single-result invoke shape. -/
theorem bindOutputs_single_lookup (out : String) (v : bytes32) (s : VenomState) :
    lookupVar out (bindOutputs [out] [v] s) = some v := by
  show lookupVar out (updateVar out v s) = some v
  simp only [lookupVar, updateVar, alookup, ainsert, AssocList.insert, AssocList.lookup,
    beq_self_eq_true, if_true]

end EvmYul.Venom.Hol

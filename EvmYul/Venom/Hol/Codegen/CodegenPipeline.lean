/-
Top-Level Codegen Pipeline + Codegen Readiness — Property Definitions

Port of vyper-hol/venom/codegen/defs/codegenScript.sml
       + vyper-hol/venom/codegen/defs/stackPlanGenScript.sml (codegen_ready + API)

Defines:
  - codegen_ready_inst / codegen_ready_fn / codegen_ready: preconditions
  - generate_context_plan: signature (algorithm deferred to analyses)
  - codegen: top-level pipeline (plan_gen → execute_plan → assemble)

NO proofs — property definitions only.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.PlanTypes
import EvmYul.Venom.Hol.Codegen.PlanOps
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.Hol.Codegen.SymbolResolve
import EvmYul.Venom.Hol.Codegen.DfgAnalysis
import EvmYul.Venom.Hol.Codegen.Liveness
import EvmYul.Venom.Hol.Codegen.LivenessAnalysis
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/- ===== Codegen Preconditions ===== -/

/-- Opcodes that must be eliminated by earlier passes before codegen:
    ALLOCA — eliminated by mem2var / memory layout
    SINK   — test-only pseudo-instruction
    DLOAD, DLOADBYTES — lowered by lower_dload pass -/
def isPreCodegenOpcode : Opcode → Bool
  | Opcode.ALLOCA => true
  | Opcode.SINK => true
  | Opcode.DLOAD => true
  | Opcode.DLOADBYTES => true
  | _ => false

/-- Per-instruction: no pre-codegen opcodes allowed. -/
def codegenReadyInst (inst : Instruction) : Prop :=
  ¬ isPreCodegenOpcode inst.opcode

/-- Per-function: structural WF + SSA + SUE + normalized CFG + no bad opcodes.
    These preconditions are discharged by earlier passes in the pipeline.
    For our property definitions, we state them as assumptions (Props). -/
def codegenReadyFn (fn : IrFunction) : Prop :=
  -- All instructions satisfy codegen_ready_inst
  (∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) ∧
  -- Well-formedness conditions (stated as Props, to be proved by earlier passes)
  True

/-- Per-context: all functions ready. -/
def codegenReady (ctx : VenomContext) : Prop :=
  ∀ fn ∈ ctx.functions, codegenReadyFn fn

/- ===== Context-Wellformedness ===== -/

/-- A context is well-formed: functions have unique names and all labels valid. -/
def ctxWf (_ctx : VenomContext) : Prop := True  -- simplified

/- ===== Plan-generator leaf defs =====
   Transcribed from vyper-hol `main:venom/codegen/defs/stackPlanGenScript.sml`.
   These are the analysis-free pieces (use only `inst` / `nextLiveness : List String`
   / `PlanState` + ported `PlanOps`). The dfg-dependent `optimistic_swap_plan` /
   `generate_regular_inst_plan` / `generate_inst_plan` and the block/fn/context
   composition are deferred (see `generate*Plan` below, still `none`). -/

/-- `operand_to_string`: a `Var`'s name, else `""`. -/
def operandToString : Operand → String
  | Operand.Var s   => s
  | Operand.Lit _   => ""
  | Operand.Label _ => ""

/-- `fresh_label`: a unique label drawn from the plan-state counter. -/
def freshLabel (pfx : String) (ps : PlanState) : String × PlanState :=
  let n := ps.labelCounter + 1
  (pfx ++ "_" ++ toString n, { ps with labelCounter := n })

/-- `emit_one_input`: restore if spilled, then push label/lit or dup a live var. -/
def emitOneInput (opc : Opcode) (nextLiveness : List String) (op : Operand)
    (ps : PlanState) : List StackOp × PlanState :=
  let (restoreOps, ps1) :=
    if isVarOperand op && (alookup' ps.spilled op).isSome then doRestore op ps
    else ([], ps)
  match op with
  | Operand.Label l =>
    let ps2 := { ps1 with stack := stackPush op ps1.stack }
    if opc = Opcode.INVOKE then (restoreOps, ps2)
    else (restoreOps ++ [StackOp.SOPushLabel l], ps2)
  | Operand.Lit v =>
    (restoreOps ++ [StackOp.SOPush (Operand.Lit v)],
     { ps1 with stack := stackPush op ps1.stack })
  | Operand.Var v =>
    if nextLiveness.contains v then
      match stackGetDepth op ps1.stack with
      | some dist => let (dupOps, ps2) := doDup dist ps1; (restoreOps ++ dupOps, ps2)
      | none => (restoreOps, ps1)
    else (restoreOps, ps1)

/-- `emit_input_plan`: emit all input operands left to right. -/
def emitInputPlan (opc : Opcode) (ops : List Operand) (nextLiveness : List String)
    (ps : PlanState) : List StackOp × PlanState :=
  ops.foldl (fun (acc : List StackOp × PlanState) op =>
    let (stepOps, ps') := emitOneInput opc nextLiveness op acc.2
    (acc.1 ++ stepOps, ps'))
    ([], ps)

/-- `generate_phi_plan`: place the phi result at the right depth. -/
def generatePhiPlan (inst : Instruction) (nextLiveness : List String)
    (ps : PlanState) : List StackOp × PlanState :=
  let phiVars := inst.operands.filter isVarOperand
  match stackGetPhiDepth phiVars ps.stack with
  | none => ([], ps)
  | some dist =>
    let atDepth := stackPeek dist ps.stack
    let ret := Operand.Var (inst.outputs.head!)
    if nextLiveness.contains (operandToString atDepth) then
      let (dupOps, ps') := doDup dist ps
      let ps'' := { ps' with stack := stackPoke 0 ret ps'.stack }
      (dupOps ++ [StackOp.SOPoke 0 ret], ps'')
    else
      let ps' := { ps with stack := stackPoke dist ret ps.stack }
      ([StackOp.SOPoke dist ret], ps')

/-- `generate_offset_plan`: push `(label + offset)`. -/
def generateOffsetPlan (inst : Instruction) (ps : PlanState) : List StackOp × PlanState :=
  let ofstVal := inst.operands.head!
  let labelOp := inst.operands[1]!
  let n := match ofstVal with | Operand.Lit v => v.toNat | _ => 0
  let ret := Operand.Var (inst.outputs.head!)
  match labelOp with
  | Operand.Label l => ([StackOp.SOPushOfst l n], { ps with stack := stackPush ret ps.stack })
  | _ => ([], ps)

/-- `generate_emit_ops`: per-opcode EVM emission. -/
def generateEmitOps (inst : Instruction) (logTopicCount : Nat)
    (ps : PlanState) : List StackOp × PlanState :=
  let opc := inst.opcode
  match opcodeToEvmName opc with
  | some name => ([StackOp.SOEmit name], ps)
  | none =>
    if opc = Opcode.JNZ then
      match inst.operands.filter isLabelOperand with
      | [Operand.Label ifNz, Operand.Label ifZ] =>
        ([StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
          StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"], ps)
      | _ => ([], ps)
    else if opc = Opcode.JMP then
      match inst.operands with
      | [Operand.Label target] => ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], ps)
      | _ => ([], ps)
    else if opc = Opcode.DJMP then ([StackOp.SOEmit "JUMP"], ps)
    else if opc = Opcode.INVOKE then
      match inst.operands.head! with
      | Operand.Label l =>
        let (retLbl, ps') := freshLabel "return_label" ps
        ([StackOp.SOPushLabel retLbl, StackOp.SOPushLabel l,
          StackOp.SOEmit "JUMP", StackOp.SOLabel retLbl], ps')
      | _ => ([], ps)
    else if opc = Opcode.RET then ([StackOp.SOEmit "JUMP"], ps)
    else if opc = Opcode.ASSERT then
      ([StackOp.SOEmit "ISZERO", StackOp.SOPushLabel "revert", StackOp.SOEmit "JUMPI"], ps)
    else if opc = Opcode.ASSERT_UNREACHABLE then
      let (endLbl, ps') := freshLabel "reachable" ps
      ([StackOp.SOPushLabel endLbl, StackOp.SOEmit "JUMPI",
        StackOp.SOEmit "INVALID", StackOp.SOLabel endLbl], ps')
    else if opc = Opcode.LOG then
      ([StackOp.SOEmit ("LOG" ++ toString logTopicCount)], ps)
    else if opc = Opcode.ISTORE then
      ([StackOp.SOEmit "SWAP1", StackOp.SOEmit "MSTORE"], ps)
    else ([], ps)

/-- `compute_operands`: which operands go on the stack, in EVM **stack order** (TOS = rightmost).

    Convention note: this port keeps `inst.operands` in *semantic* order (`operands[0]` = the first
    source argument), which is what the reference interpreter reads — e.g. `execPure2 f [op1,op2] =
    f op1 op2`. Vyper, by contrast, stores operands already in *stack* order (its parser/builder do
    `operands.reverse()` / `*reversed(args)` — "venom internally represents top of stack as rightmost
    operand"), and `_generate_evm_for_instruction` consumes that stack order. Since the rest of this
    generator (`emitInputPlan`/`reorderPlan`, last-operand-on-top) is a faithful transcription of
    Vyper's codegen, it expects stack order too. So we perform the semantic→stack reversal *here*
    (the analog of Vyper's parser reversal) for the pure/arithmetic ops, so the generated EVM
    computes `f` in the operand order the interpreter specifies. Without this, non-commutative
    binops (SUB/DIV/LT/SHL/…) miscompile to `f op2 op1`.
    Control-flow ops (JMP/JNZ/DJMP/INVOKE) are *not* reversed — Vyper excludes them from the parser
    reversal too. LOG drops its `Lit` topic-count head (`.tail`) then reverses the remaining
    `[offset, size, topic₀…]`: EVM `LOGn` (and `asmLog`) want `offset` on top of the stack, so the
    stack-order emission must place it last — without the reversal offset/size/topics come out reversed
    (the interpreter reads `memory[topicₙ₋₁,…]` with scrambled topics). -/
def computeOperands (inst : Instruction) : List Operand :=
  let opc := inst.opcode
  if [Opcode.JMP, Opcode.DJMP, Opcode.JNZ, Opcode.INVOKE].contains opc then
    getNonLabelOperands inst
  else if opc = Opcode.LOG then
    inst.operands.tail.reverse
  else
    inst.operands.reverse

/-- `is_commutative` (from `venom/defs/venomEffectsScript.sml`): operands of these
    opcodes may be reordered freely. Used by the commutative-reorder optimization in
    `generate_regular_inst_plan`. -/
def isCommutative : Opcode → Bool
  | Opcode.ADD => true
  | Opcode.MUL => true
  | Opcode.OR  => true
  | Opcode.XOR => true
  | Opcode.AND => true
  | Opcode.EQ  => true
  | _          => false

/-- `reorder_cost`: the stack cost of a reorder = number of swap/spill/restore ops.
    Used to pick the cheaper of two operand orders for commutative opcodes. -/
def reorderCost (ops : List StackOp) : Nat :=
  (ops.filter (fun op => match op with
    | StackOp.SOSwap _ => true
    | StackOp.SOSpill _ => true
    | StackOp.SORestore _ => true
    | _ => false)).length

/- ===== Per-instruction plan generation ===== -/

/-- `optimistic_swap_plan`: if the next-scheduled var differs from the current top,
    bring it to the top with a swap (skipped at terminators / when nothing useful). -/
def optimisticSwapPlan (dfg : DfgAnalysis) (inst : Instruction) (nextLiveness : List String)
    (nextIsTerminator : Bool) (ps : PlanState) : List StackOp × PlanState :=
  if nextIsTerminator then ([], ps)
  else if inst.outputs.isEmpty then ([], ps)
  else if nextLiveness.isEmpty then ([], ps)
  else
    let nextScheduled := nextLiveness.getLast!
    let currentTop := inst.outputs.getLast!
    if operandEquiv dfg (Operand.Var currentTop) (Operand.Var nextScheduled) then ([], ps)
    else
      match stackGetDepth (Operand.Var nextScheduled) ps.stack with
      | none      => ([], ps)
      | some dist => doSwap dist ps

/-- `generate_regular_inst_plan`: the main per-instruction path (`_generate_evm_for_instruction`,
    non-phi/offset cases). Transcribed from `main:stackPlanGenScript.sml`. -/
def generateRegularInstPlan (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (_cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    : List StackOp × PlanState :=
  let opc := inst.opcode
  let operands := computeOperands inst
  let logTopicCount :=
    match opc with
    | Opcode.LOG => match inst.operands.head! with | Operand.Lit v => v.toNat | _ => 0
    | _ => 0
  -- emit input operands
  let (inputOps, ps1) := emitInputPlan opc operands nextLiveness ps
  -- join-point reorder (jmp only)
  let (joinOps, ps2) :=
    if opc = Opcode.JMP then
      match inst.operands with
      | [Operand.Label target] =>
        let targetLive := liveVarsAt liveness target 0
        match fn.blocks.find? (·.label == target) with
        | none => ([], ps1)
        | some targetBb =>
          let targetStack := inputVarsFrom curBbLabel targetBb.instructions targetLive
          reorderPlan (targetStack.map Operand.Var) ps1
      | _ => ([], ps1)
    else ([], ps1)
  -- commutative optimization: pick the cheaper of the two operand orders
  let (operands', ps3) :=
    if isCommutative opc && operands.length ≥ 2 then
      let (opsA, _) := reorderPlan operands ps2
      let n := operands.length
      let swapped := operands.take (n - 2) ++ [operands[n - 1]!, operands[n - 2]!]
      let (opsB, _) := reorderPlan swapped ps2
      if reorderCost opsA < reorderCost opsB then (operands, ps2) else (swapped, ps2)
    else (operands, ps2)
  -- final reorder
  let (reorderOps, ps4) := reorderPlan operands' ps3
  -- pop consumed, push outputs
  let ps5 := { ps4 with stack := stackPop operands'.length ps4.stack }
  let outputs := inst.outputs
  let ps6 := outputs.foldl (fun ps' out => { ps' with stack := stackPush (Operand.Var out) ps'.stack }) ps5
  -- emit EVM opcode(s)
  let (emitOps, ps7) := generateEmitOps inst logTopicCount ps6
  -- post-processing
  if outputs.isEmpty then
    let ps8 := releaseDeadSpills nextLiveness ps7
    (inputOps ++ joinOps ++ reorderOps ++ emitOps, ps8)
  else
    let (popOps, ps8) :=
      if ¬ isHalting then
        let dead := outputs.filter (fun out => ¬ nextLiveness.contains out)
        popmanyPlan (dead.map Operand.Var) ps7
      else ([], ps7)
    let liveOuts := outputs.filter (fun out => nextLiveness.contains out)
    let (optOps, ps9) :=
      if liveOuts.isEmpty then ([], ps8)
      else optimisticSwapPlan dfg inst nextLiveness nextIsTerminator ps8
    let ps10 := releaseDeadSpills nextLiveness ps9
    (inputOps ++ joinOps ++ reorderOps ++ emitOps ++ popOps ++ optOps, ps10)

/- ===== Plan Generator API ===== -/

/-- `generate_inst_plan`: dispatch to phi / offset / param / nop / regular.
    `none` iff an opcode that earlier passes should have eliminated is encountered. -/
def generateInstPlan (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    : Option (List StackOp × PlanState) :=
  if isPreCodegenOpcode inst.opcode then none
  else if inst.opcode = Opcode.PHI then some (generatePhiPlan inst nextLiveness ps)
  else if inst.opcode = Opcode.OFFSET then some (generateOffsetPlan inst ps)
  else if inst.opcode = Opcode.PARAM then some ([], ps)
  else if inst.opcode = Opcode.NOP then some ([], ps)
  else some (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
               nextIsTerminator curBbLabel ps)

/- ===== Per-block plan generation ===== -/

/-- `is_halting_opcode`. -/
def isHaltingOpcode : Opcode → Bool
  | Opcode.RETURN | Opcode.REVERT | Opcode.STOP | Opcode.INVALID | Opcode.SELFDESTRUCT => true
  | _ => false

/-- `bb_is_halting`. -/
def bbIsHalting (bb : BasicBlock) : Bool :=
  match bb.instructions with
  | []    => false
  | insts => isHaltingOpcode insts.getLast!.opcode

/-- `get_params`: the leading PARAM instructions of a block. -/
def getParams : List Instruction → List Instruction
  | []          => []
  | inst :: rest => if inst.opcode = Opcode.PARAM then inst :: getParams rest else []

/-- `non_param_insts`. -/
def nonParamInsts (bb : BasicBlock) : List Instruction :=
  bb.instructions.filter (fun inst => inst.opcode != Opcode.PARAM)

/-- `prepare_params_plan`: push the entry block's params, pop the dead ones. -/
def prepareParamsPlan (liveness : DfState (List String)) (fn : IrFunction) (ps : PlanState)
    : List StackOp × PlanState :=
  match fn.blocks with
  | []           => ([], ps)
  | entry :: _ =>
    let params := getParams entry.instructions
    if params.isEmpty then ([], ps)
    else
      let ps' := params.foldl
        (fun ps' inst => { ps' with stack := stackPush (Operand.Var inst.outputs.head!) ps'.stack }) ps
      let nextLive := liveVarsAt liveness entry.label params.length
      let toPop := ps'.stack.filter (fun v => ¬ nextLive.contains (operandToString v))
      let toPopVars := toPop.filter isVarOperand
      let (popOps, ps'') := popmanyPlan toPopVars ps'
      let firstNonParam := entry.instructions.find? (fun inst => inst.opcode != Opcode.PARAM)
      let nextIsTerm := match firstNonParam with | some inst => isTerminator inst.opcode | none => false
      let (swapOps, ps''') := optimisticSwapPlan DfgAnalysis.empty params.getLast! nextLive nextIsTerm ps''
      (popOps ++ swapOps, ps''')

/-- `clean_stack_plan`: at a single-predecessor join with a branching predecessor,
    pop the values the predecessor's exit layout has but this block doesn't want. -/
def cleanStackPlan (liveness : DfState (List String)) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) : List StackOp × PlanState :=
  match cfg.predsOf bb.label with
  | [predLbl] =>
    if (cfg.succsOf predLbl).length ≤ 1 then ([], ps)
    else
      match fn.blocks.find? (·.label == predLbl) with
      | none => ([], ps)
      | some predBb =>
        let inputs := inputVarsFrom predLbl bb.instructions (liveVarsAt liveness bb.label 0)
        let layout := liveVarsAt liveness predLbl predBb.instructions.length
        let toPop := layout.filter (fun v => ¬ inputs.contains v)
        popmanyPlan (toPop.map Operand.Var) ps
  | _ => ([], ps)

/-- `generate_block_plan`: a block's plan = `JUMPDEST` + params + clean-stack + the
    folded per-instruction plans. `none` iff some instruction is rejected. -/
def generateBlockPlan (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) : Option (List StackOp × PlanState) :=
  let labelOp := [StackOp.SOLabel bb.label]
  let (paramOps, ps1) :=
    if (fn.blocks.head?.map (·.label)) == some bb.label then prepareParamsPlan liveness fn ps
    else ([], ps)
  let (cleanOps, ps2) :=
    if (cfg.predsOf bb.label).length = 1 then cleanStackPlan liveness cfg fn bb ps1
    else ([], ps1)
  let insts := nonParamInsts bb
  let isHalting := bbIsHalting bb
  let nParams := (getParams bb.instructions).length
  let result := insts.zipIdx.foldl
    (fun (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat) =>
      match acc with
      | none => none
      | some (ops, ps) =>
        let (inst, i) := instI
        let nextLive :=
          if i + 1 < insts.length then liveVarsAt liveness bb.label (i + nParams + 1)
          else liveVarsAt liveness bb.label bb.instructions.length
        let nextIsTerm := if i + 1 < insts.length then isTerminator insts[i + 1]!.opcode else false
        match generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm bb.label ps with
        | none => none
        | some (stepOps, ps') => some (ops ++ stepOps, ps'))
    (some ([], ps2))
  match result with
  | none => none
  | some (instOps, ps3) => some (labelOp ++ paramOps ++ cleanOps ++ instOps, ps3)

/- ===== Per-function plan (DFS over blocks) ===== -/

-- `generate_fn_plan_aux` / `generate_succs_plan`: a DFS over the CFG generating each
-- block's plan once (mutual recursion with a `visited` set, plan-state branched per
-- successor). HOL proves termination by a manual WF measure; here it's structural on
-- `fuel`, supplied generously by `fnPlanFuel`.
mutual
def generateFnPlanAux : Nat → DfState (List String) → DfgAnalysis → CfgAnalysis → IrFunction →
    List String → List String → PlanState → Option (List StackOp × List String × PlanState)
  | 0,        _,        _,   _,   _,  _,           visited, ps => some ([], visited, ps)
  | _ + 1,    _,        _,   _,   _,  [],          visited, ps => some ([], visited, ps)
  | fuel + 1, liveness, dfg, cfg, fn, lbl :: rest, visited, ps =>
    if visited.contains lbl then generateFnPlanAux fuel liveness dfg cfg fn rest visited ps
    else
      let visited' := lbl :: visited
      match fn.blocks.find? (·.label == lbl) with
      | none => generateFnPlanAux fuel liveness dfg cfg fn rest visited' ps
      | some bb =>
        match generateBlockPlan liveness dfg cfg fn bb ps with
        | none => none
        | some (blockOps, ps') =>
          match generateSuccsPlan fuel liveness dfg cfg fn ps'.stack ps'.spilled
                  (cfg.succsOf lbl) visited' ps' with
          | none => none
          | some (succOps, visited'', ps'') =>
            match generateFnPlanAux fuel liveness dfg cfg fn rest visited'' ps'' with
            | none => none
            | some (restOps, vF, psF) => some (blockOps ++ succOps ++ restOps, vF, psF)
def generateSuccsPlan : Nat → DfState (List String) → DfgAnalysis → CfgAnalysis → IrFunction →
    List Operand → SpilledMap → List String → List String → PlanState →
    Option (List StackOp × List String × PlanState)
  | 0,        _,        _,   _,   _,  _,          _,            _,           visited, ps => some ([], visited, ps)
  | _ + 1,    _,        _,   _,   _,  _,          _,            [],          visited, ps => some ([], visited, ps)
  | fuel + 1, liveness, dfg, cfg, fn, savedStack, savedSpilled, succ :: rest, visited, psG =>
    let psBranch := { psG with stack := savedStack, spilled := savedSpilled }
    match generateFnPlanAux fuel liveness dfg cfg fn [succ] visited psBranch with
    | none => none
    | some (sOps, vAfter, psAfter) =>
      let psG' := { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
      match generateSuccsPlan fuel liveness dfg cfg fn savedStack savedSpilled rest vAfter psG' with
      | none => none
      | some (restOps, vF, psF) => some (sOps ++ restOps, vF, psF)
end

/-- A generous DFS fuel: the `visited` set caps real work; fuel must merely exceed the
    total recursive-call count (≤ a polynomial in #blocks + #edges). -/
def fnPlanFuel (fn : IrFunction) : Nat :=
  let b := fn.blocks.length
  let e := fn.blocks.foldl (fun a bb => a + (bbSuccs bb).length) 0
  (b + 1) * (b + e + 2) + 10

/-- `generate_fn_plan_fuel`. -/
def generateFnPlanFuel (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat)
    : Option (List StackOp × PlanState) :=
  let liveness := livenessAnalyzeFuel fuel fn
  let dfg := DfgAnalysis.buildFunction fn
  let cfg := cfgAnalyze fn
  let ps := { initPlanState fnEom with labelCounter := lblCtr }
  match (entryBlock fn).map (·.label) with
  | none     => some ([], ps)
  | some lbl =>
    match generateFnPlanAux fuel liveness dfg cfg fn [lbl] [] ps with
    | none            => none
    | some (ops, _, ps') => some (ops, ps')

/-- `generate_fn_plan` (the well-founded HOL version; here `fnPlanFuel` supplies the bound). -/
def generateFnPlan (fn : IrFunction) (fnEom lblCtr : Nat) : Option (List StackOp × PlanState) :=
  generateFnPlanFuel (fnPlanFuel fn) fn fnEom lblCtr

/-- `revert_postamble`. -/
def revertPostamble : List StackOp :=
  [StackOp.SOLabel "revert", StackOp.SOPush (Operand.Lit (UInt256.ofNat 0)),
   StackOp.SOEmit "DUP1", StackOp.SOEmit "REVERT"]

/-- `generate_context_plan_fuel`: compose the per-function plans (threading the label
    counter), then append the shared revert postamble. This makes the **fuel**
    pipeline (`codegenFuel`) a real, executable codegen. -/
def generateContextPlanFuel (fuel : Nat) (ctx : VenomContext)
    (fnEomMap : AssocList String Nat) : Option (List StackOp) :=
  let result := ctx.functions.foldl
    (fun (acc : Option (List StackOp × Nat)) fn =>
      match acc with
      | none => none
      | some (ops, lblCtr) =>
        let eom := (AssocList.lookup String Nat fnEomMap fn.name).getD 0
        match generateFnPlanFuel fuel fn eom lblCtr with
        | none => none
        | some (fnOps, ps) => some (ops ++ fnOps, ps.labelCounter))
    (some ([], 0))
  match result with
  | none => none
  | some (allOps, _) => some (allOps ++ revertPostamble)

/-- A generous whole-context plan fuel: the per-function `fnPlanFuel` caps each function's DFS work,
    and the extra base covers the liveness fixpoint; the sum bounds every function's need (the fuel is
    applied per function inside `generateContextPlanFuel`). -/
def contextPlanFuel (ctx : VenomContext) : Nat :=
  ctx.functions.foldl (fun acc fn => acc + fnPlanFuel fn) 1000

/-- Generate stack plan for entire context (all functions).
    fn_eom_map maps function names to their frame end-of-memory offsets.
    Returns NONE if any function fails.  Now **real** (was a `none` stub): delegates to the fuel
    pipeline with the generous `contextPlanFuel`, so `codegen` is the executable codegen and
    `codegen_correct`'s premise is satisfiable (de-vacuified) — see `CodegenCorrectness`.  Since
    `contextPlanFuel` may be insufficient for a pathological context, `codegen` can still return
    `none` there; the correctness theorem only fires when it returns `some`, so this never weakens it. -/
def generateContextPlan (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    : Option (List StackOp) :=
  generateContextPlanFuel (contextPlanFuel ctx) ctx fnEomMap

/- ===== Top-Level Codegen Pipeline ===== -/

/--
Full codegen pipeline:
  1. generate_context_plan : VenomContext → stack_op list
  2. execute_plan         : stack_op list → asm_inst list
  3. assemble             : asm_inst list → byte list

Returns NONE if plan generation fails (malformed input).
Data segment (selector tables, deploy code, CBOR metadata) is appended
after the code assembly — it bypasses the plan generator.
-/
def codegen (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  match generateContextPlan ctx fnEomMap with
  | none => none
  | some plan =>
    let codeAsm := executePlan plan
    let dataAsm : List AsmInst := dataSeg.flatMap dataSectionAsm
    some (assemble (codeAsm ++ dataAsm))

/-- Fuel-bounded variant. -/
def codegenFuel (fuel : Nat) (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  match generateContextPlanFuel fuel ctx fnEomMap with
  | none => none
  | some plan =>
    let codeAsm := executePlan plan
    let dataAsm : List AsmInst := dataSeg.flatMap dataSectionAsm
    some (assemble (codeAsm ++ dataAsm))

end EvmYul.Venom.Hol.Codegen

/-
GenBlockSimComp / CfgWalk / param/return prefixes, non-entry block layout & JMP-chain recording

Sub-split of `GenBlockSimComp/CfgWalk` (phase 6, the CFG walk); see `GenBlockSimComp`'s
header for the full roadmap. Continues the `EvmYul.Venom.Hol.Codegen` namespace and imports the previous
part — layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.RegularBody

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ## Param-loading prefix (`prepareParamsPlan`) characterization

Toward non-trivial *entry* bodies (which the var-reading tension otherwise blocks): a function-entry
block's plan is `[SOLabel] ++ prepareParamsPlan ++ … ++ body`. `prepareParamsPlan` is where the entry's
params become the tracked stack `S` that a var-reading body reads from. In the common Vyper case — all
params live, and the optimistic swap already in place — it emits **no** asm ops (the caller has already
put the args on the asm stack), it only records the params on the plan stack (`paramPushState`). That
turns the entry into exactly the `varentry` config (`S = param vars`) the block sims already handle. -/

/-- Push all params onto the plan stack (the plan-side of the calling convention; no asm ops). -/
def paramPushState (params : List Instruction) (ps : PlanState) : PlanState :=
  params.foldl (fun ps' inst => { ps' with stack := stackPush (Operand.Var inst.outputs.head!) ps'.stack }) ps

/-- **`prepareParamsPlan` emits no asm ops when all params are live and the optimistic swap is a
    no-op** — it only pushes the params onto the plan stack (`paramPushState`). `hpop` says no param is
    dead (nothing to pop); `hswap` says the last param is already optimally placed (or the next inst is
    a terminator). At function entry the caller has already placed the args on the asm stack, so there
    is nothing to emit; the plan just records them, yielding the `varentry` config `S = param vars`. -/
theorem prepareParamsPlan_allLive_noSwap
    {liveness : DfState (List String)} {fn : IrFunction} {ps : PlanState}
    {entry : BasicBlock} {restBlocks : List BasicBlock}
    (hblocks : fn.blocks = entry :: restBlocks)
    (hne : (getParams entry.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams entry.instructions) ps).stack.filter
        (fun v => ¬ (liveVarsAt liveness entry.label (getParams entry.instructions).length).contains
          (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams entry.instructions).getLast!
        (liveVarsAt liveness entry.label (getParams entry.instructions).length)
        (match entry.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams entry.instructions) ps)
        = ([], paramPushState (getParams entry.instructions) ps)) :
    prepareParamsPlan liveness fn ps = ([], paramPushState (getParams entry.instructions) ps) := by
  simp only [paramPushState] at hpop hswap
  unfold prepareParamsPlan paramPushState
  rw [hblocks]
  simp only [hne, Bool.false_eq_true, if_false]
  rw [hpop]
  simp only [popmanyPlan, List.isEmpty_nil, if_true, List.nil_append]
  exact hswap

/-- **Param-entry block-plan decomposition.** For the entry block `bb` with params (all live, swap a
    no-op) and `≠ 1` predecessors, the block plan is `[SOLabel] ++ instOps`, where `instOps` is the
    per-instruction `Option`-fold over `nonParamInsts bb` starting from the param-pushed plan state
    `paramPushState` — the params contribute *no* asm ops (`prepareParamsPlan_allLive_noSwap`), only the
    tracked stack. The param analogue of `generateBlockPlan_decompose` (which assumes no params). -/
theorem generateBlockPlan_paramEntry_decompose
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    {restBlocks : List BasicBlock}
    (hblocks : fn.blocks = bb :: restBlocks)
    (hne : (getParams bb.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams bb.instructions) ps).stack.filter
        (fun v => ¬ (liveVarsAt liveness bb.label (getParams bb.instructions).length).contains
          (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams bb.instructions).getLast!
        (liveVarsAt liveness bb.label (getParams bb.instructions).length)
        (match bb.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams bb.instructions) ps)
        = ([], paramPushState (getParams bb.instructions) ps))
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    ∃ instOps,
      ((nonParamInsts bb).zipIdx.foldl
        (fun (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat) =>
          match acc with
          | none => none
          | some (ops, psc) =>
            let (inst, i) := instI
            let nextLive :=
              if i + 1 < (nonParamInsts bb).length then
                liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
              else liveVarsAt liveness bb.label bb.instructions.length
            let nextIsTerm :=
              if i + 1 < (nonParamInsts bb).length then
                isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
            match generateInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb) nextIsTerm
                    bb.label psc with
            | none => none
            | some (stepOps, psn) => some (ops ++ stepOps, psn))
        (some ([], paramPushState (getParams bb.instructions) ps))) = some (instOps, ps') ∧
      blockOps = StackOp.SOLabel bb.label :: instOps := by
  have hprep : prepareParamsPlan liveness fn ps = ([], paramPushState (getParams bb.instructions) ps) :=
    prepareParamsPlan_allLive_noSwap hblocks hne hpop hswap
  unfold generateBlockPlan at hplan
  rw [hprep] at hplan
  rw [hblocks] at hplan
  simp only [List.head?_cons, Option.map_some, beq_self_eq_true, if_true] at hplan
  rw [if_neg hnotsingle] at hplan
  dsimp only at hplan
  split at hplan
  · simp at hplan
  · rename_i instOps ps3 hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hplan
    obtain ⟨hblk, hps⟩ := hplan
    subst hps
    refine ⟨instOps, hf, ?_⟩
    rw [← hblk]; simp

/-- **Param-entry block plan, de-`Option`'d** (`≠1` preds, all params live, swap no-op). The param
    analogue of `genBlockPlan_regular`: `blockOps = SOLabel :: (plain fold over nonParamInsts from
    paramPushState)`. This is the form the body sims consume — the body fold starts from the
    param-pushed stack, i.e. the `varentry` config `S = param vars`. -/
theorem genBlockPlan_paramEntry_regular
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    {restBlocks : List BasicBlock}
    (hblocks : fn.blocks = bb :: restBlocks)
    (hne : (getParams bb.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams bb.instructions) ps).stack.filter
        (fun v => ¬ (liveVarsAt liveness bb.label (getParams bb.instructions).length).contains
          (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams bb.instructions).getLast!
        (liveVarsAt liveness bb.label (getParams bb.instructions).length)
        (match bb.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams bb.instructions) ps)
        = ([], paramPushState (getParams bb.instructions) ps))
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ inst ∈ nonParamInsts bb, ¬ isPreCodegenOpcode inst.opcode ∧
      inst.opcode ≠ Opcode.PHI ∧ inst.opcode ≠ Opcode.OFFSET ∧
      inst.opcode ≠ Opcode.PARAM ∧ inst.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = StackOp.SOLabel bb.label :: ((nonParamInsts bb).zipIdx.foldl
        (fun (acc : List StackOp × PlanState) (instI : Instruction × Nat) =>
          let (inst, i) := instI
          let nextLive :=
            if i + 1 < (nonParamInsts bb).length then
              liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
            else liveVarsAt liveness bb.label bb.instructions.length
          let nextIsTerm :=
            if i + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
          (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).1,
           (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).2))
        ([], paramPushState (getParams bb.instructions) ps)).1 := by
  obtain ⟨instOps, hf, hblk⟩ := generateBlockPlan_paramEntry_decompose liveness dfg cfg fn bb ps
    blockOps ps' hblocks hne hpop hswap hnotsingle hplan
  have hio : instOps = _ := congrArg Prod.fst
    (genInstOps_eq_plain bb (paramPushState (getParams bb.instructions) ps) instOps ps' hreg hf)
  rw [hblk, hio]

/-- **Param-entry single-body split.** For an entry with params and body
    `nonParamInsts bb = [inst, term]` (one non-terminator then a terminator), the block plan is
    `[SOLabel] ++ instStep ++ termOps`, where `instStep` runs `inst` from the param-pushed stack with
    the post-param liveness index `nParams + 1`. Param analogue of `genBlockPlan_singleBody_split`;
    isolates the terminator so its `AsmOp` position (`hget`) and the body fold can be discharged
    separately. -/
theorem genBlockPlan_paramEntry_singleBody_split
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    {inst term : Instruction} {restBlocks : List BasicBlock}
    (hnpi : nonParamInsts bb = [inst, term])
    (histerm : isTerminator term.opcode = true)
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1)).contains out = true)
    (hblocks : fn.blocks = bb :: restBlocks)
    (hne : (getParams bb.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams bb.instructions) ps).stack.filter
        (fun v => ¬ (liveVarsAt liveness bb.label (getParams bb.instructions).length).contains
          (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams bb.instructions).getLast!
        (liveVarsAt liveness bb.label (getParams bb.instructions).length)
        (match bb.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams bb.instructions) ps)
        = ([], paramPushState (getParams bb.instructions) ps))
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts bb, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    ∃ termOps, blockOps = [StackOp.SOLabel bb.label]
      ++ (generateRegularInstPlan liveness dfg cfg fn inst
          (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1)) false true bb.label
          (paramPushState (getParams bb.instructions) ps)).1
      ++ termOps := by
  have hbop := genBlockPlan_paramEntry_regular liveness dfg cfg fn bb ps blockOps ps'
    hblocks hne hpop hswap hnotsingle hreg hplan
  rw [hbop, hnpi]
  simp only [List.length_cons, List.length_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.getElem!_cons_succ, List.getElem!_cons_zero,
    histerm, Nat.zero_add]
  rw [generateRegularInstPlan_isHalting_irrel liveness dfg cfg fn inst
    (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1))
    true bb.label (paramPushState (getParams bb.instructions) ps) (bbIsHalting bb) hlive]
  exact ⟨_, rfl⟩

/-- Folding param-pushes over any plan state appends the param vars to its stack (`stackPush` appends,
    TOS last). -/
theorem paramPushState_stack (params : List Instruction) (ps : PlanState) :
    paramPushState params ps
      = { ps with stack := ps.stack ++ params.map (fun inst => Operand.Var inst.outputs.head!) } := by
  unfold paramPushState
  induction params generalizing ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.foldl_cons, ih]
    cases ps with
    | mk stk sp al lc => simp [stackPush, List.append_assoc]

/-- **`paramPushState` from the initial plan state is exactly the `varentry` config** —
    `{ initPlanState fnEom with stack := S.map Var }` with `S` the param output vars. This is the bridge
    that lets the param-entry block plan (whose body fold starts from `paramPushState`) feed the
    already-built `varentry` block sims (whose `ps0` is `{ initPlanState fnEom with stack := S.map Var }`)
    — for the entry function `lblCtr = 0`, so the two plan states coincide. -/
theorem paramPushState_initPlanState {fnEom : Nat} (params : List Instruction) :
    paramPushState params (initPlanState fnEom)
      = { initPlanState fnEom with
          stack := (params.map (fun inst => inst.outputs.head!)).map Operand.Var } := by
  rw [paramPushState_stack]
  simp only [initPlanState, List.nil_append, List.map_map]
  rfl

/-- **`hblock` discharged from `generateFnPlan` for a param-entry single-body block.** Param analogue of
    `hblock_singleBody_entry_discharged`: the resolved program has the block plan `[SOLabel] ++ instStep`
    at pc 0, where `instStep` runs the body `inst` from the param-pushed stack. Composes
    `generateFnPlan_entry_isPrefix` + `genBlockPlan_paramEntry_singleBody_split` +
    `asmBlockAt_of_planLabelFree`. -/
theorem hblock_paramEntry_singleBody_discharged
    {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock} {inst term : Instruction}
    {ops : List StackOp} {ps : PlanState} {restBlocks : List BasicBlock}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hblocks : fn.blocks = entry :: restBlocks)
    (hnpi : nonParamInsts entry = [inst, term])
    (histerm : isTerminator term.opcode = true)
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
        ((getParams entry.instructions).length + 1)).contains out = true)
    (hne : (getParams entry.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams entry.instructions)
          { initPlanState fnEom with labelCounter := lblCtr }).stack.filter
        (fun v => ¬ (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
          (getParams entry.instructions).length).contains (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams entry.instructions).getLast!
        (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label (getParams entry.instructions).length)
        (match entry.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams entry.instructions) { initPlanState fnEom with labelCounter := lblCtr })
        = ([], paramPushState (getParams entry.instructions) { initPlanState fnEom with labelCounter := lblCtr }))
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hfree : ops.all stackOpLabelFree = true) :
    asmBlockAt (asmResolve (executePlan ops)).1 0
      (executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
              ((getParams entry.instructions).length + 1)) false true entry.label
            (paramPushState (getParams entry.instructions)
              { initPlanState fnEom with labelCounter := lblCtr })).1)) := by
  have hheadeq : fn.blocks.head? = some entry := by rw [hblocks]; rfl
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  obtain ⟨termOps, hsplit⟩ := genBlockPlan_paramEntry_singleBody_split hnpi histerm hlive hblocks
    hne hpop hswap hnotsingle hreg hbp
  have hopsEq : ops = ([StackOp.SOLabel entry.label]
      ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
          (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
          (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
            ((getParams entry.instructions).length + 1)) false true entry.label
          (paramPushState (getParams entry.instructions)
            { initPlanState fnEom with labelCounter := lblCtr })).1) ++ (termOps ++ rest) := by
    rw [hops, hsplit]; simp [List.append_assoc]
  refine asmBlockAt_of_planLabelFree [] _ (termOps ++ rest) ?_ ?_
  · simp only [List.nil_append]; rw [hopsEq]
  · simp only [List.nil_append]; rw [← hopsEq]; exact hfree

/-- Param-entry single-body split, STOP terminator, `termOps` pinned to `[SOEmit "STOP"]` (via
    `generateRegularInstPlan_emit_noIO`). The param analogue of `genBlockPlan_singleBody_split_stop`;
    pins the STOP `AsmOp` position for `hget_paramEntry_stop_discharged`. -/
theorem genBlockPlan_paramEntry_singleBody_split_stop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    {inst term : Instruction} {restBlocks : List BasicBlock}
    (hnpi : nonParamInsts bb = [inst, term])
    (histerm : isTerminator term.opcode = true)
    (hterm_stop : term.opcode = Opcode.STOP)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1)).contains out = true)
    (hblocks : fn.blocks = bb :: restBlocks)
    (hne : (getParams bb.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams bb.instructions) ps).stack.filter
        (fun v => ¬ (liveVarsAt liveness bb.label (getParams bb.instructions).length).contains
          (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams bb.instructions).getLast!
        (liveVarsAt liveness bb.label (getParams bb.instructions).length)
        (match bb.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams bb.instructions) ps)
        = ([], paramPushState (getParams bb.instructions) ps))
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts bb, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = [StackOp.SOLabel bb.label]
      ++ (generateRegularInstPlan liveness dfg cfg fn inst
          (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1)) false true bb.label
          (paramPushState (getParams bb.instructions) ps)).1
      ++ [StackOp.SOEmit "STOP"] := by
  have hbop := genBlockPlan_paramEntry_regular liveness dfg cfg fn bb ps blockOps ps'
    hblocks hne hpop hswap hnotsingle hreg hplan
  have htname : opcodeToEvmName term.opcode = some "STOP" := by rw [hterm_stop]; rfl
  rw [hbop, hnpi]
  simp only [List.length_cons, List.length_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.getElem!_cons_succ, List.getElem!_cons_zero,
    histerm, Nat.zero_add]
  norm_num
  rw [generateRegularInstPlan_isHalting_irrel liveness dfg cfg fn inst
    (liveVarsAt liveness bb.label ((getParams bb.instructions).length + 1))
    true bb.label (paramPushState (getParams bb.instructions) ps) (bbIsHalting bb) hlive]
  rw [generateRegularInstPlan_emit_noIO (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    hterm_ops hterm_outs htname]


/-- **`hget` (STOP `AsmOp` position) discharged from `generateFnPlan` for a param-entry single-body
    block.** Param analogue of `hget_singleBody_stop_entry_discharged`: `AsmOp "STOP"` sits at
    `pc = bodyLen` (length of the executed label + body). -/
theorem hget_paramEntry_stop_discharged
    {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock} {inst term : Instruction}
    {ops : List StackOp} {ps : PlanState} {restBlocks : List BasicBlock}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hblocks : fn.blocks = entry :: restBlocks)
    (hnpi : nonParamInsts entry = [inst, term])
    (histerm : isTerminator term.opcode = true)
    (hterm_stop : term.opcode = Opcode.STOP)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
        ((getParams entry.instructions).length + 1)).contains out = true)
    (hne : (getParams entry.instructions).isEmpty = false)
    (hpop : ((paramPushState (getParams entry.instructions)
          { initPlanState fnEom with labelCounter := lblCtr }).stack.filter
        (fun v => ¬ (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
          (getParams entry.instructions).length).contains (operandToString v))).filter isVarOperand = [])
    (hswap : optimisticSwapPlan DfgAnalysis.empty (getParams entry.instructions).getLast!
        (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label (getParams entry.instructions).length)
        (match entry.instructions.find? (fun inst => inst.opcode != Opcode.PARAM) with
         | some inst => isTerminator inst.opcode | none => false)
        (paramPushState (getParams entry.instructions) { initPlanState fnEom with labelCounter := lblCtr })
        = ([], paramPushState (getParams entry.instructions) { initPlanState fnEom with labelCounter := lblCtr }))
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP) :
    ∃ hlt : (executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
              ((getParams entry.instructions).length + 1)) false true entry.label
            (paramPushState (getParams entry.instructions)
              { initPlanState fnEom with labelCounter := lblCtr })).1)).length
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨(executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
              ((getParams entry.instructions).length + 1)) false true entry.label
            (paramPushState (getParams entry.instructions)
              { initPlanState fnEom with labelCounter := lblCtr })).1)).length, hlt⟩
        = AsmInst.AsmOp "STOP" := by
  have hheadeq : fn.blocks.head? = some entry := by rw [hblocks]; rfl
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  have hsplit := genBlockPlan_paramEntry_singleBody_split_stop hnpi histerm hterm_stop hterm_ops
    hterm_outs hlive hblocks hne hpop hswap hnotsingle hreg hbp
  have hopsEq : ops = (([StackOp.SOLabel entry.label]
      ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
          (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
          (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label
            ((getParams entry.instructions).length + 1)) false true entry.label
          (paramPushState (getParams entry.instructions)
            { initPlanState fnEom with labelCounter := lblCtr })).1) ++ [StackOp.SOEmit "STOP"]) ++ rest := by
    rw [hops, hsplit]
  exact hget_stop_segment hopsEq

/-! ## Venom-side param prefix (counterpart to the codegen `paramPushState`)

The codegen side records the entry params on the plan stack (`paramPushState`, no asm ops). The Venom
side must *process* the leading `PARAM` instructions: each loads `params[idx]` into `vars[out]`, so that
the body then reads those vars. This is the atom of that processing — the full Venom-side prefix
(threading these through `runBlock`/`execBlock` with the `instIdx` offset the params introduce) is what
a whole param-entry *function* capstone additionally needs, on top of the (complete) codegen layer. -/

/-- **Single `PARAM` step (Venom side).** A well-formed PARAM instruction (`operands = [Lit idx]`,
    `outputs = [out]`, index in range) loads `params[idx]` into `vars[out]` — the Venom counterpart to
    the codegen `paramPushState` (which records the same var on the plan stack). -/
theorem stepInstBase_param {inst : Instruction} {vs : VenomState} {idx : UInt256} {out : String}
    (hopc : inst.opcode = Opcode.PARAM)
    (hops : inst.operands = [Operand.Lit idx]) (houts : inst.outputs = [out])
    (hidx : idx.toNat < vs.params.length) :
    stepInstBase inst vs = ExecResult.OK (updateVar out (vs.params.get ⟨idx.toNat, hidx⟩) vs) := by
  unfold stepInstBase
  rw [hopc, hops, houts]
  simp only [hidx, dif_pos]

/-! ### instIdx-obliviousness toolkit

`stepInstBase` never reads `instIdx` (the only `instIdx` write in the Venom semantics is `jumpTo`,
used solely by terminators). The atomic `*_setInstIdx` lemmas capture this: setting the input
`instIdx` commutes with each state helper (`updateVar`, `mstore`, `sstore`, …) and is invisible to
each reader (`evalOperand`, `mload`, `sload`, …). The capstone `execBodyThread_instIdx_congr` lifts
this to the whole body thread: threading a body from two configs that agree except on `instIdx`
yields results agreeing except on `instIdx`. That is exactly the bridge the param route needs — the
body threaded from the **param-loaded state** (at `instIdx = nParams`, via `execBodyThread_append`)
matches the asm-side body thread (which `genBlockPrefixBodyG_sim_inv` hardcodes at `instIdx = 0`) on
every observable field. -/

/-- `evalOperand` ignores `instIdx` (reads only `vars` / `labels`). -/
theorem evalOperand_setInstIdx (op : Operand) (s : VenomState) (i : Nat) :
    evalOperand op { s with instIdx := i } = evalOperand op s := by
  cases op <;> rfl

/-- `updateVar` commutes with setting `instIdx` (writes only `vars`). -/
theorem updateVar_setInstIdx (x : String) (v : bytes32) (s : VenomState) (i : Nat) :
    updateVar x v { s with instIdx := i } = { updateVar x v s with instIdx := i } := rfl

theorem mstore_setInstIdx (o : Nat) (v : bytes32) (s : VenomState) (i : Nat) :
    mstore o v { s with instIdx := i } = { mstore o v s with instIdx := i } := rfl

theorem mstore8_setInstIdx (o : Nat) (v : bytes32) (s : VenomState) (i : Nat) :
    mstore8 o v { s with instIdx := i } = { mstore8 o v s with instIdx := i } := rfl

theorem sstore_setInstIdx (k v : bytes32) (s : VenomState) (i : Nat) :
    sstore k v { s with instIdx := i } = { sstore k v s with instIdx := i } := rfl

theorem tstore_setInstIdx (k v : bytes32) (s : VenomState) (i : Nat) :
    tstore k v { s with instIdx := i } = { tstore k v s with instIdx := i } := rfl

theorem mload_setInstIdx (o : Nat) (s : VenomState) (i : Nat) :
    mload o { s with instIdx := i } = mload o s := rfl

theorem sload_setInstIdx (k : bytes32) (s : VenomState) (i : Nat) :
    sload k { s with instIdx := i } = sload k s := rfl

theorem tload_setInstIdx (k : bytes32) (s : VenomState) (i : Nat) :
    tload k { s with instIdx := i } = tload k s := rfl

theorem mcopy_setInstIdx (d src sz : Nat) (s : VenomState) (i : Nat) :
    mcopy d src sz { s with instIdx := i } = { mcopy d src sz s with instIdx := i } := rfl

/-- **Per-step instIdx-obliviousness for pure-binop opcodes** (`ADD`/`SUB`/…/`SHL`/`BYTE`). A sample
    `hobliv` discharger for `execBodyThread_instIdx_congr`: setting the input `instIdx` only sets the
    output's `instIdx`. Threads the `evalOperand` / `updateVar` atomics through the `execPure2` match. -/
theorem execPure2_setInstIdx {f : bytes32 → bytes32 → bytes32} {inst : Instruction}
    {s s' : VenomState} {i : Nat} (h : execPure2 f inst s = ExecResult.OK s') :
    execPure2 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execPure2 at h ⊢
  simp only [evalOperand_setInstIdx, updateVar_setInstIdx]
  split at h <;> first | (split at h <;> simp_all) | simp_all

/-- **`execBodyThread` is instIdx-oblivious on non-`instIdx` fields** (given per-step obliviousness).
    Threading the same body from two configs agreeing except on `instIdx` yields results agreeing
    except on `instIdx` — the bridge that lets the param-entry body thread (from the param-loaded state
    at `instIdx = nParams`) match the asm-side body thread (from `instIdx = 0`). The per-step
    hypothesis `hobliv` is dischargeable per body (e.g. `execPure2_setInstIdx` for pure-binop insts). -/
theorem execBodyThread_instIdx_congr (body : List Instruction)
    (hobliv : ∀ inst ∈ body, ∀ (t t' : VenomState) (j : Nat),
       stepInstBase inst t = ExecResult.OK t' →
       stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j }) :
    ∀ (start start' : Nat) (s s' sEnd sEnd' : VenomState),
    { s with instIdx := 0 } = { s' with instIdx := 0 } →
    execBodyThread body start s = some sEnd →
    execBodyThread body start' s' = some sEnd' →
    { sEnd with instIdx := 0 } = { sEnd' with instIdx := 0 } := by
  induction body with
  | nil =>
    intro start start' s s' sEnd sEnd' hss hthr hthr'
    simp only [execBodyThread] at hthr hthr'
    obtain rfl := Option.some.inj hthr
    obtain rfl := Option.some.inj hthr'
    exact hss
  | cons inst rest ih =>
    intro start start' s s' sEnd sEnd' hss hthr hthr'
    have hs' : { s with instIdx := s'.instIdx } = s' :=
      congrArg (fun t => { t with instIdx := s'.instIdx }) hss
    simp only [execBodyThread] at hthr hthr'
    cases hstep : stepInstBase inst s with
    | OK s1 =>
      rw [hstep] at hthr
      have hstep' : stepInstBase inst s' = ExecResult.OK { s1 with instIdx := s'.instIdx } := by
        rw [← hs']
        exact hobliv inst (List.mem_cons.2 (Or.inl rfl)) s s1 s'.instIdx hstep
      rw [hstep'] at hthr'
      refine ih (fun i hi => hobliv i (List.mem_cons.2 (Or.inr hi)))
        (start + 1) (start' + 1)
        { s1 with instIdx := start + 1 }
        { { s1 with instIdx := s'.instIdx } with instIdx := start' + 1 }
        sEnd sEnd' ?_ hthr hthr'
      simp
    | IntRet _ _ => rw [hstep] at hthr; simp at hthr
    | Halt _ => rw [hstep] at hthr; simp at hthr
    | Abort _ _ => rw [hstep] at hthr; simp at hthr
    | Error _ => rw [hstep] at hthr; simp at hthr

/-- **instIdx-oblivious existence transfer.** If a body threads successfully from one config, it
    threads successfully from any config agreeing except on `instIdx`, to a result agreeing except on
    `instIdx`. Strengthens `execBodyThread_instIdx_congr` (which assumes *both* threads succeed) to
    *derive* the second thread — exactly what the param-route assembly needs: the front thread
    (`params ++ body` from `vs`, reached via `execBodyThread_append`) exists and matches the asm-side
    body thread (`body` from the param-loaded state at `instIdx = 0`) on every observable field. -/
theorem execBodyThread_instIdx_exists (body : List Instruction)
    (hobliv : ∀ inst ∈ body, ∀ (t t' : VenomState) (j : Nat),
       stepInstBase inst t = ExecResult.OK t' →
       stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j }) :
    ∀ (start start' : Nat) (s s' sEnd : VenomState),
    { s with instIdx := 0 } = { s' with instIdx := 0 } →
    execBodyThread body start s = some sEnd →
    ∃ sEnd', execBodyThread body start' s' = some sEnd' ∧
             { sEnd with instIdx := 0 } = { sEnd' with instIdx := 0 } := by
  induction body with
  | nil =>
    intro start start' s s' sEnd hss hthr
    simp only [execBodyThread] at hthr ⊢
    obtain rfl := Option.some.inj hthr
    exact ⟨s', rfl, hss⟩
  | cons inst rest ih =>
    intro start start' s s' sEnd hss hthr
    have hs' : { s with instIdx := s'.instIdx } = s' :=
      congrArg (fun t => { t with instIdx := s'.instIdx }) hss
    simp only [execBodyThread] at hthr ⊢
    cases hstep : stepInstBase inst s with
    | OK s1 =>
      rw [hstep] at hthr
      have hstep' : stepInstBase inst s' = ExecResult.OK { s1 with instIdx := s'.instIdx } := by
        rw [← hs']
        exact hobliv inst (List.mem_cons.2 (Or.inl rfl)) s s1 s'.instIdx hstep
      rw [hstep']
      exact ih (fun i hi => hobliv i (List.mem_cons.2 (Or.inr hi)))
        (start + 1) (start' + 1)
        { s1 with instIdx := start + 1 }
        { { s1 with instIdx := s'.instIdx } with instIdx := start' + 1 }
        sEnd (by simp) hthr
    | IntRet _ _ => rw [hstep] at hthr; simp at hthr
    | Halt _ => rw [hstep] at hthr; simp at hthr
    | Abort _ _ => rw [hstep] at hthr; simp at hthr
    | Error _ => rw [hstep] at hthr; simp at hthr

/-- `venomAsmTerminalRel` reads only `accounts`/`transient`/`returndata`/`logs`, so it transfers
    across states agreeing except on `instIdx` (i.e. `{· with instIdx := 0}`-equal) — the terminal
    side of instIdx-obliviousness. -/
theorem venomAsmTerminalRel_of_instIdx_eq {s1 s2 : VenomState} {as : AsmState}
    (heq : { s1 with instIdx := 0 } = { s2 with instIdx := 0 })
    (h : venomAsmTerminalRel s2 as) : venomAsmTerminalRel s1 as := by
  obtain ⟨ha, ht, hr, hl⟩ := h
  refine ⟨ha.trans ?_, ht.trans ?_, hr.trans ?_, hl.trans ?_⟩
  · exact (congrArg (·.accounts) heq).symm
  · exact (congrArg (·.transient) heq).symm
  · exact (congrArg (·.returndata) heq).symm
  · exact (congrArg (·.logs) heq).symm

/-- `haltState` only sets `halted`, invisible to `venomAsmTerminalRel`. -/
theorem venomAsmTerminalRel_haltState {s : VenomState} {as : AsmState}
    (h : venomAsmTerminalRel s as) : venomAsmTerminalRel (haltState s) as := h

/-- The `htermrel` shape the param-route assembly produces: from the asm-side body relation
    `venomAsmTerminalRel sEndBody asFin` and the front/body instIdx-agreement (front thread `sEnd` vs
    body thread `sEndBody`, agreeing except on `instIdx`), conclude `venomAsmTerminalRel (haltState
    sEnd) asFin` — exactly `genBlockSimulation_body_halt`'s `htermrel` for `front = params ++ body`. -/
theorem venomAsmTerminalRel_haltState_of_instIdx_eq {sEnd sEndBody : VenomState} {as : AsmState}
    (heq : { sEnd with instIdx := 0 } = { sEndBody with instIdx := 0 })
    (h : venomAsmTerminalRel sEndBody as) : venomAsmTerminalRel (haltState sEnd) as :=
  venomAsmTerminalRel_haltState (venomAsmTerminalRel_of_instIdx_eq heq h)

/-- **`execBodyThread` splits over `++`.** Threading a concatenated instruction list is threading the
    prefix, then the suffix from the advanced index — provided the prefix succeeds (`some sMid`). The
    Venom-side glue that lets a param-entry block be viewed as `front = params ++ body`: the whole-front
    thread that `genBlockSimulation_body_halt` demands decomposes into the param thread
    (`execBodyThread_two_params`) followed by the body thread. -/
theorem execBodyThread_append (l1 l2 : List Instruction) :
    ∀ (start : Nat) (s sMid : VenomState),
    execBodyThread l1 start s = some sMid →
    execBodyThread (l1 ++ l2) start s = execBodyThread l2 (start + l1.length) sMid := by
  induction l1 with
  | nil =>
    intro start s sMid hthread
    obtain rfl := Option.some.inj hthread
    simp
  | cons inst rest ih =>
    intro start s sMid hthread
    cases hstep : stepInstBase inst s with
    | OK s' =>
      simp only [execBodyThread, hstep] at hthread
      have key := ih (start + 1) _ sMid hthread
      simp only [List.cons_append, execBodyThread, hstep, List.length_cons]
      have hidx : start + 1 + rest.length = start + (rest.length + 1) := by omega
      rw [key, hidx]
    | IntRet _ _ => simp [execBodyThread, hstep] at hthread
    | Halt _ => simp [execBodyThread, hstep] at hthread
    | Abort _ _ => simp [execBodyThread, hstep] at hthread
    | Error _ => simp [execBodyThread, hstep] at hthread

/-- **Two-PARAM Venom loading** — the Venom counterpart to the 2-param `paramPushState`. Threading
    `PARAM 0 → x ; PARAM 1 → y` succeeds and leaves `x, y` bound to `params[0], params[1]` (memory /
    accounts / shared fields untouched). Iterates `stepInstBase_param` — the first step of the
    Venom-side param prefix a whole param-entry function needs (`runBlock` peeling the leading PARAMs
    to populate `vars` before the body reads them). -/
theorem execBodyThread_two_params
    {p0 p1 : Instruction} {s : VenomState} {x y : String}
    (hp0opc : p0.opcode = Opcode.PARAM) (hp0ops : p0.operands = [Operand.Lit (EvmYul.UInt256.ofNat 0)])
    (hp0out : p0.outputs = [x])
    (hp1opc : p1.opcode = Opcode.PARAM) (hp1ops : p1.operands = [Operand.Lit (EvmYul.UInt256.ofNat 1)])
    (hp1out : p1.outputs = [y])
    (h0 : (EvmYul.UInt256.ofNat 0).toNat < s.params.length)
    (h1 : (EvmYul.UInt256.ofNat 1).toNat < s.params.length) :
    ∃ s', execBodyThread [p0, p1] 0 s = some s' ∧
          s'.vars = ainsert (ainsert s.vars x (s.params.get ⟨(EvmYul.UInt256.ofNat 0).toNat, h0⟩))
                      y (s.params.get ⟨(EvmYul.UInt256.ofNat 1).toNat, h1⟩) ∧
          s'.memory = s.memory ∧ s'.accounts = s.accounts ∧ s'.transient = s.transient ∧
          s'.returndata = s.returndata ∧ s'.logs = s.logs := by
  simp only [execBodyThread, stepInstBase_param hp0opc hp0ops hp0out h0]
  rw [stepInstBase_param
    (vs := { updateVar x (s.params.get ⟨(EvmYul.UInt256.ofNat 0).toNat, h0⟩) s with instIdx := 0 + 1 })
    hp1opc hp1ops hp1out h1]
  dsimp only
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [updateVar]

/-- **`runBlock` peels the leading PARAMs of a 2-param entry** — the Venom-side counterpart of
    `generateBlockPlan`'s param prefix. Composes `runBlock_no_phi` (PARAM head is not PHI) with
    `execBlock_body_prefix` (the two PARAMs are non-terminators stepping to OK, via
    `execBodyThread_two_params`): `runBlock (2 + restFuel) ctx bb vs = execBlock restFuel ctx bb s'`,
    where `s'` is the param-loaded state (`x, y` bound to `params[0], params[1]`, `instIdx = 2`). The
    body then runs from `s'` at `instIdx = 2` — the offset the codegen side collapses via
    `paramPushState`, to be bridged next. -/
theorem runBlock_paramEntry_peel
    {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {p0 p1 : Instruction} {rest : List Instruction} {x y : String}
    (hbb : bb.instructions = p0 :: p1 :: rest)
    (hp0opc : p0.opcode = Opcode.PARAM) (hp0ops : p0.operands = [Operand.Lit (EvmYul.UInt256.ofNat 0)])
    (hp0out : p0.outputs = [x])
    (hp1opc : p1.opcode = Opcode.PARAM) (hp1ops : p1.operands = [Operand.Lit (EvmYul.UInt256.ofNat 1)])
    (hp1out : p1.outputs = [y])
    (h0 : (EvmYul.UInt256.ofNat 0).toNat < vs.params.length)
    (h1 : (EvmYul.UInt256.ofNat 1).toNat < vs.params.length) :
    ∃ s', runBlock (2 + restFuel) ctx bb vs = execBlock restFuel ctx bb s' ∧
          s'.vars = ainsert (ainsert vs.vars x (vs.params.get ⟨(EvmYul.UInt256.ofNat 0).toNat, h0⟩))
                      y (vs.params.get ⟨(EvmYul.UInt256.ofNat 1).toNat, h1⟩) ∧
          s'.memory = vs.memory ∧ s'.accounts = vs.accounts := by
  obtain ⟨s', hthread, hvars, hmem, hacc, _, _, _⟩ :=
    execBodyThread_two_params (s := { vs with instIdx := 0 }) hp0opc hp0ops hp0out hp1opc hp1ops hp1out
      (by simpa using h0) (by simpa using h1)
  refine ⟨s', ?_, ?_, hmem, hacc⟩
  · rw [runBlock_no_phi (2 + restFuel) ctx bb vs p0 (p1 :: rest) hbb (by rw [hp0opc]; decide)]
    have hget : ∀ (j : Nat) (hj : j < [p0, p1].length),
        getInstruction bb (0 + j) = some [p0, p1][j] := by
      intro j hj
      have hj' : j < 2 := by simpa using hj
      interval_cases j
      · simp [getInstruction, hbb]
      · simp [getInstruction, hbb]
    have := execBlock_body_prefix ctx bb restFuel [p0, p1] 0 { vs with instIdx := 0 } s'
      rfl hget (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                   rcases hi with h | h <;> subst h
                   · rw [hp0opc]; decide
                   · rw [hp1opc]; decide) hthread
    simpa using this
  · simpa using hvars

/-- **Param-entry STOP-block simulation** — the param-route capstone. A block whose instructions are
    two leading `PARAM`s, then a var-reading regular body, then `STOP`. The asm side is the ordinary
    var-reading body sim over the *param-loaded* state `vs0` (`genBlockPrefixBodyG_sim_inv` — params
    emit no asm ops, being the function's incoming stack), and the Venom side peels the params
    (`hpeel`) so the whole front `[p0,p1] ++ body` threads from the pre-param `vs`
    (`execBodyThread_append`). The instIdx offset between the two thread starts (front at `nParams = 2`,
    asm-side body at `0`) is bridged by the obliviousness toolkit: `execBodyThread_instIdx_exists`
    supplies the front thread's existence + agreement, and `venomAsmTerminalRel_haltState_of_instIdx_eq`
    turns the body relation into `genBlockSimulation_body_halt`'s `htermrel`. The `hobliv` hypothesis
    (per-step instIdx-obliviousness of the body) is dischargeable per body (`execPure2_setInstIdx` &c.).
    This is the first route where a **function-entry** block's incoming params feed a var-reading body
    end to end — the counterpart of `genBlockSimulation_regularGN_stop_varentry` (which assumes the
    vars pre-defined) for a genuine entry that *loads* them. -/
theorem genBlockSimulation_regularGN_stop_paramentry
    {ctx : VenomContext} {bb : BasicBlock} {vs vs0 : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term : Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEndBody : VenomState}
    {p0 p1 : Instruction} {x y : String}
    (hp0opc : p0.opcode = Opcode.PARAM) (hp0ops : p0.operands = [Operand.Lit (EvmYul.UInt256.ofNat 0)])
    (hp0out : p0.outputs = [x])
    (hp1opc : p1.opcode = Opcode.PARAM) (hp1ops : p1.operands = [Operand.Lit (EvmYul.UInt256.ofNat 1)])
    (hp1out : p1.outputs = [y])
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hbb : bb.instructions = [p0, p1] ++ body ++ [term])
    (htermSTOP : term.opcode = Opcode.STOP)
    (hnontermBody : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (hpeel : execBodyThread [p0, p1] 0 { vs with instIdx := 0 } = some vs0)
    (hobliv : ∀ inst ∈ body, ∀ (t t' : VenomState) (j : Nat),
       stepInstBase inst t = ExecResult.OK t' →
       stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j })
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 vs0)
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 vs0 asm)
    (hthreadBody : execBodyThread body 0 vs0 = some sEndBody)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 vs0 sEndBody asm hready hsd0 hsv0 hrel0 hthreadBody hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨sEnd, hthreadBody2, heq⟩ :=
    execBodyThread_instIdx_exists body hobliv 0 2 vs0 vs0 sEndBody rfl hthreadBody
  have hthreadFront : execBodyThread ([p0, p1] ++ body) 0 { vs with instIdx := 0 } = some sEnd := by
    rw [execBodyThread_append [p0, p1] body 0 { vs with instIdx := 0 } vs0 hpeel]
    simpa using hthreadBody2
  have hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd) := by
    unfold stepInstBase; rw [htermSTOP]
  have histerm : isTerminator term.opcode = true := by rw [htermSTOP]; decide
  have hphi : p0.opcode ≠ Opcode.PHI := by rw [hp0opc]; decide
  have hnonterm : ∀ inst ∈ [p0, p1] ++ body, isTerminator inst.opcode = false := by
    intro inst hi
    rw [List.mem_append] at hi
    rcases hi with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · rw [hp0opc]; decide
      · rw [hp1opc]; decide
    · exact hnontermBody inst h
  refine genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    ([p0, p1] ++ body) term p0 (p1 :: (body ++ [term])) sEnd (haltState sEnd) asMid (asmNext asMid)
    bodyLen hbb (by simp) hphi hnonterm hthreadFront histerm hstepterm hbrun
    (htermrun_of_stop asm bodyLen hlt hget asMid hbpc) (by omega) ?_
  exact venomAsmTerminalRel_haltState_of_instIdx_eq heq.symm
    (venomAsmRel_terminal labelOffsets _ sEndBody asMid hbrel)

/-- **Param-entry STOP-block simulation over the demand-threaded H-fold body** — the H-fold twin of
    `genBlockSimulation_regularGN_stop_paramentry`. A function-entry block whose instructions are two
    leading `PARAM`s, then a var-reading body that **may contain memory copies / LOG** (a
    `RegularBodyH … dem`), then `STOP`. Same structure as the G-fold param capstone: the asm side is the
    var-reading body sim over the *param-loaded* state `vs0` (`genBlockPrefixBodyH_sim_inv` — params emit
    no asm ops), the Venom side peels the params (`hpeel`) so the whole front `[p0,p1] ++ body` threads
    from the pre-param `vs` (`execBodyThread_append`), and the front/body `instIdx` offset is bridged by
    the obliviousness toolkit. Lets a **function-entry** block's incoming params feed an H-fold
    copy/LOG body end to end (headroom now `Σ dem`). -/
theorem genBlockSimulation_regularHN_stop_paramentry
    {ctx : VenomContext} {bb : BasicBlock} {vs vs0 : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel dem : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term : Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEndBody : VenomState}
    {p0 p1 : Instruction} {x y : String}
    (hp0opc : p0.opcode = Opcode.PARAM) (hp0ops : p0.operands = [Operand.Lit (EvmYul.UInt256.ofNat 0)])
    (hp0out : p0.outputs = [x])
    (hp1opc : p1.opcode = Opcode.PARAM) (hp1ops : p1.operands = [Operand.Lit (EvmYul.UInt256.ofNat 1)])
    (hp1out : p1.outputs = [y])
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = [p0, p1] ++ body ++ [term])
    (htermSTOP : term.opcode = Opcode.STOP)
    (hnontermBody : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (hpeel : execBodyThread [p0, p1] 0 { vs with instIdx := 0 } = some vs0)
    (hobliv : ∀ inst ∈ body, ∀ (t t' : VenomState) (j : Nat),
       stepInstBase inst t = ExecResult.OK t' →
       stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j })
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 vs0)
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 vs0 asm)
    (hthreadBody : execBodyThread body 0 vs0 = some sEndBody)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 vs0 sEndBody asm hready hsd0 hsv0 hrel0 hthreadBody hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨sEnd, hthreadBody2, heq⟩ :=
    execBodyThread_instIdx_exists body hobliv 0 2 vs0 vs0 sEndBody rfl hthreadBody
  have hthreadFront : execBodyThread ([p0, p1] ++ body) 0 { vs with instIdx := 0 } = some sEnd := by
    rw [execBodyThread_append [p0, p1] body 0 { vs with instIdx := 0 } vs0 hpeel]
    simpa using hthreadBody2
  have hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd) := by
    unfold stepInstBase; rw [htermSTOP]
  have histerm : isTerminator term.opcode = true := by rw [htermSTOP]; decide
  have hphi : p0.opcode ≠ Opcode.PHI := by rw [hp0opc]; decide
  have hnonterm : ∀ inst ∈ [p0, p1] ++ body, isTerminator inst.opcode = false := by
    intro inst hi
    rw [List.mem_append] at hi
    rcases hi with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · rw [hp0opc]; decide
      · rw [hp1opc]; decide
    · exact hnontermBody inst h
  refine genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    ([p0, p1] ++ body) term p0 (p1 :: (body ++ [term])) sEnd (haltState sEnd) asMid (asmNext asMid)
    bodyLen hbb (by simp) hphi hnonterm hthreadFront histerm hstepterm hbrun
    (htermrun_of_stop asm bodyLen hlt hget asMid hbpc) (by omega) ?_
  exact venomAsmTerminalRel_haltState_of_instIdx_eq heq.symm
    (venomAsmRel_terminal labelOffsets _ sEndBody asMid hbrel)

/-! ## Non-entry block layout: `hblock` from the two-block split

The entry-only `hblock` discharge (`hblock_singleBody_entry_discharged`) locates a block at pc 0. For a
**non-entry** block reached via JMP (the second route around the var-reading tension — the predecessor
leaves live vars on the stack), the block sits at a *non-zero* pc. `generateFnPlan_twoBlock_split` gives
`ops = entryOps ++ nextOps`, so the (label-free) `next` block's plan is a segment of the resolved program
at `pc = (executePlan entryOps).length` — via `asmBlockAt_resolved_of_middle_no_label` (resolution is the
identity on a label-push-free segment, so no offset shift). This is the non-entry counterpart of the
entry `hblock` discharge, feeding the `varentry` block sims at their actual pc. -/

/-- **`hblock` for the non-entry `next` block of a 2-block function.** Given the two-block split
    `ops = entryOps ++ nextOps` and that `next`'s plan is label-push-free (a STOP/INVALID-terminated
    block with no internal JMP), `next`'s plan is an `asmBlockAt` in the resolved program at
    `pc = (executePlan entryOps).length`. -/
theorem hblock_twoBlock_next_discharged
    {ops entryOps nextOps : List StackOp}
    (hopsEq : ops = entryOps ++ nextOps)
    (hfree : ∀ a ∈ executePlan nextOps, (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl) ∧
       (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)) :
    asmBlockAt (asmResolve (executePlan ops)).1 (executePlan entryOps).length (executePlan nextOps) := by
  have hep : executePlan ops = executePlan entryOps ++ executePlan nextOps ++ [] := by
    rw [hopsEq, executePlan_append, List.append_nil]
  rw [hep]
  exact asmBlockAt_resolved_of_middle_no_label (executePlan entryOps) (executePlan nextOps) []
    (fun a ha lbl => (hfree a ha).1 lbl) (fun a ha lbl d => (hfree a ha).2 lbl d)


theorem contains_cons_of_contains {l : List String} {a b : String} (h : l.contains b = true) :
    (a :: l).contains b = true := by rw [List.contains_cons, h, Bool.or_true]

/-- Cons-unfolding for `dfsSuccsEntries` (the `let psBranch` reduced). -/
theorem dfsSuccsEntries_cons (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (tbl : AssocList String PlanState) (psG : PlanState) :
    dfsSuccsEntries (fuel + 1) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG =
    (match dfsEntriesAux fuel L D C fn [succ] visited tbl
             { psG with stack := savedStack, spilled := savedSpilled } with
     | none => none
     | some (vAfter, tblAfter, psAfter) =>
       match dfsSuccsEntries fuel L D C fn savedStack savedSpilled rest vAfter tblAfter
               { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
       | none => none
       | some (vF, tblF, psF) => some (vF, tblF, psF)) := rfl

/-- **Visited-set monotonicity of the entry DFS.** Once a label is in `visited`, it stays visited
    through the whole DFS (the DFS only ever adds to `visited`). Needed to keep `lbl` "already visited"
    across the successor recursion in the table-preservation proof. -/
theorem dfsEntries_visited_mono (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (lbl : String),
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some result →
      visited.contains lbl = true → result.1.contains lbl = true)
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (lbl : String),
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG = some result →
      visited.contains lbl = true → result.1.contains lbl = true) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result lbl hsome hvis
      rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact hvis
    · intro ss sp succs visited tbl psG result lbl hsome hvis
      rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact hvis
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result lbl hsome hvis
      cases worklist with
      | nil => rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact hvis
      | cons lbl' rest =>
        by_cases hvis' : visited.contains lbl'
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis'] at hsome
          exact ihA rest visited tbl ps result lbl hsome hvis
        · have hvisf : visited.contains lbl' = false := by simp only [Bool.not_eq_true] at hvis'; exact hvis'
          cases hfind : fn.blocks.find? (·.label == lbl') with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            exact ihA rest (lbl' :: visited) _ ps result lbl hsome (contains_cons_of_contains hvis)
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            split at hsome
            · exact absurd hsome (by simp)
            · next blockOps ps' _ =>
              split at hsome
              · exact absurd hsome (by simp)
              · next visited'' tbl'' ps'' hgs =>
                have hv'' := ihS ps'.stack ps'.spilled (C.succsOf lbl') (lbl' :: visited)
                  (AssocList.insert String PlanState tbl lbl' ps) ps' (visited'', tbl'', ps'') lbl
                  hgs (contains_cons_of_contains hvis)
                exact ihA rest visited'' tbl'' ps'' result lbl hsome hv''
    · intro ss sp succs visited tbl psG result lbl hsome hvis
      cases succs with
      | nil => rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact hvis
      | cons succ rest =>
        rw [dfsSuccsEntries_cons] at hsome
        split at hsome
        · exact absurd hsome (by simp)
        · next vAfter tblAfter psAfter hga =>
          split at hsome
          · exact absurd hsome (by simp)
          · next vF tblF psF hgs =>
            obtain rfl := Option.some.inj hsome
            have hvA := ihA [succ] visited tbl { psG with stack := ss, spilled := sp }
              (vAfter, tblAfter, psAfter) lbl hga hvis
            exact ihS ss sp rest vAfter tblAfter _ (vF, tblF, psF) lbl hgs hvA

/-- **Table-preservation.** Once a label is visited, the DFS never changes its recorded entry plan
    (all later inserts are for other labels). The core of the recording lemma. -/
theorem dfsEntries_table_mono (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (lbl : String),
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some result →
      visited.contains lbl = true →
      AssocList.lookup String PlanState result.2.1 lbl = AssocList.lookup String PlanState tbl lbl)
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (lbl : String),
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG = some result →
      visited.contains lbl = true →
      AssocList.lookup String PlanState result.2.1 lbl = AssocList.lookup String PlanState tbl lbl) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result lbl hsome hvis
      rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; rfl
    · intro ss sp succs visited tbl psG result lbl hsome hvis
      rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; rfl
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result lbl hsome hvis
      cases worklist with
      | nil => rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; rfl
      | cons lbl' rest =>
        by_cases hvis' : visited.contains lbl'
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis'] at hsome
          exact ihA rest visited tbl ps result lbl hsome hvis
        · have hvisf : visited.contains lbl' = false := by
            simp only [Bool.not_eq_true] at hvis'; exact hvis'
          have hne : lbl ≠ lbl' := by intro h; subst h; rw [hvisf] at hvis; simp at hvis
          cases hfind : fn.blocks.find? (·.label == lbl') with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            rw [ihA rest (lbl' :: visited) (AssocList.insert String PlanState tbl lbl' ps) ps result
              lbl hsome (contains_cons_of_contains hvis)]
            exact assocLookup_insert_ne tbl lbl' lbl ps hne
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            split at hsome
            · exact absurd hsome (by simp)
            · next blockOps ps' _ =>
              split at hsome
              · exact absurd hsome (by simp)
              · next visited'' tbl'' ps'' hgs =>
                have hvis'' : visited''.contains lbl = true :=
                  (dfsEntries_visited_mono L D C fn n).2 ps'.stack ps'.spilled (C.succsOf lbl')
                    (lbl' :: visited) (AssocList.insert String PlanState tbl lbl' ps) ps'
                    (visited'', tbl'', ps'') lbl hgs (contains_cons_of_contains hvis)
                rw [ihA rest visited'' tbl'' ps'' result lbl hsome hvis'']
                rw [ihS ps'.stack ps'.spilled (C.succsOf lbl') (lbl' :: visited)
                  (AssocList.insert String PlanState tbl lbl' ps) ps' (visited'', tbl'', ps'') lbl hgs
                  (contains_cons_of_contains hvis)]
                exact assocLookup_insert_ne tbl lbl' lbl ps hne
    · intro ss sp succs visited tbl psG result lbl hsome hvis
      cases succs with
      | nil => rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; rfl
      | cons succ rest =>
        rw [dfsSuccsEntries_cons] at hsome
        split at hsome
        · exact absurd hsome (by simp)
        · next vAfter tblAfter psAfter hga =>
          split at hsome
          · exact absurd hsome (by simp)
          · next vF tblF psF hgs =>
            obtain rfl := Option.some.inj hsome
            have hvA : vAfter.contains lbl = true :=
              (dfsEntries_visited_mono L D C fn n).1 [succ] visited tbl
                { psG with stack := ss, spilled := sp } (vAfter, tblAfter, psAfter) lbl hga hvis
            rw [ihS ss sp rest vAfter tblAfter
              { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
              (vF, tblF, psF) lbl hgs hvA]
            exact ihA [succ] visited tbl { psG with stack := ss, spilled := sp }
              (vAfter, tblAfter, psAfter) lbl hga hvis

/-- **First-visit recording.** When `lbl` (unvisited, a real block `bb`) is the head of the worklist,
    the DFS records its entry plan `ps`: the final table maps `lbl ↦ ps`. The visit inserts `lbl ↦ ps`,
    and table-preservation (`dfsEntries_table_mono`) keeps it through the successor + rest recursion
    (`lbl` is now visited); `dfsEntries_visited_mono` supplies the "still visited" side-condition. -/
theorem dfsEntriesAux_head_records (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (bb : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hsome : dfsEntriesAux (fuel + 1) L D C fn (lbl :: rest) visited tbl ps = some result) :
    AssocList.lookup String PlanState result.2.1 lbl = some ps := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next blockOps ps' _ =>
    split at hsome
    · exact absurd hsome (by simp)
    · next visited'' tbl'' ps'' hgs =>
      have hlblvis : (lbl :: visited).contains lbl = true := by simp
      have hvis'' : visited''.contains lbl = true :=
        (dfsEntries_visited_mono L D C fn fuel).2 ps'.stack ps'.spilled (C.succsOf lbl)
          (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps'
          (visited'', tbl'', ps'') lbl hgs hlblvis
      rw [(dfsEntries_table_mono L D C fn fuel).1 rest visited'' tbl'' ps'' result lbl hsome hvis'']
      rw [(dfsEntries_table_mono L D C fn fuel).2 ps'.stack ps'.spilled (C.succsOf lbl)
        (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps' (visited'', tbl'', ps'') lbl
        hgs hlblvis]
      exact assocLookup_insert_self tbl lbl ps


/-- **First-visit adds the head to visited.** When an unvisited real block `lbl` heads the worklist,
    it ends up in the output visited set (the visit adds it, later recursion preserves it). -/
theorem dfsEntriesAux_head_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (bb : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hsome : dfsEntriesAux (fuel + 1) L D C fn (lbl :: rest) visited tbl ps = some result) :
    result.1.contains lbl = true := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next blockOps ps' _ =>
    split at hsome
    · exact absurd hsome (by simp)
    · next visited'' tbl'' ps'' hgs =>
      have hlblvis : (lbl :: visited).contains lbl = true := by simp
      have hvis'' : visited''.contains lbl = true :=
        (dfsEntries_visited_mono L D C fn fuel).2 ps'.stack ps'.spilled (C.succsOf lbl)
          (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps'
          (visited'', tbl'', ps'') lbl hgs hlblvis
      exact (dfsEntries_visited_mono L D C fn fuel).1 rest visited'' tbl'' ps'' result lbl hsome hvis''

/-- **A first-unvisited successor records its branch entry plan.** `dfsSuccsEntries` visits the first
    successor `succ` (if unvisited) with entry plan `psBranch = { psG with stack, spilled }`; the final
    table then maps `succ ↦ psBranch`. Combines `dfsEntriesAux_head_records` on the `[succ]` sub-call
    with `dfsEntries_table_mono` (over the remaining successors, `succ` now visited via
    `dfsEntriesAux_head_visited`). -/
theorem dfsSuccsEntries_records_first_succ (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (tbl : AssocList String PlanState) (psG : PlanState)
    (bb : BasicBlock) (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains succ = false)
    (hfind : fn.blocks.find? (·.label == succ) = some bb)
    (hsome : dfsSuccsEntries (fuel + 2) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG
      = some result) :
    AssocList.lookup String PlanState result.2.1 succ
      = some { psG with stack := savedStack, spilled := savedSpilled } := by
  rw [dfsSuccsEntries_cons] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vAfter tblAfter psAfter hga =>
    split at hsome
    · exact absurd hsome (by simp)
    · next vF tblF psF hgs =>
      obtain rfl := Option.some.inj hsome
      have hrec : AssocList.lookup String PlanState tblAfter succ
          = some { psG with stack := savedStack, spilled := savedSpilled } :=
        dfsEntriesAux_head_records fuel L D C fn succ [] visited tbl
          { psG with stack := savedStack, spilled := savedSpilled } bb (vAfter, tblAfter, psAfter)
          hvisf hfind hga
      have hvA : vAfter.contains succ = true :=
        dfsEntriesAux_head_visited fuel L D C fn succ [] visited tbl
          { psG with stack := savedStack, spilled := savedSpilled } bb (vAfter, tblAfter, psAfter)
          hvisf hfind hga
      rw [(dfsEntries_table_mono L D C fn (fuel + 1)).2 savedStack savedSpilled rest vAfter tblAfter
        { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) succ
        hgs hvA]
      exact hrec

/-- **Second-successor entry recording.** When processing successors `succ1 :: succ2 :: rest`, the
    first successor's subtree runs to `psAfter` (recording `succ1` at `psG`'s stack/spilled), then the
    plan-state advances to `psG' = { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }`
    (allocator threaded through `succ1`'s subtree). If `succ2` is still unvisited (a DFS-tree edge from
    the pred's second branch), it records at `psG'`'s stack/spilled = the pred's exit stack/spilled with
    the threaded allocator. Reduces to `dfsSuccsEntries_records_first_succ` on the tail recursion — the
    allocator-threading (fnEom fixed, nextOffset ≥) is `dfsEntries_alloc_inv` on `succ1`'s subtree. -/
theorem dfsSuccsEntries_records_second_succ (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ1 succ2 : String) (rest visited : List String) (tbl : AssocList String PlanState)
    (psG : PlanState) (bb1 bb2 : BasicBlock) (vAfter : List String)
    (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (hvisf1 : visited.contains succ1 = false)
    (hfind1 : fn.blocks.find? (·.label == succ1) = some bb1)
    (hga : dfsEntriesAux (fuel + 2) L D C fn [succ1] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } = some (vAfter, tblAfter, psAfter))
    (hvisf2 : vAfter.contains succ2 = false)
    (hfind2 : fn.blocks.find? (·.label == succ2) = some bb2)
    (hsome : dfsSuccsEntries (fuel + 2 + 1) L D C fn savedStack savedSpilled (succ1 :: succ2 :: rest)
      visited tbl psG = some result) :
    AssocList.lookup String PlanState result.2.1 succ2
      = some { stack := savedStack, spilled := savedSpilled, alloc := psAfter.alloc,
               labelCounter := psAfter.labelCounter : PlanState } := by
  rw [dfsSuccsEntries_cons, hga] at hsome
  simp only [] at hsome
  cases hgs : dfsSuccsEntries (fuel + 2) L D C fn savedStack savedSpilled (succ2 :: rest) vAfter tblAfter
      { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
  | none => rw [hgs] at hsome; simp at hsome
  | some rF =>
    rw [hgs] at hsome; obtain rfl := Option.some.inj hsome
    exact dfsSuccsEntries_records_first_succ fuel L D C fn savedStack savedSpilled succ2 rest vAfter
      tblAfter { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } bb2 rF
      hvisf2 hfind2 hgs

/-- **Tree-edge psOf recording (instrumented DFS).** The direct hplan fact: when the first successor
    `succ` is unvisited (a DFS-tree edge), it records the predecessor's *exit* plan state `ps'` — the
    branch is `ps'` itself by structure eta (`{ ps' with stack := ps'.stack, spilled := ps'.spilled } =
    ps'`). This is the recording counterpart of `generateSuccsPlan_first_succ_prefix` (which shows
    `generateBlockPlan` runs on `ps'`): on a tree edge, the successor's entry plan = predecessor's exit,
    so `psOfFn succ = ps' = psPostBody`. -/
theorem dfsSuccsEntries_records_tree_edge (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (ps' : PlanState) (succ : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (bb : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains succ = false)
    (hfind : fn.blocks.find? (·.label == succ) = some bb)
    (hsome : dfsSuccsEntries (fuel + 2) L D C fn ps'.stack ps'.spilled (succ :: rest) visited tbl ps'
      = some result) :
    AssocList.lookup String PlanState result.2.1 succ = some ps' := by
  rw [dfsSuccsEntries_records_first_succ fuel L D C fn ps'.stack ps'.spilled succ rest visited tbl ps'
    bb result hvisf hfind hsome, planState_eta_stack_spilled ps']


/-- **A first-unvisited successor lands in the succs output visited set.** -/
theorem dfsSuccsEntries_first_succ_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (tbl : AssocList String PlanState) (psG : PlanState)
    (bb : BasicBlock) (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains succ = false)
    (hfind : fn.blocks.find? (·.label == succ) = some bb)
    (hsome : dfsSuccsEntries (fuel + 2) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG
      = some result) :
    result.1.contains succ = true := by
  rw [dfsSuccsEntries_cons] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vAfter tblAfter psAfter hga =>
    split at hsome
    · exact absurd hsome (by simp)
    · next vF tblF psF hgs =>
      obtain rfl := Option.some.inj hsome
      have hvA : vAfter.contains succ = true :=
        dfsEntriesAux_head_visited fuel L D C fn succ [] visited tbl
          { psG with stack := savedStack, spilled := savedSpilled } bb (vAfter, tblAfter, psAfter)
          hvisf hfind hga
      exact (dfsEntries_visited_mono L D C fn (fuel + 1)).2 savedStack savedSpilled rest vAfter tblAfter
        { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) succ
        hgs hvA

/-- **A second-unvisited successor lands in the succs output visited set.** Companion of
    `dfsSuccsEntries_records_second_succ`: same reduction to the first-successor case on the tail. -/
theorem dfsSuccsEntries_second_succ_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ1 succ2 : String) (rest visited : List String) (tbl : AssocList String PlanState)
    (psG : PlanState) (bb2 : BasicBlock) (vAfter : List String)
    (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (hga : dfsEntriesAux (fuel + 2) L D C fn [succ1] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } = some (vAfter, tblAfter, psAfter))
    (hvisf2 : vAfter.contains succ2 = false)
    (hfind2 : fn.blocks.find? (·.label == succ2) = some bb2)
    (hsome : dfsSuccsEntries (fuel + 2 + 1) L D C fn savedStack savedSpilled (succ1 :: succ2 :: rest)
      visited tbl psG = some result) :
    result.1.contains succ2 = true := by
  rw [dfsSuccsEntries_cons, hga] at hsome
  simp only [] at hsome
  cases hgs : dfsSuccsEntries (fuel + 2) L D C fn savedStack savedSpilled (succ2 :: rest) vAfter tblAfter
      { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
  | none => rw [hgs] at hsome; simp at hsome
  | some rF =>
    rw [hgs] at hsome; obtain rfl := Option.some.inj hsome
    exact dfsSuccsEntries_first_succ_visited fuel L D C fn savedStack savedSpilled succ2 rest vAfter
      tblAfter { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } bb2 rF
      hvisf2 hfind2 hgs

/-- **Whole-remaining-DFS tree-edge recording.** When `pred` (unvisited) heads the worklist and its
    first successor `succ` is a tree edge (unvisited), the *final* result table maps `succ ↦ ps'`, where
    `ps'` is `pred`'s exit plan (`generateBlockPlan`). The successor's `dfsSuccsEntries` records `ps'`
    (`dfsSuccsEntries_records_tree_edge`), and `dfsEntries_table_mono` preserves it through the rest of
    the worklist (`succ` now visited, via `dfsSuccsEntries_first_succ_visited`). This lifts the tree-edge
    recording from the `dfsSuccsEntries` level to a `dfsEntriesAux` head visit — one level up toward the
    whole `psOfFn` table (which is the `dfsEntriesAux` run from `[entryLbl]`). -/
theorem dfsEntriesAux_head_succ_records (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (pred : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (predBB : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (succ : String) (succRest : List String) (succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hpvisf : visited.contains pred = false)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hbp : generateBlockPlan L D C fn predBB ps = some (blockOps, ps'))
    (hsuccs : C.succsOf pred = succ :: succRest)
    (hsvisf : (pred :: visited).contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsome : dfsEntriesAux (fuel + 3) L D C fn (pred :: rest) visited tbl ps = some result) :
    AssocList.lookup String PlanState result.2.1 succ = some ps' := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hpvisf hpfind] at hsome
  simp only [hbp, hsuccs] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next visited'' tbl'' ps'' hgs =>
    have hrec := dfsSuccsEntries_records_tree_edge fuel L D C fn ps' succ succRest (pred :: visited)
      (AssocList.insert String PlanState tbl pred ps) succBB (visited'', tbl'', ps'') hsvisf hsfind hgs
    have hvis'' := dfsSuccsEntries_first_succ_visited fuel L D C fn ps'.stack ps'.spilled succ succRest
      (pred :: visited) (AssocList.insert String PlanState tbl pred ps) ps' succBB
      (visited'', tbl'', ps'') hsvisf hsfind hgs
    rw [(dfsEntries_table_mono L D C fn (fuel + 2)).1 rest visited'' tbl'' ps'' result succ hsome hvis'']
    exact hrec


/-- **JMP join-reorder synthesises the target's canonical entry stack.** The JMP-specific instantiation
    of `reorderPlan_stack_suffix_eq_target`: a JMP's `joinOps = reorderPlan (targetStack.map Var) ps1`
    (where `targetStack = inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt … target 0)` is the
    target block's expected entry stack) reorders the predecessor's exit so its top region is exactly
    `targetStack.map Var` — the target's canonical entry layout. Every predecessor of a join target
    reorders to this same layout, so all their exits (and the target's DFS entry = first predecessor's
    exit, via `dfsSuccsEntries_records_tree_edge`) agree there — the join-edge branch of
    `psPostBody = psOfFn bb'.label`. -/
theorem jmp_join_reorder_suffix (liveness : DfState (List String)) (curBbLabel target : String)
    (targetBb : BasicBlock) (ps1 : PlanState)
    (hnd : ps1.stack.Nodup)
    (hndT : ((inputVarsFrom curBbLabel targetBb.instructions
      (liveVarsAt liveness target 0)).map Operand.Var).Nodup)
    (hlen : (inputVarsFrom curBbLabel targetBb.instructions
      (liveVarsAt liveness target 0)).length ≤ ps1.stack.length)
    (hpres : ∀ t ∈ (inputVarsFrom curBbLabel targetBb.instructions
      (liveVarsAt liveness target 0)).map Operand.Var, t ∈ ps1.stack) :
    (reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
        (liveVarsAt liveness target 0)).map Operand.Var) ps1).2.stack.drop
      ((reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
          (liveVarsAt liveness target 0)).map Operand.Var) ps1).2.stack.length
        - (inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)).length)
      = (inputVarsFrom curBbLabel targetBb.instructions
          (liveVarsAt liveness target 0)).map Operand.Var := by
  set targetStack := inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)
  have hlenmap : (targetStack.map Operand.Var).length ≤ ps1.stack.length := by
    rw [List.length_map]; exact hlen
  have h := reorderPlan_stack_suffix_eq_target (targetStack.map Operand.Var) ps1 hndT hnd hlenmap hpres
  rw [List.length_map] at h
  exact h


/-- **Head-visit's tree successor lands in the output visited set.** The visited-set companion of
    `dfsEntriesAux_head_succ_records`: when an unvisited `pred` heads the worklist and its first
    successor `succ` is a tree edge, `succ` is visited in the final output. With `head_succ_records`
    (records `succ ↦ ps'`) and `dfsEntries_table_mono` (a visited label's entry is preserved), this is
    the toolkit for propagating a head-visit's tree-edge recording out through the enclosing DFS levels
    (the general-predecessor lift). -/
theorem dfsEntriesAux_head_succ_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (pred : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (predBB : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (succ : String) (succRest : List String) (succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hpvisf : visited.contains pred = false)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hbp : generateBlockPlan L D C fn predBB ps = some (blockOps, ps'))
    (hsuccs : C.succsOf pred = succ :: succRest)
    (hsvisf : (pred :: visited).contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsome : dfsEntriesAux (fuel + 3) L D C fn (pred :: rest) visited tbl ps = some result) :
    result.1.contains succ = true := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hpvisf hpfind] at hsome
  simp only [hbp, hsuccs] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next visited'' tbl'' ps'' hgs =>
    have hvis'' := dfsSuccsEntries_first_succ_visited fuel L D C fn ps'.stack ps'.spilled succ succRest
      (pred :: visited) (AssocList.insert String PlanState tbl pred ps) ps' succBB
      (visited'', tbl'', ps'') hsvisf hsfind hgs
    exact (dfsEntries_visited_mono L D C fn (fuel + 2)).1 rest visited'' tbl'' ps'' result succ hsome hvis''

/-- **Head-visit second-successor recording.** `pred` (unvisited) heads the worklist with two successors
    `succ1 :: succ2 :: succRest` (the JNZ shape). After `succ1`'s subtree runs to `psAfter`, if `succ2` is
    still unvisited it records `pred`'s exit stack/spilled with the allocator threaded through `succ1`'s
    subtree. Head-level lift of `dfsSuccsEntries_records_second_succ` (via `dfsEntries_table_mono`). -/
theorem dfsEntriesAux_head_succ2_records (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (pred : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (predBB : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (succ1 succ2 : String) (succRest : List String) (succBB1 succBB2 : BasicBlock)
    (vAfter : List String) (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (hpvisf : visited.contains pred = false)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hbp : generateBlockPlan L D C fn predBB ps = some (blockOps, ps'))
    (hsuccs : C.succsOf pred = succ1 :: succ2 :: succRest)
    (hsvisf1 : (pred :: visited).contains succ1 = false)
    (hsfind1 : fn.blocks.find? (·.label == succ1) = some succBB1)
    (hga : dfsEntriesAux (fuel + 2) L D C fn [succ1] (pred :: visited)
      (AssocList.insert String PlanState tbl pred ps)
      { ps' with stack := ps'.stack, spilled := ps'.spilled } = some (vAfter, tblAfter, psAfter))
    (hsvisf2 : vAfter.contains succ2 = false)
    (hsfind2 : fn.blocks.find? (·.label == succ2) = some succBB2)
    (hsome : dfsEntriesAux (fuel + 2 + 1 + 1) L D C fn (pred :: rest) visited tbl ps = some result) :
    AssocList.lookup String PlanState result.2.1 succ2
      = some { stack := ps'.stack, spilled := ps'.spilled, alloc := psAfter.alloc,
               labelCounter := psAfter.labelCounter : PlanState } := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hpvisf hpfind] at hsome
  simp only [hbp, hsuccs] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next visited'' tbl'' ps'' hgs =>
    have hrec := dfsSuccsEntries_records_second_succ fuel L D C fn ps'.stack ps'.spilled succ1 succ2
      succRest (pred :: visited) (AssocList.insert String PlanState tbl pred ps) ps' succBB1 succBB2
      vAfter tblAfter psAfter (visited'', tbl'', ps'') hsvisf1 hsfind1 hga hsvisf2 hsfind2 hgs
    have hvis'' := dfsSuccsEntries_second_succ_visited fuel L D C fn ps'.stack ps'.spilled succ1 succ2
      succRest (pred :: visited) (AssocList.insert String PlanState tbl pred ps) ps' succBB2
      vAfter tblAfter psAfter (visited'', tbl'', ps'') hga hsvisf2 hsfind2 hgs
    rw [(dfsEntries_table_mono L D C fn (fuel + 2 + 1)).1 rest visited'' tbl'' ps'' result succ2
      hsome hvis'']
    exact hrec

/-- **Head-visit second-successor visited-set membership.** Companion of
    `dfsEntriesAux_head_succ2_records`. -/
theorem dfsEntriesAux_head_succ2_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (pred : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (predBB : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (succ1 succ2 : String) (succRest : List String) (succBB2 : BasicBlock)
    (vAfter : List String) (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (hpvisf : visited.contains pred = false)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hbp : generateBlockPlan L D C fn predBB ps = some (blockOps, ps'))
    (hsuccs : C.succsOf pred = succ1 :: succ2 :: succRest)
    (hga : dfsEntriesAux (fuel + 2) L D C fn [succ1] (pred :: visited)
      (AssocList.insert String PlanState tbl pred ps)
      { ps' with stack := ps'.stack, spilled := ps'.spilled } = some (vAfter, tblAfter, psAfter))
    (hsvisf2 : vAfter.contains succ2 = false)
    (hsfind2 : fn.blocks.find? (·.label == succ2) = some succBB2)
    (hsome : dfsEntriesAux (fuel + 2 + 1 + 1) L D C fn (pred :: rest) visited tbl ps = some result) :
    result.1.contains succ2 = true := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hpvisf hpfind] at hsome
  simp only [hbp, hsuccs] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next visited'' tbl'' ps'' hgs =>
    have hvis'' := dfsSuccsEntries_second_succ_visited fuel L D C fn ps'.stack ps'.spilled succ1 succ2
      succRest (pred :: visited) (AssocList.insert String PlanState tbl pred ps) ps' succBB2
      vAfter tblAfter psAfter (visited'', tbl'', ps'') hga hsvisf2 hsfind2 hgs
    exact (dfsEntries_visited_mono L D C fn (fuel + 2 + 1)).1 rest visited'' tbl'' ps'' result succ2
      hsome hvis''


/-- **Generic `Option` fold-lift.** If a step `F (some acc) x` always succeeds as `some (G acc x)` on
    the list's elements, the whole `Option`-threaded fold equals `some` of the raw `G`-fold. -/
theorem foldl_option_lift {α β : Type} (F : Option β → α → Option β) (G : β → α → β)
    (l : List α) (init : β)
    (h : ∀ (acc : β) (x : α), x ∈ l → F (some acc) x = some (G acc x)) :
    l.foldl F (some init) = some (l.foldl G init) := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, h init x (List.mem_cons_self ..),
        ih (G init x) (fun acc y hy => h acc y (List.mem_cons_of_mem x hy))]

/-- **Single-step regular lift for `instFoldF`.** On a regular (non-special) instruction, one
    `instFoldF` step from a `some` accumulator succeeds, threading `generateRegularInstPlan`
    (via `generateInstPlan_regular_eq`). -/
theorem instFoldF_some_regular
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ops : List StackOp) (psc : PlanState) (inst : Instruction) (i : Nat)
    (h0 : ¬ isPreCodegenOpcode inst.opcode)
    (hphi : inst.opcode ≠ Opcode.PHI) (hoff : inst.opcode ≠ Opcode.OFFSET)
    (hparam : inst.opcode ≠ Opcode.PARAM) (hnop : inst.opcode ≠ Opcode.NOP) :
    instFoldF L D C fn bb (some (ops, psc)) (inst, i)
      = some (let nextLive := if i + 1 < (nonParamInsts bb).length then
                  liveVarsAt L bb.label (i + (getParams bb.instructions).length + 1)
                else liveVarsAt L bb.label bb.instructions.length
              let nextIsTerm := if i + 1 < (nonParamInsts bb).length then
                  isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
              let r := generateRegularInstPlan L D C fn inst nextLive (bbIsHalting bb) nextIsTerm bb.label psc
              (ops ++ r.1, r.2)) := by
  unfold instFoldF
  simp only [generateInstPlan_regular_eq h0 hphi hoff hparam hnop]

/-- **Body-fold representation lift (① layer a).** For a body of all-regular (non-special) instructions,
    the `Option`-threaded `instFoldF` body-fold equals `some` of the raw per-instruction fold with the
    positional `generateRegularInstPlan` generator — i.e. the concrete `generateBlockPlan` closure equals
    the abstract per-block adapter's `gp`/`lg` fold when the adapter's `gp` is instantiated with this
    positional generator. Together with `generateBlockPlan_ps'_eq_bodyfold_jmp` (`ps' = body-fold`) and
    `psOfFn_entry_succ` (`psOf successor = ps'`), this discharges the per-block `hstep` residual
    `body-fold = psOf successor` for aligned JMP blocks. -/
theorem instFoldF_regular_fold
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (l : List (Instruction × Nat)) (ps0 : PlanState)
    (hreg : ∀ x ∈ l, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    l.foldl (instFoldF L D C fn bb) (some ([], ps0))
      = some (l.foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
          let nextLive := if x.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (x.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length
          let nextIsTerm := if x.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[x.2 + 1]!.opcode else false
          let r := generateRegularInstPlan L D C fn x.1 nextLive (bbIsHalting bb) nextIsTerm bb.label acc.2
          (acc.1 ++ r.1, r.2)) ([], ps0)) := by
  apply foldl_option_lift
  intro acc x hx
  obtain ⟨h0, hphi, hoff, hparam, hnop⟩ := hreg x hx
  exact instFoldF_some_regular L D C fn bb acc.1 acc.2 x.1 x.2 h0 hphi hoff hparam hnop

/-- **Adapter `lg`-fold = positional `front.zipIdx` fold.** The per-block adapter
    (`hstep_regularHSVP_jmp` etc.) folds `gp x.1` over `lg`; since `lg.map Prod.fst = front.zipIdx 0`
    (`hfront`), that equals the fold of `gp` over `front.zipIdx 0` directly (`List.foldl_map`). This is
    the `lg`-instantiation step connecting the adapter's fold to `bridge_foldOut_eq_psOf_jmp`. -/
theorem adapter_fold_eq_zipIdx
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (lg : List ((Instruction × Nat) × List String)) (front : List Instruction) (ps0 : PlanState)
    (hfront : lg.map Prod.fst = front.zipIdx 0) :
    lg.foldl (fun (acc : List StackOp × PlanState) x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)
      = (front.zipIdx 0).foldl
          (fun (acc : List StackOp × PlanState) x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0) := by
  rw [← hfront, List.foldl_map]

/-- **Aligned JMP block: full-plan output = body-fold output.** Composes the plan-representation
    spine (`generateBlockPlan_split_term`), the dispatch (`generateInstPlan_regular_eq`), and the JMP
    terminator-step identity (`generateRegularInstPlan_jmp_id`): for a multi-pred, phi/param-free block
    whose `nonParamInsts = front ++ [JMP target]` with an aligned successor (`inputVarsFrom = []`), the
    block-plan output `ps'` equals the body-fold output `ps_body` whenever `ps_body` has no spills.

    With `psOfFn_entry_succ` (`psOf successor = ps'`, the predecessor's full-block output) this yields
    `psOf successor = ps_body` — the per-block `hstep` residual `body-fold = psOf successor`, now
    reduced to the body-fold *representation* reconciliation (the adapter's abstract `gp`/`lg` fold vs
    `instFoldF`, the only remaining ① layer). -/
theorem generateBlockPlan_ps'_eq_bodyfold_jmp
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) → ps' = ps_body) := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, _⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide)
      (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide)] at hterm_step
  have hps' : ps' = (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).2 := by
    rw [Option.some.injEq, Prod.mk.injEq] at hterm_step; exact hterm_step.2.symm
  rw [hps', generateRegularInstPlan_jmp_id hterm_jmp hterm_ops hterm_outs hjoin hsp]

/-- **Aligned JMP block: full plan structure.** Strengthens `generateBlockPlan_ps'_eq_bodyfold_jmp`
    with the ops side (via `generateRegularInstPlan_jmp_full`): the block plan is
    `SOLabel bb.label :: bodyOps ++ [SOPushLabel target, SOEmit "JUMP"]` and `ps' = ps_body`, the
    body-fold output — the plan-level foundation for the asm layout (`hpush`/`hjump`/`hblock` after
    `asmResolve (executePlan …)`), the remaining ③ asm-layout side of `hstep_regularHSVP_jmp`. -/
theorem generateBlockPlan_aligned_jmp
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) →
        blockOps = StackOp.SOLabel bb.label :: bodyOps ++
          [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] ∧ ps' = ps_body) := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide)
      (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide),
      generateRegularInstPlan_jmp_full hterm_jmp hterm_ops hterm_outs hjoin hsp] at hterm_step
  obtain ⟨htops, hps'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hterm_step
  exact ⟨by rw [hblk, ← htops], hps'.symm⟩

/-- **Aligned bare-halting block plan = label ∷ body ++ `[SOEmit name]`** (STOP/INVALID). The bare-op
    analogue of `generateBlockPlan_aligned_jmp`: for a phi/param-free multi-pred block whose terminator is
    a bare halting op with a single EVM name (`opcodeToEvmName = some name`), no operands, no outputs, the
    block plan decomposes into the body-fold (`instFoldF`) and a single trailing `SOEmit name`, and the
    block output `ps' = ps_body` (when the body leaves no spills). Composes `generateBlockPlan_split_term`
    (generic body∘term split) + `generateInstPlan_regular_eq` + `generateRegularInstPlan_bareHalt_full`. -/
theorem generateBlockPlan_aligned_bareHalt
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = [])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) →
        blockOps = StackOp.SOLabel bb.label :: bodyOps ++ [StackOp.SOEmit name] ∧ ps' = ps_body) := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2,
      generateRegularInstPlan_bareHalt_full hname hterm_ops hterm_outs hsp] at hterm_step
  obtain ⟨htops, hps'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hterm_step
  exact ⟨by rw [hblk, ← htops], hps'.symm⟩

/-- **Aligned two-operand-terminal (RETURN/REVERT) block plan = label ∷ body ++ emit ++ `[SOEmit name]`.**
    Operand-terminal analogue of `generateBlockPlan_aligned_bareHalt`: the block plan's *ops* decompose
    into the body-fold, the operand emission `emitInputPlan term.opcode [sz, off] nl ps_body`, and a single
    trailing `SOEmit name`. Composes `generateBlockPlan_split_term` + `generateInstPlan_regular_eq` +
    `generateRegularInstPlan_return_full`. `hreorderNil` (join-reorder positioned after emission) is
    quantified over the body-fold — the alignment condition, discharged separately. Only `blockOps` (ops)
    characterized; terminal `ps'` irrelevant (halts). -/
theorem generateBlockPlan_aligned_return
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false)
    (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      blockOps = StackOp.SOLabel bb.label :: bodyOps ++
        ((emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name]) := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2] at hterm_step
  have h1 : (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).1 = termOps :=
    congrArg Prod.fst (Option.some.inj hterm_step)
  have hto : termOps = (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
      (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name] := by
    rw [← h1]
    exact generateRegularInstPlan_return_full hname hncomm hnjmp hco hterm_outs
      (hreorderNil bodyOps ps_body hbody)
  rw [hblk, hto]

/-- **Aligned JNZ block plan = label ∷ body ++ `[DUP1, push ifNz, JUMPI, push ifZ, JUMP]`.** Dual-successor
    analogue of `generateBlockPlan_aligned_return`: the block plan ops decompose into the body-fold and the
    5-op JNZ tail. Composes `generateBlockPlan_split_term` + `generateInstPlan_regular_eq` +
    `generateRegularInstPlan_jnz_full`. The condition-DUP1 emission (`hemit`) and join-reorder (`hreorder`)
    are quantified over the body-fold — alignment conditions discharged separately. -/
theorem generateBlockPlan_aligned_jnz
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      blockOps = StackOp.SOLabel bb.label :: bodyOps ++
        [StackOp.SODup 1, StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
         StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2] at hterm_step
  have h1 : (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).1 = termOps :=
    congrArg Prod.fst (Option.some.inj hterm_step)
  have hto : termOps = [StackOp.SODup 1, StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
      StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := by
    rw [← h1]
    exact generateRegularInstPlan_jnz_full hterm_jnz hterm_ops hterm_outs
      (hemit bodyOps ps_body hbody) (hreorder bodyOps ps_body hbody)
  rw [hblk, hto]

/-- **Aligned JNZ block: `ps' = body-fold output`.** The JNZ analogue of
    `generateBlockPlan_ps'_eq_bodyfold_jmp`: the JNZ terminator threads the plan state unchanged
    (`generateRegularInstPlan_jnz_id` — the DUP+POP cancel), so the block output `ps'` equals the body-fold
    output when the body leaves no spills. The plan-effect half a JNZ scheduling-residual discharge needs:
    combined with the DFS successor-recording (`psOfFn ifNz = predecessor exit`) it gives
    `(lg.foldl gp).2 = psOfFn ifNz` for the *taken* branch (`ifNz` = first successor). The state-alignment
    conditions (`hemit`/`hreorderS`) are quantified over the body-fold. -/
theorem generateBlockPlan_ps'_eq_bodyfold_jnz
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c] (liveVarsAt L bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) → ps' = ps_body) := by
  obtain ⟨bodyOps, ps_body, termOps, hbody, hterm_step, _⟩ :=
    generateBlockPlan_split_term L D C fn bb ps blockOps ps' front term hentry hmulti hnp hplan
  refine ⟨bodyOps, ps_body, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2] at hterm_step
  have hps' : ps' = (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).2 := by
    rw [Option.some.injEq, Prod.mk.injEq] at hterm_step; exact hterm_step.2.symm
  rw [hps', generateRegularInstPlan_jnz_id hterm_jnz hterm_ops hterm_outs
    (hemit bodyOps ps_body hbody) (hreorderS bodyOps ps_body hbody) hsp]

/-- **General aligned-JMP block whole-program asm structure** (any block placed as a plan segment
    `ops = preOps ++ blockOps ++ tailOps`, entry or chain-reached). The compiled asm is
    `executePlan preOps ++ (label+body asm ++ [AsmPushLabel target, AsmOp "JUMP"]) ++ executePlan tailOps`.
    Generalizes `entry_aligned_jmp_prog_asm` (`preOps = []`, entry) to blocks reached via a JMP chain
    (`generateFnPlanFuel_chain_segment` supplies `hseg`; `JmpChainTo` supplies `hgbp`) — the non-entry
    component of the ③ asm-layout side, needed by the universal per-block discharge. -/
theorem blockplan_aligned_jmp_prog_asm
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
            ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps := by
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_aligned_jmp L D C fn bb ps_in blockOps ps' front term target hentry0 hmulti hnp
      hterm_jmp hterm_ops hterm_outs hjoin hgbp
  obtain ⟨hblockOpsEq, _⟩ := himp (hnospill bodyOps ps_body hbody)
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockOpsEq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: bodyOps ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"]
      = [StackOp.SOLabel bb.label] ++ bodyOps ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] := rfl
  rw [heq, executePlan_aligned_jmp_block]

/-- **Whole-program asm structure for an entry-aligned-JMP function.** The compiled asm of the whole
    function plan is the entry block's label+body asm, then `[AsmPushLabel target, AsmOp "JUMP"]`, then
    the rest — placing the entry aligned JMP block's tail at pc `= (executePlan ([SOLabel entry.label]
    ++ bodyOps)).length`. Composes `generateFnPlanFuel_first_succ_segment` (ops = entryOps ++ …),
    `generateBlockPlan_aligned_jmp` (entryOps = SOLabel :: body ++ [PushLabel, JUMP]), and
    `executePlan_aligned_jmp_block`. With `asmResolve` pointwise (`asmResolve_fst`) +
    `aligned_jmp_tail_resolved` + `asmBlockAt_resolved_of_middle_no_label` this yields the entry
    block's `hblock`/`hpush`/`hjump` — the ③ asm-layout side on a real (generic) entry function. -/
theorem entry_aligned_jmp_prog_asm
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry succBB : BasicBlock} {succ : String} {succRest : List String}
    {ops : List StackOp} {ps : PlanState}
    {front : List Instruction} {term : Instruction} {target : String}
    (hfuel : 3 ≤ fuel)
    (hheadeq : fn.blocks.head? = some entry)
    (hsucc : (cfgAnalyze fn).succsOf entry.label = succ :: succRest)
    (hne : (succ == entry.label) = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn entry)
    (hnp : nonParamInsts entry = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom entry.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry) (some ([], { initPlanState fnEom with labelCounter := lblCtr }))
          = some (bodyOps, ps_body) → ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body succAsm,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry) (some ([], { initPlanState fnEom with labelCounter := lblCtr }))
          = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)
            ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ succAsm := by
  obtain ⟨entryOps, ps', succBlockOps, psS, rest, hentryBp, _, hopseq⟩ :=
    generateFnPlanFuel_first_succ_segment hfuel hheadeq hsucc hne hsfind hfn hgen
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_aligned_jmp (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr } entryOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hentryBp
  obtain ⟨hentryOpsEq, _⟩ := himp (hnospill bodyOps ps_body hbody)
  refine ⟨bodyOps, ps_body, executePlan (succBlockOps ++ rest), hbody, ?_⟩
  rw [hopseq, List.append_assoc, executePlan_append, hentryOpsEq]
  congr 1
  have heq : StackOp.SOLabel entry.label :: bodyOps ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"]
      = [StackOp.SOLabel entry.label] ++ bodyOps ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] := rfl
  rw [heq, executePlan_aligned_jmp_block]

/-- **Entry aligned-JMP block asm-layout: `hblock`/`hpush`/`hjump`.** From the whole-program asm
    structure (`entry_aligned_jmp_prog_asm`) this derives, at pc `0`, the three asm-layout facts
    `hstep_regularHSVP_jmp` needs for a function whose entry is an aligned JMP block:
    `asmBlockAt prog 0 (label+body asm)` (`asmBlockAt_resolved_of_middle_no_label`, given the body asm
    is push-label-free — `hlblfree`), and the resolved push-label + `JUMP` at pc `bodyLen`/`bodyLen+1`
    (`aligned_jmp_tail_resolved`). This closes the ③ asm-layout side for the entry aligned JMP block on a
    real (generic) function; what remains is threading the HSVP body-sim facts + the residual discharge
    (`bridge_foldOut_eq_psOf_jmp`) into the adapter and feeding `codegen_correct_sched`. -/
theorem entry_aligned_jmp_layout
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry succBB : BasicBlock} {succ : String} {succRest : List String}
    {ops : List StackOp} {ps : PlanState}
    {front : List Instruction} {term : Instruction} {target : String}
    (hfuel : 3 ≤ fuel) (hheadeq : fn.blocks.head? = some entry)
    (hsucc : (cfgAnalyze fn).succsOf entry.label = succ :: succRest)
    (hne : (succ == entry.label) = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn entry)
    (hnp : nonParamInsts entry = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom entry.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry) (some ([], { initPlanState fnEom with labelCounter := lblCtr }))
          = some (bodyOps, ps_body) → ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry) (some ([], { initPlanState fnEom with labelCounter := lblCtr }))
          = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel entry.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry) (some ([], { initPlanState fnEom with labelCounter := lblCtr }))
          = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 0
        (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)) ∧
      (∃ h : (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)).length]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel target)) ∧
      (∃ h : (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)).length + 1
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)).length + 1]'h
          = AsmInst.AsmOp "JUMP") := by
  obtain ⟨bodyOps, ps_body, succAsm, hbody, hopsEq⟩ :=
    entry_aligned_jmp_prog_asm hfuel hheadeq hsucc hne hsfind hfn hgen hmulti hnp hterm_jmp hterm_ops
      hterm_outs hjoin hentry0 hnospill
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_, ?_⟩
  · rw [hopsEq]
    have := asmBlockAt_resolved_of_middle_no_label ([] : List AsmInst)
      (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps))
      ([AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ succAsm)
      (fun a ha lbl => (hlblfree bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree bodyOps ps_body hbody a ha).2 lbl d)
    simpa using this
  · rw [hopsEq]
    exact (aligned_jmp_tail_resolved (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)) succAsm target).1
  · rw [hopsEq]
    exact (aligned_jmp_tail_resolved (executePlan ([StackOp.SOLabel entry.label] ++ bodyOps)) succAsm target).2

/-- **General aligned-JMP block asm-layout** (`hblock`/`hpush`/`hjump` at pc `(executePlan preOps).length`).
    Generalizes `entry_aligned_jmp_layout` (`preOps = []`, pc 0) to any block placed as a plan segment —
    the non-entry component of the ③ asm-layout side. Composes `blockplan_aligned_jmp_prog_asm` with
    `asmBlockAt_resolved_of_middle_no_label` (hblock, body push-label-free) and `aligned_jmp_tail_resolved`
    (hpush/hjump), reassociating the whole-program asm around the block segment. -/
theorem blockplan_aligned_jmp_layout
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel target)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 1
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 1]'h
          = AsmInst.AsmOp "JUMP") := by
  obtain ⟨bodyOps, ps_body, hbody, hprog⟩ :=
    blockplan_aligned_jmp_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term target
      hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp hseg hnospill
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
        ++ ([AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      ([AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps)
      (fun a ha lbl => (hlblfree bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree bodyOps ps_body hbody a ha).2 lbl d)
  · have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := (aligned_jmp_tail_resolved (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      (executePlan tailOps) target).1
    simpa [List.length_append] using this
  · have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := (aligned_jmp_tail_resolved (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      (executePlan tailOps) target).2
    simpa [List.length_append] using this

/-- **`pcOfLabel` of an aligned-JMP block = its segment offset.** For an aligned-JMP block placed as a
    plan segment (`ops = preOps ++ blockOps ++ tailOps`) whose label does not occur in the prefix asm,
    `pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length` — the block's pc,
    matching `hstep_regularHSVP_jmp`'s `as0.pc` on the canonical schedule. Composes
    `blockplan_aligned_jmp_prog_asm` + `pcOfLabel_asmResolve` + `pcOfLabel_of_decomp`. -/
theorem pcOfLabel_aligned_jmp_block
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨bodyOps, ps_body, _hbody, hprog⟩ :=
    blockplan_aligned_jmp_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term target
      hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp hseg hnospill
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
      = AsmInst.AsmLabel bb.label :: executePlan bodyOps := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan bodyOps
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan bodyOps ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]

/-- **Aligned bare-halting (STOP/INVALID) block whole-program asm structure.** Bare-op analogue of
    `blockplan_aligned_jmp_prog_asm`: the compiled asm is
    `executePlan preOps ++ (label+body asm ++ [AsmOp name]) ++ executePlan tailOps`. -/
theorem blockplan_aligned_bareHalt_prog_asm
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
            ++ [AsmInst.AsmOp name]) ++ executePlan tailOps := by
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_aligned_bareHalt L D C fn bb ps_in blockOps ps' front term name hentry0 hmulti hnp
      hname hterm_ops hterm_outs hterm_reg hgbp
  obtain ⟨hblockOpsEq, _⟩ := himp (hnospill bodyOps ps_body hbody)
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockOpsEq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: bodyOps ++ [StackOp.SOEmit name]
      = [StackOp.SOLabel bb.label] ++ bodyOps ++ [StackOp.SOEmit name] := rfl
  rw [heq, executePlan_aligned_bareHalt_block]

/-- **Aligned bare-halting (STOP/INVALID) asm-layout.** Bare-op analogue of `blockplan_aligned_jmp_layout`:
    the block sits at segment offset `(executePlan preOps).length` and the terminal op `AsmOp name` is at
    that offset + label-body length (matching `hstep_regularHSVP_stop`/`_invalid`'s `hblock` + `hget`). -/
theorem blockplan_aligned_bareHalt_layout
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length]'h
          = AsmInst.AsmOp name) := by
  obtain ⟨bodyOps, ps_body, hbody, hprog⟩ :=
    blockplan_aligned_bareHalt_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp hseg hnospill
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
        ++ ([AsmInst.AsmOp name] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      ([AsmInst.AsmOp name] ++ executePlan tailOps)
      (fun a ha lbl => (hlblfree bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree bodyOps ps_body hbody a ha).2 lbl d)
  · have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
        ++ [AsmInst.AsmOp name] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := aligned_bareHalt_tail_resolved (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      (executePlan tailOps) name
    simpa [List.length_append] using this

/-- **`pcOfLabel` of an aligned bare-halting block = its segment offset** (bare-op analogue of
    `pcOfLabel_aligned_jmp_block`). -/
theorem pcOfLabel_aligned_bareHalt_block
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨bodyOps, ps_body, _hbody, hprog⟩ :=
    blockplan_aligned_bareHalt_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp hseg hnospill
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
      = AsmInst.AsmLabel bb.label :: executePlan bodyOps := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan bodyOps
        ++ [AsmInst.AsmOp name]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan bodyOps ++ [AsmInst.AsmOp name] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]

/-- **Aligned RETURN/REVERT block whole-program asm structure.** Operand-terminal analogue of
    `blockplan_aligned_bareHalt_prog_asm`: the block plan `SOLabel ∷ body ++ emit ++ [SOEmit name]`
    reassociates to `[SOLabel] ++ (body++emit) ++ [SOEmit name]`, so — reusing
    `executePlan_aligned_bareHalt_block` with the prefix `body++emit` — the compiled asm is
    `executePlan preOps ++ (label+(body++emit) asm ++ [AsmOp name]) ++ executePlan tailOps`. -/
theorem blockplan_aligned_return_prog_asm
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
            (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
              (liveVarsAt L bb.label bb.instructions.length) ps_body).1))
            ++ [AsmInst.AsmOp name]) ++ executePlan tailOps := by
  obtain ⟨bodyOps, ps_body, hbody, hblockeq⟩ :=
    generateBlockPlan_aligned_return L D C fn bb ps_in blockOps ps' front term name offv szv
      hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockeq]
  congr 2
  have hreassoc : StackOp.SOLabel bb.label :: bodyOps ++
        ((emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name])
      = [StackOp.SOLabel bb.label] ++ (bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1) ++ [StackOp.SOEmit name] := by
    simp [List.append_assoc]
  rw [hreassoc, executePlan_aligned_bareHalt_block]

/-- **Aligned RETURN/REVERT asm-layout.** `hblock` (`asmBlockAt` for label+body+emit) + `hget`
    (`AsmOp name` at segment offset + `(body++emit)` length = `bodyLen + emitLen`), matching
    `hasm_regularHSVP_return_var`'s layout. Reuses `aligned_bareHalt_tail_resolved` with prefix
    `body++emit`; the interior is label-free from `hlblfree` (body) + `emitInputPlan_no_label` (emit). -/
theorem blockplan_aligned_return_layout
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1))) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
              (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length) ps_body).1))).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
              (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length) ps_body).1))).length]'h
          = AsmInst.AsmOp name) := by
  obtain ⟨bodyOps, ps_body, hbody, hprog⟩ :=
    blockplan_aligned_return_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp hseg
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
            (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
              (liveVarsAt L bb.label bb.instructions.length) ps_body).1))
        ++ ([AsmInst.AsmOp name] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    refine asmBlockAt_resolved_of_middle_no_label (executePlan preOps) _
      ([AsmInst.AsmOp name] ++ executePlan tailOps) ?_ ?_
    · intro a ha lbl
      rw [← List.append_assoc, executePlan_append, List.mem_append] at ha
      rcases ha with h | h
      · exact (hlblfree bodyOps ps_body hbody a h).1 lbl
      · exact (executePlan_no_label _
          (emitInputPlan_no_label term.opcode _ [Operand.Var szv, Operand.Var offv]
            (by intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop;
                rcases hop with rfl | rfl <;> simp) ps_body) a h).1 lbl
    · intro a ha lbl d
      rw [← List.append_assoc, executePlan_append, List.mem_append] at ha
      rcases ha with h | h
      · exact (hlblfree bodyOps ps_body hbody a h).2 lbl d
      · exact (executePlan_no_label _
          (emitInputPlan_no_label term.opcode _ [Operand.Var szv, Operand.Var offv]
            (by intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop;
                rcases hop with rfl | rfl <;> simp) ps_body) a h).2 lbl d
  · have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1)))
        ++ [AsmInst.AsmOp name] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := aligned_bareHalt_tail_resolved (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
      (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1))) (executePlan tailOps) name
    simpa [List.length_append] using this

/-- **`pcOfLabel` of an aligned RETURN/REVERT block = its segment offset.** The block still begins with
    `SOLabel bb.label`, so — like `pcOfLabel_aligned_bareHalt_block` but with the `body++emit` prefix — the
    first `AsmLabel bb.label` in the resolved program sits at `(executePlan preOps).length`. -/
theorem pcOfLabel_aligned_return_block
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨bodyOps, ps_body, _hbody, hprog⟩ :=
    blockplan_aligned_return_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp hseg
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1))
      = AsmInst.AsmLabel bb.label :: executePlan (bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1) := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan (bodyOps ++
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1) ++ [AsmInst.AsmOp name])
        ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan (bodyOps ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1)
            ++ [AsmInst.AsmOp name] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]

/-- **Aligned JNZ block whole-program asm structure.** Dual-successor analogue of
    `blockplan_aligned_jmp_prog_asm`: the compiled asm is `executePlan preOps ++ (label+body asm ++
    [DUP1, push ifNz, JUMPI, push ifZ, JUMP]) ++ executePlan tailOps`. -/
theorem blockplan_aligned_jnz_prog_asm
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
            ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps := by
  obtain ⟨bodyOps, ps_body, hbody, hblockeq⟩ :=
    generateBlockPlan_aligned_jnz L D C fn bb ps_in blockOps ps' front term c ifNz ifZ hentry0 hmulti
      hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockeq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: bodyOps ++ [StackOp.SODup 1, StackOp.SOPushLabel ifNz,
        StackOp.SOEmit "JUMPI", StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"]
      = [StackOp.SOLabel bb.label] ++ bodyOps ++ [StackOp.SODup 1, StackOp.SOPushLabel ifNz,
        StackOp.SOEmit "JUMPI", StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := rfl
  rw [heq, executePlan_aligned_jnz_block]

/-- **Aligned JNZ asm-layout.** `hblock` (label+body, like JMP — the condition is in the body, DUP1 in the
    tail) + the 5 tail positions (`AsmOp "DUP1"`, `resolveInst … (AsmPushLabel ifNz)`, `AsmOp "JUMPI"`,
    `resolveInst … (AsmPushLabel ifZ)`, `AsmOp "JUMP"`) at `bodyLen`..`bodyLen+4` — exactly
    `hstep_regularHSVP_jnz_{taken,nottaken}`'s `hdup`/`hpushNz`/`hjumpi`/`hpushZ`/`hjump`. Reuses
    `aligned_jnz_tail_resolved` + `asmBlockAt_resolved_of_middle_no_label` (body label-free from `hlblfree`). -/
theorem blockplan_aligned_jnz_layout
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length]'h
          = AsmInst.AsmOp "DUP1") ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 1
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 1]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifNz)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 2
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 2]'h
          = AsmInst.AsmOp "JUMPI") ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 3
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 3]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifZ)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 4
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length + 4]'h
          = AsmInst.AsmOp "JUMP") := by
  obtain ⟨bodyOps, ps_body, hbody, hprog⟩ :=
    blockplan_aligned_jnz_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term c ifNz ifZ
      hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp hseg
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
        ++ ([AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
              AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)) _
      (fun a ha lbl => (hlblfree bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree bodyOps ps_body hbody a ha).2 lbl d)
  all_goals
    have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
        ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
            AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    obtain ⟨hd', hn', hj', hz', hm'⟩ := aligned_jnz_tail_resolved
      (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps))
      (executePlan tailOps) ifNz ifZ
    first
      | (simpa [List.length_append] using hd')
      | (simpa [List.length_append] using hn')
      | (simpa [List.length_append] using hj')
      | (simpa [List.length_append] using hz')
      | (simpa [List.length_append] using hm')

/-- **`pcOfLabel` of an aligned JNZ block = its segment offset** (same leading `SOLabel bb.label`
    decomposition as `pcOfLabel_aligned_jmp_block`, with the 5-op JNZ tail). -/
theorem pcOfLabel_aligned_jnz_block
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨bodyOps, ps_body, _hbody, hprog⟩ :=
    blockplan_aligned_jnz_prog_asm L D C fn bb ps_in ops preOps tailOps blockOps ps' front term c ifNz ifZ
      hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp hseg
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)
      = AsmInst.AsmLabel bb.label :: executePlan bodyOps := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan bodyOps
        ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
            AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan bodyOps ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
            AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]

/-- **① toolkit composition: adapter's positional gp-fold output = psOf successor** (aligned JMP block).
    Chains `generateBlockPlan_ps'_eq_bodyfold_jmp` (`ps' = body-fold`), `instFoldF_regular_fold`
    (`instFoldF` body-fold = `some` of the raw positional gp-fold), and layer 4 (`psSucc = ps'`, which
    `psOfFn_entry_succ`/`psOfFn_chain` supply). The per-block `hstep` residuals `hstk/hsp/hfe/hno` are
    then `rfl`/`le_refl` corollaries of this single equality — the ③ interface between the closed ①
    bridge and the driver's per-block hypotheses. The `gp` here is the positional `generateRegularInstPlan`
    generator (what a codegen-faithful instantiation of `hstep_regularHSVP_jmp`'s abstract `gp` uses). -/
theorem bridge_foldOut_eq_psOf_jmp
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' psSucc : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps'))
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hlayer4 : psSucc = ps')
    (hnospill : ((front.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
          let nextLive := if x.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (x.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length
          let nextIsTerm := if x.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[x.2 + 1]!.opcode else false
          let r := generateRegularInstPlan L D C fn x.1 nextLive (bbIsHalting bb) nextIsTerm bb.label acc.2
          (acc.1 ++ r.1, r.2)) ([], ps)).2.spilled = ([] : AssocList Operand Nat)) :
    ((front.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
          let nextLive := if x.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (x.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length
          let nextIsTerm := if x.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[x.2 + 1]!.opcode else false
          let r := generateRegularInstPlan L D C fn x.1 nextLive (bbIsHalting bb) nextIsTerm bb.label acc.2
          (acc.1 ++ r.1, r.2)) ([], ps)).2 = psSucc := by
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_ps'_eq_bodyfold_jmp L D C fn bb ps blockOps ps' front term target
      hentry hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hplan
  have hlift := instFoldF_regular_fold L D C fn bb (front.zipIdx 0) ps hreg
  rw [hbody] at hlift
  have hps_body : ps_body = _ := congrArg Prod.snd (Option.some.inj hlift)
  rw [← hps_body] at hnospill ⊢
  rw [hlayer4, himp hnospill]

/-- **Whole-function psOf for the entry block's tree successor.** Connects the head-visit recording to
    the actual `psOfFn` table: for the entry block (which heads the whole DFS's initial worklist), if its
    first successor `succ` is a tree edge, then `psOfFn succ = ps'`, the entry block's exit plan. The base
    case of the general-predecessor lift, realised on the real `psOfFn`/`blockEntryTable`. -/
theorem psOfFn_entry_succ (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat)
    (entryBB predBB : BasicBlock) (blockOps : List StackOp) (ps' : PlanState)
    (succ : String) (succRest : List String) (succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hentry : entryBlock fn = some entryBB)
    (hpfind : fn.blocks.find? (·.label == entryBB.label) = some predBB)
    (hbp : generateBlockPlan (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn predBB { initPlanState fnEom with labelCounter := lblCtr } = some (blockOps, ps'))
    (hsuccs : (cfgAnalyze fn).succsOf entryBB.label = succ :: succRest)
    (hsvisf : (entryBB.label :: ([] : List String)).contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hdfs : dfsEntriesAux (fuel + 3) (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entryBB.label] [] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some result) :
    psOfFn (fuel + 3) fn fnEom lblCtr succ = ps' := by
  have hrec := dfsEntriesAux_head_succ_records fuel (livenessAnalyzeFuel (fuel + 3) fn)
    (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn entryBB.label [] [] []
    { initPlanState fnEom with labelCounter := lblCtr } predBB blockOps ps' succ succRest succBB result
    (by simp) hpfind hbp hsuccs hsvisf hsfind hdfs
  unfold psOfFn blockEntryTable
  simp only [hentry, Option.map_some, hdfs, hrec, Option.getD_some]

/-- **psOfFn successor = entry-block body-fold output** (aligned JMP entry). Composes the real
    DFS-table lemma `psOfFn_entry_succ` (`psOfFn succ = ps'`, the entry block's `generateBlockPlan`
    exit state) with `bridge_foldOut_eq_psOf_jmp` (`ps' = body-fold output`, via the closed ① bridge) —
    the concrete layer-4 × bridge composition against the actual `psOfFn`/`blockEntryTable`, for an entry
    block that is an aligned JMP. This is the ③ assembly step that establishes the driver's per-block
    hypothesis `psOf successor = body-fold` on the *real* schedule (`psOf := psOfFn`), no longer taking
    `psSucc = ps'` as an abstract hypothesis; the four residuals `hstk/hsp/hfe/hno` are its projections. -/
theorem psOfFn_succ_eq_bodyfold_jmp
    (fuel fnEom lblCtr : Nat) (fn : IrFunction)
    (entryBB predBB : BasicBlock) (blockOps : List StackOp) (ps' : PlanState)
    (succ : String) (succRest : List String) (succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry : entryBlock fn = some entryBB)
    (hpfind : fn.blocks.find? (·.label == entryBB.label) = some predBB)
    (hbp : generateBlockPlan (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn predBB { initPlanState fnEom with labelCounter := lblCtr } = some (blockOps, ps'))
    (hsuccs : (cfgAnalyze fn).succsOf entryBB.label = succ :: succRest)
    (hsvisf : (entryBB.label :: ([] : List String)).contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hdfs : dfsEntriesAux (fuel + 3) (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entryBB.label] [] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some result)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel (fuel + 3) fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom predBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel (fuel + 3) fn) target 0) = [])
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ((front.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
          let nextLive := if x.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt (livenessAnalyzeFuel (fuel + 3) fn) predBB.label (x.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel (fuel + 3) fn) predBB.label predBB.instructions.length
          let nextIsTerm := if x.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[x.2 + 1]!.opcode else false
          let r := generateRegularInstPlan (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
            (cfgAnalyze fn) fn x.1 nextLive (bbIsHalting predBB) nextIsTerm predBB.label acc.2
          (acc.1 ++ r.1, r.2)) ([], { initPlanState fnEom with labelCounter := lblCtr })).2.spilled
          = ([] : AssocList Operand Nat)) :
    psOfFn (fuel + 3) fn fnEom lblCtr succ
      = ((front.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
          let nextLive := if x.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt (livenessAnalyzeFuel (fuel + 3) fn) predBB.label (x.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel (fuel + 3) fn) predBB.label predBB.instructions.length
          let nextIsTerm := if x.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[x.2 + 1]!.opcode else false
          let r := generateRegularInstPlan (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
            (cfgAnalyze fn) fn x.1 nextLive (bbIsHalting predBB) nextIsTerm predBB.label acc.2
          (acc.1 ++ r.1, r.2)) ([], { initPlanState fnEom with labelCounter := lblCtr })).2 := by
  have h4 := psOfFn_entry_succ fuel fn fnEom lblCtr entryBB predBB blockOps ps' succ succRest succBB
    result hentry hpfind hbp hsuccs hsvisf hsfind hdfs
  have hb := bridge_foldOut_eq_psOf_jmp (livenessAnalyzeFuel (fuel + 3) fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn predBB { initPlanState fnEom with labelCounter := lblCtr } blockOps ps' ps'
    front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hbp hreg rfl hnospill
  rw [h4, ← hb]


/-- **A subtree recording persists through the enclosing `dfsSuccsEntries` (general-lift step).** If the
    first successor's `[succ]` sub-call has already recorded `X ↦ e` (with `X` visited), then the whole
    `dfsSuccsEntries` output still records `X ↦ e`. `dfsEntries_table_mono` carries it past the remaining
    successors. This is the inductive step that lifts a recording made anywhere in the DFS subtree up one
    level toward the whole `psOfFn` table (in the actual DFS every worklist is a singleton, so the tree
    is traversed purely through `dfsSuccsEntries`). -/
theorem dfsSuccsEntries_lift_record (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (tbl : AssocList String PlanState) (psG : PlanState)
    (vAfter : List String) (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState) (X : String) (e : PlanState)
    (hga : dfsEntriesAux fuel L D C fn [succ] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } = some (vAfter, tblAfter, psAfter))
    (hrecX : AssocList.lookup String PlanState tblAfter X = some e)
    (hvisX : vAfter.contains X = true)
    (hsome : dfsSuccsEntries (fuel + 1) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG
      = some result) :
    AssocList.lookup String PlanState result.2.1 X = some e := by
  rw [dfsSuccsEntries_cons] at hsome
  simp only [hga] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vF tblF psF hgs =>
    obtain rfl := Option.some.inj hsome
    rw [(dfsEntries_table_mono L D C fn fuel).2 savedStack savedSpilled rest vAfter tblAfter
      { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) X hgs hvisX]
    exact hrecX

/-- Visited-companion of `dfsSuccsEntries_lift_record`: a label visited in the first successor's
    sub-call stays visited through the whole `dfsSuccsEntries` (so records + visited lift together, and
    the step composes up multiple DFS levels). -/
theorem dfsSuccsEntries_lift_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (tbl : AssocList String PlanState) (psG : PlanState)
    (vAfter : List String) (tblAfter : AssocList String PlanState) (psAfter : PlanState)
    (result : List String × AssocList String PlanState × PlanState) (X : String)
    (hga : dfsEntriesAux fuel L D C fn [succ] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } = some (vAfter, tblAfter, psAfter))
    (hvisX : vAfter.contains X = true)
    (hsome : dfsSuccsEntries (fuel + 1) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG
      = some result) :
    result.1.contains X = true := by
  rw [dfsSuccsEntries_cons] at hsome
  simp only [hga] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vF tblF psF hgs =>
    obtain rfl := Option.some.inj hsome
    exact (dfsEntries_visited_mono L D C fn fuel).2 savedStack savedSpilled rest vAfter tblAfter
      { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) X hgs hvisX


/-- **A successor's own tree-edge is recorded in the enclosing `dfsSuccsEntries` output.** When `pred`
    is the first successor processed by `dfsSuccsEntries` (unvisited) and `pred`'s own first successor
    `succ` is a tree edge, the `dfsSuccsEntries` output records `succ ↦ ps'` (`pred`'s exit). Composes
    `dfsEntriesAux_head_succ_records`/`_visited` on the `[pred]` sub-call with `dfsEntries_table_mono`
    over the remaining successors. This is the recursive shape of the general lift: every DFS node
    records the tree-edges of its subtree, and `dfsSuccsEntries` threads them to its output. -/
theorem dfsSuccsEntries_first_pred_succ_records (fuel : Nat) (L : DfState (List String))
    (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand)
    (savedSpilled : SpilledMap) (pred : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (psG : PlanState) (predBB : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (succ : String) (succRest : List String) (succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hpvisf : visited.contains pred = false)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hbp : generateBlockPlan L D C fn predBB { psG with stack := savedStack, spilled := savedSpilled }
      = some (blockOps, ps'))
    (hsuccs : C.succsOf pred = succ :: succRest)
    (hsvisf : (pred :: visited).contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsome : dfsSuccsEntries (fuel + 4) L D C fn savedStack savedSpilled (pred :: rest) visited tbl psG
      = some result) :
    AssocList.lookup String PlanState result.2.1 succ = some ps' := by
  rw [dfsSuccsEntries_cons] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vAfter tblAfter psAfter hga =>
    have hrec := dfsEntriesAux_head_succ_records fuel L D C fn pred [] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } predBB blockOps ps' succ succRest succBB
      (vAfter, tblAfter, psAfter) hpvisf hpfind hbp hsuccs hsvisf hsfind hga
    have hvis := dfsEntriesAux_head_succ_visited fuel L D C fn pred [] visited tbl
      { psG with stack := savedStack, spilled := savedSpilled } predBB blockOps ps' succ succRest succBB
      (vAfter, tblAfter, psAfter) hpvisf hpfind hbp hsuccs hsvisf hsfind hga
    split at hsome
    · exact absurd hsome (by simp)
    · next vF tblF psF hgs =>
      obtain rfl := Option.some.inj hsome
      rw [(dfsEntries_table_mono L D C fn (fuel + 3)).2 savedStack savedSpilled rest vAfter tblAfter
        { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) succ
        hgs hvis]
      exact hrec


/-- **CFG reachability** from `root` via `succsOf` — the induction variable for the whole-function
    `psOf` lift. `CfgReach C root lbl` means the DFS (which explores every successor of every visited
    block) reaches `lbl` starting from `root`; the general lift folds the recursive recording toolkit
    (`dfsSuccsEntries_first_pred_succ_records` etc.) along a `CfgReach` derivation. -/
inductive CfgReach (C : CfgAnalysis) (root : String) : String → Prop where
  | base : CfgReach C root root
  | step {pred succ : String} (hp : CfgReach C root pred) (hs : succ ∈ C.succsOf pred) :
      CfgReach C root succ

/-- Reachability composes: a path `root ⇝ a` extended by `a ⇝ b` is a path `root ⇝ b`. -/
theorem CfgReach_trans {C : CfgAnalysis} {root a b : String}
    (hra : CfgReach C root a) (hab : CfgReach C a b) : CfgReach C root b := by
  induction hab with
  | base => exact hra
  | step _ hs ih => exact CfgReach.step ih hs

/-- A direct successor of `root` is reachable (one step). -/
theorem CfgReach_succ {C : CfgAnalysis} {root succ : String} (hs : succ ∈ C.succsOf root) :
    CfgReach C root succ := CfgReach.step CfgReach.base hs

/-! ### The JNZ successor order is a THEOREM, not an assumption

`bbSuccs` is `(getSuccessors bb).reverse.dedup`, so a JNZ's CFG successors come out in the OPPOSITE
order to its label operands: the fall-through `ifZ` first, the taken target `ifNz` second. Getting this
backwards silently makes a `hpsucc` hypothesis unsatisfiable (and any residual discharged from it
vacuous), so it is derived here rather than assumed. -/

/-- The last instruction of `front ++ [term]`. -/
theorem getLast!_append_singleton (front : List Instruction) (term : Instruction) :
    (front ++ [term]).getLast! = term := by
  induction front with
  | nil => rfl
  | cons hd tl ih => cases tl <;> simpa using ih

/-- **A JNZ block's CFG successors are `[ifZ, ifNz]`** — fall-through FIRST, taken target SECOND. -/
theorem bbSuccs_jnz {bb : BasicBlock} {front : List Instruction} {term : Instruction}
    {c ifNz ifZ : String}
    (hbb : bb.instructions = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hne : ifZ ≠ ifNz) :
    bbSuccs bb = [ifZ, ifNz] := by
  have hlast : bb.instructions.getLast! = term := by
    rw [hbb]; exact getLast!_append_singleton front term
  unfold bbSuccs
  cases hi : bb.instructions with
  | nil => rw [hi] at hbb; exact absurd hbb.symm (by simp)
  | cons a l =>
    have hgl : (a :: l).getLast! = term := by rw [← hi]; exact hlast
    simp only []
    rw [hgl]
    simp [getSuccessors, hterm_jnz, hterm_ops, isTerminator, getLabel, hne]

/-- Inserts at other labels leave a key's entry alone. -/
theorem lookup_foldl_insert_of_not_mem (bbs : List BasicBlock) (m : AssocList String (List String))
    (k : String) (hk : k ∉ bbs.map (·.label)) :
    AssocList.lookup String (List String)
      (bbs.foldl (fun m b => AssocList.insert String (List String) m b.label (bbSuccs b)) m) k
      = AssocList.lookup String (List String) m k := by
  induction bbs generalizing m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, lookup_insert_ne _ _ _ _ (fun h => hk.1 h)]

/-- With distinct block labels, `buildSuccs` maps each block to its own `bbSuccs`. -/
theorem lookup_foldl_insert_of_mem :
    ∀ (bbs : List BasicBlock), (bbs.map (·.label)).Nodup →
    ∀ (bb : BasicBlock), bb ∈ bbs → ∀ (m : AssocList String (List String)),
    AssocList.lookup String (List String)
      (bbs.foldl (fun m b => AssocList.insert String (List String) m b.label (bbSuccs b)) m) bb.label
      = some (bbSuccs bb) := by
  intro bbs
  induction bbs with
  | nil => intro _ bb hmem; exact absurd hmem (by simp)
  | cons hd tl ih =>
    intro hnd bb hmem m
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [List.foldl_cons, lookup_foldl_insert_of_not_mem tl _ bb.label hnd.1, lookup_insert_self]
    · exact ih hnd.2 bb hmem' _

/-- `cfgAnalyze`'s successor query is exactly `bbSuccs` (given distinct block labels). -/
theorem cfgAnalyze_succsOf_of_mem {fn : IrFunction} {bb : BasicBlock}
    (hnd : (fn.blocks.map (·.label)).Nodup) (hmem : bb ∈ fn.blocks) :
    (cfgAnalyze fn).succsOf bb.label = bbSuccs bb := by
  unfold cfgAnalyze CfgAnalysis.succsOf fmapLookupList buildSuccs
  simp only []
  rw [lookup_foldl_insert_of_mem fn.blocks hnd bb hmem _]
  rfl

/-- **`hpsucc`, derived.** A JNZ block's CFG successors are `[ifZ, ifNz]` — the FALL-THROUGH first, the
    TAKEN target second. This is exactly the `hpsucc` shape the two JNZ canonical `hstep`s ask for, so
    callers never have to guess the order (guessing it wrong makes `hpsucc` unsatisfiable). -/
theorem cfgAnalyze_succsOf_jnz {fn : IrFunction} {bb : BasicBlock} {front : List Instruction}
    {term : Instruction} {c ifNz ifZ : String}
    (hnd : (fn.blocks.map (·.label)).Nodup) (hmem : bb ∈ fn.blocks)
    (hbb : bb.instructions = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hne : ifZ ≠ ifNz) :
    (cfgAnalyze fn).succsOf bb.label = [ifZ, ifNz] := by
  rw [cfgAnalyze_succsOf_of_mem hnd hmem, bbSuccs_jnz hbb hterm_jnz hterm_ops hne]

/-- **`hpsucc` for JMP, derived.** A JMP has a single label operand, so the `reverse` in `bbSuccs` is a
    no-op and the successor list is `[target]` — the JMP canonical `hstep`'s `hpsucc` (`= target :: succRest`)
    IS satisfiable (with `succRest = []`). Recorded explicitly because the JNZ sibling's `hpsucc` was not,
    which silently made its residual discharge vacuous. -/
theorem bbSuccs_jmp {bb : BasicBlock} {front : List Instruction} {term : Instruction} {target : String}
    (hbb : bb.instructions = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target]) :
    bbSuccs bb = [target] := by
  have hlast : bb.instructions.getLast! = term := by
    rw [hbb]; exact getLast!_append_singleton front term
  unfold bbSuccs
  cases hi : bb.instructions with
  | nil => rw [hi] at hbb; exact absurd hbb.symm (by simp)
  | cons a l =>
    have hgl : (a :: l).getLast! = term := by rw [← hi]; exact hlast
    simp only []
    rw [hgl]
    simp [getSuccessors, hterm_jmp, hterm_ops, isTerminator, getLabel]

theorem cfgAnalyze_succsOf_jmp {fn : IrFunction} {bb : BasicBlock} {front : List Instruction}
    {term : Instruction} {target : String}
    (hnd : (fn.blocks.map (·.label)).Nodup) (hmem : bb ∈ fn.blocks)
    (hbb : bb.instructions = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target]) :
    (cfgAnalyze fn).succsOf bb.label = [target] := by
  rw [cfgAnalyze_succsOf_of_mem hnd hmem, bbSuccs_jmp hbb hterm_jmp hterm_ops]

/-- **Everything reachable from `a` lies in any successor-closed set containing `a`.** -/
theorem CfgReach_mem_of_closed {C : CfgAnalysis} {a : String} {R : List String}
    (ha : a ∈ R) (hclosed : ∀ x ∈ R, ∀ y ∈ C.succsOf x, y ∈ R) :
    ∀ {z}, CfgReach C a z → z ∈ R := by
  intro z hz
  induction hz with
  | base => exact ha
  | step _ hs ih => exact hclosed _ ih _ hs

/-- **How to actually discharge a `¬ CfgReach` obligation** (e.g. the JNZ not-taken tree-edge
    condition `hnr`): exhibit a successor-closed over-approximation `R` of `a`'s reachable set that
    misses `b`. For a concrete CFG, `R` is a literal list and both side conditions are `by decide`. -/
theorem not_CfgReach_of_closed {C : CfgAnalysis} {a b : String} (R : List String)
    (ha : a ∈ R) (hclosed : ∀ x ∈ R, ∀ y ∈ C.succsOf x, y ∈ R) (hb : b ∉ R) :
    ¬ CfgReach C a b := fun h => hb (CfgReach_mem_of_closed ha hclosed h)

/-- Empty-worklist `dfsEntriesAux` is the identity. -/
theorem dfsEntriesAux_nil (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (visited : List String) (tbl : AssocList String PlanState) (ps : PlanState) :
    dfsEntriesAux fuel L D C fn [] visited tbl ps = some (visited, tbl, ps) := by
  cases fuel <;> rfl

/-- **A block is visited after its own `[s]` sub-call.** Whichever branch the visit takes — already
    visited (skip), found (visit), or not found (still added to `visited`) — `s` ends up in the output
    visited set. The per-successor step of `dfsSuccsEntries_visits_all`. -/
theorem dfsEntriesAux_head_in_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (s : String) (visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (hsome : dfsEntriesAux (fuel + 1) L D C fn [s] visited tbl ps = some result) :
    result.1.contains s = true := by
  by_cases hvis : visited.contains s
  · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis, dfsEntriesAux_nil] at hsome
    obtain rfl := Option.some.inj hsome; exact hvis
  · have hvisf : visited.contains s = false := by simp only [Bool.not_eq_true] at hvis; exact hvis
    cases hfind : fn.blocks.find? (·.label == s) with
    | none =>
      rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind, dfsEntriesAux_nil] at hsome
      obtain rfl := Option.some.inj hsome
      simp
    | some bb =>
      exact dfsEntriesAux_head_visited fuel L D C fn s [] visited tbl ps bb result hvisf hfind hsome

/-- **`dfsSuccsEntries` visits every successor.** Given enough fuel, each successor in the list ends up
    in the output visited set (its `[s]` sub-call visits it via `head_in_visited`, later successors
    preserve it via `visited_mono`). The engine of the DFS's visited-closure (a visited block's
    successors are all visited). -/
theorem dfsSuccsEntries_visits_all (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap) :
    ∀ (succs : List String) (fuel : Nat) (visited : List String) (tbl : AssocList String PlanState)
      (psG : PlanState) (result : List String × AssocList String PlanState × PlanState),
      succs.length < fuel →
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG = some result →
      ∀ s ∈ succs, result.1.contains s = true := by
  intro succs
  induction succs with
  | nil => intro fuel visited tbl psG result _ _ s hs; exact absurd hs (by simp)
  | cons s0 rest ih =>
    intro fuel visited tbl psG result hlen hsome s hs
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by simp only [List.length_cons] at hlen; omega⟩
    rw [dfsSuccsEntries_cons] at hsome
    split at hsome
    · exact absurd hsome (by simp)
    · next vAfter tblAfter psAfter hga =>
      split at hsome
      · exact absurd hsome (by simp)
      · next vF tblF psF hgs =>
        obtain rfl := Option.some.inj hsome
        rcases List.mem_cons.mp hs with rfl | hs'
        · have hs0 : vAfter.contains s = true :=
            dfsEntriesAux_head_in_visited f L D C fn s visited tbl
              { psG with stack := savedStack, spilled := savedSpilled } (vAfter, tblAfter, psAfter) hga
          exact (dfsEntries_visited_mono L D C fn (f + 1)).2 savedStack savedSpilled rest vAfter tblAfter
            { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) s
            hgs hs0
        · exact ih (f + 1) vAfter tblAfter
            { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF)
            (by simp only [List.length_cons] at hlen; omega) hgs s hs'


/-- **A head block's successors are all visited.** When a found block `X` heads the worklist
    (unvisited) with fuel exceeding its out-degree, every successor of `X` is in the output visited set:
    the visit runs `dfsSuccsEntries (C.succsOf X)` which visits them all (`dfsSuccsEntries_visits_all`),
    and the trailing empty-worklist call is the identity. The head-level case of the DFS visited-closure
    (a visited block's successors are visited) — the engine of reachability-completeness. -/
theorem dfsEntriesAux_head_succs_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (X : String) (visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (bb : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains X = false)
    (hfind : fn.blocks.find? (·.label == X) = some bb)
    (hbp : generateBlockPlan L D C fn bb ps = some (blockOps, ps'))
    (hfuel : (C.succsOf X).length < fuel)
    (hsome : dfsEntriesAux (fuel + 1) L D C fn [X] visited tbl ps = some result) :
    ∀ s ∈ C.succsOf X, result.1.contains s = true := by
  intro s hs
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
  simp only [hbp] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next visited'' tbl'' ps'' hgs =>
    rw [dfsEntriesAux_nil] at hsome
    obtain rfl := Option.some.inj hsome
    exact dfsSuccsEntries_visits_all L D C fn ps'.stack ps'.spilled (C.succsOf X) fuel (X :: visited)
      (AssocList.insert String PlanState tbl X ps) ps' (visited'', tbl'', ps'') hfuel hgs s hs


/-- **A first successor's own successors are visited (dfsSuccsEntries closure step).** When
    `dfsSuccsEntries` processes an unvisited found first successor `succ` (with fuel exceeding `succ`'s
    out-degree), all of `succ`'s successors end up visited in the output: the `[succ]` sub-call visits
    them (`dfsEntriesAux_head_succs_visited`) and the remaining successors preserve them
    (`dfsEntries_visited_mono`). The succs-side companion of `dfsEntriesAux_head_succs_visited`. -/
theorem dfsSuccsEntries_first_succ_succs_visited (fuel : Nat) (L : DfState (List String))
    (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand)
    (savedSpilled : SpilledMap) (succ : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (psG : PlanState) (bb : BasicBlock) (blockOps : List StackOp)
    (ps' : PlanState) (result : List String × AssocList String PlanState × PlanState)
    (hvisf : visited.contains succ = false)
    (hfind : fn.blocks.find? (·.label == succ) = some bb)
    (hbp : generateBlockPlan L D C fn bb { psG with stack := savedStack, spilled := savedSpilled }
      = some (blockOps, ps'))
    (hfuel : (C.succsOf succ).length < fuel)
    (hsome : dfsSuccsEntries (fuel + 2) L D C fn savedStack savedSpilled (succ :: rest) visited tbl psG
      = some result) :
    ∀ s ∈ C.succsOf succ, result.1.contains s = true := by
  intro s hs
  rw [dfsSuccsEntries_cons] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next vAfter tblAfter psAfter hga =>
    have hsv : vAfter.contains s = true :=
      dfsEntriesAux_head_succs_visited fuel L D C fn succ visited tbl
        { psG with stack := savedStack, spilled := savedSpilled } bb blockOps ps' (vAfter, tblAfter, psAfter)
        hvisf hfind hbp hfuel hga s hs
    split at hsome
    · exact absurd hsome (by simp)
    · next vF tblF psF hgs =>
      obtain rfl := Option.some.inj hsome
      exact (dfsEntries_visited_mono L D C fn (fuel + 1)).2 savedStack savedSpilled rest vAfter tblAfter
        { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } (vF, tblF, psF) s hgs hsv


/-- Number of `fn` blocks not yet visited — the decreasing measure for the fuel-vs-work accounting. -/
def numUnvisited (fn : IrFunction) (visited : List String) : Nat :=
  fn.blocks.countP (fun b => !visited.contains b.label)

/-- Growing `visited` (contains-wise) does not increase `numUnvisited`. -/
theorem numUnvisited_mono (fn : IrFunction) {visited visited' : List String}
    (h : ∀ l, visited.contains l = true → visited'.contains l = true) :
    numUnvisited fn visited' ≤ numUnvisited fn visited := by
  unfold numUnvisited
  apply List.countP_mono_left
  intro b _ hb'
  have hh := h b.label
  revert hb' hh
  cases visited.contains b.label <;> cases visited'.contains b.label <;> simp

theorem numUnvisited_cons_aux (bs : List BasicBlock) {X : String} {visited : List String}
    (hnd : (bs.map (·.label)).Nodup) (hmem : X ∈ bs.map (·.label))
    (hvisf : visited.contains X = false) :
    bs.countP (fun b => !(X :: visited).contains b.label)
      = bs.countP (fun b => !visited.contains b.label) - 1 := by
  induction bs with
  | nil => simp at hmem
  | cons b rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.mem_cons] at hmem
    rw [List.countP_cons, List.countP_cons]
    by_cases hbX : b.label = X
    · subst hbX
      have hrest : rest.countP (fun bb => !(b.label :: visited).contains bb.label)
          = rest.countP (fun bb => !visited.contains bb.label) := by
        apply List.countP_congr
        intro bb hbb
        have hne : bb.label ≠ b.label := fun hc => hnd.1 (hc ▸ List.mem_map_of_mem hbb)
        simp [hne]
      rw [hrest]
      have hnm : b.label ∉ visited := by simpa using hvisf
      simp [hnm]
    · have hbeq : (!(X :: visited).contains b.label) = (!visited.contains b.label) := by
        simp [hbX]
      rw [hbeq]
      have hmem' : X ∈ rest.map (·.label) := hmem.resolve_left (fun h => hbX h.symm)
      have hge : 0 < rest.countP (fun bb => !visited.contains bb.label) := by
        rw [List.countP_eq_length_filter]
        obtain ⟨bb, hbb, hbbl⟩ := List.mem_map.mp hmem'
        exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hbb, by simp only [hbbl]; rw [hvisf]; rfl⟩)
      rw [ih hnd.2 hmem']; omega

theorem numUnvisited_cons (fn : IrFunction) {X : String} {visited : List String}
    (hnd : (fn.blocks.map (·.label)).Nodup) (hmem : X ∈ fn.blocks.map (·.label))
    (hvisf : visited.contains X = false) :
    numUnvisited fn (X :: visited) = numUnvisited fn visited - 1 :=
  numUnvisited_cons_aux fn.blocks hnd hmem hvisf


/-- An unvisited found block makes `numUnvisited` positive. -/
theorem numUnvisited_pos (fn : IrFunction) {X : String} {visited : List String}
    (hmem : X ∈ fn.blocks.map (·.label)) (hvisf : visited.contains X = false) :
    0 < numUnvisited fn visited := by
  unfold numUnvisited
  rw [List.countP_eq_length_filter]
  obtain ⟨bb, hbb, hbbl⟩ := List.mem_map.mp hmem
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hbb, by simp only [hbbl]; rw [hvisf]; rfl⟩)

/-- `find? = none` means the label is absent from the blocks. -/
theorem label_not_mem_of_find_none (fn : IrFunction) {X : String}
    (hf : fn.blocks.find? (·.label == X) = none) : X ∉ fn.blocks.map (·.label) := by
  intro hmem
  obtain ⟨bb, hbb, hbbl⟩ := List.mem_map.mp hmem
  rw [List.find?_eq_none] at hf
  exact absurd (by simp [hbbl] : (·.label == X) bb = true) (by simpa using hf bb hbb)

set_option maxHeartbeats 2000000 in
/-- **Whole-DFS visited-closure.** With a max-out-degree bound `B` and unique block labels, once the
    fuel exceeds the work measure `(B+2)·numUnvisited`, every found block first-visited during the DFS
    has all its successors visited too. The fuel-vs-work accounting: the measure decreases at each first
    visit (`numUnvisited_cons`) and funds `head_succs_visited` (via `hB`) plus the sub-recursion. -/
theorem dfs_visited_closed (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (B : Nat) (hB : ∀ Z, (C.succsOf Z).length ≤ B)
    (hnd : (fn.blocks.map (·.label)).Nodup) :
    ∀ (fuel : Nat),
    (∀ (X : String) (visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (Y : String),
      (B + 2) * numUnvisited fn visited < fuel →
      dfsEntriesAux fuel L D C fn [X] visited tbl ps = some result →
      Y ∈ fn.blocks.map (·.label) → result.1.contains Y = true → visited.contains Y = false →
      ∀ s ∈ C.succsOf Y, result.1.contains s = true)
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (result : List String × AssocList String PlanState × PlanState) (Y : String),
      succs.length + (B + 2) * numUnvisited fn visited < fuel →
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG = some result →
      Y ∈ fn.blocks.map (·.label) → result.1.contains Y = true → visited.contains Y = false →
      ∀ s ∈ C.succsOf Y, result.1.contains s = true) := by
  intro fuel
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ _ hf => absurd hf (by omega), fun _ _ _ _ _ _ _ _ hf => absurd hf (by omega)⟩
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · -- P_aux [X]
      intro X visited tbl ps result Y hfuel hsome hYmem hYres hYvisf s hs
      by_cases hvisX : visited.contains X = true
      · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvisX, dfsEntriesAux_nil] at hsome
        obtain rfl := Option.some.inj hsome
        rw [hYvisf] at hYres; exact absurd hYres (by simp)
      · have hvisf : visited.contains X = false := by simp only [Bool.not_eq_true] at hvisX; exact hvisX
        cases hfind : fn.blocks.find? (·.label == X) with
        | none =>
          rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind, dfsEntriesAux_nil] at hsome
          obtain rfl := Option.some.inj hsome
          have hYX : Y = X := by
            have hmem2 : Y ∈ X :: visited := by simpa using hYres
            rcases List.mem_cons.mp hmem2 with h | h
            · exact h
            · exact absurd h (by simpa using hYvisf)
          exact absurd (hYX ▸ hYmem) (label_not_mem_of_find_none fn hfind)
        | some bb =>
          have hXmem : X ∈ fn.blocks.map (·.label) := by
            have hb := List.find?_some hfind
            have hbm := List.mem_of_find?_eq_some hfind
            exact List.mem_map.mpr ⟨bb, hbm, by simpa using hb⟩
          have hpos := numUnvisited_pos fn hXmem hvisf
          have hmul2 : (B + 2) * numUnvisited fn visited
              = (B + 2) * numUnvisited fn (X :: visited) + (B + 2) := by
            rw [numUnvisited_cons fn hnd hXmem hvisf]
            have hM1 : numUnvisited fn visited = (numUnvisited fn visited - 1) + 1 := by omega
            conv_lhs => rw [hM1]
            rw [Nat.mul_add, Nat.mul_one]
          obtain ⟨bo, ps', hbp⟩ : ∃ bo ps', generateBlockPlan L D C fn bb ps = some (bo, ps') := by
            rcases h : generateBlockPlan L D C fn bb ps with _ | ⟨bo, ps'⟩
            · rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind, h] at hsome
              exact absurd hsome (by simp)
            · exact ⟨bo, ps', rfl⟩
          rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
          simp only [hbp] at hsome
          split at hsome
          · exact absurd hsome (by simp)
          · next v'' t'' p'' hgs =>
            rw [dfsEntriesAux_nil] at hsome
            obtain rfl := Option.some.inj hsome
            by_cases hYX : Y = X
            · subst hYX
              exact dfsSuccsEntries_visits_all L D C fn ps'.stack ps'.spilled (C.succsOf Y) n
                (Y :: visited) (AssocList.insert String PlanState tbl Y ps) ps' (v'', t'', p'')
                (by have := hB Y; omega) hgs s hs
            · refine ihS ps'.stack ps'.spilled (C.succsOf X) (X :: visited)
                (AssocList.insert String PlanState tbl X ps) ps' (v'', t'', p'') Y ?_ hgs hYmem hYres ?_ s hs
              · have := hB X; omega
              · have hni : Y ∉ X :: visited := by
                  simp only [List.mem_cons, not_or]
                  exact ⟨hYX, by simpa using hYvisf⟩
                simpa using hni
    · -- P_succs
      intro savedStack savedSpilled succs visited tbl psG result Y hfuel hsome hYmem hYres hYvisf s hs
      cases succs with
      | nil =>
        rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome
        rw [hYvisf] at hYres; exact absurd hYres (by simp)
      | cons s0 rest =>
        rw [dfsSuccsEntries_cons] at hsome
        split at hsome
        · exact absurd hsome (by simp)
        · next vA tA pA hga =>
          split at hsome
          · exact absurd hsome (by simp)
          · next vF tF pF hgs =>
            obtain rfl := Option.some.inj hsome
            by_cases hYvA : vA.contains Y = true
            · -- Y first-visited in [s0]; closure in vA, lifted to result.1 = vF
              simp only [List.length_cons] at hfuel
              have hcl := ihA s0 visited tbl { psG with stack := savedStack, spilled := savedSpilled }
                (vA, tA, pA) Y (by omega) hga hYmem hYvA hYvisf s hs
              exact (dfsEntries_visited_mono L D C fn n).2 savedStack savedSpilled rest vA tA
                { psG with alloc := pA.alloc, labelCounter := pA.labelCounter } (vF, tF, pF) s hgs hcl
            · -- Y first-visited in rest
              simp only [List.length_cons] at hfuel
              have hle : numUnvisited fn vA ≤ numUnvisited fn visited :=
                numUnvisited_mono fn (fun l hl => (dfsEntries_visited_mono L D C fn n).1 [s0] visited tbl
                  { psG with stack := savedStack, spilled := savedSpilled } (vA, tA, pA) l hga hl)
              have hmulle : (B + 2) * numUnvisited fn vA ≤ (B + 2) * numUnvisited fn visited :=
                Nat.mul_le_mul_left _ hle
              refine ihS savedStack savedSpilled rest vA tA
                { psG with alloc := pA.alloc, labelCounter := pA.labelCounter } (vF, tF, pF) Y
                (by omega) hgs hYmem hYres ?_ s hs
              · simp only [Bool.not_eq_true] at hYvA; exact hYvA


theorem numUnvisited_nil (fn : IrFunction) : numUnvisited fn [] = fn.blocks.length := by
  unfold numUnvisited; simp

/-- Reachable blocks are found (given the entry is found and successors are found). -/
theorem CfgReach_found {C : CfgAnalysis} {fn : IrFunction} {entry pred : String}
    (hentry : entry ∈ fn.blocks.map (·.label))
    (hsf : ∀ Z s, s ∈ C.succsOf Z → s ∈ fn.blocks.map (·.label))
    (h : CfgReach C entry pred) : pred ∈ fn.blocks.map (·.label) := by
  induction h with
  | base => exact hentry
  | step _ hs _ => exact hsf _ _ hs

/-- **Reachability-completeness.** With sufficient fuel, the DFS visits every CFG-reachable block:
    the base (entry) is visited (`head_in_visited`), and the step lifts via the visited-closure
    (`dfs_visited_closed`: a visited block's successors are all visited). -/
theorem dfs_reaches_all (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (B : Nat) (hB : ∀ Z, (C.succsOf Z).length ≤ B)
    (hnd : (fn.blocks.map (·.label)).Nodup) {fuel : Nat} {entry : String} {ps : PlanState}
    {result : List String × AssocList String PlanState × PlanState}
    (hentry : entry ∈ fn.blocks.map (·.label))
    (hsf : ∀ Z s, s ∈ C.succsOf Z → s ∈ fn.blocks.map (·.label))
    (hfuel : (B + 2) * fn.blocks.length < fuel)
    (hsome : dfsEntriesAux fuel L D C fn [entry] [] [] ps = some result) :
    ∀ pred, CfgReach C entry pred → result.1.contains pred = true := by
  intro pred hreach
  induction hreach with
  | base =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact dfsEntriesAux_head_in_visited f L D C fn entry [] [] ps result hsome
  | step hp hs ih =>
    exact (dfs_visited_closed L D C fn B hB hnd fuel).1 entry [] [] ps result _
      (by rw [numUnvisited_nil]; exact hfuel) hsome (CfgReach_found hentry hsf hp) ih (by simp) _ hs


/-- **Visited blocks are recorded.** Every block in the DFS output visited-set has a table entry
    (the DFS inserts a label into the table exactly when it adds it to visited). A mutual induction
    preserving the invariant `visited ⊆ table-keys`. -/
theorem dfs_visited_recorded (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (result : List String × AssocList String PlanState × PlanState),
      (∀ Y, visited.contains Y = true → (AssocList.lookup String PlanState tbl Y).isSome = true) →
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some result →
      ∀ Y, result.1.contains Y = true → (AssocList.lookup String PlanState result.2.1 Y).isSome = true)
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (result : List String × AssocList String PlanState × PlanState),
      (∀ Y, visited.contains Y = true → (AssocList.lookup String PlanState tbl Y).isSome = true) →
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG = some result →
      ∀ Y, result.1.contains Y = true → (AssocList.lookup String PlanState result.2.1 Y).isSome = true) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result hinv hsome Y hY
      rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact hinv Y hY
    · intro ss sp succs visited tbl psG result hinv hsome Y hY
      rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact hinv Y hY
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps result hinv hsome Y hY
      cases worklist with
      | nil => rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact hinv Y hY
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl = true
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis] at hsome
          exact ihA rest visited tbl ps result hinv hsome Y hY
        · have hvisf : visited.contains lbl = false := by simp only [Bool.not_eq_true] at hvis; exact hvis
          have hinv' : ∀ Z, (lbl :: visited).contains Z = true →
              (AssocList.lookup String PlanState (AssocList.insert String PlanState tbl lbl ps) Z).isSome = true := by
            intro Z hZ
            by_cases hZlbl : Z = lbl
            · subst hZlbl; rw [assocLookup_insert_self]; rfl
            · rw [assocLookup_insert_ne tbl lbl Z ps hZlbl]
              apply hinv Z
              have hZm : Z ∈ lbl :: visited := by simpa using hZ
              rcases List.mem_cons.mp hZm with h | h
              · exact absurd h hZlbl
              · simpa using h
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            exact ihA rest (lbl :: visited) _ ps result hinv' hsome Y hY
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            split at hsome
            · exact absurd hsome (by simp)
            · next bo ps' _ =>
              split at hsome
              · exact absurd hsome (by simp)
              · next v'' t'' p'' hgs =>
                have hstep := ihS ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited)
                  (AssocList.insert String PlanState tbl lbl ps) ps' (v'', t'', p'') hinv' hgs
                exact ihA rest v'' t'' p'' result hstep hsome Y hY
    · intro ss sp succs visited tbl psG result hinv hsome Y hY
      cases succs with
      | nil => rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact hinv Y hY
      | cons s0 rest =>
        rw [dfsSuccsEntries_cons] at hsome
        split at hsome
        · exact absurd hsome (by simp)
        · next vA tA pA hga =>
          split at hsome
          · exact absurd hsome (by simp)
          · next vF tF pF hgs =>
            obtain rfl := Option.some.inj hsome
            have hstepA := ihA [s0] visited tbl { psG with stack := ss, spilled := sp } (vA, tA, pA) hinv hga
            exact ihS ss sp rest vA tA
              { psG with alloc := pA.alloc, labelCounter := pA.labelCounter } (vF, tF, pF) hstepA hgs Y hY

/-- **Reachable ⇒ recorded (recording fold core).** Combining `dfs_reaches_all` (the DFS visits every
    reachable block) with `dfs_visited_recorded` (visited ⇒ recorded): for a reachable block `Y`, the
    whole-DFS output table has an entry for `Y` — i.e. `psOfFn Y` is its recorded DFS entry plan, not
    the `default`. -/
theorem dfs_reachable_recorded (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (B : Nat) (hB : ∀ Z, (C.succsOf Z).length ≤ B)
    (hnd : (fn.blocks.map (·.label)).Nodup) {fuel : Nat} {entry : String} {ps : PlanState}
    {result : List String × AssocList String PlanState × PlanState}
    (hentry : entry ∈ fn.blocks.map (·.label))
    (hsf : ∀ Z s, s ∈ C.succsOf Z → s ∈ fn.blocks.map (·.label))
    (hfuel : (B + 2) * fn.blocks.length < fuel)
    (hsome : dfsEntriesAux fuel L D C fn [entry] [] [] ps = some result) :
    ∀ Y, CfgReach C entry Y → (AssocList.lookup String PlanState result.2.1 Y).isSome = true := by
  intro Y hreach
  have hvis := dfs_reaches_all L D C fn B hB hnd hentry hsf hfuel hsome Y hreach
  exact (dfs_visited_recorded L D C fn fuel).1 [entry] [] [] ps result
    (by intro Z hZ; simp at hZ) hsome Y hvis


/-- **Well-scheduled JMP block exits with the target's canonical entry stack.** When the JMP block's
    stack is already the target's expected layout `S = inputVarsFrom curBbLabel targetBb …` (the
    well-scheduling invariant `hsv`/`hsched`), its `generateRegularInstPlan` exit stack is exactly
    `targetStack.map Var` — the JMP is a no-op reorder and `releaseDeadSpills` leaves the stack. This is
    the block-plan side of the capstone `hplan`: pred's exit stack = the successor's canonical entry
    layout, matching the successor's DFS entry (`psOfFn`) on the stack. -/
theorem jmp_exit_stack_canonical
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock} {S : List String}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hsv : StackIsVars S ps)
    (hnd : S.Nodup)
    (hsched : S = inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack
      = (inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)).map Operand.Var := by
  rw [generateRegularInstPlan_jmp_eq_of_stackIsVars hjmp hops houts htgt hsv hnd hsched]
  show (releaseDeadSpills nextLiveness ps).stack = _
  rw [releaseDeadSpills_stack]
  rw [show ps.stack = S.map Operand.Var from hsv, hsched]


/-- **Entry block's recorded value.** The whole DFS from `[entry] [] []` records `entry ↦ ps` (its
    initial plan state) — the base value fact of the recording lift (`head_records` at the whole-DFS
    level). -/
theorem dfs_entry_recorded_value (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) {fuel : Nat} {entry : String} {ps : PlanState} {bb : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hfind : fn.blocks.find? (·.label == entry) = some bb)
    (hsome : dfsEntriesAux (fuel + 1) L D C fn [entry] [] [] ps = some result) :
    AssocList.lookup String PlanState result.2.1 entry = some ps :=
  dfsEntriesAux_head_records fuel L D C fn entry [] [] [] ps bb result (by simp) hfind hsome

/-- **General recorded value lifts from the first insertion.** For a reachable block `Y`, its
    whole-DFS recorded value equals the value it was first inserted with (recording persists via
    `dfs_visited_recorded` + `table_mono`) — packaged as: if the DFS output records `Y ↦ e` and `Y`
    stays visited, that `e` is `psOfFn Y`. The value characterisation for the capstone edge then
    follows by identifying `e` with the predecessor's exit (`records_tree_edge`) on a tree edge. -/
theorem psOfFn_of_recorded {result : List String × AssocList String PlanState × PlanState}
    {Y : String} {e : PlanState}
    (hrec : AssocList.lookup String PlanState result.2.1 Y = some e) :
    (AssocList.lookup String PlanState result.2.1 Y).getD default = e := by
  rw [hrec]; rfl


/-- **Two-step tree-edge value lift.** For the whole DFS from `[entry]`, along a length-2 DFS-tree path
    `entry → mid → succ` (both fresh tree edges), the output table records `succ ↦ mid's exit`. Composes
    the entry visit unfolding with `dfsSuccsEntries_first_pred_succ_records` applied to the entry's
    successor list (`mid` = entry's first successor). Demonstrates the recording value lift one level
    beyond the entry base case (`psOfFn_entry_succ`); the general depth is the analogous fold. -/
theorem dfs_two_step_records (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (fuel : Nat) (entry mid succ : String) (midRest succRest : List String)
    (ps psE psM : PlanState) (boE boM : List StackOp)
    (entryBB midBB succBB : BasicBlock)
    (result : List String × AssocList String PlanState × PlanState)
    (hEfind : fn.blocks.find? (·.label == entry) = some entryBB)
    (hEbp : generateBlockPlan L D C fn entryBB ps = some (boE, psE))
    (hEsuccs : C.succsOf entry = mid :: midRest)
    (hMfresh : ([entry] : List String).contains mid = false)
    (hMfind : fn.blocks.find? (·.label == mid) = some midBB)
    (hMbp : generateBlockPlan L D C fn midBB psE = some (boM, psM))
    (hMsuccs : C.succsOf mid = succ :: succRest)
    (hSfresh : (mid :: [entry]).contains succ = false)
    (hSfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsome : dfsEntriesAux (fuel + 5) L D C fn [entry] [] [] ps = some result) :
    AssocList.lookup String PlanState result.2.1 succ = some psM := by
  rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ (by simp) hEfind] at hsome
  simp only [hEbp] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · next v'' t'' p'' hgs =>
    rw [dfsEntriesAux_nil] at hsome
    obtain rfl := Option.some.inj hsome
    rw [hEsuccs] at hgs
    exact dfsSuccsEntries_first_pred_succ_records fuel L D C fn psE.stack psE.spilled mid midRest
      [entry] (AssocList.insert String PlanState ([] : AssocList String PlanState) entry ps) psE midBB
      boM psM succ succRest succBB (v'', t'', p'') hMfresh hMfind
      (by rw [planState_eta_stack_spilled psE]; exact hMbp) hMsuccs hSfresh hSfind hgs

/-- **psOfFn succ = mid's body-fold, for a depth-1 (mid) aligned-JMP block.** Composes
    `dfs_two_step_records` (records `succ ↦ psM`, mid's exit) with `generateBlockPlan_ps'_eq_bodyfold_jmp`
    (mid's exit = body-fold output). The depth-1 generalization of `psOfFn_succ_eq_bodyfold_jmp` — the
    successor-recording residual for a non-entry block one JMP step from the entry. -/
theorem psOfFn_succ_eq_bodyfold_jmp_mid
    (fuel fnEom lblCtr : Nat) (fn : IrFunction)
    (entryBB midBB succBB : BasicBlock) (mid succ : String) (midRest succRest : List String)
    (boE boM : List StackOp) (psE psM : PlanState)
    (result : List String × AssocList String PlanState × PlanState)
    (term : Instruction) (fr : List Instruction) (target : String)
    (hentryblk : entryBlock fn = some entryBB)
    (hEfind : fn.blocks.find? (·.label == entryBB.label) = some entryBB)
    (hEbp : generateBlockPlan (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn entryBB { initPlanState fnEom with labelCounter := lblCtr } = some (boE, psE))
    (hEsuccs : (cfgAnalyze fn).succsOf entryBB.label = mid :: midRest)
    (hMfresh : ([entryBB.label] : List String).contains mid = false)
    (hMfind : fn.blocks.find? (·.label == mid) = some midBB)
    (hMbp : generateBlockPlan (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn midBB psE = some (boM, psM))
    (hMsuccs : (cfgAnalyze fn).succsOf mid = succ :: succRest)
    (hSfresh : (mid :: [entryBB.label]).contains succ = false)
    (hSfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsome : dfsEntriesAux (fuel + 5) (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entryBB.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    -- mid is an aligned JMP block to target = succ
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel (fuel + 5) fn) (cfgAnalyze fn) fn midBB)
    (hnp : nonParamInsts midBB = fr ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom midBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel (fuel + 5) fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn midBB) (some ([], psE)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn midBB) (some ([], psE)) = some (bodyOps, ps_body) ∧
      psOfFn (fuel + 5) fn fnEom lblCtr succ = ps_body := by
  have hrec := dfs_two_step_records (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn fuel entryBB.label mid succ midRest succRest
    { initPlanState fnEom with labelCounter := lblCtr } psE psM boE boM entryBB midBB succBB result
    hEfind hEbp hEsuccs hMfresh hMfind hMbp hMsuccs hSfresh hSfind hsome
  have hpsof : psOfFn (fuel + 5) fn fnEom lblCtr succ = psM := by
    unfold psOfFn blockEntryTable
    simp only [hentryblk, Option.map_some, hsome, hrec, Option.getD_some]
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_ps'_eq_bodyfold_jmp (livenessAnalyzeFuel (fuel + 5) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn midBB psE boM psM fr term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs
      hjoin hMbp
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hpsof, himp (hnospill bodyOps ps_body hbody)]

/-! ### General JMP-chain recording — the `psOfFn` connection

`dfs_two_step_records` records a length-2 tree path; these generalize it to an arbitrary `JmpChainTo`
chain (the recording mirror of `generateFnPlanAux_chain_segment`), culminating in `psOfFn_chain`:
`generateBlockPlan tgtBB (psOfFn tgt) = (tgtBlockOps, tgtPs')`. This is what makes the derived
canonical `psOfFn` agree with the whole-function layout and `codegen_correct_sched`'s free `psOf`. -/

/-- **Single-successor recording lift (JMP-chain recording core).** For a fresh, found block `lbl` whose
    only CFG successor is `succ`: any block `X` recorded (and visited) in the `[succ]` sub-DFS (run from
    `lbl`'s exit `ps'`, table augmented with `lbl ↦ ps`) is still recorded with the same value, and still
    visited, in the whole `[lbl]` DFS output. The recording mirror of `generateFnPlanAux_single_succ_step`. -/
theorem dfsEntriesAux_single_succ_lift {fuel : Nat} {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {lbl succ : String} {visited : List String}
    {tbl : AssocList String PlanState} {ps : PlanState} {bb : BasicBlock} {block : List StackOp}
    {ps' : PlanState} {X : String} {e : PlanState}
    {resultSucc result : List String × AssocList String PlanState × PlanState}
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hsucc : C.succsOf lbl = [succ])
    (hblock : generateBlockPlan L D C fn bb ps = some (block, ps'))
    (hsub : dfsEntriesAux fuel L D C fn [succ] (lbl :: visited)
      (AssocList.insert String PlanState tbl lbl ps) ps' = some resultSucc)
    (hrecX : AssocList.lookup String PlanState resultSucc.2.1 X = some e)
    (hvisX : resultSucc.1.contains X = true)
    (htop : dfsEntriesAux (fuel + 2) L D C fn [lbl] visited tbl ps = some result) :
    AssocList.lookup String PlanState result.2.1 X = some e ∧ result.1.contains X = true := by
  rw [dfsEntriesAux_visit_block (fuel + 1) L D C fn lbl [] visited tbl ps bb hvis hfind] at htop
  simp only [hblock, hsucc] at htop
  rcases hgs : dfsSuccsEntries (fuel + 1) L D C fn ps'.stack ps'.spilled [succ] (lbl :: visited)
      (AssocList.insert String PlanState tbl lbl ps) ps' with _ | ⟨v'', t'', p''⟩
  · rw [hgs] at htop; simp at htop
  · simp only [hgs, dfsEntriesAux_nil] at htop
    obtain rfl := Option.some.inj htop
    have hga : dfsEntriesAux fuel L D C fn [succ] (lbl :: visited)
        (AssocList.insert String PlanState tbl lbl ps)
        { ps' with stack := ps'.stack, spilled := ps'.spilled } = some resultSucc := by
      rw [planState_eta_stack_spilled ps']; exact hsub
    refine ⟨?_, ?_⟩
    · exact dfsSuccsEntries_lift_record fuel L D C fn ps'.stack ps'.spilled succ [] (lbl :: visited)
        (AssocList.insert String PlanState tbl lbl ps) ps' resultSucc.1 resultSucc.2.1 resultSucc.2.2
        (v'', t'', p'') X e hga hrecX hvisX hgs
    · exact dfsSuccsEntries_lift_visited fuel L D C fn ps'.stack ps'.spilled succ [] (lbl :: visited)
        (AssocList.insert String PlanState tbl lbl ps) ps' resultSucc.1 resultSucc.2.1 resultSucc.2.2
        (v'', t'', p'') X hga hvisX hgs

/-- **`dfsEntriesAux`/`dfsSuccsEntries` totality** on a codegen-ready function (mirror of
    `generateFnPlanAux_generateSuccsPlan_isSome`; the only `none` is a `generateBlockPlan` failure,
    excluded by `generateBlockPlan_isSome`). -/
theorem dfsEntriesAux_dfsSuccsEntries_isSome (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (fuel : Nat),
      (∀ worklist visited tbl ps,
        (dfsEntriesAux fuel L D C fn worklist visited tbl ps).isSome) ∧
      (∀ ss sp succs visited tbl ps,
        (dfsSuccsEntries fuel L D C fn ss sp succs visited tbl ps).isSome) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun w v t p => ?_, fun ss sp su v t p => ?_⟩
    · simp only [dfsEntriesAux, Option.isSome_some]
    · simp only [dfsSuccsEntries, Option.isSome_some]
  | succ fuel ih =>
    obtain ⟨ihAux, ihSuccs⟩ := ih
    refine ⟨fun w v t p => ?_, fun ss sp su v t p => ?_⟩
    · cases w with
      | nil => simp only [dfsEntriesAux, Option.isSome_some]
      | cons lbl rest =>
        simp only [dfsEntriesAux]
        split
        · exact ihAux rest v t p
        · split
          · exact ihAux rest _ _ p
          · rename_i bb hfind
            have hbb : ∀ inst ∈ bb.instructions, codegenReadyInst inst :=
              hfn bb (List.mem_of_find?_eq_some hfind)
            obtain ⟨⟨bo, ps'⟩, hb⟩ := Option.isSome_iff_exists.mp
              (generateBlockPlan_isSome L D C fn bb p hbb)
            simp only [hb]
            obtain ⟨⟨v'', t'', p''⟩, hs⟩ := Option.isSome_iff_exists.mp
              (ihSuccs ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: v)
                (AssocList.insert String PlanState t lbl p) ps')
            simp only [hs]
            exact ihAux rest v'' t'' p''
    · cases su with
      | nil => simp only [dfsSuccsEntries, Option.isSome_some]
      | cons succ rest =>
        simp only [dfsSuccsEntries]
        obtain ⟨⟨v'', t'', p''⟩, ha⟩ := Option.isSome_iff_exists.mp
          (ihAux [succ] v t { p with stack := ss, spilled := sp })
        simp only [ha]
        obtain ⟨⟨vF, tF, pF⟩, hr⟩ := Option.isSome_iff_exists.mp
          (ihSuccs ss sp rest v'' t'' { p with alloc := p''.alloc, labelCounter := p''.labelCounter })
        simp only [hr, Option.isSome_some]

/-- **Chain records the target's entry plan state.** The recording mirror of
    `generateFnPlanAux_chain_segment`: along a `JmpChainTo` chain, the `dfsEntriesAux` output records
    `tgtLbl ↦ ps_tgt` where `ps_tgt` is the (threaded) plan state from which the target's block plan is
    generated — i.e. `generateBlockPlan tgtBB ps_tgt = (tgtBlockOps, tgtPs')`. Base = `head_records`;
    step = `single_succ_lift` over the recursive `dfsEntriesAux` totality. -/
theorem dfsEntriesAux_chain_records {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {tgtLbl : String} {tgtBlockOps : List StackOp} {tgtPs' : PlanState}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (path : List BasicBlock) (fuel : Nat) (visited : List String)
      (tbl : AssocList String PlanState) (ps : PlanState)
      (result : List String × AssocList String PlanState × PlanState),
      2 * path.length + 1 ≤ fuel →
      JmpChainTo L D C fn tgtLbl tgtBlockOps tgtPs' path visited ps →
      dfsEntriesAux fuel L D C fn [(path.head?.map (·.label)).getD tgtLbl] visited tbl ps = some result →
      ∃ ps_tgt tgtBB, fn.blocks.find? (·.label == tgtLbl) = some tgtBB ∧
        generateBlockPlan L D C fn tgtBB ps_tgt = some (tgtBlockOps, tgtPs') ∧
        AssocList.lookup String PlanState result.2.1 tgtLbl = some ps_tgt ∧
        result.1.contains tgtLbl = true := by
  intro path
  induction path with
  | nil =>
    intro fuel visited tbl ps result hfuel hchain htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, tgtBB, hfind, hbp⟩ := hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at htop
    refine ⟨ps, tgtBB, hfind, hbp, ?_, ?_⟩
    · exact dfsEntriesAux_head_records f L D C fn tgtLbl [] visited tbl ps tgtBB result hvis hfind htop
    · exact dfsEntriesAux_head_visited f L D C fn tgtLbl [] visited tbl ps tgtBB result hvis hfind htop
  | cons bb rest ih =>
    intro fuel visited tbl ps result hfuel hchain htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, hfind, hsucc, block, ps', hblock, hchain'⟩ := hchain
    obtain ⟨fr, rfl⟩ : ∃ fr, fuel = fr + 2 := ⟨fuel - 2, by simp only [List.length_cons] at hfuel; omega⟩
    have hfr : 2 * rest.length + 1 ≤ fr := by simp only [List.length_cons] at hfuel; omega
    obtain ⟨resultSucc, hsub⟩ := Option.isSome_iff_exists.mp
      ((dfsEntriesAux_dfsSuccsEntries_isSome L D C fn hfn fr).1
        [(rest.head?.map (·.label)).getD tgtLbl] (bb.label :: visited)
        (AssocList.insert String PlanState tbl bb.label ps) ps')
    obtain ⟨ps_tgt, tgtBB, hfindT, hbpT, hrec, hcontains⟩ :=
      ih fr (bb.label :: visited) (AssocList.insert String PlanState tbl bb.label ps) ps' resultSucc hfr hchain' hsub
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at htop
    obtain ⟨hrecR, hcontainsR⟩ :=
      dfsEntriesAux_single_succ_lift hvis hfind hsucc hblock hsub hrec hcontains htop
    exact ⟨ps_tgt, tgtBB, hfindT, hbpT, hrecR, hcontainsR⟩

/-- **General-depth successor-recording.** For a JMP chain from the DFS head to `pred`, with `pred`'s
    only successor a fresh `succ`, the whole-DFS output records `succ ↦ predPs'` (pred's exit) — the
    arbitrary-depth generalization of `dfs_two_step_records`. Inducts on the chain: base = `pred` at the
    head (`dfsEntriesAux_head_succ_records`/`_visited`), step = single-successor lift
    (`dfsEntriesAux_single_succ_lift`), mirroring `dfsEntriesAux_chain_records`. -/
theorem dfsEntriesAux_chain_succ_records {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (path : List BasicBlock) (fuel : Nat) (visited : List String)
      (tbl : AssocList String PlanState) (ps : PlanState)
      (result : List String × AssocList String PlanState × PlanState)
      (pred succ : String) (succBB : BasicBlock) (blockOps : List StackOp)
      (predPs' : PlanState) (succRest : List String),
      2 * path.length + 3 ≤ fuel →
      JmpChainTo L D C fn pred blockOps predPs' path visited ps →
      C.succsOf pred = succ :: succRest →
      fn.blocks.find? (·.label == succ) = some succBB →
      (∀ b ∈ path, b.label ≠ succ) → visited.contains succ = false → succ ≠ pred →
      dfsEntriesAux fuel L D C fn [(path.head?.map (·.label)).getD pred] visited tbl ps = some result →
      AssocList.lookup String PlanState result.2.1 succ = some predPs' ∧ result.1.contains succ = true := by
  intro path
  induction path with
  | nil =>
    intro fuel visited tbl ps result pred succ succBB blockOps predPs' succRest hfuel hchain
      hsuccs hsfind hsfresh hsvis hsne htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, predBB', hfindP, hbp⟩ := hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at htop
    have hsvisf : (pred :: visited).contains succ = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [hsne], hsvis⟩
    refine ⟨dfsEntriesAux_head_succ_records f L D C fn pred [] visited tbl ps predBB' blockOps predPs'
      succ succRest succBB result hvis hfindP hbp hsuccs hsvisf hsfind htop,
      dfsEntriesAux_head_succ_visited f L D C fn pred [] visited tbl ps predBB' blockOps predPs'
      succ succRest succBB result hvis hfindP hbp hsuccs hsvisf hsfind htop⟩
  | cons bb rest ih =>
    intro fuel visited tbl ps result pred succ succBB blockOps predPs' succRest hfuel hchain
      hsuccs hsfind hsfresh hsvis hsne htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvisBB, hfindBB, hsuccBB, block, ps'_bb, hblockBB, hchain'⟩ := hchain
    obtain ⟨fr, rfl⟩ : ∃ fr, fuel = fr + 2 := ⟨fuel - 2, by simp only [List.length_cons] at hfuel; omega⟩
    have hfr : 2 * rest.length + 3 ≤ fr := by simp only [List.length_cons] at hfuel; omega
    obtain ⟨resultSucc, hsub⟩ := Option.isSome_iff_exists.mp
      ((dfsEntriesAux_dfsSuccsEntries_isSome L D C fn hfn fr).1
        [(rest.head?.map (·.label)).getD pred] (bb.label :: visited)
        (AssocList.insert String PlanState tbl bb.label ps) ps'_bb)
    have hsvis' : (bb.label :: visited).contains succ = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [(hsfresh bb (List.mem_cons_self ..)).symm], hsvis⟩
    obtain ⟨hrecS, hvisS⟩ :=
      ih fr (bb.label :: visited) (AssocList.insert String PlanState tbl bb.label ps) ps'_bb resultSucc
        pred succ succBB blockOps predPs' succRest hfr hchain' hsuccs hsfind
        (fun b hb => hsfresh b (List.mem_cons_of_mem bb hb)) hsvis' hsne hsub
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at htop
    exact dfsEntriesAux_single_succ_lift hvisBB hfindBB hsuccBB hblockBB hsub hrecS hvisS htop

/-- **`JmpChainTo` ⇒ `psOfFn` (the canonical-`psOf` connection).** For a JMP chain whose head is the
    entry block, the canonical `psOfFn tgtLbl` is exactly the plan state from which the target's block
    plan is generated — so `generateBlockPlan tgtBB (psOfFn … tgtLbl) = (tgtBlockOps, tgtPs')`. This is
    what makes the whole-function layout (`generateFnPlanFuel_chain_segment`) and the budget-ranked
    scheduler (`codegen_correct_sched`, whose `psOf` is a free parameter) agree with the *derived*
    `psOfFn`: the per-block `hstep` reads `tgtBlockOps = generateBlockPlan tgt (psOfFn tgt)`. -/
theorem psOfFn_chain {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {tgtLbl : String} {tgtBlockOps : List StackOp} {tgtPs' : PlanState}
    {path : List BasicBlock}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD tgtLbl = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      tgtLbl tgtBlockOps tgtPs' path [] { initPlanState fnEom with labelCounter := lblCtr }) :
    ∃ tgtBB, fn.blocks.find? (·.label == tgtLbl) = some tgtBB ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn tgtBB
        (psOfFn fuel fn fnEom lblCtr tgtLbl) = some (tgtBlockOps, tgtPs') := by
  obtain ⟨⟨rv, rtbl, rps⟩, hdfs⟩ := Option.isSome_iff_exists.mp
    ((dfsEntriesAux_dfsSuccsEntries_isSome (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn hfn fuel).1 [entry.label] [] []
      { initPlanState fnEom with labelCounter := lblCtr })
  obtain ⟨ps_tgt, tgtBB, hfindT, hbpT, hrec, _⟩ :=
    dfsEntriesAux_chain_records hfn path fuel [] [] { initPlanState fnEom with labelCounter := lblCtr }
      (rv, rtbl, rps) hfuel hchain (by rw [hpathhead]; exact hdfs)
  have hpsof : psOfFn fuel fn fnEom lblCtr tgtLbl = ps_tgt := by
    unfold psOfFn blockEntryTable
    simp only [hentry, Option.map_some, hdfs, hrec, Option.getD_some]
  exact ⟨tgtBB, hfindT, by rw [hpsof]; exact hbpT⟩

/-- **Alloc-frame invariant** — `fnEom` preserved and `nextOffset` non-decreasing from `a` to `b`. Threaded
    by the codegen pipeline (spill slots only grow `nextOffset`, never touch `fnEom`); the property the JNZ
    not-taken residual needs (the second successor `ifZ` is DFS-recorded with `alloc` passed through the
    first successor `ifNz`'s subtree, so `hfe`/`hno` hold iff the DFS keeps `AllocInv`). -/
def AllocInv (a b : SpillAlloc) : Prop := b.fnEom = a.fnEom ∧ a.nextOffset ≤ b.nextOffset

theorem AllocInv.rfl' (a : SpillAlloc) : AllocInv a a := ⟨rfl, le_refl _⟩

theorem AllocInv.trans' {a b c : SpillAlloc} (h1 : AllocInv a b) (h2 : AllocInv b c) : AllocInv a c :=
  ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩

theorem allocSpillSlot_inv (alloc : SpillAlloc) : AllocInv alloc (allocSpillSlot alloc).2 :=
  ⟨allocSpillSlot_fnEom alloc, allocSpillSlot_nextOffset_ge alloc⟩

theorem freeSpillSlot_inv (off : Nat) (alloc : SpillAlloc) : AllocInv alloc (freeSpillSlot off alloc) :=
  ⟨rfl, le_refl _⟩

theorem doRestore_alloc_inv (op : Operand) (ps : PlanState) :
    AllocInv ps.alloc (doRestore op ps).2.alloc := by
  unfold doRestore; split
  · exact AllocInv.rfl' _
  · exact freeSpillSlot_inv _ _

/-- The `allocSpillSlot` spill-fold of `doDup`/`doSwap`'s bulk branch keeps `AllocInv` on the alloc. -/
theorem allocSpillFold_inv (items : List Operand) :
    ∀ (acc : List StackOp × List Nat × SpillAlloc),
    AllocInv acc.2.2 (items.foldl (fun (x : List StackOp × List Nat × SpillAlloc) (item : Operand) =>
        let (off, al') := allocSpillSlot x.2.2
        (x.1 ++ [StackOp.SOSpill off], x.2.1 ++ [off], al')) acc).2.2 := by
  induction items with
  | nil => intro acc; exact AllocInv.rfl' _
  | cons hd tl ih =>
    intro acc; exact AllocInv.trans' (allocSpillSlot_inv acc.2.2) (ih _)

/-- The `freeSpillSlot` fold keeps `AllocInv` on the alloc. -/
theorem freeSpillFold_inv (offs : List Nat) :
    ∀ (al : SpillAlloc), AllocInv al (offs.foldl (fun a off => freeSpillSlot off a) al) := by
  induction offs with
  | nil => intro al; exact AllocInv.rfl' _
  | cons hd tl ih => intro al; exact AllocInv.trans' (freeSpillSlot_inv hd al) (ih _)

theorem doDup_alloc_inv (dist : Nat) (ps : PlanState) : AllocInv ps.alloc (doDup dist ps).2.alloc := by
  unfold doDup; split
  · exact AllocInv.rfl' _
  · exact AllocInv.trans' (allocSpillFold_inv _ ([], [], ps.alloc)) (freeSpillFold_inv _ _)

theorem doSwap_alloc_inv (dist : Nat) (ps : PlanState) : AllocInv ps.alloc (doSwap dist ps).2.alloc := by
  unfold doSwap
  split
  · exact AllocInv.rfl' _
  · split
    · exact AllocInv.rfl' _
    · exact AllocInv.trans' (allocSpillFold_inv _ ([], [], ps.alloc)) (freeSpillFold_inv _ _)

theorem emitOneInput_alloc_inv (opc : Opcode) (nl : List String) (op : Operand) (ps : PlanState) :
    AllocInv ps.alloc (emitOneInput opc nl op ps).2.alloc := by
  unfold emitOneInput
  cases op <;>
    simp only [isVarOperand, Bool.true_and, Bool.false_and, if_false, Bool.and_false] <;>
    (repeat' split) <;>
    first
      | exact AllocInv.rfl' _
      | exact doRestore_alloc_inv _ _
      | exact doDup_alloc_inv _ _
      | exact AllocInv.trans' (doRestore_alloc_inv _ _) (doDup_alloc_inv _ _)

theorem reorderOne_alloc_inv (dfg : Unit) (targetOps : List Operand) (targetIdx : Nat) (op : Operand)
    (ps : PlanState) : AllocInv ps.alloc (reorderOne dfg targetOps targetIdx op ps).2.alloc := by
  unfold reorderOne
  simp only [] <;>
    (repeat' split) <;>
    first
      | exact AllocInv.rfl' _
      | exact doRestore_alloc_inv _ _
      | exact AllocInv.trans' (doSwap_alloc_inv _ _) (doSwap_alloc_inv _ _)
      | exact AllocInv.trans' (doRestore_alloc_inv _ _)
          (AllocInv.trans' (doSwap_alloc_inv _ _) (doSwap_alloc_inv _ _))

/-- A `List StackOp × PlanState`-threading fold whose step keeps `AllocInv` keeps it over the whole fold. -/
theorem foldl_pair_alloc_inv {α : Type} (l : List α)
    (f : List StackOp × PlanState → α → List StackOp × PlanState)
    (hf : ∀ acc x, AllocInv acc.2.alloc (f acc x).2.alloc) :
    ∀ (acc : List StackOp × PlanState), AllocInv acc.2.alloc (l.foldl f acc).2.alloc := by
  induction l with
  | nil => intro acc; exact AllocInv.rfl' _
  | cons hd tl ih => intro acc; exact AllocInv.trans' (hf acc hd) (ih _)

/-- A `PlanState`-threading fold whose step keeps `AllocInv` keeps it over the whole fold. -/
theorem foldl_ps_alloc_inv {α : Type} (l : List α) (f : PlanState → α → PlanState)
    (hf : ∀ ps x, AllocInv ps.alloc (f ps x).alloc) :
    ∀ (ps : PlanState), AllocInv ps.alloc (l.foldl f ps).alloc := by
  induction l with
  | nil => intro ps; exact AllocInv.rfl' _
  | cons hd tl ih => intro ps; exact AllocInv.trans' (hf ps hd) (ih _)

theorem emitInputPlan_alloc_inv (opc : Opcode) (ops : List Operand) (nl : List String) (ps : PlanState) :
    AllocInv ps.alloc (emitInputPlan opc ops nl ps).2.alloc := by
  unfold emitInputPlan
  apply foldl_pair_alloc_inv
  intro acc op
  exact emitOneInput_alloc_inv opc nl op acc.2

theorem reorderPlan_alloc_inv (targetOps : List Operand) (ps : PlanState) :
    AllocInv ps.alloc (reorderPlan targetOps ps).2.alloc := by
  unfold reorderPlan
  apply foldl_pair_alloc_inv
  intro acc x
  exact reorderOne_alloc_inv () targetOps x.1 x.2 acc.2

theorem releaseDeadSpills_alloc_inv (nl : List String) (ps : PlanState) :
    AllocInv ps.alloc (releaseDeadSpills nl ps).alloc := by
  unfold releaseDeadSpills
  refine foldl_ps_alloc_inv ps.spilled _ (fun ps' x => ?_) ps
  rcases x with ⟨op, off⟩
  cases op <;> (repeat' split) <;> first | exact AllocInv.rfl' _ | exact freeSpillSlot_inv _ _

/-- `djmpChain` only mints `freshLabel`s (labelCounter), never touches the spill allocator. -/
theorem djmpChain_alloc_inv (i : Nat) (labels : List String) (ps : PlanState) :
    AllocInv ps.alloc (djmpChain i labels ps).2.2.alloc := by
  induction labels generalizing i ps with
  | nil => exact AllocInv.rfl' _
  | cons hd tl ih =>
    exact AllocInv.trans' (AllocInv.rfl' _) (ih (i + 1) _)

theorem generateDjmpPlan_alloc_inv (labels : List String) (ps : PlanState) :
    AllocInv ps.alloc (generateDjmpPlan labels ps).2.alloc := by
  unfold generateDjmpPlan
  exact djmpChain_alloc_inv 0 labels ps

/-- `generateEmitOps` only emits opcodes and (INVOKE/ASSERT_UNREACHABLE/DJMP) mints labels;
    the spill allocator is untouched. -/
theorem generateEmitOps_alloc_inv (inst : Instruction) (n : Nat) (ps : PlanState) :
    AllocInv ps.alloc (generateEmitOps inst n ps).2.alloc := by
  unfold generateEmitOps
  simp only []
  (repeat' split) <;>
    first
    | exact AllocInv.rfl' _
    | exact generateDjmpPlan_alloc_inv _ _

theorem popmanyPlan_alloc_inv (toPop : List Operand) (ps : PlanState) :
    AllocInv ps.alloc (popmanyPlan toPop ps).2.alloc := by
  unfold popmanyPlan
  simp only []
  (repeat' split) <;>
    first
    | exact AllocInv.rfl' _
    | exact doSwap_alloc_inv _ _
    | (apply foldl_pair_alloc_inv
       intro acc v
       obtain ⟨accOps, accPs⟩ := acc
       simp only []
       (repeat' split) <;>
         first
         | exact AllocInv.rfl' _
         | exact doSwap_alloc_inv _ _)

theorem optimisticSwapPlan_alloc_inv (dfg : DfgAnalysis) (inst : Instruction)
    (nextLiveness : List String) (nextIsTerminator : Bool) (ps : PlanState) :
    AllocInv ps.alloc
      (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator ps).2.alloc := by
  unfold optimisticSwapPlan
  simp only []
  (repeat' split) <;> first | exact AllocInv.rfl' _ | exact doSwap_alloc_inv _ _

/-- The "push outputs" fold only rewrites the stack, so it leaves the spill allocator fixed. -/
theorem outputsPush_foldl_alloc (outs : List String) (ps : PlanState) :
    (outs.foldl (fun ps' out => { ps' with stack := stackPush (Operand.Var out) ps'.stack }) ps).alloc
      = ps.alloc := by
  induction outs generalizing ps with
  | nil => rfl
  | cons hd tl ih => rw [List.foldl_cons, ih]

/-- The whole per-instruction plan generator advances the spill allocator monotonically
    (`fnEom` fixed, `nextOffset` non-decreasing). Composes the emit/reorder/release/emit-ops/
    popmany/optswap leaves. The shared prefix `ps ⟶ ps7` (input ops → join reorder → commutative
    → final reorder → stack pop/push → EVM emission) is common to both post-processing branches. -/
theorem generateRegularInstPlan_alloc_inv
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (_cfg : CfgAnalysis)
    (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState) :
    AllocInv ps.alloc
      (generateRegularInstPlan liveness dfg _cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).2.alloc := by
  unfold generateRegularInstPlan
  simp only []
  split
  · -- outputs empty: post = releaseDeadSpills nextLiveness ps7
    refine AllocInv.trans' ?_ (releaseDeadSpills_alloc_inv _ _)
    refine AllocInv.trans' ?_ (generateEmitOps_alloc_inv _ _ _)
    rw [outputsPush_foldl_alloc]
    refine AllocInv.trans' ?_ (reorderPlan_alloc_inv _ _)
    (repeat' split) <;>
      first
      | exact emitInputPlan_alloc_inv _ _ _ _
      | exact AllocInv.trans' (emitInputPlan_alloc_inv _ _ _ _) (reorderPlan_alloc_inv _ _)
  · -- outputs non-empty: post = releaseDeadSpills nextLiveness ps9, ps9 ⟵ ps8 ⟵ ps7
    refine AllocInv.trans' ?_ (releaseDeadSpills_alloc_inv _ _)
    split <;> (try refine AllocInv.trans' ?_ (optimisticSwapPlan_alloc_inv _ _ _ _ _))
    all_goals (split <;> (try refine AllocInv.trans' ?_ (popmanyPlan_alloc_inv _ _)))
    all_goals
      refine AllocInv.trans' ?_ (generateEmitOps_alloc_inv _ _ _)
      rw [outputsPush_foldl_alloc]
      refine AllocInv.trans' ?_ (reorderPlan_alloc_inv _ _)
      (repeat' split) <;>
        first
        | exact emitInputPlan_alloc_inv _ _ _ _
        | exact AllocInv.trans' (emitInputPlan_alloc_inv _ _ _ _) (reorderPlan_alloc_inv _ _)

/-- The phi plan either dups a live value or pokes the return var into place — stack only. -/
theorem generatePhiPlan_alloc_inv (inst : Instruction) (nextLiveness : List String)
    (ps : PlanState) : AllocInv ps.alloc (generatePhiPlan inst nextLiveness ps).2.alloc := by
  unfold generatePhiPlan
  simp only []
  (repeat' split) <;> first | exact AllocInv.rfl' _ | exact doDup_alloc_inv _ _

/-- The offset plan just pushes `label + offset` — stack only. -/
theorem generateOffsetPlan_alloc_inv (inst : Instruction) (ps : PlanState) :
    AllocInv ps.alloc (generateOffsetPlan inst ps).2.alloc := by
  unfold generateOffsetPlan
  simp only []
  (repeat' split) <;> exact AllocInv.rfl' _

/-- The entry-block param push fold only rewrites the stack, so it leaves the allocator fixed. -/
theorem paramsPush_foldl_alloc (params : List Instruction) (ps : PlanState) :
    (params.foldl
      (fun ps' inst => { ps' with stack := stackPush (Operand.Var inst.outputs.head!) ps'.stack })
      ps).alloc = ps.alloc := by
  induction params generalizing ps with
  | nil => rfl
  | cons hd tl ih => rw [List.foldl_cons, ih]

theorem prepareParamsPlan_alloc_inv (liveness : DfState (List String)) (fn : IrFunction)
    (ps : PlanState) : AllocInv ps.alloc (prepareParamsPlan liveness fn ps).2.alloc := by
  unfold prepareParamsPlan
  split
  · exact AllocInv.rfl' _
  · simp only []
    split
    · exact AllocInv.rfl' _
    · refine AllocInv.trans' ?_ (optimisticSwapPlan_alloc_inv _ _ _ _ _)
      refine AllocInv.trans' ?_ (popmanyPlan_alloc_inv _ _)
      rw [paramsPush_foldl_alloc]
      exact AllocInv.rfl' _

theorem cleanStackPlan_alloc_inv (liveness : DfState (List String)) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) :
    AllocInv ps.alloc (cleanStackPlan liveness cfg fn bb ps).2.alloc := by
  unfold cleanStackPlan
  simp only []
  (repeat' split) <;> first | exact AllocInv.rfl' _ | exact popmanyPlan_alloc_inv _ _

/-- The per-instruction dispatch: whenever it commits to a plan (`some`), the allocator advanced. -/
theorem generateInstPlan_alloc_inv (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    {ops : List StackOp} {ps' : PlanState}
    (h : generateInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
      curBbLabel ps = some (ops, ps')) :
    AllocInv ps.alloc ps'.alloc := by
  unfold generateInstPlan at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
      exact generatePhiPlan_alloc_inv _ _ _
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
          exact generateOffsetPlan_alloc_inv _ _
        · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
          exact generateRegularInstPlan_alloc_inv _ _ _ _ _ _ _ _ _ _
      · split at h
        · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
          exact AllocInv.rfl' _
        · split at h
          · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
            exact AllocInv.rfl' _
          · simp only [Option.some.injEq, Prod.ext_iff] at h; obtain ⟨_, rfl⟩ := h
            exact generateRegularInstPlan_alloc_inv _ _ _ _ _ _ _ _ _ _

/-- Generic `foldl` invariant: a property preserved by each step holds at the end. -/
theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β) (l : List α) (b : β)
    (hb : P b) (hf : ∀ acc x, P acc → P (f acc x)) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons hd tl ih => exact ih (f b hd) (hf b hd hb)

/-- The whole block plan advances the allocator: `JUMPDEST` + params + clean-stack + the folded
    per-instruction plans, each of which is allocator-monotone. -/
theorem generateBlockPlan_alloc_inv (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (ps : PlanState)
    {ops : List StackOp} {ps3 : PlanState}
    (h : generateBlockPlan liveness dfg cfg fn bb ps = some (ops, ps3)) :
    AllocInv ps.alloc ps3.alloc := by
  unfold generateBlockPlan at h
  simp only [] at h
  -- Name the param/clean-prefix states and their invariants.
  set ps1 := (if (fn.blocks.head?.map (·.label)) == some bb.label then
      prepareParamsPlan liveness fn ps else ([], ps)).2 with hps1
  have hpre1 : AllocInv ps.alloc ps1.alloc := by
    rw [hps1]; split
    · exact prepareParamsPlan_alloc_inv _ _ _
    · exact AllocInv.rfl' _
  set ps2 := (if (cfg.predsOf bb.label).length = 1 then
      cleanStackPlan liveness cfg fn bb ps1 else ([], ps1)).2 with hps2
  have hpre2 : AllocInv ps1.alloc ps2.alloc := by
    rw [hps2]; split
    · exact cleanStackPlan_alloc_inv _ _ _ _ _
    · exact AllocInv.rfl' _
  -- The instruction fold preserves `AllocInv ps2.alloc _` on the `some` component.
  have hfold : ∀ (o : Option (List StackOp × PlanState)),
      (∀ oo pp, o = some (oo, pp) → AllocInv ps2.alloc pp.alloc) → ∀ oo3 pp3,
      ((nonParamInsts bb).zipIdx.foldl
        (fun (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat) =>
          match acc with
          | none => none
          | some (ops, ps) =>
            let (inst, i) := instI
            let nextLive :=
              if i + 1 < (nonParamInsts bb).length then
                liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
              else liveVarsAt liveness bb.label bb.instructions.length
            let nextIsTerm :=
              if i + 1 < (nonParamInsts bb).length then
                isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
            match generateInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb) nextIsTerm
                bb.label ps with
            | none => none
            | some (stepOps, ps') => some (ops ++ stepOps, ps'))
        o) = some (oo3, pp3) → AllocInv ps2.alloc pp3.alloc := by
    intro o hinit
    refine foldl_invariant
      (fun acc => ∀ oo pp, acc = some (oo, pp) → AllocInv ps2.alloc pp.alloc) _ _ o hinit ?_
    intro acc instI hacc oo pp hstep
    cases acc with
    | none => exact absurd hstep (by simp)
    | some aval =>
      obtain ⟨aops, aps⟩ := aval
      obtain ⟨inst, i⟩ := instI
      have hai : AllocInv ps2.alloc aps.alloc := hacc aops aps rfl
      simp only [] at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · rename_i stepOps aps' hgen
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨_, rfl⟩ := hstep
        exact AllocInv.trans' hai (generateInstPlan_alloc_inv _ _ _ _ _ _ _ _ _ _ hgen)
  -- Peel the final `match result`.
  split at h
  · exact absurd h (by simp)
  · rename_i instOps ps3' hres
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact AllocInv.trans' hpre1 (AllocInv.trans' hpre2 (hfold _ (by
      intro oo pp hoo; simp only [Option.some.injEq, Prod.mk.injEq] at hoo
      obtain ⟨_, rfl⟩ := hoo; exact AllocInv.rfl' _) _ _ hres))

/-- **The entry-state DFS is allocator-monotone.** Both `dfsEntriesAux` and `dfsSuccsEntries` thread the
    spill allocator forward: `fnEom` stays fixed and `nextOffset` never decreases. Proven by the same
    combined `induction fuel` mutual structure as `dfsEntries_faithful`, using `generateBlockPlan_alloc_inv`
    at each visited block and chaining across the successor recursion. The key line is `dfsSuccsEntries`'s
    `psG' := { psG with alloc := psAfter.alloc, … }`: the second successor's recorded entry carries the
    allocator threaded through the first successor's whole subtree — exactly the monotonicity the JNZ
    not-taken join obligation (`hfe`/`hno`) needs. -/
theorem dfsEntries_alloc_inv (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (v : List String) (t : AssocList String PlanState) (ps'' : PlanState),
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some (v, t, ps'') →
      AllocInv ps.alloc ps''.alloc)
    ∧
    (∀ (ss : List Operand) (sp : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (v : List String) (t : AssocList String PlanState) (psF : PlanState),
      dfsSuccsEntries fuel L D C fn ss sp succs visited tbl psG = some (v, t, psF) →
      AllocInv psG.alloc psF.alloc) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited tbl ps v t ps'' hEq => ?_,
            fun ss sp succs visited tbl psG v t psF hEq => ?_⟩
    · simp only [dfsEntriesAux, Option.some.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, _, rfl⟩ := hEq; exact AllocInv.rfl' _
    · simp only [dfsSuccsEntries, Option.some.injEq, Prod.mk.injEq] at hEq
      obtain ⟨_, _, rfl⟩ := hEq; exact AllocInv.rfl' _
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨fun worklist visited tbl ps v t ps'' hEq => ?_,
            fun ss sp succs visited tbl psG v t psF hEq => ?_⟩
    · cases worklist with
      | nil =>
        simp only [dfsEntriesAux, Option.some.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, _, rfl⟩ := hEq; exact AllocInv.rfl' _
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis] at hEq
          exact ihA _ _ _ _ _ _ _ hEq
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hEq
            exact ihA _ _ _ _ _ _ _ hEq
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hEq
            split at hEq
            · exact absurd hEq (by simp)
            · rename_i blockOps ps' hbp
              have hA : AllocInv ps.alloc ps'.alloc := generateBlockPlan_alloc_inv _ _ _ _ _ _ hbp
              split at hEq
              · exact absurd hEq (by simp)
              · rename_i v2 t2 ps2 hds
                have hB : AllocInv ps'.alloc ps2.alloc := ihS _ _ _ _ _ _ _ _ _ hds
                exact AllocInv.trans' hA (AllocInv.trans' hB (ihA _ _ _ _ _ _ _ hEq))
    · cases succs with
      | nil =>
        simp only [dfsSuccsEntries, Option.some.injEq, Prod.mk.injEq] at hEq
        obtain ⟨_, _, rfl⟩ := hEq; exact AllocInv.rfl' _
      | cons succ rest =>
        rw [dfsSuccsEntries] at hEq
        split at hEq
        · exact absurd hEq (by simp)
        · rename_i vAfter tblAfter psAfter hda
          have hA := ihA _ _ _ _ _ _ _ hda
          simp only [] at hEq
          split at hEq
          · exact absurd hEq (by simp)
          · rename_i vF tblF psFF hds
            have hB := ihS _ _ _ _ _ _ _ _ _ hds
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            obtain ⟨_, _, rfl⟩ := hEq
            exact AllocInv.trans' hA hB

/-- **The entry-state DFS only ever visits reachable labels.** Everything in the output visited-set was
    either already visited, or is `CfgReach`-reachable from some label on the worklist (resp. from some
    successor, for `dfsSuccsEntries`). Same combined `induction fuel` as `dfsEntries_alloc_inv`. This is
    what turns the JNZ tree-edge side condition from an assumption about a DFS *run* into a plain CFG
    fact (`¬ CfgReach C ifNz ifZ`) — see `dfsEntriesAux_not_reach_fresh`. -/
theorem dfsEntries_visited_reach (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (r : List String × AssocList String PlanState × PlanState),
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some r →
      ∀ l, r.1.contains l = true →
        visited.contains l = true ∨ ∃ w ∈ worklist, CfgReach C w l)
    ∧
    (∀ (ss : List Operand) (sp : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (r : List String × AssocList String PlanState × PlanState),
      dfsSuccsEntries fuel L D C fn ss sp succs visited tbl psG = some r →
      ∀ l, r.1.contains l = true →
        visited.contains l = true ∨ ∃ w ∈ succs, CfgReach C w l) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited tbl ps r hsome l hl => ?_,
            fun ss sp succs visited tbl psG r hsome l hl => ?_⟩
    · rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact Or.inl hl
    · rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact Or.inl hl
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨fun worklist visited tbl ps r hsome l hl => ?_,
            fun ss sp succs visited tbl psG r hsome l hl => ?_⟩
    · cases worklist with
      | nil => rw [dfsEntriesAux] at hsome; obtain rfl := Option.some.inj hsome; exact Or.inl hl
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis] at hsome
          rcases ihA rest visited tbl ps r hsome l hl with h | ⟨w, hw, hr⟩
          · exact Or.inl h
          · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hr⟩
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            rcases ihA rest (lbl :: visited) _ ps r hsome l hl with h | ⟨w, hw, hr⟩
            · rcases (by simpa [List.contains_cons] using h : l = lbl ∨ visited.contains l = true) with
                rfl | h'
              · exact Or.inr ⟨l, List.mem_cons_self .., CfgReach.base⟩
              · exact Or.inl h'
            · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hr⟩
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind] at hsome
            split at hsome
            · exact absurd hsome (by simp)
            · next blockOps ps' _ =>
              split at hsome
              · exact absurd hsome (by simp)
              · next v2 t2 ps2 hgs =>
                rcases ihA rest v2 t2 ps2 r hsome l hl with h2 | ⟨w, hw, hr⟩
                · rcases ihS ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited) _ ps'
                    (v2, t2, ps2) hgs l h2 with h3 | ⟨w, hw, hr⟩
                  · rcases (by simpa [List.contains_cons] using h3 :
                      l = lbl ∨ visited.contains l = true) with rfl | h'
                    · exact Or.inr ⟨l, List.mem_cons_self .., CfgReach.base⟩
                    · exact Or.inl h'
                  · exact Or.inr ⟨lbl, List.mem_cons_self .., CfgReach_trans (CfgReach_succ hw) hr⟩
                · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hr⟩
    · cases succs with
      | nil => rw [dfsSuccsEntries] at hsome; obtain rfl := Option.some.inj hsome; exact Or.inl hl
      | cons succ rest =>
        rw [dfsSuccsEntries_cons] at hsome
        split at hsome
        · exact absurd hsome (by simp)
        · next vAfter tblAfter psAfter hga =>
          split at hsome
          · exact absurd hsome (by simp)
          · next vF tblF psF hgs =>
            obtain rfl := Option.some.inj hsome
            rcases ihS ss sp rest vAfter tblAfter _ (vF, tblF, psF) hgs l hl with h | ⟨w, hw, hr⟩
            · rcases ihA [succ] visited tbl _ (vAfter, tblAfter, psAfter) hga l h with h2 | ⟨w, hw, hr⟩
              · exact Or.inl h2
              · simp only [List.mem_singleton] at hw
                subst hw
                exact Or.inr ⟨w, List.mem_cons_self .., hr⟩
            · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hr⟩

/-- **The JNZ tree-edge condition from a plain CFG fact.** If `succ2` is not CFG-reachable from `succ1`
    and is not already visited, then `succ1`'s whole DFS subtree never discovers it. This discharges the
    `hfresh2` side condition of the second-successor recording. -/
theorem dfsEntriesAux_not_reach_fresh (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (f : Nat) (succ1 succ2 : String) (vis : List String)
    (tb : AssocList String PlanState) (ps : PlanState)
    (r : List String × AssocList String PlanState × PlanState)
    (hnr : ¬ CfgReach C succ1 succ2)
    (hvis : vis.contains succ2 = false)
    (hsome : dfsEntriesAux f L D C fn [succ1] vis tb ps = some r) :
    r.1.contains succ2 = false := by
  cases hc : r.1.contains succ2 with
  | false => rfl
  | true =>
    rcases (dfsEntries_visited_reach L D C fn f).1 [succ1] vis tb ps r hsome succ2 hc with h | ⟨w, hw, hr⟩
    · rw [hvis] at h; exact absurd h (by simp)
    · simp only [List.mem_singleton] at hw
      subst hw
      exact absurd hr hnr

/-- **General-depth SECOND-successor recording (the JNZ not-taken shape).** For a JMP chain from the DFS
    head to `pred`, whose successors are `succ1 :: succ2 :: succRest`, the whole-DFS output records
    `succ2` at `pred`'s exit stack/spilled with the allocator threaded through `succ1`'s subtree. Unlike
    the first successor (whose entry is `predPs'` exactly), `succ2`'s entry agrees with `predPs'` only on
    stack/spilled — its allocator is `psAfter`'s, related to `predPs'`'s by `AllocInv` (fnEom fixed,
    nextOffset non-decreasing) via `dfsEntries_alloc_inv`. That is precisely the shape of the JNZ
    not-taken join obligation (`hstk`/`hsp` equalities, `hfe`/`hno` allocator facts).

    The tree-edge side condition is `hfresh2`: `succ1`'s subtree never discovers `succ2`. It is stated
    ∀-quantified over the subtree's starting visited-set/table (and fuel), so it is invariant under the
    chain induction — callers discharge it from the CFG. Base = `dfsEntriesAux_head_succ2_records`; step =
    the same `dfsEntriesAux_single_succ_lift` (which lifts an arbitrary recorded value). -/
theorem dfsEntriesAux_chain_succ2_records {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (path : List BasicBlock) (fuel : Nat) (visited : List String)
      (tbl : AssocList String PlanState) (ps : PlanState)
      (result : List String × AssocList String PlanState × PlanState)
      (pred succ1 succ2 : String) (succBB1 succBB2 : BasicBlock) (blockOps : List StackOp)
      (predPs' : PlanState) (succRest : List String),
      2 * path.length + 4 ≤ fuel →
      JmpChainTo L D C fn pred blockOps predPs' path visited ps →
      C.succsOf pred = succ1 :: succ2 :: succRest →
      fn.blocks.find? (·.label == succ1) = some succBB1 →
      fn.blocks.find? (·.label == succ2) = some succBB2 →
      (∀ b ∈ path, b.label ≠ succ1) → visited.contains succ1 = false → succ1 ≠ pred →
      (∀ b ∈ path, b.label ≠ succ2) → visited.contains succ2 = false → succ2 ≠ pred →
      (∀ (f : Nat) (vis : List String) (tb : AssocList String PlanState)
         (r : List String × AssocList String PlanState × PlanState),
        vis.contains succ2 = false →
        dfsEntriesAux f L D C fn [succ1] vis tb predPs' = some r → r.1.contains succ2 = false) →
      dfsEntriesAux fuel L D C fn [(path.head?.map (·.label)).getD pred] visited tbl ps = some result →
      ∃ psS, AssocList.lookup String PlanState result.2.1 succ2 = some psS ∧
        psS.stack = predPs'.stack ∧ psS.spilled = predPs'.spilled ∧
        AllocInv predPs'.alloc psS.alloc ∧ result.1.contains succ2 = true := by
  intro path
  induction path with
  | nil =>
    intro fuel visited tbl ps result pred succ1 succ2 succBB1 succBB2 blockOps predPs' succRest
      hfuel hchain hsuccs hsfind1 hsfind2 _ hsvis1 hsne1 _ hsvis2 hsne2 hfresh2 htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, predBB', hfindP, hbp⟩ := hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 + 1 + 1 := ⟨fuel - 4, by omega⟩
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at htop
    have hsvisf1 : (pred :: visited).contains succ1 = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [hsne1], hsvis1⟩
    have hsvisf2 : (pred :: visited).contains succ2 = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [hsne2], hsvis2⟩
    -- the first successor's subtree terminates; name its result
    obtain ⟨rSub, hga⟩ := Option.isSome_iff_exists.mp
      ((dfsEntriesAux_dfsSuccsEntries_isSome L D C fn hfn (f + 2)).1 [succ1] (pred :: visited)
        (AssocList.insert String PlanState tbl pred ps)
        { predPs' with stack := predPs'.stack, spilled := predPs'.spilled })
    obtain ⟨vAfter, tblAfter, psAfter⟩ := rSub
    rw [planState_eta_stack_spilled predPs'] at hga
    -- succ2 stays fresh across that subtree (tree edge)
    have hfr2 : vAfter.contains succ2 = false := hfresh2 (f + 2) (pred :: visited) _ _ hsvisf2 hga
    rw [← planState_eta_stack_spilled predPs'] at hga
    have hallo := (dfsEntries_alloc_inv L D C fn (f + 2)).1 [succ1] (pred :: visited)
      (AssocList.insert String PlanState tbl pred ps)
      { predPs' with stack := predPs'.stack, spilled := predPs'.spilled } vAfter tblAfter psAfter hga
    refine ⟨_, dfsEntriesAux_head_succ2_records f L D C fn pred [] visited tbl ps predBB' blockOps
      predPs' succ1 succ2 succRest succBB1 succBB2 vAfter tblAfter psAfter result hvis hfindP hbp
      hsuccs hsvisf1 hsfind1 hga hfr2 hsfind2 htop, rfl, rfl, hallo,
      dfsEntriesAux_head_succ2_visited f L D C fn pred [] visited tbl ps predBB' blockOps predPs'
        succ1 succ2 succRest succBB2 vAfter tblAfter psAfter result hvis hfindP hbp hsuccs hga hfr2
        hsfind2 htop⟩
  | cons bb rest ih =>
    intro fuel visited tbl ps result pred succ1 succ2 succBB1 succBB2 blockOps predPs' succRest
      hfuel hchain hsuccs hsfind1 hsfind2 hsfresh1 hsvis1 hsne1 hsfresh2 hsvis2 hsne2 hfresh2 htop
    simp only [JmpChainTo] at hchain
    obtain ⟨hvisBB, hfindBB, hsuccBB, block, ps'_bb, hblockBB, hchain'⟩ := hchain
    obtain ⟨fr, rfl⟩ : ∃ fr, fuel = fr + 2 := ⟨fuel - 2, by simp only [List.length_cons] at hfuel; omega⟩
    have hfr : 2 * rest.length + 4 ≤ fr := by simp only [List.length_cons] at hfuel; omega
    obtain ⟨resultSucc, hsub⟩ := Option.isSome_iff_exists.mp
      ((dfsEntriesAux_dfsSuccsEntries_isSome L D C fn hfn fr).1
        [(rest.head?.map (·.label)).getD pred] (bb.label :: visited)
        (AssocList.insert String PlanState tbl bb.label ps) ps'_bb)
    have hsvis1' : (bb.label :: visited).contains succ1 = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [(hsfresh1 bb (List.mem_cons_self ..)).symm], hsvis1⟩
    have hsvis2' : (bb.label :: visited).contains succ2 = false := by
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simp [(hsfresh2 bb (List.mem_cons_self ..)).symm], hsvis2⟩
    obtain ⟨psS, hrecS, hstk, hsp, hallo, hvisS⟩ :=
      ih fr (bb.label :: visited) (AssocList.insert String PlanState tbl bb.label ps) ps'_bb resultSucc
        pred succ1 succ2 succBB1 succBB2 blockOps predPs' succRest hfr hchain' hsuccs hsfind1 hsfind2
        (fun b hb => hsfresh1 b (List.mem_cons_of_mem bb hb)) hsvis1' hsne1
        (fun b hb => hsfresh2 b (List.mem_cons_of_mem bb hb)) hsvis2' hsne2 hfresh2 hsub
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at htop
    obtain ⟨hrecR, hvisR⟩ :=
      dfsEntriesAux_single_succ_lift hvisBB hfindBB hsuccBB hblockBB hsub hrecS hvisS htop
    exact ⟨psS, hrecR, hstk, hsp, hallo, hvisR⟩

end EvmYul.Venom.Hol.Codegen

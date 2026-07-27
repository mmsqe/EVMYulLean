import EvmYul.Venom.Hol.Codegen.GenInstSim.JoinProducers

/-!
# GenInstSim — GenLayout

0-input context-push through the real generator, the remaining non-commutative binop
instantiations, block-plan asm structure, memory monotonicity, and the both-spilled store producer.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

variable {offsetToPc : AssocList Nat Nat}

/-! ## 0-input context-push through the real generator (`generateRegularInstPlan`)

The degenerate case of the unary-var family, for a 0-input / 1-output op (`CALLVALUE`, `CALLER`,
`CODESIZE`, …): with no operands, input emission is empty, so the generated plan (under the swap
no-op) is just `[SOEmit name]`, and the sim is `emit_read0_sim` followed by `releaseDeadSpills_sim`.
This is the `generateRegularInstPlan`-level counterpart of `emit_ctx_push_sim` — the piece a body-fold
`BodyStep` producer for context pushes builds on. -/

/-- **Plan decomposition** for a 0-input / 1-output op: no input emission, so the plan is
    `[SOEmit name]` followed by the optimistic swap, with `releaseDeadSpills` on the output state. The
    0-operand analog of `genRegularInstPlan_unopVar_eq`. -/
theorem genRegularInstPlan_read0_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {out name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ([StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { ps with stack := ps.stack ++ [Operand.Var out] }).1,
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { ps with stack := ps.stack ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = ([] : List Operand) := by rw [hops]; rfl
  have hemit : emitInputPlan inst.opcode ([] : List Operand) nextLiveness ps = ([], ps) := rfl
  have hmem : out ∈ nextLiveness := by simpa using hlive
  unfold generateRegularInstPlan
  simp [hcompute, hrev, hemit, houts, reorderPlan_empty, stackPop_zero, stackPush,
    popmanyPlan_nil, generateEmitOps_evmName hname, hmem, hnjmp]

/-- **The runnable sim for a 0-input context-push op** through `generateRegularInstPlan`. A degenerate
    `genRegularInstPlan_unopVar_sim`: no input emission, so the plan (under the swap no-op) is just
    `[SOEmit name]`, and the sim is `emit_read0_sim` then `releaseDeadSpills_sim`. -/
theorem genRegularInstPlan_read0_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {out name : String} {v : bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (h : as.pc < prog.length),
        prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog as = asmPushVal v as)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out v vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive, hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ := emit_read0_sim hrel hfresh hspill hblock hdisp
  have hpush : ({ ps with stack := stackPush (Operand.Var out) ps.stack } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by rfl
  rw [hpush] at hrelE
  exact ⟨as2, hrunE, releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE, hpcE⟩

/-- **The runnable sim for SLOAD** through `generateRegularInstPlan`. Same plan shape as a unary var-op
    (`genRegularInstPlan_unopVar_eq`: DUP the key, emit `SLOAD`), but the emitted step is a storage
    read (`emit_sload_sim`) rather than a pure unop, so the pushed value is `sload key vs` — a function
    of the input *and* shared state (agreeing via the `accounts`/`callCtx` conjuncts), not just the
    input. The storage-read counterpart of `genRegularInstPlan_unopVar_sim`. -/
theorem genRegularInstPlan_sload_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {dist : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (sload w vs) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SLOAD"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_sload_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **TLOAD instruction sim** — the transient-storage twin of `genRegularInstPlan_sload_sim`. Identical
    plan/stack scaffolding (the generic `genRegularInstPlan_unopVar_eq` 1-input/1-output shape); only the
    read semantics differ: `emit_tload_sim` reconciles the `TLOAD` asm read with `tload w vs`. -/
theorem genRegularInstPlan_tload_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {dist : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (tload w vs) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "TLOAD"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_tload_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **BLOCKHASH instruction sim** — the block-env twin of `genRegularInstPlan_tload_sim`:
    DUP the index var, emit `BLOCKHASH`; the generated plan preserves `venomAsmRel` across the
    Venom step `out := blockCtx.blockhash w`. -/
theorem genRegularInstPlan_blockhash_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {dist : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "BLOCKHASH")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "BLOCKHASH" →
          asmStep offsetToPc prog s = asmStateUnop (fun v s => s.blockCtx.blockhash v.toNat) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (vs.blockCtx.blockhash w.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "BLOCKHASH"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_blockhash_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Spilled TLOAD instruction sim — the first spill-aware `genRegularInstPlan` producer.** The
    `x`-spilled reroute of `genRegularInstPlan_tload_sim`: the operand is *restored* from its spill slot
    (not DUP'd), transitions onto the stack, and the TLOAD runs — the whole generated plan preserves
    `venomAsmRel` across the Venom step `out := tload w`. Composes `genRegularInstPlan_unopVar_spilled_eq`
    (plan reduction) + `emitInputPlan_single_var_sim_spilled` (spilled emit) + `emit_tload_sim`. Concrete
    demonstration that a compiled op runs correctly with a spilled operand — the read-class instance of
    the Gap-C producer reroute. -/
theorem genRegularInstPlan_tload_spilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {off : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base) (houtx : out ≠ x)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (tload w vs) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_unopVar_spilled_eq hname hnjmp hcompute hops houts hstack0 hlive hspill hlivex,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hemitshape : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps.spilled (Operand.Var x), alloc := freeSpillSlot off ps.alloc }) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append, emitOneInput_var_spilled_eq hspill hlivex]
  have hps1stack : ps1.stack = base ++ [Operand.Var x, Operand.Var x] := by
    rw [hps1def, hemitshape, hstack0]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemitshape]
    exact aremove_lookup_none ps.spilled (Operand.Var x) (Operand.Var out) hspill_out
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim_spilled (offsetToPc := offsetToPc) hspill hlivex hrel hspillWf hbI
  have hps1stack'' : ps1.stack = (base ++ [Operand.Var x]) ++ [Operand.Var x] := by rw [hps1stack]; simp
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack'' hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · exact hfresh h
    · exact houtx (by injection h)
    · exact houtx (by injection h)
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "TLOAD"]) := by rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_tload_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x, Operand.Var out] } := by
    congr 1
    rw [hps1stack, show base ++ [Operand.Var x, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var x] from by simp,
        stackPop_1_append_single]
    simp [stackPush, List.append_assoc]
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Spilled-operand unary-op instruction sim** (generic pure `f`). The spilled twin of
    `genRegularInstPlan_unopVar_sim`, and the op-generic twin of `genRegularInstPlan_tload_spilled_sim`:
    the operand `x` lives in a spill slot, so `emitInputPlan` emits `SORestore off ; DUP1` before the
    opcode. Covers ISZERO / NOT / SLOAD / EXTCODESIZE / … with a spilled input — previously only the
    both-live case (`genRegularInstPlan_unopVar_sim`) and the TLOAD-specific spilled case existed. -/
theorem genRegularInstPlan_unopVar_spilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out name : String} {base : List Operand} {off : Nat} {w : bytes32}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base) (houtx : out ≠ x)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f w) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_unopVar_spilled_eq hname hnjmp hcompute hops houts hstack0 hlive hspill hlivex,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hemitshape : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps.spilled (Operand.Var x), alloc := freeSpillSlot off ps.alloc }) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append, emitOneInput_var_spilled_eq hspill hlivex]
  have hps1stack : ps1.stack = base ++ [Operand.Var x, Operand.Var x] := by
    rw [hps1def, hemitshape, hstack0]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemitshape]
    exact aremove_lookup_none ps.spilled (Operand.Var x) (Operand.Var out) hspill_out
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim_spilled (offsetToPc := offsetToPc) hspill hlivex hrel hspillWf hbI
  have hps1stack'' : ps1.stack = (base ++ [Operand.Var x]) ++ [Operand.Var x] := by rw [hps1stack]; simp
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack'' hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · exact hfresh h
    · exact houtx (by injection h)
    · exact houtx (by injection h)
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_unop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x, Operand.Var out] } := by
    congr 1
    rw [hps1stack, show base ++ [Operand.Var x, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var x] from by simp,
        stackPop_1_append_single]
    simp [stackPush, List.append_assoc]
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega


/-- **CALLDATALOAD instruction sim** — the calldata-word read over the real plan; the calldata twin of
    `genRegularInstPlan_tload_sim` (same generic 1-input plan; `emit_calldataload_sim` reconciles). -/
theorem genRegularInstPlan_calldataload_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {dist : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATALOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "CALLDATALOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun offset s =>
            wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out (wordOfBytes
               ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding w.toNat 32)) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALLDATALOAD"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_calldataload_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Generic account-read instruction sim** over the generic 1-input/1-output plan. BALANCE /
    EXTCODESIZE / EXTCODEHASH instantiate `fRead` (and the per-opcode `name` / `asmStep_*_ok`). -/
theorem genRegularInstPlan_accountRead_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out name : String} {base : List Operand} {dist : Nat} {w : bytes32}
    {fRead : bytes32 → Accounts → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out (fRead w vs.accounts) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_accountRead_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Plan decomposition** for a no-output *single*-var instruction (SELFDESTRUCT): the emitted ops
    are the one-operand input-emission `++ [SOEmit name]`. The single-operand analog of
    `genRegularInstPlan_noOutput2Var_ops_eq` (the commutative branch is dead — only one operand). -/
theorem genRegularInstPlan_noOutput1Var_ops_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x : String} {base : List Operand} {name : String} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
        curBbLabel ps).1
      = (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name] := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hpvar := emitInputPlan_single_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill hlivex hdepth hsmall hpeek
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname, reorderPlan_single_var_nil base x ps1 hps1',
        hps1', stackPop_1_append_single, hnjmp]

/-- **Full per-instruction terminal sim for SELFDESTRUCT**: composes the single-operand input-emission
    decomposition with `emitInputPlan_single_var_sim` and `emit_selfdestruct_sim`. Running the whole
    `generateRegularInstPlan` plan from `venomAsmRel` reaches `AsmHalt` with the account transfer of
    the Venom `SELFDESTRUCT` (`venomAsmTerminalRel`). No memory coverage needed (accounts, not memory);
    the first operand-carrying terminal that mutates accounts to be discharged end to end. -/
theorem genRegularInstPlan_selfdestruct_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x : String} {wx : bytes32} {base : List Operand} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SELFDESTRUCT")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) (hlen : dist < ps.stack.length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
             isHalting nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (selfdestruct wx vs)) as' := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_noOutput1Var_ops_eq hname hnjmp hcompute hops houts hstack0 hnospill hlivex
        hdepth hsmall, hrev] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel hlen hbI
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by
    rw [emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall (stackGetDepth_peek hdepth), hstack0]
  have hstacktop : as1.stack = wx :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hvx
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SELFDESTRUCT"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, htermE⟩ := emit_selfdestruct_sim hrelI hstacktop hbE'
  refine ⟨as2, ?_, htermE⟩
  rw [executePlan_append, List.length_append, runAsm_append_ok hrunI]
  exact hrunE

/-- ISZERO instantiation. -/
theorem genRegularInstPlan_iszeroLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a : bytes32} {out : String} {base : List Operand}
    (hisz : inst.opcode = Opcode.ISZERO)
    (hops : inst.operands = [Operand.Lit a]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.isZero a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_unopLit_sim (by rw [hisz]; rfl) (by rw [hisz]; decide)
    (by simp [computeOperands, hisz]) hops houts hstack0 hlive hfresh hspill
    (fun _ h hg => asmStep_iszero_ok h hg) optimisticSwapPlan_terminator hrel hblock

/-- NOT instantiation. -/
theorem genRegularInstPlan_notLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a : bytes32} {out : String} {base : List Operand}
    (hnot : inst.opcode = Opcode.NOT)
    (hops : inst.operands = [Operand.Lit a]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (~~~ a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_unopLit_sim (f := (~~~ ·)) (by rw [hnot]; rfl) (by rw [hnot]; decide)
    (by simp [computeOperands, hnot]) hops houts hstack0 hlive hfresh hspill
    (fun _ h hg => asmStep_not_ok h hg) optimisticSwapPlan_terminator hrel hblock

/-! ## Remaining non-commutative binop instantiations

The same-shape opcodes, each a one-liner over `genRegularInstPlan_nonCommBinopLit_sim` with its `f`
and `asmStep_*_ok` dispatch (mechanical copies of `DIV`/`SHL`/`SLT`). -/

/-- MOD instantiation. -/
theorem genRegularInstPlan_modLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.Mod)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (safeMod a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_mod_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SDIV instantiation. -/
theorem genRegularInstPlan_sdivLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SDIV)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (safeSdiv a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sdiv_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SMOD instantiation. -/
theorem genRegularInstPlan_smodLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SMOD)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (safeSmod a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_smod_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- EXP instantiation. -/
theorem genRegularInstPlan_expLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.Exp)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.exp a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_exp_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SGT instantiation. -/
theorem genRegularInstPlan_sgtLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SGT)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.sgt a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sgt_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SHR instantiation (shift; `f a b = b >>> a` pinned, like SHL). -/
theorem genRegularInstPlan_shrLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SHR)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (b >>> a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (f := fun a b => b >>> a)
    (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_shr_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SAR instantiation. -/
theorem genRegularInstPlan_sarLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SAR)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.sar a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sar_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-! ## Block plan asm structure

The bridge from the generator decomposition (`generateBlockPlan_decompose`:
`blockOps = SOLabel bb.label :: cleanOps ++ instOps`) to the asm interpreter: the
compiled block is `AsmLabel bb.label :: (executePlan cleanOps ++ executePlan instOps)`.
This is the shape `genBlockSimulation`'s `runAsm`/`plan_seq_sim` reasoning decomposes —
the leading `AsmLabel` runs via `soLabel_sim`, then the clean and instruction segments. -/

/-- `executePlan` of a label-prefixed plan. -/
theorem executePlan_label_cons (l : String) (ops : List StackOp) :
    executePlan (StackOp.SOLabel l :: ops) = AsmInst.AsmLabel l :: executePlan ops := by
  rw [executePlan_cons]; rfl

/-- Asm structure of a decomposed block plan (`SOLabel :: cleanOps ++ instOps`). -/
theorem executePlan_blockOps (l : String) (cleanOps instOps : List StackOp) :
    executePlan (StackOp.SOLabel l :: cleanOps ++ instOps)
      = AsmInst.AsmLabel l :: (executePlan cleanOps ++ executePlan instOps) := by
  rw [executePlan_append, executePlan_label_cons, List.cons_append]


/-! ## Memory monotonicity of the asm machine

No `asmStep`/`runAsm` ever shrinks memory (reads pad, writes/`asmExpandMemory` grow, stack ops
preserve). This discharges the `hmemmono` precondition of the spill-aware invariant
(`StackDiscHS`) unconditionally. -/


theorem byteArray_write_size_le (source : ByteArray) (sa : Nat) (dest : ByteArray) (da len : Nat) :
    dest.size ≤ (source.write sa dest da len).size := by
  simp only [ByteArray.write]
  split
  · exact le_refl _
  · split
    · rw [ByteArray.size_copySlice]; omega
    · rw [ByteArray.size_copySlice, ByteArray.size_append]; omega

theorem asmExpandMemory_size_mono (needed : Nat) (mem : ByteArray) :
    mem.size ≤ (asmExpandMemory needed mem).size := by
  simp only [asmExpandMemory]
  split
  · exact le_refl _
  · exact byteArray_write_size_le _ 0 mem mem.size _

/-- `s.memory.size ≤` an `if siz=0 then s.memory else asmExpandMemory …` — the shape every copy/SHA3/LOG
    op takes for its expanded memory. -/
theorem memCond_size (c : Prop) [Decidable c] (n : Nat) (m : ByteArray) :
    m.size ≤ (if c then m else asmExpandMemory n m).size := by
  split
  · exact le_refl _
  · exact asmExpandMemory_size_mono n m

-- Memory-preserving helpers (result carries `s.memory` unchanged).
theorem asmPushVal_memory_le {v s s'} (h : asmPushVal v s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmPushVal at h; injection h with h; subst h; exact le_refl _
theorem asmPop_memory_le {s s'} (h : asmPop s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmPop at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmBinop_memory_le {f s s'} (h : asmBinop f s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmBinop at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmUnop_memory_le {f s s'} (h : asmUnop f s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmUnop at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmTernop_memory_le {f s s'} (h : asmTernop f s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmTernop at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmStateUnop_memory_le {f s s'} (h : asmStateUnop f s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmStateUnop at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmDup_memory_le {n s s'} (h : asmDup n s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmDup at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmSwap_memory_le {n s s'} (h : asmSwap n s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmSwap at h; split at h
  · split at h
    · injection h with h; subst h; exact le_refl _
    · exact absurd h (by simp)
  · exact absurd h (by simp)
theorem asmSload_memory_le {s s'} (h : asmSload s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmSload at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmSstore_memory_le {s s'} (h : asmSstore s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmSstore at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)
theorem asmJump_memory_le {o2pc s s'} (h : asmJump o2pc s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmJump at h; split at h
  · split at h
    · injection h with h; subst h; exact le_refl _
    · exact absurd h (by simp)
  · exact absurd h (by simp)
theorem asmJumpi_memory_le {o2pc s s'} (h : asmJumpi o2pc s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmJumpi at h; split at h
  · split at h
    · injection h with h; subst h; exact le_refl _
    · split at h
      · injection h with h; subst h; exact le_refl _
      · exact absurd h (by simp)
  · exact absurd h (by simp)

-- Memory-monotone helpers (expand memory, never shrink).
theorem asmMload_memory_le {s s'} (h : asmMload s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmMload at h; split at h
  · injection h with h; subst h; dsimp only; exact asmExpandMemory_size_mono _ _
  · exact absurd h (by simp)
theorem asmMstore_memory_le {s s'} (h : asmMstore s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmMstore at h; split at h
  · injection h with h; subst h; dsimp only
    exact le_trans (asmExpandMemory_size_mono _ _) (byteArray_write_size_le _ 0 _ _ _)
  · exact absurd h (by simp)
theorem asmMstore8_memory_le {s s'} (h : asmMstore8 s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmMstore8 at h; split at h
  · injection h with h; subst h; dsimp only
    exact le_trans (asmExpandMemory_size_mono _ _) (byteArray_write_size_le _ 0 _ _ _)
  · exact absurd h (by simp)
theorem asmSha3_memory_le {s s'} (h : asmSha3 s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmSha3 at h; split at h
  · injection h with h; subst h; dsimp only; exact memCond_size _ _ _
  · exact absurd h (by simp)
theorem asmCopyToMem_memory_le {src s s'} (h : asmCopyToMem src s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmCopyToMem at h; split at h
  · injection h with h; subst h; dsimp only
    exact le_trans (memCond_size _ _ _) (byteArray_write_size_le _ 0 _ _ _)
  · exact absurd h (by simp)
theorem asmExtcodecopy_memory_le {s s'} (h : asmExtcodecopy s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmExtcodecopy at h; split at h
  · have h2 := asmCopyToMem_memory_le h; exact h2
  · exact absurd h (by simp)
theorem asmReturndatacopy_memory_le {s s'} (h : asmReturndatacopy s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmReturndatacopy at h; split at h
  · dsimp only at h; split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; dsimp only
      exact le_trans (memCond_size _ _ _) (byteArray_write_size_le _ 0 _ _ _)
  · exact absurd h (by simp)
theorem asmMcopy_memory_le {s s'} (h : asmMcopy s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmMcopy at h; split at h
  · injection h with h; subst h; dsimp only
    exact le_trans (memCond_size _ _ _) (byteArray_write_size_le _ 0 _ _ _)
  · exact absurd h (by simp)
theorem asmLog_memory_le {n s s'} (h : asmLog n s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmLog at h; split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; dsimp only; exact memCond_size _ _ _

-- Never-AsmOK helpers (vacuous: these ops halt/revert/fault).
theorem asmReturnOp_memory_le {s s'} (h : asmReturnOp s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmReturnOp at h; split at h <;> simp_all
theorem asmRevertOp_memory_le {s s'} (h : asmRevertOp s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmRevertOp at h; split at h <;> simp_all
theorem asmSelfdestruct_memory_le {s s'} (h : asmSelfdestruct s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmSelfdestruct at h; split at h <;> simp_all

theorem asmCall_memory_le {s s'} (h : asmCall s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmCall asmCallWriteback at h; split at h
  · injection h with h; subst h; dsimp only; exact byteArray_write_size_le _ 0 _ _ _
  · exact absurd h (by simp)

theorem asmStaticCall_memory_le {s s'} (h : asmStaticCall s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmStaticCall asmCallWriteback at h; split at h
  · injection h with h; subst h; dsimp only; exact byteArray_write_size_le _ 0 _ _ _
  · exact absurd h (by simp)

theorem asmDelegateCall_memory_le {s s'} (h : asmDelegateCall s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmDelegateCall asmCallWriteback at h; split at h
  · injection h with h; subst h; dsimp only; exact byteArray_write_size_le _ 0 _ _ _
  · exact absurd h (by simp)

theorem asmCreate_memory_le {s s'} (h : asmCreate s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmCreate at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)

theorem asmCreate2_memory_le {s s'} (h : asmCreate2 s = AsmResult.AsmOK s') : s.memory.size ≤ s'.memory.size := by
  unfold asmCreate2 at h; split at h
  · injection h with h; subst h; exact le_refl _
  · exact absurd h (by simp)

set_option maxHeartbeats 4000000 in
/-- **A single `asmStep` never shrinks memory.** Case analysis over the instruction dispatch: every
    `AsmOK`-producing branch either preserves `s.memory` or expands it (`asmExpandMemory`/write). -/
theorem asmStep_memory_size_mono {o2pc prog s s'} (h : asmStep o2pc prog s = AsmResult.AsmOK s') :
    s.memory.size ≤ s'.memory.size := by
  unfold asmStep at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | exact asmPop_memory_le h
      | exact asmBinop_memory_le h
      | exact asmUnop_memory_le h
      | exact asmTernop_memory_le h
      | exact asmStateUnop_memory_le h
      | exact asmPushVal_memory_le h
      | exact asmDup_memory_le h
      | exact asmSwap_memory_le h
      | exact asmSload_memory_le h
      | exact asmSstore_memory_le h
      | exact asmMload_memory_le h
      | exact asmMstore_memory_le h
      | exact asmMstore8_memory_le h
      | exact asmSha3_memory_le h
      | exact asmCopyToMem_memory_le h
      | exact asmExtcodecopy_memory_le h
      | exact asmReturndatacopy_memory_le h
      | exact asmMcopy_memory_le h
      | exact asmLog_memory_le h
      | exact asmJump_memory_le h
      | exact asmJumpi_memory_le h
      | exact asmReturnOp_memory_le h
      | exact asmRevertOp_memory_le h
      | exact asmSelfdestruct_memory_le h
      | exact asmCall_memory_le h
      | exact asmStaticCall_memory_le h
      | exact asmDelegateCall_memory_le h
      | exact asmCreate_memory_le h
      | exact asmCreate2_memory_le h
      | (injection h with h; subst h; exact le_refl _)
      | (exact absurd h (by simp))
  · exact absurd h (by simp)

/-- **`runAsm` never shrinks memory.** Fuel induction over `asmStep_memory_size_mono`. -/
theorem runAsm_memory_size_mono {n o2pc prog s s'} (h : runAsm n o2pc prog s = AsmResult.AsmOK s') :
    s.memory.size ≤ s'.memory.size := by
  induction n generalizing s with
  | zero => rw [runAsm] at h; injection h with h; subst h; exact le_refl _
  | succ n ih =>
    rw [runAsm] at h
    split at h
    · rename_i s1 heq
      exact le_trans (asmStep_memory_size_mono heq) (ih h)
    · rename_i heq
      exact absurd h (heq s')

/-- **`emitInputPlan` sim for a mixed pair `[live v, spilled w]`** — the complement of
    `emitInputPlan_pair_spill_first_sim`: the head is the ordinary DUP path for the live var `v`, the
    tail the spilled-restore path for `w`. Since the head is a pure stack DUP (memory unchanged), the
    spill well-formedness lifts to the tail via `runAsm_memory_size_mono` (placed after it here for the
    forward reference). Completes the two-var mixed spill coverage (either operand spilled). -/
theorem emitInputPlan_pair_spill_second_sim {opc nl v w ps lo vs as prog off d}
    (hnospillv : alookup' ps.spilled (Operand.Var v) = none)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hdepthv : stackGetDepth (Operand.Var v) ps.stack = some d) (hsmall : d ≤ 15)
    (hlenv : d < ps.stack.length)
    (hspillw : alookup' ps.spilled (Operand.Var w) = some off)
    (hrel : venomAsmRel lo ps vs as)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length := by
  -- head: live v via doDup
  set ps1 : PlanState := { ps with stack := stackDup d ps.stack } with hps1def
  have hdd : doDup d ps = ([StackOp.SODup (d + 1)], ps1) := by
    rw [hps1def]; unfold doDup; rw [if_pos hsmall]
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SODup (d + 1)], ps1) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillv, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivev, if_true, hdepthv, hdd, List.nil_append]
  have hspillw1 : alookup' ps1.spilled (Operand.Var w) = some off := by rw [hps1def]; exact hspillw
  -- tail: spilled w via restore
  set ps2 : PlanState := { ps1 with stack := ps1.stack ++ [Operand.Var w, Operand.Var w],
                                     spilled := aremove ps1.spilled (Operand.Var w),
                                     alloc := freeSpillSlot off ps1.alloc } with hps2def
  have htail : emitOneInput opc nl (Operand.Var w) ps1 = ([StackOp.SORestore off, StackOp.SODup 1], ps2) :=
    emitOneInput_var_spilled_eq hspillw1 hlivew
  have hfold : emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps
      = ([StackOp.SODup (d + 1)] ++ [StackOp.SORestore off, StackOp.SODup 1], ps2) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hfold] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbHead, hbTail⟩ := asmBlockAt_append hblock
  -- run head
  obtain ⟨as1, hrunHead, hrelHead, hpcHead⟩ :=
    doDup_sim (offsetToPc := offsetToPc) hdd hsmall hrel hlenv hbHead
  -- lift spill wf to ps1/as1 (head is pure DUP; memory never shrinks)
  have hmemmono : as.memory.size ≤ as1.memory.size := runAsm_memory_size_mono hrunHead
  have hspillWf1 : ∀ o off', alookup' ps1.spilled o = some off' →
      32 ∣ off' ∧ off' + 32 ≤ as1.memory.size ∧ off' < 2 ^ 256 := by
    intro o off' ho
    have ho' : alookup' ps.spilled o = some off' := by rw [hps1def] at ho; exact ho
    obtain ⟨hdvd, hle, hlt⟩ := hspillWf o off' ho'
    exact ⟨hdvd, le_trans hle hmemmono, hlt⟩
  -- run tail
  have hbTail' : asmBlockAt prog as1.pc (executePlan [StackOp.SORestore off, StackOp.SODup 1]) := by
    rw [hpcHead]; exact hbTail
  obtain ⟨as2, hrunTail, hrelTail, hpcTail⟩ :=
    emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hspillw1 hlivew htail hrelHead hspillWf1 hbTail'
  have hlen : (executePlan ([StackOp.SODup (d + 1)] ++ [StackOp.SORestore off, StackOp.SODup 1])).length
      = (executePlan [StackOp.SODup (d + 1)]).length
        + (executePlan [StackOp.SORestore off, StackOp.SODup 1]).length := by
    rw [executePlan_append, List.length_append]
  refine ⟨as2, ?_, hrelTail, ?_⟩
  · rw [hlen]; exact runAsm_compose hrunHead hrunTail
  · rw [hlen, hpcTail, hpcHead]; omega

/-- **Key-spilled store sim — the first non-positioned reorder-under-spill producer.** `SSTORE x y`,
    key `x` spilled, value `y` live: DUP `y`, restore `x`, then the reorder runs `SWAP2 ; SWAP1` to bring
    the deep `y` to its store position, then SSTORE — the whole plan preserves `venomAsmRel` across
    `sstore wx wy`. Composes the LS emit + two `doSwap_sim` + `emit_sstore_sim`. -/
theorem genRegularInstPlan_sstore_keyspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {wx wy : bytes32} {base : List Operand} {offx d_y : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (sstore wx wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenv : d_y < ps.stack.length := stackGetDepth_lt_length hdepth_y
  rw [genRegularInstPlan_sstore_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  -- the plan tail as a right-nested append
  rw [show ([StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"] : List StackOp)
        = [StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"]) from rfl] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap2raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap1raw, hbStoreraw⟩ := asmBlockAt_append hbRest2
  -- run emit
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_second_sim (offsetToPc := offsetToPc) hnospill_y hlivey hlivex hdepth_y hsmall_y
      hlenv hspill_x hrel hspillWf hbI
  -- SWAP2
  have hlen2 : (2 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap2 : doSwap 2 ps1 = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [hps1stack, stackSwap_2_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap2 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpcI]; exact hbSwap2raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrelI hlen2 hbSwap2 (by intro h; omega)
  -- SWAP1
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var x, Operand.Var y] from rfl,
        stackSwap_1_append_triple base (Operand.Var x) (Operand.Var x) (Operand.Var y)]
  have hbSwap1 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel2 hlen1 hbSwap1 (by intro h; omega)
  -- SSTORE
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as3.stack = wx :: wy :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvx hvy
  have hbSST : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by rw [hpc3, hpc2, hpcI]; exact hbStoreraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_sstore_sim hrel3 hstacktop hbSST (fun h hg => hdisp as3 h hg)
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } with
      stack := stackPop 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var x]) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x] } := by
    rw [show base ++ [Operand.Var x, Operand.Var y, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit "SSTORE"]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega

/-- **Key-spilled non-commutative binop sim.** Value `y` live, key `x` spilled: DUP `y`, restore `x`,
    run the `SWAP2 ; SWAP1` reorder, run the binop, push `out` — the whole plan preserves `venomAsmRel`
    across `out := f wx wy`. Composes the LS emit sim, two `doSwap_sim`, and `emit_binop_sim`. -/
theorem genRegularInstPlan_nonCommBinopVar_keyspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offx d_y : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenv : d_y < ps.stack.length := stackGetDepth_lt_length hdepth_y
  rw [genRegularInstPlan_nonCommBinopVar_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
    show alookup' (aremove ps.spilled (Operand.Var x)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var x) (Operand.Var out) hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ [StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name])) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap2raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap1raw, hbEmitraw⟩ := asmBlockAt_append hbRest2
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_second_sim (offsetToPc := offsetToPc) hnospill_y hlivey hlivex hdepth_y hsmall_y
      hlenv hspill_x hrel hspillWf hbI
  have hlen2 : (2 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap2 : doSwap 2 ps1 = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [hps1stack, stackSwap_2_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap2 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpcI]; exact hbSwap2raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrelI hlen2 hbSwap2 (by intro h; omega)
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var x, Operand.Var y] from rfl,
        stackSwap_1_append_triple base (Operand.Var x) (Operand.Var x) (Operand.Var y)]
  have hbSwap1 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel2 hlen1 hbSwap1 (by intro h; omega)
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as3.stack = wx :: wy :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvx hvy
  have hfresh3 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var x, Operand.Var y, Operand.Var x]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h)
    · exact hfresh h
    · exact hox (by injection h)
    · exact hoy (by injection h)
    · exact hox (by injection h)
  have hps3spill : alookup' ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).spilled (Operand.Var out) = none := hps1spill
  have hbEmit : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit name]) := by rw [hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_binop_sim hrel3 hstacktop hfresh3 hps3spill hbEmit (fun h hg => hdisp as3 h hg)
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] } with
      stack := stackPush (Operand.Var out) (stackPop 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var x])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x, Operand.Var out] } := by
    rw [show base ++ [Operand.Var x, Operand.Var y, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit name]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega

/-- **Key-spilled commutative binop sim.** Value `y` live, key `x` spilled; the commutative
    dispatch picks the swapped order, so the reorder is `SWAP1 ; SWAP2` (first SWAP1 transposes
    the two equal restored `x`'s — a stack no-op) leaving `base ++ [x, x, y]`; the binop pops
    `f wy wx`, rewritten to `f wx wy` by `hfcomm`. Preserves `venomAsmRel` across `out := f wx wy`. -/
theorem genRegularInstPlan_commBinopVar_keyspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offx d_y : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenv : d_y < ps.stack.length := stackGetDepth_lt_length hdepth_y
  rw [genRegularInstPlan_commBinopVar_keyspilled_eq hname hcomm hops houts hxy hstack0 hlive
      hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
    show alookup' (aremove ps.spilled (Operand.Var x)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var x) (Operand.Var out) hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ [StackOp.SOSwap 1, StackOp.SOSwap 2] ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 2] ++ [StackOp.SOEmit name])) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap1raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap2raw, hbEmitraw⟩ := asmBlockAt_append hbRest2
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_second_sim (offsetToPc := offsetToPc) hnospill_y hlivey hlivex hdepth_y hsmall_y
      hlenv hspill_x hrel hspillWf hbI
  -- SWAP1 : swaps the two equal x's, a no-op on the stack
  have hlen1 : (1 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap1 : doSwap 1 ps1 = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [hps1stack, stackSwap_1_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpcI]; exact hbSwap1raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrelI hlen1 hbSwap1 (by intro h; omega)
  -- SWAP2 : rotate the deep y to TOS
  have hlen2 : (2 : Nat) < ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] } : PlanState).stack.length := by simp
  have hswap2 : doSwap 2 { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] }
      = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] } : PlanState).stack
          = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] from rfl,
        stackSwap_2_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpc2, hpcI]; exact hbSwap2raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrel2 hlen2 hbSwap2 (by intro h; omega)
  -- binop : top two are y (TOS), x — value f wy wx, rewritten to f wx wy by commutativity
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
      = (base ++ [Operand.Var x]) ++ [Operand.Var x, Operand.Var y] := by simp
  have hstacktop : as3.stack = wy :: wx :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvy hvx
  have hfresh3 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var x, Operand.Var x, Operand.Var y]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h)
    · exact hfresh h
    · exact hox (by injection h)
    · exact hox (by injection h)
    · exact hoy (by injection h)
  have hbEmit : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit name]) := by rw [hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_binop_sim hrel3 hstacktop hfresh3 hps1spill hbEmit (fun h hg => hdisp as3 h hg)
  -- rewrite f wy wx -> f wx wy
  rw [hfcomm wy wx] at hrel4
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] } with
      stack := stackPush (Operand.Var out) (stackPop 2 (base ++ [Operand.Var x, Operand.Var x, Operand.Var y])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x, Operand.Var out] } := by
    rw [show base ++ [Operand.Var x, Operand.Var x, Operand.Var y] = (base ++ [Operand.Var x]) ++ [Operand.Var x, Operand.Var y] from by simp,
        stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 2] ++ [StackOp.SOEmit name])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 1]).length
           + ((executePlan [StackOp.SOSwap 2]).length + (executePlan [StackOp.SOEmit name]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega


/-- Removing a *different* key preserves a lookup. -/
theorem aremove_lookup_ne {β} (m : AssocList Operand β) (k o : Operand) (h : o ≠ k) :
    AssocList.lookup Operand β (aremove m k) o = AssocList.lookup Operand β m o := by
  rw [assocLookup_eq_listLookup, assocLookup_eq_listLookup]
  exact listLookup_filter_ne _ k o h

/-- **`emitInputPlan` sim for a pair of SPILLED vars `[spilled v, spilled w]`** — both operands
    restored from their spill slots. The head restore frees `v`; `w` (a different key) stays spilled, so
    the tail restore fires. Spill well-formedness lifts across the head via `runAsm_memory_size_mono`
    and `aremove_lookup_some` (the head only removed `v`). Completes the 2-var spill matrix (LL/LS/SL/SS). -/
theorem emitInputPlan_pair_both_spilled_sim {opc nl v w ps lo vs as prog offv offw}
    (hvw : v ≠ w)
    (hspillv : alookup' ps.spilled (Operand.Var v) = some offv)
    (hspillw : alookup' ps.spilled (Operand.Var w) = some offw)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hrel : venomAsmRel lo ps vs as)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length := by
  -- head: spilled v via restore
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                    spilled := aremove ps.spilled (Operand.Var v),
                                    alloc := freeSpillSlot offv ps.alloc } with hps1def
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore offv, StackOp.SODup 1], ps1) :=
    emitOneInput_var_spilled_eq hspillv hlivev
  have hspillw1 : alookup' ps1.spilled (Operand.Var w) = some offw := by
    rw [hps1def]
    show alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = some offw
    unfold alookup'
    rw [aremove_lookup_ne ps.spilled (Operand.Var v) (Operand.Var w)
      (by intro h; injection h with h'; exact hvw h'.symm)]
    exact hspillw
  -- tail: spilled w via restore
  set ps2 : PlanState := { ps1 with stack := ps1.stack ++ [Operand.Var w, Operand.Var w],
                                     spilled := aremove ps1.spilled (Operand.Var w),
                                     alloc := freeSpillSlot offw ps1.alloc } with hps2def
  have htail : emitOneInput opc nl (Operand.Var w) ps1 = ([StackOp.SORestore offw, StackOp.SODup 1], ps2) :=
    emitOneInput_var_spilled_eq hspillw1 hlivew
  have hfold : emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps
      = ([StackOp.SORestore offv, StackOp.SODup 1] ++ [StackOp.SORestore offw, StackOp.SODup 1], ps2) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hfold] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbHead, hbTail⟩ := asmBlockAt_append hblock
  -- run head
  obtain ⟨as1, hrunHead, hrelHead, hpcHead⟩ :=
    emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hspillv hlivev hhead hrel hspillWf hbHead
  -- lift spill wf to ps1/as1
  have hmemmono : as.memory.size ≤ as1.memory.size := runAsm_memory_size_mono hrunHead
  have hspillWf1 : ∀ o off', alookup' ps1.spilled o = some off' →
      32 ∣ off' ∧ off' + 32 ≤ as1.memory.size ∧ off' < 2 ^ 256 := by
    intro o off' ho
    have ho' : alookup' ps.spilled o = some off' := by
      rw [hps1def] at ho
      exact aremove_lookup_some ps.spilled (Operand.Var v) o off' ho
    obtain ⟨hdvd, hle, hlt⟩ := hspillWf o off' ho'
    exact ⟨hdvd, le_trans hle hmemmono, hlt⟩
  -- run tail
  have hbTail' : asmBlockAt prog as1.pc (executePlan [StackOp.SORestore offw, StackOp.SODup 1]) := by
    rw [hpcHead]; exact hbTail
  obtain ⟨as2, hrunTail, hrelTail, hpcTail⟩ :=
    emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hspillw1 hlivew htail hrelHead hspillWf1 hbTail'
  have hlen : (executePlan ([StackOp.SORestore offv, StackOp.SODup 1] ++ [StackOp.SORestore offw, StackOp.SODup 1])).length
      = (executePlan [StackOp.SORestore offv, StackOp.SODup 1]).length
        + (executePlan [StackOp.SORestore offw, StackOp.SODup 1]).length := by
    rw [executePlan_append, List.length_append]
  refine ⟨as2, ?_, hrelTail, ?_⟩
  · rw [hlen]; exact runAsm_compose hrunHead hrunTail
  · rw [hlen, hpcTail, hpcHead]; omega

/-! ### Both-spilled store — the SS 2-operand spill-aware producer (Gap C) -/

/-- **Runnable N-input all-*spilled* emission sim.** The spill-aware companion of
    `emitInputPlan_allVars_sim`: every operand is spilled, so each emits a `SORestore ; SODup` (rather
    than a single `DUP`). Running the whole plan preserves `venomAsmRel` (emission never touches the
    Venom state), advances the pc, and never shrinks asm memory. `Nodup` keeps the tail operands
    spilled after each `aremove`; spill-wf lifts across each restore via `runAsm_memory_size_mono`. The
    N-input generalisation of `emitInputPlan_pair_both_spilled_sim` — for a CALL/LOG whose operands are
    all in spill slots. -/
theorem emitInputPlan_allVars_all_spilled_sim (opc : Opcode) (nl : List String) :
    ∀ (vs : List String) (ps : PlanState) {lo : AssocList String Nat} {vst : VenomState}
      {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat},
      vs.Nodup →
      (∀ v ∈ vs, ∃ off, alookup' ps.spilled (Operand.Var v) = some off) →
      (∀ v ∈ vs, nl.contains v = true) →
      (∀ o off, alookup' ps.spilled o = some off → 32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256) →
      venomAsmRel lo ps vst as →
      asmBlockAt prog as.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1) →
      ∃ as', runAsm (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length offsetToPc prog as
               = AsmResult.AsmOK as' ∧
             venomAsmRel lo (emitInputPlan opc (vs.map Operand.Var) nl ps).2 vst as' ∧
             as'.pc = as.pc + (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length ∧
             as.memory.size ≤ as'.memory.size := by
  intro vs
  induction vs with
  | nil =>
    intro ps lo vst as prog offsetToPc _ _ _ _ hrel hblock
    refine ⟨as, ?_, ?_, ?_, le_refl _⟩
    · show runAsm (executePlan (emitInputPlan opc [] nl ps).1).length offsetToPc prog as = _
      simp [emitInputPlan, executePlan, runAsm]
    · simpa [emitInputPlan] using hrel
    · simp [emitInputPlan, executePlan]
  | cons v vs ih =>
    intro ps lo vst as prog offsetToPc hnodup hspilled hlive hwf hrel hblock
    obtain ⟨offv, hspillv⟩ := hspilled v List.mem_cons_self
    have hlivev : nl.contains v = true := hlive v List.mem_cons_self
    have hvnotin : v ∉ vs := (List.nodup_cons.mp hnodup).1
    set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                     spilled := aremove ps.spilled (Operand.Var v),
                                     alloc := freeSpillSlot offv ps.alloc } with hps1
    have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore offv, StackOp.SODup 1], ps1) :=
      emitOneInput_var_spilled_eq hspillv hlivev
    have hpeel : emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps
        = ([StackOp.SORestore offv, StackOp.SODup 1] ++ (emitInputPlan opc (vs.map Operand.Var) nl ps1).1,
           (emitInputPlan opc (vs.map Operand.Var) nl ps1).2) := by
      show (Operand.Var v :: vs.map Operand.Var).foldl
          (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps) = _
      rw [List.foldl_cons]
      simp only [List.nil_append, hhead]
      exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (vs.map Operand.Var) [StackOp.SORestore offv, StackOp.SODup 1] ps1
    rw [List.map_cons] at hblock ⊢
    rw [hpeel] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hbrest⟩ := asmBlockAt_append hblock
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
      emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hspillv hlivev hhead hrel hwf hb1
    have hmemmono1 : as.memory.size ≤ as1.memory.size := runAsm_memory_size_mono hrun1
    have hwf1 : ∀ o off, alookup' ps1.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as1.memory.size ∧ off < 2 ^ 256 := by
      intro o off ho
      rw [hps1] at ho
      have ho' : alookup' ps.spilled o = some off := aremove_lookup_some ps.spilled (Operand.Var v) o off ho
      obtain ⟨ha, hc, h2⟩ := hwf o off ho'
      exact ⟨ha, by omega, h2⟩
    have hnodup' : vs.Nodup := (List.nodup_cons.mp hnodup).2
    have hspilled' : ∀ w ∈ vs, ∃ off, alookup' ps1.spilled (Operand.Var w) = some off := by
      intro w hw
      obtain ⟨off, hoff⟩ := hspilled w (List.mem_cons_of_mem _ hw)
      have hwv : w ≠ v := by rintro rfl; exact hvnotin hw
      refine ⟨off, ?_⟩
      rw [hps1]
      exact (aremove_lookup_ne ps.spilled (Operand.Var v) (Operand.Var w)
        (by intro h; injection h with h'; exact hwv h')).trans hoff
    have hlive' : ∀ w ∈ vs, nl.contains w = true := fun w hw => hlive w (List.mem_cons_of_mem _ hw)
    have hbrest' : asmBlockAt prog as1.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps1).1) := by
      rw [hpc1]; exact hbrest
    obtain ⟨as', hrun', hrel', hpc', hmem'⟩ :=
      ih ps1 (lo := lo) (vst := vst) (as := as1) (prog := prog) (offsetToPc := offsetToPc)
        hnodup' hspilled' hlive' hwf1 hrel1 hbrest'
    refine ⟨as', ?_, hrel', ?_, ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · omega

/-- **Per-operand emittability for a mixed live/spilled input list.** Threads the growing stack and the
    shrinking spilled map: each live operand (`alookup' = none`) must sit at a DUP-reachable depth in the
    current stack (which then grows by `[v]`); each spilled operand emits a restore (the map loses its
    entry, the stack grows by `[v, v]`). The explicit threading handles a repeated operand (spilled
    first, then live off the restored copy), so no `Nodup` is needed. The mixed generalisation of
    `emitDepthsOk`. -/
def emitMixedOk (nl : List String) : List String → SpilledMap → List Operand → Prop
  | [], _, _ => True
  | v :: vs, spl, base =>
      nl.contains v = true ∧
      (match alookup' spl (Operand.Var v) with
       | none => ∃ d, stackGetDepth (Operand.Var v) base = some d ∧ d ≤ 15 ∧
                    emitMixedOk nl vs spl (base ++ [Operand.Var v])
       | some _ => emitMixedOk nl vs (aremove spl (Operand.Var v)) (base ++ [Operand.Var v, Operand.Var v]))

/-- **Runnable mixed live/spilled N-input emission sim.** The general spill-aware companion of
    `emitInputPlan_allVars_sim` (all live) and `emitInputPlan_allVars_all_spilled_sim` (all spilled):
    each operand emits either a `DUP` (live) or a `SORestore ; SODup` (spilled), as `emitMixedOk`
    prescribes. Running the whole plan preserves `venomAsmRel`, advances the pc, and never shrinks asm
    memory. Live steps preserve memory (`doDup_runAsm_mem`) and the spill map; spilled steps lift
    spill-wf across the restore (`runAsm_memory_size_mono`) and shrink the map (`aremove`) — the
    realistic CALL/LOG case. -/
theorem emitInputPlan_mixed_sim (opc : Opcode) (nl : List String) :
    ∀ (vs : List String) (ps : PlanState) {lo : AssocList String Nat} {vst : VenomState}
      {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat},
      emitMixedOk nl vs ps.spilled ps.stack →
      (∀ o off, alookup' ps.spilled o = some off → 32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256) →
      venomAsmRel lo ps vst as →
      asmBlockAt prog as.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1) →
      ∃ as', runAsm (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length offsetToPc prog as
               = AsmResult.AsmOK as' ∧
             venomAsmRel lo (emitInputPlan opc (vs.map Operand.Var) nl ps).2 vst as' ∧
             as'.pc = as.pc + (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length ∧
             as.memory.size ≤ as'.memory.size := by
  intro vs
  induction vs with
  | nil =>
    intro ps lo vst as prog offsetToPc _ _ hrel hblock
    refine ⟨as, ?_, ?_, ?_, le_refl _⟩
    · show runAsm (executePlan (emitInputPlan opc [] nl ps).1).length offsetToPc prog as = _
      simp [emitInputPlan, executePlan, runAsm]
    · simpa [emitInputPlan] using hrel
    · simp [emitInputPlan, executePlan]
  | cons v vs ih =>
    intro ps lo vst as prog offsetToPc hok hwf hrel hblock
    obtain ⟨hlivev, hbranch⟩ := hok
    rcases hsv : alookup' ps.spilled (Operand.Var v) with _ | offv
    · -- LIVE: doDup at depth d
      rw [hsv] at hbranch
      obtain ⟨d, hdepth, hsmall, hoktail⟩ := hbranch
      have hpeek : stackPeek d ps.stack = Operand.Var v := stackGetDepth_peek hdepth
      have hdup : stackDup d ps.stack = ps.stack ++ [Operand.Var v] := by unfold stackDup; rw [hpeek]
      set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v] } with hps1
      have hdo' : doDup d ps = ([StackOp.SODup (d + 1)], ps1) := by unfold doDup; rw [if_pos hsmall, hdup]
      have hemit : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SODup (d + 1)], ps1) := by
        rw [show emitOneInput opc nl (Operand.Var v) ps = doDup d ps from ?_, hdo']
        rcases hdd : doDup d ps with ⟨_, _⟩
        unfold emitOneInput
        simp only [isVarOperand, hsv, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
          if_false, hlivev, if_true, hdepth, hdd, List.nil_append]
      have hpeel : emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps
          = ([StackOp.SODup (d + 1)] ++ (emitInputPlan opc (vs.map Operand.Var) nl ps1).1,
             (emitInputPlan opc (vs.map Operand.Var) nl ps1).2) := by
        show (Operand.Var v :: vs.map Operand.Var).foldl
            (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps) = _
        rw [List.foldl_cons]; simp only [List.nil_append, hemit]
        exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (vs.map Operand.Var) [StackOp.SODup (d + 1)] ps1
      rw [List.map_cons, hpeel, executePlan_append] at hblock ⊢
      obtain ⟨hb1, hbrest⟩ := asmBlockAt_append hblock
      have hlen : d < ps.stack.length := stackGetDepth_lt_length hdepth
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ := doDup_sim hdo' hsmall hrel hlen hb1
      have hmem1 : as1.memory = as.memory := doDup_runAsm_mem hsmall (hrel.1.1 ▸ hlen) hb1 hrun1
      have hwf1 : ∀ o off, alookup' ps1.spilled o = some off →
          32 ∣ off ∧ off + 32 ≤ as1.memory.size ∧ off < 2 ^ 256 := by
        intro o off ho; rw [hps1] at ho; obtain ⟨ha, hc, h2⟩ := hwf o off ho
        exact ⟨ha, by rw [hmem1]; exact hc, h2⟩
      have hoktail' : emitMixedOk nl vs ps1.spilled ps1.stack := by rw [hps1]; exact hoktail
      have hbrest' : asmBlockAt prog as1.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps1).1) := by
        rw [hpc1]; exact hbrest
      obtain ⟨as', hrun', hrel', hpc', hmem'⟩ :=
        ih ps1 (lo := lo) (vst := vst) (as := as1) (prog := prog) (offsetToPc := offsetToPc)
          hoktail' hwf1 hrel1 hbrest'
      refine ⟨as', ?_, hrel', ?_, ?_⟩
      · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
      · rw [List.length_append, hpc', hpc1]; omega
      · rw [hmem1] at hmem'; omega
    · -- SPILLED: restore + dup
      rw [hsv] at hbranch
      set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                       spilled := aremove ps.spilled (Operand.Var v),
                                       alloc := freeSpillSlot offv ps.alloc } with hps1
      have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore offv, StackOp.SODup 1], ps1) :=
        emitOneInput_var_spilled_eq hsv hlivev
      have hpeel : emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps
          = ([StackOp.SORestore offv, StackOp.SODup 1] ++ (emitInputPlan opc (vs.map Operand.Var) nl ps1).1,
             (emitInputPlan opc (vs.map Operand.Var) nl ps1).2) := by
        show (Operand.Var v :: vs.map Operand.Var).foldl
            (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps) = _
        rw [List.foldl_cons]; simp only [List.nil_append, hhead]
        exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (vs.map Operand.Var) [StackOp.SORestore offv, StackOp.SODup 1] ps1
      rw [List.map_cons, hpeel, executePlan_append] at hblock ⊢
      obtain ⟨hb1, hbrest⟩ := asmBlockAt_append hblock
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hsv hlivev hhead hrel hwf hb1
      have hmemmono1 : as.memory.size ≤ as1.memory.size := runAsm_memory_size_mono hrun1
      have hwf1 : ∀ o off, alookup' ps1.spilled o = some off →
          32 ∣ off ∧ off + 32 ≤ as1.memory.size ∧ off < 2 ^ 256 := by
        intro o off ho; rw [hps1] at ho
        have ho' : alookup' ps.spilled o = some off := aremove_lookup_some ps.spilled (Operand.Var v) o off ho
        obtain ⟨ha, hc, h2⟩ := hwf o off ho'; exact ⟨ha, by omega, h2⟩
      have hoktail' : emitMixedOk nl vs ps1.spilled ps1.stack := by rw [hps1]; exact hbranch
      have hbrest' : asmBlockAt prog as1.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps1).1) := by
        rw [hpc1]; exact hbrest
      obtain ⟨as', hrun', hrel', hpc', hmem'⟩ :=
        ih ps1 (lo := lo) (vst := vst) (as := as1) (prog := prog) (offsetToPc := offsetToPc)
          hoktail' hwf1 hrel1 hbrest'
      refine ⟨as', ?_, hrel', ?_, ?_⟩
      · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
      · rw [List.length_append, hpc', hpc1]; omega
      · omega



/-- All-live depth facts imply the mixed-emission spec (the map never fires). Bridges
    `emitDepthsOk` into `emitMixedOk` so the all-live TAIL of a head-spilled N-ary emission can
    reuse the depth-threading toolkit. -/
theorem emitMixedOk_of_depthsOk {nl : List String} :
    ∀ {vs : List String} {dists : List Nat} {spl : SpilledMap} {stk : List Operand},
      (∀ v ∈ vs, alookup' spl (Operand.Var v) = none) →
      emitDepthsOk nl vs dists stk →
      emitMixedOk nl vs spl stk := by
  intro vs
  induction vs with
  | nil => intro dists spl stk _ _; trivial
  | cons v vs ih =>
    intro dists spl stk hns hd
    cases dists with
    | nil => exact hd.elim
    | cons d ds =>
      obtain ⟨hlive, hdepth, hsmall, htail⟩ := hd
      have hnsv : alookup' spl (Operand.Var v) = none := hns v List.mem_cons_self
      refine ⟨hlive, ?_⟩
      simp only [hnsv]
      exact ⟨d, hdepth, hsmall, ih (fun w hw => hns w (List.mem_cons_of_mem v hw)) htail⟩

/-- **Closed form of the head-spilled N-ary emission**: the first-emitted operand `v` is restored
    from its slot (+ keep-alive DUP), the remaining distinct live vars DUP at their growing-stack
    depths — stack grows by `[v, v] ++ rest`, `v` leaves the map, its slot is freed. The mixed
    (1-spilled, N-live) generalization of `emitInputPlan_allVars_eq`. -/
theorem emitInputPlan_headSpilled_eq (opc : Opcode) (nl : List String)
    {v : String} {rest : List String} {dists : List Nat} {ps : PlanState} {off : Nat}
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nl.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nl rest dists (ps.stack ++ [Operand.Var v, Operand.Var v])) :
    emitInputPlan opc ((v :: rest).map Operand.Var) nl ps
      = ([StackOp.SORestore off, StackOp.SODup 1] ++ dists.map (fun d => StackOp.SODup (d + 1)),
         { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v] ++ rest.map Operand.Var,
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                   spilled := aremove ps.spilled (Operand.Var v),
                                   alloc := freeSpillSlot off ps.alloc } with hps1
  have hhead : emitOneInput opc nl (Operand.Var v) ps
      = ([StackOp.SORestore off, StackOp.SODup 1], ps1) :=
    emitOneInput_var_spilled_eq hspill hlive
  have hpeel : emitInputPlan opc (Operand.Var v :: rest.map Operand.Var) nl ps
      = ([StackOp.SORestore off, StackOp.SODup 1]
          ++ (emitInputPlan opc (rest.map Operand.Var) nl ps1).1,
         (emitInputPlan opc (rest.map Operand.Var) nl ps1).2) := by
    show (Operand.Var v :: rest.map Operand.Var).foldl
        (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1,
          (emitOneInput opc nl op acc.2).2)) ([], ps) = _
    rw [List.foldl_cons]
    simp only [List.nil_append, hhead]
    exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (rest.map Operand.Var)
      [StackOp.SORestore off, StackOp.SODup 1] ps1
  have hns1 : ∀ w ∈ rest, alookup' ps1.spilled (Operand.Var w) = none := by
    intro w hw
    show alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none
    exact aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var w) (hns w hw)
  have htail := emitInputPlan_allVars_eq opc nl rest dists ps1 hns1
    (by show emitDepthsOk nl rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]); exact hd)
  rw [List.map_cons, hpeel, htail]

/-- **Head-spilled LOG plan reduction**: the first-emitted operand is restored (its kept copy
    lands just below the emitted run), the remaining live operands DUP — the emitted layout is
    ALREADY positioned over `base ++ [v]` (`reorderPlan_allVars_nil`), the `LOGn` pops the inputs,
    and the block nets `+1` (the kept restore). The first spilled VARIABLE-ARITY plan reduction. -/
theorem genRegularInstPlan_log_headspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {v : String} {rest : List String} {dists : List Nat} {tc : bytes32}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnd : (v :: rest).Nodup)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists (ps.stack ++ [Operand.Var v, Operand.Var v])) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
          ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
             stack := base ++ [Operand.Var v] }) := by
  have hcL : isCommutative Opcode.LOG = false := rfl
  have hjL : ¬ (Opcode.LOG = Opcode.JMP) := by decide
  have hpvar := emitInputPlan_headSpilled_eq inst.opcode nextLiveness hspill hlive hns hd
  unfold generateRegularInstPlan
  simp only [hopc, hhead, hcompute, houts]
  rcases hemit : emitInputPlan Opcode.LOG ((v :: rest).map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan Opcode.LOG ((v :: rest).map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = (base ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var := by
    rw [← h2, show emitInputPlan Opcode.LOG ((v :: rest).map Operand.Var) nextLiveness ps
        = emitInputPlan inst.opcode ((v :: rest).map Operand.Var) nextLiveness ps from by
      rw [hopc], hpvar, hstack0]
    simp
  have hreo : reorderPlan (Operand.Var v :: rest.map Operand.Var) ps1 = ([], ps1) :=
    reorderPlan_allVars_nil (base ++ [Operand.Var v]) (v :: rest) ps1 hps1' hnd
  have hpop : stackPop (rest.length + 1)
        (base ++ Operand.Var v :: Operand.Var v :: rest.map Operand.Var)
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((v :: rest).map Operand.Var)
    rw [List.length_map, show (v :: rest).length = rest.length + 1 from rfl] at h
    rw [show base ++ Operand.Var v :: Operand.Var v :: rest.map Operand.Var
          = (base ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var from by simp]
    exact h
  simp [hcL, hjL, hreo, hps1', hpop, generateEmitOps_log hopc, List.append_assoc]

/-- **Runnable head-spilled LOG sim** — the first spilled VARIABLE-ARITY op end-to-end: restore
    the spilled first-emitted operand (keep-alive copy stays below the run), DUP the remaining
    live operands, `LOGn` pops the inputs — `venomAsmRel` is preserved across the event append
    and the block nets `+1`. Composes `emitInputPlan_mixed_sim` (the restore + DUPs) with
    `emit_log_sim`; the reorder is a no-op by `reorderPlan_allVars_nil` over `base ++ [v]`. -/
theorem genRegularInstPlan_log_headspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {v : String} {rest : List String} {dists : List Nat} {tc : bytes32} {base : List Operand}
    {off : Nat} {n : Nat} {offset size : bytes32} {topics : List bytes32}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnd : (v :: rest).Nodup)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]))
    (hlenes : (v :: rest).length = n + 2)
    (htc : tc.toNat = n)
    (htlen : topics.length = n)
    (hvals : ((v :: rest).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) (hn : n ≤ 4)
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] } as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_log_headspilled_eq hopc hhead hcompute houts hstack0 hnd hspill hlive
      hns hd, hcompute] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode ((v :: rest).map Operand.Var) nextLiveness ps).2
    with hps1def
  have hpvar := emitInputPlan_headSpilled_eq inst.opcode nextLiveness hspill hlive hns hd
  have hps1stack : ps1.stack
      = (base ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var := by
    rw [hps1def, hpvar, hstack0]; simp
  have hps1fnEom : ps1.alloc.fnEom = ps.alloc.fnEom := by
    rw [hps1def, hpvar]
    show (freeSpillSlot off ps.alloc).fnEom = ps.alloc.fnEom
    rfl
  have hok : emitMixedOk nextLiveness (v :: rest) ps.spilled ps.stack := by
    refine ⟨hlive, ?_⟩
    simp only [hspill]
    exact emitMixedOk_of_depthsOk
      (fun w hw => aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var w) (hns w hw))
      (by rw [hstack0] at hd ⊢; exact hd)
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmono⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness (v :: rest) ps hok hspillWf hrel hbI
  have hstacktop : as1.stack
      = offset :: size :: topics ++ as1.stack.drop ((v :: rest).map Operand.Var).length :=
    venomAsmRel_asmStack_topVals hrelI hps1stack hvals
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]) := by
    rw [hpcI, ← htc]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_log_sim hrelI hstacktop htlen (le_trans hcov hmono)
      (by rw [hps1fnEom]; exact hbelow) hsize hn hbE'
  have hps5 : ({ ps1 with stack := stackPop (n + 2) ps1.stack } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var v] } := by
    rw [hps1stack, ← hlenes]
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((v :: rest).map Operand.Var)
    rw [List.length_map] at h
    rw [h]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [List.length_append, htc]; exact runAsm_compose hrunI hrunE
  · rw [List.length_append, htc, hpcE, hpcI]; omega

/-- **Head-spilled CALL plan reduction**: the first-emitted operand `v` is restored from its slot
    (keep-alive copy below the run), the remaining six DUP — the layout is ALREADY positioned over
    `base ++ [v]` (`reorderPlan_allVars_nil`), CALL pops the seven and pushes the success flag —
    intermediate `base ++ [v, out]` (net +2). The spilled-CALL analogue of
    `genRegularInstPlan_call_eq`; NO reorder theory needed (the `p = 0` family). -/
theorem genRegularInstPlan_call_headspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {v : String} {rest : List String} {dists : List Nat} {out : String}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : (v :: rest).Nodup)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]))
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "CALL"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var v, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var v, Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_headSpilled_eq inst.opcode nextLiveness hspill hlivev hns hd
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode ((v :: rest).map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode ((v :: rest).map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = (base ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var := by
    rw [← h2, hpvar, hstack0]; simp
  have hreo : reorderPlan (Operand.Var v :: rest.map Operand.Var) ps1 = ([], ps1) :=
    reorderPlan_allVars_nil (base ++ [Operand.Var v]) (v :: rest) ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop (rest.length + 1)
        (base ++ Operand.Var v :: Operand.Var v :: rest.map Operand.Var)
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((v :: rest).map Operand.Var)
    rw [List.length_map, show (v :: rest).length = rest.length + 1 from rfl] at h
    rw [show base ++ Operand.Var v :: Operand.Var v :: rest.map Operand.Var
          = (base ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var from by simp]
    exact h
  simp [generateEmitOps_evmName hname, hreo, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- **Full-relation head-spilled CALL block core**: restore the spilled first-emitted operand
    (keep-alive copy stays), DUP the six live ones, run CALL — concluding the COMPLETE
    `venomAsmRel` at `{ps1 with stack := base ++ [v, out]}` (net +2) and the writeback state.
    The spilled-config sibling of `call_block_emit_rel_full`; the emitted layout is positioned
    over `base ++ [v]`, so no reorder runs. -/
theorem call_block_emit_rel_full_headspilled {lo : AssocList String Nat} {vs : VenomState}
    {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out v : String} {rest : List String} {dists : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nl.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nl rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]))
    (hvals : List.map (operandVal vs lo) ((v :: rest).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v) (houtrest : out ∉ rest)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var v, Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "CALL"])).length := by
  have hemiteq := emitInputPlan_headSpilled_eq Opcode.CALL nl hspill hlivev hns hd
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  have hok : emitMixedOk nl (v :: rest) ps.spilled ps.stack := by
    refine ⟨hlivev, ?_⟩
    simp only [hspill]
    exact emitMixedOk_of_depthsOk
      (fun w hw => aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var w) (hns w hw)) hd
  obtain ⟨as1, hrunE, hrelE, hpcE, hmono⟩ :=
    emitInputPlan_mixed_sim (offsetToPc := offsetToPc) Opcode.CALL nl (v :: rest) ps hok
      hspillWf hrel hbI
  have hps'stack : (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.stack
      = (ps.stack ++ [Operand.Var v]) ++ (v :: rest).map Operand.Var := by
    rw [hemiteq]; simp
  have hps'spill : (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.spilled
      = aremove ps.spilled (Operand.Var v) := by rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack ++ [Operand.Var v])
    (ops := (v :: rest).map Operand.Var) (vals := vals) hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : ((v :: rest).map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : (v :: rest).length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  have halloc1 : (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.alloc
      = freeSpillSlot off ps.alloc := by rw [hemiteq]
  have hmemrel1' : memoryRel ps.alloc vs.memory as1.memory := by
    rw [halloc1] at hmemrel1
    exact hmemrel1
  have hro2 : rOff.toNat ≤ as1.memory.size := by omega
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 (!as1.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1' hargs haszlt]
    exact hcall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    call_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1' hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  have hpcadv : s''.pc = as1.pc + 1 := by
    have hcalleq : asmCall as1 = AsmResult.AsmOK s'' := hasmOK
    unfold asmCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h2 | h2
      · intro hc; rw [hc] at h2; exact hfreshS h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        intro hc; rw [hc] at h2
        injection h2 with h2'
        exact houtv h2'
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      subst hwe'
      simp only [List.mem_cons] at hw
      rcases hw with h3 | h3
      · exact houtv h3
      · exact houtrest h3
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 7 ≤ (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 7 (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.stack
      = ps.stack ++ [Operand.Var v] := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top (ps.stack ++ [Operand.Var v]) ((v :: rest).map Operand.Var)
  rw [hpop7] at hStkFinal
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.spilled s''.memory := by
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off' hlook
      rw [hps'spill] at hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc] at hlook
      rw [aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var out) hspill_out] at hlook
      simp at hlook
    · intro op off' hlook
      rw [hps'spill] at hlook
      have hge : ps.alloc.fnEom ≤ off' :=
        hspillReg op off' (aremove_lookup_some ps.spilled (Operand.Var v) op off' hlook)
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off' 32 h32
      intro k hk
      have := hframe' (off' + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var v, Operand.Var out]) s''.stack
      rw [hstk']
      have hassoc : ps.stack ++ [Operand.Var v, Operand.Var out]
          = (ps.stack ++ [Operand.Var v]) ++ [Operand.Var out] := by simp
      rw [hassoc]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      have halloc : (emitInputPlan Opcode.CALL ((v :: rest).map Operand.Var) nl ps).2.alloc
          = freeSpillSlot off ps.alloc := by rw [hemiteq]
      rw [halloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv, hpcE]
    rfl

/-- **The head-spilled CALL producer sim** — the first SPILLED external-call config end-to-end:
    the spilled first-emitted operand is restored (net +2 with the success flag), the whole
    generated plan preserves the complete `venomAsmRel` against the `stepExternalCall` writeback.
    No reorder theory involved (the `p = 0` positioned family). -/
theorem genRegularInstPlan_call_headspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {v : String} {rest : List String} {dists : List Nat}
    {out : String} {base : List Operand} {off : Nat}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : (v :: rest).Nodup)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]))
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) ((v :: rest).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v) (houtrest : out ∉ rest)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := base ++ [Operand.Var v, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var v, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_call_headspilled_eq hopc hcompute houts hstack0 hnd hspill hlivev hns
      hd hlive, hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    call_block_emit_rel_full_headspilled (offsetToPc := offsetToPc) hopc heval houts hspill
      hlivev hns hd hvals hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtv houtrest
      hspill_out hspillReg hspillWf hcall hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-- The N-input emission splits over an operand-list append. -/
theorem emitInputPlan_append (opc : Opcode) (nl : List String) (l1 l2 : List Operand)
    (ps : PlanState) :
    emitInputPlan opc (l1 ++ l2) nl ps
      = ((emitInputPlan opc l1 nl ps).1 ++ (emitInputPlan opc l2 nl (emitInputPlan opc l1 nl ps).2).1,
         (emitInputPlan opc l2 nl (emitInputPlan opc l1 nl ps).2).2) := by
  show (l1 ++ l2).foldl _ ([], ps) = _
  rw [List.foldl_append]
  rw [show (l1.foldl (fun (acc : List StackOp × PlanState) op =>
        (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps))
      = ((emitInputPlan opc l1 nl ps).1, (emitInputPlan opc l1 nl ps).2) from rfl]
  exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) l2
    (emitInputPlan opc l1 nl ps).1 (emitInputPlan opc l1 nl ps).2

/-- **Closed form of the last-spilled N-ary emission**: the live prefix DUPs at its depth chain,
    then the spilled last-emitted operand restores (+ keep-alive DUP) — stack grows by
    `rest ++ [v, v]`, `v` leaves the map, its slot is freed. The `q = 0` sibling of
    `emitInputPlan_headSpilled_eq`. -/
theorem emitInputPlan_lastSpilled_eq (opc : Opcode) (nl : List String)
    {rest : List String} {v : String} {dists : List Nat} {ps : PlanState} {off : Nat}
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nl rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nl.contains v = true) :
    emitInputPlan opc ((rest ++ [v]).map Operand.Var) nl ps
      = (dists.map (fun d => StackOp.SODup (d + 1)) ++ [StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := (ps.stack ++ rest.map Operand.Var) ++ [Operand.Var v, Operand.Var v],
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
  rw [List.map_append, emitInputPlan_append,
      emitInputPlan_allVars_eq opc nl rest dists ps hns hd]
  have hlast : emitInputPlan opc ([v].map Operand.Var) nl
      ({ ps with stack := ps.stack ++ rest.map Operand.Var } : PlanState)
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := (ps.stack ++ rest.map Operand.Var) ++ [Operand.Var v, Operand.Var v],
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
    show ([Operand.Var v]).foldl _ ([], _) = _
    rw [List.foldl_cons, List.foldl_nil]
    simp only [List.nil_append,
      emitOneInput_var_spilled_eq (ps := { ps with stack := ps.stack ++ rest.map Operand.Var })
        (show alookup' ({ ps with stack := ps.stack ++ rest.map Operand.Var } : PlanState).spilled
            (Operand.Var v) = some off from hspill) hlive]
  rw [hlast]

/-- All-live depth facts + a trailing spilled operand give the mixed-emission spec for the
    snoc list. -/
theorem emitMixedOk_snoc_spilled {nl : List String} :
    ∀ {rest : List String} {dists : List Nat} {spl : SpilledMap} {stk : List Operand}
      {v : String} {off : Nat},
      (∀ w ∈ rest, alookup' spl (Operand.Var w) = none) →
      emitDepthsOk nl rest dists stk →
      alookup' spl (Operand.Var v) = some off →
      nl.contains v = true →
      emitMixedOk nl (rest ++ [v]) spl stk := by
  intro rest
  induction rest with
  | nil =>
    intro dists spl stk v off _ _ hspill hlive
    refine ⟨hlive, ?_⟩
    simp only [hspill]
    trivial
  | cons w rest' ih =>
    intro dists spl stk v off hns hd hspill hlive
    cases dists with
    | nil => exact hd.elim
    | cons d ds =>
      obtain ⟨hlivew, hdepth, hsmall, htail⟩ := hd
      have hnsw : alookup' spl (Operand.Var w) = none := hns w List.mem_cons_self
      refine ⟨hlivew, ?_⟩
      simp only [hnsw]
      exact ⟨d, hdepth, hsmall,
        ih (fun u hu => hns u (List.mem_cons_of_mem w hu)) htail hspill hlive⟩

/-- **Last-spilled LOG plan reduction**: live prefix DUPs, spilled last operand restored, the
    general `SWAP N; …; SWAP 1` doubles-reorder (`reorderPlan_lastspilled`), `LOGn` pops the
    inputs — net `+1` (the kept restore). The FIRST consumer of the general reorder atoms. -/
theorem genRegularInstPlan_log_lastspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {rest : List String} {v : String} {dists : List Nat} {tc : bytes32}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hrestne : rest ≠ [])
    (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nextLiveness.contains v = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
          ++ descSwaps (rest.length + 1)
          ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
             stack := base ++ [Operand.Var v] }) := by
  have hcL : isCommutative Opcode.LOG = false := rfl
  have hjL : ¬ (Opcode.LOG = Opcode.JMP) := by decide
  have hpvar := emitInputPlan_lastSpilled_eq Opcode.LOG nextLiveness hns hd hspill hlive
  unfold generateRegularInstPlan
  simp only [hopc, hhead, hcompute, houts, List.map_append, List.map_cons, List.map_nil]
  rcases hemit : emitInputPlan Opcode.LOG (rest.map Operand.Var ++ [Operand.Var v]) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan Opcode.LOG (rest.map Operand.Var ++ [Operand.Var v]) nextLiveness ps).2
      = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ rest.map Operand.Var ++ [Operand.Var v, Operand.Var v] := by
    rw [← h2, show rest.map Operand.Var ++ [Operand.Var v] = (rest ++ [v]).map Operand.Var from by
        simp, hpvar, hstack0]
  have hndm : (rest.map Operand.Var).Nodup := hnd.map (fun _ _ h => Operand.Var.inj h)
  have hvm : Operand.Var v ∉ rest.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvrest (hwe' ▸ hw)
  have hreo := reorderPlan_lastspilled base (rest.map Operand.Var) (Operand.Var v) ps1
    (by rw [hps1']) (by simpa using hrestne) (by simpa using h16) hvm hndm
  have hreo' : reorderPlan (rest.map Operand.Var ++ [Operand.Var v]) ps1
      = (descSwaps (rest.length + 1),
         { ps1 with stack := base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]) }) := by
    rw [hreo]
    simp
  have hpop : stackPop (rest.length + 1)
        (base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]))
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((rest ++ [v]).map Operand.Var)
    rw [List.length_map, show (rest ++ [v]).length = rest.length + 1 from by simp] at h
    rw [show base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v])
          = (base ++ [Operand.Var v]) ++ (rest ++ [v]).map Operand.Var from by simp]
    exact h
  simp [hcL, hjL, hreo', hpop, generateEmitOps_log hopc, List.append_assoc]
/-- A live-prefix extension of the mixed-emission spec: prepend depth-checked live legs to any
    mixed tail. -/
theorem emitMixedOk_append_live {nl : List String} :
    ∀ {pre : List String} {dists : List Nat} {tail : List String} {spl : SpilledMap}
      {stk : List Operand},
      (∀ w ∈ pre, alookup' spl (Operand.Var w) = none) →
      emitDepthsOk nl pre dists stk →
      emitMixedOk nl tail spl (stk ++ pre.map Operand.Var) →
      emitMixedOk nl (pre ++ tail) spl stk := by
  intro pre
  induction pre with
  | nil =>
    intro dists tail spl stk _ _ htail
    simpa using htail
  | cons w pre' ih =>
    intro dists tail spl stk hns hd htail
    cases dists with
    | nil => exact hd.elim
    | cons d ds =>
      obtain ⟨hlivew, hdepth, hsmall, hdtail⟩ := hd
      have hnsw : alookup' spl (Operand.Var w) = none := hns w List.mem_cons_self
      refine ⟨hlivew, ?_⟩
      simp only [hnsw]
      refine ⟨d, hdepth, hsmall, ?_⟩
      exact ih (fun u hu => hns u (List.mem_cons_of_mem w hu)) hdtail
        (by rw [show stk ++ (w :: pre').map Operand.Var
              = (stk ++ [Operand.Var w]) ++ pre'.map Operand.Var from by simp] at htail
            exact htail)

/-- **Closed form of the mid-spilled N-ary emission**: live prefix DUPs, the spilled middle
    operand restores (+ keep-alive DUP), the live suffix DUPs over the grown stack — the layout
    of `reorderPlan_midspilled`. -/
theorem emitInputPlan_midSpilled_eq (opc : Opcode) (nl : List String)
    {pre post : List String} {v : String} {dists dists' : List Nat} {ps : PlanState} {off : Nat}
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nl pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nl.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nl post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v])) :
    emitInputPlan opc ((pre ++ [v] ++ post).map Operand.Var) nl ps
      = (dists.map (fun d => StackOp.SODup (d + 1))
          ++ ([StackOp.SORestore off, StackOp.SODup 1]
            ++ dists'.map (fun d => StackOp.SODup (d + 1))),
         { ps with stack := ((ps.stack ++ pre.map Operand.Var)
                     ++ [Operand.Var v, Operand.Var v]) ++ post.map Operand.Var,
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
  rw [show (pre ++ [v] ++ post).map Operand.Var
        = pre.map Operand.Var ++ (Operand.Var v :: post.map Operand.Var) from by simp,
      emitInputPlan_append,
      emitInputPlan_allVars_eq opc nl pre dists ps hnspre hdpre]
  have hmid : emitInputPlan opc (Operand.Var v :: post.map Operand.Var) nl
      ({ ps with stack := ps.stack ++ pre.map Operand.Var } : PlanState)
      = ([StackOp.SORestore off, StackOp.SODup 1]
          ++ dists'.map (fun d => StackOp.SODup (d + 1)),
         { ps with stack := ((ps.stack ++ pre.map Operand.Var)
                     ++ [Operand.Var v, Operand.Var v]) ++ post.map Operand.Var,
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
    rw [show (Operand.Var v :: post.map Operand.Var)
          = [Operand.Var v] ++ post.map Operand.Var from rfl,
        emitInputPlan_append]
    have hv : emitInputPlan opc [Operand.Var v] nl
        ({ ps with stack := ps.stack ++ pre.map Operand.Var } : PlanState)
        = ([StackOp.SORestore off, StackOp.SODup 1],
           { ps with stack := (ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v],
                     spilled := aremove ps.spilled (Operand.Var v),
                     alloc := freeSpillSlot off ps.alloc }) := by
      show ([Operand.Var v]).foldl _ ([], _) = _
      rw [List.foldl_cons, List.foldl_nil]
      simp only [List.nil_append,
        emitOneInput_var_spilled_eq
          (ps := { ps with stack := ps.stack ++ pre.map Operand.Var })
          (show alookup' ({ ps with stack := ps.stack ++ pre.map Operand.Var } : PlanState).spilled
              (Operand.Var v) = some off from hspill) hlivev]
    rw [hv,
        emitInputPlan_allVars_eq opc nl post dists'
          ({ ps with stack := (ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v],
                     spilled := aremove ps.spilled (Operand.Var v),
                     alloc := freeSpillSlot off ps.alloc } : PlanState)
          hnspost hdpost]
  rw [hmid]

/-- **Mid-spilled LOG plan reduction**: live prefix + spilled middle restore + live suffix, the
    general `SWAP N; …; SWAP q; SWAP N` doubles-reorder (`reorderPlan_midspilled`), `LOGn` —
    net `+1`. Completes the spilled variable-arity trilogy (head / last / mid). -/
theorem genRegularInstPlan_log_midspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {pre post : List String} {v : String} {dists dists' : List Nat} {tc : bytes32}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nextLiveness pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nextLiveness post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v])) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
          ++ ((StackOp.SOSwap (pre.length + post.length + 1)
                :: StackOp.SOSwap (pre.length + post.length)
                :: descRun (post.length + 1) (pre.length - 1))
              ++ [StackOp.SOSwap post.length]
              ++ [StackOp.SOSwap (pre.length + post.length + 1)])
          ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
             stack := base ++ [Operand.Var v] }) := by
  have hcL : isCommutative Opcode.LOG = false := rfl
  have hjL : ¬ (Opcode.LOG = Opcode.JMP) := by decide
  have hpvar := emitInputPlan_midSpilled_eq Opcode.LOG nextLiveness hnspre hdpre hspill hlivev
    hnspost hdpost
  unfold generateRegularInstPlan
  simp only [hopc, hhead, hcompute, houts, List.map_append, List.map_cons, List.map_nil]
  rcases hemit : emitInputPlan Opcode.LOG
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan Opcode.LOG
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) nextLiveness ps).2
      = ps1 := by rw [hemit]
  have hps1' : ps1.stack
      = base ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v] ++ post.map Operand.Var := by
    rw [← h2, show pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var
          = (pre ++ [v] ++ post).map Operand.Var from by simp, hpvar, hstack0]
  have hndmpre : (pre.map Operand.Var).Nodup := hndpre.map (fun _ _ h => Operand.Var.inj h)
  have hndmpost : (post.map Operand.Var).Nodup := hndpost.map (fun _ _ h => Operand.Var.inj h)
  have hvmpre : Operand.Var v ∉ pre.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpre (hwe' ▸ hw)
  have hvmpost : Operand.Var v ∉ post.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpost (hwe' ▸ hw)
  have hdisjm : ∀ x ∈ pre.map Operand.Var, x ∉ post.map Operand.Var := by
    intro x hx hx2
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hx2
    rw [← hwe] at hue
    injection hue with hue'
    exact hdisj w hw (hue' ▸ hu)
  have hreo := reorderPlan_midspilled base (pre.map Operand.Var) (post.map Operand.Var)
    (Operand.Var v) ps1
    (by rw [hps1']) (by simpa using hprene) (by simpa using hpostne)
    (by simpa using h16) hvmpre hvmpost hndmpre hndmpost hdisjm
  have hreo' : reorderPlan (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) ps1
      = ((StackOp.SOSwap (pre.length + post.length + 1)
            :: StackOp.SOSwap (pre.length + post.length)
            :: descRun (post.length + 1) (pre.length - 1))
          ++ [StackOp.SOSwap post.length]
          ++ [StackOp.SOSwap (pre.length + post.length + 1)],
         { ps1 with stack := base ++ Operand.Var v
             :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) }) := by
    rw [show pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var
          = pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var from by simp,
        hreo]
    simp
  have hpop : stackPop (pre.length + (post.length + 1))
        (base ++ Operand.Var v :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var))
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v])
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var)
    rw [show (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var).length
          = pre.length + (post.length + 1) from by simp] at h
    rw [show base ++ Operand.Var v
          :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var)
          = (base ++ [Operand.Var v])
            ++ (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) from by simp]
    exact h
  simp [hcL, hjL, h2, hreo', hpop, generateEmitOps_log hopc, List.append_assoc]

/-- **Mid-spilled CALL plan reduction**: live prefix + spilled middle restore + live suffix,
    the general doubles-reorder (`reorderPlan_midspilled`), `CALL`, success push — net `+2`.
    The non-positioned spilled external-call config, over the general atoms. -/
theorem genRegularInstPlan_call_midspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {pre post : List String} {v : String} {dists dists' : List Nat} {out : String}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nextLiveness pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nextLiveness post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]))
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
          ++ ((StackOp.SOSwap (pre.length + post.length + 1)
                :: StackOp.SOSwap (pre.length + post.length)
                :: descRun (post.length + 1) (pre.length - 1))
              ++ [StackOp.SOSwap post.length]
              ++ [StackOp.SOSwap (pre.length + post.length + 1)])
          ++ [StackOp.SOEmit "CALL"]
          ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                  stack := base ++ [Operand.Var v, Operand.Var out] }).1,
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var v, Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_midSpilled_eq inst.opcode nextLiveness hnspre hdpre hspill hlivev
    hnspost hdpost
  unfold generateRegularInstPlan
  simp only [hcompute, houts, List.map_append, List.map_cons, List.map_nil]
  rcases hemit : emitInputPlan inst.opcode
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) nextLiveness ps).2
      = ps1 := by rw [hemit]
  have hps1' : ps1.stack
      = base ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v] ++ post.map Operand.Var := by
    rw [← h2, show pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var
          = (pre ++ [v] ++ post).map Operand.Var from by simp, hpvar, hstack0]
  have hndmpre : (pre.map Operand.Var).Nodup := hndpre.map (fun _ _ h => Operand.Var.inj h)
  have hndmpost : (post.map Operand.Var).Nodup := hndpost.map (fun _ _ h => Operand.Var.inj h)
  have hvmpre : Operand.Var v ∉ pre.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpre (hwe' ▸ hw)
  have hvmpost : Operand.Var v ∉ post.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpost (hwe' ▸ hw)
  have hdisjm : ∀ x ∈ pre.map Operand.Var, x ∉ post.map Operand.Var := by
    intro x hx hx2
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hx2
    rw [← hwe] at hue
    injection hue with hue'
    exact hdisj w hw (hue' ▸ hu)
  have hreo := reorderPlan_midspilled base (pre.map Operand.Var) (post.map Operand.Var)
    (Operand.Var v) ps1
    (by rw [hps1']) (by simpa using hprene) (by simpa using hpostne)
    (by simpa using h16) hvmpre hvmpost hndmpre hndmpost hdisjm
  have hreo' : reorderPlan (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) ps1
      = ((StackOp.SOSwap (pre.length + post.length + 1)
            :: StackOp.SOSwap (pre.length + post.length)
            :: descRun (post.length + 1) (pre.length - 1))
          ++ [StackOp.SOSwap post.length]
          ++ [StackOp.SOSwap (pre.length + post.length + 1)],
         { ps1 with stack := base ++ Operand.Var v
             :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) }) := by
    rw [show pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var
          = pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var from by simp,
        hreo]
    simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop (pre.length + (post.length + 1))
        (base ++ Operand.Var v :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var))
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v])
      (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var)
    rw [show (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var).length
          = pre.length + (post.length + 1) from by simp] at h
    rw [show base ++ Operand.Var v
          :: (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var)
          = (base ++ [Operand.Var v])
            ++ (pre.map Operand.Var ++ Operand.Var v :: post.map Operand.Var) from by simp]
    exact h
  simp [generateEmitOps_evmName hname, h2, hreo', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp, List.append_assoc]

/-- **Last-spilled CALL plan reduction**: live prefix DUPs, spilled last-emitted operand
    restored, the general `SWAP N; …; SWAP 1` doubles-reorder (`reorderPlan_lastspilled`),
    `CALL`, success push — net `+2`. The `q = 0` external-call config over the general atoms. -/
theorem genRegularInstPlan_call_lastspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {rest : List String} {v : String} {dists : List Nat} {out : String}
    {base : List Operand} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hrestne : rest ≠ [])
    (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
          ++ descSwaps (rest.length + 1)
          ++ [StackOp.SOEmit "CALL"]
          ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                  stack := base ++ [Operand.Var v, Operand.Var out] }).1,
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var v, Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_lastSpilled_eq inst.opcode nextLiveness hns hd hspill hlivev
  unfold generateRegularInstPlan
  simp only [hcompute, houts, List.map_append, List.map_cons, List.map_nil]
  rcases hemit : emitInputPlan inst.opcode (rest.map Operand.Var ++ [Operand.Var v]) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (rest.map Operand.Var ++ [Operand.Var v]) nextLiveness ps).2
      = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ rest.map Operand.Var ++ [Operand.Var v, Operand.Var v] := by
    rw [← h2, show rest.map Operand.Var ++ [Operand.Var v] = (rest ++ [v]).map Operand.Var from by
        simp, hpvar, hstack0]
  have hndm : (rest.map Operand.Var).Nodup := hnd.map (fun _ _ h => Operand.Var.inj h)
  have hvm : Operand.Var v ∉ rest.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvrest (hwe' ▸ hw)
  have hreo := reorderPlan_lastspilled base (rest.map Operand.Var) (Operand.Var v) ps1
    (by rw [hps1']) (by simpa using hrestne) (by simpa using h16) hvm hndm
  have hreo' : reorderPlan (rest.map Operand.Var ++ [Operand.Var v]) ps1
      = (descSwaps (rest.length + 1),
         { ps1 with stack := base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]) }) := by
    rw [hreo]
    simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop (rest.length + 1)
        (base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]))
      = base ++ [Operand.Var v] := by
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((rest ++ [v]).map Operand.Var)
    rw [List.length_map, show (rest ++ [v]).length = rest.length + 1 from by simp] at h
    rw [show base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v])
          = (base ++ [Operand.Var v]) ++ (rest ++ [v]).map Operand.Var from by simp]
    exact h
  simp [generateEmitOps_evmName hname, h2, hreo', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp, List.append_assoc]

/-- Closed form of the SLL ternop input emission (`z` spilled, `y`/`x` live): restore+dup `z`,
    then DUP the two live operands over the grown stack — `base ++ [z, z, y, x]`, the spill entry
    gone, the slot freed. The 3-operand extension of `emit2_valspilled`. -/
theorem emit3_zspilled {opc nl x y z ps base offz d_y d_x}
    (hstack0 : ps.stack = base)
    (hspill_z : alookup' ps.spilled (Operand.Var z) = some offz) (hlivez : nl.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nl.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nl.contains x = true)
    (hyz : y ≠ z) (hxz : x ≠ z) (hxy : x ≠ y)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 2 ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15) :
    (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var z, Operand.Var z, Operand.Var y, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var z),
                  alloc := freeSpillSlot offz ps.alloc } := by
  have hhead : emitOneInput opc nl (Operand.Var z) ps
      = ([StackOp.SORestore offz, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var z, Operand.Var z],
                   spilled := aremove ps.spilled (Operand.Var z),
                   alloc := freeSpillSlot offz ps.alloc }) :=
    emitOneInput_var_spilled_eq hspill_z hlivez
  set psZ : PlanState := { ps with
                             stack := ps.stack ++ [Operand.Var z, Operand.Var z],
                             spilled := aremove ps.spilled (Operand.Var z),
                             alloc := freeSpillSlot offz ps.alloc } with hpsZdef
  have hpsZstack : psZ.stack = ps.stack ++ [Operand.Var z, Operand.Var z] := by rw [hpsZdef]
  have hdepthy1 : stackGetDepth (Operand.Var y) psZ.stack = some (d_y + 2) := by
    rw [hpsZstack, show ps.stack ++ [Operand.Var z, Operand.Var z]
          = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var z] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hyz,
        stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
  have hnospilly1 : alookup' psZ.spilled (Operand.Var y) = none := by
    rw [hpsZdef]; exact aremove_lookup_none ps.spilled (Operand.Var z) (Operand.Var y) hnospill_y
  have hpeeky : stackPeek (d_y + 2) psZ.stack = Operand.Var y := stackGetDepth_peek hdepthy1
  have hddy : doDup (d_y + 2) psZ
      = ([StackOp.SODup (d_y + 2 + 1)], { psZ with stack := stackDup (d_y + 2) psZ.stack }) := by
    unfold doDup; rw [if_pos hsmall_y]
  have hlegy : emitOneInput opc nl (Operand.Var y) psZ
      = ([StackOp.SODup (d_y + 2 + 1)], { psZ with stack := stackDup (d_y + 2) psZ.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospilly1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivey, if_true, hdepthy1, hddy, List.nil_append]
  set psY : PlanState := { psZ with stack := stackDup (d_y + 2) psZ.stack } with hpsYdef
  have hpsYstack : psY.stack = ps.stack ++ [Operand.Var z, Operand.Var z, Operand.Var y] := by
    rw [hpsYdef]; show stackDup (d_y + 2) psZ.stack = _
    unfold stackDup; rw [hpeeky, hpsZstack]; simp
  have hdepthx1 : stackGetDepth (Operand.Var x) psY.stack = some (d_x + 3) := by
    rw [hpsYstack,
        show ps.stack ++ [Operand.Var z, Operand.Var z, Operand.Var y]
          = ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var z]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var z]) hxy,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxz,
        stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  have hnospillx1 : alookup' psY.spilled (Operand.Var x) = none := by
    rw [hpsYdef]
    show alookup' psZ.spilled (Operand.Var x) = none
    rw [hpsZdef]
    exact aremove_lookup_none ps.spilled (Operand.Var z) (Operand.Var x) hnospill_x
  have hpeekx : stackPeek (d_x + 3) psY.stack = Operand.Var x := stackGetDepth_peek hdepthx1
  have hddx : doDup (d_x + 3) psY
      = ([StackOp.SODup (d_x + 3 + 1)], { psY with stack := stackDup (d_x + 3) psY.stack }) := by
    unfold doDup; rw [if_pos hsmall_x]
  have hlegx : emitOneInput opc nl (Operand.Var x) psY
      = ([StackOp.SODup (d_x + 3 + 1)], { psY with stack := stackDup (d_x + 3) psY.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillx1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepthx1, hddx, List.nil_append]
  have hemit3 : (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { psY with stack := stackDup (d_x + 3) psY.stack } := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, hlegy, hlegx, List.nil_append]
  have hdupx : stackDup (d_x + 3) psY.stack
      = base ++ [Operand.Var z, Operand.Var z, Operand.Var y, Operand.Var x] := by
    unfold stackDup; rw [hpeekx, hpsYstack, hstack0]; simp
  rw [hemit3, hdupx]

/-- **Z-spilled ternop plan reduction** — the FIRST spilled ternary config: the last operand `z`
    (first emitted) comes off its spill slot, so the emission leaves the three operands POSITIONED
    (`reorderPlan = []` over the kept restored copy, `base' = base ++ [z]`); the op pops three and
    pushes `out`, leaving `base ++ [z, out]` (net +2). The 3-ary extension of
    `genRegularInstPlan_nonCommBinopVar_spilled_eq`. -/
theorem genRegularInstPlan_ternopVar_zspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y z out : String} {base : List Operand} {name : String} {offz d_y d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_z : alookup' ps.spilled (Operand.Var z) = some offz)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 2 ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var z, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var z, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hemitstack : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var z, Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hrev, emit3_zspilled hstack0 hspill_z hlivez hnospill_y hlivey hnospill_x hlivex
      hyz hxz hxy hdepth_y hsmall_y hdepth_x hsmall_x]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1'' : ps1.stack
      = (base ++ [Operand.Var z]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
        nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hemitstack
    rw [← h2, hemitstack]; simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 3 ps1.stack ++ [Operand.Var out]
      = base ++ [Operand.Var z, Operand.Var out] := by
    rw [hps1'', stackPop_3_append_triple]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname,
        reorderPlan_triple_var_nil (base ++ [Operand.Var z]) z y x ps1 hps1''
          (Ne.symm hyz) (Ne.symm hxy) (Ne.symm hxz),
        hpush, stackPush, popmanyPlan_nil, hmem, hncomm, hnjmp]

/-- **Z-spilled ternop sim** — restore `z`, DUP the live `y`/`x` (the mixed emission), run the
    ternop over the positioned top three, push `out`: the whole plan preserves `venomAsmRel`
    across `out := f wx wy wz`. The first runnable spilled ternary producer. -/
theorem genRegularInstPlan_ternopVar_zspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {x y z out : String} {wx wy wz : bytes32} {base : List Operand} {name : String}
    {offz d_y d_x : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_z : alookup' ps.spilled (Operand.Var z) = some offz)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 2 ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var z, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var z, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy wz) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hemit3 := emit3_zspilled (opc := inst.opcode) (nl := nextLiveness)
    hstack0 hspill_z hlivez hnospill_y hlivey hnospill_x hlivex hyz hxz hxy
    hdepth_y hsmall_y hdepth_x hsmall_x
  rw [genRegularInstPlan_ternopVar_zspilled_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz
      hstack0 hlive hspill_z hlivez hnospill_y hlivey hnospill_x hlivex hdepth_y hsmall_y
      hdepth_x hsmall_x, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps).2 with hps1def
  have hemit3flat : ps1
      = { ps with stack := base ++ [Operand.Var z, Operand.Var z, Operand.Var y, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var z),
                  alloc := freeSpillSlot offz ps.alloc } := by
    rw [hps1def]; exact hemit3
  have hps1stack : ps1.stack
      = (base ++ [Operand.Var z]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hemit3flat]; simp
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hemit3flat]
    show alookup' (aremove ps.spilled (Operand.Var z)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var z) (Operand.Var out) hspill_out
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  have hok : emitMixedOk nextLiveness [z, y, x] ps.spilled ps.stack := by
    have hy' : alookup' (aremove ps.spilled (Operand.Var z)) (Operand.Var y) = none :=
      aremove_lookup_none ps.spilled (Operand.Var z) (Operand.Var y) hnospill_y
    have hx' : alookup' (aremove ps.spilled (Operand.Var z)) (Operand.Var x) = none :=
      aremove_lookup_none ps.spilled (Operand.Var z) (Operand.Var x) hnospill_x
    simp only [emitMixedOk, hspill_z]
    rw [hy', hx']
    refine ⟨hlivez, hlivey, ⟨d_y + 2, ?_, by omega, hlivex, ⟨d_x + 3, ?_, by omega, trivial⟩⟩⟩
    · rw [show ps.stack ++ [Operand.Var z, Operand.Var z]
            = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var z] from by simp,
          stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hyz,
          stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
    · rw [show ps.stack ++ [Operand.Var z, Operand.Var z] ++ [Operand.Var y]
            = ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var z]) ++ [Operand.Var y] from by simp,
          stackGetDepth_append_ne ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var z]) hxy,
          stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxz,
          stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  obtain ⟨as1, hrunI, hrelI, hpcI, _⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness [z, y, x] ps hok hspillWf hrel hbI
  simp only [show ([z, y, x].map Operand.Var)
      = [Operand.Var z, Operand.Var y, Operand.Var x] from rfl] at hrunI hrelI hpcI
  have hstacktop : as1.stack = wx :: wy :: wz :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hvx hvy hvz
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro ((h | h) | h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_3op_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 3 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var z, Operand.Var out] } := by
    rw [hps1stack, stackPop_3_append_triple]
    simp [stackPush, List.append_assoc]
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega


/-- Closed form of the LLS ternop input emission (`z`/`y` live, `x` spilled): DUP the two live
    operands, then restore+dup `x` — `base ++ [z, y, x, x]`, the spill entry gone, the slot freed. -/
theorem emit3_xspilled {opc nl x y z ps base offx d_z d_y}
    (hstack0 : ps.stack = base)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none) (hlivez : nl.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nl.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nl.contains x = true)
    (hyz : y ≠ z)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 1 ≤ 15) :
    (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var x),
                  alloc := freeSpillSlot offx ps.alloc } := by
  -- leg z: DUP at d_z
  have hpeekz : stackPeek d_z ps.stack = Operand.Var z := stackGetDepth_peek hdepth_z
  have hddz : doDup d_z ps = ([StackOp.SODup (d_z + 1)], { ps with stack := stackDup d_z ps.stack }) := by
    unfold doDup; rw [if_pos hsmall_z]
  have hlegz : emitOneInput opc nl (Operand.Var z) ps
      = ([StackOp.SODup (d_z + 1)], { ps with stack := stackDup d_z ps.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospill_z, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivez, if_true, hdepth_z, hddz, List.nil_append]
  set psZ : PlanState := { ps with stack := stackDup d_z ps.stack } with hpsZdef
  have hpsZstack : psZ.stack = ps.stack ++ [Operand.Var z] := by
    rw [hpsZdef]; show stackDup d_z ps.stack = _; unfold stackDup; rw [hpeekz]
  -- leg y: DUP at d_y + 1 over base ++ [z]
  have hdepthy1 : stackGetDepth (Operand.Var y) psZ.stack = some (d_y + 1) := by
    rw [hpsZstack, stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
  have hnospilly1 : alookup' psZ.spilled (Operand.Var y) = none := hnospill_y
  have hpeeky : stackPeek (d_y + 1) psZ.stack = Operand.Var y := stackGetDepth_peek hdepthy1
  have hddy : doDup (d_y + 1) psZ
      = ([StackOp.SODup (d_y + 1 + 1)], { psZ with stack := stackDup (d_y + 1) psZ.stack }) := by
    unfold doDup; rw [if_pos hsmall_y]
  have hlegy : emitOneInput opc nl (Operand.Var y) psZ
      = ([StackOp.SODup (d_y + 1 + 1)], { psZ with stack := stackDup (d_y + 1) psZ.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospilly1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivey, if_true, hdepthy1, hddy, List.nil_append]
  set psY : PlanState := { psZ with stack := stackDup (d_y + 1) psZ.stack } with hpsYdef
  have hpsYstack : psY.stack = ps.stack ++ [Operand.Var z, Operand.Var y] := by
    rw [hpsYdef]; show stackDup (d_y + 1) psZ.stack = _
    unfold stackDup; rw [hpeeky, hpsZstack]; simp
  -- leg x: restore + dup (the spilled map untouched by the DUPs)
  have hspillx1 : alookup' psY.spilled (Operand.Var x) = some offx := hspill_x
  have hlegx : emitOneInput opc nl (Operand.Var x) psY
      = ([StackOp.SORestore offx, StackOp.SODup 1],
         { psY with stack := psY.stack ++ [Operand.Var x, Operand.Var x],
                    spilled := aremove psY.spilled (Operand.Var x),
                    alloc := freeSpillSlot offx psY.alloc }) :=
    emitOneInput_var_spilled_eq hspillx1 hlivex
  have hemit3 : (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { psY with stack := psY.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove psY.spilled (Operand.Var x),
                   alloc := freeSpillSlot offx psY.alloc } := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hlegz, hlegy, hlegx, List.nil_append]
  rw [hemit3, hpsYstack, hstack0]
  simp [hpsYdef, hpsZdef, List.append_assoc]

/-- **First-spilled ternop plan reduction**: LLS emit, the proven `SWAP3;SWAP2;SWAP1` reorder
    (`reorderPlan_ternop_firstspilled`), the op over the positioned top three, `out` pushed —
    intermediate `base ++ [x, out]` (net +2 over the kept restored copy). -/
theorem genRegularInstPlan_ternopVar_xspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y z out : String} {base : List Operand} {name : String} {offx d_z d_y : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hyz : y ≠ z) (hxz : x ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 1 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var x, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hemit3 := emit3_xspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_z hlivez
    hnospill_y hlivey hspill_x hlivex hyz hdepth_z hsmall_z hdepth_y hsmall_y
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
      nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack
      = base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [← h2, hemit3]
  have hreorder : reorderPlan [Operand.Var z, Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1],
         { ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_ternop_firstspilled base x y z ps1 hxz hyz hps1stack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 3 (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x])
      ++ [Operand.Var out] = base ++ [Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var x]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] from by simp,
        stackPop_3_append_triple]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname, hreorder, hpush, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **First-spilled ternop sim**: DUP the live `z`/`y`, restore `x`, run the proven
    `SWAP3;SWAP2;SWAP1` reorder, the ternop over the positioned top three, push `out` — the whole
    plan preserves `venomAsmRel` across `out := f wx wy wz`. Composes the mixed emission sim, three
    `doSwap_sim`, and `emit_3op_sim`. -/
theorem genRegularInstPlan_ternopVar_xspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {x y z out : String} {wx wy wz : bytes32} {base : List Operand} {name : String}
    {offx d_z d_y : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 1 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy wz) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_xspilled_eq hname hncomm hnjmp hcompute hops houts hyz hxz
      hstack0 hlive hnospill_z hlivez hnospill_y hlivey hspill_x hlivex hdepth_z hsmall_z
      hdepth_y hsmall_y, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps).2 with hps1def
  have hemit3 := emit3_xspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_z hlivez
    hnospill_y hlivey hspill_x hlivex hyz hdepth_z hsmall_z hdepth_y hsmall_y
  have hps1stack : ps1.stack
      = base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, hemit3]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemit3]
    show alookup' (aremove ps.spilled (Operand.Var x)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var x) (Operand.Var out) hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
            nextLiveness ps).1
            ++ [StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
            nextLiveness ps).1
            ++ ([StackOp.SOSwap 3] ++ ([StackOp.SOSwap 2]
              ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name]))) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap3raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap2raw, hbRest3⟩ := asmBlockAt_append hbRest2
  obtain ⟨hbSwap1raw, hbEmitraw⟩ := asmBlockAt_append hbRest3
  -- the LLS emission
  have hok : emitMixedOk nextLiveness [z, y, x] ps.spilled ps.stack := by
    have hdy1 : stackGetDepth (Operand.Var y) (ps.stack ++ [Operand.Var z]) = some (d_y + 1) := by
      rw [stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
    simp only [emitMixedOk, hnospill_z, hnospill_y, hspill_x]
    exact ⟨hlivez, ⟨d_z, hdepth_z, by omega, ⟨hlivey, ⟨d_y + 1, hdy1, by omega,
      ⟨hlivex, trivial⟩⟩⟩⟩⟩
  obtain ⟨as1, hrunI, hrelI, hpcI, _⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness [z, y, x] ps hok hspillWf hrel hbI
  simp only [show ([z, y, x].map Operand.Var)
      = [Operand.Var z, Operand.Var y, Operand.Var x] from rfl] at hrunI hrelI hpcI
  -- SWAP3
  have hlen3 : (3 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap3 : doSwap 3 ps1
      = ([StackOp.SOSwap 3], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
          Operand.Var x, Operand.Var z] }) := by
    rw [doSwap_three]; congr 1
    rw [hps1stack,
        stackSwap_3_append_quad base (Operand.Var z) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap3 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 3]) := by
    rw [hpcI]; exact hbSwap3raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap3 hrelI hlen3 hbSwap3 (by intro h; omega)
  -- SWAP2
  have hlen2 : (2 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
      Operand.Var x, Operand.Var z] } : PlanState).stack.length := by simp
  have hswap2 : doSwap 2 { ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
        Operand.Var x, Operand.Var z] }
      = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
          Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x,
          Operand.Var z] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var y, Operand.Var x, Operand.Var z] from rfl,
        stackSwap_2_append_quad base (Operand.Var x) (Operand.Var y) (Operand.Var x) (Operand.Var z)]
  have hbSwap2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 2]) := by
    rw [hpc2, hpcI]; exact hbSwap2raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap2 hrel2 hlen2 hbSwap2 (by intro h; omega)
  -- SWAP1
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
      Operand.Var x, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
        Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
          Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var x,
          Operand.Var y] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y] from rfl,
        stackSwap_1_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var x) (Operand.Var y)]
  have hbSwap1 : asmBlockAt prog as3.pc (executePlan [StackOp.SOSwap 1]) := by
    rw [hpc3, hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel3 hlen1 hbSwap1 (by intro h; omega)
  -- the ternop over the positioned top three
  have hps4stack : ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y,
      Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var x]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as4.stack = wx :: wy :: wz :: as4.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrel4 hps4stack hvx hvy hvz
  have hfresh4 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var x,
      Operand.Var z, Operand.Var y, Operand.Var x] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h | h)
    · exact hfresh h
    · exact hox (by injection h)
    · exact hoz (by injection h)
    · exact hoy (by injection h)
    · exact hox (by injection h)
  have hps4spill : AssocList.lookup Operand Nat ({ ps1 with stack := base ++ [Operand.Var x,
      Operand.Var z, Operand.Var y, Operand.Var x] } : PlanState).spilled (Operand.Var out)
      = none := hps1spill
  have hbEmit : asmBlockAt prog as4.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpc4, hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as5, hrun5, hrel5, hpc5⟩ :=
    emit_3op_sim hrel4 hstacktop hfresh4 hps4spill hbEmit (fun h hg => hdisp as4 h hg)
  have hps6 : ({ { ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y,
        Operand.Var x] } with
        stack := stackPush (Operand.Var out) (stackPop 3 (base ++ [Operand.Var x, Operand.Var z,
          Operand.Var y, Operand.Var x])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var x, Operand.Var out] } := by
    rw [show base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var x]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] from by simp,
        stackPop_3_append_triple]
    simp [stackPush, List.append_assoc]
  rw [hps6] at hrel5
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel5
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var z, Operand.Var y,
        Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 3] ++ ([StackOp.SOSwap 2]
          ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name]))))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
          nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 3]).length + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit name]).length))) := by
    rw [executePlan_append, executePlan_append, executePlan_append, executePlan_append,
        List.length_append, List.length_append, List.length_append, List.length_append]
  refine ⟨as5, ?_, hrelR, ?_⟩
  · rw [hlenEq]
    exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3
      (runAsm_compose hrun4 hrun5)))
  · rw [hlenEq, hpc5, hpc4, hpc3, hpc2, hpcI]; omega

/-- **Mid-spilled ternary emission**: `z` live (DUP at `d_z`), `y` spilled (restore + keep-alive
    DUP), `x` live (DUP at `d_x + 3` over the three pushes) — stack grows by
    `[z, y, y, x]`, `y` leaves the spilled map, its slot is freed. -/
theorem emit3_yspilled {opc nl x y z ps base offy d_z d_x}
    (hstack0 : ps.stack = base)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none) (hlivez : nl.contains z = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nl.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nl.contains x = true)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15) :
    (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var y),
                  alloc := freeSpillSlot offy ps.alloc } := by
  -- leg z: DUP at d_z
  have hpeekz : stackPeek d_z ps.stack = Operand.Var z := stackGetDepth_peek hdepth_z
  have hddz : doDup d_z ps = ([StackOp.SODup (d_z + 1)], { ps with stack := stackDup d_z ps.stack }) := by
    unfold doDup; rw [if_pos hsmall_z]
  have hlegz : emitOneInput opc nl (Operand.Var z) ps
      = ([StackOp.SODup (d_z + 1)], { ps with stack := stackDup d_z ps.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospill_z, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivez, if_true, hdepth_z, hddz, List.nil_append]
  set psZ : PlanState := { ps with stack := stackDup d_z ps.stack } with hpsZdef
  have hpsZstack : psZ.stack = ps.stack ++ [Operand.Var z] := by
    rw [hpsZdef]; show stackDup d_z ps.stack = _; unfold stackDup; rw [hpeekz]
  -- leg y: restore + dup (the spilled map untouched by the z DUP)
  have hspilly1 : alookup' psZ.spilled (Operand.Var y) = some offy := hspill_y
  have hlegy : emitOneInput opc nl (Operand.Var y) psZ
      = ([StackOp.SORestore offy, StackOp.SODup 1],
         { psZ with stack := psZ.stack ++ [Operand.Var y, Operand.Var y],
                    spilled := aremove psZ.spilled (Operand.Var y),
                    alloc := freeSpillSlot offy psZ.alloc }) :=
    emitOneInput_var_spilled_eq hspilly1 hlivey
  set psY : PlanState :=
    { psZ with
        stack := psZ.stack ++ [Operand.Var y, Operand.Var y],
        spilled := aremove psZ.spilled (Operand.Var y),
        alloc := freeSpillSlot offy psZ.alloc } with hpsYdef
  have hpsYstack : psY.stack
      = ps.stack ++ [Operand.Var z, Operand.Var y, Operand.Var y] := by
    rw [hpsYdef]; show psZ.stack ++ _ = _; rw [hpsZstack]; simp
  -- leg x: DUP at d_x + 3 over the grown stack, past the removed y
  have hnospillx1 : alookup' psY.spilled (Operand.Var x) = none := by
    show alookup' (aremove psZ.spilled (Operand.Var y)) (Operand.Var x) = none
    exact aremove_lookup_none psZ.spilled (Operand.Var y) (Operand.Var x) hnospill_x
  have hdepthx3 : stackGetDepth (Operand.Var x) psY.stack = some (d_x + 3) := by
    rw [hpsYstack,
        show ps.stack ++ [Operand.Var z, Operand.Var y, Operand.Var y]
          = ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) hxy,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxy,
        stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  have hpeekx : stackPeek (d_x + 3) psY.stack = Operand.Var x := stackGetDepth_peek hdepthx3
  have hddx : doDup (d_x + 3) psY
      = ([StackOp.SODup (d_x + 3 + 1)], { psY with stack := stackDup (d_x + 3) psY.stack }) := by
    unfold doDup; rw [if_pos hsmall_x]
  have hlegx : emitOneInput opc nl (Operand.Var x) psY
      = ([StackOp.SODup (d_x + 3 + 1)], { psY with stack := stackDup (d_x + 3) psY.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillx1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepthx3, hddx, List.nil_append]
  have hemit3 : (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
      = { psY with stack := stackDup (d_x + 3) psY.stack } := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hlegz, hlegy, hlegx, List.nil_append]
  have hstk : stackDup (d_x + 3) psY.stack
      = ps.stack ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x] := by
    unfold stackDup; rw [hpeekx, hpsYstack]; simp
  rw [hemit3, hstk, hstack0]

/-- **Mid-spilled ternop plan reduction**: LLS emit, the proven `SWAP3;SWAP2;SWAP1;SWAP3` reorder
    (`reorderPlan_ternop_midspilled`, equal-`y` SWAP1 no-op included), the op over the positioned
    top three, `out` pushed — intermediate `base ++ [y, out]` (net +2 over the kept restored copy). -/
theorem genRegularInstPlan_ternopVar_yspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y z out : String} {base : List Operand} {name : String} {offy d_z d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOSwap 3]
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var y, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var y, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hemit3 := emit3_yspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_z hlivez
    hspill_y hlivey hnospill_x hlivex hxy hxz hdepth_z hsmall_z hdepth_x hsmall_x
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
      nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack
      = base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [← h2, hemit3]
  have hreorder : reorderPlan [Operand.Var z, Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOSwap 3],
         { ps1 with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_ternop_midspilled base x y z ps1 hxy hxz hyz hps1stack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 3 (base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x])
      ++ [Operand.Var out] = base ++ [Operand.Var y, Operand.Var out] := by
    rw [show base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] from by simp,
        stackPop_3_append_triple]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname, hreorder, hpush, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **Mid-spilled ternop sim**: DUP the live `z`, restore `y`, DUP the live `x`, run the proven
    `SWAP3;SWAP2;SWAP1;SWAP3` reorder (the equal-`y` SWAP1 is a stack no-op), the ternop over the
    positioned top three, push `out` — the whole plan preserves `venomAsmRel` across
    `out := f wx wy wz`. -/
theorem genRegularInstPlan_ternopVar_yspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {x y z out : String} {wx wy wz : bytes32} {base : List Operand} {name : String}
    {offy d_z d_x : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy wz) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_yspilled_eq hname hncomm hnjmp hcompute hops houts hxy hxz hyz
      hstack0 hlive hnospill_z hlivez hspill_y hlivey hnospill_x hlivex hdepth_z hsmall_z
      hdepth_x hsmall_x, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps).2 with hps1def
  have hemit3 := emit3_yspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_z hlivez
    hspill_y hlivey hnospill_x hlivex hxy hxz hdepth_z hsmall_z hdepth_x hsmall_x
  have hps1stack : ps1.stack
      = base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [hps1def, hemit3]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemit3]
    show alookup' (aremove ps.spilled (Operand.Var y)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var out) hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
            nextLiveness ps).1
            ++ [StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOSwap 3]
            ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
            nextLiveness ps).1
            ++ ([StackOp.SOSwap 3] ++ ([StackOp.SOSwap 2]
              ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 3]
                ++ [StackOp.SOEmit name])))) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append, executePlan_append,
      executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap3raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap2raw, hbRest3⟩ := asmBlockAt_append hbRest2
  obtain ⟨hbSwap1raw, hbRest4⟩ := asmBlockAt_append hbRest3
  obtain ⟨hbSwap3braw, hbEmitraw⟩ := asmBlockAt_append hbRest4
  -- the LLS emission
  have hok : emitMixedOk nextLiveness [z, y, x] ps.spilled ps.stack := by
    have hx' : alookup' (aremove ps.spilled (Operand.Var y)) (Operand.Var x) = none :=
      aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var x) hnospill_x
    simp only [emitMixedOk, hnospill_z, hspill_y, hx']
    refine ⟨hlivez, d_z, hdepth_z, by omega, hlivey, hlivex, d_x + 3, ?_, by omega, trivial⟩
    rw [show ps.stack ++ [Operand.Var z] ++ [Operand.Var y, Operand.Var y]
          = ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) hxy,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxy,
        stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  obtain ⟨as1, hrunI, hrelI, hpcI, _⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness [z, y, x] ps hok hspillWf hrel hbI
  simp only [show ([z, y, x].map Operand.Var)
      = [Operand.Var z, Operand.Var y, Operand.Var x] from rfl] at hrunI hrelI hpcI
  -- SWAP3
  have hlen3 : (3 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap3 : doSwap 3 ps1
      = ([StackOp.SOSwap 3], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
          Operand.Var y, Operand.Var z] }) := by
    rw [doSwap_three]; congr 1
    rw [hps1stack,
        stackSwap_3_append_quad base (Operand.Var z) (Operand.Var y) (Operand.Var y) (Operand.Var x)]
  have hbSwap3 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 3]) := by
    rw [hpcI]; exact hbSwap3raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap3 hrelI hlen3 hbSwap3 (by intro h; omega)
  -- SWAP2
  have hlen2 : (2 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
      Operand.Var y, Operand.Var z] } : PlanState).stack.length := by simp
  have hswap2 : doSwap 2 { ps1 with stack := base ++ [Operand.Var x, Operand.Var y,
        Operand.Var y, Operand.Var z] }
      = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
          Operand.Var y, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var y,
          Operand.Var z] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var y, Operand.Var y, Operand.Var z] from rfl,
        stackSwap_2_append_quad base (Operand.Var x) (Operand.Var y) (Operand.Var y) (Operand.Var z)]
  have hbSwap2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 2]) := by
    rw [hpc2, hpcI]; exact hbSwap2raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap2 hrel2 hlen2 hbSwap2 (by intro h; omega)
  -- SWAP1 (equal-y stack no-op)
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
      Operand.Var y, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
        Operand.Var y, Operand.Var y] }
      = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
          Operand.Var y, Operand.Var y] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y,
          Operand.Var y] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] from rfl,
        stackSwap_1_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var y)]
  have hbSwap1 : asmBlockAt prog as3.pc (executePlan [StackOp.SOSwap 1]) := by
    rw [hpc3, hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel3 hlen1 hbSwap1 (by intro h; omega)
  -- second SWAP3
  have hlen3b : (3 : Nat) < ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
      Operand.Var y, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap3b : doSwap 3 { ps1 with stack := base ++ [Operand.Var x, Operand.Var z,
        Operand.Var y, Operand.Var y] }
      = ([StackOp.SOSwap 3], { ps1 with stack := base ++ [Operand.Var y, Operand.Var z,
          Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_three]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y,
          Operand.Var y] } : PlanState).stack
          = base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] from rfl,
        stackSwap_3_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var y)]
  have hbSwap3b : asmBlockAt prog as4.pc (executePlan [StackOp.SOSwap 3]) := by
    rw [hpc4, hpc3, hpc2, hpcI]; exact hbSwap3braw
  obtain ⟨as5, hrun5, hrel5, hpc5⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hswap3b hrel4 hlen3b hbSwap3b (by intro h; omega)
  -- the ternop over the positioned top three
  have hps5stack : ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y,
      Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var y]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as5.stack = wx :: wy :: wz :: as5.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrel5 hps5stack hvx hvy hvz
  have hfresh5 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var y,
      Operand.Var z, Operand.Var y, Operand.Var x] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h | h)
    · exact hfresh h
    · exact hoy (by injection h)
    · exact hoz (by injection h)
    · exact hoy (by injection h)
    · exact hox (by injection h)
  have hps5spill : AssocList.lookup Operand Nat ({ ps1 with stack := base ++ [Operand.Var y,
      Operand.Var z, Operand.Var y, Operand.Var x] } : PlanState).spilled (Operand.Var out)
      = none := hps1spill
  have hbEmit : asmBlockAt prog as5.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as6, hrun6, hrel6, hpc6⟩ :=
    emit_3op_sim hrel5 hstacktop hfresh5 hps5spill hbEmit (fun h hg => hdisp as5 h hg)
  have hps7 : ({ { ps1 with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y,
        Operand.Var x] } with
        stack := stackPush (Operand.Var out) (stackPop 3 (base ++ [Operand.Var y, Operand.Var z,
          Operand.Var y, Operand.Var x])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var out] } := by
    rw [show base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y]) ++ [Operand.Var z, Operand.Var y, Operand.Var x] from by simp,
        stackPop_3_append_triple]
    simp [stackPush, List.append_assoc]
  rw [hps7] at hrel6
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel6
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var z, Operand.Var y,
        Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 3] ++ ([StackOp.SOSwap 2]
          ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 3] ++ [StackOp.SOEmit name])))))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
          nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 3]).length + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + ((executePlan [StackOp.SOSwap 3]).length
             + (executePlan [StackOp.SOEmit name]).length)))) := by
    rw [executePlan_append, executePlan_append, executePlan_append, executePlan_append,
        executePlan_append, List.length_append, List.length_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as6, ?_, hrelR, ?_⟩
  · rw [hlenEq]
    exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3
      (runAsm_compose hrun4 (runAsm_compose hrun5 hrun6))))
  · rw [hlenEq, hpc6, hpc5, hpc4, hpc3, hpc2, hpcI]; omega
/-- Full emit `.2` for a both-spilled 2-var op (`y`, `x` both spilled): stack `base ++ [y,y,x,x]`,
    both slots freed. The SS analogue of `emit2_keyspilled`/`emit2_valspilled`. -/
theorem emit2_bothspilled {opc nl x y ps base offx offy}
    (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nl.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nl.contains x = true)
    (hxy : x ≠ y) :
    (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x],
                  spilled := aremove (aremove ps.spilled (Operand.Var y)) (Operand.Var x),
                  alloc := freeSpillSlot offx (freeSpillSlot offy ps.alloc) } := by
  have hhead : emitOneInput opc nl (Operand.Var y) ps
      = ([StackOp.SORestore offy, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y],
                   spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc }) :=
    emitOneInput_var_spilled_eq hspill_y hlivey
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y],
                                   spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc } with hps1def
  have hxney : (Operand.Var x) ≠ (Operand.Var y) := by intro h; injection h with h'; exact hxy h'
  have hspillx1 : alookup' ps1.spilled (Operand.Var x) = some offx := by
    rw [hps1def]
    exact (aremove_lookup_ne ps.spilled (Operand.Var y) (Operand.Var x) hxney).trans hspill_x
  have htail : emitOneInput opc nl (Operand.Var x) ps1
      = ([StackOp.SORestore offx, StackOp.SODup 1],
         { ps1 with stack := ps1.stack ++ [Operand.Var x, Operand.Var x],
                    spilled := aremove ps1.spilled (Operand.Var x), alloc := freeSpillSlot offx ps1.alloc }) :=
    emitOneInput_var_spilled_eq hspillx1 hlivex
  have hemit2 : (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { ps1 with stack := ps1.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps1.spilled (Operand.Var x), alloc := freeSpillSlot offx ps1.alloc } := by
    unfold emitInputPlan; simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hemit2, hps1def, hstack0]; simp

/-- **Both-spilled store plan reduction.** `SSTORE x y`, both key `x` and value `y` spilled: emit
    restores+DUPs each (`base ++ [y, y, x, x]`), the reorder is the same `SWAP2 ; SWAP1`
    (`reorderPlan_bothspilled`) giving `base ++ [y, x, y, x]`, `stackPop 2` leaves `base ++ [y, x]`
    (the two kept restored operands). -/
theorem genRegularInstPlan_sstore_bothspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y : String} {base : List Operand} {name : String} {offx offy : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
           ++ [StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
             stack := base ++ [Operand.Var y, Operand.Var x] }) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [← h2, hemit2]
  have hreorder : reorderPlan [Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1],
         { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_bothspilled base x y ps1 hxy hps1stack
  have hpop2 : stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x])
      = base ++ [Operand.Var y, Operand.Var x] := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]
  simp [generateEmitOps_evmName hname, hreorder, hpop2, hncomm, hnjmp]

/-- **Both-spilled store sim.** `SSTORE x y` with both operands spilled runs correctly: restore+DUP
    both (`base ++ [y,y,x,x]`), the `SWAP2 ; SWAP1` reorder (`base ++ [y,x,y,x]`), then `SSTORE`
    consumes key+value — preserving `venomAsmRel` across `sstore wx wy vs`. Composes the both-restore
    emit sim, two `doSwap_sim`, and `emit_sstore_sim`. -/
theorem genRegularInstPlan_sstore_bothspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {wx wy : bytes32} {base : List Operand} {offx offy : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (sstore wx wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hspill_y hlivey hspill_x hlivex, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy]
  rw [show ([StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"] : List StackOp)
        = [StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"]) from rfl] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap2raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap1raw, hbStoreraw⟩ := asmBlockAt_append hbRest2
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_both_spilled_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hspill_x hlivey hlivex hrel hspillWf hbI
  have hlen2 : (2 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap2 : doSwap 2 ps1 = ([StackOp.SOSwap 2],
      { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [hps1stack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
          = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
        stackSwap_2_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
    simp
  have hbSwap2 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpcI]; exact hbSwap2raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrelI hlen2 hbSwap2 (by intro h; omega)
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1],
         { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
          = (base ++ [Operand.Var y]) ++ [Operand.Var x, Operand.Var x, Operand.Var y] from by simp,
        stackSwap_1_append_triple (base ++ [Operand.Var y]) (Operand.Var x) (Operand.Var x) (Operand.Var y)]
    simp
  have hbSwap1 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel2 hlen1 hbSwap1 (by intro h; omega)
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as3.stack = wx :: wy :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvx hvy
  have hbSST : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by rw [hpc3, hpc2, hpcI]; exact hbStoreraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_sstore_sim hrel3 hstacktop hbSST (fun h hg => hdisp as3 h hg)
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } with
      stack := stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var x] } := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit "SSTORE"]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega

/-- **Both-spilled non-commutative binop plan reduction.** Both operands spilled: emit
    restores+DUPs each (`base ++ [y, y, x, x]`), the `SWAP2 ; SWAP1` reorder
    (`reorderPlan_bothspilled`) gives `base ++ [y, x, y, x]`, the op pops two and pushes `out`
    (optSwap intermediate `base ++ [y, x, out]` — both restored operands kept, net +3). -/
theorem genRegularInstPlan_nonCommBinopVar_bothspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offx offy : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [← h2, hemit2]
  have hreorder : reorderPlan [Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_bothspilled base x y ps1 hxy hps1stack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]) ++ [Operand.Var out]
      = base ++ [Operand.Var y, Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname, hreorder, hpush, stackPush, popmanyPlan_nil, hmem, hncomm, hnjmp]

/-- **Both-spilled non-commutative binop sim.** Both operands off spill slots: restore both,
    `SWAP2 ; SWAP1` reorder, run the binop, push `out` — preserves `venomAsmRel` across
    `out := f wx wy`. Composes the both-restore emit sim, two `doSwap_sim`, and `emit_binop_sim`. -/
theorem genRegularInstPlan_nonCommBinopVar_bothspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offx offy : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_nonCommBinopVar_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hspill_y hlivey hspill_x hlivex, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy]
    show alookup' (aremove (aremove ps.spilled (Operand.Var y)) (Operand.Var x)) (Operand.Var out) = none
    exact ((aremove_lookup_ne _ (Operand.Var x) (Operand.Var out) (by intro h; injection h with h'; exact hox h')).trans
      (aremove_lookup_ne _ (Operand.Var y) (Operand.Var out) (by intro h; injection h with h'; exact hoy h'))).trans hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ [StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name])) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap2raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap1raw, hbEmitraw⟩ := asmBlockAt_append hbRest2
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_both_spilled_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hspill_x hlivey hlivex hrel hspillWf hbI
  have hlen2 : (2 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap2 : doSwap 2 ps1 = ([StackOp.SOSwap 2],
      { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [hps1stack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
          = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
        stackSwap_2_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
    simp
  have hbSwap2 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpcI]; exact hbSwap2raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrelI hlen2 hbSwap2 (by intro h; omega)
  have hlen1 : (1 : Nat) < ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack.length := by simp
  have hswap1 : doSwap 1 { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1],
         { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
          = (base ++ [Operand.Var y]) ++ [Operand.Var x, Operand.Var x, Operand.Var y] from by simp,
        stackSwap_1_append_triple (base ++ [Operand.Var y]) (Operand.Var x) (Operand.Var x) (Operand.Var y)]
    simp
  have hbSwap1 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpc2, hpcI]; exact hbSwap1raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrel2 hlen1 hbSwap1 (by intro h; omega)
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack
      = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] := by simp
  have hstacktop : as3.stack = wx :: wy :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvx hvy
  have hfresh3 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h | h)
    · exact hfresh h
    · exact hoy (by injection h)
    · exact hox (by injection h)
    · exact hoy (by injection h)
    · exact hox (by injection h)
  have hps3spill : alookup' ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } : PlanState).spilled (Operand.Var out) = none := hps1spill
  have hbEmit : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit name]) := by rw [hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_binop_sim hrel3 hstacktop hfresh3 hps3spill hbEmit (fun h hg => hdisp as3 h hg)
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] } with
      stack := stackPush (Operand.Var out) (stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] } := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 2] ++ ([StackOp.SOSwap 1] ++ [StackOp.SOEmit name])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 2]).length
           + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit name]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega

/-- **Both-spilled commutative binop plan reduction.** Both operands spilled; the commutative dispatch
    takes the swapped order (`reorderCost` tie), so the reorder is `SWAP1 ; SWAP2`
    (`reorderPlan_bothspilled_swapped`, `base ++ [y,y,x,x]` → `base ++ [y,x,x,y]`); pop 2 then push
    `out` gives optSwap intermediate `base ++ [y, x, out]` (net +3). -/
theorem genRegularInstPlan_commBinopVar_bothspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offx offy : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out]) (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 1, StackOp.SOSwap 2] ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }).2) := by
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1flat : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by rw [← h2, hemit2]
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y]) ++ [Operand.Var out]
      = base ++ [Operand.Var y, Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y]
          = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var x, Operand.Var y] from by simp,
        stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname,
        reorderPlan_bothspilled base x y ps1 hxy hps1flat,
        reorderPlan_bothspilled_swapped base x y ps1 hxy hps1flat,
        hpush, stackPush, popmanyPlan_nil, hmem, reorderCost, hcomm, hjmp]

/-- **Both-spilled commutative binop sim.** Both operands off slots; the commutative dispatch
    picks the swapped order (`SWAP1 ; SWAP2`); the binop pops `f wy wx`, rewritten to `f wx wy`
    by `hfcomm`. Preserves `venomAsmRel` across `out := f wx wy`. -/
theorem genRegularInstPlan_commBinopVar_bothspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offx offy : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_commBinopVar_bothspilled_eq hname hcomm hops houts hxy hstack0 hlive
      hspill_y hlivey hspill_x hlivex, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [hps1def, emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy]
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emit2_bothspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hspill_x hlivex hxy]
    show alookup' (aremove (aremove ps.spilled (Operand.Var y)) (Operand.Var x)) (Operand.Var out) = none
    exact ((aremove_lookup_ne _ (Operand.Var x) (Operand.Var out) (by intro h; injection h with h'; exact hox h')).trans
      (aremove_lookup_ne _ (Operand.Var y) (Operand.Var out) (by intro h; injection h with h'; exact hoy h'))).trans hspill_out
  rw [show ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ [StackOp.SOSwap 1, StackOp.SOSwap 2] ++ [StackOp.SOEmit name])
        = (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
            ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 2] ++ [StackOp.SOEmit name])) from by simp] at hblock ⊢
  rw [executePlan_append, executePlan_append, executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwap1raw, hbRest2⟩ := asmBlockAt_append hbRest
  obtain ⟨hbSwap2raw, hbEmitraw⟩ := asmBlockAt_append hbRest2
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_both_spilled_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hspill_x hlivey hlivex hrel hspillWf hbI
  have hlen1 : (1 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hswap1 : doSwap 1 ps1 = ([StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] }) := by
    rw [doSwap_one]; congr 1
    rw [hps1stack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
          = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
        stackSwap_1_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
  have hbSwap1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpcI]; exact hbSwap1raw
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap1 hrelI hlen1 hbSwap1 (by intro h; omega)
  have hlen2 : (2 : Nat) < ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] } : PlanState).stack.length := by simp
  have hswap2 : doSwap 2 { ps1 with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] }
      = ([StackOp.SOSwap 2], { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    rw [doSwap_two]; congr 1
    rw [show ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] } : PlanState).stack
          = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
        stackSwap_2_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
    simp
  have hbSwap2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOSwap 2]) := by rw [hpc2, hpcI]; exact hbSwap2raw
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ := doSwap_sim (offsetToPc := offsetToPc) hswap2 hrel2 hlen2 hbSwap2 (by intro h; omega)
  have hps3stack : ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack
      = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var x, Operand.Var y] := by simp
  have hstacktop : as3.stack = wy :: wx :: as3.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel3 hps3stack hvy hvx
  have hfresh3 : ¬ (Operand.Var out) ∈ ({ ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } : PlanState).stack := by
    show ¬ (Operand.Var out) ∈ base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h | h)
    · exact hfresh h
    · exact hoy (by injection h)
    · exact hox (by injection h)
    · exact hox (by injection h)
    · exact hoy (by injection h)
  have hbEmit : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit name]) := by rw [hpc3, hpc2, hpcI]; exact hbEmitraw
  obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emit_binop_sim hrel3 hstacktop hfresh3 hps1spill hbEmit (fun h hg => hdisp as3 h hg)
  rw [hfcomm wy wx] at hrel4
  have hps5 : ({ { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] } with
      stack := stackPush (Operand.Var out) (stackPop 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] } := by
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] = (base ++ [Operand.Var y, Operand.Var x]) ++ [Operand.Var x, Operand.Var y] from by simp,
        stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps5] at hrel4
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrel4
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1
        ++ ([StackOp.SOSwap 1] ++ ([StackOp.SOSwap 2] ++ [StackOp.SOEmit name])))).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 1]).length
           + ((executePlan [StackOp.SOSwap 2]).length + (executePlan [StackOp.SOEmit name]).length)) := by
    rw [executePlan_append, executePlan_append, executePlan_append, List.length_append,
        List.length_append, List.length_append]
  refine ⟨as4, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrun2 (runAsm_compose hrun3 hrun4))
  · rw [hlenEq, hpc4, hpc3, hpc2, hpcI]; omega


/-- **`popmanyPlan`'s per-item step, discharged** — the `hpopstep` residual that
    `popmanyPlan_sim` has carried undischarged since it was stated (which is why it had no callers).

    `gpop p v` locates `v` on the plan stack, swaps it to the top if it isn't already there, and pops
    it. So the asm is `doSwap dist` followed by a single `POP`, and the two halves are already proved:
    `doSwap_sim` moves the value to TOS keeping `venomAsmRel`, and `emit_pop1_sim` drops it. The Venom
    state is untouched throughout — `popmanyPlan` only ever discards variables that are *dead*, and
    Venom keeps every variable in `vars` regardless of whether it is on the operand stack, which is
    exactly the slack `planStackRel` allows.

    `hbig` is `doSwap_sim`'s own big-swap side condition (only bites at depth > 16, where the swap goes
    through the temp spill region); at depth ≤ 16 it is vacuous. -/
theorem gpop_sim {p v lo vs as prog}
    (hrel : venomAsmRel lo p vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (gpop p v).1))
    (hbig : ∀ dist, stackGetDepth v p.stack = some dist → dist > 16 →
      (SpillAllocWf p.alloc ∧
       p.alloc.freeSlots = [] ∧
       p.alloc.nextOffset + 32 * (dist + 1) < 2 ^ 256 ∧
       p.alloc.nextOffset + 32 * (dist + 1) ≤ as.memory.size ∧
       (∀ o off', alookup' p.spilled o = some off' → off' + 32 ≤ p.alloc.nextOffset))) :
    ∃ as', runAsm (executePlan (gpop p v).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (gpop p v).2 vs as' ∧
           as'.pc = as.pc + (executePlan (gpop p v).1).length := by
  cases hd : stackGetDepth v p.stack with
  | none =>
    -- `v` is not on the stack: nothing to pop
    have hgp : gpop p v = ([], p) := by unfold gpop; rw [hd]
    rw [hgp]
    exact ⟨as, rfl, hrel, by rw [show executePlan ([] : List StackOp) = [] from rfl]; simp⟩
  | some dist =>
    have hlt : dist < p.stack.length := stackGetDepth_lt_length hd
    rcases hsw : (if dist = 0 then (([], p) : List StackOp × PlanState) else doSwap dist p)
      with ⟨swapOps, ps'⟩
    have hgp : gpop p v
        = (swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack }) := by
      unfold gpop; rw [hd]; simp only []; rw [hsw]
    rw [hgp] at hblock ⊢
    rw [executePlan_append] at hblock
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    -- the swap half (a no-op when `v` is already on top)
    have hswap : ∃ as1, runAsm (executePlan swapOps).length offsetToPc prog as = AsmResult.AsmOK as1 ∧
        venomAsmRel lo ps' vs as1 ∧ as1.pc = as.pc + (executePlan swapOps).length ∧
        ps'.stack.length = p.stack.length := by
      by_cases h0 : dist = 0
      · rw [if_pos h0] at hsw
        obtain ⟨rfl, rfl⟩ : swapOps = [] ∧ ps' = p :=
          ⟨(congrArg Prod.fst hsw).symm, (congrArg Prod.snd hsw).symm⟩
        exact ⟨as, rfl, hrel,
          by rw [show executePlan ([] : List StackOp) = [] from rfl]; simp, rfl⟩
      · rw [if_neg h0] at hsw
        obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
          doSwap_sim hsw hrel hlt hb1 (fun hb => by
            have := hbig dist hd hb; exact this)
        refine ⟨as1, hrun1, hrel1, hpc1, ?_⟩
        have := doSwap_length (dist := dist) (ps := p) hlt
        rw [hsw] at this; exact this
    obtain ⟨as1, hrun1, hrel1, hpc1, hlen'⟩ := hswap
    -- the pop half
    have haslen : 0 < as1.stack.length := by
      have hps := planStackRel_length hrel1.1
      omega
    obtain ⟨a, rest, hstk⟩ : ∃ a rest, as1.stack = a :: rest := by
      cases hs : as1.stack with
      | nil => rw [hs] at haslen; simp at haslen
      | cons a r => exact ⟨a, r, rfl⟩
    have hb2' : asmBlockAt prog as1.pc (executePlan [StackOp.SOPop 1]) := by rw [hpc1]; exact hb2
    obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emit_pop1_sim hrel1 hstk hb2'
    refine ⟨as2, ?_, hrel2, ?_⟩
    · rw [executePlan_append, List.length_append]; exact runAsm_compose hrun1 hrun2
    · rw [executePlan_append, List.length_append, hpc2, hpc1]; omega


/-- Popping 1 then `n` more is popping `n+1` (`stackPop k = take (length - k)`). -/
theorem stackPop_succ (n : Nat) (stk : List Operand) :
    stackPop n (stackPop 1 stk) = stackPop (n + 1) stk := by
  unfold stackPop
  rw [List.length_take, List.take_take]
  congr 1
  omega

/-- **The `n`-fold `POP` runner** — `SOPop n` lowers to `n` copies of `AsmOp "POP"`, and running them
    drops the top `n` of the asm stack while the plan side does `stackPop n`. The Venom state is
    untouched (`planStackRel_popN`: Venom keeps every variable in `vars` whether or not it is on the
    operand stack). This is the atom the contiguous-top branch of `popmanyPlan` bottoms out in — the
    `hcontig` residual — the `n`-ary companion of `emit_pop1_sim`. -/
theorem emit_popN_sim {lo : AssocList String Nat} {vs : VenomState} {prog : List AsmInst} :
    ∀ (n : Nat) (ps : PlanState) (as : AsmState),
      venomAsmRel lo ps vs as →
      n ≤ ps.stack.length →
      asmBlockAt prog as.pc (executePlan [StackOp.SOPop n]) →
      ∃ as', runAsm (executePlan [StackOp.SOPop n]).length offsetToPc prog as
               = AsmResult.AsmOK as' ∧
             venomAsmRel lo { ps with stack := stackPop n ps.stack } vs as' ∧
             as'.pc = as.pc + (executePlan [StackOp.SOPop n]).length := by
  intro n
  induction n with
  | zero =>
    intro ps as hrel _ _
    refine ⟨as, rfl, ?_, by simp [executePlan, execStackOp]⟩
    rw [stackPop_zero]
    exact hrel
  | succ k ih =>
    intro ps as hrel hn hblock
    have hpn : ∀ m : Nat, executePlan [StackOp.SOPop m] = List.replicate m (AsmInst.AsmOp "POP") := by
      intro m; simp [executePlan, execStackOp]
    have hep : executePlan [StackOp.SOPop (k + 1)]
        = AsmInst.AsmOp "POP" :: executePlan [StackOp.SOPop k] := by
      rw [hpn, hpn, List.replicate_succ]
    rw [hep] at hblock
    -- one POP …
    have hb1 : asmBlockAt prog as.pc (executePlan [StackOp.SOPop 1]) := by
      obtain ⟨hget, _⟩ := asmBlockAt_cons_drop hblock
      refine ⟨?_, ?_⟩
      · rcases hblock with ⟨hlen, _⟩
        show as.pc + 1 ≤ prog.length
        simp only [hep, List.length_cons] at hlen
        omega
      · intro j hj
        have hj1 : j < 1 := by rw [hpn] at hj; simpa using hj
        interval_cases j
        rw [hpn]; simpa using hget
    have haslen : 0 < as.stack.length := by
      have := planStackRel_length hrel.1; omega
    obtain ⟨a, rest, hstk⟩ : ∃ a rest, as.stack = a :: rest := by
      cases hs : as.stack with
      | nil => rw [hs] at haslen; simp at haslen
      | cons a r => exact ⟨a, r, rfl⟩
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ := emit_pop1_sim hrel hstk hb1
    -- … then `k` more
    have hlen1 : (stackPop 1 ps.stack).length = ps.stack.length - 1 := by
      unfold stackPop; rw [List.length_take]; omega
    have hk : k ≤ ({ ps with stack := stackPop 1 ps.stack } : PlanState).stack.length := by
      show k ≤ (stackPop 1 ps.stack).length; rw [hlen1]; omega
    have hb2 : asmBlockAt prog as1.pc (executePlan [StackOp.SOPop k]) := by
      obtain ⟨_, hrest⟩ := asmBlockAt_cons_drop hblock
      have hp1 : as1.pc = as.pc + 1 := by rw [hpc1, hpn]; simp
      rw [hp1]; exact hrest
    obtain ⟨as2, hrun2, hrel2, hpc2⟩ := ih { ps with stack := stackPop 1 ps.stack } as1 hrel1 hk hb2
    refine ⟨as2, ?_, ?_, ?_⟩
    · rw [hep, List.length_cons]
      have h1 : (executePlan [StackOp.SOPop 1]).length = 1 := by rw [hpn]; simp
      have := runAsm_compose hrun1 hrun2
      rw [h1] at this
      rw [show (executePlan [StackOp.SOPop k]).length + 1
            = 1 + (executePlan [StackOp.SOPop k]).length from by omega]
      exact this
    · have : ({ { ps with stack := stackPop 1 ps.stack } with
                stack := stackPop k (stackPop 1 ps.stack) } : PlanState)
             = { ps with stack := stackPop (k + 1) ps.stack } := by
        rw [stackPop_succ]
      rw [← this]; exact hrel2
    · rw [hep, List.length_cons, hpc2, hpc1, hpn]
      simp
      omega






/-- `gpop` never grows the plan stack (it pops one, after an optional length-preserving swap). -/
theorem gpop_stack_length_le (p : PlanState) (v : Operand) :
    (gpop p v).2.stack.length ≤ p.stack.length := by
  cases hd : stackGetDepth v p.stack with
  | none => have hgp : gpop p v = ([], p) := by unfold gpop; rw [hd]
            rw [hgp]
  | some dist =>
    have hlt : dist < p.stack.length := stackGetDepth_lt_length hd
    rcases hsw : (if dist = 0 then (([], p) : List StackOp × PlanState) else doSwap dist p)
      with ⟨swapOps, ps'⟩
    have hgp : gpop p v
        = (swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack }) := by
      unfold gpop; rw [hd]; simp only []; rw [hsw]
    have hlen : ps'.stack.length = p.stack.length := by
      by_cases h0 : dist = 0
      · rw [if_pos h0] at hsw
        have : ps' = p := (congrArg Prod.snd hsw).symm
        rw [this]
      · rw [if_neg h0] at hsw
        have := doSwap_length (dist := dist) (ps := p) hlt
        rw [hsw] at this; exact this
    rw [hgp]
    show (stackPop 1 ps'.stack).length ≤ p.stack.length
    unfold stackPop; rw [List.length_take]; omega

/-- **`popmanyPlan`'s per-item fold branch, discharged under a shallow-stack invariant.**

    The other half of `popmanyPlan_sim`'s undischarged residual. Its `hpopstep` was quantified over
    *every* plan state, which cannot be supplied: at an unbounded stack depth `doSwap` may exceed
    `SWAP16` and route through the temp spill region, dragging in `doSwap_sim`'s big-swap side
    condition. `foldl_ops_sim_inv` is the harness built for exactly this — the per-step sim need only
    hold on states satisfying an invariant it preserves.

    The invariant here is `stack.length ≤ 17`: any depth found is `< length ≤ 17`, hence `≤ 16`, so the
    big-swap condition is **vacuous** at every step; and `gpop` only ever shrinks the stack
    (`gpop_stack_length_le`), so the invariant is preserved for free. Together with
    `popmanyPlan_sim_closed` this closes both of `popmanyPlan`'s branches. -/
theorem popmany_fold_sim {lo : AssocList String Nat} {vs : VenomState} {prog : List AsmInst} :
    ∀ (l : List Operand) (ps0 : PlanState) (as0 : AsmState),
      ps0.stack.length ≤ 17 →
      venomAsmRel lo ps0 vs as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc v => (acc.1 ++ (gpop acc.2 v).1, (gpop acc.2 v).2))
          ([], ps0)).1) →
      ∃ as', runAsm
              (executePlan (l.foldl (fun acc v => (acc.1 ++ (gpop acc.2 v).1, (gpop acc.2 v).2))
                ([], ps0)).1).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo
              (l.foldl (fun acc v => (acc.1 ++ (gpop acc.2 v).1, (gpop acc.2 v).2)) ([], ps0)).2
              vs as' ∧
             as'.pc = as0.pc +
              (executePlan (l.foldl (fun acc v => (acc.1 ++ (gpop acc.2 v).1, (gpop acc.2 v).2))
                ([], ps0)).1).length := by
  intro l ps0 as0 hInv0 hrel0 hblock
  exact foldl_ops_sim_inv lo vs prog offsetToPc gpop
    (fun p => p.stack.length ≤ 17)
    (fun v p hp => le_trans (gpop_stack_length_le p v) hp)
    (fun v p sA hp hrelp hbp =>
      gpop_sim hrelp hbp
        (fun dist hd hgt => absurd hgt (by
          have := stackGetDepth_lt_length hd; omega)))
    l ps0 as0 hInv0 hrel0 hblock



/-- **`popmanyPlan` simulates — closed, no residuals.** The replacement for `popmanyPlan_sim`, whose
    two ∀-quantified residual hypotheses (`hpopstep`, `hcontig`) were never discharged and which
    consequently had no callers.

    `popmanyPlan` has two real branches and both are now proved:
      * doomed variables at contiguous depths → one `doSwap n` + one `SOPop n`
        (`isContiguousTop` itself forces `n ≤ 16`, so no big swap);
      * otherwise → a per-item swap-and-pop fold (`popmany_fold_sim`, via `popmany_step_eq`), closed
        under the shallow-stack invariant that makes every swap distance `≤ 16`.

    `hshallow` (`stack.length ≤ 17`) is what keeps every `doSwap` inside `SWAP16` and so out of the
    temp spill region — the honest cost of avoiding the big-swap side condition at each fold step.
    `hlen` says you cannot pop more than you have; it is only used by the contiguous branch.

    The Venom state is unchanged throughout: `popmanyPlan` discards only *dead* variables, and Venom
    keeps every variable in `vars` whether or not it is on the operand stack. -/
theorem popmanyPlan_sim_closed {toPop : List Operand} {ps ps' : PlanState} {ops : List StackOp}
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hpop : popmanyPlan toPop ps = (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hshallow : ps.stack.length ≤ 17)
    (hlen : toPop.length < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  -- the shallow stack bounds every swap distance by 16, so no swap spills
  have hn16 : toPop.length ≤ 16 := by omega
  refine popmanyPlan_sim_inv (fun p => p.stack.length ≤ 17)
    (fun v p hp => le_trans (gpop_stack_length_le p v) hp) hshallow hpop hrel hblock
    (fun v p sA hp hrelp hbp =>
      gpop_sim hrelp hbp
        (fun dist hd hgt => absurd hgt (by have := stackGetDepth_lt_length hd; omega)))
    ?_
  -- the contiguous branch: one `doSwap n`, then one `SOPop n`
  intro hbc
  rw [executePlan_append] at hbc ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hbc
  have hsw : doSwap toPop.length ps
      = ((doSwap toPop.length ps).1, (doSwap toPop.length ps).2) := rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    doSwap_sim hsw hrel hlen hb1 (fun hb => absurd hb (by omega))
  have hlenA : (doSwap toPop.length ps).2.stack.length = ps.stack.length :=
    doSwap_length (dist := toPop.length) (ps := ps) hlen
  have hnle : toPop.length ≤ (doSwap toPop.length ps).2.stack.length := by rw [hlenA]; omega
  have hb2' : asmBlockAt prog as1.pc (executePlan [StackOp.SOPop toPop.length]) := by
    rw [hpc1]; exact hb2
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_popN_sim toPop.length (doSwap toPop.length ps).2 as1 hrel1 hnle hb2'
  refine ⟨as2, ?_, hrel2, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · rw [List.length_append, hpc2, hpc1]; omega



/-- **Block-prologue simulation: the leading label plus the clean-stack pops.**

    This is the brick the `toPop ≠ []` join was missing. A block's plan is
    `SOLabel :: cleanOps ++ bodyOps ++ termOps` (`generateBlockPlan_split_term_clean`), and the
    clean-stack prologue is non-empty exactly at a join that genuinely drops values: one predecessor,
    that predecessor branches, and some variable live at its exit is not an input here. Every existing
    layout lemma assumed the prologue away (`CleanTrivial`) and so started the body at `as0.pc + 1` and
    the body fold at the block's *entry* plan state.

    Here the prologue is executed: `soLabel_sim` steps over the `JUMPDEST`, then
    `popmanyPlan_sim_closed` runs the pops, landing the body at
    `as0.pc + 1 + (executePlan cleanOps).length` in plan state `ps2` — the state *after* the pops,
    which is exactly where the body fold begins. The Venom state is unchanged across the whole
    prologue, since only dead variables are discarded.

    Specialising `cleanOps = []` / `ps2 = ps` gives back the old hand-off at `as0.pc + 1`. -/
theorem blockPrologue_sim {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps ps2 : PlanState} {cleanOps : List StackOp}
    {lo : AssocList String Nat} {vs : VenomState} {as0 : AsmState} {prog : List AsmInst}
    {predLbl : String} {predBb : BasicBlock}
    (hpreds : C.predsOf bb.label = [predLbl])
    (hbranch : ¬ (C.succsOf predLbl).length ≤ 1)
    (hpfind : fn.blocks.find? (·.label == predLbl) = some predBb)
    (hclean : cleanStackPlan L C fn bb ps = (cleanOps, ps2))
    (hrel : venomAsmRel lo ps vs as0)
    (hshallow : ps.stack.length ≤ 17)
    (hlen : ((liveVarsAt L predLbl predBb.instructions.length).filter
              (fun v => ¬ (inputVarsFrom predLbl bb.instructions
                (liveVarsAt L bb.label 0)).contains v)).length < ps.stack.length)
    (hblock : asmBlockAt prog as0.pc (executePlan ([StackOp.SOLabel bb.label] ++ cleanOps))) :
    ∃ asMid, runAsm (executePlan ([StackOp.SOLabel bb.label] ++ cleanOps)).length
               offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
             venomAsmRel lo ps2 vs asMid ∧
             asMid.pc = as0.pc + (executePlan ([StackOp.SOLabel bb.label] ++ cleanOps)).length := by
  -- the clean-stack prologue *is* a `popmanyPlan` over the dropped variables
  have hpop : popmanyPlan
      (((liveVarsAt L predLbl predBb.instructions.length).filter
        (fun v => ¬ (inputVarsFrom predLbl bb.instructions
          (liveVarsAt L bb.label 0)).contains v)).map Operand.Var) ps
      = (cleanOps, ps2) := by
    rw [← hclean]
    unfold cleanStackPlan
    rw [hpreds]
    simp only [if_neg hbranch, hpfind]
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  -- the JUMPDEST
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ := soLabel_sim lo ps vs as0 prog bb.label hrel hb1
  -- the pops
  have hb2' : asmBlockAt prog as1.pc (executePlan cleanOps) := by rw [hpc1]; exact hb2
  have hlen' : (((liveVarsAt L predLbl predBb.instructions.length).filter
      (fun v => ¬ (inputVarsFrom predLbl bb.instructions
        (liveVarsAt L bb.label 0)).contains v)).map Operand.Var).length < ps.stack.length := by
    rw [List.length_map]; exact hlen
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    popmanyPlan_sim_closed hpop hrel1 hshallow hlen' hb2'
  refine ⟨as2, ?_, hrel2, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · rw [List.length_append, hpc2, hpc1]; omega



/-- **The block prologue as a plain asm segment**: JUMPDEST then the clean-stack pops. The
    `popmanyPlan`-level core of `blockPrologue_sim` (which reads `toPop` off the CFG); this form is what
    the block simulations compose with. Venom state untouched — only dead variables are discarded. -/
theorem blockPrologue_prefix_sim {lo : AssocList String Nat} {vs : VenomState} {prog : List AsmInst}
    {ps0 ps2 : PlanState} {cleanOps : List StackOp} {toPop : List Operand}
    {as0 : AsmState} {l : String}
    (hrel : venomAsmRel lo ps0 vs as0)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlen : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc (executePlan ([StackOp.SOLabel l] ++ cleanOps))) :
    ∃ asMid, runAsm (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length offsetToPc prog as0
               = AsmResult.AsmOK asMid ∧
             venomAsmRel lo ps2 vs asMid ∧
             asMid.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length := by
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ := soLabel_sim lo ps0 vs as0 prog l hrel hb1
  have hb2' : asmBlockAt prog as1.pc (executePlan cleanOps) := by rw [hpc1]; exact hb2
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := popmanyPlan_sim_closed hpop hrel1 hshallow hlen hb2'
  refine ⟨as2, ?_, hrel2, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · rw [List.length_append, hpc2, hpc1]; omega



/-- **The join bridge: the phi's hypothesis is *derived*, not assumed.**

`planStackRel_phi_poke_offSlot` needs to know that the phi binds its output to the value sitting in
that asm slot. That has been an input up to now. Here it is *earned*, from the only relation that is
actually true on arrival: the one with respect to the **arriving** predecessor's exit layout — which is
exactly what that predecessor's own block simulation hands you.

Off the phi slot the two layouts agree, so the relation transfers verbatim (the phi's output is fresh,
so `updateVar` disturbs nothing there). *At* the phi slot the arriving layout names that edge's own
source `src`; the relation therefore says the asm slot holds `src`'s value, and the phi binds `out` to
precisely that. So the recorded layout — which names some *other* edge's source there — is repaired.

This is the step an `hstep` for a genuine join consumes: relation-on-arrival in, relation-against-the-
recorded-plan out. -/
theorem planStackRel_phi_join_bridge {lo : AssocList String Nat} {vs : VenomState}
    {psArr psRec : List Operand} {asmStack : List bytes32} {d : Nat} {src out : String} {v : bytes32}
    (hrel : planStackRel lo vs psArr asmStack)
    (hlen : psRec.length = psArr.length)
    (hd : d < psRec.length)
    (hoff : ∀ i, i < psRec.length → i ≠ d → psRec.reverse[i]! = psArr.reverse[i]!)
    (hsrc : psArr.reverse[d]! = Operand.Var src)
    (hval : lookupVar src vs = some v)
    (hfresh : ∀ i, i < psRec.length → i ≠ d → psRec.reverse[i]! ≠ Operand.Var out) :
    planStackRel lo (updateVar out v vs) (stackPoke d (Operand.Var out) psRec) asmStack := by
  obtain ⟨hlenA, hcorr⟩ := hrel
  refine planStackRel_phi_poke_offSlot (by rw [hlen]; exact hlenA) hd ?_ ?_
  · -- off the phi slot: the layouts agree and `out` is fresh, so the relation transfers
    intro i hi hne
    rw [hoff i hi hne, operandVal_updateVar_ne _ _ _ _ _ (by rw [← hoff i hi hne]; exact hfresh i hi hne)]
    exact hcorr i (by omega)
  · -- at the phi slot: the asm value IS `src`'s value, and the phi binds `out` to it
    have hdA : d < psArr.length := by omega
    have hthis := hcorr d hdA
    rw [hsrc] at hthis
    have hlk : lookupVar src vs = some (asmStack[d]!) := hthis
    have hv : v = asmStack[d]! := by
      rw [hval] at hlk
      exact Option.some.inj hlk
    rw [hv]
    exact lookupVar_updateVar_self vs out _



/-- Bind a whole batch of phi outputs. -/
def updateVars : List (String × bytes32) → VenomState → VenomState
  | [], vs => vs
  | (o, v) :: rest, vs => updateVars rest (updateVar o v vs)

/-- A variable none of the phis defines is untouched by the batch. -/
theorem lookupVar_updateVars_notMem :
    ∀ (l : List (String × bytes32)) (vs : VenomState) (w : String),
      w ∉ l.map Prod.fst → lookupVar w (updateVars l vs) = lookupVar w vs := by
  intro l
  induction l with
  | nil => intro vs w _; rfl
  | cons x rest ih =>
    intro vs w hw
    simp only [List.map_cons, List.mem_cons, not_or] at hw
    unfold updateVars
    rw [ih _ w hw.2]
    exact lookupVar_updateVar_ne vs x.1 w x.2 hw.1

/-- Each phi output really does read back its own value (outputs are distinct). -/
theorem lookupVar_updateVars_mem :
    ∀ (l : List (String × bytes32)) (vs : VenomState) (o : String) (v : bytes32),
      (l.map Prod.fst).Nodup → (o, v) ∈ l →
      lookupVar o (updateVars l vs) = some v := by
  intro l
  induction l with
  | nil => intro _ _ _ _ hm; simp at hm
  | cons x rest ih =>
    intro vs o v hnd hm
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold updateVars
    rcases List.mem_cons.mp hm with rfl | hr
    · rw [lookupVar_updateVars_notMem rest _ o hnd.1]
      exact lookupVar_updateVar_self vs o v
    · exact ih _ o v hnd.2 hr



/-- A join's phi prologue, as data: for each phi, the stack depth it owns, the source arriving on
*this* edge, the output it defines, and the value that source carries. -/
abbrev PhiEdge := Nat × String × String × bytes32

abbrev PhiEdge.depth (x : PhiEdge) : Nat := x.1
abbrev PhiEdge.src   (x : PhiEdge) : String := x.2.1
abbrev PhiEdge.out   (x : PhiEdge) : String := x.2.2.1
abbrev PhiEdge.val   (x : PhiEdge) : bytes32 := x.2.2.2

/-- **The join bridge, for a whole phi prologue.**

`planStackRel_phi_join_bridge` earns the phi's hypothesis for *one* phi. It cannot simply be iterated:
after repairing one slot the relation against the recorded layout is still false at every *other* phi
slot, so its "relation holds off the slot" hypothesis fails at the second phi. The phis have to be taken
together — the same shape the plan side and the poke side both forced.

Input: the relation against the **arriving** predecessor's exit layout, which is what that predecessor's
block simulation gives you and is true on every edge. Output: the relation against the **recorded** plan
stack, which is what the block was compiled for. In between, every phi's slot is repaired at once. -/
theorem planStackRel_phi_join_bridge_multi {lo : AssocList String Nat} {vs vs' : VenomState}
    {psArr psRec : List Operand} {asmStack : List bytes32} (l : List PhiEdge)
    (hrel : planStackRel lo vs psArr asmStack)
    (hlen : psRec.length = psArr.length)
    (hd : ∀ x ∈ l, x.depth < psRec.length)
    -- off *all* the phi slots the two layouts agree
    (hoff : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ x.depth) → psRec.reverse[i]! = psArr.reverse[i]!)
    -- at its own slot, the arriving layout names *this* edge's source, carrying its value
    (hsrc : ∀ x ∈ l, psArr.reverse[x.depth]! = Operand.Var x.src)
    (hval : ∀ x ∈ l, lookupVar x.src vs = some x.val)
    -- the phi outputs are fresh on the recorded stack
    (hfresh : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ x.depth) →
        ∀ x ∈ l, psRec.reverse[i]! ≠ Operand.Var x.out)
    -- the post-state: each phi output holds its value, and nothing else moved. Stated by *behaviour*,
    -- not by construction — `evalPhis` builds it in its own order, and the bridge must not care.
    (hout : ∀ x ∈ l, lookupVar x.out vs' = some x.val)
    (hpres : ∀ w, w ∉ l.map PhiEdge.out → lookupVar w vs' = lookupVar w vs) :
    planStackRel lo vs'
      (l.foldl (fun st x => stackPoke x.depth (Operand.Var x.out) st) psRec) asmStack := by
  obtain ⟨hlenA, hcorr⟩ := hrel
  have hfold : l.foldl (fun st x => stackPoke x.depth (Operand.Var x.out) st) psRec
      = (l.map (fun x => (x.depth, x.out))).foldl
          (fun s (dp : Nat × String) => stackPoke dp.1 (Operand.Var dp.2) s) psRec := by
    rw [List.foldl_map]
  rw [hfold]
  refine planStackRel_phi_pokes (l.map (fun x => (x.depth, x.out))) psRec
      (by rw [hlen]; exact hlenA) ?_ ?_ ?_
  · intro dp hdp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hdp
    exact hd x hx
  · -- off every phi slot: layouts agree, no phi output sits there, so nothing the phis wrote is read
    intro i hi hne
    have hne' : ∀ x ∈ l, i ≠ x.depth := by
      intro x hx
      exact hne (x.depth, x.out) (List.mem_map_of_mem hx)
    rw [hoff i hi hne']
    have hnv : ∀ x ∈ l, psArr.reverse[i]! ≠ Operand.Var x.out := by
      intro x hx; rw [← hoff i hi hne']; exact hfresh i hi hne' x hx
    have hstep : operandVal vs' lo (psArr.reverse[i]!) = operandVal vs lo (psArr.reverse[i]!) := by
      cases hop : psArr.reverse[i]! with
      | Lit w => rfl
      | Label m => rfl
      | Var w =>
        show lookupVar w vs' = lookupVar w vs
        refine hpres w ?_
        intro hmem
        obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hmem
        exact hnv x hx (by rw [hop]; exact congrArg Operand.Var hxw.symm)
    rw [hstep]
    exact hcorr i (by omega)
  · -- at each phi slot: the asm value IS this edge's source value, and the phi bound `out` to it
    intro dp hdp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hdp
    have hdA : x.depth < psArr.length := by have := hd x hx; omega
    have harr := hcorr x.depth hdA
    rw [hsrc x hx] at harr
    have hlk : lookupVar x.src vs = some (asmStack[x.depth]!) := harr
    have hv : x.val = asmStack[x.depth]! := by
      rw [hval x hx] at hlk; exact Option.some.inj hlk
    show lookupVar x.out vs' = some (asmStack[x.depth]!)
    rw [hout x hx, hv]

end EvmYul.Venom.Hol.Codegen

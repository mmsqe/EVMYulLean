/-
GenBlockSimComp / CfgWalk / clean-stack prologues, the DJMP switch, fuel sufficiency, the phi-join, instIdx-obliviousness & fresh labels

Sub-split of `GenBlockSimComp/CfgWalk` (phase 6, the CFG walk); see `GenBlockSimComp`'s
header for the full roadmap. Continues the `EvmYul.Venom.Hol.Codegen` namespace and imports the previous
part — layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.CfgWalkDischarge

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ### Clean-stack prologue: the JNZ family -/

/-- Aligned JNZ block plan with a clean-stack prologue. `hemit`/`hreorder` are now quantified over the
    body fold from the *post-pop* state, which is where the body actually starts. -/
theorem generateBlockPlan_aligned_jnz_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      blockOps = StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++
        [StackOp.SODup 1, StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
         StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, termOps, hclean, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term_clean L D C fn bb ps blockOps ps' front term hentry hnp hplan
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2] at hterm_step
  have h1 : (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).1 = termOps :=
    congrArg Prod.fst (Option.some.inj hterm_step)
  have hto : termOps = [StackOp.SODup 1, StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
      StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := by
    rw [← h1]
    exact generateRegularInstPlan_jnz_full hterm_jnz hterm_ops hterm_outs
      (hemit ps2 bodyOps ps_body hbody) (hreorder ps2 bodyOps ps_body hbody)
  rw [hblk, hto]

/-- Whole-program asm of a JNZ block with a clean-stack prologue. -/
theorem blockplan_aligned_jnz_prog_asm_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
            ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hblockeq⟩ :=
    generateBlockPlan_aligned_jnz_clean L D C fn bb ps_in blockOps ps' front term c ifNz ifZ hentry0
      hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockeq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++ [StackOp.SODup 1,
        StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI", StackOp.SOPushLabel ifZ,
        StackOp.SOEmit "JUMP"]
      = [StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps) ++ [StackOp.SODup 1,
        StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI", StackOp.SOPushLabel ifZ,
        StackOp.SOEmit "JUMP"] := by
    simp [List.append_assoc]
  rw [heq, executePlan_aligned_jnz_block]

/-- Asm layout of a JNZ block with a clean-stack prologue — the five tail positions still sit at
    segment-length .. segment-length+4. -/
theorem blockplan_aligned_jnz_layout_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ cleanOps ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)),
        (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl) ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length]'h = AsmInst.AsmOp "DUP1") ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 1 < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 1]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifNz)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 2 < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 2]'h = AsmInst.AsmOp "JUMPI") ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 3 < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 3]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifZ)) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 4 < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 4]'h = AsmInst.AsmOp "JUMP") := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hprog⟩ :=
    blockplan_aligned_jnz_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      c ifNz ifZ hentry0 hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp hseg
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
        ++ ([AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))) _
      (fun a ha lbl => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).2 lbl d)
  all_goals
    have hpre : executePlan ops
        = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
        ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    obtain ⟨hd', hn', hj', hz', hm'⟩ := aligned_jnz_tail_resolved
      (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      (executePlan tailOps) ifNz ifZ
    first
      | (simpa [List.length_append] using hd')
      | (simpa [List.length_append] using hn')
      | (simpa [List.length_append] using hj')
      | (simpa [List.length_append] using hz')
      | (simpa [List.length_append] using hm')

/-- `pcOfLabel` of a JNZ block with a clean-stack prologue — identical statement to the `CleanTrivial`
    version. -/
theorem pcOfLabel_aligned_jnz_block_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (c ifNz ifZ : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, _hclean, _hbody, hprog⟩ :=
    blockplan_aligned_jnz_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      c ifNz ifZ hentry0 hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp hseg
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
      = AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps) := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps)
        ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan (cleanOps ++ bodyOps) ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
                AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]



/-- Spill-aware JNZ-taken entry segment *through* a clean-stack prologue — the `toPop ≠ []` counterpart
    of `hasm_regularHSVP_jnz_taken`. The body fold runs from the post-pop state, and `bodyLen` absorbs
    the pops, so the DUP1/push/JUMPI tail still sits at `as0.pc + bodyLen ..+2`. -/
theorem hasm_regularHSVP_jnz_taken_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l ifNz : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    -- the condition: a var at the fold-output TOS, non-zero
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    -- the resolved conditional tail
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd asMid ∧
      asMid.pc = idx ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  -- DUP1
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  -- push-label ifNz ; JUMPI, taken
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpush' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpush
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have ejumpi : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := idx } :=
    resolved_jumpi_taken_sim (by rw [hs1]) hcond hpc2' hpush' hoff_lk hoff hpc3' hjumpi' hidx_lk
  -- the taken JUMPI restores the fold-exit stack: the final state is asMid at the target pc
  have hfinal : ({ s1 with stack := cond :: rest, pc := idx } : AsmState)
      = { asMid with pc := idx } := by
    rw [hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idx } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejumpi
  refine ⟨{ asMid with pc := idx }, ?_, venomAsmRel_setPc hbrel, rfl,
    hbsd.rebuild (Nat.le_refl _) (fun _ _ h => h) hbsd.shallow hbsd.defined, hbsv⟩
  rw [show bodyLen + 3 = bodyLen + (1 + 2) from rfl, runAsm_add_ok hbrun,
      show (1 + 2 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]
  exact ejumpi


/-- Spill-aware JNZ-not-taken entry segment *through* a clean-stack prologue — the fall-through
    counterpart of `hasm_regularHSVP_jnz_taken_clean`. -/
theorem hasm_regularHSVP_jnz_nottaken_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l ifNz ifZ : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {bodyLen offNz offZ idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    -- the condition: a var at the fold-output TOS, zero
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    -- the resolved conditional tail
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as0.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as0.pc + bodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as0.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd asMid ∧
      asMid.pc = idxZ ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  -- DUP1
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  -- push-label ifNz ; JUMPI, NOT taken (condition zero)
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpushNz' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpushNz
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have efall : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := s1.pc + 2 } :=
    resolved_jumpi_nottaken_sim (by rw [hs1, hcond]) hpc2' hpushNz' hoffNz_lk hoffNz
      hpc3' hjumpi'
  set s2 := ({ s1 with stack := cond :: rest, pc := s1.pc + 2 } : AsmState) with hs2
  have hs2pc : s2.pc = asMid.pc + 3 := by rw [hs2]; show s1.pc + 2 = _; rw [hs1pc]
  -- push-label ifZ ; JUMP
  have hpc4' : s2.pc < prog.length := by rw [hs2pc, hbpc]; exact hpc4
  have hpushZ' : prog.get ⟨s2.pc, hpc4'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ) :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hpushZ
  have hpc5' : s2.pc + 1 < prog.length := by rw [hs2pc, hbpc]; exact hpc5
  have hjump' : prog.get ⟨s2.pc + 1, hpc5'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hjump
  have ejump : runAsm 2 offsetToPc prog s2 = AsmResult.AsmOK { s2 with pc := idxZ } :=
    resolved_jump_sim hpc4' hpushZ' hoffZ_lk hoffZ hpc5' hjump' hidxZ_lk
  -- the fall-through restored the fold-exit stack: the final state is asMid at the ifZ target
  have hfinal : ({ s2 with pc := idxZ } : AsmState) = { asMid with pc := idxZ } := by
    rw [hs2, hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idxZ } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejump
  refine ⟨{ asMid with pc := idxZ }, ?_, venomAsmRel_setPc hbrel, rfl,
    hbsd.rebuild (Nat.le_refl _) (fun _ _ h => h) hbsd.shallow hbsd.defined, hbsv⟩
  have e01 : runAsm 3 offsetToPc prog asMid = AsmResult.AsmOK s2 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]
    exact efall
  have e02 : runAsm 5 offsetToPc prog asMid = AsmResult.AsmOK { asMid with pc := idxZ } := by
    rw [show (5 : Nat) = 3 + 2 from rfl, runAsm_add_ok e01]
    exact ejump
  rw [runAsm_add_ok hbrun]
  exact e02



/-! ### Clean-stack prologue: the RETURN / REVERT family -/

/-- Aligned RETURN/REVERT block plan with a clean-stack prologue. -/
theorem generateBlockPlan_aligned_return_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false)
    (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      blockOps = StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++
        ((emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name]) := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, termOps, hclean, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term_clean L D C fn bb ps blockOps ps' front term hentry hnp hplan
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2] at hterm_step
  have h1 : (generateRegularInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
      (bbIsHalting bb) false bb.label ps_body).1 = termOps :=
    congrArg Prod.fst (Option.some.inj hterm_step)
  have hto : termOps = (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
      (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name] := by
    rw [← h1]
    exact generateRegularInstPlan_return_full hname hncomm hnjmp hco hterm_outs
      (hreorderNil ps2 bodyOps ps_body hbody)
  rw [hblk, hto]


/-- Whole-program asm of a RETURN/REVERT block with a clean-stack prologue. -/
theorem blockplan_aligned_return_prog_asm_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
            (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
              (liveVarsAt L bb.label bb.instructions.length) ps_body).1))
            ++ [AsmInst.AsmOp name]) ++ executePlan tailOps := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hblockeq⟩ :=
    generateBlockPlan_aligned_return_clean L D C fn bb ps_in blockOps ps' front term name offv szv
      hentry0 hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockeq]
  congr 2
  have hreassoc : StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++
        ((emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1 ++ [StackOp.SOEmit name])
      = [StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1) ++ [StackOp.SOEmit name] := by
    simp [List.append_assoc]
  rw [hreassoc, executePlan_aligned_bareHalt_block]


/-- Asm layout of a RETURN/REVERT block with a clean-stack prologue. -/
theorem blockplan_aligned_return_layout_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ cleanOps ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)),
        (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d))) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      asmBlockAt (asmResolve (executePlan ops)).1 (executePlan preOps).length
        (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1))) ∧
      (∃ h : (executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
              (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length) ps_body).1))).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
              (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length) ps_body).1))).length]'h
          = AsmInst.AsmOp name) := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hprog⟩ :=
    blockplan_aligned_return_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      name offv szv hentry0 hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp hseg
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
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
      · exact (hlblfree cleanOps ps2 bodyOps ps_body hbody a h).1 lbl
      · exact (executePlan_no_label _
          (emitInputPlan_no_label term.opcode _ [Operand.Var szv, Operand.Var offv]
            (by intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop;
                rcases hop with rfl | rfl <;> simp) ps_body) a h).1 lbl
    · intro a ha lbl d
      rw [← List.append_assoc, executePlan_append, List.mem_append] at ha
      rcases ha with h | h
      · exact (hlblfree cleanOps ps2 bodyOps ps_body hbody a h).2 lbl d
      · exact (executePlan_no_label _
          (emitInputPlan_no_label term.opcode _ [Operand.Var szv, Operand.Var offv]
            (by intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop;
                rcases hop with rfl | rfl <;> simp) ps_body) a h).2 lbl d
  · have hpre : executePlan ops = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1)))
        ++ [AsmInst.AsmOp name] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := aligned_bareHalt_tail_resolved (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
      (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1))) (executePlan tailOps) name
    simpa [List.length_append] using this


/-- `pcOfLabel` of a RETURN/REVERT block with a clean-stack prologue — identical statement to the `CleanTrivial` version. -/
theorem pcOfLabel_aligned_return_block_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String) (offv szv : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ ps2 bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, _hclean, _hbody, hprog⟩ :=
    blockplan_aligned_return_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      name offv szv hentry0 hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp hseg
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps ++
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1))
      = AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps ++
          (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1) := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps ++
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1) ++ [AsmInst.AsmOp name])
        ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan (cleanOps ++ bodyOps ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1)
            ++ [AsmInst.AsmOp name] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]


/-- Spill-aware RETURN segment *through* a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hasm_regularHSVP_return_var`. -/
theorem hasm_regularHSVP_return_var_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    -- the return operands: live members of the grown shape, unspilled in the exit map
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    -- memory facts, checked at the entry state / the fold output
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    -- layout
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hbudget : bodyLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel
             (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallowPS hlenPop hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  -- operand membership + depths at the fold output
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps2)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  -- run the operand emission
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- the operand values on the asm top
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  -- RETURN halts; coverage lifted from the entry state across the whole run
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "RETURN" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact runAsm_memory_size_mono hbrun
  have hcompose : runAsm (bodyLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmHalt ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + emitLen + 1 = bodyLen + (emitLen + 1) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok herun]
    exact runAsm_return 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  exact venomAsmRel_return (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel hsafe' hlen


/-- Spill-aware REVERT segment *through* a clean-stack prologue — the REVERT counterpart. -/
theorem hasm_regularHSVP_revert_var_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    -- the return operands: live members of the grown shape, unspilled in the exit map
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    -- memory facts, checked at the entry state / the fold output
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    -- layout
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "REVERT")
    (hbudget : bodyLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel
             (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallowPS hlenPop hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  -- operand membership + depths at the fold output
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps2)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  -- run the operand emission
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- the operand values on the asm top
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  -- RETURN halts; coverage lifted from the entry state across the whole run
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "REVERT" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact runAsm_memory_size_mono hbrun
  have hcompose : runAsm (bodyLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmRevert ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + emitLen + 1 = bodyLen + (emitLen + 1) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok herun]
    exact runAsm_revert 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  exact venomAsmRel_revert (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel hsafe' hlen


/-- Spill-aware per-block JNZ-taken simulation *through* a clean-stack prologue — the `toPop ≠ []`
    counterpart of `genBlockSimulation_regularHSVP_jnz_taken`. -/
theorem genBlockSimulation_regularHSVP_jnz_taken_clean
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    {ifNz : String} {off idx : Nat}
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo ifNz sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧ asMid.pc = idx ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 (jumpTo ifNz sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 (jumpTo ifNz sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo ifNz sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jnz_taken_clean (vs0 := vs0) (ifNz := ifNz) (base := base) (c := c) (cond := cond)
      P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock hbodyLenEq hstkF hcval hcond hpc1 hdup
      hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩


/-- Spill-aware per-block JNZ-not-taken simulation *through* a clean-stack prologue — the `toPop ≠ []`
    counterpart of `genBlockSimulation_regularHSVP_jnz_nottaken`. -/
theorem genBlockSimulation_regularHSVP_jnz_nottaken_clean
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    {ifNz ifZ : String} {offNz offZ idxZ : Nat}
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as0.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as0.pc + bodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as0.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo ifZ sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧ asMid.pc = idxZ ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 (jumpTo ifZ sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 (jumpTo ifZ sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo ifZ sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jnz_nottaken_clean (vs0 := vs0) (ifNz := ifNz) (ifZ := ifZ) (base := base) (c := c)
      (cond := cond) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock hbodyLenEq hstkF hcval
      hcond hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5
      hjump hidxZ_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩


/-- **The DJMP trampoline, with the whole asm state exposed.** Same run as `djmp_trampoline_sim`, but
    the conclusion names the resulting state exactly: `{ s with pc := idx, stack := rest }`. That is the
    missing link for `venomAsmRel` — the old conclusion gave only `s'.pc` and `s'.stack`, so there was no
    way to know the switch had left memory, spills, accounts and the rest of the machine alone, and hence
    no way to carry the relation across it. It plainly has: every step is a `JUMPDEST`/`POP`/`PUSH`/`JUMP`,
    all of which touch only the pc and the stack. -/
theorem djmp_trampoline_sim_state {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {t l : String} {off idx : Nat} {sel : bytes32} {rest : List bytes32}
    (hstack : s.stack = sel :: rest)
    (hpc0 : s.pc < prog.length) (hg0 : prog.get ⟨s.pc, hpc0⟩ = AsmInst.AsmLabel t)
    (hpc1 : s.pc + 1 < prog.length) (hg1 : prog.get ⟨s.pc + 1, hpc1⟩ = AsmInst.AsmOp "POP")
    (hpc2 : s.pc + 2 < prog.length)
    (hpush : prog.get ⟨s.pc + 2, hpc2⟩ = resolveInst offsets (AsmInst.AsmPushLabel l))
    (hoff_lk : AssocList.lookup String Nat offsets l = some off) (hoff : off < 2 ^ 256)
    (hpc3 : s.pc + 3 < prog.length) (hg3 : prog.get ⟨s.pc + 3, hpc3⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runAsm 4 offsetToPc prog s
      = AsmResult.AsmOK { s with pc := idx, stack := rest } := by
  have e0 : asmStep offsetToPc prog s = AsmResult.AsmOK (asmNext s) := asmStep_label_ok hpc0 hg0
  set s1 := asmNext s with hs1
  have hs1pc : s1.pc = s.pc + 1 := rfl
  have hpc1' : s1.pc < prog.length := by rw [hs1pc]; exact hpc1
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK ({ asmNext s1 with stack := rest }) := by
    have hg1' : prog.get ⟨s1.pc, hpc1'⟩ = AsmInst.AsmOp "POP" := by
      rw [show (⟨s1.pc, hpc1'⟩ : Fin _) = ⟨s.pc + 1, hpc1⟩ from Fin.ext hs1pc]; exact hg1
    have hs1stack : s1.stack = sel :: rest := by rw [hs1]; exact hstack
    rw [asmStep]
    split
    · next h =>
      rw [show prog.get ⟨s1.pc, h⟩ = AsmInst.AsmOp "POP" from hg1']
      simp only [asmPop, hs1stack]
    · next hc => exact absurd hpc1' hc
  set s2 := ({ asmNext s1 with stack := rest } : AsmState) with hs2
  have hs2pc : s2.pc = s.pc + 2 := by rw [hs2]; show (asmNext s1).pc = _; rw [hs1]; rfl
  have hpc2' : s2.pc < prog.length := by rw [hs2pc]; exact hpc2
  have hpush' : prog.get ⟨s2.pc, hpc2'⟩ = resolveInst offsets (AsmInst.AsmPushLabel l) := by
    rw [show (⟨s2.pc, hpc2'⟩ : Fin _) = ⟨s.pc + 2, hpc2⟩ from Fin.ext hs2pc]; exact hpush
  have hpc3' : s2.pc + 1 < prog.length := by rw [hs2pc]; exact hpc3
  have hg3' : prog.get ⟨s2.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMP" := by
    have e : s2.pc + 1 = s.pc + 3 := by rw [hs2pc]
    conv_lhs => rw [show (⟨s2.pc + 1, hpc3'⟩ : Fin prog.length) = ⟨s.pc + 3, hpc3⟩ from Fin.ext e]
    exact hg3
  have ejump : runAsm 2 offsetToPc prog s2 = AsmResult.AsmOK { s2 with pc := idx } :=
    resolved_jump_sim hpc2' hpush' hoff_lk hoff hpc3' hg3' hidx_lk
  have hst : ({ s2 with pc := idx } : AsmState) = { s with pc := idx, stack := rest } := rfl
  rw [← hst, runAsm_succ_ok hpc0 e0, runAsm_succ_ok hpc1' e1]
  exact ejump


/-- **The DJMP n-way switch, with the whole asm state exposed.** `djmp_switch_sim` established only
    `s'.pc = target` and `s'.stack = rest`. That is enough to say where control lands, but *not* enough to
    carry `venomAsmRel` across the switch — the relation constrains memory, spills, accounts, transient
    storage, logs and the rest, and the old conclusion said nothing about any of them.

    This version names the state exactly: `{ s with pc := target, stack := rest }`. Nothing else moves,
    which is obvious once said — every instruction in the switch (`DUP1`, `PUSH`, `EQ`, `JUMPI`, `POP`,
    `JUMP`, `JUMPDEST`) touches only the pc and the operand stack — but it had to be *proved* to be
    usable, and it is what unblocks `venomAsmRel_djmp_switch`. -/
theorem djmp_switch_sim_state {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {sel : bytes32} {rest : List bytes32}
    (pre : List (List byte × String × Nat)) (s : AsmState) (hstack : s.stack = sel :: rest)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog (s.pc + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        sel ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere offsets prog (s.pc + 5 * pre.length) matb tName matoff)
    (hsel : sel = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target) :
    runAsm (5 * pre.length + 5 + 4) offsetToPc prog s
      = AsmResult.AsmOK { s with pc := target, stack := rest } := by
  -- (1) scan the non-matching prefix
  have hscan := djmp_scan_nottaken (offsetToPc := offsetToPc) pre s hstack hpre
  set sI := ({ s with stack := sel :: rest, pc := s.pc + 5 * pre.length } : AsmState) with hsI
  -- (2) take the matching entry → trampoline
  obtain ⟨⟨m0, mg0⟩, ⟨m1, mg1⟩, ⟨m2, mg2⟩, ⟨m3, mg3⟩, mlk, moff, ⟨m4, mg4⟩⟩ := hmatch
  -- `sI.pc` is defeq `s.pc + 5*pre.length`, so the positional hyps feed the brick directly
  have htaken : runAsm 5 offsetToPc prog sI
      = AsmResult.AsmOK { sI with stack := sel :: rest, pc := idxTramp } := by
    refine djmp_entry_taken_sim (s := sI) (rfl) ?_ m0 mg0 m1 mg1 m2 mg2 m3 mg3 mlk moff m4 mg4 hidx_lk
    rw [djmpVal] at hsel; exact hsel
  set sT := ({ sI with stack := sel :: rest, pc := idxTramp } : AsmState) with hsT
  -- (3) run the trampoline → target (`sT.pc` is defeq `idxTramp`)
  obtain ⟨t0, tg0⟩ := ht0; obtain ⟨t1, tg1⟩ := ht1; obtain ⟨t2, tg2⟩ := ht2; obtain ⟨t3, tg3⟩ := ht3
  have htramp : runAsm 4 offsetToPc prog sT
      = AsmResult.AsmOK { sT with pc := target, stack := rest } :=
    djmp_trampoline_sim_state (s := sT) (rfl) t0 tg0 t1 tg1 t2 tg2 hl_lk hloff t3 tg3 htarget_lk
  -- compose 5*|pre| + 5 + 4, tracking the state through
  have hst : ({ sT with pc := target, stack := rest } : AsmState)
      = { s with pc := target, stack := rest } := rfl
  rw [← hst, show 5 * pre.length + 5 + 4 = 5 * pre.length + (5 + 4) from by ring,
      runAsm_add_ok hscan, runAsm_add_ok htaken]
  exact htramp



/-- **`venomAsmRel` survives the DJMP comparison switch** — the fact item 3 was missing.

    `djmp_switch_sim` located the switch's landing pc and stack, but said nothing about the rest of the
    machine, so the codegen relation could not be carried across it and `DJMP` had no per-block story.
    With `djmp_switch_sim_state` naming the whole resulting state, the relation follows immediately:
    the switch only pops the selector, so the plan side does `stackPop 1` and every other component —
    memory, spills, the allocator, accounts, transient storage, returndata, logs, and the whole shared
    environment — is literally unchanged. `venomAsmRel` does not constrain the pc at all
    (`venomAsmRel_setPc`), so landing at the selected target is free.

    This is the DJMP analogue of what `popmanyPlan` needed for the clean-stack prologue, and it has the
    same shape: an asm-only stack edit that Venom cannot observe. -/
theorem venomAsmRel_djmp_switch {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    {s : AsmState} {sel : bytes32} {rest : List bytes32}
    (pre : List (List byte × String × Nat))
    (hrel : venomAsmRel lo ps vs s)
    (hstack : s.stack = sel :: rest)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog (s.pc + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        sel ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere offsets prog (s.pc + 5 * pre.length) matb tName matoff)
    (hsel : sel = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target) :
    ∃ s', runAsm (5 * pre.length + 5 + 4) offsetToPc prog s = AsmResult.AsmOK s' ∧
          s'.pc = target ∧
          venomAsmRel lo { ps with stack := stackPop 1 ps.stack } vs s' := by
  refine ⟨{ s with pc := target, stack := rest }, ?_, rfl, ?_⟩
  · exact djmp_switch_sim_state (offsetToPc := offsetToPc) pre s hstack hpre hmatch hsel hidx_lk
      ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  · -- the switch pops the selector and touches nothing else; `venomAsmRel` ignores the pc
    have hpop := venomAsmRel_pop hrel hstack
    have heq : ({ asmNext s with stack := rest } : AsmState)
        = { s with pc := s.pc + 1, stack := rest } := rfl
    rw [heq] at hpop
    exact venomAsmRel_setPc (p := target) hpop



/-! ### DJMP switch: reading the layout off the plan

`venomAsmRel_djmp_switch` consumes a `djmpEntryHere` fact per switch entry, at `base + 5*k`. Those must
come from the plan, and the plan does not *look* uniform: `djmpChain` threads a `freshLabel` through each
entry, so the trampoline names are not syntactically apparent. Pinning that down — the `k`-th trampoline
is `djmp_tramp_(base+1+k)` — is what reveals the chain for what it is: a flat run of 5-op entries, hence
a flat run of 5 asm instructions each, hence the `k`-th entry at exactly `5*k`. -/

/-- Shifting the start index of `zipIdx` shifts every recorded position. -/
theorem zipIdx_shift {α : Type} (l : List α) : ∀ (n : Nat),
    l.zipIdx (n+1) = (l.zipIdx n).map (fun p => (p.1, p.2 + 1)) := by
  induction l with
  | nil => intro n; simp
  | cons a t ih =>
    intro n
    simp only [List.zipIdx_cons, List.map_cons, ih (n+1), ih n, List.map_map]

/-- The `k`-th trampoline label `djmpChain` mints, as a function of the incoming label counter.
    This is the arithmetic the `freshLabel` threading hides. -/
def djmpTrampLabel (base k : Nat) : String := "djmp_tramp" ++ "_" ++ toString (base + 1 + k)

theorem djmpChain_ops :
    ∀ (labels : List String) (i : Nat) (ps : PlanState),
      (djmpChain i labels ps).1
        = (labels.zipIdx 0).flatMap (fun p =>
            [StackOp.SODup 1, StackOp.SOPush (Operand.Lit (UInt256.ofNat (i + p.2))),
             StackOp.SOEmit "EQ",
             StackOp.SOPushLabel (djmpTrampLabel ps.labelCounter p.2),
             StackOp.SOEmit "JUMPI"]) := by
  intro labels
  induction labels with
  | nil => intro i ps; rw [djmpChain]; simp
  | cons l rest ih =>
    intro i ps
    rw [djmpChain]
    simp only [freshLabel]
    rw [ih (i+1) { ps with labelCounter := ps.labelCounter + 1 }]
    rw [List.zipIdx_cons]
    simp only [List.flatMap_cons, zipIdx_shift rest 0, List.flatMap_map]
    congr 1
    refine List.flatMap_congr (fun x _ => ?_)
    simp only [djmpTrampLabel]
    have e1 : i + 1 + x.2 = i + (x.2 + 1) := by omega
    have e2 : ps.labelCounter + 1 + 1 + x.2 = ps.labelCounter + 1 + (x.2 + 1) := by omega
    rw [e1, e2]

/-- The asm of one switch entry: exactly the five instructions `djmpEntryHere` expects. -/
theorem executePlan_djmpEntry (i k base : Nat) :
    executePlan [StackOp.SODup 1, StackOp.SOPush (Operand.Lit (UInt256.ofNat (i + k))),
                 StackOp.SOEmit "EQ", StackOp.SOPushLabel (djmpTrampLabel base k),
                 StackOp.SOEmit "JUMPI"]
      = [AsmInst.AsmOp "DUP1",
         AsmInst.AsmPush (encodeNumBytes (UInt256.ofNat (i + k)).toNat),
         AsmInst.AsmOp "EQ",
         AsmInst.AsmPushLabel (djmpTrampLabel base k),
         AsmInst.AsmOp "JUMPI"] := by
  simp [executePlan, execStackOp, dupName]

/-- The whole switch chain's asm, in closed form: five instructions per entry. -/
theorem executePlan_djmpChain (labels : List String) (i : Nat) (ps : PlanState) :
    executePlan (djmpChain i labels ps).1
      = (labels.zipIdx 0).flatMap (fun p =>
          [AsmInst.AsmOp "DUP1",
           AsmInst.AsmPush (encodeNumBytes (UInt256.ofNat (i + p.2)).toNat),
           AsmInst.AsmOp "EQ",
           AsmInst.AsmPushLabel (djmpTrampLabel ps.labelCounter p.2),
           AsmInst.AsmOp "JUMPI"]) := by
  rw [djmpChain_ops]
  show List.flatMap execStackOp _ = _
  rw [List.flatMap_assoc]
  refine List.flatMap_congr (fun x _ => ?_)
  exact executePlan_djmpEntry i x.2 ps.labelCounter

/-- `flatMap` of a constant-length function. -/
theorem length_flatMap_const {α β : Type} (n : Nat) :
    ∀ (l : List α) (f : α → List β), (∀ x ∈ l, (f x).length = n) →
      (l.flatMap f).length = n * l.length := by
  intro l
  induction l with
  | nil => intro f _; simp
  | cons a t ih =>
    intro f h
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self, ih f (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    ring

/-- Hence the chain is exactly `5 * |labels|` instructions long — which is what makes the `k`-th
    entry live at `base + 5*k`. -/
theorem executePlan_djmpChain_length (labels : List String) (i : Nat) (ps : PlanState) :
    (executePlan (djmpChain i labels ps).1).length = 5 * labels.length := by
  rw [executePlan_djmpChain,
      length_flatMap_const 5 _ _ (fun x _ => by simp), List.length_zipIdx]

/-- **Indexing a constant-length `flatMap`**: the `k`-th block starts at `n*k`. -/
theorem flatMap_const_getElem? {α β : Type} (n : Nat) :
    ∀ (l : List α) (f : α → List β), (∀ x ∈ l, (f x).length = n) →
      ∀ (k : Nat) (hk : k < l.length) (j : Nat), j < n →
        (l.flatMap f)[n * k + j]? = (f l[k])[j]? := by
  intro l
  induction l with
  | nil => intro f _ k hk; simp at hk
  | cons a t ih =>
    intro f h k hk j hj
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
      rw [List.getElem?_append_left (by rw [h a List.mem_cons_self]; exact hj)]
      rfl
    | succ m =>
      have hm : m < t.length := by simp at hk; omega
      simp only [List.flatMap_cons]
      have hlen : (f a).length = n := h a List.mem_cons_self
      have hidx : n * (m + 1) + j = (f a).length + (n * m + j) := by rw [hlen]; ring
      rw [hidx, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [ih f (fun x hx => h x (List.mem_cons_of_mem _ hx)) m hm j hj]
      rfl

/-- **The `k`-th DJMP switch entry lives at offset `5*k`**, with comparison value `i+k` and trampoline
    `djmpTrampLabel base k`. This is the shape `djmpEntryHere` wants, read straight off the plan. -/
theorem executePlan_djmpChain_entry (labels : List String) (i : Nat) (ps : PlanState)
    (k : Nat) (hk : k < labels.length) :
    (executePlan (djmpChain i labels ps).1)[5 * k + 0]? = some (AsmInst.AsmOp "DUP1") ∧
    (executePlan (djmpChain i labels ps).1)[5 * k + 1]?
      = some (AsmInst.AsmPush (encodeNumBytes (UInt256.ofNat (i + k)).toNat)) ∧
    (executePlan (djmpChain i labels ps).1)[5 * k + 2]? = some (AsmInst.AsmOp "EQ") ∧
    (executePlan (djmpChain i labels ps).1)[5 * k + 3]?
      = some (AsmInst.AsmPushLabel (djmpTrampLabel ps.labelCounter k)) ∧
    (executePlan (djmpChain i labels ps).1)[5 * k + 4]? = some (AsmInst.AsmOp "JUMPI") := by
  rw [executePlan_djmpChain]
  have hz : (labels.zipIdx 0).length = labels.length := List.length_zipIdx
  have hk' : k < (labels.zipIdx 0).length := by rw [hz]; exact hk
  have hget : (labels.zipIdx 0)[k] = (labels[k], k) := by
    simp [List.getElem_zipIdx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [flatMap_const_getElem? 5 _ _ (fun x _ => by simp) k hk' _ (by omega), hget]; rfl)


/-- Indexing into the middle segment of a three-way append. -/
theorem getElem?_mid {α : Type} (pre mid post : List α) (m : Nat) (hm : m < mid.length) :
    (pre ++ mid ++ post)[pre.length + m]? = mid[m]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left hm]

/-- **Reading one instruction of a middle segment out of the resolved program.** Both DJMP bridges
    (`djmpEntryHere_of_chain`, `djmpTrampHere_of_chain`) do exactly this, at every position of every
    entry/trampoline: `asmResolve` is a pointwise `map`, so the instruction at `|pre| + m` in the resolved
    program is `resolveInst` applied to the segment's `m`-th instruction. -/
theorem resolved_get_of_mid {asm : List AsmInst} {pre mid post : List AsmInst}
    (hasm : asm = pre ++ mid ++ post) {m : Nat} {a : AsmInst}
    (hm : mid[m]? = some a) :
    ∃ h : pre.length + m < (asmResolve asm).1.length,
      (asmResolve asm).1.get ⟨pre.length + m, h⟩
        = resolveInst (computeLabelOffsets asm).2 a := by
  obtain ⟨hmlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  have hmid : asm[pre.length + m]? = some a := by
    rw [hasm, getElem?_mid pre mid post m hmlt]; exact hm
  have hr : (asmResolve asm).1[pre.length + m]?
      = some (resolveInst (computeLabelOffsets asm).2 a) := by
    rw [asmResolve_fst, List.getElem?_map, hmid]; rfl
  obtain ⟨h, hg⟩ := List.getElem?_eq_some_iff.mp hr
  exact ⟨h, by rw [List.get_eq_getElem]; exact hg⟩

/-- **`djmpEntryHere`, read off the plan.** The last layout fact DJMP's per-block sim needs: for a
    whole-function asm of the form `pre ++ <switch chain> ++ post`, the `k`-th switch entry really does
    sit at `|pre| + 5*k` in the *resolved* program, with the comparison value `i+k` and the trampoline
    `djmpTrampLabel base k`.

    Two things make this go through. `asmResolve` is a pointwise `map` (`asmResolve_fst`), and
    `resolveInst` is the identity on `AsmOp`/`AsmPush` — so the four non-label instructions of each entry
    survive resolution untouched, and the one `AsmPushLabel` resolves to exactly what `djmpEntryHere`
    asks for. Combined with `executePlan_djmpChain_entry` (the entry is at `5*k` within the chain), this
    is the fact `djmp_switch_sim_state` scans over and `venomAsmRel_djmp_switch` consumes. -/
theorem djmpEntryHere_of_chain {asm : List AsmInst}
    (labels : List String) (i : Nat) (ps : PlanState) (pre post : List AsmInst)
    (hasm : asm = pre ++ executePlan (djmpChain i labels ps).1 ++ post)
    (k : Nat) (hk : k < labels.length) {off : Nat}
    (hlk : AssocList.lookup String Nat (computeLabelOffsets asm).2
             (djmpTrampLabel ps.labelCounter k) = some off)
    (hoff : off < 2 ^ 256) :
    djmpEntryHere (computeLabelOffsets asm).2 (asmResolve asm).1 (pre.length + 5 * k)
      (encodeNumBytes (UInt256.ofNat (i + k)).toNat)
      (djmpTrampLabel ps.labelCounter k) off := by
  set O := (computeLabelOffsets asm).2 with hO
  obtain ⟨h0, h1, h2, h3, h4⟩ := executePlan_djmpChain_entry labels i ps k hk
  have key : ∀ (j : Nat) (a : AsmInst),
      (executePlan (djmpChain i labels ps).1)[5 * k + j]? = some a →
      ∃ h : pre.length + 5 * k + j < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 5 * k + j, h⟩ = resolveInst O a := by
    intro j a ha
    rw [show pre.length + 5 * k + j = pre.length + (5 * k + j) from by omega]
    exact resolved_get_of_mid hasm ha
  exact ⟨key 0 _ h0, key 1 _ h1, key 2 _ h2, key 3 _ h3, hlk, hoff, key 4 _ h4⟩


/-! ### DJMP switch: the trampolines

The mirror of the chain. `djmp_switch_sim` lands on the matching entry's trampoline and runs its four
instructions (`JUMPDEST ; POP ; PUSH target ; JUMP`) — the `POP` is what discards the selector, which is
why `venomAsmRel_djmp_switch` sees a plain `stackPop 1`. Same shape as the chain: `djmpChain` mints the
trampoline labels via `freshLabel`, so their positions only become readable once `djmpTrampLabel` pins
the counter arithmetic; then each trampoline is a flat 4-op block, hence 4 asm instructions, hence the
`k`-th at `4*k`. -/

/-- `djmpChain`'s trampolines, in closed form: four ops each — `JUMPDEST ; POP ; PUSH target ; JUMP`. -/
theorem djmpChain_tramps :
    ∀ (labels : List String) (i : Nat) (ps : PlanState),
      (djmpChain i labels ps).2.1
        = (labels.zipIdx 0).flatMap (fun p =>
            [StackOp.SOLabel (djmpTrampLabel ps.labelCounter p.2), StackOp.SOPop 1,
             StackOp.SOPushLabel p.1, StackOp.SOEmit "JUMP"]) := by
  intro labels
  induction labels with
  | nil => intro i ps; rw [djmpChain]; simp
  | cons l rest ih =>
    intro i ps
    rw [djmpChain]
    simp only [freshLabel]
    rw [ih (i+1) { ps with labelCounter := ps.labelCounter + 1 }]
    rw [List.zipIdx_cons]
    simp only [List.flatMap_cons, zipIdx_shift rest 0, List.flatMap_map]
    congr 1
    refine List.flatMap_congr (fun x _ => ?_)
    simp only [djmpTrampLabel]
    have e2 : ps.labelCounter + 1 + 1 + x.2 = ps.labelCounter + 1 + (x.2 + 1) := by omega
    rw [e2]

/-- Each trampoline is four asm instructions. -/
theorem executePlan_djmpTramp (base k : Nat) (l : String) :
    executePlan [StackOp.SOLabel (djmpTrampLabel base k), StackOp.SOPop 1,
                 StackOp.SOPushLabel l, StackOp.SOEmit "JUMP"]
      = [AsmInst.AsmLabel (djmpTrampLabel base k), AsmInst.AsmOp "POP",
         AsmInst.AsmPushLabel l, AsmInst.AsmOp "JUMP"] := by
  simp [executePlan, execStackOp]

theorem executePlan_djmpTramps (labels : List String) (i : Nat) (ps : PlanState) :
    executePlan (djmpChain i labels ps).2.1
      = (labels.zipIdx 0).flatMap (fun p =>
          [AsmInst.AsmLabel (djmpTrampLabel ps.labelCounter p.2), AsmInst.AsmOp "POP",
           AsmInst.AsmPushLabel p.1, AsmInst.AsmOp "JUMP"]) := by
  rw [djmpChain_tramps]
  show List.flatMap execStackOp _ = _
  rw [List.flatMap_assoc]
  refine List.flatMap_congr (fun x _ => ?_)
  exact executePlan_djmpTramp ps.labelCounter x.2 x.1

/-- The `k`-th trampoline's four instructions sit at offset `4*k`. -/
theorem executePlan_djmpTramps_entry (labels : List String) (i : Nat) (ps : PlanState)
    (k : Nat) (hk : k < labels.length) :
    (executePlan (djmpChain i labels ps).2.1)[4 * k + 0]?
      = some (AsmInst.AsmLabel (djmpTrampLabel ps.labelCounter k)) ∧
    (executePlan (djmpChain i labels ps).2.1)[4 * k + 1]? = some (AsmInst.AsmOp "POP") ∧
    (executePlan (djmpChain i labels ps).2.1)[4 * k + 2]?
      = some (AsmInst.AsmPushLabel labels[k]) ∧
    (executePlan (djmpChain i labels ps).2.1)[4 * k + 3]? = some (AsmInst.AsmOp "JUMP") := by
  rw [executePlan_djmpTramps]
  have hk' : k < (labels.zipIdx 0).length := by rw [List.length_zipIdx]; exact hk
  have hget : (labels.zipIdx 0)[k] = (labels[k], k) := by simp [List.getElem_zipIdx]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [flatMap_const_getElem? 4 _ _ (fun x _ => by simp) k hk' _ (by omega), hget]; rfl)

/-- **The `k`-th trampoline, in the resolved program.** Exactly the four positional facts
    `djmp_switch_sim`'s `ht0`..`ht3` want, at `|pre| + 4*k`. `AsmLabel`, `AsmOp` survive resolution
    untouched; the one `AsmPushLabel` resolves to the selected block's address, which is what the final
    `JUMP` consumes. -/
theorem djmpTrampHere_of_chain {asm : List AsmInst}
    (labels : List String) (i : Nat) (ps : PlanState) (pre post : List AsmInst)
    (hasm : asm = pre ++ executePlan (djmpChain i labels ps).2.1 ++ post)
    (k : Nat) (hk : k < labels.length) :
    (∃ h : pre.length + 4 * k < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 4 * k, h⟩
          = AsmInst.AsmLabel (djmpTrampLabel ps.labelCounter k)) ∧
    (∃ h : pre.length + 4 * k + 1 < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 4 * k + 1, h⟩ = AsmInst.AsmOp "POP") ∧
    (∃ h : pre.length + 4 * k + 2 < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 4 * k + 2, h⟩
          = resolveInst (computeLabelOffsets asm).2 (AsmInst.AsmPushLabel labels[k])) ∧
    (∃ h : pre.length + 4 * k + 3 < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 4 * k + 3, h⟩ = AsmInst.AsmOp "JUMP") := by
  set O := (computeLabelOffsets asm).2 with hO
  obtain ⟨h0, h1, h2, h3⟩ := executePlan_djmpTramps_entry labels i ps k hk
  have key : ∀ (j : Nat) (a : AsmInst),
      (executePlan (djmpChain i labels ps).2.1)[4 * k + j]? = some a →
      ∃ h : pre.length + 4 * k + j < (asmResolve asm).1.length,
        (asmResolve asm).1.get ⟨pre.length + 4 * k + j, h⟩ = resolveInst O a := by
    intro j a ha
    rw [show pre.length + 4 * k + j = pre.length + (4 * k + j) from by omega]
    exact resolved_get_of_mid hasm ha
  exact ⟨key 0 _ h0, key 1 _ h1, key 2 _ h2, key 3 _ h3⟩


/-! ### DJMP: the whole plan's layout

`generateDjmpPlan` is the comparison chain, then a `POP ; PUSH revert ; JUMP` default for the
out-of-range case (which the interpreter reports as `Error`, i.e. the trivial `hbsim` arm), then the
trampolines. Pinning the three segments' lengths is what fixes the two addresses `djmp_switch_sim`
needs: the `k`-th entry at `5*k`, and the `k`-th trampoline at `5n + 3 + 4*k`. -/

/-- `generateDjmpPlan` = comparison chain, then the out-of-range default, then the trampolines. -/
theorem generateDjmpPlan_ops (labels : List String) (ps : PlanState) :
    (generateDjmpPlan labels ps).1
      = (djmpChain 0 labels ps).1
        ++ [StackOp.SOPop 1, StackOp.SOPushLabel "revert", StackOp.SOEmit "JUMP"]
        ++ (djmpChain 0 labels ps).2.1 := by
  unfold generateDjmpPlan
  rfl

/-- The out-of-range default lowers to three asm instructions. -/
theorem executePlan_djmpDefault :
    executePlan [StackOp.SOPop 1, StackOp.SOPushLabel "revert", StackOp.SOEmit "JUMP"]
      = [AsmInst.AsmOp "POP", AsmInst.AsmPushLabel "revert", AsmInst.AsmOp "JUMP"] := by
  simp [executePlan, execStackOp]

/-- **The DJMP plan's asm layout**: the comparison chain occupies `[0, 5n)`, the default `[5n, 5n+3)`,
    and the trampolines `[5n+3, 5n+3+4n)`. So the `k`-th entry is at `5*k` and the `k`-th trampoline at
    `5n + 3 + 4*k` — the two addresses `djmp_switch_sim` needs. -/
theorem executePlan_generateDjmpPlan (labels : List String) (ps : PlanState) :
    executePlan (generateDjmpPlan labels ps).1
      = executePlan (djmpChain 0 labels ps).1
        ++ [AsmInst.AsmOp "POP", AsmInst.AsmPushLabel "revert", AsmInst.AsmOp "JUMP"]
        ++ executePlan (djmpChain 0 labels ps).2.1 := by
  rw [generateDjmpPlan_ops, executePlan_append, executePlan_append, executePlan_djmpDefault]

theorem executePlan_generateDjmpPlan_length (labels : List String) (ps : PlanState) :
    (executePlan (generateDjmpPlan labels ps).1).length = 5 * labels.length + 3 + 4 * labels.length := by
  rw [executePlan_generateDjmpPlan]
  have hc := executePlan_djmpChain_length labels 0 ps
  have ht : (executePlan (djmpChain 0 labels ps).2.1).length = 4 * labels.length := by
    rw [executePlan_djmpTramps, length_flatMap_const 4 _ _ (fun x _ => by simp), List.length_zipIdx]
  simp only [List.length_append, List.length_cons, List.length_nil, hc, ht]

/-- The trampoline segment starts at `5n + 3`, so the `k`-th trampoline is at `5n + 3 + 4*k`. -/
theorem djmpTramps_offset (labels : List String) (ps : PlanState) (pre : List AsmInst) :
    pre ++ executePlan (generateDjmpPlan labels ps).1
      = (pre ++ executePlan (djmpChain 0 labels ps).1
          ++ [AsmInst.AsmOp "POP", AsmInst.AsmPushLabel "revert", AsmInst.AsmOp "JUMP"])
        ++ executePlan (djmpChain 0 labels ps).2.1 := by
  rw [executePlan_generateDjmpPlan]
  simp [List.append_assoc]

theorem djmpTramps_offset_length (labels : List String) (ps : PlanState) (pre : List AsmInst) :
    (pre ++ executePlan (djmpChain 0 labels ps).1
      ++ [AsmInst.AsmOp "POP", AsmInst.AsmPushLabel "revert", AsmInst.AsmOp "JUMP"]).length
    = pre.length + 5 * labels.length + 3 := by
  rw [List.length_append, List.length_append, executePlan_djmpChain_length]
  simp


set_option maxHeartbeats 1000000 in
/-- **Spill-aware DJMP entry segment** (HSVP prefix + the n-way comparison switch). The DJMP twin of
    `hasm_regularHSVP_jmp`: the block runs its label + HSVP body, leaving the selector on top of the
    fold-output stack, and then the switch scans to the matching entry, takes its trampoline, and lands
    at the selected block with the selector popped.

    The plan side is `stackPop 1` on the body's output — nothing else moves, because the switch is an
    asm-only stack edit Venom cannot observe (`venomAsmRel_djmp_switch`). The switch's positional facts
    are inputs; `djmpEntryHere_of_chain` / `djmpTrampHere_of_chain` supply them from the plan. -/
theorem hasm_regularHSVP_djmp {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {selVar : String} {selVal : bytes32} {base : List Operand}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    -- the selector sits on top of the body's output stack
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.stack = base ++ [Operand.Var selVar])
    (hselval : operandVal sEnd lo (Operand.Var selVar) = some selVal)
    -- the switch, laid out immediately after the body
    (pre : List (List byte × String × Nat))
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere lo prog (as0.pc + bodyLen + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        selVal ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere lo prog (as0.pc + bodyLen + 5 * pre.length) matb tName matoff)
    (hsel : selVal = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst lo (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat lo lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target) :
    ∃ asMid, runAsm (bodyLen + (5 * pre.length + 5 + 4)) offsetToPc prog as0
               = AsmResult.AsmOK asMid ∧
      asMid.pc = target ∧
      venomAsmRel lo
        { (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 with
          stack := stackPop 1 (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack }
        sEnd asMid := by
  -- label + body
  obtain ⟨asB, hbrun, hbrel, hbpc, _, _⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  -- the selector is on top of the asm stack at the switch's entry
  have hstk : asB.stack = selVal :: asB.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hbrel hstkF hselval
  -- the switch
  have hpre' : ∀ (k : Nat) (hk : k < pre.length),
      djmpEntryHere lo prog (asB.pc + 5 * k) (pre.get ⟨k, hk⟩).1
        (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
      selVal ≠ djmpVal (pre.get ⟨k, hk⟩).1 := by rw [hbpc]; exact hpre
  have hmatch' : djmpEntryHere lo prog (asB.pc + 5 * pre.length) matb tName matoff := by
    rw [hbpc]; exact hmatch
  obtain ⟨as', hsrun, hspc, hsrel⟩ :=
    venomAsmRel_djmp_switch (offsetToPc := offsetToPc) pre hbrel hstk hpre' hmatch' hsel hidx_lk
      ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  exact ⟨as', by rw [runAsm_add_ok hbrun]; exact hsrun, hspc, hsrel⟩

set_option maxHeartbeats 1000000 in
/-- **Spill-aware per-block DJMP simulation.** The Venom side is a plain `OK (jumpTo target sEnd)` —
    `runBlock_ok` is terminator-agnostic, and `stepInstBase` on a `DJMP` produces exactly that shape. The
    asm side runs label + body + the n-way switch. The plan side ends at the body's output with the
    selector popped: the switch is an asm-only stack edit Venom cannot observe. -/
theorem genBlockSimulation_regularHSVP_djmp
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {selVar : String} {selVal : bytes32} {base : List Operand} {tgtLbl : String}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo tgtLbl sEnd))
    (hnohalt : (jumpTo tgtLbl sEnd).halted = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.stack = base ++ [Operand.Var selVar])
    (hselval : operandVal sEnd lo (Operand.Var selVar) = some selVal)
    (pre : List (List byte × String × Nat))
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere lo prog (as0.pc + bodyLen + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        selVal ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere lo prog (as0.pc + bodyLen + 5 * pre.length) matb tName matoff)
    (hsel : selVal = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst lo (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat lo lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo tgtLbl sEnd) ∧
    ∃ asMid, runAsm (bodyLen + (5 * pre.length + 5 + 4)) offsetToPc prog as0
               = AsmResult.AsmOK asMid ∧ asMid.pc = target ∧
      venomAsmRel lo
        { (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 with
          stack := stackPop 1 (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack }
        (jumpTo tgtLbl sEnd) asMid := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo tgtLbl sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hpc, hrel⟩ :=
    hasm_regularHSVP_djmp (vs0 := vs0) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq
      hstkF hselval pre hpre hmatch hsel hidx_lk ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  exact ⟨asMid, hrun, hpc, hrel⟩


/-! ### Fuel sufficiency: the DFS's visited set really is closed under successors

`DfsClosed` was introduced as a *decidable* stand-in for a fact that ought to be a theorem: with enough
fuel, the DFS recurses into every successor of every block it visits, so its visited set is closed. The
only thing standing in the way was fuel accounting, and the accounting is easier than it looks — the
fuel does **not** split across sibling calls (both `dfsSuccsEntries` and the worklist tail receive the
same `fuel`), so what must be bounded is the *depth* of the call tree, not the total number of calls.

The depth is bounded by `|worklist| + U·(S+2)`, where `U` counts unvisited blocks and `S` bounds the
out-degree: reaching a new block costs one `dfsEntriesAux` level, plus at most `S` levels to walk to it
within its predecessor's successor list, plus one `dfsSuccsEntries` level. Each fresh visit strictly
decreases `U`. -/

/-- Strict `countP` comparison: if `q` implies `p` on `l` and some element satisfies `p` but not `q`. -/
theorem countP_lt_countP {α : Type} :
    ∀ (l : List α) (p q : α → Bool),
      (∀ x ∈ l, q x = true → p x = true) →
      ∀ (x : α), x ∈ l → p x = true → q x = false →
      l.countP q < l.countP p := by
  intro l
  induction l with
  | nil => intro p q _ x hx; simp at hx
  | cons a t ih =>
    intro p q hle x hx hp hq
    have hsub : ∀ y ∈ t, q y = true → p y = true :=
      fun y hy => hle y (List.mem_cons_of_mem _ hy)
    have hmono : t.countP q ≤ t.countP p := List.countP_mono_left hsub
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [List.countP_cons, hp, hq]; simp; omega
    · by_cases hqa : q a = true
      · have hpa : p a = true := hle a List.mem_cons_self hqa
        have := ih p q hsub x hx' hp hq
        simp only [List.countP_cons, hqa, hpa]; simp; omega
      · have hqa' : q a = false := by simpa using hqa
        have := ih p q hsub x hx' hp hq
        simp only [List.countP_cons, hqa']
        by_cases hpa : p a = true
        · simp [hpa]; omega
        · have : p a = false := by simpa using hpa
          simp [this]; omega

/-- The DFS's progress measure: how many of `fn`'s blocks are still unvisited. -/
def unvisitedCount (fn : IrFunction) (visited : List String) : Nat :=
  fn.blocks.countP (fun b => !visited.contains b.label)

/-- Growing `visited` never grows the unvisited count. -/
theorem unvisitedCount_mono {fn : IrFunction} {v v' : List String}
    (h : ∀ l, v.contains l = true → v'.contains l = true) :
    unvisitedCount fn v' ≤ unvisitedCount fn v := by
  unfold unvisitedCount
  refine List.countP_mono_left ?_
  intro b _ hb
  simp only [Bool.not_eq_true'] at hb ⊢
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  rw [h b.label hc] at hb
  exact absurd hb (by simp)

/-- Visiting a fresh, real block strictly shrinks the unvisited count. -/
theorem unvisitedCount_lt {fn : IrFunction} {visited : List String} {lbl : String} {bb : BasicBlock}
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hfresh : visited.contains lbl = false) :
    unvisitedCount fn (lbl :: visited) < unvisitedCount fn visited := by
  have hmem : bb ∈ fn.blocks := List.mem_of_find?_eq_some hfind
  have hlbl : bb.label = lbl := by
    have := List.find?_some hfind; simpa using this
  unfold unvisitedCount
  refine countP_lt_countP fn.blocks _ _ ?_ bb hmem ?_ ?_
  · intro b _ hb
    simp only [List.contains_cons, Bool.not_eq_true', Bool.or_eq_false_iff] at hb ⊢
    exact hb.2
  · simp only [Bool.not_eq_true', hlbl, hfresh]
  · simp [hlbl]

/-- The `[]`-valued companion of `lookup_foldl_insert_of_not_mem` (for `initLblMap`). -/
theorem lookup_foldl_insert_nil_of_not_mem (bbs : List BasicBlock)
    (m : AssocList String (List String)) (k : String) (hk : k ∉ bbs.map (·.label)) :
    AssocList.lookup String (List String)
      (bbs.foldl (fun m b => AssocList.insert String (List String) m b.label []) m) k
      = AssocList.lookup String (List String) m k := by
  induction bbs generalizing m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, lookup_insert_ne _ _ _ _ (fun h => hk.1 h)]

/-- **A label naming no block has no successors.** The `succs` map's keys are exactly the block labels
    (`initLblMap` seeds them, `buildSuccs` only overwrites them), so an unknown label looks up to `none`
    and `succsOf` defaults to `[]`. Needed because the DFS *does* visit dangling successor labels — it
    marks them and moves on — and the closure property must not stumble on them. -/
theorem succsOf_nil_of_not_block (fn : IrFunction) (l : String)
    (hl : l ∉ fn.blocks.map (·.label)) :
    (cfgAnalyze fn).succsOf l = [] := by
  show fmapLookupList (buildSuccs fn.blocks) l = []
  unfold fmapLookupList buildSuccs initLblMap
  rw [lookup_foldl_insert_of_not_mem fn.blocks _ l hl,
      lookup_foldl_insert_nil_of_not_mem fn.blocks _ l hl]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The DFS is closed under CFG successors, given enough fuel.** Mutual induction on fuel, with the
    measure `|worklist| + U·(S+2)` (and `+1` on the successor side). Two conclusions are threaded: every
    worklist entry ends up visited (which is what lets a block's successors be marked), and every block
    this call freshly visits has all its successors visited by the end.

    `hnb` handles dangling successor labels — the DFS visits them and moves on, and they have no
    successors (`succsOf_nil_of_not_block`), so the closure property does not stumble on them. -/
theorem dfsEntries_closure (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (S : Nat)
    (hS : ∀ b ∈ fn.blocks, (C.succsOf b.label).length ≤ S)
    (hnb : ∀ l, fn.blocks.find? (·.label == l) = none → C.succsOf l = []) :
    ∀ (fuel : Nat),
    (∀ (wl visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (r : List String × AssocList String PlanState × PlanState),
      dfsEntriesAux fuel L D C fn wl visited tbl ps = some r →
      wl.length + unvisitedCount fn visited * (S + 2) ≤ fuel →
      (∀ w ∈ wl, r.1.contains w = true) ∧
      (∀ l, visited.contains l = false → r.1.contains l = true →
         ∀ s ∈ C.succsOf l, r.1.contains s = true))
    ∧
    (∀ (ss : List Operand) (sp : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (r : List String × AssocList String PlanState × PlanState),
      dfsSuccsEntries fuel L D C fn ss sp succs visited tbl psG = some r →
      succs.length + unvisitedCount fn visited * (S + 2) + 1 ≤ fuel →
      (∀ s ∈ succs, r.1.contains s = true) ∧
      (∀ l, visited.contains l = false → r.1.contains l = true →
         ∀ s ∈ C.succsOf l, r.1.contains s = true)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro wl visited tbl ps r hr hlen
      rw [dfsEntriesAux] at hr
      obtain rfl := Option.some.inj hr
      refine ⟨?_, ?_⟩
      · intro w hw
        have : wl.length = 0 := by omega
        rw [List.length_eq_zero_iff] at this; subst this; simp at hw
      · intro l hfr hin; rw [hfr] at hin; simp at hin
    · intro ss sp succs visited tbl psG r hr hlen
      omega
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · -- dfsEntriesAux (n+1)
      intro wl visited tbl ps r hr hlen
      cases wl with
      | nil =>
        rw [dfsEntriesAux_nil] at hr
        obtain rfl := Option.some.inj hr
        exact ⟨by simp, fun l hfr hin => by rw [hfr] at hin; simp at hin⟩
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl = true
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis] at hr
          have hb := ihA rest visited tbl ps r hr (by simp at hlen ⊢; omega)
          refine ⟨?_, hb.2⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact (dfsEntries_visited_mono L D C fn n).1 rest visited tbl ps r w hr hvis
          · exact hb.1 w hw'
        · have hvf : visited.contains lbl = false := by simpa using hvis
          have hmonoV : ∀ l, visited.contains l = true → (lbl :: visited).contains l = true := by
            intro l h; rw [List.contains_cons, h, Bool.or_true]
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvf hfind] at hr
            have hU : unvisitedCount fn (lbl :: visited) ≤ unvisitedCount fn visited :=
              unvisitedCount_mono hmonoV
            have hb := ihA rest (lbl :: visited) _ ps r hr (by simp at hlen ⊢; nlinarith [hlen, hU])
            refine ⟨?_, ?_⟩
            · intro w hw
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact (dfsEntries_visited_mono L D C fn n).1 rest (w :: visited) _ ps r w hr (by simp)
              · exact hb.1 w hw'
            · intro l hfr hin s hs
              by_cases hl : l = lbl
              · subst hl; rw [hnb l hfind] at hs; simp at hs
              · refine hb.2 l ?_ hin s hs
                rw [List.contains_cons, hfr, Bool.or_false, beq_eq_false_iff_ne]; exact hl
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvf hfind] at hr
            cases hbp : generateBlockPlan L D C fn bb ps with
            | none => rw [hbp] at hr; exact absurd hr (by simp)
            | some rbp =>
              obtain ⟨bo, ps'⟩ := rbp
              rw [hbp] at hr; simp only [] at hr
              cases hss : dfsSuccsEntries n L D C fn ps'.stack ps'.spilled (C.succsOf lbl)
                  (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps' with
              | none => rw [hss] at hr; exact absurd hr (by simp)
              | some rss =>
                obtain ⟨v2, tbl2, ps2⟩ := rss
                rw [hss] at hr; simp only [] at hr
                -- measures
                have hUlt : unvisitedCount fn (lbl :: visited) < unvisitedCount fn visited :=
                  unvisitedCount_lt hfind hvf
                have hmem : bb ∈ fn.blocks := List.mem_of_find?_eq_some hfind
                have hlbl : bb.label = lbl := by have := List.find?_some hfind; simpa using this
                have hsl : (C.succsOf lbl).length ≤ S := by rw [← hlbl]; exact hS bb hmem
                have hlen' : rest.length + unvisitedCount fn visited * (S + 2) ≤ n := by
                  simp at hlen; omega
                -- the successor walk
                have hSfuel : (C.succsOf lbl).length
                    + unvisitedCount fn (lbl :: visited) * (S + 2) + 1 ≤ n := by nlinarith [hlen', hUlt, hsl]
                obtain ⟨hSw, hScl⟩ := ihS ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited) _ ps'
                  (v2, tbl2, ps2) hss hSfuel
                -- the worklist tail
                have hmonoV2 : ∀ l, (lbl :: visited).contains l = true → v2.contains l = true :=
                  fun l h => (dfsEntries_visited_mono L D C fn n).2 ps'.stack ps'.spilled
                    (C.succsOf lbl) (lbl :: visited) _ ps' (v2, tbl2, ps2) l hss h
                have hU2 : unvisitedCount fn v2 ≤ unvisitedCount fn (lbl :: visited) :=
                  unvisitedCount_mono hmonoV2
                have hAfuel : rest.length + unvisitedCount fn v2 * (S + 2) ≤ n := by
                  nlinarith [hlen', hU2, hUlt]
                obtain ⟨hAw, hAcl⟩ := ihA rest v2 tbl2 ps2 r hr hAfuel
                have hmonoR : ∀ l, v2.contains l = true → r.1.contains l = true :=
                  fun l h => (dfsEntries_visited_mono L D C fn n).1 rest v2 tbl2 ps2 r l hr h
                refine ⟨?_, ?_⟩
                · intro w hw
                  rcases List.mem_cons.mp hw with rfl | hw'
                  · exact hmonoR w (hmonoV2 w (by simp))
                  · exact hAw w hw'
                · intro l hfr hin s hs
                  by_cases hl : l = lbl
                  · subst hl; exact hmonoR s (hSw s hs)
                  · have hfr2 : (lbl :: visited).contains l = false := by
                      rw [List.contains_cons, hfr, Bool.or_false, beq_eq_false_iff_ne]; exact hl
                    by_cases hv2 : v2.contains l = true
                    · exact hmonoR s (hScl l hfr2 hv2 s hs)
                    · exact hAcl l (by simpa using hv2) hin s hs
    · -- dfsSuccsEntries (n+1)
      intro ss sp succs visited tbl psG r hr hlen
      cases succs with
      | nil =>
        rw [dfsSuccsEntries] at hr
        obtain rfl := Option.some.inj hr
        exact ⟨by simp, fun l hfr hin => by rw [hfr] at hin; simp at hin⟩
      | cons succ srest =>
        rw [dfsSuccsEntries_cons] at hr
        cases hda : dfsEntriesAux n L D C fn [succ] visited tbl
            { psG with stack := ss, spilled := sp } with
        | none => rw [hda] at hr; exact absurd hr (by simp)
        | some rda =>
          obtain ⟨vA, tblA, psA⟩ := rda
          rw [hda] at hr; simp only [] at hr
          have hlen' : srest.length + unvisitedCount fn visited * (S + 2) + 1 ≤ n := by
            simp at hlen; omega
          obtain ⟨hAw, hAcl⟩ := ihA [succ] visited tbl _ (vA, tblA, psA) hda (by simp; omega)
          have hmonoA : ∀ l, visited.contains l = true → vA.contains l = true :=
            fun l h => (dfsEntries_visited_mono L D C fn n).1 [succ] visited tbl _
              (vA, tblA, psA) l hda h
          have hUA : unvisitedCount fn vA ≤ unvisitedCount fn visited := unvisitedCount_mono hmonoA
          cases hds : dfsSuccsEntries n L D C fn ss sp srest vA tblA
              { psG with alloc := psA.alloc, labelCounter := psA.labelCounter } with
          | none => rw [hds] at hr; exact absurd hr (by simp)
          | some rds =>
            obtain ⟨vF, tblF, psF⟩ := rds
            rw [hds] at hr; simp only [] at hr
            obtain rfl := Option.some.inj hr
            obtain ⟨hSw, hScl⟩ := ihS ss sp srest vA tblA _ (vF, tblF, psF) hds
              (by nlinarith [hlen', hUA])
            have hmonoF : ∀ l, vA.contains l = true → vF.contains l = true :=
              fun l h => (dfsEntries_visited_mono L D C fn n).2 ss sp srest vA tblA _
                (vF, tblF, psF) l hds h
            refine ⟨?_, ?_⟩
            · intro s hs
              rcases List.mem_cons.mp hs with rfl | hs'
              · exact hmonoF s (hAw s (by simp))
              · exact hSw s hs'
            · intro l hfr hin s hs
              by_cases hvA : vA.contains l = true
              · exact hmonoF s (hAcl l hfr hvA s hs)
              · exact hScl l (by simpa using hvA) hin s hs


theorem not_mem_labels_of_find?_none {fn : IrFunction} {l : String}
    (h : fn.blocks.find? (·.label == l) = none) : l ∉ fn.blocks.map (·.label) := by
  intro hmem
  obtain ⟨b, hb, hbl⟩ := List.mem_map.mp hmem
  have := List.find?_eq_none.mp h b hb
  simp [hbl] at this

theorem unvisitedCount_nil (fn : IrFunction) : unvisitedCount fn [] = fn.blocks.length := by
  unfold unvisitedCount
  simp

set_option maxHeartbeats 1000000 in
/-- **The closure, transported to the plan DFS's own visited set.** `dfsEntries_closure` speaks about
    `dfsEntriesAux`; the visited set a caller sees comes from `generateFnPlanAux`. `dfsEntries_faithful`
    says they agree, so both of the closure's conclusions transfer verbatim. This is the shared core of
    `dfsClosed_of_fuel` and `entryVisited_of_fuel` — the entry is visited (`.1`) and the visited set is
    closed (`.2`). -/
theorem dfsClosure_planDfs {fuel fnEom lblCtr : Nat} {fn : IrFunction} {elbl : String} (S : Nat)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hS : ∀ b ∈ fn.blocks, ((cfgAnalyze fn).succsOf b.label).length ≤ S)
    (hfuel : 1 + fn.blocks.length * (S + 2) ≤ fuel)
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hga : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [elbl] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, psF)) :
    vF.contains elbl = true ∧
    (∀ l, vF.contains l = true → ∀ s ∈ (cfgAnalyze fn).succsOf l, vF.contains s = true) := by
  obtain ⟨⟨vE, tbl, psE⟩, hda⟩ := Option.isSome_iff_exists.mp
    ((dfsEntriesAux_dfsSuccsEntries_isSome (livenessAnalyzeFuel fuel fn)
      (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn hfn fuel).1 [elbl] [] []
      { initPlanState fnEom with labelCounter := lblCtr })
  have hfaith := (dfsEntries_faithful (livenessAnalyzeFuel fuel fn)
    (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn fuel).1 [elbl] [] []
    { initPlanState fnEom with labelCounter := lblCtr }
  rw [hga, hda] at hfaith
  simp only [Option.map_some] at hfaith
  have hveq : vE = vF := congrArg (fun r => r.1) (Option.some.inj hfaith)
  obtain ⟨hw, hcl⟩ := (dfsEntries_closure (livenessAnalyzeFuel fuel fn)
    (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn S hS
    (fun l' hfnone => succsOf_nil_of_not_block fn l' (not_mem_labels_of_find?_none hfnone))
    fuel).1 [elbl] [] [] { initPlanState fnEom with labelCounter := lblCtr }
    (vE, tbl, psE) hda (by rw [unvisitedCount_nil]; simpa using hfuel)
  rw [hveq] at hw hcl
  exact ⟨hw elbl (by simp), fun l hl s hs => hcl l (by simp) hl s hs⟩

/-- `dfsVisited` *is* the plan DFS's visited set (when the plan exists). -/
theorem dfsVisited_eq {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    (hentry : entryBlock fn = some entry)
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hga : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, psF)) :
    dfsVisited fuel fn fnEom lblCtr = vF := by
  show (match (entryBlock fn).map (·.label) with
        | none => []
        | some lbl => match generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn)
                        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn [lbl] []
                        { initPlanState fnEom with labelCounter := lblCtr } with
                      | none => []
                      | some (_, v, _) => v) = vF
  rw [hentry]; simp only [Option.map_some]; rw [hga]

set_option maxHeartbeats 1000000 in
/-- **`DfsClosed` is a theorem, not a decidable side condition.** Given an out-degree bound `S` and
    `1 + |blocks|·(S+2) ≤ fuel`, the DFS's visited set is closed under CFG successors — so
    `visited_of_CfgReach` (and hence `reach_segment_gbp_fn`, and hence the whole `_reach` hstep family)
    no longer needs it supplied by `decide`.

    This was the last purely-structural hole in item 1: `dfsEntries_visited_reach` already gave
    visited ⇒ `CfgReach`, and this gives the converse. -/
theorem dfsClosed_of_fuel {fuel fnEom lblCtr : Nat} {fn : IrFunction} (S : Nat)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hS : ∀ b ∈ fn.blocks, ((cfgAnalyze fn).succsOf b.label).length ≤ S)
    (hfuel : 1 + fn.blocks.length * (S + 2) ≤ fuel) :
    DfsClosed fuel fn fnEom lblCtr := by
  intro l hl s hs
  -- `dfsVisited` is `[]` unless the entry exists and the plan DFS succeeds; both are vacuous here
  revert hl
  unfold dfsVisited
  cases hent : (entryBlock fn).map (·.label) with
  | none => intro hl; simp at hl
  | some elbl =>
    simp only []
    cases hga : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [elbl] [] { initPlanState fnEom with labelCounter := lblCtr } with
    | none => intro hl; simp at hl
    | some rga =>
      obtain ⟨ops, vF, psF⟩ := rga
      intro hl
      exact (dfsClosure_planDfs S hfn hS hfuel hga).2 l (by simpa using hl) s hs

/-- The accumulator only grows. -/
theorem foldl_add_ge {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat), a ≤ l.foldl (fun acc y => acc + f y) a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons y t ih => intro a; exact le_trans (Nat.le_add_right a (f y)) (ih (a + f y))

/-- Every element is at most the total. -/
theorem le_foldl_add {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat) (x : α), x ∈ l → f x ≤ l.foldl (fun acc y => acc + f y) a := by
  intro l
  induction l with
  | nil => intro a x hx; simp at hx
  | cons y t ih =>
    intro a x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (Nat.le_add_left (f x) a) (foldl_add_ge f t (a + f x))
    · exact ih (a + f y) x hx'

/-- **`fnPlanFuel` meets the bound.** Taking the out-degree bound to be the total edge count `e` — every
    block's successors are a subset of all of them — the requirement `1 + |blocks|·(e+2) ≤ fuel` is
    comfortably met by `fnPlanFuel = (b+1)·(b+e+2) + 10`. -/
theorem fnPlanFuel_sufficient {fn : IrFunction} (hnd : (fn.blocks.map (·.label)).Nodup) :
    (∀ b ∈ fn.blocks, ((cfgAnalyze fn).succsOf b.label).length
        ≤ fn.blocks.foldl (fun a bb => a + (bbSuccs bb).length) 0) ∧
    1 + fn.blocks.length * (fn.blocks.foldl (fun a bb => a + (bbSuccs bb).length) 0 + 2)
      ≤ fnPlanFuel fn := by
  set b := fn.blocks.length with hb
  set e := fn.blocks.foldl (fun a bb => a + (bbSuccs bb).length) 0 with he
  refine ⟨fun bb hbb => ?_, ?_⟩
  · rw [cfgAnalyze_succsOf_of_mem hnd hbb, he]
    exact le_foldl_add (fun x => (bbSuccs x).length) fn.blocks 0 bb hbb
  · show 1 + b * (e + 2) ≤ fnPlanFuel fn
    unfold fnPlanFuel
    simp only [← hb, ← he]
    nlinarith [Nat.zero_le b, Nat.zero_le e]

/-- **`DfsClosed` holds unconditionally for the real pipeline.** -/
theorem dfsClosed_fnPlanFuel {fnEom lblCtr : Nat} {fn : IrFunction}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst) :
    DfsClosed (fnPlanFuel fn) fn fnEom lblCtr :=
  dfsClosed_of_fuel _ hfn (fnPlanFuel_sufficient hnd).1 (fnPlanFuel_sufficient hnd).2

set_option maxHeartbeats 1000000 in
/-- **The entry block is visited** — the second of the `_reach` family's two side conditions, and the
    other half of `dfsClosure_planDfs`. -/
theorem entryVisited_of_fuel {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock} (S : Nat)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hS : ∀ b ∈ fn.blocks, ((cfgAnalyze fn).succsOf b.label).length ≤ S)
    (hfuel : 1 + fn.blocks.length * (S + 2) ≤ fuel)
    (hentry : entryBlock fn = some entry)
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hga : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, psF)) :
    (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true := by
  rw [dfsVisited_eq hentry hga]
  exact (dfsClosure_planDfs S hfn hS hfuel hga).1

/-- **Both `_reach` side conditions are theorems for the real pipeline.** A caller supplies neither
    `hclosed` nor `hent` by `decide`: CFG reachability alone places any reachable block. -/
theorem entryVisited_fnPlanFuel {fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hentry : entryBlock fn = some entry)
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hga : generateFnPlanAux (fnPlanFuel fn) (livenessAnalyzeFuel (fnPlanFuel fn) fn)
        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn [entry.label] []
        { initPlanState fnEom with labelCounter := lblCtr } = some (ops, vF, psF)) :
    (dfsVisited (fnPlanFuel fn) fn fnEom lblCtr).contains entry.label = true :=
  entryVisited_of_fuel _ hfn (fnPlanFuel_sufficient hnd).1 (fnPlanFuel_sufficient hnd).2 hentry hga


/-- A phi of the prologue together with what it does on *this* edge: its output, the source selected
for this predecessor, and that source's value. -/
abbrev PhiRun := Instruction × String × String × bytes32

abbrev PhiRun.inst (x : PhiRun) : Instruction := x.1
abbrev PhiRun.out  (x : PhiRun) : String := x.2.1
abbrev PhiRun.src  (x : PhiRun) : String := x.2.2.1
abbrev PhiRun.val  (x : PhiRun) : bytes32 := x.2.2.2

/-- **`evalPhis` over a whole PHI prefix, characterised by behaviour rather than construction.**

Phis are parallel: every one of them reads the *original* state, and `evalPhis` then applies the
updates outermost-first. A caller should not have to know that order — and must not, since it is not
the order any left-fold would produce. So the result is pinned by how it *looks up*: each output holds
its own selected value, every other variable is untouched. -/
theorem evalPhis_multi :
    ∀ (l : List PhiRun) (vs : VenomState) (prev : String),
      vs.prevBb = some prev →
      (∀ x ∈ l, x.inst.opcode = Opcode.PHI) →
      (∀ x ∈ l, x.inst.outputs = [x.out]) →
      (∀ x ∈ l, resolvePhi prev x.inst.operands = some (Operand.Var x.src)) →
      (∀ x ∈ l, lookupVar x.src vs = some x.val) →
      (l.map PhiRun.out).Nodup →
      ∃ vs', evalPhis vs (l.map PhiRun.inst) = ExecResult.OK vs'
        ∧ (∀ x ∈ l, lookupVar x.out vs' = some x.val)
        ∧ (∀ w, w ∉ l.map PhiRun.out → lookupVar w vs' = lookupVar w vs) := by
  intro l
  induction l with
  | nil => intro vs prev _ _ _ _ _ _; exact ⟨vs, rfl, by simp, by simp⟩
  | cons x rest ih =>
    intro vs prev hprev hphi houts hres hval hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨vs'', hev, hout'', hpres''⟩ :=
      ih vs prev hprev (fun y hy => hphi y (List.mem_cons_of_mem _ hy))
        (fun y hy => houts y (List.mem_cons_of_mem _ hy))
        (fun y hy => hres y (List.mem_cons_of_mem _ hy))
        (fun y hy => hval y (List.mem_cons_of_mem _ hy)) hnd.2
    have hx : x ∈ x :: rest := by simp
    have hone : evalOnePhi vs x.inst = some (x.out, x.val) :=
      evalOnePhi_var (houts x hx) hprev (hres x hx) (hval x hx)
    refine ⟨updateVar x.out x.val vs'', ?_, ?_, ?_⟩
    · -- `evalPhis` recurses on the ORIGINAL state, then applies this phi's update on top
      show evalPhis vs (x.inst :: rest.map PhiRun.inst) = _
      unfold evalPhis
      rw [if_neg (by simp [hphi x hx]), hone, hev]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hyr
      · exact lookupVar_updateVar_self vs'' y.out y.val
      · have hne : y.out ≠ x.out := by
          intro he; exact hnd.1 (by rw [← he]; exact List.mem_map_of_mem hyr)
        rw [lookupVar_updateVar_ne vs'' x.out y.out x.val hne]
        exact hout'' y hyr
    · intro w hw
      simp only [List.map_cons, List.mem_cons, not_or] at hw
      rw [lookupVar_updateVar_ne vs'' x.out w x.val hw.1]
      exact hpres'' w hw.2




/-- **The phi step of a genuine join, whole prologue, any incoming edge.**

The Venom side runs `evalPhis` over all the leading phis; the asm side does not move (the plan emits
only `SOPoke`s, which are renames). What comes out is the relation against the **recorded** plan stack —
the layout this block was actually compiled for — starting from the relation against the **arriving**
predecessor's layout, which is the only one true on every edge and is what that predecessor's own block
simulation gives you.

This is the step an `hstep` for a real (≥ 2-predecessor) join consumes, for any number of phis. -/
theorem phi_join_steps {lo : AssocList String Nat} {vs : VenomState}
    {psArr psRec : List Operand} {asmStack : List bytes32} {prev : String}
    (l : List PhiRun) (dep : PhiRun → Nat)
    -- Venom side
    (hprev : vs.prevBb = some prev)
    (hphi : ∀ x ∈ l, x.inst.opcode = Opcode.PHI)
    (houts : ∀ x ∈ l, x.inst.outputs = [x.out])
    (hres : ∀ x ∈ l, resolvePhi prev x.inst.operands = some (Operand.Var x.src))
    (hval : ∀ x ∈ l, lookupVar x.src vs = some x.val)
    (hnd : (l.map PhiRun.out).Nodup)
    -- asm side: the relation that actually holds on arrival
    (hrel : planStackRel lo vs psArr asmStack)
    (hlen : psRec.length = psArr.length)
    (hd : ∀ x ∈ l, dep x < psRec.length)
    (hoff : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ dep x) → psRec.reverse[i]! = psArr.reverse[i]!)
    (hsrc : ∀ x ∈ l, psArr.reverse[dep x]! = Operand.Var x.src)
    (hfresh : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ dep x) →
        ∀ x ∈ l, psRec.reverse[i]! ≠ Operand.Var x.out) :
    ∃ vs', evalPhis vs (l.map PhiRun.inst) = ExecResult.OK vs'
      ∧ planStackRel lo vs'
          ((l.map (fun x => (dep x, x.src, x.out, x.val))).foldl
            (fun st (y : PhiEdge) => stackPoke y.depth (Operand.Var y.out) st) psRec) asmStack := by
  obtain ⟨vs', hev, hout, hpres⟩ := evalPhis_multi l vs prev hprev hphi houts hres hval hnd
  refine ⟨vs', hev, ?_⟩
  refine planStackRel_phi_join_bridge_multi
      (l.map (fun x => (dep x, x.src, x.out, x.val))) hrel hlen ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hd x hx
  · intro i hi hne
    exact hoff i hi (fun x hx => hne _ (List.mem_map_of_mem hx))
  · intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hsrc x hx
  · intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hval x hx
  · intro i hi hne y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hfresh i hi (fun z hz => hne _ (List.mem_map_of_mem hz)) x hx
  · intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hout x hx
  · intro w hw
    refine hpres w ?_
    intro hmem
    obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hmem
    exact hw (by rw [← hxw]; exact List.mem_map_of_mem (List.mem_map_of_mem hx))


/-- **A join's block execution reduces to a phi-free one.** `runBlock` evaluates the phi prefix and then
runs `execBlock` from the first non-phi instruction. -/
theorem runBlock_eq_execBlock_of_phis {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {vs vs' : VenomState} (hev : evalPhis vs bb.instructions = ExecResult.OK vs') :
    runBlock fuel ctx bb vs
      = execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions } := by
  unfold runBlock
  rw [hev]

/-- **`evalPhis` only ever sees the leading phis.** It stops at the first non-`PHI` instruction, so
everything after the prologue is invisible to it. This is what lets a block's phi evaluation be
described by its phi prefix alone — it was an assumption of `join_entry_reduces`; it is a theorem. -/
theorem evalPhis_append_nonphi (s : VenomState) :
    ∀ (phis rest : List Instruction),
      (∀ i ∈ phis, i.opcode = Opcode.PHI) →
      (∀ i, rest.head? = some i → i.opcode ≠ Opcode.PHI) →
      evalPhis s (phis ++ rest) = evalPhis s phis := by
  intro phis
  induction phis with
  | nil =>
    intro rest _ hrest
    cases rest with
    | nil => rfl
    | cons i t =>
      show evalPhis s (i :: t) = evalPhis s []
      unfold evalPhis
      rw [if_pos (hrest i rfl)]
  | cons φ ps ih =>
    intro rest hphi hrest
    have hφ : φ.opcode = Opcode.PHI := hphi φ (by simp)
    show evalPhis s (φ :: (ps ++ rest)) = evalPhis s (φ :: ps)
    unfold evalPhis
    rw [if_neg (by simp [hφ]), if_neg (by simp [hφ]),
        ih rest (fun i hi => hphi i (List.mem_cons_of_mem _ hi)) hrest]

/-- **The join entry, reduced.** Put together: on *any* incoming edge of a genuine join, the phi
prologue emits no EVM code (so the asm stack does not move), the Venom side's `evalPhis` is discharged,
and what remains to simulate is `execBlock` from the first non-phi instruction — starting from a state
that *is* related to the asm against the block's own (recorded, post-phi) plan stack.

That is the whole content of "a join can be compiled against one predecessor and entered from another":
the phis absorb the difference, and everything after them is an ordinary phi-free block. -/
theorem join_entry_reduces {lo : AssocList String Nat} {fuel : Nat} {ctx : VenomContext}
    {bb : BasicBlock} {vs : VenomState} {psArr psRec : List Operand} {asmStack : List bytes32}
    {prev : String} (l : List PhiRun) (dep : PhiRun → Nat)
    (hphis : bb.instructions = l.map PhiRun.inst ++ (bb.instructions.drop l.length))
    (hprev : vs.prevBb = some prev)
    (hphi : ∀ x ∈ l, x.inst.opcode = Opcode.PHI)
    (houts : ∀ x ∈ l, x.inst.outputs = [x.out])
    (hres : ∀ x ∈ l, resolvePhi prev x.inst.operands = some (Operand.Var x.src))
    (hval : ∀ x ∈ l, lookupVar x.src vs = some x.val)
    (hnd : (l.map PhiRun.out).Nodup)
    (hrel : planStackRel lo vs psArr asmStack)
    (hlen : psRec.length = psArr.length)
    (hd : ∀ x ∈ l, dep x < psRec.length)
    (hoff : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ dep x) → psRec.reverse[i]! = psArr.reverse[i]!)
    (hsrc : ∀ x ∈ l, psArr.reverse[dep x]! = Operand.Var x.src)
    (hfresh : ∀ i, i < psRec.length → (∀ x ∈ l, i ≠ dep x) →
        ∀ x ∈ l, psRec.reverse[i]! ≠ Operand.Var x.out)
    -- the prologue really is the *leading* phis: what follows it does not start with one
    (hnext : ∀ i, (bb.instructions.drop l.length).head? = some i → i.opcode ≠ Opcode.PHI) :
    ∃ vs', runBlock fuel ctx bb vs
             = execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions }
      ∧ planStackRel lo vs'
          ((l.map (fun x => (dep x, x.src, x.out, x.val))).foldl
            (fun st (y : PhiEdge) => stackPoke y.depth (Operand.Var y.out) st) psRec) asmStack := by
  obtain ⟨vs', hev, hrel'⟩ :=
    phi_join_steps (lo := lo) (psArr := psArr) (psRec := psRec) (asmStack := asmStack) (prev := prev)
      l dep hprev hphi houts hres hval hnd hrel hlen hd hoff hsrc hfresh
  -- `evalPhis` stops at the first non-phi, so the block's phi evaluation *is* the prologue's
  have hevb : evalPhis vs bb.instructions = evalPhis vs (l.map PhiRun.inst) := by
    conv_lhs => rw [hphis]
    exact evalPhis_append_nonphi vs (l.map PhiRun.inst) (bb.instructions.drop l.length)
      (fun i hi => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
        exact hphi x hx) hnext
  exact ⟨vs', runBlock_eq_execBlock_of_phis (by rw [hevb]; exact hev), hrel'⟩


/-! ### The phi prefix, structurally

`join_entry_reduces` hands `execBlock` the index `phiPrefixLength bb.instructions` and claims what is
left is a phi-free block. Two facts make that true rather than merely plausible, and both were being
taken on faith. -/

/-- **The phi prefix really is the leading phis.** `join_entry_reduces` hands `execBlock` the index
`phiPrefixLength bb.instructions`; this says that index is exactly the number of leading phis, so the
block resumes at the first non-phi instruction and not somewhere else. -/
theorem phiPrefixLength_append :
    ∀ (phis rest : List Instruction),
      (∀ i ∈ phis, i.opcode = Opcode.PHI) →
      (∀ i, rest.head? = some i → i.opcode ≠ Opcode.PHI) →
      phiPrefixLength (phis ++ rest) = phis.length := by
  intro phis
  induction phis with
  | nil =>
    intro rest _ hrest
    cases rest with
    | nil => rfl
    | cons i t =>
      show phiPrefixLength (i :: t) = 0
      unfold phiPrefixLength
      rw [if_neg (hrest i rfl)]
  | cons φ ps ih =>
    intro rest hphi hrest
    have hφ : φ.opcode = Opcode.PHI := hphi φ (by simp)
    show phiPrefixLength (φ :: (ps ++ rest)) = (φ :: ps).length
    unfold phiPrefixLength
    rw [if_pos hφ, ih rest (fun i hi => hphi i (List.mem_cons_of_mem _ hi)) hrest]
    simp [Nat.add_comm]

/-! ### Why the join cannot be plugged into the existing `hstep` family by a uniform index shift

`runBlock` resumes a join at `instIdx := phiPrefixLength` — after its phis. The whole `hstep` family, by
contrast, requires the block's head *not* to be a phi (`hphi`, in each of its members). Neither applies
to the other until the two are related, and the natural way to relate them is a uniform re-basing of the
instruction index by the prefix length.

That does not work, and it is worth knowing before trying: a jump *discards* the instruction index. -/

/-- A jump resets the instruction index, whatever it was. -/
theorem jumpTo_instIdx (lbl : String) (s : VenomState) : (jumpTo lbl s).instIdx = 0 := rfl

/-- **So block results cannot be re-based by a uniform `+ pre.length`.** Resuming a block after its phi
prefix and running the phi-free residual do not differ by a fixed offset on the instruction index — a
jump throws the index away. An `execBlock` shift lemma must be stated *up to* `instIdx` (which is what
`venomAsmRel` and `venomAsmTerminalRel` already ignore), not as an equation on states.

Recorded because the natural formulation is false, and it is the first thing one would reach for. -/
theorem jump_defeats_uniform_shift :
    ∀ (lbl : String) (s : VenomState) (k : Nat), 0 < k →
      (jumpTo lbl s).instIdx ≠ (jumpTo lbl s).instIdx + k := by
  intro lbl s k hk
  rw [jumpTo_instIdx]
  omega


/-! ### Running a block after its phi prefix *is* running the phi-free residual — up to `instIdx`

`jump_defeats_uniform_shift` above rules out the obvious formulation. This is the one that works: state
the correspondence at the granularity the simulation relations already use — equality up to the
instruction index — and it holds. -/

/-- Two states agree except possibly in the instruction index — the granularity `venomAsmRel` and
`venomAsmTerminalRel` already work at. -/
def sameUpToIdx (a b : VenomState) : Prop :=
  { a with instIdx := 0 } = { b with instIdx := 0 }

theorem sameUpToIdx.refl (a : VenomState) : sameUpToIdx a a := rfl

theorem sameUpToIdx_setIdx {a b : VenomState} (h : sameUpToIdx a b) (j k : Nat) :
    sameUpToIdx { a with instIdx := j } { b with instIdx := k } := by
  unfold sameUpToIdx at *
  cases a; cases b; simp_all

theorem sameUpToIdx.halted {a b : VenomState} (h : sameUpToIdx a b) : a.halted = b.halted := by
  unfold sameUpToIdx at h; cases a; cases b; simp_all

/-- …lifted to block results. -/
def ResSameUpToIdx : ExecResult → ExecResult → Prop
  | ExecResult.OK a,       ExecResult.OK b       => sameUpToIdx a b
  | ExecResult.Halt a,     ExecResult.Halt b     => sameUpToIdx a b
  | ExecResult.Abort t a,  ExecResult.Abort t' b => t = t' ∧ sameUpToIdx a b
  | ExecResult.IntRet v a, ExecResult.IntRet w b => v = w ∧ sameUpToIdx a b
  | ExecResult.Error e,    ExecResult.Error e'   => e = e'
  | _, _ => False

/-- The residual block is read at the shifted index — at *every* index, in range or not. -/
theorem getInstruction_shift {bb bb' : BasicBlock} {pre : List Instruction}
    (hbb : bb.instructions = pre ++ bb'.instructions) (i : Nat) :
    getInstruction bb (pre.length + i) = getInstruction bb' i := by
  unfold getInstruction
  rw [hbb]
  by_cases h : i < bb'.instructions.length
  · rw [dif_pos (by simp; omega), dif_pos h]
    simp [List.getElem_append_right]
  · rw [dif_neg (by simp; omega), dif_neg h]



/-- **Running a block after a prefix IS running the residual block — up to the instruction index.**

This is what a genuine join needs and could not have. `runBlock` resumes a join at
`instIdx := phiPrefixLength`, after its phis; the `hstep` family requires the block's head not to be a
phi. Relating them by re-basing the index uniformly is *false* (`jump_defeats_uniform_shift`: `jumpTo`
resets the index to zero). Stated at the granularity the simulation relations actually use — equality
up to `instIdx` — it is true, and this proves it.

The side conditions are the two branches of `execBlock` that hand the state to separate machinery
(`INVOKE`, external calls); those have their own treatment and are excluded here rather than waved at.
`stepInstBase` respecting `sameUpToIdx` is the remaining input — true because it never reads `instIdx`,
and dischargeable per instruction exactly as the `PARAM`-prefix simulations already do. -/
theorem execBlock_shift_upto {ctx : VenomContext} {bb bb' : BasicBlock} {pre : List Instruction}
    (hbb : bb.instructions = pre ++ bb'.instructions)
    (hno : ∀ inst ∈ bb'.instructions, inst.opcode ≠ Opcode.INVOKE)
    (hnx : ∀ inst ∈ bb'.instructions, isExternalCall inst.opcode = false)
    (hstep : ∀ inst ∈ bb'.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
        ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2)) :
    ∀ (fuel i : Nat) (s1 s2 : VenomState), sameUpToIdx s1 s2 →
      ResSameUpToIdx
        (execBlock fuel ctx bb  { s1 with instIdx := pre.length + i })
        (execBlock fuel ctx bb' { s2 with instIdx := i }) := by
  intro fuel
  induction fuel with
  | zero => intro i s1 s2 _; unfold execBlock; exact rfl
  | succ fuel' ih =>
    intro i s1 s2 hs
    unfold execBlock
    dsimp only
    rw [getInstruction_shift hbb i]
    cases hgi : getInstruction bb' i with
    | none => exact rfl
    | some inst =>
      dsimp only
      have hmem : inst ∈ bb'.instructions := by
        unfold getInstruction at hgi
        by_cases h : i < bb'.instructions.length
        · rw [dif_pos h] at hgi
          simp only [Option.some.injEq] at hgi
          exact hgi ▸ List.get_mem _ _
        · rw [dif_neg h] at hgi; exact absurd hgi (by simp)
      have hss : sameUpToIdx { s1 with instIdx := pre.length + i } { s2 with instIdx := i } :=
        sameUpToIdx_setIdx hs _ _
      have hstep' := hstep inst hmem _ _ hss
      cases h1 : stepInstBase inst { s1 with instIdx := pre.length + i } with
      | OK t1 =>
        cases h2 : stepInstBase inst { s2 with instIdx := i } with
        | OK t2 =>
          rw [h1, h2] at hstep'
          dsimp only
          have ht : sameUpToIdx t1 t2 := hstep'
          by_cases hterm : isTerminator inst.opcode = true
          · rw [if_pos hterm, if_pos hterm, ht.halted]
            by_cases hh : t2.halted = true
            · rw [if_pos hh, if_pos hh]; exact ht
            · rw [if_neg hh, if_neg hh]; exact ht
          · rw [if_neg hterm, if_neg hterm]
            exact ih (i + 1) t1 t2 ht
        | _ => rw [h1, h2] at hstep'; exact absurd hstep' (by simp [ResSameUpToIdx])
      | Halt t1 =>
        cases h2 : stepInstBase inst { s2 with instIdx := i } with
        | Halt t2 => rw [h1, h2] at hstep'; dsimp only; exact hstep'
        | _ => rw [h1, h2] at hstep'; exact absurd hstep' (by simp [ResSameUpToIdx])
      | Abort a t1 =>
        cases h2 : stepInstBase inst { s2 with instIdx := i } with
        | Abort a' t2 =>
          rw [h1, h2] at hstep'
          dsimp only
          obtain ⟨rfl, ht⟩ := hstep'
          exact ⟨rfl, ht⟩
        | _ => rw [h1, h2] at hstep'; exact absurd hstep' (by simp [ResSameUpToIdx])
      | IntRet v t1 =>
        cases h2 : stepInstBase inst { s2 with instIdx := i } with
        | IntRet w t2 =>
          rw [h1, h2] at hstep'
          dsimp only
          obtain ⟨rfl, ht⟩ := hstep'
          exact ⟨rfl, ht⟩
        | _ => rw [h1, h2] at hstep'; exact absurd hstep' (by simp [ResSameUpToIdx])
      | Error e =>
        cases h2 : stepInstBase inst { s2 with instIdx := i } with
        | Error e' =>
          rw [h1, h2] at hstep'
          dsimp only
          have he : e = e' := hstep'
          subst he
          have hx : ¬ (isExternalCall inst.opcode = true) := by simp [hnx inst hmem]
          rw [if_neg (hno inst hmem), if_neg (hno inst hmem), if_neg hx, if_neg hx]
          exact rfl
        | _ => rw [h1, h2] at hstep'; exact absurd hstep' (by simp [ResSameUpToIdx])



/-- **A genuine join, reduced to an ordinary block.**

The `hstep` family requires a block whose head is not a phi — 36 separate `hphi` hypotheses. A join's
head *is* a phi, so it cannot be instantiated there. This closes the distance: on any incoming edge, once
the phis are discharged, a join *is* a block with a non-phi head, and its `runBlock` *is* that block's
`execBlock` — up to the instruction index, which is exactly the granularity `venomAsmRel` and
`venomAsmTerminalRel` already work at.

Together with `join_entry_reduces` (which discharges the phis, keeps the asm stack still, and establishes
the relation against the block's own recorded plan stack), that is the whole of what a genuine join needed
and did not have. -/
theorem join_runBlock_eq_residual {ctx : VenomContext} {bb bb' : BasicBlock}
    {phis : List Instruction} {vs vs' : VenomState} {fuel : Nat}
    (hbb : bb.instructions = phis ++ bb'.instructions)
    (hphi : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hnext : ∀ i, bb'.instructions.head? = some i → i.opcode ≠ Opcode.PHI)
    (hno : ∀ inst ∈ bb'.instructions, inst.opcode ≠ Opcode.INVOKE)
    (hnx : ∀ inst ∈ bb'.instructions, isExternalCall inst.opcode = false)
    (hstep : ∀ inst ∈ bb'.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
        ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2))
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs') :
    ResSameUpToIdx (runBlock fuel ctx bb vs)
                   (execBlock fuel ctx bb' { vs' with instIdx := 0 }) := by
  rw [runBlock_eq_execBlock_of_phis hev, hbb,
      phiPrefixLength_append phis bb'.instructions hphi hnext]
  have h := execBlock_shift_upto (ctx := ctx) (bb := bb) (bb' := bb') (pre := phis)
    hbb hno hnx hstep fuel 0 vs' vs' (sameUpToIdx.refl vs')
  simpa using h


/-! ### Discharging the one remaining input: `stepInstBase` respects the relation

`execBlock_shift_upto` needs `stepInstBase` to respect `sameUpToIdx`. It does, because it never reads
`instIdx` — only `jumpTo` writes it. Proving that for all 92 opcodes at once would mean proving it for
every exec-combinator; the codebase already discharges these per instruction (the `*_setInstIdx`
family), and the same is done here at the granularity the shift lemma consumes. -/

/-- `sameUpToIdx` says the second state is the first with a different index. -/
theorem sameUpToIdx_iff {a b : VenomState} :
    sameUpToIdx a b ↔ b = { a with instIdx := b.instIdx } := by
  unfold sameUpToIdx
  constructor
  · intro h; cases a; cases b; simp_all
  · intro h; cases a; cases b; simp_all

/-- **`execWrite2` respects the relation** when its writer does: the operands read the same, and the
write touches no index. Covers `SSTORE`/`TSTORE`/`MSTORE`/`MSTORE8`. -/
theorem execWrite2_respects {f : bytes32 → bytes32 → VenomState → VenomState} {inst : Instruction}
    (hf : ∀ (v1 v2 : bytes32) (s : VenomState) (i : Nat),
        f v1 v2 { s with instIdx := i } = { f v1 v2 s with instIdx := i })
    (t1 t2 : VenomState) (h : sameUpToIdx t1 t2) :
    ResSameUpToIdx (execWrite2 f inst t1) (execWrite2 f inst t2) := by
  obtain ⟨j, rfl⟩ : ∃ j, t2 = { t1 with instIdx := j } :=
    ⟨t2.instIdx, sameUpToIdx_iff.mp h⟩
  unfold execWrite2
  cases hops : inst.operands with
  | nil => exact rfl
  | cons o1 rest =>
    cases rest with
    | nil => exact rfl
    | cons o2 rest2 =>
      cases rest2 with
      | cons _ _ => exact rfl
      | nil =>
        simp only [evalOperand_setInstIdx]
        cases evalOperand o1 t1 with
        | none => exact rfl
        | some v1 =>
          cases evalOperand o2 t1 with
          | none => exact rfl
          | some v2 =>
            show ResSameUpToIdx (ExecResult.OK (f v1 v2 t1))
                                (ExecResult.OK (f v1 v2 { t1 with instIdx := j }))
            rw [hf v1 v2 t1 j]
            show sameUpToIdx (f v1 v2 t1) { f v1 v2 t1 with instIdx := j }
            unfold sameUpToIdx
            cases (f v1 v2 t1); rfl

/-- **A halting terminator respects the relation** — `haltState` writes only `halted`. -/
theorem halt_respects (t1 t2 : VenomState) (h : sameUpToIdx t1 t2) :
    ResSameUpToIdx (ExecResult.Halt (haltState t1)) (ExecResult.Halt (haltState t2)) := by
  show sameUpToIdx (haltState t1) (haltState t2)
  unfold sameUpToIdx haltState at *
  cases t1; cases t2; simp_all


/-- `SSTORE` respects the relation. -/
theorem sstore_respects {inst : Instruction} (hop : inst.opcode = Opcode.SSTORE)
    (t1 t2 : VenomState) (h : sameUpToIdx t1 t2) :
    ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2) := by
  unfold stepInstBase
  rw [hop]
  exact execWrite2_respects (fun v1 v2 s i => sstore_setInstIdx v1 v2 s i) t1 t2 h

/-- `STOP` respects the relation. -/
theorem stop_respects {inst : Instruction} (hop : inst.opcode = Opcode.STOP)
    (t1 t2 : VenomState) (h : sameUpToIdx t1 t2) :
    ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2) := by
  unfold stepInstBase
  rw [hop]
  exact halt_respects t1 t2 h


/-! ### The join's block simulation, from the residual's — the `hphi` barrier removed

The `hstep` family requires a block whose head is not a phi: 36 separate `hphi` hypotheses. A genuine
join's head *is* a phi, so the family cannot be instantiated there, and that is the last thing standing
between this development and a join.

It is removed here, not worked around. Prove the block simulation for the *residual* block — which has a
non-phi head, so the family applies to it unchanged — and it transfers to the join: on any incoming edge
the two runs agree up to the instruction index, and neither `venomAsmRel` nor `venomAsmTerminalRel` sees
that index. -/

/-- **A phi-free block's `runBlock` is just its `execBlock`.** `evalPhis` returns immediately and the
phi prefix is empty. -/
theorem runBlock_of_no_phi {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    (hnp : ∀ i, bb.instructions.head? = some i → i.opcode ≠ Opcode.PHI) :
    runBlock fuel ctx bb vs = execBlock fuel ctx bb { vs with instIdx := 0 } := by
  have hev : evalPhis vs bb.instructions = ExecResult.OK vs := by
    cases h : bb.instructions with
    | nil => rfl
    | cons i t =>
      unfold evalPhis
      rw [if_pos (hnp i (by rw [h]; rfl))]
  have hlen : phiPrefixLength bb.instructions = 0 := by
    cases h : bb.instructions with
    | nil => rfl
    | cons i t =>
      unfold phiPrefixLength
      rw [if_neg (hnp i (by rw [h]; rfl))]
  rw [runBlock_eq_execBlock_of_phis hev, hlen]

/-- **The simulation relations do not see the instruction index.** Neither `venomAsmRel` nor
`venomAsmTerminalRel` mentions `instIdx`, so both are congruences for `sameUpToIdx` — which is what
lets a result proved for the residual block be carried back to the join. -/
theorem venomAsmRel_congr {lo ps} {a b : VenomState} {as : AsmState} (h : sameUpToIdx a b) :
    venomAsmRel lo ps a as → venomAsmRel lo ps b as := by
  obtain ⟨j, rfl⟩ : ∃ j, b = { a with instIdx := j } := ⟨b.instIdx, sameUpToIdx_iff.mp h⟩
  exact id

theorem venomAsmTerminalRel_congr {a b : VenomState} {as : AsmState} (h : sameUpToIdx a b) :
    venomAsmTerminalRel a as → venomAsmTerminalRel b as := by
  obtain ⟨j, rfl⟩ : ∃ j, b = { a with instIdx := j } := ⟨b.instIdx, sameUpToIdx_iff.mp h⟩
  exact id


/-- **The block-simulation conclusion, as a predicate on the Venom result.** This is exactly the shape
`genBlockSimulation` proves — factored out so it can be moved between results. -/
def BlockSim (lo : AssocList String Nat) (ps' : PlanState) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (as : AsmState) : ExecResult → Prop
  | ExecResult.OK vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
             venomAsmRel lo ps' vs' as'
  | ExecResult.Halt vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
             venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.RevertAbort vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
             venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
             venomAsmTerminalRel vs' as'
  | _ => True

/-- **A simulation transfers across `ResSameUpToIdx`.** The relations do not see the instruction index,
so a block simulation proved for one result holds for any result that agrees with it up to the index. -/
theorem BlockSim_congr {lo ps' offsetToPc prog as} {r1 r2 : ExecResult}
    (h : ResSameUpToIdx r1 r2) (hsim : BlockSim lo ps' offsetToPc prog as r2) :
    BlockSim lo ps' offsetToPc prog as r1 := by
  cases r1 with
  | OK a =>
    cases r2 with
    | OK b =>
      obtain ⟨as', hrun, hrel⟩ := hsim
      exact ⟨as', hrun, venomAsmRel_congr (Eq.symm h) hrel⟩
    | _ => exact absurd h (by simp [ResSameUpToIdx])
  | Halt a =>
    cases r2 with
    | Halt b =>
      obtain ⟨as', hrun, hrel⟩ := hsim
      exact ⟨as', hrun, venomAsmTerminalRel_congr (Eq.symm h) hrel⟩
    | _ => exact absurd h (by simp [ResSameUpToIdx])
  | Abort t a =>
    cases r2 with
    | Abort t' b =>
      obtain ⟨rfl, hst⟩ := h
      cases t with
      | RevertAbort =>
        obtain ⟨as', hrun, hrel⟩ := hsim
        exact ⟨as', hrun, venomAsmTerminalRel_congr (Eq.symm hst) hrel⟩
      | ExHaltAbort =>
        obtain ⟨as', hrun, hrel⟩ := hsim
        exact ⟨as', hrun, venomAsmTerminalRel_congr (Eq.symm hst) hrel⟩
    | _ => exact absurd h (by simp [ResSameUpToIdx])
  | IntRet v a => trivial
  | Error e => trivial

/-- **The join's block simulation, from the residual's.**

The `hstep` family cannot be instantiated at a join — its 36 `hphi` hypotheses require a non-phi head.
This closes that: prove the simulation for the *residual* — the instructions after the phis — and it
transfers to the join.

Careful about what that simulation is *of*: the residual's execution against a program matching the
join's, not `generateBlockPlan` applied to a synthetic residual block. The generator indexes liveness by
position, so dropping the phis shifts every later index and it compiles differently
(`residual_block_compiles_differently`). On any incoming edge, once the phis are discharged, the two
runs agree up to the instruction index, and the relations do not see it. -/
theorem BlockSim_join {ctx : VenomContext} {bb bb' : BasicBlock} {phis : List Instruction}
    {vs vs' : VenomState} {fuel : Nat}
    {lo : AssocList String Nat} {ps' : PlanState} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {as : AsmState}
    (hbb : bb.instructions = phis ++ bb'.instructions)
    (hphi : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hnext : ∀ i, bb'.instructions.head? = some i → i.opcode ≠ Opcode.PHI)
    (hno : ∀ inst ∈ bb'.instructions, inst.opcode ≠ Opcode.INVOKE)
    (hnx : ∀ inst ∈ bb'.instructions, isExternalCall inst.opcode = false)
    (hstep : ∀ inst ∈ bb'.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
        ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2))
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    -- the residual block's own simulation: `genBlockSimulation` applies to it, since its head is no phi
    (hres : BlockSim lo ps' offsetToPc prog as (runBlock fuel ctx bb' vs')) :
    BlockSim lo ps' offsetToPc prog as (runBlock fuel ctx bb vs) := by
  refine BlockSim_congr (r2 := runBlock fuel ctx bb' vs') ?_ hres
  rw [runBlock_of_no_phi hnext]
  exact join_runBlock_eq_residual hbb hphi hnext hno hnx hstep hev


/-! ### From `planStackRel` to the whole of `venomAsmRel` across the phis

The phi work so far produced `planStackRel` — the interesting component, and the one the miscompile broke.
But `genBlockSimulation` wants the *whole* of `venomAsmRel` at the block's entry, and nothing so far
supplied the rest.

It comes for free, and the reason is worth stating: `evalPhis` writes only `vars`, and the plan's `SOPoke`
writes only the stack. So memory, accounts, transient storage, returndata, logs and the environment all
come through untouched, and the spill map and allocator are unchanged. The one component that reads the
state and *could* have been disturbed is `planSpillRel` — and it is not, because a phi output is fresh and
so is never one of the spilled operands. -/

/-- **`planSpillRel` survives the phi batch.** A phi output is fresh, so it is not one of the spilled
operands, and the spill map's readings are untouched. -/
theorem planSpillRel_updateVars {lo : AssocList String Nat} {vs vs' : VenomState}
    {spilled : SpilledMap} {mem : ByteArray} {outs : List String}
    (hpres : ∀ w, w ∉ outs → lookupVar w vs' = lookupVar w vs)
    (hfresh : ∀ op off, AssocList.lookup Operand Nat spilled op = some off →
        ∀ o ∈ outs, op ≠ Operand.Var o)
    (h : planSpillRel lo vs spilled mem) :
    planSpillRel lo vs' spilled mem := by
  intro op off hlk
  obtain ⟨v, hval, hmem⟩ := h op off hlk
  refine ⟨v, ?_, hmem⟩
  cases hop : op with
  | Lit w => rw [hop] at hval; exact hval
  | Label m => rw [hop] at hval; exact hval
  | Var w =>
    have hw : w ∉ outs := by
      intro hmem'
      exact hfresh op off hlk w hmem' hop
    rw [hop] at hval
    show lookupVar w vs' = some v
    rw [hpres w hw]
    exact hval

/-- **The phi step upgrades `planStackRel` to the whole of `venomAsmRel`.**

Everything else in the relation is untouched: `updateVar` writes only `vars`, so memory, accounts,
transient storage, returndata, logs and the environment are all unchanged; and the plan side's `SOPoke`
writes only the stack, so the spill map and allocator are unchanged too. The one component that *could*
have been disturbed is `planSpillRel`, which reads the state — and it is not, because a phi output is
fresh and so is never one of the spilled operands.

This is what `genBlockSimulation` needs at the residual block's entry, and what the phi work up to now
did not supply: it produced `planStackRel`, which is the interesting part, but not the whole relation. -/
theorem venomAsmRel_phi_join {lo : AssocList String Nat} {vs vs' : VenomState} {as : AsmState}
    {ps psPost : PlanState} {outs : List String}
    (hrel : venomAsmRel lo ps vs as)
    -- the plan side poked only the stack
    (hstack : psPost.spilled = ps.spilled) (halloc : psPost.alloc = ps.alloc)
    -- the Venom side bound only the phi outputs
    (hpres : ∀ w, w ∉ outs → lookupVar w vs' = lookupVar w vs)
    (hmem : vs'.memory = vs.memory) (hacc : vs'.accounts = vs.accounts)
    (htr : vs'.transient = vs.transient) (hrd : vs'.returndata = vs.returndata)
    (hlog : vs'.logs = vs.logs) (hcc : vs'.callCtx = vs.callCtx) (htx : vs'.txCtx = vs.txCtx)
    (hbc : vs'.blockCtx = vs.blockCtx) (hcode : vs'.code = vs.code)
    (hph : vs'.prevHashes = vs.prevHashes)
    -- phi outputs are fresh: none of them is a spilled operand
    (hfresh : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ∀ o ∈ outs, op ≠ Operand.Var o)
    -- and the stack side is the phi bridge's conclusion
    (hps : planStackRel lo vs' psPost.stack as.stack) :
    venomAsmRel lo psPost vs' as := by
  obtain ⟨_, hsp, hmr, ha, ht, hr, hl, hc, hx, hb, hcd, hrest⟩ := hrel
  refine ⟨hps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstack]; exact planSpillRel_updateVars hpres hfresh hsp
  · rw [halloc, hmem]; exact hmr
  · rw [hacc]; exact ha
  · rw [htr]; exact ht
  · rw [hrd]; exact hr
  · rw [hlog]; exact hl
  · rw [hcc]; exact hc
  · rw [htx]; exact hx
  · rw [hbc]; exact hb
  · rw [hcode]; exact hcd
  · rw [hph]; exact hrest


/-- **`evalPhis` writes only `vars`.** Every other field of the state comes through untouched — which is
what makes the rest of `venomAsmRel` survive the phi prologue for free. -/
theorem evalPhis_only_vars :
    ∀ (phis : List Instruction) (vs vs' : VenomState),
      evalPhis vs phis = ExecResult.OK vs' → { vs' with vars := vs.vars } = vs := by
  intro phis
  induction phis with
  | nil => intro vs vs' h; cases h; cases vs; rfl
  | cons φ rest ih =>
    intro vs vs' h
    unfold evalPhis at h
    by_cases hφ : φ.opcode ≠ Opcode.PHI
    · rw [if_pos hφ] at h; cases h; cases vs; rfl
    · rw [if_neg hφ] at h
      cases ho : evalOnePhi vs φ with
      | none => rw [ho] at h; exact absurd h (by simp)
      | some p =>
        rw [ho] at h
        cases hr : evalPhis vs rest with
        | OK w =>
          rw [hr] at h
          simp only [ExecResult.OK.injEq] at h
          subst h
          have := ih vs w hr
          cases vs; cases w; simp_all [updateVar]
        | _ => rw [hr] at h; exact absurd h (by simp)

/-- **The phi step upgrades `planStackRel` to the whole of `venomAsmRel`** — with the untouched fields
*derived* rather than assumed. -/
theorem venomAsmRel_phi_join' {lo : AssocList String Nat} {vs vs' : VenomState} {as : AsmState}
    {ps psPost : PlanState} {outs : List String} {phis : List Instruction}
    (hrel : venomAsmRel lo ps vs as)
    (hsp : psPost.spilled = ps.spilled) (hal : psPost.alloc = ps.alloc)
    (hev : evalPhis vs phis = ExecResult.OK vs')
    (hpres : ∀ w, w ∉ outs → lookupVar w vs' = lookupVar w vs)
    (hfresh : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ∀ o ∈ outs, op ≠ Operand.Var o)
    (hps : planStackRel lo vs' psPost.stack as.stack) :
    venomAsmRel lo psPost vs' as := by
  have hf := evalPhis_only_vars phis vs vs' hev
  refine venomAsmRel_phi_join (outs := outs) hrel hsp hal hpres ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfresh hps
  · simpa using congrArg VenomState.memory hf
  · simpa using congrArg VenomState.accounts hf
  · simpa using congrArg VenomState.transient hf
  · simpa using congrArg VenomState.returndata hf
  · simpa using congrArg VenomState.logs hf
  · simpa using congrArg VenomState.callCtx hf
  · simpa using congrArg VenomState.txCtx hf
  · simpa using congrArg VenomState.blockCtx hf
  · simpa using congrArg VenomState.code hf
  · simpa using congrArg VenomState.prevHashes hf



/-- **The join's simulation, without any residual block at all.**

`BlockSim_join` routes through a synthetic phi-free `BasicBlock`. That was needed to reach a block with
a non-phi head — but the `hstep` family cannot be applied to it anyway, because `generateBlockPlan`
indexes liveness by position and the synthetic block compiles differently
(`residual_block_compiles_differently`). So the detour buys nothing, and it invites the mistake.

This is the form to use. Say what happens when the *join itself* is resumed after its phis — same block,
same plan, same program — and the simulation follows. `runBlock` *is* `evalPhis` then `execBlock` from the
first non-phi instruction; there is nothing else to prove.

The residual-block route stays available for callers who already have a simulation in that shape
(`min_join_sim` uses it, via `hasm_stop`), but nothing has to go that way.

**What this does and does not buy.** The theorem itself is free — one rewrite, no side conditions. What
it does *not* do is remove the per-opcode work needed to discharge `hres` for a *generic* join. A join
resumes at `instIdx = phiPrefixLength`, not `0`, so proving its body simulation means running the body
machinery at an offset — and that needs the body instructions to be instruction-index oblivious, which is
the same content the residual route needs.

That requirement is not introduced here: it is already in the codebase. The `PARAM`-prefix simulations
face exactly it, and meet it with `execBodyThread_instIdx_congr`, whose `hobliv` hypothesis is discharged
per opcode (`execPure2_setInstIdx` covers the pure binops). Neither join route escapes it in general.

What the residual-free route *does* remove is the detour through a synthetic block, and the trap that
comes with it (`residual_block_compiles_differently`). For a concrete block, `hres` is proved by
computation and no obliviousness is needed at all — which is how `min_join_sim_self` goes. -/
theorem BlockSim_join_self {ctx : VenomContext} {bb : BasicBlock} {vs vs' : VenomState} {fuel : Nat}
    {lo : AssocList String Nat} {ps' : PlanState} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {as : AsmState}
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    (hres : BlockSim lo ps' offsetToPc prog as
      (execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions })) :
    BlockSim lo ps' offsetToPc prog as (runBlock fuel ctx bb vs) := by
  rw [runBlock_eq_execBlock_of_phis hev]
  exact hres



/-! ### instIdx-obliviousness for every exec combinator

`execBodyThread_instIdx_congr` — the bridge the `PARAM`-prefix simulations use, and the one a *generic*
join needs, since a join resumes at `instIdx = phiPrefixLength` rather than `0` — takes a per-step
obliviousness hypothesis. Only `execPure2` had a discharger for it; the semantics has six combinators.

Here are the other five. Between them they cover every opcode the semantics routes through a combinator,
so the hypothesis is now dischargeable for an ordinary block body rather than only for pure binops. The
two readers carry a side condition, and must: they take the state as an argument, so they have to be told
they do not read the index. -/

/-- **Per-step instIdx-obliviousness for 1-input pure opcodes** (`NOT`, `ISZERO`). -/
theorem execPure1_setInstIdx {f : bytes32 → bytes32} {inst : Instruction}
    {s s' : VenomState} {i : Nat} (h : execPure1 f inst s = ExecResult.OK s') :
    execPure1 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execPure1 at h ⊢
  simp only [evalOperand_setInstIdx, updateVar_setInstIdx]
  split at h <;> first | (split at h <;> simp_all) | simp_all

/-- **…for 3-input pure opcodes** (`ADDMOD`, `MULMOD`). -/
theorem execPure3_setInstIdx {f : bytes32 → bytes32 → bytes32 → bytes32} {inst : Instruction}
    {s s' : VenomState} {i : Nat} (h : execPure3 f inst s = ExecResult.OK s') :
    execPure3 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execPure3 at h ⊢
  simp only [evalOperand_setInstIdx, updateVar_setInstIdx]
  split at h <;> first | (split at h <;> simp_all) | simp_all

/-- **…for 0-input state readers** (the env-push family), given the reader ignores `instIdx`. -/
theorem execRead0_setInstIdx {f : VenomState → bytes32} {inst : Instruction}
    {s s' : VenomState} {i : Nat}
    (hf : ∀ (t : VenomState) (j : Nat), f { t with instIdx := j } = f t)
    (h : execRead0 f inst s = ExecResult.OK s') :
    execRead0 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execRead0 at h ⊢
  simp only [hf, updateVar_setInstIdx]
  split at h <;> simp_all

/-- **…for 1-input state readers** (`SLOAD`, `TLOAD`, `MLOAD`, `BALANCE`, …), same side condition. -/
theorem execRead1_setInstIdx {f : bytes32 → VenomState → bytes32} {inst : Instruction}
    {s s' : VenomState} {i : Nat}
    (hf : ∀ (v : bytes32) (t : VenomState) (j : Nat), f v { t with instIdx := j } = f v t)
    (h : execRead1 f inst s = ExecResult.OK s') :
    execRead1 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execRead1 at h ⊢
  simp only [evalOperand_setInstIdx, hf, updateVar_setInstIdx]
  split at h <;> first | (split at h <;> simp_all) | simp_all

/-- **…for the 2-input writers** (`SSTORE`, `TSTORE`, `MSTORE`, `MSTORE8`), given the writer commutes
with setting the index — which the `*_setInstIdx` atoms already say. -/
theorem execWrite2_setInstIdx {f : bytes32 → bytes32 → VenomState → VenomState} {inst : Instruction}
    {s s' : VenomState} {i : Nat}
    (hf : ∀ (v1 v2 : bytes32) (t : VenomState) (j : Nat),
        f v1 v2 { t with instIdx := j } = { f v1 v2 t with instIdx := j })
    (h : execWrite2 f inst s = ExecResult.OK s') :
    execWrite2 f inst { s with instIdx := i } = ExecResult.OK { s' with instIdx := i } := by
  unfold execWrite2 at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons o1 rest =>
    cases rest with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons o2 rest2 =>
      cases rest2 with
      | cons _ _ => rw [hops] at h; exact absurd h (by simp)
      | nil =>
        rw [hops] at h
        dsimp only at h ⊢
        simp only [evalOperand_setInstIdx]
        cases hv1 : evalOperand o1 s with
        | none => rw [hv1] at h; exact absurd h (by simp)
        | some v1 =>
          cases hv2 : evalOperand o2 s with
          | none => rw [hv1, hv2] at h; exact absurd h (by simp)
          | some v2 =>
            rw [hv1, hv2] at h
            simp only [ExecResult.OK.injEq] at h
            subst h
            dsimp only
            rw [hf]


/-! ### Discharging `hobliv` at the opcode level

The combinator lemmas above are the reusable content; `hobliv` is stated about `stepInstBase`, so a caller
needs it one opcode at a time. Here is that step, once per combinator, which is also what fires each of
those lemmas.

RETRACTION. An earlier version of this note claimed `execRead0` is "defined in the semantics but no
opcode routes through it". That is **false**. `execRead0` carries nineteen opcodes — the whole
environment-push family (`CALLER`, `ADDRESS`, `ORIGIN`, `CALLVALUE`, `NUMBER`, `GAS`, …) — making it the
second-largest of the six; this very file already proves a `bodyStep_*` theorem for nine of them. The
claim came from `grep '=> execRead0'`, which misses arms that put the combinator on the *next* line, and
every opcode in this family does. Measured with a parser instead: **60 of the 81 body opcode arms route
through a combinator** (`execPure2` 22, `execRead0` 19, `execRead1` 11, `execWrite2` 4, `execPure1` 2,
`execPure3` 2), so `hobliv` for any of those 60 is one `StepObliv` lemma away. `stepObliv_caller` below
fires the `execRead0` discharger on a real opcode, which is what a claim of coverage should have had to
survive in the first place. -/

/-- The shape `execBodyThread_instIdx_congr`'s `hobliv` wants, for one instruction. -/
abbrev StepObliv (inst : Instruction) : Prop :=
  ∀ (t t' : VenomState) (j : Nat), stepInstBase inst t = ExecResult.OK t' →
    stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j }

/-- `ISZERO` — a 1-input pure opcode. -/
theorem stepObliv_iszero {inst : Instruction} (hop : inst.opcode = Opcode.ISZERO) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execPure1_setInstIdx h

/-- `ADDMOD` — a 3-input pure opcode. -/
theorem stepObliv_addmod {inst : Instruction} (hop : inst.opcode = Opcode.ADDMOD) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execPure3_setInstIdx h

/-- `SLOAD` — a 1-input state reader; the reader ignores the index. -/
theorem stepObliv_sload {inst : Instruction} (hop : inst.opcode = Opcode.SLOAD) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execRead1_setInstIdx (fun v u k => sload_setInstIdx v u k) h

/-- `SSTORE` — a 2-input writer; the writer commutes with setting the index. -/
theorem stepObliv_sstore {inst : Instruction} (hop : inst.opcode = Opcode.SSTORE) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execWrite2_setInstIdx (fun v1 v2 u k => sstore_setInstIdx v1 v2 u k) h

/-- `CALLER` — a 0-input state reader, and the opcode that refutes the retracted claim above:
`execRead0` is the environment-push family, nineteen opcodes strong. The reader looks only at
`callCtx`, which `instIdx :=` does not touch, so the side condition is `rfl`. -/
theorem stepObliv_caller {inst : Instruction} (hop : inst.opcode = Opcode.CALLER) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execRead0_setInstIdx (fun _ _ => rfl) h

/-- `ASSIGN` — one of the 21 body opcodes with *no* combinator: its arm is written out inline. It
writes only `vars`, so obliviousness still holds; it just has to be proved structurally. -/
theorem stepObliv_assign {inst : Instruction} (hop : inst.opcode = Opcode.ASSIGN) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons o1 rest =>
    cases rest with
    | cons _ _ => rw [hops] at h; exact absurd h (by simp)
    | nil =>
      cases houts : inst.outputs with
      | nil => rw [hops, houts] at h; exact absurd h (by simp)
      | cons out orest =>
        cases orest with
        | cons _ _ => rw [hops, houts] at h; exact absurd h (by simp)
        | nil =>
          rw [hops, houts] at h
          dsimp only at h ⊢
          simp only [evalOperand_setInstIdx]
          cases hv : evalOperand o1 t with
          | none => rw [hv] at h; exact absurd h (by simp)
          | some v =>
            rw [hv] at h
            simp only [ExecResult.OK.injEq] at h
            subst h
            dsimp only
            rw [updateVar_setInstIdx]

/-- `NOP` — the degenerate case: it returns the state untouched, so obliviousness is definitional. -/
theorem stepObliv_nop {inst : Instruction} (hop : inst.opcode = Opcode.NOP) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  simp only [ExecResult.OK.injEq] at h
  subst h
  rfl

/-- `MCOPY` — a 3-operand memory mover with no combinator. The `mcopy_setInstIdx` atom already existed
in the codebase (nothing consumed it); this is the opcode that consumes it. -/
theorem stepObliv_mcopy {inst : Instruction} (hop : inst.opcode = Opcode.MCOPY) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 =>
  cases r1 with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons b r2 =>
  cases r2 with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons c r3 =>
  cases r3 with
  | cons _ _ => rw [hops] at h; exact absurd h (by simp)
  | nil =>
    rw [hops] at h
    dsimp only at h ⊢
    simp only [evalOperand_setInstIdx]
    cases ha : evalOperand a t with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some va =>
    cases hb : evalOperand b t with
    | none => rw [ha, hb] at h; exact absurd h (by simp)
    | some vb =>
    cases hc : evalOperand c t with
    | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
    | some vc =>
      rw [ha, hb, hc] at h
      simp only [ExecResult.OK.injEq] at h
      subst h
      dsimp only
      rw [mcopy_setInstIdx]

/-- `ASSERT` — a *conditional abort*, and the opcode I twice mis-classified. It is **not** a terminator
(`isTerminator` is exactly `JMP JNZ DJMP RET RETURN REVERT STOP SINK SELFDESTRUCT INVALID`), and it is
**not** excluded from codegen — `generateEmitOps` lowers it to `ISZERO; PUSH revert; JUMPI`. It is an
ordinary body opcode, and obliviousness is nearly free: `StepObliv` constrains only the `OK` branch, so
the `Abort` branch is ruled out by the hypothesis and the surviving branch returns the state untouched. -/
theorem stepObliv_assert {inst : Instruction} (hop : inst.opcode = Opcode.ASSERT) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 =>
  cases r1 with
  | cons _ _ => rw [hops] at h; exact absurd h (by simp)
  | nil =>
    rw [hops] at h
    dsimp only at h ⊢
    simp only [evalOperand_setInstIdx]
    cases ha : evalOperand a t with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some va =>
      rw [ha] at h
      dsimp only at h ⊢
      by_cases hz : va = (⟨0⟩ : EvmYul.UInt256)
      · rw [if_pos hz] at h; exact absurd h (by simp)
      · rw [if_neg hz] at h
        rw [if_neg hz]
        simp only [ExecResult.OK.injEq] at h
        subst h
        rfl

/-- `ISTORE` — writes the `immutables` map, which `instIdx :=` does not touch, so the post-states are
literally the same record. -/
theorem stepObliv_istore {inst : Instruction} (hop : inst.opcode = Opcode.ISTORE) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 =>
  cases r1 with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons b r2 =>
  cases r2 with
  | cons _ _ => rw [hops] at h; exact absurd h (by simp)
  | nil =>
    rw [hops] at h
    dsimp only at h ⊢
    simp only [evalOperand_setInstIdx]
    cases ha : evalOperand a t with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some va =>
    cases hb : evalOperand b t with
    | none => rw [ha, hb] at h; exact absurd h (by simp)
    | some vb =>
      rw [ha, hb] at h
      simp only [ExecResult.OK.injEq] at h
      subst h
      rfl

/-! #### The eleven inline arms

Of the 81 body opcode arms, 60 route through a combinator (above). The other 21 write their arm out
inline. Eleven of those are dischargeable and are discharged here; the remaining ten are excluded by
class — CALL / CREATE / CREATE2 / DELEGATECALL / STATICCALL / INVOKE are external-call machinery, ALLOCA
and DLOADBYTES are lowered before codegen (`opToEvm` returns `none`), and PHI / PARAM are the prefix.

RETRACTION, the second of this arc. I described SHA3, LOG, CALLDATACOPY, CODECOPY, EXTCODECOPY and
RETURNDATACOPY as "six genuine gaps — memory-reading arms, genuinely harder." They are not harder. Every
one of them is `evalOperand` (already oblivious) over a field `instIdx :=` does not touch, followed by
`writeMemoryWithExpansion` or `updateVar`. Two `rfl` atoms — `readMemory_setInstIdx` and
`writeMemoryWithExpansion_setInstIdx` — discharge all six, and they went through on the first probe. The
claim was pessimistic rather than flattering, which is why it went unchallenged for a commit: a guess
that undersells the work still needs checking. -/

@[simp] theorem readMemory_setInstIdx (o sz : Nat) (t : VenomState) (j : Nat) :
    readMemory o sz { t with instIdx := j } = readMemory o sz t := rfl

@[simp] theorem writeMemoryWithExpansion_setInstIdx (o : Nat) (b : ByteArray) (t : VenomState) (j : Nat) :
    writeMemoryWithExpansion o b { t with instIdx := j }
      = { writeMemoryWithExpansion o b t with instIdx := j } := rfl

theorem stepObliv_sha3 {inst : Instruction} (hop : inst.opcode = Opcode.SHA3) : StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 => cases r1 with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons b r2 => cases r2 with
      | cons _ _ => rw [hops] at h; exact absurd h (by simp)
      | nil =>
        cases houts : inst.outputs with
        | nil =>
          rw [hops, houts] at h; dsimp only at h
          cases ha : evalOperand a t <;> cases hb : evalOperand b t <;>
            rw [ha, hb] at h <;> exact absurd h (by simp)
        | cons out o2 => cases o2 with
          | cons _ _ =>
            rw [hops, houts] at h; dsimp only at h
            cases ha : evalOperand a t <;> cases hb : evalOperand b t <;>
              rw [ha, hb] at h <;> exact absurd h (by simp)
          | nil =>
            rw [hops, houts] at h; dsimp only at h ⊢
            simp only [evalOperand_setInstIdx]
            cases ha : evalOperand a t with
            | none => rw [ha] at h; exact absurd h (by simp)
            | some va => cases hb : evalOperand b t with
              | none => rw [ha, hb] at h; exact absurd h (by simp)
              | some vb =>
                rw [ha, hb] at h; dsimp only at h ⊢
                simp only [ExecResult.OK.injEq] at h
                subst h
                rw [readMemory_setInstIdx, updateVar_setInstIdx]

/-- 3-operand memory writers whose source is a preserved field: CALLDATACOPY / CODECOPY. -/
theorem stepObliv_calldatacopy {inst : Instruction} (hop : inst.opcode = Opcode.CALLDATACOPY) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 => cases r1 with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons b r2 => cases r2 with
      | nil => rw [hops] at h; exact absurd h (by simp)
      | cons c r3 => cases r3 with
        | cons _ _ => rw [hops] at h; exact absurd h (by simp)
        | nil =>
          rw [hops] at h; dsimp only at h ⊢
          simp only [evalOperand_setInstIdx]
          cases ha : evalOperand a t with
          | none => rw [ha] at h; exact absurd h (by simp)
          | some va => cases hb : evalOperand b t with
            | none => rw [ha, hb] at h; exact absurd h (by simp)
            | some vb => cases hc : evalOperand c t with
              | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
              | some vc =>
                rw [ha, hb, hc] at h; dsimp only at h ⊢
                simp only [ExecResult.OK.injEq] at h
                subst h
                rw [writeMemoryWithExpansion_setInstIdx]

theorem stepObliv_codecopy {inst : Instruction} (hop : inst.opcode = Opcode.CODECOPY) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 => cases r1 with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons b r2 => cases r2 with
      | nil => rw [hops] at h; exact absurd h (by simp)
      | cons c r3 => cases r3 with
        | cons _ _ => rw [hops] at h; exact absurd h (by simp)
        | nil =>
          rw [hops] at h; dsimp only at h ⊢
          simp only [evalOperand_setInstIdx]
          cases ha : evalOperand a t with
          | none => rw [ha] at h; exact absurd h (by simp)
          | some va => cases hb : evalOperand b t with
            | none => rw [ha, hb] at h; exact absurd h (by simp)
            | some vb => cases hc : evalOperand c t with
              | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
              | some vc =>
                rw [ha, hb, hc] at h; dsimp only at h ⊢
                simp only [ExecResult.OK.injEq] at h
                subst h
                rw [writeMemoryWithExpansion_setInstIdx]

@[simp] theorem evalOperands_setInstIdx (ops : List Operand) (t : VenomState) (j : Nat) :
    evalOperands ops { t with instIdx := j } = evalOperands ops t := by
  induction ops with
  | nil => rfl
  | cons o r ih => simp only [evalOperands, evalOperand_setInstIdx, ih]

theorem stepObliv_extcodecopy {inst : Instruction} (hop : inst.opcode = Opcode.EXTCODECOPY) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 => cases r1 with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons b r2 => cases r2 with
      | nil => rw [hops] at h; exact absurd h (by simp)
      | cons c r3 => cases r3 with
        | nil => rw [hops] at h; exact absurd h (by simp)
        | cons d r4 => cases r4 with
          | cons _ _ => rw [hops] at h; exact absurd h (by simp)
          | nil =>
            rw [hops] at h; dsimp only at h ⊢
            simp only [evalOperand_setInstIdx]
            cases ha : evalOperand a t with
            | none => rw [ha] at h; exact absurd h (by simp)
            | some va => cases hb : evalOperand b t with
              | none => rw [ha, hb] at h; exact absurd h (by simp)
              | some vb => cases hc : evalOperand c t with
                | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
                | some vc => cases hd : evalOperand d t with
                  | none => rw [ha, hb, hc, hd] at h; exact absurd h (by simp)
                  | some vd =>
                    rw [ha, hb, hc, hd] at h; dsimp only at h ⊢
                    simp only [ExecResult.OK.injEq] at h
                    subst h
                    rw [writeMemoryWithExpansion_setInstIdx]

theorem stepObliv_returndatacopy {inst : Instruction} (hop : inst.opcode = Opcode.RETURNDATACOPY) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a r1 => cases r1 with
    | nil => rw [hops] at h; exact absurd h (by simp)
    | cons b r2 => cases r2 with
      | nil => rw [hops] at h; exact absurd h (by simp)
      | cons c r3 => cases r3 with
        | cons _ _ => rw [hops] at h; exact absurd h (by simp)
        | nil =>
          rw [hops] at h; dsimp only at h ⊢
          simp only [evalOperand_setInstIdx]
          cases ha : evalOperand a t with
          | none => rw [ha] at h; exact absurd h (by simp)
          | some va => cases hb : evalOperand b t with
            | none => rw [ha, hb] at h; exact absurd h (by simp)
            | some vb => cases hc : evalOperand c t with
              | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
              | some vc =>
                rw [ha, hb, hc] at h; dsimp only at h ⊢
                by_cases hov : vb.toNat + vc.toNat > t.returndata.size
                · rw [if_pos hov] at h; exact absurd h (by simp)
                · rw [if_neg hov] at h
                  rw [if_neg hov]
                  simp only [ExecResult.OK.injEq] at h
                  subst h
                  rw [writeMemoryWithExpansion_setInstIdx]

theorem stepObliv_log {inst : Instruction} (hop : inst.opcode = Opcode.LOG) : StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢; rw [hop] at h ⊢; dsimp only at h ⊢
  cases hops : inst.operands with
  | nil => rw [hops] at h; exact absurd h (by simp)
  | cons a rest =>
    cases a with
    | Var v => rw [hops] at h; exact absurd h (by simp)
    | Label l => rw [hops] at h; exact absurd h (by simp)
    | Lit tc =>
      rw [hops] at h; dsimp only at h ⊢
      by_cases hlen : (rest.length != tc.toNat + 2) = true
      · rw [if_pos hlen] at h; exact absurd h (by simp)
      · rw [if_neg hlen] at h
        rw [if_neg hlen]
        simp only [evalOperand_setInstIdx, evalOperands_setInstIdx]
        cases ha : evalOperand rest[0]! t with
        | none => rw [ha] at h; exact absurd h (by simp)
        | some va => cases hb : evalOperand rest[1]! t with
          | none => rw [ha, hb] at h; exact absurd h (by simp)
          | some vb => cases hc : evalOperands (rest.drop 2) t with
            | none => rw [ha, hb, hc] at h; exact absurd h (by simp)
            | some vc =>
              rw [ha, hb, hc] at h; dsimp only at h ⊢
              simp only [ExecResult.OK.injEq] at h
              subst h
              rw [readMemory_setInstIdx]


/-- `ADD` — a 2-input pure opcode; the family that already had a discharger. -/
theorem stepObliv_add {inst : Instruction} (hop : inst.opcode = Opcode.ADD) :
    StepObliv inst := by
  intro t t' j h
  unfold stepInstBase at h ⊢
  rw [hop] at h ⊢
  exact execPure2_setInstIdx h


/-! ## Fresh labels: replacing the `hgood` ban with a naming condition

`hgood` bans the three opcodes that mint fresh labels — INVOKE, ASSERT_UNREACHABLE, DJMP — and is consumed
in exactly three places, all one-liners over the plan's label count. The ban is stronger than anything the
counting argument needs.

What it needs is that the label being counted is not one a `freshLabel` could have minted. Every minted
label carries its prefix by construction; every other label operation in the emitter is a `SOPushLabel`,
which is a *push*, not a definition. So the ban is replaced here by `¬ IsFreshLabel bb.label` — a fact
about naming, which no real function violates.

`DJMP`'s targets, incidentally, are label operands: `djmp_target_is_static_succ` shows the block a `DJMP`
hands control to is always a static CFG successor, which refutes the reason originally given for excluding
it. -/

/-- `extractLabels` returns exactly the labels it was given. -/
theorem extractLabels_mem {labelOps : List Operand} {labels : List String} {l : String}
    (h : extractLabels labelOps = some labels) (hl : l ∈ labels) :
    Operand.Label l ∈ labelOps := by
  induction labelOps generalizing labels with
  | nil => simp only [extractLabels, Option.some.injEq] at h; subst h; simp at hl
  | cons op rest ih =>
    cases op with
    | Var _ => simp [extractLabels] at h
    | Lit _ => simp [extractLabels] at h
    | Label lbl =>
      simp only [extractLabels] at h
      cases hr : extractLabels rest with
      | none => rw [hr] at h; simp at h
      | some ls =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hl with rfl | hmem
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hr hmem)

/-- **A `DJMP`'s target is always a static CFG successor.** Its targets are *label operands* — the
selector only picks which one — so `getSuccessors`, which `filterMap`s the label operands of any
terminator, already contains every label a `DJMP` can reach.

This refutes the justification the codebase gives for excluding `DJMP` from the reachability-carrying
drivers: that it "computes its target from a runtime selector rather than a label operand, and so could
leave the static CFG". The selector is runtime; the *targets* are not. -/
theorem djmp_target_is_static_succ {inst : Instruction} {s s' : VenomState}
    (hop : inst.opcode = Opcode.DJMP)
    (hstep : stepInstBase inst s = ExecResult.OK s') :
    s'.currentBb ∈ getSuccessors inst := by
  unfold stepInstBase at hstep
  rw [hop] at hstep
  cases hops : inst.operands with
  | nil => rw [hops] at hstep; exact absurd hstep (by simp)
  | cons sel labelOps =>
    rw [hops] at hstep
    dsimp only at hstep
    cases hsel : evalOperand sel s with
    | none => rw [hsel] at hstep; exact absurd hstep (by simp)
    | some idx =>
      cases hlab : extractLabels labelOps with
      | none => rw [hsel, hlab] at hstep; exact absurd hstep (by simp)
      | some labels =>
        rw [hsel, hlab] at hstep
        dsimp only at hstep
        split at hstep
        · rename_i hlt
          simp only [ExecResult.OK.injEq] at hstep
          subst hstep
          have hcur : (jumpTo (labels.get ⟨idx.toNat, hlt⟩) s).currentBb
              = labels.get ⟨idx.toNat, hlt⟩ := rfl
          rw [hcur]
          unfold getSuccessors
          rw [if_pos (by rw [hop]; decide), hops]
          refine List.mem_filterMap.mpr ⟨Operand.Label (labels.get ⟨idx.toNat, hlt⟩), ?_, rfl⟩
          exact List.mem_cons_of_mem _
            (extractLabels_mem hlab (List.get_mem _ _))
        · exact absurd hstep (by simp)

/-- `freshLabel` names are structurally marked: prefix, underscore, counter. -/
theorem freshLabel_eq (pfx : String) (ps : PlanState) :
    (freshLabel pfx ps).1 = pfx ++ "_" ++ toString (ps.labelCounter + 1) := rfl

/-- **Every `SOLabel` a `DJMP` emits is a trampoline name.** The comparison chain emits none at all; the
trampoline list emits exactly one per target, each from `freshLabel "djmp_tramp"`. -/
theorem djmpChain_soLabel_is_tramp :
    ∀ (ls : List String) (i : Nat) (ps : PlanState) (m : String),
      StackOp.SOLabel m ∈ ((djmpChain i ls ps).2.1 : List StackOp) →
      ∃ k : Nat, m = "djmp_tramp" ++ "_" ++ toString k := by
  intro ls
  induction ls with
  | nil => intro i ps m hm; simp [djmpChain] at hm
  | cons l rest ih =>
    intro i ps m hm
    simp only [djmpChain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h) | h
    · injection h with h
      exact ⟨ps.labelCounter + 1, h.trans (freshLabel_eq "djmp_tramp" ps)⟩
    · simp at h
    · simp at h
    · simp at h
    · exact ih (i + 1) (freshLabel "djmp_tramp" ps).2 m h

/-- The comparison chain emits **no** `SOLabel` at all — only `DUP`, `PUSH`, `EQ`, a label *push*, and a
`JUMPI`. Label pushes are not label definitions. -/
theorem djmpChain_chain_no_soLabel :
    ∀ (ls : List String) (i : Nat) (ps : PlanState) (m : String),
      StackOp.SOLabel m ∉ ((djmpChain i ls ps).1 : List StackOp) := by
  intro ls
  induction ls with
  | nil => intro i ps m hm; simp [djmpChain] at hm
  | cons l rest ih =>
    intro i ps m hm
    simp only [djmpChain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h | h) | h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · exact ih (i + 1) (freshLabel "djmp_tramp" ps).2 m h

/-- **Every `SOLabel` in a `DJMP`'s whole plan is a trampoline.** The chain contributes none, the
out-of-range default contributes none, and the trampolines contribute exactly one apiece. -/
theorem generateDjmpPlan_soLabel_is_tramp (labels : List String) (ps : PlanState) (m : String)
    (hm : StackOp.SOLabel m ∈ ((generateDjmpPlan labels ps).1 : List StackOp)) :
    ∃ k : Nat, m = "djmp_tramp" ++ "_" ++ toString k := by
  unfold generateDjmpPlan at hm
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with (h | h | h | h) | h
  · exact absurd h (djmpChain_chain_no_soLabel labels 0 ps m)
  · simp at h
  · simp at h
  · simp at h
  · exact djmpChain_soLabel_is_tramp labels 0 ps m h

/-- A label minted by `freshLabel`, from one of the three prefixes the generator ever uses. -/
def IsFreshLabel (m : String) : Prop :=
  ∃ k : Nat, m = "return_label" ++ "_" ++ toString k ∨
             m = "reachable" ++ "_" ++ toString k ∨
             m = "djmp_tramp" ++ "_" ++ toString k

theorem generateEmitOps_djmp {inst : Instruction} {ltc : Nat} {ps : PlanState}
    (h : inst.opcode = Opcode.DJMP) :
    generateEmitOps inst ltc ps
      = generateDjmpPlan (inst.operands.filterMap
          (fun o => match o with | Operand.Label l => some l | _ => none)) ps := by
  unfold generateEmitOps; simp only [h]; rfl

theorem generateEmitOps_invoke {inst : Instruction} {ltc : Nat} {ps : PlanState}
    (h : inst.opcode = Opcode.INVOKE) :
    generateEmitOps inst ltc ps
      = (match inst.operands.head! with
         | Operand.Label l =>
           let (retLbl, ps') := freshLabel "return_label" ps
           ([StackOp.SOPushLabel retLbl, StackOp.SOPushLabel l,
             StackOp.SOEmit "JUMP", StackOp.SOLabel retLbl], ps')
         | _ => ([], ps)) := by
  unfold generateEmitOps; simp only [h]; rfl

theorem generateEmitOps_assert_unreachable {inst : Instruction} {ltc : Nat} {ps : PlanState}
    (h : inst.opcode = Opcode.ASSERT_UNREACHABLE) :
    generateEmitOps inst ltc ps
      = (let (endLbl, ps') := freshLabel "reachable" ps
         ([StackOp.SOPushLabel endLbl, StackOp.SOEmit "JUMPI",
           StackOp.SOEmit "INVALID", StackOp.SOLabel endLbl], ps')) := by
  unfold generateEmitOps; simp only [h]; rfl

/-- **Every `SOLabel` the emitter ever produces is freshly minted.** Exhaustive over all opcodes: for the
three minters it is `freshLabel`'s, and for everything else `generateEmitOps_no_soLabel` already says
there is no `SOLabel` to talk about. Every other branch emits `SOEmit` or `SOPushLabel` — and a label
*push* is not a label *definition*, which is the distinction this whole question turned on. -/
theorem generateEmitOps_soLabel_is_fresh (inst : Instruction) (ltc : Nat) (ps : PlanState)
    (m : String) (hm : StackOp.SOLabel m ∈ ((generateEmitOps inst ltc ps).1 : List StackOp)) :
    IsFreshLabel m := by
  by_cases hd : inst.opcode = Opcode.DJMP
  · rw [generateEmitOps_djmp hd] at hm
    obtain ⟨k, hk⟩ := generateDjmpPlan_soLabel_is_tramp _ ps m hm
    exact ⟨k, Or.inr (Or.inr hk)⟩
  by_cases hi : inst.opcode = Opcode.INVOKE
  · rw [generateEmitOps_invoke hi] at hm
    split at hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
                 StackOp.SOLabel.injEq] at hm
      exact ⟨ps.labelCounter + 1, Or.inl (hm.trans (freshLabel_eq "return_label" ps))⟩
    · simp at hm
  by_cases ha : inst.opcode = Opcode.ASSERT_UNREACHABLE
  · rw [generateEmitOps_assert_unreachable ha] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
               StackOp.SOLabel.injEq] at hm
    exact ⟨ps.labelCounter + 1, Or.inr (Or.inl (hm.trans (freshLabel_eq "reachable" ps)))⟩
  · exact absurd rfl (generateEmitOps_no_soLabel inst ltc ps hi ha hd _ hm m)

/-- **Every `SOLabel` a regular instruction's plan emits is freshly minted.** Same case structure as
`generateRegularInstPlan_no_soLabel`: every component but the emitter contributes no `SOLabel` at all, and
the emitter's are fresh by `generateEmitOps_soLabel_is_fresh`. -/
theorem generateRegularInstPlan_soLabel_is_fresh (liveness : DfState (List String))
    (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction)
    (nextLiveness : List String) (isHalting nextIsTerminator : Bool) (curBbLabel : String)
    (ps : PlanState) (m : String)
    (hso : StackOp.SOLabel m ∈ ((generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
      isHalting nextIsTerminator curBbLabel ps).1 : List StackOp)) :
    IsFreshLabel m := by
  unfold generateRegularInstPlan at hso
  simp only [] at hso
  have hjoin : ∀ _h : StackOp.SOLabel m ∈ (if inst.opcode = Opcode.JMP then
      (match inst.operands with
       | [Operand.Label target] =>
         match fn.blocks.find? (·.label == target) with
         | none => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)
         | some targetBb =>
           reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
             (liveVarsAt liveness target 0)).map Operand.Var)
             (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2
       | _ => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2))
    else ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)).1,
      IsFreshLabel m := by
    intro h
    exfalso
    (repeat' split at h) <;>
      first
      | exact absurd h List.not_mem_nil
      | exact reorderPlan_no_soLabel _ _ _ h m rfl
  split at hso
  · simp only [List.mem_append] at hso
    rcases hso with ((h | h) | h) | h
    · exact absurd rfl (emitInputPlan_no_soLabel _ _ _ _ _ h m)
    · exact hjoin h
    · exact absurd rfl (reorderPlan_no_soLabel _ _ _ h m)
    · exact generateEmitOps_soLabel_is_fresh _ _ _ m h
  · simp only [List.mem_append] at hso
    rcases hso with (((( h | h) | h) | h) | h) | h
    · exact absurd rfl (emitInputPlan_no_soLabel _ _ _ _ _ h m)
    · exact hjoin h
    · exact absurd rfl (reorderPlan_no_soLabel _ _ _ h m)
    · exact generateEmitOps_soLabel_is_fresh _ _ _ m h
    · exfalso
      (repeat' split at h) <;>
        first
        | exact absurd h List.not_mem_nil
        | exact popmanyPlan_no_soLabel _ _ _ h m rfl
    · exfalso
      (repeat' split at h) <;>
        first
        | exact absurd h List.not_mem_nil
        | exact optimisticSwapPlan_no_soLabel _ _ _ _ _ _ h m rfl

/-- …and therefore every `SOLabel` any instruction's plan emits is freshly minted. -/
theorem generateInstPlan_soLabel_is_fresh (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    {ops : List StackOp} {ps' : PlanState} {m : String}
    (h : generateInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
      curBbLabel ps = some (ops, ps'))
    (hso : StackOp.SOLabel m ∈ (ops : List StackOp)) :
    IsFreshLabel m := by
  unfold generateInstPlan at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq, Prod.ext_iff] at h
      obtain ⟨rfl, -⟩ := h
      exact absurd rfl (generatePhiPlan_no_soLabel _ _ _ _ hso m)
    · split at h
      · simp only [Option.some.injEq, Prod.ext_iff] at h
        obtain ⟨rfl, -⟩ := h
        exact absurd rfl (generateOffsetPlan_no_soLabel _ _ _ hso m)
      · split at h
        · simp only [Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, -⟩ := h
          exact absurd hso (by simp)
        · split at h
          · simp only [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, -⟩ := h
            exact absurd hso (by simp)
          · simp only [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, -⟩ := h
            exact generateRegularInstPlan_soLabel_is_fresh _ _ _ _ _ _ _ _ _ _ m hso

/-- The weaker zero lemma: a label the ops never *define* is counted zero times, even if they define
others. -/
theorem planLabelCount_eq_zero_of_ne (l : String) (ops : List StackOp)
    (h : ∀ so ∈ ops, ∀ m, so = StackOp.SOLabel m → m ≠ l) : planLabelCount l ops = 0 := by
  unfold planLabelCount
  rw [List.countP_eq_zero]
  intro a ha
  cases a with
  | SOLabel m => simpa using (h _ ha m rfl)
  | _ => simp
/-- **A block plan emits its own label exactly once, and no other — with no `hgood` at all.**

The blanket ban on the three minters is replaced by the fact that actually matters: every `SOLabel` the
instruction fold emits is *freshly minted*, and `l` is not a fresh label. Block labels are not fresh
labels, so this covers exactly the case the counting argument uses. -/
theorem generateBlockPlan_planLabelCount_fresh (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (ps : PlanState)
    {blockOps : List StackOp} {ps' : PlanState} {l : String}
    (hlnf : ¬ IsFreshLabel l)
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    planLabelCount l blockOps = if bb.label == l then 1 else 0 := by
  unfold generateBlockPlan at hplan
  simp only [] at hplan
  split at hplan
  · exact absurd hplan (by simp)
  · rename_i instOps ps3 hres
    simp only [Option.some.injEq, Prod.ext_iff] at hplan
    obtain ⟨rfl, -⟩ := hplan
    -- every SOLabel the instruction fold emits is fresh, hence ≠ l
    have hinst : ∀ so ∈ instOps, ∀ m, so = StackOp.SOLabel m → m ≠ l := by
      refine foldl_invariant_mem
        (fun acc : Option (List StackOp × PlanState) =>
          ∀ oo pp, acc = some (oo, pp) → ∀ so ∈ oo, ∀ m, so = StackOp.SOLabel m → m ≠ l)
        _ _ _ ?_ ?_ instOps ps3 hres
      · intro oo pp h
        simp only [Option.some.injEq, Prod.ext_iff] at h
        obtain ⟨rfl, -⟩ := h
        exact fun so hso => absurd hso List.not_mem_nil
      · intro acc x hx hacc oo pp heq so hso
        cases acc with
        | none => exact absurd heq (by simp)
        | some aval =>
          obtain ⟨aops, aps⟩ := aval
          obtain ⟨inst, i⟩ := x
          simp only [] at heq
          split at heq
          · exact absurd heq (by simp)
          · rename_i stepOps aps' hgen
            simp only [Option.some.injEq, Prod.ext_iff] at heq
            obtain ⟨rfl, -⟩ := heq
            rw [List.mem_append] at hso
            rcases hso with h | h
            · exact hacc aops aps rfl so h
            · intro m hm
              subst hm
              intro hml
              exact hlnf (hml ▸ generateInstPlan_soLabel_is_fresh _ _ _ _ _ _ _ _ _ _ hgen h)
    have hparam : ∀ so ∈ (if (fn.blocks.head?.map (·.label)) == some bb.label then
        prepareParamsPlan L fn ps else ([], ps)).1, ∀ m, so ≠ StackOp.SOLabel m := by
      intro so hso
      split at hso
      · exact prepareParamsPlan_no_soLabel _ _ _ so hso
      · exact absurd hso List.not_mem_nil
    have hclean : ∀ so ∈ (if (C.predsOf bb.label).length = 1 then
        cleanStackPlan L C fn bb (if (fn.blocks.head?.map (·.label)) == some bb.label then
          prepareParamsPlan L fn ps else ([], ps)).2
        else ([], (if (fn.blocks.head?.map (·.label)) == some bb.label then
          prepareParamsPlan L fn ps else ([], ps)).2)).1, ∀ m, so ≠ StackOp.SOLabel m := by
      intro so hso
      split at hso
      · exact cleanStackPlan_no_soLabel _ _ _ _ _ so hso
      · exact absurd hso List.not_mem_nil
    rw [planLabelCount_append, planLabelCount_append, planLabelCount_append,
        planLabelCount_soLabel, planLabelCount_eq_zero l _ hparam,
        planLabelCount_eq_zero l _ hclean, planLabelCount_eq_zero_of_ne l _ hinst]
    simp

/-! ### The DFS induction, with `hgood` removed

The same substitution one level up. `generateFnPlan_planLabelCount`'s 4-way DFS invariant is quantified
over every label `l`; the rewrite threads `¬ IsFreshLabel l` in beside it, and the single place the old
proof used `hgood` — the per-block count — takes `generateBlockPlan_planLabelCount_fresh` instead.

Nothing else in a hundred and eighty lines of mutual induction changes, which is the point: the ban on
`INVOKE`, `ASSERT_UNREACHABLE` and `DJMP` was doing exactly one job, in exactly one place, and it was the
wrong job. -/
theorem generateFnPlan_planLabelCount_fresh (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (ps : PlanState) (ops : List StackOp)
       (v' : List String) (ps' : PlanState),
      generateFnPlanAux fuel L D C fn worklist visited ps = some (ops, v', ps') →
      ∀ l, ¬ IsFreshLabel l → (visited.contains l = true → planLabelCount l ops = 0)
         ∧ planLabelCount l ops ≤ 1
         ∧ (1 ≤ planLabelCount l ops → v'.contains l = true)
         ∧ (visited.contains l = true → v'.contains l = true))
    ∧
    (∀ (ss : List Operand) (sp : SpilledMap) (succs visited : List String) (psG : PlanState)
       (ops : List StackOp) (v' : List String) (ps' : PlanState),
      generateSuccsPlan fuel L D C fn ss sp succs visited psG = some (ops, v', ps') →
      ∀ l, ¬ IsFreshLabel l → (visited.contains l = true → planLabelCount l ops = 0)
         ∧ planLabelCount l ops ≤ 1
         ∧ (1 ≤ planLabelCount l ops → v'.contains l = true)
         ∧ (visited.contains l = true → v'.contains l = true)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited ps ops v' ps' h l hlnf => ?_,
            fun ss sp succs visited psG ops v' ps' h l hlnf => ?_⟩
    · rw [generateFnPlanAux] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨fun _ => rfl, by simp [planLabelCount], by simp [planLabelCount], fun hv => hv⟩
    · rw [generateSuccsPlan] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨fun _ => rfl, by simp [planLabelCount], by simp [planLabelCount], fun hv => hv⟩
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨fun worklist visited ps ops v' ps' h l hlnf => ?_,
            fun ss sp succs visited psG ops v' ps' h l hlnf => ?_⟩
    · cases worklist with
      | nil =>
        rw [generateFnPlanAux] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨fun _ => rfl, by simp [planLabelCount], by simp [planLabelCount], fun hv => hv⟩
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [generateFnPlanAux_skip_visited _ _ _ _ _ _ _ _ _ hvis] at h
          exact ihA rest visited ps ops v' ps' h l hlnf
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [generateFnPlanAux_find_none _ _ _ _ _ _ _ _ _ hvisf hfind] at h
            obtain ⟨hA, hB, hCc, hD⟩ := ihA rest (lbl :: visited) ps ops v' ps' h l hlnf
            exact ⟨fun hv => hA (contains_cons_of_contains hv), hB, hCc,
                   fun hv => hD (contains_cons_of_contains hv)⟩
          | some bb =>
            rw [generateFnPlanAux_visit_block _ _ _ _ _ _ _ _ _ _ hvisf hfind] at h
            split at h
            · exact absurd h (by simp)
            · rename_i blockOps psB hbp
              split at h
              · exact absurd h (by simp)
              · rename_i succOps v2 ps2 hsucc
                split at h
                · exact absurd h (by simp)
                · rename_i restOps vF psF hrest
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, -⟩ := h
                  -- bb's own label is lbl
                  have hlbl : bb.label = lbl := by
                    have := List.find?_some hfind
                    simpa using this
                  have hmemb : bb ∈ fn.blocks := List.mem_of_find?_eq_some hfind
                  have hcB := generateBlockPlan_planLabelCount_fresh L D C fn bb ps hlnf hbp
                  rw [hlbl] at hcB
                  obtain ⟨hSa, hSb, hSc, hSd⟩ :=
                    ihS psB.stack psB.spilled (C.succsOf lbl) (lbl :: visited) psB succOps v2 ps2
                      hsucc l hlnf
                  obtain ⟨hRa, hRb, hRc, hRd⟩ := ihA rest v2 ps2 restOps vF psF hrest l hlnf
                  rw [planLabelCount_append, planLabelCount_append]
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro hv
                    have hne : (lbl == l) = false := by
                      by_cases hh : lbl = l
                      · subst hh; rw [hvisf] at hv; simp at hv
                      · simpa using hh
                    rw [hcB, hne]
                    have h1 : planLabelCount l succOps = 0 := hSa (contains_cons_of_contains hv)
                    have h2 : planLabelCount l restOps = 0 :=
                      hRa (hSd (contains_cons_of_contains hv))
                    simp [h1, h2]
                  · by_cases hh : lbl = l
                    · subst hh
                      have hvl : (lbl :: visited).contains lbl = true := by simp
                      have h1 : planLabelCount lbl succOps = 0 := hSa hvl
                      have h2 : planLabelCount lbl restOps = 0 := hRa (hSd hvl)
                      rw [hcB]; simp [h1, h2]
                    · have hne : (lbl == l) = false := by simpa using hh
                      rw [hcB, hne]
                      by_cases hs : 1 ≤ planLabelCount l succOps
                      · have h2 : planLabelCount l restOps = 0 := hRa (hSc hs)
                        simp [h2]; omega
                      · have h1 : planLabelCount l succOps = 0 := by omega
                        simp [h1]; omega
                  · intro hge
                    by_cases hh : lbl = l
                    · subst hh
                      exact hRd (hSd (by simp))
                    · have hne : (lbl == l) = false := by simpa using hh
                      rw [hcB, hne] at hge
                      simp at hge
                      by_cases hs : 1 ≤ planLabelCount l succOps
                      · exact hRd (hSc hs)
                      · have h1 : planLabelCount l succOps = 0 := by omega
                        rw [h1] at hge
                        exact hRc (by omega)
                  · intro hv
                    exact hRd (hSd (contains_cons_of_contains hv))
    · cases succs with
      | nil =>
        rw [generateSuccsPlan] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨fun _ => rfl, by simp [planLabelCount], by simp [planLabelCount], fun hv => hv⟩
      | cons succ rest =>
        rw [generateSuccsPlan] at h
        simp only [] at h
        split at h
        · exact absurd h (by simp)
        · rename_i sOps vAfter psAfter hga
          split at h
          · exact absurd h (by simp)
          · rename_i restOps vF psF hgs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            obtain ⟨hAa, hAb, hAc, hAd⟩ :=
              ihA [succ] visited { psG with stack := ss, spilled := sp } sOps vAfter psAfter hga l hlnf
            have psG' : PlanState :=
              { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
            obtain ⟨hRa, hRb, hRc, hRd⟩ :=
              ihS ss sp rest vAfter _ restOps vF psF hgs l hlnf
            rw [planLabelCount_append]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro hv
              have h1 : planLabelCount l sOps = 0 := hAa hv
              have h2 : planLabelCount l restOps = 0 := hRa (hAd hv)
              simp [h1, h2]
            · by_cases hs : 1 ≤ planLabelCount l sOps
              · have h2 : planLabelCount l restOps = 0 := hRa (hAc hs)
                simp [h2]; omega
              · have h1 : planLabelCount l sOps = 0 := by omega
                simp [h1]; omega
            · intro hge
              by_cases hs : 1 ≤ planLabelCount l sOps
              · exact hRd (hAc hs)
              · have h1 : planLabelCount l sOps = 0 := by omega
                rw [h1] at hge
                exact hRc (by omega)
            · intro hv
              exact hRd (hAd hv)

/-- **The whole-function plan emits each non-fresh label at most once — no `hgood`.** -/
theorem generateFnPlanFuel_planLabelCount_fresh {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {ops : List StackOp} {ps : PlanState}
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (l : String) (hlnf : ¬ IsFreshLabel l) :
    planLabelCount l ops ≤ 1 := by
  unfold generateFnPlanFuel at hgen
  simp only [] at hgen
  split at hgen
  · simp only [Option.some.injEq, Prod.mk.injEq] at hgen
    obtain ⟨rfl, -⟩ := hgen
    simp [planLabelCount]
  · split at hgen
    · exact absurd hgen (by simp)
    · rename_i ops2 v2 ps2 haux
      simp only [Option.some.injEq, Prod.mk.injEq] at hgen
      obtain ⟨rfl, -⟩ := hgen
      exact ((generateFnPlan_planLabelCount_fresh (livenessAnalyzeFuel fuel fn)
        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn fuel).1
        _ [] _ _ _ _ haux l hlnf).2.1

/-- **`hpreuniq`, discharged for functions containing `DJMP`, `INVOKE` and `ASSERT_UNREACHABLE`.**

The side condition is no longer a ban on those three opcodes, but a fact about naming: the block's own
label is not one a `freshLabel` could have minted. No real function violates it, and it is the only thing
the counting argument ever needed. -/
theorem hpreuniq_fresh {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {ops blockOps rest : List StackOp} {ps : PlanState} {bb : BasicBlock}
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hblk : blockOps = StackOp.SOLabel bb.label :: rest) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_of_asmLabelCount_one hblk
    (by rw [asmLabelCount_executePlan]
        exact generateFnPlanFuel_planLabelCount_fresh hgen bb.label hbbnf)

/-- The cheap discharge: every fresh label is at least ten characters — `"reachable" ++ "_"` is the
shortest prefix at ten, before any digits — so any shorter name is safe. Every block label in this file
qualifies with room to spare. -/
theorem short_not_fresh {l : String} (h : l.length < 10) : ¬ IsFreshLabel l := by
  rintro ⟨k, hk | hk | hk⟩ <;>
    · rw [hk] at h
      simp only [String.length_append] at h
      have h1 : "return_label".length = 12 := rfl
      have h2 : "reachable".length = 9 := rfl
      have h3 : "djmp_tramp".length = 10 := rfl
      have h4 : "_".length = 1 := rfl
      omega

/-- **`hpreuniq` in the form a caller has it — no `hgood`.** Drop-in for `hpreuniq_of_blockPlan`. -/
theorem hpreuniq_of_blockPlan_fresh {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps')) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  exact hpreuniq_fresh hbbnf hgen hrest

/-- **`hoff_lk`, discharged with no `hgood`.** Drop-in for `labelOffset_of_blockPlan`. -/
theorem labelOffset_of_blockPlan_fresh {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops pre suf blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps'))
    (hseg : ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan ops)).2 bb.label
      = some (((executePlan pre).map asmInstSize).sum) := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  exact labelOffset_of_plan hseg hrest
    (generateFnPlanFuel_planLabelCount_fresh hgen bb.label hbbnf)

/-- **`hoff_lk` + `hidx_lk` + `hidxeq` together, with no `hgood`.** Drop-in for
`jumpTarget_of_blockPlan` — the whole jump-target family, for a function that may contain `DJMP`,
`INVOKE` or `ASSERT_UNREACHABLE`. -/
theorem jumpTarget_of_blockPlan_fresh {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops pre suf blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps'))
    (hseg : ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan ops)).2 bb.label
        = some (((executePlan pre).map asmInstSize).sum) ∧
    AssocList.lookup Nat Nat (asmResolve (executePlan ops)).2
        (((executePlan pre).map asmInstSize).sum) = some (executePlan pre).length ∧
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan pre).length := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  have hcount := generateFnPlanFuel_planLabelCount_fresh hgen bb.label hbbnf
  obtain ⟨h2, h3⟩ := idxOfLabel_of_plan hseg hrest hcount
  exact ⟨labelOffset_of_plan hseg hrest hcount, h2, h3⟩

end EvmYul.Venom.Hol.Codegen

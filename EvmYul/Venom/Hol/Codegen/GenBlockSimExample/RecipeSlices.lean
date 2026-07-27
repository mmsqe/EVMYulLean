/-
GenBlockSimExample / hsupply slice families & the recipe → walk bridges

Split part of `GenBlockSimExample`; see that module's header for the full roadmap.
This part is wrapped in `namespace EvmYul.Venom.Hol.Codegen` (the enclosing namespace of the second half); layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeWalk

namespace EvmYul.Venom.Hol.Codegen

/-! ## The first generic `hsupply` slices: empty-body halting blocks

`codegen_correct_ofBlocks_recipeW`'s `hsupply` needs, per block, a body-sim run plus a `TermRecipeW`. For a
block whose only instruction is its terminator BOTH halves are already generic: the asm side is the SOLabel
step (`soLabel_sim`), the Venom side is `termRecipeW_*_of_body`. Composing them discharges `hsupply` for an
ARBITRARY such block from its layout facts alone — no per-function `simp`, no per-function `runBlock`. -/

/-- **Generic `hsupply` for an empty-body STOP block.** For ANY `bb` whose instructions are `[stopInst]`: the
    SOLabel step supplies the body-sim run, the STOP producer supplies the recipe. The caller gives only the
    block's asm layout (`asmBlockAt` at the block's pc, the STOP placement one past it) and the budget bound. -/
theorem hsupplyW_emptyStop {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hstoppc : asm.pc + 1 < prog.length)
    (hstop : prog.get ⟨asm.pc + 1, hstoppc⟩ = AsmInst.AsmOp "STOP")
    (hw : 1 + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt : as1.pc < prog.length := by rw [hpc1']; exact hstoppc
  have hst : prog.get ⟨as1.pc, hlt⟩ = AsmInst.AsmOp "STOP" := by
    conv_lhs => rw [show (⟨as1.pc, hlt⟩ : Fin _) = ⟨asm.pc + 1, hstoppc⟩ from Fin.ext hpc1']
    exact hstop
  rw [hlen1] at hrun1
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_stop_of_body (front := []) (stopInst := stopInst) (hd := stopInst) (tl := [])
    (restFuel := k) (by simpa using hbb) hstopop (by simp) (by rw [hstopop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel1 hw hlt hst

/-- **Generic `hsupply` for an empty-body INVALID block** — the aborting sibling, same composition. -/
theorem hsupplyW_emptyInvalid {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {invInst : Instruction}
    (hbb : bb.instructions = [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hinvpc : asm.pc + 1 < prog.length)
    (hinv : prog.get ⟨asm.pc + 1, hinvpc⟩ = AsmInst.AsmOp "INVALID")
    (hw : 1 + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt : as1.pc < prog.length := by rw [hpc1']; exact hinvpc
  have hiv : prog.get ⟨as1.pc, hlt⟩ = AsmInst.AsmOp "INVALID" := by
    conv_lhs => rw [show (⟨as1.pc, hlt⟩ : Fin _) = ⟨asm.pc + 1, hinvpc⟩ from Fin.ext hpc1']
    exact hinv
  rw [hlen1] at hrun1
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_invalid_of_body (front := []) (invInst := invInst) (hd := invInst) (tl := [])
    (restFuel := k) (by simpa using hbb) hinvop (by simp) (by rw [hinvop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel1 hw hlt hiv

/-- **Generic `hsupply` for an empty-body JMP block** — the first CONTINUING empty-body slice. For ANY `bb`
    whose instructions are `[jmpInst]`: the SOLabel step supplies the body-sim run (`soLabel_sim`), the JMP
    producer supplies the recipe (`termRecipeW_jmp_of_body`). Unlike the halting slices this one must also
    hand over the successor: its plan state (`hps`), its block (`hlk'`), and its jump-target resolution
    (`hoff_lk`/`hidx_lk`). The caller gives only layout facts — no per-function `runBlock` reduction. -/
theorem hsupplyW_emptyJmp {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s : VenomState} {jmpInst : Instruction} {lbl : String}
    (hbb : bb.instructions = [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hnothalt : s.halted = false)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm) (hps : ps = psOf lbl)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hpush1 : asm.pc + 1 < prog.length)
    (hpush : prog.get ⟨asm.pc + 1, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hjump1 : asm.pc + 1 + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + 1 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb')
    (hw : wOf lbl + (1 + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt1 : as1.pc < prog.length := by rw [hpc1']; exact hpush1
  have hp : prog.get ⟨as1.pc, hlt1⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl) := by
    conv_lhs => rw [show (⟨as1.pc, hlt1⟩ : Fin _) = ⟨asm.pc + 1, hpush1⟩ from Fin.ext hpc1']
    exact hpush
  have hlt2 : as1.pc + 1 < prog.length := by rw [hpc1']; exact hjump1
  have e2 : as1.pc + 1 = asm.pc + 1 + 1 := by rw [hpc1']
  have hj : prog.get ⟨as1.pc + 1, hlt2⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨as1.pc + 1, hlt2⟩ : Fin _) = ⟨asm.pc + 1 + 1, hjump1⟩ from Fin.ext e2]
    exact hjump
  rw [hlen1] at hrun1
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_jmp_of_body (front := []) (jmpInst := jmpInst) (hd := jmpInst) (tl := [])
    (restFuel := k) (bb' := bb') (by simpa using hbb) hjmpop hoperands (by simp)
    (by rw [hjmpop]; decide) (by intro i hi; cases hi) (by simp [execBodyThread])
    (by simpa using hnothalt) hrel1 hps hw hlt1 hp hoff_lk hoff hlt2 hj hidx_lk hlk'


/-- **Generic `hsupply` for a NON-EMPTY-body STOP block.** The empty-body slices bottom out in
    `soLabel_sim`; this one takes the real body-sim stack — `RegularBodyH` (the per-instruction condition)
    → `bodyStepsReadyH_regular_list` → `genBlockBodyH_sim_inv` — for the asm half, and
    `termRecipeW_stop_of_body` for the Venom half, reconciling the two notions of the body-end Venom state
    (`genBlockBodyH_sim_inv`'s `gvBodyStep` fold vs the producer's `execBodyThread` `sEnd`) through
    `execBodyThread_eq_gvFold`. So `codegen_correct_ofBlocks_recipeW`'s per-block obligation is discharged
    for ANY STOP block of modeled instructions — the body no longer has to be empty. Mirrors
    `HbsimMatch_stop_regular`, but lands in the recipe shape the driver consumes. -/
theorem termRecipeW_stop_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    -- the per-instruction condition (irreducible) + structural invariants
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    -- STOP placed right after the body
    (hpc : as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hstop : prog.get ⟨as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hstop_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hstop
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  exact ⟨as', _, sEnd, _, hrun,
    termRecipeW_stop_of_body hbb hstopop hcons hphi hnonterm hthread hrel' hle hpc_as hstop_as⟩

/-- **Generic `hsupply` for a NON-EMPTY-body INVALID block** — the aborting sibling of
    `termRecipeW_stop_regular`: identical body-sim stack, the terminator's placement swapped. -/
theorem termRecipeW_invalid_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    -- the per-instruction condition (irreducible) + structural invariants
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    -- STOP placed right after the body
    (hpc : as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hinv : prog.get ⟨as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = AsmInst.AsmOp "INVALID")
    (hle : (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hinv_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hinv
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  exact ⟨as', _, sEnd, _, hrun,
    termRecipeW_invalid_of_body hbb hinvop hcons hphi hnonterm hthread hrel' hle hpc_as hinv_as⟩








set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body JMP block** — the first CONTINUING `_regular` slice. -/
theorem termRecipeW_jmp_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel off : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {lbl : String}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 = psOf lbl)
    (hpc : as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb')
    (hle : wOf lbl + ((executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hpush_as : prog.get ⟨as'.pc, hpc_as⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl) := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hpush
  have hpc2_as : as'.pc + 1 < prog.length := by rw [hpc']; exact hpc2
  have e2 : as'.pc + 1 = as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 := by rw [hpc']
  have hjump_as : prog.get ⟨as'.pc + 1, hpc2_as⟩ = AsmInst.AsmOp "JUMP" := by
    rw [show (⟨as'.pc + 1, hpc2_as⟩ : Fin prog.length) = ⟨_, hpc2⟩ from Fin.ext e2]
    exact hjump
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  exact ⟨as', _, sEnd, _, hrun,
    termRecipeW_jmp_of_body hbb hjmpop hoperands hcons hphi hnonterm hthread hnothalt hrel' hps hle
      hpc_as hpush_as hoff_lk hoff hpc2_as hjump_as hidx_lk hlk'⟩


/-- **Non-vacuity of `termRecipeW_jmp_regular`.** Instantiated at an EMPTY body every generator-side
    hypothesis discharges outright: the per-instruction condition `RegularBodyH` is trivially true at `[]`,
    and the body fold collapses DEFINITIONALLY to `([], ps0)` — so the emitted plan is empty, `bodyLen = 0`,
    `hps` becomes `ps0 = psOf lbl`, and the terminator sits at `as0.pc`. What remains are the state
    hypotheses every consumer already carries, and those are inhabited: `venomAsmRel_init0_iff` characterises
    `venomAsmRel lo (initPlanState 0) vs asm` as "asm mirrors vs with an empty stack" (satisfiable for any
    `vs`), and `StackDiscH 0 (initPlanState 0) vs` holds for ANY `vs`. So the slice applies to something. -/
theorem termRecipeW_jmp_regular_nonvacuous
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel off : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {jmpInst : Instruction} {s : VenomState} {S : List String} {lbl : String}
    (hbb : bb.instructions = [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hnothalt : s.halted = false)
    (hsd : StackDiscH 0 ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hps : ps0 = psOf lbl)
    (hpc : as0.pc < prog.length)
    (hpush : prog.get ⟨as0.pc, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb')
    (hle : wOf lbl + (0 + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (([] : List Instruction).length + (restFuel + 1)) ctx bb s :=
  termRecipeW_jmp_regular (liveness := liveness) (dfg := dfg) (cfg := cfg) (front := [])
    (jmpInst := jmpInst) (hd := jmpInst) (tl := []) (dem := dem) (nextLiveness := nextLiveness)
    (curBbLabel := curBbLabel) (S := S) (sEnd := { s with instIdx := 0 }) (restFuel := restFuel)
    (bb' := bb') (off := off)
    (hbb := hbb) (hjmpop := hjmpop) (hoperands := hoperands) (hcons := rfl)
    (hphi := by rw [hjmpop]; decide) (hnonterm := by intro i hi; cases hi)
    (hthread := by simp [execBodyThread]) (hnothalt := hnothalt)
    (hreg := by simp [RegularBodyH]) (hsd := hsd) (hsv := hsv) (hrel0 := hrel0)
    (hblock := show asmBlockAt prog as0.pc [] from ⟨by simp; omega, by intro j hj; simp at hj⟩)
    (hps := hps) (hpc := hpc) (hpush := hpush) (hoff_lk := hoff_lk) (hoff := hoff)
    (hpc2 := hpc2) (hjump := hjump) (hidx_lk := hidx_lk) (hlk' := hlk') (hle := hle)



set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body JNZ (taken) block** — the branching `_regular` slice. The
    condition is a VARIABLE the body already leaves on the plan stack (`hcondtos`), so no operand
    materialization is needed: the terminator's own asm is just `PUSH ifNz ; JUMPI`. Both facts the recipe
    needs about the asm stack are DERIVED from the body-sim relation rather than assumed — the
    condition-on-top (`venomAsmRel_asmStack_top1_var`) and the condition-dropped successor relation
    (`venomAsmRel_pop_tos`, since only `planStackRel` reads the stacks). Mirrors the older route's
    `termRecipe_jnz_taken_of_regular` into the N-constrained walk shape the driver consumes. -/
theorem termRecipeW_jnz_taken_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel off : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {condvar ifNz ifZ : String} {cond : bytes32}
    {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some cond)
    (hcond_ne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hval : operandVal sEnd lo (Operand.Var condvar) = some cond)
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var condvar])
    (hpsj : psOf ifNz = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with
      stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hp1 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hp1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hp2 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hp2⟩
      = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hw : wOf ifNz + ((executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2)
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hstk_c : as'.stack = cond :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hcondtos hval
  have hsucc : venomAsmRel lo (psOf ifNz) sEnd { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hp1' : as'.pc < prog.length := hpc' ▸ hp1
  have hpush' : prog.get ⟨as'.pc, hp1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer hpc' hpush
  have hp2' : as'.pc + 1 < prog.length := by rw [hpc']; exact hp2
  have hjumpi' : prog.get ⟨as'.pc + 1, hp2'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (congrArg (· + 1) hpc') hjumpi
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hrun,
    termRecipeW_jnz_taken_of_body (condOp := Operand.Var condvar) (ifZ := ifZ) (stk := as'.stack.drop 1)
      hbb hop hoperands hcondv hcond_ne hcons hphi hnonterm hthread hnothalt hw
      hstk_c hp1' hpush' hoff_lk hoff hp2' hjumpi' hidx_lk hsucc hlk'⟩

set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body JNZ (not taken) block** — the fall-through sibling of
    `termRecipeW_jnz_taken_regular`. The condition evaluates to zero, so control reaches `ifZ` via the
    4-op tail (`PUSH ifNz ; JUMPI` falls through, then `PUSH ifZ ; JUMP`) rather than the 2-op taken tail.
    Same derivation: the condition-on-top and the condition-dropped successor relation both come from the
    body-sim relation. With this the JNZ pair is complete for non-empty bodies. -/
theorem termRecipeW_jnz_nottaken_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel offN offZ : Nat} {ctx : VenomContext}
    {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {condvar ifNz ifZ : String} {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some ({ val := 0 } : bytes32))
    (hval : operandVal sEnd lo (Operand.Var condvar) = some (EvmYul.UInt256.ofNat 0))
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var condvar])
    (hpsj : psOf ifZ = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with
      stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hp1 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpushN : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hp1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hp2 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hp2⟩
      = AsmInst.AsmOp "JUMPI")
    (hp3 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 < prog.length)
    (hpushZ : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2, hp3⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hp4 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1
      < prog.length)
    (hjump : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1, hp4⟩
      = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hw : wOf ifZ + ((executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 4)
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hstk_c : as'.stack = EvmYul.UInt256.ofNat 0 :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hcondtos hval
  have hsucc : venomAsmRel lo (psOf ifZ) sEnd { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hp1' : as'.pc < prog.length := hpc' ▸ hp1
  have hpushN' : prog.get ⟨as'.pc, hp1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer hpc' hpushN
  have hp2' : as'.pc + 1 < prog.length := by rw [hpc']; exact hp2
  have hjumpi' : prog.get ⟨as'.pc + 1, hp2'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (congrArg (· + 1) hpc') hjumpi
  have hp3' : as'.pc + 2 < prog.length := by rw [hpc']; exact hp3
  have hpushZ' : prog.get ⟨as'.pc + 2, hp3'⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ) :=
    prog_get_transfer (congrArg (· + 2) hpc') hpushZ
  have hp4' : as'.pc + 2 + 1 < prog.length := by rw [hpc']; exact hp4
  have hjump' : prog.get ⟨as'.pc + 2 + 1, hp4'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (congrArg (· + 2 + 1) hpc') hjump
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hrun,
    termRecipeW_jnz_nottaken_of_body (condOp := Operand.Var condvar) (ifNz := ifNz)
      (stk := as'.stack.drop 1) hbb hop hoperands hcondv hcons hphi hnonterm hthread hnothalt hw
      hstk_c hp1' hpushN' hoffN_lk hoffN hp2' hjumpi' hp3' hpushZ' hoffZ_lk hoffZ hp4' hjump'
      hidxZ_lk hsucc hlk'⟩

set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body DJMP block** — the dynamic-jump case, and the last
    terminator reachable from `RegularBodyH` alone. Like JNZ the selector is a variable the body leaves on
    the plan stack, so the selector-on-top and selector-dropped successor relation are derived from the
    body-sim relation; unlike JNZ the terminator's asm is a scan chain, supplied by `djmp_switch_sim_state`
    (the `pre` list of non-matching entries, the matching entry, and the trampoline). Only the scan/match
    positions are relative to the body-end pc, so they transfer across `hpc'`; the trampoline is absolute.

    With this, every terminator whose operands the BODY materializes has a non-empty-body slice
    (STOP/INVALID/JMP/JNZ×2/DJMP). The remaining three — RETURN/REVERT/SELFDESTRUCT — read their operands
    through the terminator's own emit segment, so their slices belong to the spill-aware `HSVP` layer
    (cf. `termRecipe_{return,revert,selfdestruct}_of_HSVP`), not to this one. -/
theorem termRecipeW_djmp_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {dInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {selvar : String} {idx : bytes32} {base : List Operand}
    {labelOps : List Operand} {labels : List String} {hi : idx.toNat < labels.length}
    {pre : List (List byte × String × Nat)}
    {matb : List byte} {tName lName : String} {matoff idxTramp loff target : Nat}
    (hbb : bb.instructions = front ++ [dInst]) (hop : dInst.opcode = Opcode.DJMP)
    (hoperands : dInst.operands = Operand.Var selvar :: labelOps)
    (hselv : evalOperand (Operand.Var selvar) sEnd = some idx)
    (hlabels : extractLabels labelOps = some labels)
    (hval : operandVal sEnd lo (Operand.Var selvar) = some idx)
    (hcons : front ++ [dInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hseltos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var selvar])
    (hpsj : psOf (labels.get ⟨idx.toNat, hi⟩)
      = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with
          stack := stackPop 1
            (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hpct : pcOf (labels.get ⟨idx.toNat, hi⟩) = target)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog ((as0.pc + (executePlan
            (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * k)
          (pre.get ⟨k, hk⟩).1 (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        idx ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    (hmatch : djmpEntryHere offsets prog ((as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length)
          + 5 * pre.length) matb tName matoff)
    (hsel : idx = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat o2pc matoff = some idxTramp)
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat o2pc loff = some target)
    (hlk : lookupBlock (labels.get ⟨idx.toNat, hi⟩) fn.blocks = some bb')
    (hw : wOf (labels.get ⟨idx.toNat, hi⟩)
        + ((executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
          + (5 * pre.length + 5 + 4)) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hstk_c : as'.stack = idx :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hseltos hval
  have hsucc : venomAsmRel lo (psOf (labels.get ⟨idx.toNat, hi⟩)) sEnd
      { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hdispatch := djmp_switch_sim_state (offsetToPc := o2pc) pre as' hstk_c
    (by intro k hk; rw [hpc']; exact hpre k hk)
    (by rw [hpc']; exact hmatch) hsel hidx_lk ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  rw [← hpct] at hdispatch
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd,
    (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hrun,
    termRecipeW_djmp_of_body (selectorOp := Operand.Var selvar) (labelOps := labelOps) (hi := hi)
      (rest := as'.stack.drop 1) (chainLen := 5 * pre.length + 5 + 4)
      hbb hop hoperands hselv hlabels hcons hphi hnonterm hthread hnothalt hw hdispatch hsucc hlk⟩

/-! ## The emit-segment slices: RETURN / REVERT / SELFDESTRUCT (non-empty body)

The six slices above bottom out in `RegularBodyH` because their terminator's operands are materialized by
the BODY (JNZ/DJMP read a variable the body left on the plan stack; STOP/INVALID/JMP have no value
operands). These three cannot: `generateBlockPlan` folds `generateInstPlan` over the terminator too
(`CodegenPipeline.lean:456`), so a terminator with value operands emits its OWN input-materialization and
the opcode lands AFTER a plan-dependent segment — "the opcode is at `as'.pc`" is not statable.

So they take the spill-aware route instead, mirroring the older `termRecipe_*_of_HSVP` producers: body sim
(`genBlockPrefixBodyHSVP_sim_inv`) THEN the operand emission (`emitInputPlan_{single,pair}_var_sim`),
composed by `runAsm_add_ok`, with the recipe packaged at the POST-EMIT state (operands on top by
`venomAsmRel_asmStack_top{1,2}_var`, terminator at that pc). They halt, so there is no successor-recording
and no var-set threading. Unlike the older producers these do NOT assume the terminator step: the Venom
result is derived from the block's structure by `termRecipeW_*_of_body` (`runBlock_body_*`).

With these, non-empty-body `hsupply` coverage is **8/8** — every codegen terminator. -/

set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body SELFDESTRUCT block** — the single-operand emit-segment slice.
    Body sim then `emitInputPlan_single_var_sim` puts the address on top; the recipe is packaged there. No
    memory-safety segment, hence no M1 FFI axioms. -/
theorem termRecipeW_selfdestruct_HSVP
    {fn : IrFunction} {ctx : VenomContext} {o2pc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {addrv : String} {waddr : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hop : term.opcode = Opcode.SELFDESTRUCT)
    (hoperands : term.operands = [Operand.Var addrv])
    (hevaladdr : evalOperand (Operand.Var addrv) sEnd = some waddr)
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo o2pc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (haddrS : addrv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (haddrM : alookup' M1 (Operand.Var addrv) = none)
    (hliveaddr : nl.contains addrv = true)
    (hvaddr : lookupVar addrv sEnd = some waddr)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (emitInputPlan opc [Operand.Var addrv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var addrv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hw : bodyLen + emitLen + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen'
        (front.length + (extraFuel + 1)) ctx bb vs0 := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have haddrmem := stackPerm_mem hbsv haddrS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d, hdepth, hlen⟩ := stackGetDepth_of_mem haddrmem
  have hsmall : d ≤ 15 := by omega
  have hnospill := alookup_of_spilled_eq hspMF haddrM
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var addrv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc⟩ :=
    emitInputPlan_single_var_sim hnospill hliveaddr hdepth hsmall hbrel hlen hbemit'
  rw [← hemitLenEq] at herun hepc
  have hpeek : stackPeek d (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack = Operand.Var addrv := stackGetDepth_peek hdepth
  have hemitstack : (emitInputPlan opc [Operand.Var addrv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var addrv] := by
    rw [emitInputPlan_single_var_eq hnospill hliveaddr hdepth hsmall hpeek]
  have hval : operandVal sEnd lo (Operand.Var addrv) = some waddr := hvaddr
  have htop : asMid2.stack = waddr :: asMid2.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var herel hemitstack hval
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "SELFDESTRUCT" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hbody : runAsm (bodyLen + emitLen) o2pc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    termRecipeW_selfdestruct_of_body (addrOp := Operand.Var addrv) (addr := waddr)
      (stk := asMid2.stack.drop 1) hbb hop hoperands hevaladdr hcons hphi hnonterm hthread' herel
      hw hpc' hget' htop⟩

set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body RETURN block** — the two-operand emit-segment slice. The
    emit arranges `[sz, off]` so `off` ends on top (`venomAsmRel_asmStack_top2_var`), and the memory-safety
    facts ride along: coverage transfers from `as0` to the post-emit state because the body's asm run only
    grows memory (`runAsm_memory_size_mono`), and `fnEom` is unchanged by the emit
    (`emitInputPlan_pair_var_eq`). -/
theorem termRecipeW_return_HSVP
    {fn : IrFunction} {ctx : VenomContext} {o2pc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hop : term.opcode = Opcode.RETURN)
    (hoperands : term.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo o2pc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hw : bodyLen + emitLen + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen'
        (front.length + (extraFuel + 1)) ctx bb vs0 := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := o2pc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "RETURN" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (by rw [hemem]; exact runAsm_memory_size_mono hbrun))
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hbody : runAsm (bodyLen + emitLen) o2pc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    termRecipeW_return_of_body (offOp := Operand.Var offv) (szOp := Operand.Var szv)
      (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2) hbb hop hoperands hevaloff hevalsz
      hcons hphi hnonterm hthread' herel hw hpc' hget' htop hcov hsafe' hlenu⟩



set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for a NON-EMPTY-body REVERT block** — the aborting twin of the RETURN slice
    (`Abort RevertAbort → AsmRevert`); identical emit segment and memory-safety transfer. -/
theorem termRecipeW_revert_HSVP
    {fn : IrFunction} {ctx : VenomContext} {o2pc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hop : term.opcode = Opcode.REVERT)
    (hoperands : term.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo o2pc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "REVERT")
    (hw : bodyLen + emitLen + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen'
        (front.length + (extraFuel + 1)) ctx bb vs0 := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := o2pc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "REVERT" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (by rw [hemem]; exact runAsm_memory_size_mono hbrun))
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hbody : runAsm (bodyLen + emitLen) o2pc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    termRecipeW_revert_of_body (offOp := Operand.Var offv) (szOp := Operand.Var szv)
      (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2) hbb hop hoperands hevaloff hevalsz
      hcons hphi hnonterm hthread' herel hw hpc' hget' htop hcov hsafe' hlenu⟩

set_option maxHeartbeats 1000000 in
/-- **Non-vacuity of the emit-segment family.** Instantiated at an EMPTY body (`lg = []`) every
    generator-side hypothesis discharges outright: `BodyStepsReadyHSVP … []` is trivially true,
    `totalGain [] = 0`, `execBodyThread [] 0 vs0 = some vs0` (so the body-end state IS the entry state), and
    the HSVP body fold collapses DEFINITIONALLY to `([], ps0)` — leaving `bodyLen = 1` (the SOLabel) and the
    emit segment intact. What remains are the state hypotheses every consumer already carries
    (`StackDiscHS`/`StackPerm`/`venomAsmRel`) plus the emit placement. So the emit-segment slices apply to
    something; their non-vacuity is exhibited here rather than asserted by inheritance. -/
theorem termRecipeW_selfdestruct_HSVP_nonvacuous
    {fn : IrFunction} {ctx : VenomContext} {o2pc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat}
    {bb : BasicBlock} {term : Instruction} {extraFuel : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    {addrv : String} {waddr : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = [term])
    (hop : term.opcode = Opcode.SELFDESTRUCT)
    (hoperands : term.operands = [Operand.Var addrv])
    (hevaladdr : evalOperand (Operand.Var addrv) vs0 = some waddr)
    (hsd0 : StackDiscHS P ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (haddrS : addrv ∈ S0)
    (hspMF : ps0.spilled = M1)
    (haddrM : alookup' M1 (Operand.Var addrv) = none)
    (hliveaddr : nl.contains addrv = true)
    (hvaddr : lookupVar addrv vs0 = some waddr)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (emitInputPlan opc [Operand.Var addrv] nl ps0).1)))
    (hbodyLenEq : bodyLen = 1)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var addrv] nl ps0).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hw : bodyLen + emitLen + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen'
        (([] : List Instruction).length + (extraFuel + 1)) ctx bb vs0 :=
  termRecipeW_selfdestruct_HSVP (P := P) (l := l) (gp := gp) (lg := []) (front := [])
    (S0 := S0) (M0 := M0) (M1 := M1) (ps0 := ps0) (vs0 := vs0) (sEnd := vs0) (as0 := as0)
    (addrv := addrv) (waddr := waddr) (opc := opc) (nl := nl) (bodyLen := bodyLen) (emitLen := emitLen)
    (term := term) (hd := term) (tl := []) (extraFuel := extraFuel)
    (hbb := hbb) (hop := hop) (hoperands := hoperands) (hevaladdr := hevaladdr)
    (hcons := rfl) (hphi := by rw [hop]; decide) (hnonterm := by intro i hi; cases hi)
    (hfront := rfl) (hready := by simp [BodyStepsReadyHSVP])
    (hsd0 := by simpa [totalGain] using hsd0)
    (hsv0 := hsv0) (hspM := hspM) (hrel0 := hrel0)
    (hthread := by simp [execBodyThread]) (hvs0 := hvs0)
    (haddrS := by simpa using haddrS) (hspMF := hspMF) (haddrM := haddrM)
    (hliveaddr := hliveaddr) (hvaddr := hvaddr) (hblock := hblock)
    (hbodyLenEq := by rw [hbodyLenEq]; rfl) (hemitLenEq := hemitLenEq)
    (hlt := hlt) (hget := hget) (hw := hw)

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The shared prologue of every driver-facing non-empty-body slice**: the block's JUMPDEST step
    (`soLabel_sim`) followed by its real body (`genBlockBodyH_sim_inv`), composed by `runAsm_add_ok`, landing
    at the body-end state with the relation at the body fold's plan state and the pc one-past-the-body. Every
    `hsupplyW_regular*` differs only in what it does AFTER this — which `termRecipeW_*_of_body` it feeds and
    which placement facts it transfers — so this is stated once and shared. -/
theorem labelThenBody_simTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {bb : BasicBlock}
    {front : List Instruction} {s sEnd : VenomState} {S Sn : List String}
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1)) :
    ∃ as' : AsmState,
      runAsm (1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length)
          o2pc prog asm = AsmResult.AsmOK as' ∧
      venomAsmRel lo (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 sEnd as' ∧
      as'.pc = asm.pc + 1
        + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps0 { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  rw [hlen1] at hrun1
  have hblock1 : asmBlockAt prog as1.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1) := by
    rw [hpc1']; exact hblock
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyHTo_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S Sn ps0 { s with instIdx := 0 } as1 hready hsd hsv hrel1 hblock1
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  refine ⟨as', ?_, hrel', by rw [hpc', hpc1']⟩
  rw [runAsm_add_ok hrun1]; exact hrun

/-- **The all-growing instance**, unchanged for every existing caller: a `RegularBodyH` is ready at
    the layout the old fold computes, so this is `labelThenBody_simTo` at
    `Sn = S ++ (front.zipIdx 0).flatMap outsOf`. Keeping the signature means the `hsupplyW_regular*`
    slices are untouched. -/
theorem labelThenBody_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {bb : BasicBlock}
    {front : List Instruction} {s sEnd : VenomState} {S : List String}
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1)) :
    ∃ as' : AsmState,
      runAsm (1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length)
          o2pc prog asm = AsmResult.AsmOK as' ∧
      venomAsmRel lo (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 sEnd as' ∧
      as'.pc = asm.pc + 1
        + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length :=
  labelThenBody_simTo (bb := bb) hthread
    (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg))
    hsd hsv hrel hbLabel hblock

/-- **Generic `hsupply` for a NON-EMPTY-body STOP block, from the block's own pc.** The `_regular` slices
    take `as0` already positioned at the body; the driver instead hands over `asm` at the block's LABEL. This
    composes the two: `soLabel_sim` (the JUMPDEST step) then `genBlockBodyH_sim_inv` (the real body), joined
    by `runAsm_add_ok`, and packages the recipe at the body-end via `termRecipeW_stop_of_body`. So
    `codegen_correct_ofBlocks_recipeW`'s per-block obligation is discharged for a STOP block with a REAL
    body, from the pc the driver actually supplies. -/
theorem hsupplyW_regularStopTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hstop : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "STOP")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hst : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "STOP" := prog_get_transfer hpcas hstop
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_stop_of_body hbb hstopop hcons hphi hnonterm hthread hrel' hw hlt hst⟩

/-- **The all-growing instance of the STOP slice**, signature unchanged so every existing caller
    (`codegen_correct_{cvStop,addStop}_recipeW`, …) is untouched. With `hsupplyW_regularStopTo` a
    body containing a CONSUMING step now reaches `TermRecipeW` — the chain
    `bodyStepHTo_commBinopDead → BodyStepsReadyHTo → labelThenBody_simTo → hsupplyW_regularStopTo`
    closes, so consuming bodies are no longer stuck below the driver. -/
theorem hsupplyW_regularStop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hstop : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "STOP")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularStopTo (pcOf := pcOf) (psOf := psOf) (wOf := wOf) (offsets := offsets)
    (restFuel := restFuel) (ctx := ctx) hbb hstopop hcons hphi hnonterm hthread
    (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg))
    hsd hsv hrel hbLabel hblock hpc hstop hw

/-! ### The driver-facing forms: composing the label step onto the `_regular` cores

The `_regular` slices above take `as0` already positioned at the BODY. The driver hands over `asm` at the
block's LABEL (`CanonEntryWH` pins `asm.pc = pcOf s.currentBb`, and a block's plan opens with `SOLabel`), so
a `_regular` core alone cannot discharge `codegen_correct_ofBlocks_recipeW`'s obligation — the label step has
to be composed on. (The `_HSVP` three need no such wrapper: their plan already carries `[SOLabel l] ++ …`.)

Each of these is `soLabel_sim` (the JUMPDEST step) ∘ `genBlockBodyH_sim_inv` (the real body), joined by
`runAsm_add_ok`, packaged through the matching `termRecipeW_*_of_body`; the branching ones additionally
derive operand-on-top and the operand-dropped successor relation from the body-end relation. With
`hsupplyW_regularStop` these complete the driver-facing non-empty-body forms for all eight terminators. -/

set_option maxHeartbeats 1000000 in
/-- Non-empty-body INVALID block, from the block's own pc. -/
theorem hsupplyW_regularInvalidTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hinv : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "INVALID")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hiv : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "INVALID" := prog_get_transfer hpcas hinv
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_invalid_of_body hbb hinvop hcons hphi hnonterm hthread hrel' hw hlt hiv⟩

theorem hsupplyW_regularInvalid
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hinv : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "INVALID")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularInvalidTo hbb hinvop hcons hphi hnonterm hthread (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg)) hsd hsv hrel hbLabel hblock hpc hinv hw
set_option maxHeartbeats 1000000 in
/-- Non-empty-body JMP block, from the block's own pc. -/
theorem hsupplyW_regularJmpTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem off : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction} {lbl : String}
    {s sEnd : VenomState} {S Sn : List String}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 = psOf lbl)
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩
      = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb')
    (hw : wOf lbl + ((1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hp : prog.get ⟨as'.pc, hlt⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl) :=
    prog_get_transfer hpcas hpush
  have hlt2 : as'.pc + 1 < prog.length := by rw [hpcas]; exact hpc2
  have hj : prog.get ⟨as'.pc + 1, hlt2⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (congrArg (· + 1) hpcas) hjump
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_jmp_of_body (bb' := bb') hbb hjmpop hoperands hcons hphi hnonterm hthread hnothalt
      hrel' hps hw hlt hp hoff_lk hoff hlt2 hj hidx_lk hlk'⟩

theorem hsupplyW_regularJmp
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem off : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction} {lbl : String}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 = psOf lbl)
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩
      = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb')
    (hw : wOf lbl + ((1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularJmpTo hbb hjmpop hoperands hcons hphi hnonterm hthread hnothalt (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg)) hsd hsv hrel hbLabel hblock hps hpc hpush hoff_lk hoff hpc2 hjump hidx_lk hlk' hw
set_option maxHeartbeats 1000000 in
/-- Non-empty-body JNZ (taken) block, from the block's own pc. -/
theorem hsupplyW_regularJnzTakenTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem off : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String} {condvar ifNz ifZ : String} {cond : bytes32}
    {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some cond)
    (hcond_ne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hval : operandVal sEnd lo (Operand.Var condvar) = some cond)
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var condvar])
    (hpsj : psOf ifNz = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hpc : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hw : wOf ifNz + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hstk_c : as'.stack = cond :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hcondtos hval
  have hsucc : venomAsmRel lo (psOf ifNz) sEnd { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hp : prog.get ⟨as'.pc, hlt⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer hpcas hpush
  have hlt2 : as'.pc + 1 < prog.length := by rw [hpcas]; exact hpc2
  have hji : prog.get ⟨as'.pc + 1, hlt2⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (congrArg (· + 1) hpcas) hjumpi
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hbody,
    termRecipeW_jnz_taken_of_body (condOp := Operand.Var condvar) (ifZ := ifZ)
      (stk := as'.stack.drop 1) hbb hop hoperands hcondv hcond_ne hcons hphi hnonterm hthread
      hnothalt hw hstk_c hlt hp hoff_lk hoff hlt2 hji hidx_lk hsucc hlk'⟩

theorem hsupplyW_regularJnzTaken
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem off : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {condvar ifNz ifZ : String} {cond : bytes32}
    {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some cond)
    (hcond_ne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hval : operandVal sEnd lo (Operand.Var condvar) = some cond)
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var condvar])
    (hpsj : psOf ifNz = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hpc : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hw : wOf ifNz + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 2) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularJnzTakenTo hbb hop hoperands hcondv hcond_ne hval hcons hphi hnonterm hthread hnothalt (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg)) hsd hsv hrel hbLabel hblock hcondtos hpsj hpc hpush hoff_lk hoff hpc2 hjumpi hidx_lk hlk' hw
set_option maxHeartbeats 1000000 in
/-- Non-empty-body JNZ (not taken) block, from the block's own pc. -/
theorem hsupplyW_regularJnzNottakenTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem offN offZ : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String} {condvar ifNz ifZ : String} {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some ({ val := 0 } : bytes32))
    (hval : operandVal sEnd lo (Operand.Var condvar) = some (EvmYul.UInt256.ofNat 0))
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var condvar])
    (hpsj : psOf ifZ = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hpc : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpushN : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI")
    (hpc3 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 < prog.length)
    (hpushZ : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2, hpc3⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc4 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1, hpc4⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hw : wOf ifZ + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 4) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hstk_c : as'.stack = EvmYul.UInt256.ofNat 0 :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hcondtos hval
  have hsucc : venomAsmRel lo (psOf ifZ) sEnd { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hpN : prog.get ⟨as'.pc, hlt⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer hpcas hpushN
  have hlt2 : as'.pc + 1 < prog.length := by rw [hpcas]; exact hpc2
  have hji : prog.get ⟨as'.pc + 1, hlt2⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (congrArg (· + 1) hpcas) hjumpi
  have hlt3 : as'.pc + 2 < prog.length := by rw [hpcas]; exact hpc3
  have hpZ : prog.get ⟨as'.pc + 2, hlt3⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ) :=
    prog_get_transfer (congrArg (· + 2) hpcas) hpushZ
  have hlt4 : as'.pc + 2 + 1 < prog.length := by rw [hpcas]; exact hpc4
  have hj : prog.get ⟨as'.pc + 2 + 1, hlt4⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (congrArg (· + 2 + 1) hpcas) hjump
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hbody,
    termRecipeW_jnz_nottaken_of_body (condOp := Operand.Var condvar) (ifNz := ifNz)
      (stk := as'.stack.drop 1) hbb hop hoperands hcondv hcons hphi hnonterm hthread hnothalt hw
      hstk_c hlt hpN hoffN_lk hoffN hlt2 hji hlt3 hpZ hoffZ_lk hoffZ hlt4 hj hidxZ_lk hsucc hlk'⟩

theorem hsupplyW_regularJnzNottaken
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem offN offZ : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {condvar ifNz ifZ : String} {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some ({ val := 0 } : bytes32))
    (hval : operandVal sEnd lo (Operand.Var condvar) = some (EvmYul.UInt256.ofNat 0))
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hcondtos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var condvar])
    (hpsj : psOf ifZ = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack })
    (hpc : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpushN : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hpc2 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI")
    (hpc3 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 < prog.length)
    (hpushZ : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2, hpc3⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc4 : asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1, hpc4⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hw : wOf ifZ + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 4) ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularJnzNottakenTo hbb hop hoperands hcondv hval hcons hphi hnonterm hthread hnothalt (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg)) hsd hsv hrel hbLabel hblock hcondtos hpsj hpc hpushN hoffN_lk hoffN hpc2 hjumpi hpc3 hpushZ hoffZ_lk hoffZ hpc4 hjump hidxZ_lk hlk' hw
set_option maxHeartbeats 1000000 in
/-- Non-empty-body DJMP block, from the block's own pc. -/
theorem hsupplyW_regularDjmpTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {dInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String} {selvar : String} {idx : bytes32}
    {base : List Operand} {labelOps : List Operand} {labels : List String}
    {hi : idx.toNat < labels.length}
    {pre : List (List byte × String × Nat)}
    {matb : List byte} {tName lName : String} {matoff idxTramp loff target lc : Nat}
    (hbb : bb.instructions = front ++ [dInst]) (hop : dInst.opcode = Opcode.DJMP)
    (hoperands : dInst.operands = Operand.Var selvar :: labelOps)
    (hselv : evalOperand (Operand.Var selvar) sEnd = some idx)
    (hlabels : extractLabels labelOps = some labels)
    (hval : operandVal sEnd lo (Operand.Var selvar) = some idx)
    (hcons : front ++ [dInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hseltos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var selvar])
    (hpsj : psOf (labels.get ⟨idx.toNat, hi⟩) = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack, labelCounter := lc })
    (hpct : pcOf (labels.get ⟨idx.toNat, hi⟩) = target)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog ((asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * k)
          (pre.get ⟨k, hk⟩).1 (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        idx ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    (hmatch : djmpEntryHere offsets prog ((asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * pre.length) matb tName matoff)
    (hsel : idx = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat o2pc matoff = some idxTramp)
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat o2pc loff = some target)
    (hlk : lookupBlock (labels.get ⟨idx.toNat, hi⟩) fn.blocks = some bb')
    (hw : wOf (labels.get ⟨idx.toNat, hi⟩) + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + (5 * pre.length + 5 + 4))
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hstk_c : as'.stack = idx :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hseltos hval
  have hsucc : venomAsmRel lo (psOf (labels.get ⟨idx.toNat, hi⟩)) sEnd
      { as' with stack := as'.stack.drop 1 } := by
    rw [hpsj]; exact venomAsmRel_pop_tos hrel' hstk_c
  have hdispatch := djmp_switch_sim_state (offsetToPc := o2pc) pre as' hstk_c
    (by intro k hk; rw [hpcas]; exact hpre k hk)
    (by rw [hpcas]; exact hmatch) hsel hidx_lk ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  rw [← hpct] at hdispatch
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hbody,
    termRecipeW_djmp_of_body (selectorOp := Operand.Var selvar) (labelOps := labelOps) (hi := hi)
      (rest := as'.stack.drop 1) (chainLen := 5 * pre.length + 5 + 4)
      hbb hop hoperands hselv hlabels hcons hphi hnonterm hthread hnothalt hw hdispatch hsucc hlk⟩

theorem hsupplyW_regularDjmp
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {dInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {selvar : String} {idx : bytes32}
    {base : List Operand} {labelOps : List Operand} {labels : List String}
    {hi : idx.toNat < labels.length}
    {pre : List (List byte × String × Nat)}
    {matb : List byte} {tName lName : String} {matoff idxTramp loff target lc : Nat}
    (hbb : bb.instructions = front ++ [dInst]) (hop : dInst.opcode = Opcode.DJMP)
    (hoperands : dInst.operands = Operand.Var selvar :: labelOps)
    (hselv : evalOperand (Operand.Var selvar) sEnd = some idx)
    (hlabels : extractLabels labelOps = some labels)
    (hval : operandVal sEnd lo (Operand.Var selvar) = some idx)
    (hcons : front ++ [dInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1) (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hseltos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack = base ++ [Operand.Var selvar])
    (hpsj : psOf (labels.get ⟨idx.toNat, hi⟩) = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack, labelCounter := lc })
    (hpct : pcOf (labels.get ⟨idx.toNat, hi⟩) = target)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog ((asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * k)
          (pre.get ⟨k, hk⟩).1 (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        idx ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    (hmatch : djmpEntryHere offsets prog ((asm.pc + 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * pre.length) matb tName matoff)
    (hsel : idx = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat o2pc matoff = some idxTramp)
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat o2pc loff = some target)
    (hlk : lookupBlock (labels.get ⟨idx.toNat, hi⟩) fn.blocks = some bb')
    (hw : wOf (labels.get ⟨idx.toNat, hi⟩) + ((1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + (5 * pre.length + 5 + 4))
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularDjmpTo hbb hop hoperands hselv hlabels hval hcons hphi hnonterm hthread hnothalt (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg)) hsd hsv hrel hbLabel hblock hseltos hpsj hpct hpre hmatch hsel hidx_lk ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk hlk hw
set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for an empty-body SELFDESTRUCT whose operand is DEAD** — i.e. already on the
    plan stack and consumed in place, which is what the real generator emits at a terminator
    (`nextLive = []` there, so `emitInputPlan` produces NO ops — no DUP). The emit-segment slices
    (`termRecipeW_selfdestruct_HSVP` et al.) go through `emitInputPlan_single_var_sim`, whose
    `hliveaddr : nl.contains addrv = true` forces the *live* (DUP) variant, so they cannot be applied to a
    real halting block. Here the block's whole asm is `[JUMPDEST ; SELFDESTRUCT]`: the SOLabel step, then the
    operand is already on top (derived from the entry relation via `venomAsmRel_asmStack_top1_var`). -/
theorem hsupplyW_emptySelfdestructDead {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {sdInst : Instruction}
    {addrv : String} {waddr : bytes32} {base : List Operand}
    (hbb : bb.instructions = [sdInst]) (hop : sdInst.opcode = Opcode.SELFDESTRUCT)
    (hoperands : sdInst.operands = [Operand.Var addrv])
    (heval : evalOperand (Operand.Var addrv) { s with instIdx := 0 } = some waddr)
    (hval : operandVal { s with instIdx := 0 } lo (Operand.Var addrv) = some waddr)
    (hstack : ps.stack = base ++ [Operand.Var addrv])
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hsdpc : asm.pc + 1 < prog.length)
    (hsd : prog.get ⟨asm.pc + 1, hsdpc⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hw : 1 + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt : as1.pc < prog.length := by rw [hpc1']; exact hsdpc
  have hst : prog.get ⟨as1.pc, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT" := by
    conv_lhs => rw [show (⟨as1.pc, hlt⟩ : Fin _) = ⟨asm.pc + 1, hsdpc⟩ from Fin.ext hpc1']
    exact hsd
  have htop : as1.stack = waddr :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel1 hstack hval
  rw [hlen1] at hrun1
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_selfdestruct_of_body (front := []) (sdInst := sdInst) (hd := sdInst) (tl := [])
    (restFuel := k) (addrOp := Operand.Var addrv) (addr := waddr) (stk := as1.stack.drop 1)
    (by simpa using hbb) hop hoperands heval (by simp) (by rw [hop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel1 hw hlt hst htop

set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for an empty-body RETURN whose operands are DEAD** — the two-operand sibling of
    `hsupplyW_emptySelfdestructDead`, and the piece that completes the dead-operand family. At a real
    terminator `nextLive = []`, so `emitInputPlan` emits NOTHING and the operands must already sit on the plan
    stack in terminator order (`hstack` — `szv` then `offv`, so `offv` ends on top). The `_HSVP` slices cannot
    serve this case: their `hliveoff`/`hliveszv` force the live (DUP) variant. Memory coverage is stated about
    the ENTRY asm state and transferred across the JUMPDEST step by `runAsm_memory_size_mono` (an asm run only
    grows memory); `fnEom` is untouched by the label step. -/
theorem hsupplyW_emptyReturnDead {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {tInst : Instruction}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = [tInst]) (hop : tInst.opcode = Opcode.RETURN)
    (hoperands : tInst.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) { s with instIdx := 0 } = some woff)
    (hevalsz : evalOperand (Operand.Var szv) { s with instIdx := 0 } = some wsz)
    (hvoff : operandVal { s with instIdx := 0 } lo (Operand.Var offv) = some woff)
    (hvsz : operandVal { s with instIdx := 0 } lo (Operand.Var szv) = some wsz)
    (hstack : ps.stack = base ++ [Operand.Var szv, Operand.Var offv])
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (htpc : asm.pc + 1 < prog.length)
    (hget : prog.get ⟨asm.pc + 1, htpc⟩ = AsmInst.AsmOp "RETURN")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat ≤ ps.alloc.fnEom) (hlenu : wsz.toNat < USize.size)
    (hw : 1 + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt : as1.pc < prog.length := by rw [hpc1']; exact htpc
  have hst : prog.get ⟨as1.pc, hlt⟩ = AsmInst.AsmOp "RETURN" := by
    conv_lhs => rw [show (⟨as1.pc, hlt⟩ : Fin _) = ⟨asm.pc + 1, htpc⟩ from Fin.ext hpc1']
    exact hget
  have htop : as1.stack = woff :: wsz :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel1 hstack hvoff hvsz
  rw [hlen1] at hrun1
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as1.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hrun1))
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_return_of_body (front := []) (retInst := tInst) (hd := tInst) (tl := [])
    (restFuel := k) (offOp := Operand.Var offv) (szOp := Operand.Var szv) (off := woff) (sz := wsz)
    (rest := as1.stack.drop 2)
    (by simpa using hbb) hop hoperands hevaloff hevalsz (by simp) (by rw [hop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel1 hw hlt hst htop hcov hbelow hlenu



set_option maxHeartbeats 1000000 in
/-- **Generic `hsupply` for an empty-body REVERT whose operands are DEAD** — the two-operand sibling of
    `hsupplyW_emptySelfdestructDead`, and the piece that completes the dead-operand family. At a real
    terminator `nextLive = []`, so `emitInputPlan` emits NOTHING and the operands must already sit on the plan
    stack in terminator order (`hstack` — `szv` then `offv`, so `offv` ends on top). The `_HSVP` slices cannot
    serve this case: their `hliveoff`/`hliveszv` force the live (DUP) variant. Memory coverage is stated about
    the ENTRY asm state and transferred across the JUMPDEST step by `runAsm_memory_size_mono` (an asm run only
    grows memory); `fnEom` is untouched by the label step. -/
theorem hsupplyW_emptyRevertDead {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps : PlanState} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {tInst : Instruction}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = [tInst]) (hop : tInst.opcode = Opcode.REVERT)
    (hoperands : tInst.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) { s with instIdx := 0 } = some woff)
    (hevalsz : evalOperand (Operand.Var szv) { s with instIdx := 0 } = some wsz)
    (hvoff : operandVal { s with instIdx := 0 } lo (Operand.Var offv) = some woff)
    (hvsz : operandVal { s with instIdx := 0 } lo (Operand.Var szv) = some wsz)
    (hstack : ps.stack = base ++ [Operand.Var szv, Operand.Var offv])
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (htpc : asm.pc + 1 < prog.length)
    (hget : prog.get ⟨asm.pc + 1, htpc⟩ = AsmInst.AsmOp "REVERT")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat ≤ ps.alloc.fnEom) (hlenu : wsz.toNat < USize.size)
    (hw : 1 + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  have hlt : as1.pc < prog.length := by rw [hpc1']; exact htpc
  have hst : prog.get ⟨as1.pc, hlt⟩ = AsmInst.AsmOp "REVERT" := by
    conv_lhs => rw [show (⟨as1.pc, hlt⟩ : Fin _) = ⟨asm.pc + 1, htpc⟩ from Fin.ext hpc1']
    exact hget
  have htop : as1.stack = woff :: wsz :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel1 hstack hvoff hvsz
  rw [hlen1] at hrun1
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as1.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hrun1))
  refine ⟨as1, ps, { s with instIdx := 0 }, 1, hrun1, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_revert_of_body (front := []) (revInst := tInst) (hd := tInst) (tl := [])
    (restFuel := k) (offOp := Operand.Var offv) (szOp := Operand.Var szv) (off := woff) (sz := wsz)
    (rest := as1.stack.drop 2)
    (by simpa using hbb) hop hoperands hevaloff hevalsz (by simp) (by rw [hop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel1 hw hlt hst htop hcov hbelow hlenu



/-- **The non-empty-body RETURN slice** (`hsupplyW_regularReturnTo`). Fills the gap the `_To` lift left
    open: `hsupplyW_emptyReturnReorder` covers a RETURN with an *empty* body (its operands positioned by a
    reorder), and the six `hsupplyW_regular*To` cover non-empty bodies under *non-halting / operand-free*
    terminators (STOP, JMP, …). Neither covers a non-empty body that *ends in RETURN*. This one does, for
    the reorder-free case the generator actually emits when the RETURN operands are already positioned
    (measured: `%a=CV; %b=CV; RETURN %b %a` ⟹ `[L, CALLVALUE, CALLVALUE, RETURN]`, no SWAP).

    Composition mirrors `hsupplyW_regularStopTo` but swaps the terminal: `labelThenBody_simTo` runs
    `[SOLabel] ++ bodyPlan`, landing at `as'` related to the body-end plan state `bodyPlan.2`; the caller
    pins that state's top two slots (`hps'stack`), so `venomAsmRel_asmStack_top2_var` delivers the recipe's
    `off :: sz :: rest` stack fact, and `termRecipeW_return_of_body` closes. Memory coverage is stated about
    the ENTRY asm state and carried across the composed run by `runAsm_memory_size_mono`, exactly as the
    empty-body slice does. RETURN operands are evaluated at the body-END state `sEnd`. -/
theorem hsupplyW_regularReturnTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {retInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RETURN)
    (hoperands : retInst.operands = [Operand.Var offv, Operand.Var szv])
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hvoff : operandVal sEnd lo (Operand.Var offv) = some woff)
    (hvsz : operandVal sEnd lo (Operand.Var szv) = some wsz)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var szv, Operand.Var offv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hret : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "RETURN")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat
      ≤ (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hst : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "RETURN" := prog_get_transfer hpcas hret
  have htop : as'.stack = woff :: wsz :: as'.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel' hps'stack hvoff hvsz
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as'.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hbody))
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_return_of_body (front := front) (retInst := retInst) (hd := hd) (tl := tl)
      (restFuel := restFuel) (offOp := Operand.Var offv) (szOp := Operand.Var szv)
      (off := woff) (sz := wsz) (rest := as'.stack.drop 2)
      hbb hop hoperands hevaloff hevalsz hcons hphi hnonterm hthread hrel' hw hlt hst htop hcov hbelow hlenu⟩

/-- **`RegularBodyH`-facing form of `hsupplyW_regularReturnTo`** (same relation to it as `hsupplyW_regularStop`
    has to `…StopTo`): the growing all-`RegularBodyH` body ready at the layout the fold computes, so the
    caller supplies a `RegularBodyH` for the body instead of a hand-built `BodyStepsReadyHTo`. The `hps'stack`
    obligation (the body-end plan stack's top two = `[szv, offv]`) stays — it is what a RETURN needs beyond a
    STOP, and it cannot be read off a `RegularBodyH` generically. -/
theorem hsupplyW_regularReturn
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {retInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RETURN)
    (hoperands : retInst.operands = [Operand.Var offv, Operand.Var szv])
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hvoff : operandVal sEnd lo (Operand.Var offv) = some woff)
    (hvsz : operandVal sEnd lo (Operand.Var szv) = some wsz)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var szv, Operand.Var offv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hret : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "RETURN")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat
      ≤ (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularReturnTo (pcOf := pcOf) (psOf := psOf) (wOf := wOf) (offsets := offsets)
    (restFuel := restFuel) (ctx := ctx) (base := base)
    hbb hop hoperands hcons hphi hnonterm hthread hevaloff hevalsz hvoff hvsz
    (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg))
    hsd hsv hrel hbLabel hblock hps'stack hpc hret hcov0 hbelow hlenu hw

/-- **The REVERT twin of `hsupplyW_regularReturnTo`** — the aborting sibling: same composition
    (`labelThenBody_simTo` → `termRecipeW_revert_of_body`, `venomAsmRel_asmStack_top2_var` for the stack
    fact), `AsmRevert` instead of `AsmHalt`. With this, both operand-carrying halting terminators that the
    generator can leave reorder-free have a non-empty-body slice (matching the empty-body pair
    `hsupplyW_empty{Return,Revert}Reorder`). -/
theorem hsupplyW_regularRevertTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {revInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [revInst]) (hop : revInst.opcode = Opcode.REVERT)
    (hoperands : revInst.operands = [Operand.Var offv, Operand.Var szv])
    (hcons : front ++ [revInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hvoff : operandVal sEnd lo (Operand.Var offv) = some woff)
    (hvsz : operandVal sEnd lo (Operand.Var szv) = some wsz)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var szv, Operand.Var offv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hrev : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "REVERT")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat
      ≤ (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hst : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "REVERT" := prog_get_transfer hpcas hrev
  have htop : as'.stack = woff :: wsz :: as'.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel' hps'stack hvoff hvsz
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as'.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hbody))
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_revert_of_body (front := front) (revInst := revInst) (hd := hd) (tl := tl)
      (restFuel := restFuel) (offOp := Operand.Var offv) (szOp := Operand.Var szv)
      (off := woff) (sz := wsz) (rest := as'.stack.drop 2)
      hbb hop hoperands hevaloff hevalsz hcons hphi hnonterm hthread hrel' hw hlt hst htop hcov hbelow hlenu⟩

/-- **`RegularBodyH`-facing form of `hsupplyW_regularRevertTo`** — the REVERT twin of `hsupplyW_regularReturn`. -/
theorem hsupplyW_regularRevert
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {revInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    {offv szv : String} {woff wsz : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [revInst]) (hop : revInst.opcode = Opcode.REVERT)
    (hoperands : revInst.operands = [Operand.Var offv, Operand.Var szv])
    (hcons : front ++ [revInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hevaloff : evalOperand (Operand.Var offv) sEnd = some woff)
    (hevalsz : evalOperand (Operand.Var szv) sEnd = some wsz)
    (hvoff : operandVal sEnd lo (Operand.Var offv) = some woff)
    (hvsz : operandVal sEnd lo (Operand.Var szv) = some wsz)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var szv, Operand.Var offv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hrev : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "REVERT")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat
      ≤ (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularRevertTo (pcOf := pcOf) (psOf := psOf) (wOf := wOf) (offsets := offsets)
    (restFuel := restFuel) (ctx := ctx) (base := base)
    hbb hop hoperands hcons hphi hnonterm hthread hevaloff hevalsz hvoff hvsz
    (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg))
    hsd hsv hrel hbLabel hblock hps'stack hpc hrev hcov0 hbelow hlenu hw

/-- **The SELFDESTRUCT non-empty-body slice** (`hsupplyW_regularSelfdestructTo`). The one-operand cousin of
    `hsupplyW_regularReturnTo`: a body-then-SELFDESTRUCT block. SELFDESTRUCT takes a single address operand and
    has NO memory window, so this is the *simplest* of the three — `labelThenBody_simTo` →
    `venomAsmRel_asmStack_top1_var` (the address on top) → `termRecipeW_selfdestruct_of_body`, with no
    coverage/below/len obligations. With this, EVERY halting terminator the recipe route models
    (STOP/INVALID/RETURN/REVERT/SELFDESTRUCT) has a non-empty-body slice. -/
theorem hsupplyW_regularSelfdestructTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {sdInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    {addrv : String} {waddr : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [sdInst]) (hop : sdInst.opcode = Opcode.SELFDESTRUCT)
    (hoperands : sdInst.operands = [Operand.Var addrv])
    (hcons : front ++ [sdInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (heval : evalOperand (Operand.Var addrv) sEnd = some waddr)
    (hval : operandVal sEnd lo (Operand.Var addrv) = some waddr)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var addrv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hsdop : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "SELFDESTRUCT")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hst : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT" := prog_get_transfer hpcas hsdop
  have htop : as'.stack = waddr :: as'.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrel' hps'stack hval
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_selfdestruct_of_body (front := front) (sdInst := sdInst) (hd := hd) (tl := tl)
      (restFuel := restFuel) (addrOp := Operand.Var addrv) (addr := waddr) (stk := as'.stack.drop 1)
      hbb hop hoperands heval hcons hphi hnonterm hthread hrel' hw hlt hst htop⟩

/-- **`RegularBodyH`-facing form of `hsupplyW_regularSelfdestructTo`.** -/
theorem hsupplyW_regularSelfdestruct
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {sdInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    {addrv : String} {waddr : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [sdInst]) (hop : sdInst.opcode = Opcode.SELFDESTRUCT)
    (hoperands : sdInst.operands = [Operand.Var addrv])
    (hcons : front ++ [sdInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (heval : evalOperand (Operand.Var addrv) sEnd = some waddr)
    (hval : operandVal sEnd lo (Operand.Var addrv) = some waddr)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hps'stack : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var addrv])
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hsdop : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "SELFDESTRUCT")
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s :=
  hsupplyW_regularSelfdestructTo (pcOf := pcOf) (psOf := psOf) (wOf := wOf) (offsets := offsets)
    (restFuel := restFuel) (ctx := ctx) (base := base)
    hbb hop hoperands hcons hphi hnonterm hthread heval hval
    (bodyStepsReadyHTo_of_bodyStepsReadyH _ _
      (bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
        (curBbLabel := curBbLabel) front S 0 hreg))
    hsd hsv hrel hbLabel hblock hps'stack hpc hsdop hw

set_option maxHeartbeats 1000000 in
/-- **The first REORDER-aware slice.** Fact 7 says this family covers reorder-free blocks because no slice
    models `reorderOps`. This one does: an empty-body RETURN whose terminator segment is a REORDER, composed
    as `soLabel_sim` (the JUMPDEST) → `reorderPlan_sim` (`PlanSim.lean:1663`, the reorder, its per-operand
    residual `hstep` supplied by the caller from `reorderOne_sim_{swap,positioned}`) →
    `termRecipeW_return_of_body`, joined by `runAsm_add_ok`. After the reorder the operands are positioned
    (`hstack'`), so the emit is empty and `venomAsmRel_asmStack_top2_var` gives the recipe its stack fact.
    Memory coverage is stated about the ENTRY asm state and transferred across the whole composed run by
    `runAsm_memory_size_mono`. This is the shape fact 7 named as the one extension left:
    `[SOLabel] ++ reorderOps ++ emitOps` rather than `[SOLabel] ++ emitOps`. -/
theorem hsupplyW_emptyReturnReorder {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps ps' : PlanState} {rops : List StackOp} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {tInst : Instruction}
    {offv szv : String} {woff wsz : bytes32} {base perm : List Operand}
    (hbb : bb.instructions = [tInst]) (hop : tInst.opcode = Opcode.RETURN)
    (hoperands : tInst.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) { s with instIdx := 0 } = some woff)
    (hevalsz : evalOperand (Operand.Var szv) { s with instIdx := 0 } = some wsz)
    (hvoff : operandVal { s with instIdx := 0 } lo (Operand.Var offv) = some woff)
    (hvsz : operandVal { s with instIdx := 0 } lo (Operand.Var szv) = some wsz)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    -- the terminator's REORDER segment, on the bounded reachable-state route (no ∀-p `hstep`)
    (hperm : List.Perm perm [Operand.Var szv, Operand.Var offv])
    (hpsstk : ps.stack = base ++ perm)
    (hbound : (base ++ perm).length ≤ 17)
    (hnospill : ∀ o, alookup' ps.spilled o = none)
    (hreorder : reorderPlan [Operand.Var szv, Operand.Var offv] ps = (rops, ps'))
    (hblockR : asmBlockAt prog (asm.pc + 1) (executePlan rops))
    (hpc : asm.pc + 1 + (executePlan rops).length < prog.length)
    (hget : prog.get ⟨asm.pc + 1 + (executePlan rops).length, hpc⟩ = AsmInst.AsmOp "RETURN")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat ≤ ps'.alloc.fnEom) (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan rops).length + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps'' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps'' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  rw [hlen1] at hrun1
  have hblockR1 : asmBlockAt prog as1.pc (executePlan rops) := by rw [hpc1']; exact hblockR
  obtain ⟨as2, hrun2, hrel2, hstack2, hpc2⟩ :=
    reorderPlan_join_bounded (offsetToPc := o2pc) hperm hpsstk hbound hnospill hreorder hrel1 hblockR1
  have hpc2' : as2.pc = asm.pc + 1 + (executePlan rops).length := by rw [hpc2, hpc1']
  have hlt : as2.pc < prog.length := by rw [hpc2']; exact hpc
  have hst : prog.get ⟨as2.pc, hlt⟩ = AsmInst.AsmOp "RETURN" := prog_get_transfer hpc2' hget
  have htop : as2.stack = woff :: wsz :: as2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel2 hstack2 hvoff hvsz
  have hbody : runAsm (1 + (executePlan rops).length) o2pc prog asm = AsmResult.AsmOK as2 := by
    rw [runAsm_add_ok hrun1]; exact hrun2
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hbody))
  refine ⟨as2, ps', { s with instIdx := 0 }, 1 + (executePlan rops).length, hbody, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_return_of_body (front := []) (retInst := tInst) (hd := tInst) (tl := [])
    (restFuel := k) (offOp := Operand.Var offv) (szOp := Operand.Var szv) (off := woff) (sz := wsz)
    (rest := as2.stack.drop 2)
    (by simpa using hbb) hop hoperands hevaloff hevalsz (by simp) (by rw [hop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel2 hw hlt hst htop hcov hbelow hlenu

set_option maxHeartbeats 1000000 in
/-- **The REVERT twin of `hsupplyW_emptyReturnReorder`** — same composition
    (`soLabel_sim` → `reorderPlan_sim` → `termRecipeW_revert_of_body`), `AsmRevert` instead of `AsmHalt`.
    With this, both operand-carrying halting terminators that the generator reorders are covered. -/
theorem hsupplyW_emptyRevertReorder {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {asm : AsmState} {ps ps' : PlanState} {rops : List StackOp} {k : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {tInst : Instruction}
    {offv szv : String} {woff wsz : bytes32} {base perm : List Operand}
    (hbb : bb.instructions = [tInst]) (hop : tInst.opcode = Opcode.REVERT)
    (hoperands : tInst.operands = [Operand.Var offv, Operand.Var szv])
    (hevaloff : evalOperand (Operand.Var offv) { s with instIdx := 0 } = some woff)
    (hevalsz : evalOperand (Operand.Var szv) { s with instIdx := 0 } = some wsz)
    (hvoff : operandVal { s with instIdx := 0 } lo (Operand.Var offv) = some woff)
    (hvsz : operandVal { s with instIdx := 0 } lo (Operand.Var szv) = some wsz)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    -- the terminator's REORDER segment, on the bounded reachable-state route (no ∀-p `hstep`)
    (hperm : List.Perm perm [Operand.Var szv, Operand.Var offv])
    (hpsstk : ps.stack = base ++ perm)
    (hbound : (base ++ perm).length ≤ 17)
    (hnospill : ∀ o, alookup' ps.spilled o = none)
    (hreorder : reorderPlan [Operand.Var szv, Operand.Var offv] ps = (rops, ps'))
    (hblockR : asmBlockAt prog (asm.pc + 1) (executePlan rops))
    (hpc : asm.pc + 1 + (executePlan rops).length < prog.length)
    (hget : prog.get ⟨asm.pc + 1 + (executePlan rops).length, hpc⟩ = AsmInst.AsmOp "REVERT")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat ≤ ps'.alloc.fnEom) (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan rops).length + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps'' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps'' vs' bodyLen (k + 1) ctx bb s := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  rw [hlen1] at hrun1
  have hblockR1 : asmBlockAt prog as1.pc (executePlan rops) := by rw [hpc1']; exact hblockR
  obtain ⟨as2, hrun2, hrel2, hstack2, hpc2⟩ :=
    reorderPlan_join_bounded (offsetToPc := o2pc) hperm hpsstk hbound hnospill hreorder hrel1 hblockR1
  have hpc2' : as2.pc = asm.pc + 1 + (executePlan rops).length := by rw [hpc2, hpc1']
  have hlt : as2.pc < prog.length := by rw [hpc2']; exact hpc
  have hst : prog.get ⟨as2.pc, hlt⟩ = AsmInst.AsmOp "REVERT" := prog_get_transfer hpc2' hget
  have htop : as2.stack = woff :: wsz :: as2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel2 hstack2 hvoff hvsz
  have hbody : runAsm (1 + (executePlan rops).length) o2pc prog asm = AsmResult.AsmOK as2 := by
    rw [runAsm_add_ok hrun1]; exact hrun2
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (runAsm_memory_size_mono hbody))
  refine ⟨as2, ps', { s with instIdx := 0 }, 1 + (executePlan rops).length, hbody, ?_⟩
  have hfuel : k + 1 = ([] : List Instruction).length + (k + 1) := by simp
  rw [hfuel]
  exact termRecipeW_revert_of_body (front := []) (revInst := tInst) (hd := tInst) (tl := [])
    (restFuel := k) (offOp := Operand.Var offv) (szOp := Operand.Var szv) (off := woff) (sz := wsz)
    (rest := as2.stack.drop 2)
    (by simpa using hbb) hop hoperands hevaloff hevalsz (by simp) (by rw [hop]; decide)
    (by intro i hi; cases hi) (by simp [execBodyThread]) hrel2 hw hlt hst htop hcov hbelow hlenu

/-! ### ⚠️ The reorder slices are built on the WRONG lemma (`hstep` is undischargeable for genuine swaps)

`hsupplyW_empty{Return,Revert}Reorder` compose `reorderPlan_sim` (`PlanSim.lean:1663`) and carry its `hstep`
as a caller obligation. That is a mistake, and this repo already documents why:
`GenBlockSimComp.lean:2965-2966` states that `reorderPlan_sim`'s `∀ p` `hstep` is **"undischargeable for
genuine swaps"** — its `∀ p` ranges over ARBITRARY plan states, where the swap-distance bounds
`reorderOne_sim_swap` needs (`dist ≤ 16`, `< ps.stack.length`) simply do not hold. So for the very case those
slices exist to cover — a real `SWAP1` — the hypothesis cannot be met. They are SOUND (nothing false is
proved) and their statements stand, but they cannot be instantiated on a genuine reorder, exactly the
`_HSVP` situation of fact 5 one level down.

The right foundation is **`reorderPlan_join_bounded`** (`GenBlockSimComp.lean:2967`), which discharges the
per-`reorderOne` step INTERNALLY — no carried `hstep` — via the reachable-state invariant
(`foldl_ops_sim_inv`: stack length fixed + no spills ⇒ every swap distance `≤ 16`), fed
`reorderOne_asm_bounded`, with `reorderPlan_perm` for the plan-stack result. Its inputs are
`hperm`/`hpsstk`/`hbound (≤ 17)`/`hnospill`/`hreorder`/`hrel` — all facts about the ACTUAL state, not a `∀ p`.
Rebuilding the two slices on it is the fix; the composition around it (`soLabel_sim` → reorder →
`termRecipeW_*_of_body`, joined by `runAsm_add_ok`) is unchanged, so this is a swap of one call, not a
redesign.

Recorded rather than silently fixed because the slices as committed look applicable and are not. -/

/-! ### Which blocks the body fold can actually reach (and why `addStopFn` cannot)

`codegen_correct_cvJmp_recipeW` below now combines BOTH a real `generateFnPlan` program AND a non-empty body
through the body fold, so this is no longer an open gap. What follows is the map of what the fold reaches —
each fact checked against the source, and each one a constraint that shaped that capstone:

**1. The body fold covers VAR-operand instructions only.** Every disjunct of `RegularStep` / `RegularStepG` /
`RegularStepH` binds its operands as `Operand.Var …` (`GenBlockSimComp.lean:17909` / `:18026` / `:18724`); the
sole `Operand.Lit` anywhere in the family is LOG's topic count. A literal-operand instruction is therefore not
a `RegularStepH` at all.

**2. Hence `addStopFn` — the only real function here with a non-empty body — is out of reach of this route.**
Its body is `addInst = ADD (Lit 5) (Lit 3)` (literal operands), so `RegularBodyH [addInst]` is unprovable, and
`hsupplyW_regularStop` cannot apply to it. That is exactly why its existing capstone
(`codegen_correct_canonical_addStop`) hand-rolls `addStop_runAsm_core` rather than using the body fold. Do not
try to wire `addStopFn` through `hsupplyW_regularStop`.

**3. The body-fold's `nextLiveness` is a PARAMETER, not the real liveness — and that is what makes halting
blocks reachable.** Every value-producing disjunct requires `nextLiveness.contains out = true`, and the
store/copy disjuncts require their inputs live (`GenBlockSimComp.lean:17911`, `:18034`, `:18732`). After a
halting terminator nothing is live, so those hypotheses are false of the REAL `liveVarsAt`. But nothing
demands they be: `nextLiveness` only has to make `hblock` true, i.e. make the fold's plan agree with the
generator's. For a HALTING block, marking the outputs live achieves exactly that — see fact 4 — and
`codegen_correct_cvStop_recipeW` is the witness (`entry: %a = CALLVALUE ; STOP`, output dead, real program).
(An earlier version of this note claimed the opposite; it was wrong.)

**4. `bodyPlanRIP` hardcodes `isHalting := false`, and that is only sound where the outputs are live.**
`generateBlockPlan` passes the block's real `bbIsHalting` (`CodegenPipeline.lean:466`), and `isHalting`
controls exactly one thing: `if ¬ isHalting then popmanyPlan (dead outputs) else ([], ps)`
(`CodegenPipeline.lean:355-359`). So the hardcoded `false` agrees with the generator precisely when
`dead = []`, i.e. when every output is in `nextLiveness` — which the covered disjuncts already demand. Concretely, for a HALTING block the generator suppresses the pop via `isHalting = true` while the fold
suppresses it via `dead = []`: same plan, opposite reasons — which is why marking a dead output live is sound
here rather than a fudge. It also hardcodes `nextIsTerminator := true` (right for a body whose next
instruction IS the terminator) and uses ONE uniform `nextLiveness`, whereas `generateBlockPlan` recomputes
`liveVarsAt` per instruction (`:462-465`).

That last difference is NOT the barrier it looks like, for the same reason as fact 3: `nextLiveness` only has
to make `hblock` true. Checked on the real generator for `entry: %s = CALLVALUE ; %o = CALLVALUE ; JMP next` —
the uniform `nextLiveness := ["s","o"]` yields `[CALLVALUE, CALLVALUE]`, exactly the body the generator emits,
because marking BOTH outputs live makes `dead = []` at each step just as the real per-instruction `nextLive`
does. **So the fold is not limited to single-instruction bodies.** (An earlier version of this note said it
was; that was wrong, and wrong the same way fact 3 was.)

**5. The emit-segment (`_HSVP`) slices cannot be applied to a REAL terminator.** They go through
`emitInputPlan_{single,pair}_var_sim`, whose `hliveaddr`/`hliveoff`/`hliveszv` (`nl.contains v = true`) force
the LIVE variant, which emits a DUP. But a terminator's real `nextLive` is `[]` (nothing is live after it), and
`emitInputPlan` then emits NOTHING — the operand is consumed in place. Checked on the real generator:
`emitInputPlan SELFDESTRUCT [Var "a"] [] …` = `[]` while `… ["a"] …` = `[DUP1]`. So those slices are sound and
satisfiable but not instantiable at the generator's own liveness. The dead case is served by
`emitOneInput_sim_var_noop` (`nextLiveness.contains v = false` ⇒ no ops), and the resulting slices are
`hsupplyW_empty{Selfdestruct,Return,Revert}Dead` — all three halting operand-carrying terminators, each
instantiable at the generator's own liveness. `hsupplyW_emptySelfdestructDead` is what the capstone's
successor block uses. Their precondition is that the operands already sit on the plan stack in terminator
order, which is exactly what a predecessor that computed them leaves behind.

**6. What is left, and what it costs.** The slices without a capstone are so for two different reasons, and
the distinction matters:
* `hsupplyW_empty{Return,Revert}Dead` — **the obstacle is the terminator's REORDER, not the body.** They
  require the terminator's emitted segment to be empty, i.e. the operands already on the plan stack in exactly
  terminator order. A nil reorder IS possible in general — `reorderPlan_pair_var_nil` proves
  `reorderPlan [Var x, Var y] ps = ([], ps)` when `ps.stack = base ++ [Var x, Var y]` — so this is a question
  of arranging the arrival order, not an impossibility. But the obvious predecessor shape does not arrange it:
  on `entry: <two CALLVALUEs> ; JMP next` / `next: RETURN _ _`, all FOUR combinations of body order × operand
  order emit `[… LABEL next; SWAP1; RETURN]` (checked). That `SWAP1` is a `reorderOps`, which
  `generateRegularInstPlan` emits before `emitOps` (`CodegenPipeline.lean:353`) and which none of these slices
  model — EXCEPT `hsupplyW_empty{Return,Revert}Reorder` (below), which model exactly that. So the segment is
  `[SWAP1]` — matched by neither the dead slice (`[]`) nor `_HSVP` (`[DUP1]`, fact 5), but handled by the
  reorder slices, and BOTH operand-carrying halting terminators the generator reorders are now covered. What
  remains is a capstone for either, and the target is already identified rather than hypothetical:
  `entry: %s = CALLVALUE ; %o = CALLVALUE ; JMP next` / `next: RETURN %s %o` compiles to
  `[LABEL entry; CALLVALUE; CALLVALUE; PUSHLBL next; JUMP; LABEL next; SWAP1; RETURN]` — checked. Its `next`
  block is `[SOLabel] ++ [SWAP1] ++ RETURN`, exactly `hsupplyW_emptyReturnReorder`'s shape, and its `entry`
  block is the reorder-free two-instruction body that `hsupplyW_regularJmp` handles (fact 4's witness). So the
  capstone is: `RegularBodyH … [cvS, cvO] []` (two state-read disjuncts, `s ∉ []` then `o ∉ ["s"]`, both live
  in `["s","o"]`) for the entry, plus `hreorder`/`hstack'` (concrete, `rfl`-shaped) and `hstep` (from
  `reorderOne_sim_{swap,positioned}`) for the successor.

  **One caveat, checked rather than assumed** (an earlier version of this paragraph called it "no missing
  lemma", which was too fast): RETURN's `hbelow : off + sz ≤ ps'.alloc.fnEom` bites. `initPlanState 0` sets
  `alloc.fnEom = 0` (`PlanTypes.lean:50-55`) and `reorderPlan` never touches `alloc`, so `hbelow` forces
  `off = sz = 0` — while CALLVALUE is symbolic. The capstone is therefore only provable under an explicit
  precondition (`vs.callCtx.callvalue = 0`, which also gives `hcov0` its left disjunct), exactly the way
  `genBlockSimulation_calldatacopy_example` carries `hmemsafe` as its one honest runtime hypothesis. That is a
  real capstone, not a vacuous one — zero call value is the common case — but it is narrower than the
  unconditional statement the other capstones prove, and worth knowing before starting. **CORRECTED later
  (`tFn_prog_indep_fnEom` and the note "Why `tFn`/`rFn` are narrow"): `hbelow` is NOT what makes a symbolic
  size hard.** `fnEom` is a free parameter of `generateFnPlan` — raising it to 32 leaves the emitted program
  byte-identical — so `hbelow` can be given arbitrary room with NO allocating function. The binding
  constraint is `hcov0`'s asm-memory disjunct, which needs `Inv : VenomState → AsmState → Prop`.

  And `hstep` is a genuine caller obligation, not something a wrapper hands over: `reorderPlan_join_sim`
  (`GenBlockSimComp.lean:2855`) takes it too, adding only the permutation/stack facts around it. Discharging
  it means casing each `(i, op)` of `targetOps.enum` into `reorderOne_sim_positioned` (already at its target
  depth ⇒ no ops) or `reorderOne_sim_swap` (`GenInstSim.lean:2786,2816`) — which is what "discharged at the
  call site" means in that family's docstrings. For the pinned two-operand target that is two cases, with
  `reorderPlan_swapped_pair_var` (`:5462`) giving the plan-level equation.
  **Every other input to that capstone is checked on the real generator**, so the assembly starts from facts:
  the program is `[L entry(0); CALLVALUE(1); CALLVALUE(2); PL next(3); JUMP(4); L next(5); SWAP1(6);
  RETURN(7)]` with `pcOf next = 5`, `length = 8`; `wOf entry = 8`, `wOf next = 3`; the entry's `hw` is
  `3 + ((1+2)+2) = 8 ≤ 8` and the successor's is `1+1+1 = 3 ≤ 3` — both tight, so the layout admits no slack;
  `hps` (the body fold's plan state IS `psOf "next"`) closes by `rfl`; and `reorderPlan [Var o, Var s]
  (psOf "next")` emits exactly ONE op, so `rops.length = 1` and the RETURN lands at `5+1+1 = 7`. What is left
  is `hstep` (two cases, above) and the `callvalue = 0` precondition. NB `bodyPlanRIP` is `private`, so a probe
  in another file must write the fold longhand.

  Two ways in, then, and BOTH are open. **(a) Arrange the arrival order.** For a non-commutative terminator
  `generateRegularInstPlan` reorders towards `operands' = computeOperands inst = inst.operands.reverse`
  (`CodegenPipeline.lean:341,343`), so `RETURN off sz` targets `[Var sz, Var off]` and
  `reorderPlan_pair_var_nil` fires exactly when `ps.stack = base ++ [Var sz, Var off]` — `off` on top. None of
  the four shapes tried reach it, and the reason is instructive: the PREDECESSOR's JMP block emits its own
  reorder (`SWAP1` before `PUSHLBL next` in two of the four), so what `next` receives is not simply what the
  body pushed. Whether some predecessor exits in the required order is untested — not refuted.
  **(b) Add a reorder-segment slice** — and this is assembly rather than new machinery, checked rather than
  assumed: the fold-level `reorderPlan_sim` is already proved (`PlanSim.lean:1663`), and its per-operand
  residual is discharged by `reorderOne_sim_{swap,positioned}` (`GenInstSim.lean:2786,2816`), whose shape is
  exactly the one the slices already compose — given `hblock` at `as.pc` it returns the asm run, the relation
  at the reorder's resulting plan state, and `as'.pc = as.pc + len`, i.e. the `soLabel_sim` /
  `emitInputPlan_*_sim` interface, joinable by `runAsm_add_ok`. So the missing slice is
  `[SOLabel] ++ body ++ reorderOps ++ emitOps` instead of `[SOLabel] ++ body ++ emitOps`. What is NOT the obstacle: per-instruction liveness
  (fact 4 refutes that diagnosis).
* `hsupplyW_regularDjmp` — **reachable, merely expensive.** DJMP's selector is a body-produced variable
  consumed by the terminator, so it satisfies fact 3 exactly as JNZ does. The cost is the dispatch chain: for
  `entry: %a = CALLVALUE ; DJMP %a t0 t1` the generator emits 27 instructions — 5-op scan entries
  `[DUP1; PUSHn; EQ; PUSHLBL tramp; JUMPI]` per label, then 4-op trampolines `[LABEL tramp; POP; PUSHLBL t;
  JUMP]`, with a `revert` fall-through. A symbolic selector forces a THREE-way split (`= 0` → t0, `= 1` → t1,
  otherwise the block errors and the driver's error arm applies), each needing the full `djmpEntryHere`
  structure. Nothing unknown, just long.
* The `_regular` cores and `termRecipeW_{return,revert}_HSVP` are 0-consumer BY DESIGN — see fact 5 and the
  wrapper note.

**7. The unifying statement: the family COVERED reorder-free blocks; modelling `reorderOps` lifts that, and the
first such slice now exists.** `bodyPlanRIP` models a block's
plan as label ++ per-instruction plans, and none of the slices model `reorderOps` — which
`generateRegularInstPlan` emits between the join and the emit (`CodegenPipeline.lean:353`). So whenever the
generator reorders, the block is outside this family, and that is the single condition behind the scattered
observations above. Checked on the two-CALLVALUE shape: with `next: RETURN %s %o` the entry block emits
`[LABEL; CALLVALUE; CALLVALUE; PUSHLBL next; JUMP]` and the fold reproduces its body exactly, so
`hsupplyW_regularJmp` applies (fact 4); with `next: RETURN %o %s` the entry block emits
`[LABEL; CALLVALUE; CALLVALUE; SWAP1; PUSHLBL next; JUMP]` while the fold still yields
`[CALLVALUE, CALLVALUE]` — the `PUSHLBL` the slice expects at `pc+1+bodyLen` is a `SWAP1`, so the slice does
NOT apply. Body length is irrelevant to this; the reorder is what decides. Note the mismatch is DETECTED, not
unsound: the slice's `hblock`/`hpush` simply cannot be discharged.

**⇒ The shape that fits is a CONTINUING block.** Facts 3 and 4 point the same way, and the capstone below is
built on exactly that: `entry: %a = CALLVALUE ; JMP next` with `next: SELFDESTRUCT %a`. The entry block
continues (`bbIsHalting = false`, matching `bodyPlanRIP`) and `a` is live at the JMP because the successor
consumes it, so the state-read disjunct of `RegularStepG` (`:18068`, `∃ out name fV fA`, `operands = []`)
applies to the body against the REAL liveness. `hsupplyW_regularJmp` takes the entry block;
`hsupplyW_emptySelfdestructDead` (not the `_HSVP` slice — see fact 5) takes the successor.

Note `RegularBodyH` takes NO liveness/dfg/cfg parameters, so the existing var-operand instances
(`cdc_regularBodyH`, `addVar_regularBodyG`, `sstore_regularBodyG'`) are already valid for the REAL analyses;
what is hand-written about them is the PROGRAM they are stated against (`cdcProg` etc., built with the dummy
`exLiveness`/`exCfg`). So the remaining work is concentrated in `hblock`: showing the real generator's emitted
plan for such a body is the asm the block sim expects. Existing pattern for that half: prove
`generated = handwritten` (cf. `(asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 = jmpProg`)
and transfer. -/


namespace Example

/-- **The first NON-EMPTY-body `hsupply` — on a REAL block.** For `entry: CALLDATACOPY a b c ; STOP`
    (compiled to `[JUMPDEST ; DUP1 ; DUP3 ; DUP5 ; CALLDATACOPY ; STOP]`), the driver's per-block
    obligation is discharged end to end: the body is a genuine memory-touching instruction whose
    `RegularBodyH` comes from `cdc_regularBodyH`, and the plan the generator emits for it really is those
    four asm ops. Every earlier capstone had EMPTY-bodied blocks (the only instruction was the
    terminator), so the nine non-empty-body slices had no consumer; this exercises the chain
    `hsupplyW_regularStop → genBlockBodyH_sim_inv → termRecipeW_stop_of_body` on a real body. `hmemsafe`
    is the one honest runtime precondition CALLDATACOPY carries. -/
theorem hsupplyW_cdcStop {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {offsets : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {wOf : String → Nat} {ctx : VenomContext} {restFuel : Nat}
    {vs : VenomState} {va vb vc : bytes32}
    (hadef : lookupVar "a" vs = some va) (hbdef : lookupVar "b" vs = some vb)
    (hcdef : lookupVar "c" vs = some vc)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel lo p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hw : 6 ≤ wOf cdcBB.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen offsetToPc cdcProg
        ({ asmOfVenom { vs with instIdx := 0 } with
            stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) })
        = AsmResult.AsmOK as' ∧
      TermRecipeW dummyFn lo pcOf psOf wOf offsetToPc offsets cdcProg as' ps' vs' bodyLen
        (([cdcInst] : List Instruction).length + (restFuel + 1)) ctx cdcBB vs := by
  have hadef' : lookupVar "a" { vs with instIdx := 0 } = some va := hadef
  have hbdef' : lookupVar "b" { vs with instIdx := 0 } = some vb := hbdef
  have hcdef' : lookupVar "c" { vs with instIdx := 0 } = some vc := hcdef
  set sEnd : VenomState :=
    { writeMemoryWithExpansion va.toNat
        ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding vb.toNat vc.toNat)
        { vs with instIdx := 0 } with instIdx := 1 } with hsEnd
  have hthread : execBodyThread [cdcInst] 0 { vs with instIdx := 0 } = some sEnd := by
    rw [hsEnd]; simp only [execBodyThread, cdcInst, stepInstBase, evalOperand, hadef', hbdef', hcdef']
  have hnonterm : ∀ inst ∈ [cdcInst], isTerminator inst.opcode = false := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
  have hdef : ∀ z ∈ ["a","b","c"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · subst h; exact ⟨va, hadef⟩
    · subst h; exact ⟨vb, hbdef⟩
    · subst h; exact ⟨vc, hcdef⟩
  have hlenS : (["a","b","c"] : List String).length
      + (([cdcInst].zipIdx 0).map (fun _ => 1)).sum ≤ 15 := by decide
  have hlt5 : ({ asmOfVenom { vs with instIdx := 0 } with
        stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) }).pc + 1
      + (executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg dummyFn ["a","b","c"] "entry" [cdcInst]
          { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) }).1).length
      < cdcProg.length := by
    show (0:Nat) + 1 + 4 < cdcProg.length
    decide
  have hget5 : cdcProg.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
        stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) }).pc + 1
      + (executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg dummyFn ["a","b","c"] "entry" [cdcInst]
          { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) }).1).length, hlt5⟩
      = AsmInst.AsmOp "STOP" := by
    rw [show (⟨_, hlt5⟩ : Fin cdcProg.length) = ⟨5, by decide⟩ from Fin.ext (by rfl)]
    rfl
  have hbLabel : asmBlockAt cdcProg
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) }).pc
      (executePlan [StackOp.SOLabel cdcBB.label]) := by
    refine ⟨by show (0:Nat) + 1 ≤ cdcProg.length; decide, fun j hj => ?_⟩
    have hj' : j < 1 := hj; interval_cases j; rfl
  have hblock : asmBlockAt cdcProg
      (({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) }).pc + 1)
      (executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg dummyFn ["a","b","c"] "entry" [cdcInst]
        { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) }).1) := by
    refine ⟨by show (0:Nat) + 1 + 4 ≤ cdcProg.length; decide, fun j hj => ?_⟩
    have hj' : j < 4 := hj; interval_cases j <;> rfl
  exact hsupplyW_regularStop (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg)
    (fn := dummyFn) (front := [cdcInst]) (stopInst := stopInst) (hd := cdcInst) (tl := [stopInst])
    (nextLiveness := ["a","b","c"]) (curBbLabel := "entry") (dem := 1) (S := ["a","b","c"])
    (ps0 := { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) })
    (sEnd := sEnd) (bb := cdcBB) (prog := cdcProg) (o2pc := offsetToPc) (lo := lo)
    (restFuel := restFuel) (ctx := ctx) (offsets := offsets) (pcOf := pcOf) (psOf := psOf) (wOf := wOf)
    (asm := { asmOfVenom { vs with instIdx := 0 } with
              stack := asmStackOf { vs with instIdx := 0 } lo (["a","b","c"].map Operand.Var) })
    (hbb := rfl) (hstopop := rfl) (hcons := rfl) (hphi := by decide) (hnonterm := hnonterm)
    (hthread := hthread) (hreg := cdc_regularBodyH hmemsafe)
    (hsd := stackDiscH_varStack hlenS hdef) (hsv := stackIsVars_varStack)
    (hrel := venomAsmRel_varStack hdef)
    (hbLabel := hbLabel) (hblock := hblock) (hpc := hlt5) (hstop := hget5) (hw := hw)

/-! ### The frontier witness: a REAL generated program with a NON-EMPTY body

`entry: %a = CALLVALUE ; JMP next` / `next: SELFDESTRUCT %a`. The entry block's body is a genuine
instruction, and `a` is live at the JMP precisely because the successor consumes it — which is what makes
the body-fold's `nextLiveness.contains out = true` true against the REAL liveness (see the note above).
`generateFnPlan` emits `[LABEL entry; CALLVALUE; PUSHLBL next; JUMP; LABEL next; SELFDESTRUCT]` — note the
absence of a POP after CALLVALUE (the output is live) and of a DUP before SELFDESTRUCT (the operand is dead
there, so it is consumed in place). -/

def cvInst2 : Instruction :=
  { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def jmpNextInst : Instruction :=
  { id := 1, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def sdAInst : Instruction :=
  { id := 2, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Var "a"], outputs := [] }
def cvEntryBB : BasicBlock := { label := "entry", instructions := [cvInst2, jmpNextInst] }
def sdNextBB  : BasicBlock := { label := "next",  instructions := [sdAInst] }
def cvJmpFn : IrFunction := { name := "main", blocks := [cvEntryBB, sdNextBB] }
def cvJmpCtx : VenomContext := { functions := [cvJmpFn], entry := some "main" }

def cvProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE",
   AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 6)), AsmInst.AsmOp "JUMP",
   AsmInst.AsmLabel "next", AsmInst.AsmOp "SELFDESTRUCT"]

theorem cv_prog : (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 = cvProg := by rfl

def tS : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["s"] }
def tO : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["o"] }
def tJ : Instruction := { id := 2, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def tR : Instruction :=
  { id := 3, opcode := Opcode.RETURN, operands := [Operand.Var "s", Operand.Var "o"], outputs := [] }
def tEntry : BasicBlock := { label := "entry", instructions := [tS, tO, tJ] }
def tNext  : BasicBlock := { label := "next",  instructions := [tR] }
def tFn : IrFunction := { name := "main", blocks := [tEntry, tNext] }
def tCtx : VenomContext := { functions := [tFn], entry := some "main" }

/-! ### A two-instruction body, and the reusable state-read step

The four `cv*_regularBodyH` above each inline the same state-read disjunct. `cv_step` states it once, for ANY
CALLVALUE instruction, output var and ambient `S` — so a body of several state-reads is a fold of it. -/

/-- **A single CALLVALUE step as a `RegularStepH`**, parameterised by its output var and the ambient `S`:
    the 6th disjunct of `RegularStepG` (`operands = []`, output live), lifted by `RegularStepH`'s first arm.
    `fV`/`fA` both read `callCtx.callvalue`, and their agreement IS `venomAsmRel`'s callCtx equality. -/
theorem cv_step {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {out : String} {S nl : List String} {i : Instruction} {n : Nat}
    (hi : i = { id := n, opcode := Opcode.CALLVALUE, operands := [], outputs := [out] })
    (hnot : out ∉ S) (hlive : nl.contains out = true) :
    RegularStepH lo nl offsetToPc prog 1 i S := by
  subst hi
  left
  refine ⟨?_, by simp⟩
  right; right; right; right; right; left
  refine ⟨out, "CALLVALUE", (fun v : VenomState => v.callCtx.callvalue),
    (fun s : AsmState => s.callCtx.callvalue),
    rfl, by simp, rfl, rfl, rfl, hnot, hlive, ?_, ?_, ?_⟩
  · intro v; rfl
  · intro s h hget
    simp only [asmStep, hget]
    split
    · rfl
    · rename_i hbad; exact absurd h hbad
  · intro p v s hrel
    obtain ⟨_, _, _, _, _, _, _, hcc, _, _, _, _⟩ := hrel
    show s.callCtx.callvalue = v.callCtx.callvalue
    rw [hcc]

/-- **A TWO-instruction body as a `RegularBodyH`** — `%s = CALLVALUE ; %o = CALLVALUE`, threading `S` from
    `[]` to `["s"]`, both outputs live in `["s","o"]`. Concrete evidence for fact 4: the fold handles a body
    longer than one instruction. -/
theorem tBody_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["s","o"] offsetToPc
      (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 1 [tS, tO] [] := by
  refine ⟨cv_step (out := "s") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  exact cv_step (out := "o") (S := [] ++ tS.outputs) rfl (by decide) (by decide)

/-- The walk invariant for `tFn`. -/
def tInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "s" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "o" s = some (EvmYul.UInt256.ofNat 0))

/-- The body-end state of `tEntry` (after both CALLVALUEs). -/
abbrev tSEnd (s : VenomState) : VenomState :=
  { updateVar "o" s.callCtx.callvalue { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 }
      with instIdx := 1 } with instIdx := 2 }

theorem tEntry_thread (s : VenomState) :
    execBodyThread [tS, tO] 0 { s with instIdx := 0 } = some (tSEnd s) := by
  simp [execBodyThread, tS, tO, stepInstBase, execRead0, updateVar]

/-- `tEntry`'s OK result is `jumpTo "next"` of the body-end state. -/
theorem tEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (2 + (j+1)) tCtx tEntry s = ExecResult.OK (jumpTo "next" (tSEnd s)) :=
  runBlock_body_jmp tCtx tEntry j [tS, tO] tJ tS [tO, tJ] s (tSEnd s) "next"
    rfl rfl rfl rfl (by decide) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                                    rcases hi with rfl | rfl <;> decide)
    (tEntry_thread s) (by simpa [updateVar] using hnh)


/-- **`tInv` survives every block of `tFn`.** For `tEntry`: fuel < 3 gives `Error`, and at `2+(j+1)` the
    result is `jumpTo "next" (tSEnd s)` — whose vars `s`/`o` are the (zero) call value, which is exactly what
    the successor's RETURN recipe needs. For `tNext`: RETURN never yields `OK`, so the obligation is vacuous. -/
theorem tInv_pres : ∀ bb ∈ tFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    tInv s → runBlock f' tCtx bb s = ExecResult.OK s' → tInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [tFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- tEntry: needs fuel >= 3; then s' = jumpTo "next" (tSEnd s)
    match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
             stepInstBase, execRead0, isTerminator] at hrun
    | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
             stepInstBase, execRead0, isTerminator] at hrun
    | 2 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS, tO,
             stepInstBase, execRead0, isTerminator] at hrun
    | (j+3) =>
      rw [show j+3 = 2+(j+1) from by omega, tEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ?_⟩
      have hs : lookupVar "s" (jumpTo "next" (tSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "s" (updateVar "o" s.callCtx.callvalue
          { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
        show lookupVar "s" (updateVar "s" s.callCtx.callvalue { s with instIdx := 0 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      have ho : lookupVar "o" (jumpTo "next" (tSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "o" (updateVar "o" s.callCtx.callvalue
          { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      exact ⟨hs, ho⟩
  · -- tNext: RETURN never yields OK. Characterise the block with `runBlock_body_return` (the route that
    -- worked for entry) instead of reducing `runBlock` by hand.
    match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tNext, tR,
             stepInstBase, isTerminator] at hrun
    | (j+1) =>
      rcases hls : lookupVar "s" s with _ | ws
      · -- "s" undefined: RETURN errors. Characterise with `runBlock_error`, don't reduce.
        have hstep : stepInstBase tR { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
          have hls' : lookupVar "s" { s with instIdx := 0 } = none := hls
          simp [tR, stepInstBase, evalOperand, hls']
        have hrb := runBlock_error tCtx tNext j [] tR tR [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) hstep (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
      · rcases hlo : lookupVar "o" s with _ | wo
        · -- "o" undefined: same.
          have hstep : stepInstBase tR { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
            have hls' : lookupVar "s" { s with instIdx := 0 } = some ws := hls
            have hlo' : lookupVar "o" { s with instIdx := 0 } = none := hlo
            simp [tR, stepInstBase, evalOperand, hls', hlo']
          have hrb := runBlock_error tCtx tNext j [] tR tR [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) hstep (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
        · have hrb := runBlock_body_return tCtx tNext j [] tR tR [] s { s with instIdx := 0 }
            (Operand.Var "s") (Operand.Var "o") ws wo rfl rfl rfl hls hlo rfl (by decide)
            (by intro i hi; cases hi) (by simp [execBodyThread])
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp] at hrun
          rw [hrb] at hrun
          exact absurd hrun (by simp)


set_option maxHeartbeats 4000000 in
/-- **The  capstone**:  / ,
    end to end against the real generated program, through the INVARIANT-carrying driver. Exercises, in one
    function: a TWO-instruction body, a genuine terminator REORDER (the ), and a value-dependent
    recipe (RETURN's ) that the plain ∀-s driver could never supply. -/
theorem codegen_correct_tFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 tCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ tFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [tFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [tEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [tNext, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan tFn 0 0 = some ((generateFnPlan tFn 0 0).get!.1, (generateFnPlan tFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel tFn) tFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv tInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel tFn) tFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan tFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := tCtx) (fn := tFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan tFn 0 0).get!.1) (psFinal := (generateFnPlan tFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ tInv_pres ?_ ⟨by simpa using hvshalt, by simpa using hzero, by simp⟩
  case _ =>
    intro bb hbb s
    simp only [tFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, tEntry, tS]
    · simp [runBlock, evalPhis, execBlock, tNext, tR]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [tFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: two CALLVALUEs + JMP
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, tEntry, tS, stepInstBase, execRead0, isTerminator]⟩
      | 1 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, tEntry, tS, tO, stepInstBase, execRead0, isTerminator]⟩
      | (j+2) =>
      rw [show j+2+1 = ([tS, tO] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [tS, tO]) (jmpInst := tJ) (hd := tS) (tl := [tO, tJ])
        (nextLiveness := ["s","o"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 7) (bb' := tNext) (sEnd := tSEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl <;> decide)
        (hthread := tEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := tBody_regularBodyH)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 2 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := ?_) (hoff := ?_) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl) (hidx_lk := ?_) (hlk' := rfl) (hw := by decide))
      · decide
      · decide
      · decide
    · -- next: RETURN with the SWAP1 reorder; the invariant supplies the operand VALUES
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc5 : asm.pc = 5 := by rw [hpc_asm]; decide
      obtain ⟨_, _, hvals⟩ := hinv
      obtain ⟨hs0, ho0⟩ := hvals hlbl
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := tR) (offv := "s") (szv := "o")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "s", Operand.Var "o"])
        (ps := psOfFn (fnPlanFuel tFn) tFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := hs0) (hevalsz := ho0) (hvoff := hs0) (hvsz := ho0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc5]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc5]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc5]; decide) (hget := by simp only [hpc5]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨tEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel tFn) tFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1.length
      omega



/-! ### ✅ The REVERT capstone — `codegen_correct_rFn_recipeW` (terminator coverage 7/8 → 8/8)

REVERT was the last codegen terminator kind with a per-block slice but no whole-function capstone. `rFn`
reuses `tFn`'s entry verbatim (`entry: %s = CALLVALUE ; %o = CALLVALUE ; JMP next`) and swaps the successor's
RETURN for a REVERT (`next: REVERT %s %o`). The generator emits the same 8-instruction shape,
`[L entry; CALLVALUE; CALLVALUE; PUSH next; JUMP; L next; SWAP1; REVERT]` (entry@0, next@5,
`offsets "next" = 7`), so `next` is again exactly the reorder slice's shape and
`hsupplyW_emptyRevertReorder` applies where `hsupplyW_emptyReturnReorder` did — the whole capstone is the
RETURN one with the terminator swapped, which is what a good slice family should buy.

Like `tFn`, the recipe is value-dependent: with `fnEom` instantiated at `0`, REVERT's
`hbelow : off + sz ≤ ps'.alloc.fnEom` forces `off = sz = 0`, which the invariant supplies from
`callvalue = 0` — so the statement carries that hypothesis, exactly as the RETURN twin does. **But `hbelow`
is not what BLOCKS a symbolic size**: `fnEom` is a free parameter and `rFn_prog_indep_fnEom` shows raising it
to 32 leaves the program byte-identical, so `hbelow` can be given arbitrary room with no allocating function.
The binding constraint is `hcov0`'s asm-memory disjunct — see "Why `tFn`/`rFn` are narrow" below.

NON-VACUITY is a THEOREM here, not an `#eval` (`rFn_reverts`). `djFn`'s witness could be evaluated because
its blocks only STOP; `rFn` cannot — REVERT reads memory, so evaluation hits `ffi.ByteArray.zeroes`, which
has no native implementation (it is an M1 FFI axiom). Proving it instead turned out STRONGER than the
`#eval` would have been: `rFn_reverts` shows `runContext 10 rCtx vs = Abort RevertAbort vs'` for EVERY `vs`
the capstone's own hypotheses admit, so the `Abort RevertAbort` arm — not the `| _ => True` catch-all — is
the one that fires, universally rather than at a single sample point. It needs no FFI axiom at all
(`[propext, Classical.choice, Quot.sound]`), since the reverting state is never inspected. -/

def rR : Instruction :=
  { id := 3, opcode := Opcode.REVERT, operands := [Operand.Var "s", Operand.Var "o"], outputs := [] }
def rNext : BasicBlock := { label := "next", instructions := [rR] }
def rFn : IrFunction := { name := "main", blocks := [tEntry, rNext] }
def rCtx : VenomContext := { functions := [rFn], entry := some "main" }

theorem rBody_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["s","o"] offsetToPc
      (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 1 [tS, tO] [] := by
  refine ⟨cv_step (out := "s") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  exact cv_step (out := "o") (S := [] ++ tS.outputs) rfl (by decide) (by decide)

theorem rEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (2 + (j+1)) rCtx tEntry s = ExecResult.OK (jumpTo "next" (tSEnd s)) :=
  runBlock_body_jmp rCtx tEntry j [tS, tO] tJ tS [tO, tJ] s (tSEnd s) "next"
    rfl rfl rfl rfl (by decide) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                                    rcases hi with rfl | rfl <;> decide)
    (tEntry_thread s) (by simpa [updateVar] using hnh)

/-- **The REVERT arm really fires** — the non-vacuity witness for `codegen_correct_rFn_recipeW`. Unlike the
    STOP-only `djFn`, `rFn` cannot be `#eval`ed (REVERT touches memory ⇒ the M1 `ffi.ByteArray.zeroes` has
    no native impl under `lake env lean`), so the witness is symbolic instead: whenever `rInv` holds at
    `next`, `rNext` aborts with `RevertAbort`. Composed with `rEntry_runBlock`, the capstone's
    `Abort RevertAbort` arm is the one that fires — not the `| _ => True` catch-all. -/
theorem rNext_reverts (s : VenomState) (j : Nat)
    (hs : lookupVar "s" s = some (EvmYul.UInt256.ofNat 0))
    (ho : lookupVar "o" s = some (EvmYul.UInt256.ofNat 0)) :
    runBlock (0 + (j+1)) rCtx rNext s = ExecResult.Abort AbortType.RevertAbort
      (revertState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat
        (EvmYul.UInt256.ofNat 0).toNat { s with instIdx := 0 }) { s with instIdx := 0 })) :=
  runBlock_body_revert rCtx rNext j [] rR rR [] s { s with instIdx := 0 }
    (Operand.Var "s") (Operand.Var "o") _ _ rfl rfl rfl hs ho rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

theorem rInv_pres : ∀ bb ∈ rFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    tInv s → runBlock f' rCtx bb s = ExecResult.OK s' → tInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [rFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
             stepInstBase, execRead0, isTerminator] at hrun
    | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
             stepInstBase, execRead0, isTerminator] at hrun
    | 2 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS, tO,
             stepInstBase, execRead0, isTerminator] at hrun
    | (j+3) =>
      rw [show j+3 = 2+(j+1) from by omega, rEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ?_⟩
      have hs : lookupVar "s" (jumpTo "next" (tSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "s" (updateVar "o" s.callCtx.callvalue
          { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
        show lookupVar "s" (updateVar "s" s.callCtx.callvalue { s with instIdx := 0 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      have ho : lookupVar "o" (jumpTo "next" (tSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "o" (updateVar "o" s.callCtx.callvalue
          { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      exact ⟨hs, ho⟩
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, rNext, rR,
             stepInstBase, isTerminator] at hrun
    | (j+1) =>
      rcases hls : lookupVar "s" s with _ | ws
      · have hstep : stepInstBase rR { s with instIdx := 0 } = ExecResult.Error "revert: undefined operand" := by
          have hls' : lookupVar "s" { s with instIdx := 0 } = none := hls
          simp [rR, stepInstBase, evalOperand, hls']
        have hrb := runBlock_error rCtx rNext j [] rR rR [] s { s with instIdx := 0 }
          "revert: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) hstep (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
      · rcases hlo : lookupVar "o" s with _ | wo
        · have hstep : stepInstBase rR { s with instIdx := 0 } = ExecResult.Error "revert: undefined operand" := by
            have hls' : lookupVar "s" { s with instIdx := 0 } = some ws := hls
            have hlo' : lookupVar "o" { s with instIdx := 0 } = none := hlo
            simp [rR, stepInstBase, evalOperand, hls', hlo']
          have hrb := runBlock_error rCtx rNext j [] rR rR [] s { s with instIdx := 0 }
            "revert: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) hstep (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
        · have hrb := runBlock_body_revert rCtx rNext j [] rR rR [] s { s with instIdx := 0 }
            (Operand.Var "s") (Operand.Var "o") ws wo rfl rfl rfl hls hlo rfl (by decide)
            (by intro i hi; cases hi) (by simp [execBodyThread])
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp] at hrun
          rw [hrb] at hrun
          exact absurd hrun (by simp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codegen_correct_rFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 rCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ rFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [rFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [tEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [rNext, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan rFn 0 0 = some ((generateFnPlan rFn 0 0).get!.1, (generateFnPlan rFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel rFn) rFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv tInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel rFn) rFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan rFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := rCtx) (fn := rFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan rFn 0 0).get!.1) (psFinal := (generateFnPlan rFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ rInv_pres ?_ ⟨by simpa using hvshalt, by simpa using hzero, by simp⟩
  case _ =>
    intro bb hbb s
    simp only [rFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, tEntry, tS]
    · simp [runBlock, evalPhis, execBlock, rNext, rR]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [rFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: two CALLVALUEs + JMP
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, tEntry, tS, stepInstBase, execRead0, isTerminator]⟩
      | 1 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, tEntry, tS, tO, stepInstBase, execRead0, isTerminator]⟩
      | (j+2) =>
      rw [show j+2+1 = ([tS, tO] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [tS, tO]) (jmpInst := tJ) (hd := tS) (tl := [tO, tJ])
        (nextLiveness := ["s","o"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 7) (bb' := rNext) (sEnd := tSEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl <;> decide)
        (hthread := tEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := rBody_regularBodyH)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 2 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := ?_) (hoff := ?_) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl) (hidx_lk := ?_) (hlk' := rfl) (hw := by decide))
      · decide
      · decide
      · decide
    · -- next: RETURN with the SWAP1 reorder; the invariant supplies the operand VALUES
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc5 : asm.pc = 5 := by rw [hpc_asm]; decide
      obtain ⟨_, _, hvals⟩ := hinv
      obtain ⟨hs0, ho0⟩ := hvals hlbl
      refine Or.inr (hsupplyW_emptyRevertReorder (tInst := rR) (offv := "s") (szv := "o")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "s", Operand.Var "o"])
        (ps := psOfFn (fnPlanFuel rFn) rFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := hs0) (hevalsz := ho0) (hvoff := hs0) (hvsz := ho0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc5]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc5]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc5]; decide) (hget := by simp only [hpc5]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨tEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel rFn) rFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1.length
      omega


/-- **The `Abort RevertAbort` arm really is the one that fires** — `codegen_correct_rFn_recipeW`'s statement
    has a `| _ => True` catch-all (the shape that made the retracted `codegen_correct_ofRecipes` vacuous), so
    the arm must be exhibited, not assumed. `rFn` cannot be `#eval`ed the way `djFn` was: REVERT reads memory,
    so evaluation hits `ffi.ByteArray.zeroes`, which has no native implementation (it is an M1 FFI axiom).
    The witness is therefore symbolic — and it is stronger than an `#eval`, being universally quantified over
    every state the capstone's own hypotheses admit. -/
theorem rFn_reverts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 rCtx vs = ExecResult.Abort AbortType.RevertAbort vs' := by
  have h0 : runContext 10 rCtx vs
      = runBlocks 10 rCtx rFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, rCtx, rFn, lookupFunction, fnEntryLabel, tEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  -- entry: two CALLVALUEs then JMP "next"
  have hentry : runBlock 9 rCtx tEntry s0 = ExecResult.OK (jumpTo "next" (tSEnd s0)) := by
    rw [show (9 : Nat) = 2 + (6 + 1) from by omega]; exact rEntry_runBlock s0 6 hnh0
  have hlk0 : lookupBlock s0.currentBb rFn.blocks = some tEntry := rfl
  have hjh : (jumpTo "next" (tSEnd s0)).halted = false := by
    simpa [jumpTo, updateVar] using hnh0
  have hstep : runBlocks 10 rCtx rFn s0 = runBlocks 9 rCtx rFn (jumpTo "next" (tSEnd s0)) :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hjh
  -- next: REVERT, with both operands the (zero) call value
  have hs : lookupVar "s" (jumpTo "next" (tSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "s" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "s" (updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]
  have ho : lookupVar "o" (jumpTo "next" (tSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "o" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]
  have hlk1 : lookupBlock (jumpTo "next" (tSEnd s0)).currentBb rFn.blocks = some rNext := rfl
  have hrev := rNext_reverts (jumpTo "next" (tSEnd s0)) 7 hs ho
  rw [show (0 : Nat) + (7 + 1) = 8 from by omega] at hrev
  rw [h0, hstep]
  exact ⟨_, runBlocks_abort_of_block hlk1 hrev⟩

/-! ### The DJMP capstone's foundation — and why the invariant collapses its case-split

`hsupplyW_regularDjmp` is the last slice without a capstone. The feared cost was a THREE-way split on a
symbolic selector (`= 0` → `t0`, `= 1` → `t1`, out-of-range → the block errors). The invariant driver removes
it: with `djInv`'s `callvalue = 0` the selector is ALWAYS `0`, so the FIRST switch entry matches, `pre = []`,
and `hpre` is vacuous — ONE case. Same trick as `tFn` (the invariant buys away a value case-split).

`generateFnPlan djFn 0 0` emits 27 instructions (checked): `L entry(0) · CALLVALUE(1) · DUP1(2) · PUSH0(3) ·
EQ(4) · PUSH2 tramp1(5) · JUMPI(6) · DUP1(7) · PUSH1(8) · EQ(9) · PUSH2 tramp2(10) · JUMPI(11) · POP(12) ·
PUSH2 revert(13) · JUMP(14) · L tramp1(15) · POP(16) · PUSH2 t0(17) · JUMP(18) · L tramp2(19) · POP(20) ·
PUSH2 t1(21) · JUMP(22) · L t1(23) · STOP(24) · L t0(25) · STOP(26)`, with
`offsets = [(t0,36),(t1,34),(tramp2,28),(tramp1,22),(entry,0)]` and `o2pc = [(36,25),(34,23),(28,19),(22,15),
(0,0)]`. So the body plan is `[CALLVALUE]` (`bodyLen = 1+1 = 2`, chain starts at `as'.pc = 2`), `chainLen =
5*0+5+4 = 9`, and `hw : (27-25) + (2+9) = 13 ≤ 27`. Every `djmpEntryHere` leg is a concrete placement fact
(`GenBlockSimComp.lean:3354`) ⇒ `⟨by decide, rfl⟩`; note the scan entry's `PUSH0` is `AsmInst.AsmPush []`, so
`hsel : idx = djmpVal []` holds at `idx = 0`. What remains is assembling those inputs. -/

def djS : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def djD : Instruction :=
  { id := 1, opcode := Opcode.DJMP,
    operands := [Operand.Var "a", Operand.Label "t0", Operand.Label "t1"], outputs := [] }
def djEntry : BasicBlock := { label := "entry", instructions := [djS, djD] }
def djT0' : BasicBlock := { label := "t0", instructions := [stopInst] }
def djT1' : BasicBlock := { label := "t1", instructions := [stopInst] }
def djFn : IrFunction := { name := "main", blocks := [djEntry, djT0', djT1'] }
def djCtx : VenomContext := { functions := [djFn], entry := some "main" }

/-- The walk invariant for `djFn`: zero call value ⇒ the DJMP selector is `0` ⇒ the FIRST switch entry
    matches ⇒ `pre = []`, collapsing the scan to a single case. -/
def djInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0

/-- The CALLVALUE body of `djEntry` as a `RegularBodyH`, via the shared `cv_step`. -/
theorem djBody_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 1 [djS] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩

/-- `djEntry`'s body threads to the CALLVALUE state. -/
theorem djEntry_thread (s : VenomState) :
    execBodyThread [djS] 0 { s with instIdx := 0 }
      = some { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } := by
  simp [execBodyThread, djS, stepInstBase, execRead0]

/-- With a zero call value the selector is `0`, so the switch takes its FIRST entry. -/
theorem djEntry_sel (s : VenomState) (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    evalOperand (Operand.Var "a")
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      = some (EvmYul.UInt256.ofNat 0) := by
  show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
    = some (EvmYul.UInt256.ofNat 0)
  rw [lookupVar_updateVar_self, hcv]

theorem djLabels : extractLabels [Operand.Label "t0", Operand.Label "t1"] = some ["t0", "t1"] := by rfl

abbrev djSEnd (s : VenomState) : VenomState :=
  { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }

theorem djIdx_lt : (EvmYul.UInt256.ofNat 0).toNat < (["t0","t1"] : List String).length := by
  simp [EvmYul.uint256_ofNat_toNat]

/-- `djEntry`'s OK result: with a zero call value the selector picks `t0`. -/
theorem djEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false)
    (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    runBlock (1 + (j+1)) djCtx djEntry s
      = ExecResult.OK (jumpTo ((["t0","t1"] : List String).get ⟨_, djIdx_lt⟩) (djSEnd s)) :=
  runBlock_body_djmp djCtx djEntry j [djS] djD djS [djD] s (djSEnd s) (Operand.Var "a")
    [Operand.Label "t0", Operand.Label "t1"] (EvmYul.UInt256.ofNat 0) ["t0","t1"] djIdx_lt
    rfl rfl rfl (djEntry_sel s hcv) djLabels rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (djEntry_thread s) (by simpa [updateVar] using hnh)

/-- `djInv` survives every block of `djFn`. -/
theorem djInv_pres : ∀ bb ∈ djFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    djInv s → runBlock f' djCtx bb s = ExecResult.OK s' → djInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv⟩ := hinv
  simp only [djFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, djEntry, djS,
             stepInstBase, execRead0, isTerminator] at hrun
    | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, djEntry, djS,
             stepInstBase, execRead0, isTerminator] at hrun
    | (j+2) =>
      rw [show j+2 = 1+(j+1) from by omega, djEntry_runBlock s j hnh hcv] at hrun
      injection hrun with h; subst h
      exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv]⟩
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, djT0', stopInst,
             stepInstBase, isTerminator] at hrun
    | (j+1) =>
      have hrb := runBlock_body_stop djCtx djT0' j [] stopInst stopInst [] s { s with instIdx := 0 }
        rfl rfl rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
      rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
      exact absurd hrun (by simp)
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, djT1', stopInst,
             stepInstBase, isTerminator] at hrun
    | (j+1) =>
      have hrb := runBlock_body_stop djCtx djT1' j [] stopInst stopInst [] s { s with instIdx := 0 }
        rfl rfl rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
      rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
      exact absurd hrun (by simp)

/-- **The CALLVALUE body is a `RegularBodyH`** — the 0-input state-read disjunct of `RegularStepG`
    (`operands = []`, output live). Both sides read `callCtx.callvalue`; the agreement conjunct
    `fA s = fV v` is exactly `venomAsmRel`'s callCtx equality. -/
theorem cv_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 1 [cvInst2] [] := by
  exact ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩


-- hps? the body fold's resulting plan state vs psOfFn "next"
example : ((([cvInst2].zipIdx 0)).foldl
  (fun acc x => (acc.1 ++ (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg cvJmpFn x.1
      ["a"] false true "entry" acc.2).1,
    (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg cvJmpFn x.1 ["a"] false true
      "entry" acc.2).2)) ([], initPlanState 0)).2
    = psOfFn (fnPlanFuel cvJmpFn) cvJmpFn 0 0 "next" := by rfl

-- what does next's SELFDESTRUCT emit segment look like?
set_option maxHeartbeats 4000000 in

/-! ### Branching, on a real generated program with a real body

`entry: %a = CALLVALUE ; JNZ %a then else` / `then: STOP` / `else: STOP`. Same two constraints as
`cvJmpFn` (the entry block continues, and `a` is live at the JNZ because the terminator consumes it), but the
condition is now a value the BODY produced, and it is SYMBOLIC — so the proof genuinely case-splits on
`callvalue = 0` and drives both JNZ arms. -/


/-! ### A HALTING block with a real body, on the real generated program

`entry: %a = CALLVALUE ; STOP`. The output `a` is DEAD at the STOP, yet the generator emits NO `POP`, because
`isHalting = true` suppresses it (`CodegenPipeline.lean:355-359`). `bodyPlanRIP` hardcodes `isHalting := false`
and so would pop a dead output — but its `nextLiveness` is a PARAMETER, not required to be the real liveness:
it only has to make `hblock` true. Passing `["a"]` makes `dead = []`, suppressing the pop for the opposite
reason and reproducing the generator's plan exactly. (Checked both ways on the real generator: `["a"]` emits
`[CALLVALUE]` = the real body, while `[]` emits `[CALLVALUE, POP]` — a pop the generator never wrote.)

So a halting block's body IS reachable, and the constraint is narrower than "the successor must consume it":
the body fold's plan must merely agree with the generator's, which a live-marked `nextLiveness` achieves
whenever the block halts. -/

def cvStopBB : BasicBlock := { label := "entry", instructions := [cvInst2, stopInst] }
def cvStopFn : IrFunction := { name := "main", blocks := [cvStopBB] }
def cvStopCtx : VenomContext := { functions := [cvStopFn], entry := some "main" }

/-- The CALLVALUE body as a `RegularBodyH` against `cvStopFn`'s generated program. -/
theorem cvStop_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 1 [cvInst2] [] := by
  exact ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩

set_option maxHeartbeats 4000000 in
/-- **Halting capstone with a real body: `codegen_correct` for `entry: %a = CALLVALUE ; STOP`.** Single
    block, non-empty body, on the real generated `[JUMPDEST ; CALLVALUE ; STOP]`, via
    `hsupplyW_regularStop` — giving that slice its first REAL-program consumer (`hsupplyW_cdcStop` exercises
    it against a hand-written program). See the note above for why a dead output is no obstacle here. -/
theorem codegen_correct_cvStop_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 cvStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ cvStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [cvStopFn, List.mem_singleton] at hbb; subst hbb
    simp only [cvStopBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan cvStopFn 0 0
      = some ((generateFnPlan cvStopFn 0 0).get!.1, (generateFnPlan cvStopFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel cvStopFn) cvStopFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel cvStopFn) cvStopFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := cvStopCtx) (fn := cvStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan cvStopFn 0 0).get!.1) (psFinal := (generateFnPlan cvStopFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [cvStopFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, cvStopBB, cvInst2]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [cvStopFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    cases k with
    | zero =>
      exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
        getInstruction, cvStopBB, cvInst2, stepInstBase, execRead0, isTerminator]⟩
    | succ j =>
    rw [show j + 1 + 1 = ([cvInst2] : List Instruction).length + (j + 1) from by
      simp only [List.length_singleton]; omega]
    refine Or.inr (hsupplyW_regularStop
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [cvInst2]) (stopInst := stopInst) (hd := cvInst2) (tl := [stopInst])
      (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := []) (ps0 := initPlanState 0)
      (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
      (hbb := rfl) (hstopop := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
      (hthread := by simp [execBodyThread, cvInst2, stepInstBase, execRead0])
      (hreg := cvStop_regularBodyH)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl)
      (hpc := by rw [hpc0]; decide) (hstop := by simp only [hpc0]; rfl) (hw := by decide))
  case _ =>
    refine ⟨⟨cvStopBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel cvStopFn) cvStopFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan cvStopFn 0 0).get!.1)).1.length
      omega


/-! ### ✅ The LITERAL-operand body enters the recipe route — `codegen_correct_addStop_recipeW`

`addStopFn` (`entry: %c = ADD 5 3 ; STOP`) is the documented witness of §6.2's operand-class gap: its
literal ADD had NO `RegularStep` disjunct, so no `RegularBodyH` and no recipe-route capstone existed for it
(only the canonical-route `codegen_correct_canonical_addStop`). With the new both-literal commutative-binop
arm (`bodyStep_commBinopLit` / `stackDisc_commBinopLit_step_S` in `GenBlockSimComp`), the fold now covers
it: `addStop_regularBodyH` is the first `RegularBodyH` whose body is a literal-operand instruction, and the
capstone runs it end-to-end on the real generated `[JUMPDEST ; PUSH 3 ; PUSH 5 ; ADD ; STOP]`.

The dead-output wrinkle is the `cvStop` one: `c` is dead at the STOP, the generator suppresses the POP via
`isHalting`, and `nextLiveness := ["c"]` makes the fold's plan agree with the generator's (dead = []).

Scope honesty: this closes the operand-class gap for the COMMUTATIVE BOTH-LITERAL binop — the shape the
documented witness has. Mixed Var/Lit operands and the non-commutative/unop/ternop literal shapes remain
outside the fold (each would be its own disjunct + sim; the mixed shapes also need DUP-vs-PUSH interleaving
lemmas that do not exist yet). -/

theorem addStop_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 1 [addInst] [] := by
  refine ⟨Or.inl ⟨Or.inl ?_, by decide⟩, trivial⟩
  exact ⟨"c", "ADD", rfl, rfl, by decide, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨UInt256.ofNat 5, UInt256.ofNat 3, (· + ·), rfl,
      fun v => rfl, rfl, by decide, fun _ h hg => asmStep_add_ok h hg⟩))))⟩

theorem codegen_correct_addStop_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 addStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ addStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [addStopFn, List.mem_singleton] at hbb; subst hbb
    simp only [addStopBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan addStopFn 0 0
      = some ((generateFnPlan addStopFn 0 0).get!.1, (generateFnPlan addStopFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel addStopFn) addStopFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel addStopFn) addStopFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := addStopCtx) (fn := addStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan addStopFn 0 0).get!.1) (psFinal := (generateFnPlan addStopFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [addStopFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, addStopBB, addInst]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [addStopFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    cases k with
    | zero =>
      exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
        getInstruction, addStopBB, addInst, stepInstBase, execPure2, evalOperand, isTerminator]⟩
    | succ j =>
    rw [show j + 1 + 1 = ([addInst] : List Instruction).length + (j + 1) from by
      simp only [List.length_singleton]; omega]
    refine Or.inr (hsupplyW_regularStop
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [addInst]) (stopInst := stopInst) (hd := addInst) (tl := [stopInst])
      (nextLiveness := ["c"]) (curBbLabel := "entry") (dem := 1) (S := []) (ps0 := initPlanState 0)
      (sEnd := { updateVar "c" (UInt256.ofNat 5 + UInt256.ofNat 3) { s with instIdx := 0 } with
        instIdx := 1 })
      (hbb := rfl) (hstopop := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
      (hthread := by simp [execBodyThread, addInst, stepInstBase, execPure2, evalOperand])
      (hreg := addStop_regularBodyH)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 3 := hj; interval_cases j <;> rfl)
      (hpc := by rw [hpc0]; decide) (hstop := by simp only [hpc0]; rfl) (hw := by decide))
  case _ =>
    refine ⟨⟨addStopBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel addStopFn) addStopFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length
      omega


/-! ### ✅ MIXED Var/Lit operands enter the body fold — `mxVarLit_regularBodyH` / `mxLitVar_regularBodyH`

`addStopFn`'s `ADD 5 3` closed the *both-literal* case; the residual listed honestly at the time was
**mixed Var/Lit**, which additionally needs "DUP-and-PUSH interleaving lemmas that do not exist yet".
They exist now (`emitInputPlan_pair_litVar_sim` / `emitInputPlan_pair_varLit_sim`), and `RegularStep`
carries a disjunct for each mixed order, dispatched by `bodyStep_commBinop{VarLit,LitVar}`.

**Finding a real generated program that exercises them took one observation.** A var operand is
DUP'd only when it is LIVE after its instruction — `emitOneInput` emits nothing for a dead var (it is
already on the stack and is consumed in place). So *no straight-line block ending in STOP can ever
exercise a var-input arm*: the var's last use is the instruction itself, so it is dead there and no
DUP is emitted. (Measured, not assumed: `entry: %a = CALLVALUE ; %c = ADD %a, 5 ; STOP` generates
`[JUMPDEST ; CALLVALUE ; PUSH 5 ; ADD ; STOP]` — no DUP, hence nothing for a mixed arm to witness.
The same obstruction applies to the *pre-existing* all-var arm, which is why no whole-program witness
for that one exists either.) Routing the value into a successor block is what keeps it live:

```
entry:  %a = CALLVALUE ; %c = ADD %a, 5 ; JMP next
next:   RETURN %a, %c
```

Both `a` and `c` are live out of `entry`, and the generator does emit the interleaved
`PUSH 5 ; DUP2 ; ADD` (mirror form `ADD 5, %a` ⇒ `DUP1 ; PUSH 5 ; ADD`): the entry block's plan is
`[SOLabel entry ; CALLVALUE ; PUSH 5 ; DUP2 ; ADD ; PUSHLABEL next ; JUMP]`, join reorder nil.

**Scope honesty — read this before quoting these two.** A `RegularBodyH` says the fold's arms are
INHABITED for this body against this program; it does NOT by itself check that the plan the fold
builds is the program the generator emitted (that check is the consumer's `hblock`). These two have
no consumer, so the emitted shape is pinned separately and machine-checked by `mxVarLit_asm` /
`mxLitVar_asm` below — otherwise the `PUSH 5 ; DUP2 ; ADD` claim above would rest on `#eval` alone.

The load-bearing, end-to-end consumption is `codegen_correct_mxMulVarLit_recipeW` (`RecipeFinal`),
which is the `[Var x, Lit b]` order on MUL. **The `[Lit a, Var y]` order has the fold arm, the
producer and the witnesses here, but no whole-function capstone** — the mirror capstone is
mechanical (the two slices it needs are the same ones) and is not claimed. -/

def mxCv : Instruction :=
  { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
/-- `%c = ADD %a, 5` — the `[Var x, Lit b]` mixed order (compiled `PUSH 5 ; DUP2 ; ADD`). -/
def mxAddVL : Instruction :=
  { id := 1, opcode := Opcode.ADD,
    operands := [Operand.Var "a", Operand.Lit (UInt256.ofNat 5)], outputs := ["c"] }
/-- `%c = ADD 5, %a` — the `[Lit a, Var y]` mixed order (compiled `DUP1 ; PUSH 5 ; ADD`). -/
def mxAddLV : Instruction :=
  { id := 1, opcode := Opcode.ADD,
    operands := [Operand.Lit (UInt256.ofNat 5), Operand.Var "a"], outputs := ["c"] }
def mxJmp : Instruction :=
  { id := 2, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def mxRet : Instruction :=
  { id := 3, opcode := Opcode.RETURN,
    operands := [Operand.Var "a", Operand.Var "c"], outputs := [] }

def mxVarLitFn : IrFunction := { name := "main", blocks :=
  [{ label := "entry", instructions := [mxCv, mxAddVL, mxJmp] },
   { label := "next", instructions := [mxRet] }] }
def mxLitVarFn : IrFunction := { name := "main", blocks :=
  [{ label := "entry", instructions := [mxCv, mxAddLV, mxJmp] },
   { label := "next", instructions := [mxRet] }] }

/-- **The generator really does interleave `PUSH` and `DUP` for `ADD %a, 5`.** The claim the section
    header makes, as a theorem rather than an `#eval`: the emitted asm is
    `PUSH 5 ; DUP2 ; ADD`, with the var DUP'd from the *already-pushed* stack (depth 1 ⇒ `DUP2`).
    Stated with the kernel-stuck `encodeNumBytes 5` verbatim — the list spine reduces around it, so
    this closes by `rfl` (see `encodeNumBytes_lt256` in `RecipeFinal` for why it must be). -/
theorem mxVarLit_asm : executePlan (generateFnPlan mxVarLitFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmPush (encodeNumBytes 5),
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "ADD", AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP",
     AsmInst.AsmLabel "next", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "RETURN"] := by rfl

/-- The mirror shape fact: `ADD 5, %a` emits `DUP1 ; PUSH 5 ; ADD` — var first, so it is DUP'd from
    the *original* stack (depth 0 ⇒ `DUP1`) and the literal is pushed on top of it. Together with
    `mxVarLit_asm` this pins both interleavings on real generator output. -/
theorem mxLitVar_asm : executePlan (generateFnPlan mxLitVarFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP1",
     AsmInst.AsmPush (encodeNumBytes 5), AsmInst.AsmOp "ADD", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "RETURN"] := by rfl

/-- **The mixed `[Var x, Lit b]` body as a `RegularBodyH`** against `mxVarLitFn`'s generated program —
    the first `RegularBodyH` whose body contains a var-operand instruction the generator actually
    DUPs, and the first user of the `bodyStep_commBinopVarLit` arm. `S` threads `[] ↦ ["a"]`; the
    ADD reads `a` out of `S` and appends `c`. -/
theorem mxVarLit_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan mxVarLitFn 0 0).get!.1)).1 1 [mxCv, mxAddVL] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "ADD", rfl, rfl, by decide, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨"a", UInt256.ofNat 5, (· + ·), rfl, fun _ => rfl, rfl, by decide, by decide,
       fun _ h hg => asmStep_add_ok h hg⟩)))))⟩

/-! ### The CONSUMING regime, pinned on real generator output

Everything above is the *duplicating* regime — operands stay live, get DUP'd, stack grows. When an
operand's last use IS the instruction, the generator emits nothing for it and the opcode eats it off
the stack. `dead{Top,Buried}_asm` pin two generator-output shapes as theorems (so the claim is
checked, not `#eval`'d) — and BOTH turn out to be cases the arm below does NOT cover:

* `deadTopFn` = `[cv c, cv a, cv b, ADD %a %b, …]` ⇒ stack `[c, a, b]` = `base ++ [x, y]` — the
  **MIRROR** order (operands `[Var x, Var y]` with `x`=a *below* `y`=b). Compiles to a bare `ADD`,
  but the asm then computes `f y x` where Venom computes `f x y`.
* `deadBuriedFn` — operands buried under a live value ⇒ `SWAP1 ; SWAP1 ; SWAP2` first, then `ADD`.

`stackDisc_commBinopDead_step_S` covers the OTHER order, `S = base ++ [y, x]` (`x` on top) `↦
base ++ [out]`, one shorter. That config is non-vacuous — a hand-built PlanState with stack
`[c, b, a]` and operands `[a, b]` makes `generateRegularInstPlan` return `(["ADD"], [%c, %d])`, a
bare shrinking `ADD`. **But measured (2026-07-21): no whole FUNCTION's generator naturally reaches
the arm's `base ++ [y, x]` bare** — a function whose def-order would give `[c, b, a]` instead emits a
`SWAP1` before the `ADD`. So the two shapes a real generator DOES emit bare are the mirror
(`deadTopFn`) and the buried (`deadBuriedFn`), neither of which this arm handles.

⇒ Two honest limits, and together they are why there is no consuming whole-function capstone yet:
* the **mirror** order needs commutativity of `f` *as a function* (strictly stronger than the
  `isCommutative` opcode flag), its own arm — like `VarLit`/`LitVar`;
* the **buried** order needs the reorder threaded.
One of those must land before a consuming body reaches `codegen_correct` end-to-end.

**How far a consuming body actually gets.** `BodyStep`'s hardcoded `StackIsVars (S ++ [outOf x])` was
the blocker and is lifted, and the chain is closed as far as the STOP terminator:

    bodyStepHTo_commBinopDead → BodyStepsReadyHTo → labelThenBody_simTo → hsupplyW_regularStopTo
      → TermRecipeW → codegen_correct_ofBlocks_recipeW

The `To` variants are additive: each original (`labelThenBody_sim`, `hsupplyW_regularStop`) is now a
corollary at `Sn = S ++ flatMap outsOf` with its signature unchanged, so every existing caller is
untouched. **The other six `hsupplyW_regular*` slices still take `RegularBodyH`** — generalising them
is the same two-line change each, and is not claimed here. -/

def dCv0 : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }
def dCv1 : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def dCv2 : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def dAdd : Instruction :=
  { id := 3, opcode := Opcode.ADD, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["d"] }
def dStore : Instruction :=
  { id := 4, opcode := Opcode.SSTORE, operands := [Operand.Var "c", Operand.Var "d"], outputs := [] }

/-- `%a`,`%b` defined immediately before the ADD ⇒ already the top two. -/
def deadTopFn : IrFunction := { name := "main", blocks :=
  [{ label := "entry", instructions := [dCv0, dCv1, dCv2, dAdd, dStore, stopInst] }] }
/-- `%a`,`%b` defined first, then `%c` on top of them ⇒ buried. -/
def deadBuriedFn : IrFunction := { name := "main", blocks :=
  [{ label := "entry", instructions := [dCv1, dCv2, dCv0, dAdd, dStore, stopInst] }] }

/-- **Dead operands already on top are consumed with no emission at all** — the ADD's inputs cost
    zero instructions, and the stack shrinks from `[c,a,b]` to `[c,d]`. -/
theorem deadTop_asm : executePlan (generateFnPlan deadTopFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "ADD", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"] := by rfl

/-- **Buried dead operands are reordered to the top first**, then consumed in place — so consumption
    is positional, which is what makes `S = base ++ [y,x] ↦ base ++ [out]` well defined. -/
theorem deadBuried_asm : executePlan (generateFnPlan deadBuriedFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "SWAP2", AsmInst.AsmOp "ADD", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"] := by rfl

/-- **The mixed `[Lit a, Var y]` body as a `RegularBodyH`** against `mxLitVarFn`'s generated program —
    the mirror witness (`DUP1 ; PUSH 5 ; ADD`), the only user of the `bodyStep_commBinopLitVar` arm.
    This order has no whole-function capstone; see the section header. -/
theorem mxLitVar_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan mxLitVarFn 0 0).get!.1)).1 1 [mxCv, mxAddLV] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "ADD", rfl, rfl, by decide, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨"a", UInt256.ofNat 5, (· + ·), rfl, fun _ => rfl, rfl, by decide, by decide,
       fun _ h hg => asmStep_add_ok h hg⟩)))))⟩

/-! ### ✅ THE FIRST LOOP THROUGH THE FUEL ROUTE — `codegen_correct_loopVFn_fuel` (§6.2 item (2))

`loopVFn` is `entry: %a = CALLVALUE ; JNZ %a entry exit` / `exit: STOP` — its CFG has a REAL back-edge
(`loopVFn_back_edge`: `entry` is its own successor). The ranked drivers provably cannot touch it: the
taken arm's decrease `wOf entry + blockLen ≤ wOf entry` forces `blockLen = 0`, contradicting the block's
own JUMPDEST (`ranked_walk_no_back_edge`). This is the note at the end of `GenBlockSim.lean` made good:
"no loop has been driven end to end through `codegen_correct_fuel_sched`" — now one has.

The proof drives BOTH JNZ arms on the real generated
`[JUMPDEST; CALLVALUE; PUSH(→0); JUMPI; PUSH(→6); JUMP; JUMPDEST; STOP]`:
the not-taken arm falls through to `exit` (blockLen 6 ≤ B = 8), and the TAKEN arm — the back-edge —
lands the asm back at pc 0 with the entry relation re-established (blockLen 4 ≤ 8). No label ordering is
used anywhere; the budget is `fuel * 8`, decreasing with the Venom fuel exactly as
`runBlocks_walk_fuel`'s invariant prescribes. The per-block obligations are assembled BY HAND from the
primitive sims (`labelThenBody_sim`, `resolved_jumpi_{taken,nottaken}_sim`, `resolved_jump_sim`,
`runBlock_body_jnz_{taken,nottaken}`, `HbsimMatch_stop_from_body`); the fuel-shaped analogue of the
ranked `hsupplyW_*`/`TermRecipeW` slice family is enumerable follow-up, not a design gap.

NON-VACUITY (`| _ => True` catch-all): for `callvalue = 0` the run takes the fall-through and
`runContext 10` evaluates to `Halt` — the REAL arm — with the asm halting within `10 * 8` steps
(both `#eval`-checked). For `callvalue ≠ 0` the loop never terminates, Venom runs out of fuel, and the
conclusion is honestly silent (`Error` hits the catch-all) — the statement speaks only about runs that
finish, which is what fuel-indexed correctness means. The TAKEN arm is nonetheless genuinely exercised:
the `by_cases` discharges it for every non-zero call value, which no ranked instantiation could do at
all. -/

def loopVJnz : Instruction :=
  { id := 1, opcode := Opcode.JNZ,
    operands := [Operand.Var "a", Operand.Label "entry", Operand.Label "exit"], outputs := [] }
def loopVEntry : BasicBlock := { label := "entry", instructions := [cvInst2, loopVJnz] }
def loopVExit : BasicBlock := { label := "exit", instructions := [stopInst] }
def loopVFn : IrFunction := { name := "main", blocks := [loopVEntry, loopVExit] }
def loopVCtx : VenomContext := { functions := [loopVFn], entry := some "main" }

/-- The back-edge is real: `entry` is its own CFG successor. -/
theorem loopVFn_back_edge : "entry" ∈ (cfgAnalyze loopVFn).succsOf "entry" := by decide

set_option maxRecDepth 100000 in
theorem codegen_correct_loopVFn_fuel {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {fuel : Nat}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext fuel loopVCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (fuel * 8) (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (fuel * 8) (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (fuel * 8) (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_fuel_sched (B := 8) (lo := lo)
    (fuel := fuel) (ctx := loopVCtx) (fn := loopVFn) (fnEom := 0) (lblCtr := 0)
    (ops := (generateFnPlan loopVFn 0 0).get!.1) (psFinal := (generateFnPlan loopVFn 0 0).get!.2)
    (entryName := "main") (entryLbl := "entry")
    (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel loopVFn) loopVFn 0 0)
    rfl rfl rfl rfl ?hnd ?hwf ?hstep loopVEntry rfl ?hpc0 hvshalt ?hrel0
  case hnd => decide
  case hwf =>
    intro b hb inst hinst hterm
    simp only [loopVFn, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [loopVEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl
      · exact absurd hterm (by decide)
      · rfl
    · simp only [loopVExit, List.mem_singleton] at hinst; subst hinst; rfl
  case hpc0 => rw [haspc]; decide
  case hrel0 =>
    show venomAsmRel lo (psOfFn (fnPlanFuel loopVFn) loopVFn 0 0 loopVEntry.label) _ as
    rw [show psOfFn (fnPlanFuel loopVFn) loopVFn 0 0 loopVEntry.label = initPlanState 0 from by decide]
    exact hrel
  case hstep =>
    intro bb s asm N f' hlk hpc hvrel hBN hnh _hreach
    obtain ⟨hmem, hlbleq⟩ := lookupBlock_mem hlk
    simp only [loopVFn, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · -- ===== ENTRY: %a = CALLVALUE ; JNZ %a entry exit =====
      have hpcE : asm.pc = 0 := hpc.trans (by decide)
      have hvrelE : venomAsmRel lo (initPlanState 0) s asm := by
        have h := hvrel
        rwa [show psOfFn (fnPlanFuel loopVFn) loopVFn 0 0 loopVEntry.label = initPlanState 0 from
          by decide] at h
      match f' with
      | 0 =>
        have h0 : runBlock 0 loopVCtx loopVEntry s = ExecResult.Error "out of fuel" := by
          simp [runBlock, evalPhis, execBlock, loopVEntry, cvInst2]
        rw [h0]; exact trivial
      | 1 =>
        have h1 : runBlock 1 loopVCtx loopVEntry s = ExecResult.Error "out of fuel" := by
          simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, loopVEntry,
            cvInst2, loopVJnz, stepInstBase, execRead0, isTerminator]
        rw [h1]; exact trivial
      | (j+2) =>
        rw [show j + 2 = 1 + (j + 1) from by omega]
        obtain ⟨as', hbody, hrel', hpcas⟩ := labelThenBody_sim
          (o2pc := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2) (prog := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1)
          (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := loopVFn)
          (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (ps0 := initPlanState 0)
          (S := []) (bb := loopVEntry) (front := [cvInst2])
          (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          (by simp [execBodyThread, cvInst2, stepInstBase, execRead0])
          ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩
          ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩
          (by simp [StackIsVars, initPlanState])
          hvrelE
          (by rw [hpcE]; refine ⟨by decide, fun i hi => ?_⟩
              have hi' : i < 1 := hi; interval_cases i; rfl)
          (by rw [hpcE]; refine ⟨by decide, fun i hi => ?_⟩
              have hi' : i < 1 := hi; interval_cases i; rfl)
        have has'pc : as'.pc = 2 := by rw [hpcas, hpcE]; rfl
        have hstk_c : as'.stack = s.callCtx.callvalue :: as'.stack.drop 1 :=
          venomAsmRel_asmStack_top1_var hrel' rfl
            (by show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
                  = some s.callCtx.callvalue
                exact lookupVar_updateVar_self _ _ _)
        have hsucc' : venomAsmRel lo (initPlanState 0)
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
            { as' with stack := as'.stack.drop 1 } :=
          venomAsmRel_pop_tos hrel' hstk_c
        have hlt2 : as'.pc < (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.length := by rw [has'pc]; decide
        have hpushE : (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.get ⟨as'.pc, hlt2⟩
            = resolveInst (computeLabelOffsets (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (AsmInst.AsmPushLabel "entry") := by
          conv_lhs => rw [show (⟨as'.pc, hlt2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext has'pc]
          rfl
        have hlt3 : as'.pc + 1 < (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.length := by rw [has'pc]; decide
        have hjumpi : (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.get ⟨as'.pc + 1, hlt3⟩ = AsmInst.AsmOp "JUMPI" := by
          conv_lhs => rw [show (⟨as'.pc + 1, hlt3⟩ : Fin _) = ⟨3, by decide⟩ from
            Fin.ext (show as'.pc + 1 = 3 by rw [has'pc])]
          rfl
        by_cases hc : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0
        · -- NOT TAKEN: fall through to exit
          have hrb := runBlock_body_jnz_nottaken loopVCtx loopVEntry j [cvInst2] loopVJnz cvInst2
            [loopVJnz] s { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with
              instIdx := 1 }
            (Operand.Var "a") "entry" "exit" rfl rfl rfl
            (by show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
                  = some (EvmYul.UInt256.ofNat 0)
                rw [lookupVar_updateVar_self, hc]) rfl (by decide)
            (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
            (by simp [execBodyThread, cvInst2, stepInstBase, execRead0])
            (by simpa [updateVar] using hnh)
          simp only [List.length_singleton] at hrb
          rw [hrb]
          have hh' : (jumpTo "exit" ({ updateVar "a" s.callCtx.callvalue
              { s with instIdx := 0 } with instIdx := 1 })).halted = false := by
            simpa [jumpTo, updateVar] using hnh
          simp only [hh', Bool.false_eq_true, if_false]
          have hnt := resolved_jumpi_nottaken_sim (offsets := (computeLabelOffsets (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2)
            (offsetToPc := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2) (prog := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1) (s := as') (ifNz := "entry") (off := 0)
            (stk := as'.stack.drop 1) (hc ▸ hstk_c) hlt2 hpushE (by decide) (by decide)
            hlt3 hjumpi
          have ha1pc : ({ as' with stack := as'.stack.drop 1, pc := as'.pc + 2 } : AsmState).pc = 4 := by
            show as'.pc + 2 = 4; rw [has'pc]
          have hlt4 : ({ as' with stack := as'.stack.drop 1, pc := as'.pc + 2 } : AsmState).pc
              < (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.length := by rw [ha1pc]; decide
          have hpushX : (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.get ⟨_, hlt4⟩ = resolveInst (computeLabelOffsets (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (AsmInst.AsmPushLabel "exit") := by
            conv_lhs => rw [show (⟨_, hlt4⟩ : Fin _) = ⟨4, by decide⟩ from Fin.ext ha1pc]
            rfl
          have hlt5 : ({ as' with stack := as'.stack.drop 1, pc := as'.pc + 2 } : AsmState).pc + 1
              < (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.length := by rw [ha1pc]; decide
          have hjmp : (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.get ⟨_, hlt5⟩ = AsmInst.AsmOp "JUMP" := by
            conv_lhs => rw [show (⟨_, hlt5⟩ : Fin _) = ⟨5, by decide⟩ from
              Fin.ext (show _ + 1 = 5 by rw [ha1pc])]
            rfl
          have hj := resolved_jump_sim (offsets := (computeLabelOffsets (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2) (offsetToPc := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2)
            (prog := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1) (s := { as' with stack := as'.stack.drop 1, pc := as'.pc + 2 })
            (target := "exit") (off := 10) (idx := 6)
            hlt4 hpushX (by decide) (by decide) hlt5 hjmp (by decide)
          have htail : runAsm 4 (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 as'
              = AsmResult.AsmOK { as' with stack := as'.stack.drop 1, pc := 6 } := by
            rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hnt]
            exact hj
          refine ⟨loopVExit, { as' with stack := as'.stack.drop 1, pc := 6 }, _, rfl,
            (runAsm_append_ok hbody).trans htail, ?_, ?_, ?_⟩
          · decide
          · show (6 : Nat) = pcOfLabel (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 loopVExit.label
            decide
          · exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hsucc')
        · -- TAKEN: the BACK-EDGE, entry -> entry
          have hrb := runBlock_body_jnz_taken loopVCtx loopVEntry j [cvInst2] loopVJnz cvInst2
            [loopVJnz] s { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with
              instIdx := 1 }
            (Operand.Var "a") "entry" "exit" s.callCtx.callvalue rfl rfl rfl
            (by show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
                  = some s.callCtx.callvalue
                exact lookupVar_updateVar_self _ _ _) hc rfl (by decide)
            (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
            (by simp [execBodyThread, cvInst2, stepInstBase, execRead0])
            (by simpa [updateVar] using hnh)
          simp only [List.length_singleton] at hrb
          rw [hrb]
          have hh' : (jumpTo "entry" ({ updateVar "a" s.callCtx.callvalue
              { s with instIdx := 0 } with instIdx := 1 })).halted = false := by
            simpa [jumpTo, updateVar] using hnh
          simp only [hh', Bool.false_eq_true, if_false]
          have ht := resolved_jumpi_taken_sim (offsets := (computeLabelOffsets (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2) (offsetToPc := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2)
            (prog := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1) (s := as') (ifNz := "entry") (off := 0) (idx := 0)
            (cond := s.callCtx.callvalue) (stk := as'.stack.drop 1)
            hstk_c hc hlt2 hpushE (by decide) (by decide) hlt3 hjumpi (by decide)
          refine ⟨loopVEntry, { as' with stack := as'.stack.drop 1, pc := 0 }, _, rfl,
            (runAsm_append_ok hbody).trans ht, ?_, ?_, ?_⟩
          · decide
          · show (0 : Nat) = pcOfLabel (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 loopVEntry.label
            decide
          · exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hsucc')
    · -- ===== EXIT: STOP =====
      have hpcX : asm.pc = 6 := hpc.trans (by decide)
      have hvrelX : venomAsmRel lo (initPlanState 0) s asm := by
        have h := hvrel
        rwa [show psOfFn (fnPlanFuel loopVFn) loopVFn 0 0 loopVExit.label = initPlanState 0 from
          by decide] at h
      match f' with
      | 0 =>
        have h0 : runBlock 0 loopVCtx loopVExit s = ExecResult.Error "out of fuel" := by
          simp [runBlock, evalPhis, execBlock, loopVExit, stopInst]
        rw [h0]; exact trivial
      | (j+1) =>
        have hrb : runBlock (j+1) loopVCtx loopVExit s
            = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
          have h := runBlock_body_stop loopVCtx loopVExit j [] stopInst stopInst [] s
            { s with instIdx := 0 } rfl rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread])
          simpa using h
        obtain ⟨as1, hrun1, hrel1, hpc1⟩ := soLabel_sim (offsetToPc := (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).2)
          lo (initPlanState 0) { s with instIdx := 0 } asm (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1 "exit" hvrelX
          (by rw [hpcX]; refine ⟨by decide, fun i hi => ?_⟩
              have hi' : i < 1 := hi; interval_cases i; rfl)
        have hlen1 : (executePlan [StackOp.SOLabel "exit"]).length = 1 := rfl
        rw [hlen1] at hrun1
        have hpc7 : as1.pc = 7 := by rw [hlen1] at hpc1; rw [hpc1, hpcX]
        have hlt7 : as1.pc < (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.length := by rw [hpc7]; decide
        have hstop7 : (asmResolve (executePlan (generateFnPlan loopVFn 0 0).get!.1)).1.get ⟨as1.pc, hlt7⟩ = AsmInst.AsmOp "STOP" := by
          conv_lhs => rw [show (⟨as1.pc, hlt7⟩ : Fin _) = ⟨7, by decide⟩ from Fin.ext hpc7]
          rfl
        have hm := HbsimMatch_stop_from_body (Entry := fun _ _ _ => True)
          hrb hrun1 hrel1 hlt7 hstop7 (by omega : 1 + 1 ≤ N)
        rw [hrb] at hm ⊢
        exact hm

def invInst2 : Instruction := { id := 3, opcode := Opcode.INVALID, operands := [], outputs := [] }
def cvInvBB : BasicBlock := { label := "entry", instructions := [cvInst2, invInst2] }
def cvInvFn : IrFunction := { name := "main", blocks := [cvInvBB] }
def cvInvCtx : VenomContext := { functions := [cvInvFn], entry := some "main" }

/-- The CALLVALUE body as a `RegularBodyH` against `cvInvFn`'s generated program. -/
theorem cvInv_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 1 [cvInst2] [] := by
  exact ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩

set_option maxHeartbeats 4000000 in
/-- **Aborting capstone with a real body: `entry: %a = CALLVALUE ; INVALID`.** The `AsmFault` twin of
    `codegen_correct_cvStop_recipeW`, on the real generated `[JUMPDEST ; CALLVALUE ; INVALID]`, via
    `hsupplyW_regularInvalid` — its first consumer. Same reason the dead output is no obstacle (fact 3). -/
theorem codegen_correct_cvInv_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 cvInvCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ cvInvFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [cvInvFn, List.mem_singleton] at hbb; subst hbb
    simp only [cvInvBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan cvInvFn 0 0
      = some ((generateFnPlan cvInvFn 0 0).get!.1, (generateFnPlan cvInvFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel cvInvFn) cvInvFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel cvInvFn) cvInvFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := cvInvCtx) (fn := cvInvFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan cvInvFn 0 0).get!.1) (psFinal := (generateFnPlan cvInvFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [cvInvFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, cvInvBB, cvInst2]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [cvInvFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    cases k with
    | zero =>
      exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
        getInstruction, cvInvBB, cvInst2, stepInstBase, execRead0, isTerminator]⟩
    | succ j =>
    rw [show j + 1 + 1 = ([cvInst2] : List Instruction).length + (j + 1) from by
      simp only [List.length_singleton]; omega]
    refine Or.inr (hsupplyW_regularInvalid
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [cvInst2]) (invInst := invInst2) (hd := cvInst2) (tl := [invInst2])
      (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := []) (ps0 := initPlanState 0)
      (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
      (hbb := rfl) (hinvop := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
      (hthread := by simp [execBodyThread, cvInst2, stepInstBase, execRead0])
      (hreg := cvInv_regularBodyH)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl)
      (hpc := by rw [hpc0]; decide) (hinv := by simp only [hpc0]; rfl) (hw := by decide))
  case _ =>
    refine ⟨⟨cvInvBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel cvInvFn) cvInvFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan cvInvFn 0 0).get!.1)).1.length
      omega

def cvJnzInst : Instruction :=
  { id := 1, opcode := Opcode.JNZ,
    operands := [Operand.Var "a", Operand.Label "then", Operand.Label "else"], outputs := [] }
def cvJnzEntry : BasicBlock := { label := "entry", instructions := [cvInst2, cvJnzInst] }
def cvThenBB : BasicBlock := { label := "then", instructions := [stopInst] }
def cvElseBB : BasicBlock := { label := "else", instructions := [stopInst] }
def cvJnzFn : IrFunction := { name := "main", blocks := [cvJnzEntry, cvThenBB, cvElseBB] }
def cvJnzCtx : VenomContext := { functions := [cvJnzFn], entry := some "main" }

/-- The CALLVALUE body as a `RegularBodyH` against `cvJnzFn`'s generated program (same disjunct and same
    proof as `cv_regularBodyH`; only the program and `fn` differ). -/
theorem cvJnz_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 1 [cvInst2] [] := by
  exact ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩

/-- **The frontier capstone: whole-function `codegen_correct` on a REAL generated program with a NON-EMPTY
    body, via the recipe route.** Every earlier recipe-route capstone had empty-bodied blocks (only
    instruction = terminator); the one existing non-empty-body capstone (`codegen_correct_canonical_addStop`)
    hand-rolls its asm run because its body is literal-operand and so outside the body fold entirely.

    Here `entry: %a = CALLVALUE ; JMP next` goes through the generic chain — `hsupplyW_regularJmp` →
    `soLabel_sim` ∘ `genBlockBodyH_sim_inv` ∘ `termRecipeW_jmp_of_body` — with the body's `RegularBodyH`
    supplied by `cv_regularBodyH`, and `next: SELFDESTRUCT %a` through `hsupplyW_emptySelfdestructDead`.
    Both blocks are discharged against the program the compiler actually emits.

    Two things make it fit where the obvious candidates do not: the entry block CONTINUES (so
    `bbIsHalting = false`, matching `bodyPlanRIP`'s hardcoded `isHalting`), and `a` is live at the JMP
    because the successor consumes it (so the state-read disjunct's `nextLiveness.contains out = true` holds
    of the REAL liveness). The successor-recording obligation `hps` — the body fold's resulting plan state IS
    `psOfFn "next"` — closes by `rfl` on the real generator. -/
theorem codegen_correct_cvJmp_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 cvJmpCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ cvJmpFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [cvJmpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [cvEntryBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [sdNextBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan cvJmpFn 0 0
      = some ((generateFnPlan cvJmpFn 0 0).get!.1, (generateFnPlan cvJmpFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel cvJmpFn) cvJmpFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo)
    (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel cvJmpFn) cvJmpFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
      - pcOfLabel (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := cvJmpCtx) (fn := cvJmpFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan cvJmpFn 0 0).get!.1) (psFinal := (generateFnPlan cvJmpFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [cvJmpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, cvEntryBB, cvInst2]
    · simp [runBlock, evalPhis, execBlock, sdNextBB, sdAInst]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    have hbb2 : bb = cvEntryBB ∨ bb = sdNextBB := by
      simp only [cvJmpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
    rcases hbb2 with hbb | hbb <;> subst hbb
    · -- entry: CALLVALUE body + JMP  (the NON-EMPTY body, on the REAL generated program)
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      -- the 2-instruction block (CALLVALUE ; JMP) needs fuel ≥ 2; at k = 0 the driver takes the error arm
      cases k with
      | zero =>
        exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction,
          cvEntryBB, cvInst2, stepInstBase, execRead0, isTerminator]⟩
      | succ j =>
      rw [show j + 1 + 1 = ([cvInst2] : List Instruction).length + (j + 1) from by simp only [List.length_singleton]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (restFuel := j)
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg)
        (front := [cvInst2]) (jmpInst := jmpNextInst) (hd := cvInst2) (tl := [jmpNextInst])
        (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 6) (bb' := sdNextBB)
        (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := ?_) (hnothalt := ?_) (hreg := cv_regularBodyH)
        (hsd := ?_) (hsv := by simp [StackIsVars, initPlanState]) (hrel := ?_)
        (hbLabel := ?_) (hblock := ?_) (hps := ?_) (hpc := ?_) (hpush := ?_)
        (hoff_lk := ?_) (hoff := ?_) (hpc2 := ?_) (hjump := ?_)
        (hidx_lk := ?_) (hlk' := rfl) (hw := ?_))
      · -- hthread
        simp [execBodyThread, cvInst2, stepInstBase, execRead0]
      · -- hnothalt
        simpa [updateVar] using hhalt
      · -- hsd
        exact ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩
      · -- hrel
        rw [hpsE] at hvrel; exact hvrel
      · -- hbLabel
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      · -- hblock
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      · -- hps
        rfl
      · -- hpc
        rw [hpc0]; decide
      · -- hpush
        simp only [hpc0]; rfl
      · -- hoff_lk
        decide
      · -- hoff
        decide
      · -- hpc2
        rw [hpc0]; decide
      · -- hjump
        simp only [hpc0]; rfl
      · -- hidx_lk
        decide
      · -- hw
        decide
    · -- next: SELFDESTRUCT %a (operand dead ⇒ consumed in place)
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc4 : asm.pc = 4 := by rw [hpc_asm]; decide
      obtain ⟨waddr, hwa⟩ := venomAsmRel_stack_defined hvrel "a" (by decide)
      refine Or.inr (hsupplyW_emptySelfdestructDead (sdInst := sdAInst) (addrv := "a")
        (waddr := waddr) (base := []) (ps := psOfFn (fnPlanFuel cvJmpFn) cvJmpFn 0 0 "next")
        rfl rfl rfl hwa hwa rfl hvrel ?_ ?_ ?_ (by decide))
      · rw [hpc4]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      · rw [hpc4]; decide
      · have e : asm.pc + 1 = 5 := by rw [hpc4]
        conv_lhs => rw [show (⟨asm.pc + 1, by rw [hpc4]; decide⟩ : Fin _) = ⟨5, by decide⟩ from Fin.ext e]
        rfl
  case _ =>
    refine ⟨⟨cvEntryBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel cvJmpFn) cvJmpFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1 "entry"
          ≤ (asmResolve (executePlan (generateFnPlan cvJmpFn 0 0).get!.1)).1.length
      omega


set_option maxHeartbeats 4000000 in
/-- **Branching capstone: `codegen_correct` on a real generated program with a real body, both JNZ arms.**
    `entry: %a = CALLVALUE ; JNZ %a then else` / `then: STOP` / `else: STOP`, emitted as
    `[LABEL entry; CALLVALUE; PUSHLBL then; JUMPI; PUSHLBL else; JUMP; LABEL else; STOP; LABEL then; STOP]`.
    The condition is a value the BODY produced and is SYMBOLIC, so the proof case-splits on
    `callvalue = 0` and drives BOTH `hsupplyW_regularJnz{Taken,Nottaken}` — the taken arm through the 2-op
    tail, the fall-through arm through the 4-op tail. The successors are empty-bodied STOPs
    (`hsupplyW_emptyStop`). -/
theorem codegen_correct_cvJnz_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 cvJnzCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ cvJnzFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [cvJnzFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [cvJnzEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [cvThenBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [cvElseBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan cvJnzFn 0 0
      = some ((generateFnPlan cvJnzFn 0 0).get!.1, (generateFnPlan cvJnzFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel cvJnzFn) cvJnzFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel cvJnzFn) cvJnzFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := cvJnzCtx) (fn := cvJnzFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan cvJnzFn 0 0).get!.1) (psFinal := (generateFnPlan cvJnzFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [cvJnzFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, cvJnzEntry, cvInst2]
    · simp [runBlock, evalPhis, execBlock, cvThenBB, stopInst]
    · simp [runBlock, evalPhis, execBlock, cvElseBB, stopInst]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    have hbb3 : bb = cvJnzEntry ∨ bb = cvThenBB ∨ bb = cvElseBB := by
      simp only [cvJnzFn, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
    rcases hbb3 with hbb | hbb | hbb <;> subst hbb
    · -- entry: CALLVALUE body + JNZ on the produced value
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      cases k with
      | zero =>
        exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
          getInstruction, cvJnzEntry, cvInst2, stepInstBase, execRead0, isTerminator]⟩
      | succ j =>
      rw [show j + 1 + 1 = ([cvInst2] : List Instruction).length + (j + 1) from by
        simp only [List.length_singleton]; omega]
      have hsd : StackDiscH ((([cvInst2] : List Instruction).zipIdx 0).map (fun _ => 1)).sum
          (initPlanState 0) { s with instIdx := 0 } :=
        ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩
      have hrel0 : venomAsmRel lo (initPlanState 0) { s with instIdx := 0 } asm := by
        rw [hpsE] at hvrel; exact hvrel
      have hthread : execBodyThread [cvInst2] 0 { s with instIdx := 0 }
          = some { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } := by
        simp [execBodyThread, cvInst2, stepInstBase, execRead0]
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 asm.pc (executePlan [StackOp.SOLabel cvJnzEntry.label]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      have hblock : asmBlockAt (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 (asm.pc + 1)
          (executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg cvJnzFn ["a"] "entry" [cvInst2]
            (initPlanState 0)).1) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      have hva : lookupVar "a" { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with
          instIdx := 1 } = some s.callCtx.callvalue := by
        rw [show lookupVar "a" { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with
          instIdx := 1 } = lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
          from rfl, lookupVar_updateVar_self]
      by_cases hz : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0
      · -- fall-through arm: condition is zero
        refine Or.inr (hsupplyW_regularJnzNottaken
          (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
          (front := [cvInst2]) (jnzInst := cvJnzInst) (hd := cvInst2) (tl := [cvJnzInst])
          (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := []) (base := [])
          (ps0 := initPlanState 0) (condvar := "a") (ifNz := "then") (ifZ := "else")
          (offN := 12) (offZ := 10) (bb' := cvElseBB)
          (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          (hbb := rfl) (hop := rfl) (hoperands := rfl)
          (hcondv := hva.trans (by rw [hz]; rfl)) (hval := hva.trans (by rw [hz]))
          (hcons := rfl) (hphi := by decide)
          (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
          (hthread := hthread) (hnothalt := by simpa [updateVar] using hhalt)
          (hreg := cvJnz_regularBodyH) (hsd := hsd) (hsv := by simp [StackIsVars, initPlanState])
          (hrel := hrel0) (hbLabel := hbLabel) (hblock := hblock) (hcondtos := rfl) (hpsj := rfl)
          (hpc := by rw [hpc0]; decide) (hpushN := by simp only [hpc0]; rfl)
          (hoffN_lk := ?_) (hoffN := ?_) (hpc2 := by rw [hpc0]; decide)
          (hjumpi := by simp only [hpc0]; rfl) (hpc3 := by rw [hpc0]; decide)
          (hpushZ := by simp only [hpc0]; rfl) (hoffZ_lk := ?_) (hoffZ := ?_)
          (hpc4 := by rw [hpc0]; decide) (hjump := by simp only [hpc0]; rfl)
          (hidxZ_lk := ?_) (hlk' := rfl) (hw := by decide))
        · decide
        · decide
        · decide
        · decide
        · decide
      · -- taken arm: condition is non-zero
        refine Or.inr (hsupplyW_regularJnzTaken
          (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
          (front := [cvInst2]) (jnzInst := cvJnzInst) (hd := cvInst2) (tl := [cvJnzInst])
          (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := []) (base := [])
          (ps0 := initPlanState 0) (condvar := "a") (ifNz := "then") (ifZ := "else")
          (cond := s.callCtx.callvalue) (off := 12) (bb' := cvThenBB)
          (sEnd := { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcondv := hva) (hcond_ne := hz) (hval := hva)
          (hcons := rfl) (hphi := by decide)
          (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
          (hthread := hthread) (hnothalt := by simpa [updateVar] using hhalt)
          (hreg := cvJnz_regularBodyH) (hsd := hsd) (hsv := by simp [StackIsVars, initPlanState])
          (hrel := hrel0) (hbLabel := hbLabel) (hblock := hblock) (hcondtos := rfl) (hpsj := rfl)
          (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
          (hoff_lk := ?_) (hoff := ?_) (hpc2 := by rw [hpc0]; decide)
          (hjumpi := by simp only [hpc0]; rfl) (hidx_lk := ?_) (hlk' := rfl) (hw := by decide))
        · decide
        · decide
        · decide
    · -- then: STOP
      have hlbl : s.currentBb = "then" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 asm.pc (executePlan [StackOp.SOLabel cvThenBB.label]) := by
        rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length := by rw [hpc8]; decide
      have hstop : (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt⟩ = AsmInst.AsmOp "STOP" := by
        simp only [hpc8]; rfl
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel cvJnzFn) cvJnzFn 0 0 "then") rfl rfl hvrel hbLabel hlt hstop (by decide))
    · -- else: STOP
      have hlbl : s.currentBb = "else" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 asm.pc (executePlan [StackOp.SOLabel cvElseBB.label]) := by
        rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
        have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length := by rw [hpc6]; decide
      have hstop : (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt⟩ = AsmInst.AsmOp "STOP" := by
        simp only [hpc6]; rfl
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel cvJnzFn) cvJnzFn 0 0 "else") rfl rfl hvrel hbLabel hlt hstop (by decide))
  case _ =>
    refine ⟨⟨cvJnzEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel cvJnzFn) cvJnzFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan cvJnzFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ The DJMP capstone — `codegen_correct_djFn_recipeW`

The eighth and last terminator kind reaches a whole-function `codegen_correct` on REAL generated output.
`djFn` is `entry: a = CALLVALUE ; DJMP a [t0, t1]` with `t0: STOP` and `t1: STOP`; the generator emits the
27-instruction switch below, and with `callvalue = 0` the selector picks `t0`.

Two things had to be fixed to apply `hsupplyW_regularDjmp` to the REAL generator (both found by TESTING the
lemma against generated output rather than reading it):

1. **`hpsj` was unsatisfiable here.** It demanded the successor's plan state equal the BODY plan state with
   the selector popped — on the nose, `labelCounter` included. But a DJMP emits one trampoline per target,
   and each bumps `labelCounter`: the real `psOfFn … "t0"` has `labelCounter = 2` while the body plan has `0`
   (`stack`/`spilled`/`alloc` all agree — the counter was the ONLY difference). Since `venomAsmRel` reads only
   `ps.stack`, `ps.spilled` and `ps.alloc` (`CodegenRel.lean:436-440`), the counter is irrelevant to the
   conclusion, so `hpsj` now takes an ARBITRARY `lc`. Both proofs went through unchanged — the obliviousness
   is definitional. Left as it was, `hsupplyW_regularDjmp` was sound but applied to NO real DJMP block.

2. **Layout facts need `decide +kernel`, not `decide`.** `computeLabelOffsets`/`asmResolve` on `djFn` do not
   reduce in the elaborator, so plain `decide`/`rfl` get stuck — and because a lookup compares the key against
   EVERY entry, one irreducible trampoline key (`"djmp_tramp" ++ "_" ++ toString …`) blocks even the lookup of
   a plain block label like `"t0"`. The kernel reduces all of it. (`decide +kernel` is kernel reduction — it
   adds no axiom, unlike `native_decide`.) `AsmInst` derives only `Inhabited`, so the equalities on program
   instructions need a `DecidableEq` instance; it is derived here, proof-side, rather than in `AsmIR.lean`.

The verified layout (`#eval`-checked, then proved by `decide +kernel`):

```
 0 AsmLabel entry     5 PUSH [0,22] (=djmp_tramp_1)  10 PUSH [0,28]  15 AsmLabel djmp_tramp_1
 1 CALLVALUE          6 JUMPI                        11 JUMPI        16 POP
 2 DUP1               7 DUP1                         12 POP          17 PUSH [0,36] (=t0)
 3 PUSH []  (=0)      8 PUSH [1]                     13 PUSH [0,0]   18 JUMP
 4 EQ                 9 EQ                           14 JUMP         …  t1@23, t0@25
```
`offsets "djmp_tramp_1" = 22`, `o2pc 22 = 15`, `offsets "t0" = 36`, `o2pc 36 = 25`, `|prog| = 27`.

NON-VACUITY (`| _ => True` catch-all — the arm that fires must be checked, cf. the retracted
`codegen_correct_ofRecipes`): for `vs0 := { default with currentBb := "entry", halted := false }` the
hypotheses hold (`vs0.callCtx.callvalue = 0` is `true`) and `runContext 10 djCtx vs0` is `Halt` — the REAL
arm, not the catch-all — with `runAsm … = AsmHalt` on the asm side. The conclusion has content. -/

-- `AsmInst` derives only `Inhabited` (`AsmIR.lean:28`); the layout facts above are equalities on program
-- instructions discharged by kernel reduction, which needs a `Decidable` instance. Derived proof-side so
-- no compiler file changes.
deriving instance DecidableEq for AsmInst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codegen_correct_djFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 djCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ djFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [djFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [djEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [djT0', List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [djT1', List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan djFn 0 0 = some ((generateFnPlan djFn 0 0).get!.1, (generateFnPlan djFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel djFn) djFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv djInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel djFn) djFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan djFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := djCtx) (fn := djFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan djFn 0 0).get!.1) (psFinal := (generateFnPlan djFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ djInv_pres ?_ ⟨by simpa using hvshalt, by simpa using hzero⟩
  case _ =>
    intro bb hbb s
    simp only [djFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, djEntry, djS]
    · simp [runBlock, evalPhis, execBlock, djT0', stopInst]
    · simp [runBlock, evalPhis, execBlock, djT1', stopInst]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    obtain ⟨hnh, hcv⟩ := hinv
    simp only [djFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, djEntry, djS, stepInstBase, execRead0, isTerminator]⟩
      | (j+1) =>
      rw [show j+1+1 = ([djS] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularDjmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [djS]) (dInst := djD) (hd := djS) (tl := [djD])
        (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := []) (base := [])
        (ps0 := initPlanState 0) (selvar := "a") (idx := EvmYul.UInt256.ofNat 0)
        (labelOps := [Operand.Label "t0", Operand.Label "t1"]) (labels := ["t0","t1"]) (hi := djIdx_lt)
        (pre := []) (matb := []) (tName := "djmp_tramp_1") (lName := "t0")
        (matoff := 22) (idxTramp := 15) (loff := 36) (target := 25) (lc := 2)
        (bb' := djT0') (sEnd := djSEnd s)
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hselv := djEntry_sel s hcv)
        (hlabels := djLabels) (hval := djEntry_sel s hcv) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := djEntry_thread s) (hnothalt := by simpa [updateVar] using hnh)
        (hreg := djBody_regularBodyH)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hseltos := rfl) (hpsj := by decide +kernel) (hpct := ?hpct)
        (hpre := by intro k hk; exact absurd hk (by simp))
        (hmatch := ?hmatch) (hsel := ?hsel) (hidx_lk := ?hidx_lk)
        (ht0 := ?ht0) (ht1 := ?ht1) (ht2 := ?ht2)
        (hl_lk := ?hl_lk) (hloff := ?hloff) (ht3 := ?ht3)
        (htarget_lk := ?htarget_lk) (hlk := rfl) (hw := ?hw))
      case hpct => decide +kernel
      case hmatch =>
        rw [hpc0]
        refine ⟨⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩,
                ⟨by decide +kernel, ?_⟩, by decide +kernel, by decide,
                ⟨by decide +kernel, ?_⟩⟩ <;> decide +kernel
      case hsel => decide +kernel
      case hidx_lk => decide +kernel
      case ht0 => exact ⟨by decide +kernel, by decide +kernel⟩
      case ht1 => exact ⟨by decide +kernel, by decide +kernel⟩
      case ht2 => exact ⟨by decide +kernel, by decide +kernel⟩
      case hl_lk => decide +kernel
      case hloff => decide
      case ht3 => exact ⟨by decide +kernel, by decide +kernel⟩
      case htarget_lk => decide +kernel
      case hw => decide +kernel
    · have hlbl : s.currentBb = "t0" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc25 : asm.pc = 25 := by rw [hpc_asm]; decide +kernel
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel djFn) djFn 0 0 "t0") rfl rfl hvrel
        (by rw [hpc25]; refine ⟨by decide, fun j hj => ?_⟩
            have hj' : j < 1 := hj; interval_cases j; rfl)
        (by rw [hpc25]; decide +kernel) (by simp only [hpc25]; rfl) (by decide +kernel))
    · have hlbl : s.currentBb = "t1" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc23 : asm.pc = 23 := by rw [hpc_asm]; decide +kernel
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel djFn) djFn 0 0 "t1") rfl rfl hvrel
        (by rw [hpc23]; refine ⟨by decide, fun j hj => ?_⟩
            have hj' : j < 1 := hj; interval_cases j; rfl)
        (by rw [hpc23]; decide +kernel) (by simp only [hpc23]; rfl) (by decide +kernel))
  case _ =>
    refine ⟨⟨djEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel djFn) djFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan djFn 0 0).get!.1)).1.length
      omega

/-! ### What "the recipe route models 8 terminator kinds" actually means — RET and SINK

`isTerminator` admits TEN opcodes; `TermRecipeW`'s nine arms model EIGHT of them (JNZ takes two arms:
taken and not-taken). The remaining two are NOT a uniform "out of scope" — they are excluded for two
completely different reasons, and the difference is worth pinning down rather than asserting, since it is
what the coverage claim rests on:

* **SINK is excluded UPSTREAM.** `isPreCodegenOpcode SINK = true` (`CodegenPipeline.lean:37`), so
  `codegenReadyInst` REJECTS it — `sink_not_codegenReady` below. Every capstone assumes `codegenReadyInst`,
  so no admissible function can contain a SINK: earlier passes are required to have eliminated it. This is a
  genuine, documented precondition.

* **RET is NOT excluded — the statement simply says nothing about it.** `retA_codegenReady` proves RET IS
  codegen-ready, `retA_isTerminator` that it is a real terminator, and the compiler really does emit code for
  it (`CodegenPipeline.lean:228`: `SOEmit "JUMP"`, jumping to the return address INVOKE pushed). But RET's
  semantics is `ExecResult.IntRet` (`Semantics.lean:389`) — an intra-contract return to an INVOKE caller —
  and `IntRet` is routed to a trivial arm at EVERY layer: `runBlocks` propagates it unchanged
  (`Exec.lean:171`), `HbsimMatch` sends it to `| _ => True`, `TermRecipeW` has no arm for it, and the
  capstones' own statement matches only `Halt`/`Abort Revert`/`Abort ExHalt` with `| _ => True` catching the
  rest. So for a function whose reachable terminator is RET, `codegen_correct` is VACUOUSLY TRUE.

`codegen_correct_retFn_vacuous` makes that checkable instead of merely stated: it discharges the full
capstone-shaped claim for `retFn` (`entry: RET 7`) using NO codegen machinery whatsoever — just
`rw [retFn_intret]; trivial`. Its axioms are `[propext, Classical.choice, Quot.sound]`: not one fact about
`generateFnPlan`, `asmResolve` or `runAsm` is needed, because the statement asserts nothing about them here.

So the honest reading of "8/8": the eight modelled kinds are **exactly the terminator kinds for which
`codegen_correct` has any content at all**. Of the other two, SINK cannot occur in an admissible function,
and RET can — but produces a claim with no content. Covering RET for real means a DIFFERENT statement, one
relating `IntRet`'s returned values to the asm side at the INVOKE boundary; that is not a missing recipe
arm, it is a missing theorem shape. -/

theorem runBlock_body_ret (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (retInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (ops : List Operand) (vals : List bytes32)
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RET)
    (hoperands : retInst.operands = ops) (hvals : evalOperands ops sEnd = some vals)
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.IntRet vals sEnd := by
  refine runBlock_body_term ctx bb restFuel front retInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hvals]

def retA : Instruction :=
  { id := 0, opcode := Opcode.RET, operands := [Operand.Lit (EvmYul.UInt256.ofNat 7)], outputs := [] }
def retEntry : BasicBlock := { label := "entry", instructions := [retA] }
def retFn : IrFunction := { name := "main", blocks := [retEntry] }
def retCtx : VenomContext := { functions := [retFn], entry := some "main" }

/-- RET is **codegen-ready** — it is NOT excluded upstream. -/
theorem retA_codegenReady : codegenReadyInst retA := by unfold codegenReadyInst; decide

/-- RET is a genuine terminator, and the compiler really emits code for it
    (`CodegenPipeline.lean:228`: `SOEmit "JUMP"`). -/
theorem retA_isTerminator : isTerminator retA.opcode = true := by decide

/-- SINK, by contrast, IS excluded upstream: `isPreCodegenOpcode SINK = true`. -/
theorem sink_not_codegenReady :
    ¬ codegenReadyInst { id := 0, opcode := Opcode.SINK, operands := [], outputs := [] } := by
  unfold codegenReadyInst; decide

theorem retEntry_intret (s : VenomState) (j : Nat) :
    runBlock (0 + (j + 1)) retCtx retEntry s
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 7] { s with instIdx := 0 } :=
  runBlock_body_ret retCtx retEntry j [] retA retA [] s { s with instIdx := 0 }
    [Operand.Lit (EvmYul.UInt256.ofNat 7)] [EvmYul.UInt256.ofNat 7]
    rfl rfl rfl rfl rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])

theorem retFn_intret (vs : VenomState) :
    runContext 10 retCtx vs
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 7]
          { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
  have h0 : runContext 10 retCtx vs
      = runBlocks 10 retCtx retFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, retCtx, retFn, lookupFunction, fnEntryLabel, retEntry]
  have hlk : lookupBlock ({ vs with prevBb := none, currentBb := "entry", instIdx := 0 } : VenomState).currentBb
      retFn.blocks = some retEntry := rfl
  have hb := retEntry_intret { vs with prevBb := none, currentBb := "entry", instIdx := 0 } 8
  rw [show (0 : Nat) + (8 + 1) = 9 from by omega] at hb
  rw [h0]
  have := runBlocks_intret_of_block (fuel := 9) hlk hb
  simpa using this

/-- **The `codegen_correct`-shaped claim for `retFn` is TRUE and EMPTY.** No codegen reasoning is used:
    RET's result is `IntRet`, which the statement routes to `| _ => True`. This is what "the recipe route
    models 8 kinds" actually means — the other codegen-ready terminator, RET, is one the theorem SAYS
    NOTHING ABOUT, rather than one it gets wrong or one that is excluded upstream. -/
theorem codegen_correct_retFn_vacuous {vs : VenomState} {as : AsmState} :
    (match runContext 10 retCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan retFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  rw [retFn_intret vs]
  trivial

/-! ### Why `tFn`/`rFn` are narrow — it is NOT `fnEom`, and NOT a missing allocating function

The RETURN/REVERT capstones carry `callvalue = 0`, forced by REVERT/RETURN's two side conditions:

    hbelow : off + sz ≤ ps'.alloc.fnEom
    hcov0  : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asm.memory.size

I recorded the cause as "`fnEom = 0` (`PlanTypes.lean:50-55`) forces `off = sz = 0`; a symbolic-size capstone
needs a function whose plan actually ALLOCATES". **That diagnosis is wrong, and the theorems below refute
it.** `fnEom` is a plain PARAMETER of `generateFnPlan` — `generateFnPlan fn fnEom lblCtr`, reaching
`initPlanState fnEom` — and I had simply been instantiating it at `0` in every capstone. Raising it costs
nothing: `tFn_prog_indep_fnEom`/`rFn_prog_indep_fnEom` show the emitted program at `fnEom = 32` is
BYTE-IDENTICAL to the one at `fnEom = 0` (`fnEom` only seeds the spill allocator's `nextOffset`, and these
functions spill nothing), while `tFn_next_fnEom`/`rFn_next_fnEom` show the value really does reach the
SUCCESSOR's allocator — which is exactly what `hbelow` reads. So `hbelow` can be given as much room as one
likes, on the same program, with no allocating function anywhere.

**The binding constraint is `hcov0`**, and it is of a different KIND: `hbelow` is a fact about the PLAN,
whereas `hcov0` is a fact about the ASM state's memory. With `sz ≠ 0` the left disjunct dies and one must
prove `((off + sz + 31) / 32) * 32 ≤ asm.memory.size` — a property of the AsmState the driver hands to each
block. `codegen_correct_ofBlocks_recipeW_inv` carries `Inv : VenomState → Prop`, which **cannot state it**.
Note also that `memoryRel` (`CodegenRel.lean:412-414`) is byte-agreement outside the spill window and says
NOTHING about `ByteArray.size`, so the relation does not supply it either.

So the real shape of this gap: generalise the driver's invariant to `Inv : VenomState → AsmState → Prop`
(the same move that `HbsimMatch_and_inv` already made for the VenomState-only `Inv`, since `Entry` is
`VenomState → AsmState → Nat → Prop` and already carries the AsmState), and thread a memory-size lower
bound across blocks. That is a driver generalisation, NOT a new example function — and it would also be the
first invariant in this development to constrain the asm side. -/

theorem tFn_prog_indep_fnEom :
    (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1
      = (asmResolve (executePlan (generateFnPlan tFn 0 0).get!.1)).1 := by decide +kernel
theorem rFn_prog_indep_fnEom :
    (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1
      = (asmResolve (executePlan (generateFnPlan rFn 0 0).get!.1)).1 := by decide +kernel
theorem tFn_next_fnEom : (psOfFn (fnPlanFuel tFn) tFn 32 0 "next").alloc.fnEom = 32 := by decide +kernel
theorem rFn_next_fnEom : (psOfFn (fnPlanFuel rFn) rFn 32 0 "next").alloc.fnEom = 32 := by decide +kernel

/-! ### ✅ SYMBOLIC-SIZE REVERT — `codegen_correct_rFn_symbolic`, and the first asm-side invariant

Every previous RETURN/REVERT capstone pinned `callvalue = 0`. This one only BOUNDS it
(`callvalue.toNat ≤ 16`), so the REVERT's offset and size are genuinely SYMBOLIC and can be non-zero.

Two things made it possible, and both corrected an earlier belief of mine:
* **`fnEom` is a free parameter** (see "Why `tFn`/`rFn` are narrow"): instantiating at `32` instead of `0`
  gives `hbelow : off + sz ≤ 32` room on a BYTE-IDENTICAL program. `hbelow` was never the blocker.
* **`hcov0` was the real blocker, and it needs an ASM fact** — `((off+sz+31)/32)*32 ≤ asm.memory.size` — which
  `Inv : VenomState → Prop` cannot state. `mInv` therefore carries `64 ≤ a.memory.size`, threaded through the
  JMP successor by `runAsm_memory_size_mono` (EVM memory only grows, so a LOWER bound is free). `mInv`'s
  third component is the `tInv` trick (condition on `currentBb`, vacuous at entry) supplying the operands'
  VALUES; dropping the old `hcv` rewrite from that proof is exactly what lets the value stay symbolic.

No dispatcher change was needed: `HbsimMatch`'s Halt/Abort arms never mention `Entry`, so the REVERT block
works for any invariant, and only the JMP arm had to be generalised.

NON-VACUITY: `rFn_reverts_sym` proves `runContext 10 rCtx vs = Abort RevertAbort vs'` for EVERY non-halted
`vs` — no call-value constraint at all — so the `Abort RevertAbort` arm is the one that fires, not the
`| _ => True` catch-all, across the whole symbolic range. -/

def mInv (s : VenomState) (a : AsmState) : Prop :=
  s.callCtx.callvalue.toNat ≤ 16 ∧ 64 ≤ a.memory.size ∧
  (s.currentBb = "next" → lookupVar "s" s = some s.callCtx.callvalue
                        ∧ lookupVar "o" s = some s.callCtx.callvalue)

theorem rBody_regularBodyH32 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["s","o"] offsetToPc
      (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 1 [tS, tO] [] := by
  refine ⟨cv_step (out := "s") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  exact cv_step (out := "o") (S := [] ++ tS.outputs) rfl (by decide) (by decide)

-- layout at fnEom := 32 (program is byte-identical to fnEom := 0, see tFn_prog_indep_fnEom)
theorem r32_entry_pc : pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 "entry" = 0 := by
  decide +kernel
theorem r32_next_pc : pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 "next" = 5 := by
  decide +kernel
theorem r32_len : (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length = 8 := by
  decide +kernel
theorem r32_psE : psOfFn (fnPlanFuel rFn) rFn 32 0 "entry" = initPlanState 32 := by
  decide +kernel

theorem codegen_correct_rFn_symbolic {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hcv : vs.callCtx.callvalue.toNat ≤ 16)
    (hmem : 64 ≤ as.memory.size)
    (hrel : venomAsmRel lo (initPlanState 32) vs as) (haspc : as.pc = 0) :
    (match runContext 10 rCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_ofBlocks_HbsimMatch
    (Entry := fun s a n => CanonEntryWH rFn lo (pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1)
        (psOfFn (fnPlanFuel rFn) rFn 32 0) (fun l => (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 l) s a n ∧ mInv s a)
    (fnEom := 32) (lblCtr := 0) (ctx := rCtx) (fn := rFn) (fuel := 10)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan rFn 32 0).get!.1) (psFinal := (generateFnPlan rFn 32 0).get!.2)
    rfl rfl rfl rfl ?_ ?_
  case _ =>
    intro bb hbb s asm N f' hE hlbleq
    obtain ⟨⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩, hcvS, hmemS, hvarS⟩ := hE
    simp only [rFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry : %s = CALLVALUE ; %o = CALLVALUE ; JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact r32_entry_pc
      match f' with
      | 0 => rw [show runBlock 0 rCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | 1 => rw [show runBlock 1 rCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | 2 => rw [show runBlock 2 rCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS, tO,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | (j+3) =>
        obtain ⟨as', hbody, hrel', hpcas⟩ :=
          labelThenBody_sim (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg)
            (fn := rFn) (nextLiveness := ["s","o"]) (curBbLabel := "entry") (dem := 1)
            (ps0 := initPlanState 32) (S := []) (bb := tEntry) (front := [tS, tO]) (sEnd := tSEnd s)
            (tEntry_thread s) rBody_regularBodyH32
            ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩
            (by simp [StackIsVars, initPlanState])
            (by rw [r32_psE] at hvrel; exact hvrel)
            (by rw [hpc0]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                have hk' : k < 1 := hk; interval_cases k; rfl)
            (by rw [hpc0]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                have hk' : k < 2 := hk; interval_cases k <;> rfl)
        have has'pc : as'.pc = 3 := by rw [hpcas, hpc0]; rfl
        have hp1 : as'.pc < (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length := by rw [has'pc]; decide +kernel
        have hp2 : as'.pc + 1 < (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length := by rw [has'pc]; decide +kernel
        have hgetP : (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.get ⟨as'.pc, hp1⟩
            = resolveInst (computeLabelOffsets (executePlan (generateFnPlan rFn 32 0).get!.1)).2
                (AsmInst.AsmPushLabel "next") := by
          conv_lhs => rw [show (⟨as'.pc, hp1⟩ : Fin _) = ⟨3, by decide +kernel⟩ from Fin.ext has'pc]
          rfl
        have hgetJ : (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.get ⟨as'.pc + 1, hp2⟩ = AsmInst.AsmOp "JUMP" := by
          conv_lhs => rw [show (⟨as'.pc + 1, hp2⟩ : Fin _) = ⟨4, by decide +kernel⟩ from
            Fin.ext (show as'.pc + 1 = 4 by rw [has'pc])]
          rfl
        rw [show j+3 = 2+(j+1) from by omega]
        refine HbsimMatch_jmp_from_body_canonWH_invA (bb' := rNext) (target := "next") (off := 7)
          (rEntry_runBlock s j (by simpa using hhalt)) (by simpa [updateVar] using hhalt)
          hbody hrel' rfl hp1 hgetP (by decide +kernel) (by decide) hp2 hgetJ
          (by decide +kernel) rfl
          (by decide +kernel) hwN ?_
        refine ⟨?_, ?_, ?_⟩
        · show (jumpTo "next" (tSEnd s)).callCtx.callvalue.toNat ≤ 16
          simpa [jumpTo, tSEnd, updateVar] using hcvS
        · show 64 ≤ as'.memory.size
          exact le_trans hmemS (runAsm_memory_size_mono hbody)
        · intro _
          have hcvj : (jumpTo "next" (tSEnd s)).callCtx.callvalue = s.callCtx.callvalue := by
            simp [jumpTo, tSEnd, updateVar]
          rw [hcvj]
          constructor
          · show lookupVar "s" (updateVar "o" s.callCtx.callvalue
              { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
            show lookupVar "s" (updateVar "s" s.callCtx.callvalue { s with instIdx := 0 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_self]
          · show lookupVar "o" (updateVar "o" s.callCtx.callvalue
              { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_self]
    · -- next : REVERT %s %o, with SYMBOLIC operands
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpc5 : asm.pc = 5 := by rw [hpc_asm]; exact r32_next_pc
      obtain ⟨hs, ho⟩ := hvarS hlbl
      have hs' : evalOperand (Operand.Var "s") { s with instIdx := 0 }
          = some s.callCtx.callvalue := hs
      have ho' : evalOperand (Operand.Var "o") { s with instIdx := 0 }
          = some s.callCtx.callvalue := ho
      match f' with
      | 0 => rw [show runBlock 0 rCtx rNext s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, rNext, rR,
                 stepInstBase, isTerminator]]
             simp [HbsimMatch]
      | (j+1) =>
        obtain ⟨as', ps'', vs'', bodyLen, hbody, hrecipe⟩ :=
          hsupplyW_emptyRevertReorder (fn := rFn) (lo := lo) (k := j)
            (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel rFn) rFn 32 0)
            (wOf := fun l => (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 l)
            (o2pc := (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).2) (offsets := (computeLabelOffsets (executePlan (generateFnPlan rFn 32 0).get!.1)).2)
            (prog := (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1) (asm := asm) (ctx := rCtx) (bb := rNext) (s := s) (tInst := rR)
            (offv := "s") (szv := "o")
            (woff := s.callCtx.callvalue) (wsz := s.callCtx.callvalue) (base := [])
            (perm := [Operand.Var "s", Operand.Var "o"])
            (ps := psOfFn (fnPlanFuel rFn) rFn 32 0 "next")
            (hbb := rfl) (hop := rfl) (hoperands := rfl)
            (hevaloff := hs') (hevalsz := ho') (hvoff := hs') (hvsz := ho')
            (hrel := hvrel)
            (hbLabel := by rw [hpc5]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                           have hk' : k < 1 := hk; interval_cases k; rfl)
            (hperm := by decide) (hpsstk := by decide +kernel) (hbound := by decide +kernel)
            (hnospill := by intro o; rfl) (hreorder := rfl)
            (hblockR := by rw [hpc5]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                           have hk' : k < 1 := hk; interval_cases k; rfl)
            (hpc := by rw [hpc5]; decide +kernel) (hget := by simp only [hpc5]; rfl)
            (hcov0 := Or.inr (by
              have h2 : s.callCtx.callvalue.toNat + s.callCtx.callvalue.toNat ≤ 32 := by omega
              omega))
            (hbelow := by
              show s.callCtx.callvalue.toNat + s.callCtx.callvalue.toNat ≤ 32
              omega)
            (hlenu := by
              have : s.callCtx.callvalue.toNat ≤ 16 := hcvS
              have hus : (16 : Nat) < USize.size := by
                have := USize.size_eq; omega
              omega)
            (hw := by decide +kernel)
        have hrb : runBlock (j+1) rCtx rNext s
            = ExecResult.Abort AbortType.RevertAbort
                (revertState (setReturndata (readMemory s.callCtx.callvalue.toNat
                  s.callCtx.callvalue.toNat { s with instIdx := 0 }) { s with instIdx := 0 })) := by
          have := runBlock_body_revert rCtx rNext j [] rR rR [] s { s with instIdx := 0 }
            (Operand.Var "s") (Operand.Var "o") s.callCtx.callvalue s.callCtx.callvalue
            rfl rfl rfl hs' ho' rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
          simpa using this
        have h := HbsimMatch_dispatchW hbody hwN hrecipe
        rw [hrb] at h ⊢
        simp only [HbsimMatch] at h ⊢
        exact h
  case _ =>
    refine ⟨⟨⟨tEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩, ?_, ?_, ?_⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel rFn) rFn 32 0 "entry") _ as
      rw [r32_psE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 "entry"
      rw [haspc, r32_entry_pc]
    · show (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan rFn 32 0).get!.1)).1.length
      omega
    · simpa using hcv
    · simpa using hmem
    · intro hcontra; exact absurd hcontra (by simp)


/-- **Non-vacuity for the SYMBOLIC statement**: the `Abort RevertAbort` arm fires for EVERY state the
    capstone's hypotheses admit — including a NON-ZERO call value. Same shape as `rFn_reverts`, but the
    call value is only BOUNDED, never pinned. -/
theorem rFn_reverts_sym (vs : VenomState) (hnh : vs.halted = false) :
    ∃ vs', runContext 10 rCtx vs = ExecResult.Abort AbortType.RevertAbort vs' := by
  have h0 : runContext 10 rCtx vs
      = runBlocks 10 rCtx rFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, rCtx, rFn, lookupFunction, fnEntryLabel, tEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hentry : runBlock 9 rCtx tEntry s0 = ExecResult.OK (jumpTo "next" (tSEnd s0)) := by
    rw [show (9 : Nat) = 2 + (6 + 1) from by omega]; exact rEntry_runBlock s0 6 hnh0
  have hlk0 : lookupBlock s0.currentBb rFn.blocks = some tEntry := rfl
  have hjh : (jumpTo "next" (tSEnd s0)).halted = false := by simpa [jumpTo, updateVar] using hnh0
  have hstep : runBlocks 10 rCtx rFn s0 = runBlocks 9 rCtx rFn (jumpTo "next" (tSEnd s0)) :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hjh
  have hs : lookupVar "s" (jumpTo "next" (tSEnd s0)) = some s0.callCtx.callvalue := by
    show lookupVar "s" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "s" (updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_self]
  have ho : lookupVar "o" (jumpTo "next" (tSEnd s0)) = some s0.callCtx.callvalue := by
    show lookupVar "o" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_self]
  have hlk1 : lookupBlock (jumpTo "next" (tSEnd s0)).currentBb rFn.blocks = some rNext := rfl
  have hrev := runBlock_body_revert rCtx rNext 7 [] rR rR [] (jumpTo "next" (tSEnd s0))
    { (jumpTo "next" (tSEnd s0)) with instIdx := 0 } (Operand.Var "s") (Operand.Var "o")
    s0.callCtx.callvalue s0.callCtx.callvalue rfl rfl rfl hs ho rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])
  rw [show ([] : List Instruction).length + (7 + 1) = 8 from by simp] at hrev
  rw [h0, hstep]
  exact ⟨_, runBlocks_abort_of_block hlk1 hrev⟩


/-! ### ✅ SYMBOLIC-SIZE RETURN — `codegen_correct_tFn_symbolic`, the halting twin

The RETURN counterpart of `codegen_correct_rFn_symbolic`, and a near-mechanical transfer of it: `tFn` and
`rFn` share an entry block and differ only in the terminator, so `hsupplyW_emptyReturnReorder` slots in where
the REVERT one did and `mInv` is reused verbatim. The differences are entirely in the RESULT: RETURN yields
`Halt (haltState (setReturndata (readMemory off sz sEnd) sEnd))` rather than `Abort RevertAbort`, so the
walk composes with `runBlocks_haltDirect_of_block` (RETURN halts DIRECTLY — it is not `OK` + `halted := true`,
which is what `runBlocks_halt_of_block` is for) and the capstone's `Halt` arm fires.

With this, BOTH memory-returning terminators are proved at symbolic size: the call value is only bounded
(`≤ 16`), never pinned, so `off`/`sz` may be non-zero. `tFn_returns_sym` witnesses non-vacuity — every
non-halted `vs` reaches `Halt`, with no call-value constraint. -/

theorem tBody_regularBodyH32 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["s","o"] offsetToPc
      (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 1 [tS, tO] [] := by
  refine ⟨cv_step (out := "s") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  exact cv_step (out := "o") (S := [] ++ tS.outputs) rfl (by decide) (by decide)

-- layout at fnEom := 32 (program is byte-identical to fnEom := 0, see tFn_prog_indep_fnEom)
theorem t32_entry_pc : pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 "entry" = 0 := by
  decide +kernel
theorem t32_next_pc : pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 "next" = 5 := by
  decide +kernel
theorem t32_len : (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length = 8 := by
  decide +kernel
theorem t32_psE : psOfFn (fnPlanFuel tFn) tFn 32 0 "entry" = initPlanState 32 := by
  decide +kernel

theorem codegen_correct_tFn_symbolic {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hcv : vs.callCtx.callvalue.toNat ≤ 16)
    (hmem : 64 ≤ as.memory.size)
    (hrel : venomAsmRel lo (initPlanState 32) vs as) (haspc : as.pc = 0) :
    (match runContext 10 tCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_ofBlocks_HbsimMatch
    (Entry := fun s a n => CanonEntryWH tFn lo (pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1)
        (psOfFn (fnPlanFuel tFn) tFn 32 0) (fun l => (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 l) s a n ∧ mInv s a)
    (fnEom := 32) (lblCtr := 0) (ctx := tCtx) (fn := tFn) (fuel := 10)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan tFn 32 0).get!.1) (psFinal := (generateFnPlan tFn 32 0).get!.2)
    rfl rfl rfl rfl ?_ ?_
  case _ =>
    intro bb hbb s asm N f' hE hlbleq
    obtain ⟨⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩, hcvS, hmemS, hvarS⟩ := hE
    simp only [tFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry : %s = CALLVALUE ; %o = CALLVALUE ; JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact t32_entry_pc
      match f' with
      | 0 => rw [show runBlock 0 tCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | 1 => rw [show runBlock 1 tCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | 2 => rw [show runBlock 2 tCtx tEntry s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tEntry, tS, tO,
                 stepInstBase, execRead0, isTerminator]]
             simp [HbsimMatch]
      | (j+3) =>
        obtain ⟨as', hbody, hrel', hpcas⟩ :=
          labelThenBody_sim (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg)
            (fn := tFn) (nextLiveness := ["s","o"]) (curBbLabel := "entry") (dem := 1)
            (ps0 := initPlanState 32) (S := []) (bb := tEntry) (front := [tS, tO]) (sEnd := tSEnd s)
            (tEntry_thread s) tBody_regularBodyH32
            ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩
            (by simp [StackIsVars, initPlanState])
            (by rw [t32_psE] at hvrel; exact hvrel)
            (by rw [hpc0]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                have hk' : k < 1 := hk; interval_cases k; rfl)
            (by rw [hpc0]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                have hk' : k < 2 := hk; interval_cases k <;> rfl)
        have has'pc : as'.pc = 3 := by rw [hpcas, hpc0]; rfl
        have hp1 : as'.pc < (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length := by rw [has'pc]; decide +kernel
        have hp2 : as'.pc + 1 < (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length := by rw [has'pc]; decide +kernel
        have hgetP : (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.get ⟨as'.pc, hp1⟩
            = resolveInst (computeLabelOffsets (executePlan (generateFnPlan tFn 32 0).get!.1)).2
                (AsmInst.AsmPushLabel "next") := by
          conv_lhs => rw [show (⟨as'.pc, hp1⟩ : Fin _) = ⟨3, by decide +kernel⟩ from Fin.ext has'pc]
          rfl
        have hgetJ : (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.get ⟨as'.pc + 1, hp2⟩ = AsmInst.AsmOp "JUMP" := by
          conv_lhs => rw [show (⟨as'.pc + 1, hp2⟩ : Fin _) = ⟨4, by decide +kernel⟩ from
            Fin.ext (show as'.pc + 1 = 4 by rw [has'pc])]
          rfl
        rw [show j+3 = 2+(j+1) from by omega]
        refine HbsimMatch_jmp_from_body_canonWH_invA (bb' := tNext) (target := "next") (off := 7)
          (tEntry_runBlock s j (by simpa using hhalt)) (by simpa [updateVar] using hhalt)
          hbody hrel' rfl hp1 hgetP (by decide +kernel) (by decide) hp2 hgetJ
          (by decide +kernel) rfl
          (by decide +kernel) hwN ?_
        refine ⟨?_, ?_, ?_⟩
        · show (jumpTo "next" (tSEnd s)).callCtx.callvalue.toNat ≤ 16
          simpa [jumpTo, tSEnd, updateVar] using hcvS
        · show 64 ≤ as'.memory.size
          exact le_trans hmemS (runAsm_memory_size_mono hbody)
        · intro _
          have hcvj : (jumpTo "next" (tSEnd s)).callCtx.callvalue = s.callCtx.callvalue := by
            simp [jumpTo, tSEnd, updateVar]
          rw [hcvj]
          constructor
          · show lookupVar "s" (updateVar "o" s.callCtx.callvalue
              { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
            show lookupVar "s" (updateVar "s" s.callCtx.callvalue { s with instIdx := 0 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_self]
          · show lookupVar "o" (updateVar "o" s.callCtx.callvalue
              { updateVar "s" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
              = some s.callCtx.callvalue
            rw [lookupVar_updateVar_self]
    · -- next : REVERT %s %o, with SYMBOLIC operands
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpc5 : asm.pc = 5 := by rw [hpc_asm]; exact t32_next_pc
      obtain ⟨hs, ho⟩ := hvarS hlbl
      have hs' : evalOperand (Operand.Var "s") { s with instIdx := 0 }
          = some s.callCtx.callvalue := hs
      have ho' : evalOperand (Operand.Var "o") { s with instIdx := 0 }
          = some s.callCtx.callvalue := ho
      match f' with
      | 0 => rw [show runBlock 0 tCtx tNext s = ExecResult.Error "out of fuel" from by
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, tNext, tR,
                 stepInstBase, isTerminator]]
             simp [HbsimMatch]
      | (j+1) =>
        obtain ⟨as', ps'', vs'', bodyLen, hbody, hrecipe⟩ :=
          hsupplyW_emptyReturnReorder (fn := tFn) (lo := lo) (k := j)
            (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1) (psOf := psOfFn (fnPlanFuel tFn) tFn 32 0)
            (wOf := fun l => (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 l)
            (o2pc := (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).2) (offsets := (computeLabelOffsets (executePlan (generateFnPlan tFn 32 0).get!.1)).2)
            (prog := (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1) (asm := asm) (ctx := tCtx) (bb := tNext) (s := s) (tInst := tR)
            (offv := "s") (szv := "o")
            (woff := s.callCtx.callvalue) (wsz := s.callCtx.callvalue) (base := [])
            (perm := [Operand.Var "s", Operand.Var "o"])
            (ps := psOfFn (fnPlanFuel tFn) tFn 32 0 "next")
            (hbb := rfl) (hop := rfl) (hoperands := rfl)
            (hevaloff := hs') (hevalsz := ho') (hvoff := hs') (hvsz := ho')
            (hrel := hvrel)
            (hbLabel := by rw [hpc5]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                           have hk' : k < 1 := hk; interval_cases k; rfl)
            (hperm := by decide) (hpsstk := by decide +kernel) (hbound := by decide +kernel)
            (hnospill := by intro o; rfl) (hreorder := rfl)
            (hblockR := by rw [hpc5]; refine ⟨by decide +kernel, fun k hk => ?_⟩
                           have hk' : k < 1 := hk; interval_cases k; rfl)
            (hpc := by rw [hpc5]; decide +kernel) (hget := by simp only [hpc5]; rfl)
            (hcov0 := Or.inr (by
              have h2 : s.callCtx.callvalue.toNat + s.callCtx.callvalue.toNat ≤ 32 := by omega
              omega))
            (hbelow := by
              show s.callCtx.callvalue.toNat + s.callCtx.callvalue.toNat ≤ 32
              omega)
            (hlenu := by
              have : s.callCtx.callvalue.toNat ≤ 16 := hcvS
              have hus : (16 : Nat) < USize.size := by
                have := USize.size_eq; omega
              omega)
            (hw := by decide +kernel)
        have hrb : runBlock (j+1) tCtx tNext s
            = ExecResult.Halt
                (haltState (setReturndata (readMemory s.callCtx.callvalue.toNat
                  s.callCtx.callvalue.toNat { s with instIdx := 0 }) { s with instIdx := 0 })) := by
          have := runBlock_body_return tCtx tNext j [] tR tR [] s { s with instIdx := 0 }
            (Operand.Var "s") (Operand.Var "o") s.callCtx.callvalue s.callCtx.callvalue
            rfl rfl rfl hs' ho' rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
          simpa using this
        have h := HbsimMatch_dispatchW hbody hwN hrecipe
        rw [hrb] at h ⊢
        simp only [HbsimMatch] at h ⊢
        exact h
  case _ =>
    refine ⟨⟨⟨tEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩, ?_, ?_, ?_⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel tFn) tFn 32 0 "entry") _ as
      rw [t32_psE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 "entry"
      rw [haspc, t32_entry_pc]
    · show (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan tFn 32 0).get!.1)).1.length
      omega
    · simpa using hcv
    · simpa using hmem
    · intro hcontra; exact absurd hcontra (by simp)


/-- **Non-vacuity for the SYMBOLIC statement**: the `Abort RevertAbort` arm fires for EVERY state the
    capstone's hypotheses admit — including a NON-ZERO call value. Same shape as `tFn_reverts`, but the
    call value is only BOUNDED, never pinned. -/
theorem tFn_returns_sym (vs : VenomState) (hnh : vs.halted = false) :
    ∃ vs', runContext 10 tCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 tCtx vs
      = runBlocks 10 tCtx tFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, tCtx, tFn, lookupFunction, fnEntryLabel, tEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hentry : runBlock 9 tCtx tEntry s0 = ExecResult.OK (jumpTo "next" (tSEnd s0)) := by
    rw [show (9 : Nat) = 2 + (6 + 1) from by omega]; exact tEntry_runBlock s0 6 hnh0
  have hlk0 : lookupBlock s0.currentBb tFn.blocks = some tEntry := rfl
  have hjh : (jumpTo "next" (tSEnd s0)).halted = false := by simpa [jumpTo, updateVar] using hnh0
  have hstep : runBlocks 10 tCtx tFn s0 = runBlocks 9 tCtx tFn (jumpTo "next" (tSEnd s0)) :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hjh
  have hs : lookupVar "s" (jumpTo "next" (tSEnd s0)) = some s0.callCtx.callvalue := by
    show lookupVar "s" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "s" (updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_self]
  have ho : lookupVar "o" (jumpTo "next" (tSEnd s0)) = some s0.callCtx.callvalue := by
    show lookupVar "o" (updateVar "o" s0.callCtx.callvalue
      { updateVar "s" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some s0.callCtx.callvalue
    rw [lookupVar_updateVar_self]
  have hlk1 : lookupBlock (jumpTo "next" (tSEnd s0)).currentBb tFn.blocks = some tNext := rfl
  have hrev := runBlock_body_return tCtx tNext 7 [] tR tR [] (jumpTo "next" (tSEnd s0))
    { (jumpTo "next" (tSEnd s0)) with instIdx := 0 } (Operand.Var "s") (Operand.Var "o")
    s0.callCtx.callvalue s0.callCtx.callvalue rfl rfl rfl hs ho rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])
  rw [show ([] : List Instruction).length + (7 + 1) = 8 from by simp] at hrev
  rw [h0, hstep]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hrev⟩

end Example

/-- **Non-vacuity: a bare STOP block drives the full dispatcher** (STOP arm; empty body). -/
theorem HbsimMatch_dispatch_nonvacuous {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 : AsmState} {ps : PlanState} {N f' : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } as0)
    (hstoppc : as0.pc < prog.length) (hstop : prog.get ⟨as0.pc, hstoppc⟩ = AsmInst.AsmOp "STOP")
    (hle : 0 + 1 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N
      (runBlock (f' + 1) ctx bb { s with instIdx := 0 }) := by
  have hrb : runBlock (f' + 1) ctx bb { s with instIdx := 0 }
      = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, hbb, hstopop, stepInstBase]
  refine HbsimMatch_dispatch (bodyLen := 0) (as' := as0) (ps' := ps) (vs' := { s with instIdx := 0 })
    (offsets := offsets) (by simp [runAsm]) ?_
  exact Or.inl ⟨hrel, hle, hrb, hstoppc, hstop⟩

/-- **Non-vacuity: a JMP disjunct is also reachable** — the continuing branch is not dead. A block whose
    body sim lands on `PUSH target; JUMP` at `as'.pc`, with the recorded plan matching the target and the
    successor block present, drives the JMP arm. -/
theorem HbsimMatch_dispatch_jmp_nonvacuous {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {ps' : PlanState} {bodyLen N f' off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs' : VenomState} {target : String}
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as') (hps : ps' = psOf target)
    (hnh : vs'.halted = false)
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs'))
    (hp1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hp1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hp2 : as'.pc + 1 < prog.length) (hjump : prog.get ⟨as'.pc + 1, hp2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hlk' : lookupBlock target fn.blocks = some bb') (hle : bodyLen + 2 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) :=
  HbsimMatch_dispatch (offsets := offsets) hbody
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨target, off, bb', hrel', hps, hle, hnh, hrb, ⟨hp1, hpush⟩, hoff_lk, hoff, ⟨hp2, hjump⟩,
        hidx_lk, hlk'⟩))))))


end EvmYul.Venom.Hol.Codegen

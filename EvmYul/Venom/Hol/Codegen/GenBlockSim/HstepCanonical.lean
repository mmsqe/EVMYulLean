import EvmYul.Venom.Hol.Codegen.GenBlockSim.CfgHfsim

/-!
# GenBlockSim -- HstepCanonical

The canonical per-block hstep family (JMP / JNZ / STOP / RETURN / REVERT / bareTerm / join) and
the codegen_correct_canonical capstone.
-/

open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/-! ### The rest of the hstep family, for join blocks

`WalkStep_join` is terminator-agnostic, but the five remaining canonical `hstep`s could not simply be
wrapped in it: each hard-codes `hbb : bb.instructions = [term]`, a *bare* terminator block. A join is
`phis ++ [term]`, so that hypothesis is false for it — which is why JMP alone went through above (it is
the one clause parameterised on the block's result rather than its syntax).

`runBlock_join_eq_execBlock_at` is the reduction they all need: a join block's `runBlock` is its
`execBlock` resumed at index `phis.length`, i.e. exactly at the terminator. From there the existing
`execBlock_step_*` lemmas fire unchanged, and the five clauses follow. -/

/-- **A join block's `runBlock` resumes at the terminator.** -/
theorem runBlock_join_eq_execBlock_at {ctx : VenomContext} {bb : BasicBlock} {fuel : Nat}
    {phis : List Instruction} {term : Instruction} {s sPhi : VenomState}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI) :
    runBlock fuel ctx bb s
      = execBlock fuel ctx bb { sPhi with instIdx := phis.length } := by
  have hlen : phiPrefixLength bb.instructions = phis.length := by
    rw [hbb]
    exact phiPrefixLength_append phis [term] hphis
      (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
  rw [runBlock_eq_execBlock_of_phis hev, hlen]

/-- **Halt-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_halt_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length } = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s = ExecResult.Halt sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_halt extraFuel ctx bb _ sEnd' term
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inl ⟨_, asm', hrb, hrun, hrel⟩)

/-- **Revert-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_revert_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length }
        = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s
      = ExecResult.Abort AbortType.RevertAbort sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_abort extraFuel ctx bb _ sEnd' term _
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hrel⟩))

/-- **Fault-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_fault_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length }
        = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s
      = ExecResult.Abort AbortType.ExHaltAbort sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_abort extraFuel ctx bb _ sEnd' term _
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hrel⟩)))


theorem hstep_jnz_taken_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {phis : List Instruction} {jnzInst : Instruction}
    {condOp : Operand} {ifNz ifZ : String} {cond : bytes32}
    {s sPhi : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [jnzInst])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { sPhi with instIdx := phis.length } = some cond)
    (hcondne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hsnothalt : sPhi.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo ifNz { sPhi with instIdx := phis.length }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  have hterm : jnzInst.opcode ≠ Opcode.PHI := by rw [hopc]; decide
  have hstepj : stepInstBase jnzInst { sPhi with instIdx := phis.length }
      = ExecResult.OK (jumpTo ifNz { sPhi with instIdx := phis.length }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcondne) h
  have hnh : (jumpTo ifNz { sPhi with instIdx := phis.length }).halted = false := by
    rw [jumpTo]; exact hsnothalt
  have hrb : execBlock (extraFuel + 1) ctx bb
      { sPhi with instIdx := phiPrefixLength bb.instructions }
      = ExecResult.OK (jumpTo ifNz { sPhi with instIdx := phis.length }) := by
    have hlen : phiPrefixLength bb.instructions = phis.length := by
      rw [hbb]
      exact phiPrefixLength_append phis [jnzInst] hphis
        (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
    rw [hlen]
    exact execBlock_step_term_ok extraFuel ctx bb _ _ jnzInst
      (by simpa using getInstruction_term bb phis jnzInst hbb) hstepj
      (by rw [hopc]; decide) hnh
  have hlk'' : lookupBlock (jumpTo ifNz { sPhi with instIdx := phis.length }).currentBb
      fn.blocks = some bb' := by rw [jumpTo]; exact hlk'
  exact hstep_jmp_block_join pcOf psOf wOf hev hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk'' hwdec

theorem hstep_jnz_nottaken_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {phis : List Instruction} {jnzInst : Instruction}
    {condOp : Operand} {ifNz ifZ : String} {cond : bytes32}
    {s sPhi : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [jnzInst])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { sPhi with instIdx := phis.length } = some cond)
    (hcondeq : cond = EvmYul.UInt256.ofNat 0)
    (hsnothalt : sPhi.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo ifZ { sPhi with instIdx := phis.length }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  have hterm : jnzInst.opcode ≠ Opcode.PHI := by rw [hopc]; decide
  have hstepj : stepInstBase jnzInst { sPhi with instIdx := phis.length }
      = ExecResult.OK (jumpTo ifZ { sPhi with instIdx := phis.length }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rename_i h; exact absurd hcondeq (bne_iff_ne.mp h)
    · rfl
  have hnh : (jumpTo ifZ { sPhi with instIdx := phis.length }).halted = false := by
    rw [jumpTo]; exact hsnothalt
  have hrb : execBlock (extraFuel + 1) ctx bb
      { sPhi with instIdx := phiPrefixLength bb.instructions }
      = ExecResult.OK (jumpTo ifZ { sPhi with instIdx := phis.length }) := by
    have hlen : phiPrefixLength bb.instructions = phis.length := by
      rw [hbb]
      exact phiPrefixLength_append phis [jnzInst] hphis
        (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
    rw [hlen]
    exact execBlock_step_term_ok extraFuel ctx bb _ _ jnzInst
      (by simpa using getInstruction_term bb phis jnzInst hbb) hstepj
      (by rw [hopc]; decide) hnh
  have hlk'' : lookupBlock (jumpTo ifZ { sPhi with instIdx := phis.length }).currentBb
      fn.blocks = some bb' := by rw [jumpTo]; exact hlk'
  exact hstep_jmp_block_join pcOf psOf wOf hev hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk'' hwdec

/-- **RETURN per-block `hstep` clause.** The first *operand-bearing* terminator instance: for a bare
    `[term]` with `term.opcode = RETURN`, `term.operands = [offOp, szOp]` and both operands evaluating
    (`off`, `sz`), the Venom step halts with returndata `readMemory off.toNat sz.toNat …`. Given the
    matching whole-program halt witness, `hstep_bareTerm_halt_gen` discharges the full per-block match.
    The returndata effect *is* observable in `venomAsmTerminalRel`, so the caller's witness must produce
    matching returndata. -/
theorem hstep_bareTerm_return {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {offOp szOp : Operand} {off sz : UInt256}
    {s : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hret : term.opcode = Opcode.RETURN)
    (hops : term.operands = [offOp, szOp])
    (hoff : evalOperand offOp { s with instIdx := 0 } = some off)
    (hsz : evalOperand szOp { s with instIdx := 0 } = some sz)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel
          (haltState (setReturndata (readMemory off.toNat sz.toNat { s with instIdx := 0 })
            { s with instIdx := 0 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock f' ctx bb s) := by
  refine hstep_bareTerm_halt_gen pcOf psOf wOf hbb (by rw [hret]; decide) ?_ hasm
  unfold stepInstBase
  simp only [hret, hops, hoff, hsz]

/-- **REVERT per-block `hstep` clause.** The `RevertAbort` operand-bearing instance, mirroring
    `hstep_bareTerm_return`: a bare `[term]` with `term.opcode = REVERT` and both operands evaluating
    aborts with `RevertAbort` and returndata `readMemory off.toNat sz.toNat …`. Discharged via
    `hstep_bareTerm_revert_gen`. -/
theorem hstep_bareTerm_revert {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {offOp szOp : Operand} {off sz : UInt256}
    {s : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hrev : term.opcode = Opcode.REVERT)
    (hops : term.operands = [offOp, szOp])
    (hoff : evalOperand offOp { s with instIdx := 0 } = some off)
    (hsz : evalOperand szOp { s with instIdx := 0 } = some sz)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel
          (revertState (setReturndata (readMemory off.toNat sz.toNat { s with instIdx := 0 })
            { s with instIdx := 0 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock f' ctx bb s) := by
  refine hstep_bareTerm_revert_gen pcOf psOf wOf hbb (by rw [hrev]; decide) ?_ hasm
  unfold stepInstBase
  simp only [hrev, hops, hoff, hsz]


/-- **Generic per-block `hstep` for a spilling JMP block** — the adapter wiring the
Step-1 spill-aware per-block sim (`genBlockSimulation_regularHSVP_jmp`) into the
codegen driver's per-block obligation (`hstep_jmp_block`, consumed by
`hstep_dispatch` → `codegen_correct_sched`). The block runs its HSVP body then
`JMP target`; the sim supplies the Venom `OK (jumpTo target sEnd)` and the asm run
to the successor pc with `venomAsmRel` at the post-body plan state, and this feeds
the driver's `hstep` match. The ONLY residual is the plan-state determinism
(`hstk`/`hsp`/`hfe`/`hno`: the post-body fold output equals the entry plan state the
schedule `psOf` assigns the successor) — the named Step-2/4 obligation, taken here
as a hypothesis. -/
theorem hstep_regularHSVP_jmp
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    -- Venom block structure + JMP terminator
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    -- HSVP body + JMP layout (as `genBlockSimulation_regularHSVP_jmp`)
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
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- the scheduling / plan-determinism residual (Step 2/4)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom
      = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset
      ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Per-block JMP `hstep` on the canonical schedule.** The whole-function assembly for an aligned-JMP
    forward edge: instantiates `hstep_regularHSVP_jmp` with `pcOf := pcOfLabel prog`, `psOf := psOfFn`,
    `wOf l := prog.length - pcOfLabel prog l`, discharging `hblock`/`hpush`/`hjump`/`hpc*` from the chain
    (`hstep_jmp_layout_canonical` + placement) and the scheduling residual `hstk`/`hsp`/`hfe`/`hno` from
    `adapter_lgfold_eq_psOfFn_succ_general` (`(lg.foldl gp).2 = psOfFn target`, projected). Body-sim
    (`hready`/`hsd0`/…), Venom facts (`hbb`/`hterm_step`/…), jump-target lookups (`hoff_lk`/`hidx_lk`/`hidxeq`),
    forward-edge ranking (`hle`/`hwdec`) and the open label-uniqueness (`hpreuniq`) are inputs. `bb` is a
    phi/param-free aligned-JMP block (`hbb`/`hnp` share `front`). -/
theorem hstep_regularHSVP_jmp_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen off idx : Nat} {target : String} {succRest : List String}
    {succBB : BasicBlock} {result : List String × AssocList String PlanState × PlanState}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = target :: succRest)
    (hsfind : fn.blocks.find? (·.label == target) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ target) (hsne : target ≠ bb.label)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = target)
    (hidxeq : idx = pcOfLabel prog bb'.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hh1, hpush0, hh2, hjump0⟩ := hstep_jmp_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  have hres := adapter_lgfold_eq_psOfFn_succ_general (fnEom := fnEom) (lblCtr := lblCtr)
    hentry hpathhead hfuel hfn hchain hpsucc hsfind hsfresh hsne hsome hpfind hentry0 hmulti hnp
    hterm_jmp hterm_ops hterm_outs hjoin hreg hnospill hfront hgp
  exact hstep_regularHSVP_jmp (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Per-block JMP `hstep` on the canonical schedule, for *any reachable* block.** The chain-free
    counterpart of `hstep_regularHSVP_jmp_canonical`. That one routes its layout fact through
    `chain_segment_gbp`, hence `JmpChainTo`, hence "every block between the entry and `bb` has exactly
    one successor" — so it can never fire on a block behind a `JNZ`. Here the layout comes from
    `reach_segment_gbp_fn` instead: plain `CfgReach` from the entry, plus the decidable `DfsClosed` /
    entry-visited facts. Every reachable block qualifies, branch targets and joins included.

    The scheduling residual (`hres`: the block's gp-fold lands on the successor's canonical entry state)
    is taken as a hypothesis rather than derived from the chain. Both of its sides *compute*, so it is
    decidable per function; deriving it in general is the DFS tree-edge/join theory, which is what the
    remaining `psOfFn_succ_*_general` family does for chains. Everything else — body-sim, Venom facts,
    jump-target lookups, ranking — is unchanged from the canonical version. -/
theorem hstep_regularHSVP_jmp_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen off idx : Nat} {target : String}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr target)
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = target)
    (hidxeq : idx = pcOfLabel prog bb'.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  -- `hpreuniq` is *derived*, not assumed: the block's plan heads with its own label
  -- (`generateBlockPlan_head_label`), and the DFS emits each label at most once (`hpreuniq_generic`).
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hh1, hpush0, hh2, hjump0⟩ := hstep_jmp_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_jmp (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Generic per-block `hstep` for a spilling JNZ-taken block** — the conditional
counterpart of `hstep_regularHSVP_jmp`: feeds `genBlockSimulation_regularHSVP_jnz_taken`
into `hstep_jmp_block` (terminator-agnostic — JNZ-taken produces `OK (jumpTo ifNz)`).
Residual: the same plan-state determinism. -/
theorem hstep_regularHSVP_jnz_taken
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hle : bodyLen + 3 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 3) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Generic per-block `hstep` for a spilling JNZ-not-taken block** — the `cond = 0`
fall-through twin, feeding `genBlockSimulation_regularHSVP_jnz_nottaken` into
`hstep_jmp_block`. Same plan-state-determinism residual. -/
theorem hstep_regularHSVP_jnz_nottaken
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idxZ = pcOf bb'.label)
    (hle : bodyLen + 5 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 5) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Per-block JNZ-taken `hstep` on the canonical schedule.** Dual-successor analogue of
    `hstep_regularHSVP_jmp_canonical` for the condition-≠0 branch: discharges the layout
    (`hblock`/`hdup`/`hpush`/`hjumpi` — the first three of the 5-op tail) from the chain via
    `hstep_jnz_layout_canonical` + placement (`pcOfLabel_aligned_jnz_block`), then applies the generic
    `hstep_regularHSVP_jnz_taken`. The scheduling residual (`hstk`/`hsp`/`hfe`/`hno` for `ifNz`) is an INPUT
    here — JNZ's term-step is not PlanState-identity (DUP+POP+emit), so the JMP residual machinery
    (`adapter_lgfold_eq_psOfFn_succ_general`) does not transfer directly; a JNZ successor-recording is future
    work. Condition (`hstkF`/`hcval`/`hcond`), jump-target, body-sim, Venom and forward-edge are inputs. -/
theorem hstep_regularHSVP_jnz_taken_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P off idx : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifNzBB ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 4 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifNz)
    -- NOTE the successor ORDER: `bbSuccs` is `(getSuccessors …).reverse`, so a JNZ's CFG successors
    -- come out as `ifZ :: ifNz` — the fall-through is the FIRST successor and the taken target the
    -- SECOND. Hence the taken branch needs the second-successor RELATION, not an equality.
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: ifNz :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfind2 : fn.blocks.find? (·.label == ifNz) = some ifNzBB)
    (hsfresh1 : ∀ b ∈ path, b.label ≠ ifZ) (hsne1 : ifZ ≠ bb.label)
    (hsfresh2 : ∀ b ∈ path, b.label ≠ ifNz) (hsne2 : ifNz ≠ bb.label)
    (hnr : ¬ CfgReach (cfgAnalyze fn) ifZ ifNz)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idx = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ :=
    chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpush⟩, ⟨hpc3, hjumpi⟩, _, _⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- discharge the scheduling residual from the chain (taken branch; ifNz = SECOND successor)
  obtain ⟨hstk, hsp, hfe, hno⟩ := adapter_lgfold_rel_psOfFn_succ2_jnz_general hentry hpathhead hfuel hfn
    hchain hpsucc hsfind1 hsfind2 hsfresh1 hsne1 hsfresh2 hsne2 hnr hsome hpfind hentry0 hmulti hnp
    hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS hreg hnospill hfront hgp
  exact hstep_regularHSVP_jnz_taken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hle hwdec

/-- **Per-block JNZ-not-taken `hstep` on the canonical schedule.** Dual-successor analogue of
    `hstep_regularHSVP_jmp_canonical` for the condition-=0 (fall-through) branch: discharges the layout
    (`hblock`/`hdup`/`hpush`/`hjumpi` — all five of the 5-op tail) from the chain via
    `hstep_jnz_layout_canonical` + placement (`pcOfLabel_aligned_jnz_block`), then applies the generic
    `hstep_regularHSVP_jnz_nottaken`. The scheduling residual (`hstk`/`hsp`/`hfe`/`hno` for `ifZ`) is
    DISCHARGED from the chain by `adapter_lgfold_rel_psOfFn_succ2_jnz_general`: `ifZ` is the *second*
    successor, so its recorded entry agrees with the block's body-fold on stack/spilled but carries the
    allocator threaded through `ifNz`'s whole subtree — hence a relation (`fnEom` fixed, `nextOffset`
    non-decreasing, via `dfsEntries_alloc_inv`) rather than the taken branch's whole-state equality.
    The tree-edge side condition is now a plain CFG fact — `hnr : ¬ CfgReach (cfgAnalyze fn) ifNz ifZ`
    (via `dfsEntriesAux_not_reach_fresh` / `dfsEntries_visited_reach`) — as are
    the condition (`hstkF`/`hcval`/`hcond`), jump-target, body-sim, Venom and forward-edge facts. -/
theorem hstep_regularHSVP_jnz_nottaken_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P offNz offZ idxZ : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifZ)
    -- `bbSuccs` reverses the terminator's labels, so the FALL-THROUGH `ifZ` is the FIRST CFG
    -- successor: its recorded entry is the block's exit exactly (a whole-PlanState equality).
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: succRest)
    (hsfind : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ ifZ) (hsne : ifZ ≠ bb.label)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idxZ = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ :=
    chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpushNz⟩, ⟨hpc3, hjumpi⟩, ⟨hpc4, hpushZ⟩, ⟨hpc5, hjump⟩⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- discharge the scheduling residual from the chain (not-taken branch; ifZ = FIRST successor)
  have hres := adapter_lgfold_eq_psOfFn_succ_jnz_general hentry hpathhead hfuel hfn hchain hpsucc hsfind
    hsfresh hsne hsome hpfind hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS
    hreg hnospill hfront hgp
  exact hstep_regularHSVP_jnz_nottaken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Generic per-block `hstep` for a spilling STOP block** — the terminal
counterpart of the continue-arm adapters. A block `front ++ [STOP]` with an HSVP
body: the Venom side halts (`runBlock_halt` → `Halt (haltState sEnd)`), the asm side
runs body + STOP to `AsmHalt` with the terminal relation (`hasm_regularHSVP_stop`,
stretched to the driver budget `N`), and `hstep_halt_block` packages the two into the
driver's per-block `hstep` match. No plan-state-determinism residual (a terminal block
has no successor). The spilling terminal `hstep` clause, generic. -/
theorem hstep_regularHSVP_stop
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState sEnd) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd (haltState sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_stop (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
      hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Generic per-block `hstep` for a spilling INVALID block** — the fault-terminal counterpart
of `hstep_regularHSVP_stop`. A block `front ++ [INVALID]` with an HSVP body: Venom aborts to
`Abort ExHaltAbort (haltState (setReturndata empty sEnd))` (`runBlock_abort`, via the INVALID step
supplied as `hterm_step`), the asm runs body + INVALID to `AsmFault` with the terminal relation
(`hasm_regularHSVP_invalid`, budget = driver `N`), and `rw [hrb]` discharges the driver match's
ExHaltAbort arm. The terminal returndata match is unconditional (both sides clear returndata on the
fault), so — unlike the pre-fix INVALID chain — there is no returndata-empty hypothesis. No
plan-state-determinism residual. -/
theorem hstep_regularHSVP_invalid
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata ByteArray.empty sEnd)) AbortType.ExHaltAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_invalid (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
      hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block STOP `hstep` on the canonical schedule.** Terminal analogue of
    `hstep_regularHSVP_jmp_canonical` for a STOP block: discharges the layout (`hblock`/`hlt`/`hget` = `AsmOp
    "STOP"`) from the chain via `hstep_bareHalt_layout_canonical` + placement, then applies the generic
    `hstep_regularHSVP_stop`. No scheduling residual / jump-target / forward-edge (STOP halts, the
    OK-not-halted branch is vacuous so `pcOf`/`psOf`/`wOf` stay abstract). Body-sim, Venom and `hN` are
    inputs; `bb` is a phi/param-free STOP block. -/
theorem hstep_regularHSVP_stop_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "STOP")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "STOP" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_stop P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN

/-- **Per-block INVALID `hstep` on the canonical schedule.** Fault-terminal analogue of
    `hstep_regularHSVP_stop_canonical`: same bare-halting layout from the chain (`AsmOp "INVALID"`), Venom
    faults to `Abort ExHaltAbort (haltState (setReturndata empty sEnd))`, applies `hstep_regularHSVP_invalid`.
    `pcOf`/`psOf`/`wOf` abstract (vacuous branch). -/
theorem hstep_regularHSVP_invalid_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "INVALID")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "INVALID" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_invalid P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN


/-- **Generic per-block `hstep` for a spilling RETURN block** — the operand-terminal
counterpart of `hstep_regularHSVP_stop`. A block `front ++ [RETURN off sz]` with an
HSVP body: Venom halts to `Halt (haltState (setReturndata (memory[woff,wsz]) sEnd))`
(`runBlock_halt`, via the RETURN step supplied as `hterm_step`), the asm runs body +
the two-operand emission + RETURN to `AsmHalt` with the terminal relation
(`hasm_regularHSVP_return_var`, budget = driver `N`), and `rw [hrb]` discharges the
driver match's Halt arm. No plan-state-determinism residual. -/
theorem hstep_regularHSVP_return
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    (hN : bodyLen + emitLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd))
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_return_var (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block RETURN `hstep` on the canonical schedule.** Operand-terminal analogue of
    `hstep_regularHSVP_stop_canonical`: discharges the 3-segment layout (`hblock` for label+body+emit, `hget`
    = `AsmOp "RETURN"` at `bodyLen+emitLen`) from the chain via `hstep_return_layout_canonical` + placement,
    then applies the generic `hstep_regularHSVP_return`. The memory-safety (`hcov0`/`hsafe`/`hlen`),
    operand-membership/liveness/lookup (`hoffS`/…/`hvsz`) and body-sim/Venom facts are inputs. `pcOf`/`psOf`/
    `wOf` abstract (RETURN halts). `bb` a phi/param-free RETURN block; `nl` = `liveVarsAt … instructions.length`. -/
theorem hstep_regularHSVP_return_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "RETURN")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "RETURN" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_return pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN

/-- **Generic per-block `hstep` for a spilling REVERT block** — the operand-terminal
counterpart of `hstep_regularHSVP_stop`. A block `front ++ [REVERT off sz]` with an
HSVP body: Venom aborts to `Abort RevertAbort (revertState (setReturndata (memory[woff,wsz]) sEnd))`
(`runBlock_abort`, via the REVERT step supplied as `hterm_step`), the asm runs body +
the two-operand emission + RETURN to `AsmHalt` with the terminal relation
(`hasm_regularHSVP_revert_var`, budget = driver `N`), and `rw [hrb]` discharges the
driver match's Halt arm. No plan-state-determinism residual. -/
theorem hstep_regularHSVP_revert
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    (hN : bodyLen + emitLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) AbortType.RevertAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_revert_var (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block REVERT `hstep` on the canonical schedule.** Revert-terminal analogue of
    `hstep_regularHSVP_return_canonical`: discharges the 3-segment layout (`hblock` for label+body+emit, `hget`
    = `AsmOp "REVERT"` at `bodyLen+emitLen`) from the chain via `hstep_return_layout_canonical` + placement,
    then applies the generic `hstep_regularHSVP_revert`. The memory-safety (`hcov0`/`hsafe`/`hlen`),
    operand-membership/liveness/lookup (`hoffS`/…/`hvsz`) and body-sim/Venom facts are inputs. `pcOf`/`psOf`/
    `wOf` abstract (REVERT aborts). `bb` a phi/param-free REVERT block; `nl` = `liveVarsAt … instructions.length`. -/
theorem hstep_regularHSVP_revert_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "REVERT")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "REVERT" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_revert pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN

/-- **Full per-block `hstep` clause for a terminal (halting) block.** For a block whose Venom step halts
    (`runBlock … = Halt s'`), the whole-program halt sim (`runAsm N … = AsmHalt asm'` +
    `venomAsmTerminalRel s' asm'`) *is* the `hstep`'s `Halt` arm; the other arms are vacuous. The
    per-block terminal dispatch of the §5 assembly (STOP/RETURN/… blocks). -/
theorem hstep_halt_block {ctx : VenomContext} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {bb : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {N f' : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt s')
    (hsim : runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK _ => True
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [hrb]; exact ⟨asm', hsim⟩


/-- **Reworked JMP `hstep` arm (offsetToPc from the *unresolved* plan).** Fixes the double-resolution:
    the walk's `offsetToPc`/`prog` come from `asmResolve origAsm` (the unresolved plan `executePlan ops`),
    so the arm takes `origAsm = pre ++ AsmLabel bb'.label :: suf` and uses `(asmResolve origAsm).2` /
    `(asmResolve origAsm).1` throughout — matching `codegen_correct_sched`'s `hstep`. `hidx : idx =
    pcOfLabel prog bb'.label` is discharged via `resolvedJump_idx_eq_pcOfLabel` (over `origAsm`) +
    `pcOfLabel_asmResolve` (label positions survive resolution). -/
theorem hstep_jmp_of_layout {fn : IrFunction} {ctx : VenomContext}
    {origAsm pre suf : List AsmInst} {labelOffsets : AssocList String Nat}
    (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen off idx : Nat}
    (horig : origAsm = pre ++ AsmInst.AsmLabel bb'.label :: suf)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel bb'.label ∧ inst ≠ AsmInst.AsmDataHeader bb'.label)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel bb'.label)
    (hoff_lk : AssocList.lookup String Nat (computeLabelOffsets origAsm).2 bb'.label = some off)
    (hidx_lk : AssocList.lookup Nat Nat (asmResolve origAsm).2 off = some idx)
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOfLabel (asmResolve origAsm).1 bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hidx : idx = pcOfLabel (asmResolve origAsm).1 bb'.label := by
    rw [pcOfLabel_asmResolve, horig]
    exact resolvedJump_idx_eq_pcOfLabel pre suf bb'.label off idx hsuf hpre (horig ▸ hoff_lk) (horig ▸ hidx_lk)
  exact hstep_jmp_block (pcOf := pcOfLabel (asmResolve origAsm).1) psOf wOf hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk' hwdec


/-- **Canonical-scheduling scaffold for `codegen_correct_sched`.** Instantiates the budget-ranked bridge
    with the *canonical* schedule — `pcOf := pcOfLabel prog`, `psOf := psOfFn`, and the rank
    `wOf l := prog.length - pcOfLabel prog l` (which decreases by exactly a block's asm length across
    each JMP) — and discharges the three entry obligations automatically: `hpc0` from the entry's
    JUMPDEST being at pc 0 (`hpc0zero`), `hw0` from the rank being ≤ `prog.length`, and the entry
    relation from `psOfFn_entry` (`psOfFn entry = init`). Reduces a whole-function capstone to just the
    per-block `hstep` for the canonical schedule. -/
theorem codegen_correct_canonical {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat} {entry : BasicBlock}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hentryblk : entryBlock fn = some entry)
    (hentrylbl : entryLbl = entry.label)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hlk0 : lookupBlock entryLbl fn.blocks = some entry)
    (hpc0zero : pcOfLabel (asmResolve (executePlan ops)).1 entry.label = 0)
    (haspc : as.pc = 0)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOfLabel (asmResolve (executePlan ops)).1 bb.label →
        venomAsmRel lo (psOfFn (fnPlanFuel fn) fn fnEom lblCtr bb.label) s asm →
        (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb.label ≤ N →
        s.halted = false →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOfLabel (asmResolve (executePlan ops)).1 bb'.label ∧
                venomAsmRel lo (psOfFn (fnPlanFuel fn) fn fnEom lblCtr bb'.label) s' asm' ∧
                ((asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb'.label) + blockLen
                  ≤ (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb.label
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo { initPlanState fnEom with labelCounter := lblCtr }
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfuelpos : 0 < fnPlanFuel fn := by simp only [fnPlanFuel]; omega
  have hpsofentry : psOfFn (fnPlanFuel fn) fn fnEom lblCtr entry.label
      = { initPlanState fnEom with labelCounter := lblCtr } := psOfFn_entry hentryblk hfn hfuelpos
  refine codegen_correct_sched (fuel := fuel) hplan hent hlk hlbl
    (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel fn) fn fnEom lblCtr)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    hstep (bb0 := entry) hlk0 ?_ ?_ hvshalt ?_
  · rw [haspc]; exact hpc0zero.symm
  · omega
  · rw [hpsofentry, hentrylbl]; exact hrel

/-- **Per-block STOP `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_stop_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_stop_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "STOP")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "STOP" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_stop P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN


/-- **Per-block INVALID `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_invalid_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_invalid_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "INVALID")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "INVALID" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_invalid P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN



/-- **Per-block RETURN `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_return_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_return_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "RETURN")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "RETURN" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_return pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN


end EvmYul.Venom.Hol.Codegen

import EvmYul.Venom.Hol.Codegen.GenBlockSim.HstepGenerations

/-!
# GenBlockSim -- WalkJoinsLoops

The shallow-stack bound, the scheduler join-agreement invariant, per-block-sim to walk,
joins with a body, and loops.
-/

open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/-! ### The shallow-stack bound is not a restriction

`popmanyPlan_sim_closed` and the block prologue require `stack.length ≤ 17`, which is what keeps every
`doSwap` inside `SWAP16` and out of the temp spill region. I had recorded that as an honest restriction
to be lifted later — by threading `doSwap_big_sim`'s spill side conditions into the fold invariant.

It needs no lifting. `StackDiscHS.shallow` already caps the plan stack at **15**, and `StackDiscHS` is the
invariant the entire body-simulation machinery threads through every block. So any state the development
governs at all already satisfies the bound, with room to spare: the clean-stack prologue's shallow
requirement costs nothing beyond what its surroundings already demand, and the big-swap spill path is
simply never reached. -/

/-- `StackDiscHS` already caps the plan stack at 15. -/
theorem StackDiscHS.stack_le_15 {k p v s} (h : StackDiscHS k p v s) : p.stack.length ≤ 15 := by
  have := h.shallow; omega

/-- Hence the shallow-stack side condition of `popmanyPlan_sim_closed` costs nothing: any state the
    body-sim machinery governs already satisfies it. -/
theorem StackDiscHS.shallow17 {k p v s} (h : StackDiscHS k p v s) : p.stack.length ≤ 17 := by
  have := h.shallow; omega

/-- `popmanyPlan` simulates, with the shallow bound supplied by the invariant the development already
    threads rather than assumed outright. -/
theorem popmanyPlan_sim_of_sd {toPop : List Operand} {ps ps' : PlanState} {ops : List StackOp}
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst} {k : Nat}
    {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS k ps vs as)
    (hpop : popmanyPlan toPop ps = (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hlen : toPop.length < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length :=
  popmanyPlan_sim_closed hpop hrel hsd.shallow17 hlen hblock

/-- The block prologue, likewise. -/
theorem blockPrologue_prefix_sim_of_sd {lo : AssocList String Nat} {vs : VenomState}
    {prog : List AsmInst} {ps0 ps2 : PlanState} {cleanOps : List StackOp} {toPop : List Operand}
    {as0 : AsmState} {l : String} {k : Nat} {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS k ps0 vs as0)
    (hrel : venomAsmRel lo ps0 vs as0)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hlen : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc (executePlan ([StackOp.SOLabel l] ++ cleanOps))) :
    ∃ asMid, runAsm (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length offsetToPc prog as0
               = AsmResult.AsmOK asMid ∧
             venomAsmRel lo ps2 vs asMid ∧
             asMid.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length :=
  blockPrologue_prefix_sim hrel hpop hsd.shallow17 hlen hblock


/-! ### Where ④ actually still stands: the scheduler's join-agreement invariant

With items 1-4 closed and both DFS side conditions discharged, exactly one thing is left, and it is worth
naming precisely rather than leaving as "generic `hres`".

`hres` says a block's post-body plan state equals its successor's *recorded* entry state. Along a DFS
tree edge that holds by construction — the successor is recorded *with* the predecessor's exit. At a join
reached from a second predecessor it is not automatic. And the compiler emits nothing to fix it up:
`cleanStackPlan` fires only at a block with exactly one predecessor, so a genuine (≥2-predecessor) join
gets no stack reconciliation at all (below).

So the residual is not a gap in the *simulation* — it is a property of the **plan generator**: every
predecessor of a block must exit with the plan state that block was recorded with. That is the stack
scheduler's join-agreement invariant, and it is the honest remaining content of ④. -/

/-- **A genuine join gets no reconciliation.** `cleanStackPlan` fires only at a block with *exactly one*
    predecessor (a JNZ branch target). At a block with two or more predecessors it emits nothing —
    `cleanTrivial_of_multi` — so the compiler performs no stack fix-up there at all.

    This pins what generic `hres` actually asks for. `hres` says a block's post-body plan state equals its
    successor's *recorded* entry state. That holds by construction along DFS tree edges (the successor is
    recorded *with* the predecessor's exit). At a join reached from a second predecessor it is not
    automatic — and, because nothing is emitted to fix it up, it must already be true. So the residual is
    not a simulation gap but a property of the **plan generator**: every predecessor of a block must exit
    with the plan state that block was recorded with. That is the stack scheduler's join-agreement
    invariant, and it is the honest remaining content of ④. -/
theorem no_reconciliation_at_join
    {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction} {bb : BasicBlock} {ps : PlanState}
    (hmulti : 2 ≤ (C.predsOf bb.label).length) :
    cleanStackPlan L C fn bb ps = ([], ps) :=
  cleanTrivial_of_multi (by omega) ps



/-- **`BlockSim` really is the conclusion `genBlockSimulation` proves.**

`BlockSim` is a definition written in this development to name that conclusion so it can be moved
between results. If it did not actually match, `BlockSim_join` could not consume `genBlockSimulation`
and the whole transfer would be decorative. It matches — definitionally. -/
theorem BlockSim_eq_genBlockSim_concl
    (labelOffsets : AssocList String Nat) (ps' : PlanState) (offsetToPc : AssocList Nat Nat)
    (ops : List StackOp) (as : AsmState) (r : ExecResult) :
    BlockSim labelOffsets ps' offsetToPc (asmResolve (executePlan ops)).1 as r
      = (match r with
        | ExecResult.OK vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
        | ExecResult.Halt vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
        | ExecResult.Abort AbortType.RevertAbort vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
            venomAsmTerminalRel vs' as'
        | ExecResult.Abort AbortType.ExHaltAbort vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
            venomAsmTerminalRel vs' as'
        | _ => True) := by
  cases r with
  | OK _ => rfl
  | Halt _ => rfl
  | Abort t _ => cases t <;> rfl
  | IntRet _ _ => rfl
  | Error _ => rfl



/-- **`genBlockSimulation`, for a genuine join.**

The family proper cannot be instantiated here — its `hphi` hypothesis demands a non-phi head, and a
join's head is a phi. This is the drop-in: give it a simulation for the block's *phi-free residual*, and
it yields the same conclusion for the join.

**But note what `hres` must be a simulation of.** It is about running the residual — the instructions
after the phis — against a program that assembles to the same thing the join's plan does. It is **not**
about `generateBlockPlan` applied to a synthetic residual `BasicBlock`: the generator looks liveness up
*by position within the block*, so dropping the phis shifts every later index and it emits different code
(`residual_block_compiles_differently` pins this, and the difference is real: 4 instructions against 5).
The program to use is the join's own — its body plan with the phi prologue in front, which assembles to
exactly the body plan alone (`executePlan_join_eq_residual`), because a phi prologue emits nothing.

On any incoming edge, the phis are discharged, the asm does not move, and the two runs agree up to the
instruction index — which neither `venomAsmRel` nor `venomAsmTerminalRel` can see. -/
theorem genBlockSimulation_join
    {fuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock} {phis : List Instruction}
    {vs vs' : VenomState} {ps' : PlanState} {ops resOps : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hbb : bb.instructions = phis ++ bb'.instructions)
    (hphi : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hnext : ∀ i, bb'.instructions.head? = some i → i.opcode ≠ Opcode.PHI)
    (hno : ∀ inst ∈ bb'.instructions, inst.opcode ≠ Opcode.INVOKE)
    (hnx : ∀ inst ∈ bb'.instructions, isExternalCall inst.opcode = false)
    (hstep : ∀ inst ∈ bb'.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
        ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2))
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    -- the join's plan and the residual's differ by the phi prologue, which assembles to nothing
    -- (`executePlan_join_eq_residual`) — so they produce the same program, which is all the
    -- simulation sees. Without this the reuse of the program below would be an assumption.
    (hops : executePlan ops = executePlan resOps)
    (hres : match runBlock fuel ctx bb' vs' with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True) :
    match runBlock fuel ctx bb vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True := by
  rw [hops]
  exact BlockSim_join hbb hphi hnext hno hnx hstep hev hres


/-- `genBlockSimulation` for a join, stated on the join's own block and plan — no residual block. -/
theorem genBlockSimulation_join_self {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {vs vs' : VenomState} {ps' : PlanState} {ops : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    (hres : match execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions } with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True) :
    match runBlock fuel ctx bb vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True :=
  BlockSim_join_self hev hres


/-! ### From the per-block simulation to the walk, for a join

`genBlockSimulation_join_self` hands back a join's `BlockSim`. The walk wants a `WalkStep`. These are
*not* the same proposition, and the difference is easy to miss: `BlockSim`'s terminal arms run the asm
with `prog.length` fuel, `WalkStep`'s run it with the walk's budget `N`. They line up only when
`N = prog.length`, which is why `hN` is a hypothesis below rather than an omission. (I expected these
three arms to be definitionally equal and they were not — the probe said so before the prose did.)

With that, both halves of the `hphi` barrier are gone: the per-block simulation accepts a PHI-headed
block, and so does the walk clause it feeds. -/

/-- Terminal arms: `BlockSim` and `WalkStep` are the same proposition. -/
theorem WalkStep_of_BlockSim_terminal {fn ctx pcOf psOf wOf labelOffsets offsetToPc prog bb as N f'}
    {s : VenomState} {ps' : PlanState}
    (hN : N = prog.length)
    (hterm : (∀ w, runBlock f' ctx bb s ≠ ExecResult.OK w))
    (hbs : BlockSim labelOffsets ps' offsetToPc prog as (runBlock f' ctx bb s)) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb as N
      (runBlock f' ctx bb s) := by
  subst hN
  cases hr : runBlock f' ctx bb s with
  | OK w => exact absurd hr (hterm w)
  | Halt w => rw [hr] at hbs; exact hbs
  | Abort a w => cases a <;> (rw [hr] at hbs; exact hbs)
  | IntRet _ _ => trivial
  | Error _ => trivial

/-! ### REMOVED: `WalkStep_of_BlockSim_ok`

It carried the block's asm run at `prog.length` fuel. With `prog` the whole function's program — which is
what the walk needs — that arm is *false* for any block that continues: a continuing block does not stop at
its own boundary, it runs on into its successor. See `dia_blockSim_ok_false_at_whole_prog` for the
refutation and `WalkStep_of_BlockSimAt` for the replacement, which takes the block's asm length as a
parameter instead of reading it off the program. -/

/-- **A general join's walk obligation, straight from the compiler.** `genBlockSimulation_join_self`
gives the join's `BlockSim`; this turns it into the walk's `WalkStep`. The `hphi` barrier is gone on
both halves now: the per-block sim accepts a PHI-headed block, and so does the walk. -/
theorem WalkStep_join_of_genBlockSim_terminal {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {fn : IrFunction} {vs vs' : VenomState} {ps' : PlanState} {ops : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {N : Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hN : N = (asmResolve (executePlan ops)).1.length)
    (hterm : ∀ w, runBlock fuel ctx bb vs ≠ ExecResult.OK w)
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    (hres : BlockSim labelOffsets ps' offsetToPc (asmResolve (executePlan ops)).1 as
      (execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions })) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc (asmResolve (executePlan ops)).1 bb as N
      (runBlock fuel ctx bb vs) :=
  WalkStep_of_BlockSim_terminal hN hterm (genBlockSimulation_join_self hev hres)


/-- **The driver accepts `WalkStep`s — so it accepts joins.**

`codegen_correct_sched` is the real whole-function driver, and its `hstep` hypothesis is spelled out
inline. This restates that hypothesis as a `WalkStep` and closes the theorem by handing over
`codegen_correct_sched` itself: it typechecks by `exact`, so the two are *definitionally* the same
obligation. That is what makes the join work of this arc load-bearing rather than decorative —
`hstep_jmp_block_join`, `hstep_bareTerm_{halt,revert,fault}_join` and `hstep_jnz_{taken,nottaken}_join`
all produce `WalkStep`s, so they can be fed to this driver directly, with no adapter.

(Stating the driver's obligation as my own predicate and *not* proving the correspondence is exactly
the trap this branch has now walked into six times. Hence the `exact`.) -/
theorem codegen_correct_sched_ws
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        WalkStep fn pcOf psOf wOf lo (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 bb asm N (runBlock f' ctx bb s))
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_sched hplan hent hlk hlbl pcOf psOf wOf hstep bb0 hlk0 hpc0 hw0 hvshalt hrel


/-! ### Joins with a body

The bare-terminator join hsteps above take a block `phis ++ [term]` and derive its `execBlock` from that
syntax. That was more machinery than the job needs. `WalkStep_join` already transfers the walk obligation
across the phi prologue for an *arbitrary* block, so a join with any body at all — a join whose body reads
the phi's own output, say — needs only its post-phi `execBlock` result and the asm witness. Each of these
is one line, and each is strictly more general than its bare-terminator counterpart.

(The bare-terminator forms are kept: they are the convenient entry point when the block's syntax is what
you have. But the general primitive is here, and it is what a join with a body needs.) -/

/-- **Halting join, ANY body.** -/
theorem hstep_join_halt {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Halt sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)

/-- **Reverting join, ANY body.** -/
theorem hstep_join_revert {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Abort AbortType.RevertAbort sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)

/-- **Faulting join, ANY body.** -/
theorem hstep_join_fault {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Abort AbortType.ExHaltAbort sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)


/-! ### The driver's `Entry` is too weak for a phi join

`codegen_correct_sched`'s `Entry` carries a block, a pc, a `venomAsmRel`, a rank bound and `halted =
false`. That is everything a phi-free block needs and *not* everything a join needs.

A join's `evalPhis` reads its sources out of `vars`, so discharging it requires knowing which predecessor
the walk arrived from and that that predecessor's variable is bound. `venomAsmRel` says nothing about
`vars` — and it cannot be made to, because the compiler is entitled to drop a variable the EVM no longer
needs (a phi does not *use* its sources, so it pops them). The witness for `evalPhis` is exactly the
information the stack no longer carries.

`codegen_correct`, underneath, takes `Entry` as a free parameter. So the fix is not to weaken the join but
to thread an invariant: `codegen_correct_sched_inv` hands `Inv s` to each `hstep` and requires it back at
the successor, which is the standard way to carry a fact the relation deliberately forgets. -/
/-- The walk's per-block obligation, carrying a user invariant `Inv` to the successor. -/
def WalkStepInv (Inv : VenomState → Prop) (fn : IrFunction) (pcOf : String → Nat)
    (psOf : String → PlanState) (wOf : String → Nat) (labelOffsets : AssocList String Nat)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (bb : BasicBlock)
    (asm : AsmState) (N : Nat) : ExecResult → Prop
  | ExecResult.OK s' =>
      if s'.halted then
        ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      else
        ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
          lookupBlock s'.currentBb fn.blocks = some bb'' ∧
          runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
          asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
          wOf bb''.label + blockLen' ≤ wOf bb.label ∧ Inv s'
  | ExecResult.Halt s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.RevertAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.ExHaltAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
  | _ => True

/-- **The budget-ranked driver, with a user invariant threaded through the walk.** -/
theorem codegen_correct_sched_inv
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (Inv : VenomState → Prop)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        Inv s →
        WalkStepInv Inv fn pcOf psOf wOf lo (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 bb asm N (runBlock f' ctx bb s))
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as)
    (hInv0 : Inv { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 }) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl)
    (Entry := fun s asm N => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
       asm.pc = pcOf bb.label ∧ venomAsmRel lo (psOf bb.label) s asm ∧ wOf bb.label ≤ N ∧
       s.halted = false ∧ Inv s)
    hplan hent hlk hlbl ?_ ⟨bb0, hlk0, hpc0, hrel, hw0, hvshalt, hInv0⟩
  intro s asm N f' bb hE hlk'
  obtain ⟨bb', hlkbb, hpc, hvrel, hwN, hnh, hinv⟩ := hE
  rw [hlk'] at hlkbb; injection hlkbb with hbbeq; subst hbbeq
  have hb := hstep bb s asm N f' hlk' hpc hvrel hwN hnh hinv
  cases hrb : runBlock f' ctx bb s with
  | OK s' =>
    rw [hrb] at hb
    by_cases hh : s'.halted
    · simp only [WalkStepInv, hh, if_true] at hb ⊢; exact hb
    · simp only [WalkStepInv, hh, Bool.false_eq_true, if_false] at hb ⊢
      obtain ⟨bb'', asm', blockLen, hlk'', hrun, hle, hpc', hvrel', hwdec, hinv'⟩ := hb
      refine ⟨asm', N - blockLen, ?_, bb'', hlk'', hpc', hvrel', by omega, by simp, hinv'⟩
      conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
      exact runAsm_append_ok hrun
  | Halt s' => rw [hrb] at hb; exact hb
  | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
  | IntRet _ _ => trivial
  | Error _ => trivial


/-! ## Loops

Loops need no dedicated top-level theorem. `codegen_correct_fuel` (in `CodegenCorrectness`) is already the
loop-admitting driver: its asm budget is `fuel * B` (Venom's own fuel × a per-block bound) with the
uniform per-block obligation `blockLen ≤ B` rather than a strictly decreasing per-label rank — nothing
orders the blocks, so a back-edge has nothing to violate; `codegen_correct_fuel_sched` is the scheduled
counterpart. A real back-edge is driven end to end through it by `codegen_correct_loopVFn_fuel`
(`GenBlockSimExample`): `entry: %a = CALLVALUE ; JNZ %a entry exit` / `exit: STOP`
(`loopVFn_back_edge`), both JNZ arms, on the real generated program, at budget `fuel * 8`. -/

end EvmYul.Venom.Hol.Codegen

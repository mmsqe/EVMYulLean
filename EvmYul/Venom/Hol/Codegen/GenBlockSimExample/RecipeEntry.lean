/-
GenBlockSimExample / the discriminating recipe version and the OK-continuing Entry arm

Split part of `GenBlockSimExample`; see that module's header for the full roadmap.
This part is wrapped in `namespace EvmYul.Venom.Hol.Codegen` (the enclosing namespace of the second half); layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.Dispatch

namespace EvmYul.Venom.Hol.Codegen

/-! ### The discriminating version: a body of two different opcodes

A one-instruction body is degenerate — `execBodyThread`'s induction never iterates, and only one
discharger is exercised. `JoinBody2` is a join whose body is `q = ISZERO p ; SSTORE d q`: two instructions,
two *different* opcodes, and the second reads what the first wrote. The thread genuinely iterates, and
`hobliv` has to be dispatched per instruction rather than supplied once. -/

namespace JoinBody2
def iQ : Instruction :=
  { id := 70, opcode := Opcode.ISZERO, operands := [Operand.Var "p"], outputs := ["q"] }
def iSt : Instruction :=
  { id := 71, opcode := Opcode.SSTORE,
    operands := [Operand.Var "d", Operand.Var "q"], outputs := [] }
def body : List Instruction := [iQ, iSt]
end JoinBody2

/-- `hobliv` for a two-opcode body: dispatched per instruction, using two different `StepObliv` lemmas. -/
theorem joinbody2_hobliv :
    ∀ inst ∈ JoinBody2.body, ∀ (t t' : VenomState) (j : Nat),
      stepInstBase inst t = ExecResult.OK t' →
      stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j } := by
  intro inst hi
  simp only [JoinBody2.body, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact stepObliv_iszero rfl
  · exact stepObliv_sstore rfl

/-- **The obliviousness chain, consumed on a body that actually iterates.** Threading the two-instruction
body from a join's resume point and from zero agree, up to the index — which is the fact that lets a body
simulation written at `instIdx = 0` be reused at the offset a join resumes from. -/
theorem joinbody2_thread_offset_congr
    {s s' sEnd sEnd' : VenomState} {start start' : Nat}
    (hss : { s with instIdx := 0 } = { s' with instIdx := 0 })
    (h1 : execBodyThread JoinBody2.body start s = some sEnd)
    (h2 : execBodyThread JoinBody2.body start' s' = some sEnd') :
    { sEnd with instIdx := 0 } = { sEnd' with instIdx := 0 } :=
  execBodyThread_instIdx_congr JoinBody2.body joinbody2_hobliv start start' s s' sEnd sEnd'
    hss h1 h2

/-! ## The four join hsteps that had no witness

The systematic sweep found that `hstep_jnz_taken_join`, `hstep_jnz_nottaken_join`, `hstep_join_revert` and
`hstep_join_fault` had zero consumers. For the two `JNZ` ones I had witnessed only the *inputs* —
`jnzjoin_ev`, `jnzjoin_cond` — and never composed them into the hstep, which is a weaker thing than I said
at the time.

These four compose. The `JNZ` pair share a block and differ only in the value the phi delivers: `a = 7`
takes the branch, `a = 0` does not. That the same block goes both ways depending on the phi is the whole
reason a `JNZ` join needed its own hstep at all.

The revert and fault pair are joins *with a body* — `p = phi(…) ; SSTORE d p ; REVERT`/`INVALID` — so the
body consumes the phi's output before the block aborts. That is the shape `hstep_join_{revert,fault}` were
written for, and nothing had exercised it. -/
/-- **JNZ-taken join, composed.** `JoinShapes.bJnz` is `p = phi(then→a, else→b) ; JNZ p, t2, e2`, and it
branches on its *own phi output*. Arriving from `then` with `a = 7`, the branch is taken. -/
theorem jnzjoin_taken_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb' : BasicBlock} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo "t2" { updateVar "p" Min.av Min.vs with instIdx := 1 }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock "t2" fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf JoinShapes.bJnz.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinShapes.bJnz asm N
      (runBlock (extraFuel + 1) ctx JoinShapes.bJnz Min.vs) :=
  hstep_jnz_taken_join (phis := [Min.pP]) (jnzInst := JoinShapes.jJnz)
    (condOp := Operand.Var "p") (ifNz := "t2") (ifZ := "e2") (cond := Min.av)
    pcOf psOf wOf jnzjoin_ev rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl)
    rfl rfl jnzjoin_cond (by decide) rfl hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk' hwdec

/-- A state arriving at the JNZ join where the phi's source is **zero**, so the branch is *not* taken.
Same block; only the incoming value differs — which is the point: the branch depends on the phi. -/
def JoinShapes.vsZero : VenomState :=
  { (default : VenomState) with
    vars := [("a", EvmYul.UInt256.ofNat 0)],
    prevBb := some "then", currentBb := "join" }

theorem jnzjoin_ev_zero :
    evalPhis JoinShapes.vsZero JoinShapes.bJnz.instructions
      = ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 0) JoinShapes.vsZero) := by
  show evalPhis JoinShapes.vsZero (Min.pP :: [JoinShapes.jJnz]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then")
        (v := EvmYul.UInt256.ofNat 0) (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis JoinShapes.vsZero [JoinShapes.jJnz] with
        | ExecResult.OK s' =>
            ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 0) s') | err => err) = _
  rw [show evalPhis JoinShapes.vsZero [JoinShapes.jJnz]
        = ExecResult.OK JoinShapes.vsZero from by unfold evalPhis; rw [if_pos (by decide)]]

theorem jnzjoin_cond_zero :
    evalOperand (Operand.Var "p")
      { (updateVar "p" (EvmYul.UInt256.ofNat 0) JoinShapes.vsZero) with
        instIdx := [Min.pP].length } = some (EvmYul.UInt256.ofNat 0) := rfl

/-- **JNZ-not-taken join, composed.** The same phi-headed block, entered with a phi source of zero: the
branch is not taken and control falls to `e2`. -/
theorem jnzjoin_nottaken_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb' : BasicBlock} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo "e2" { updateVar "p" (EvmYul.UInt256.ofNat 0) JoinShapes.vsZero with instIdx := 1 })
        asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock "e2" fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf JoinShapes.bJnz.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinShapes.bJnz asm N
      (runBlock (extraFuel + 1) ctx JoinShapes.bJnz JoinShapes.vsZero) :=
  hstep_jnz_nottaken_join (phis := [Min.pP]) (jnzInst := JoinShapes.jJnz)
    (condOp := Operand.Var "p") (ifNz := "t2") (ifZ := "e2")
    (cond := EvmYul.UInt256.ofNat 0)
    pcOf psOf wOf jnzjoin_ev_zero rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl)
    rfl rfl jnzjoin_cond_zero rfl rfl hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk' hwdec

namespace JoinBodyRF
/-- A join **with a body** that then reverts: `p = phi(…) ; SSTORE d p ; REVERT 0 0`. -/
def bRev : BasicBlock :=
  { label := "join", instructions := [Min.pP, JoinBody.bSst, JoinShapes.jRevert] }
/-- …and one that faults. -/
def bFlt : BasicBlock :=
  { label := "join", instructions := [Min.pP, JoinBody.bSst, JoinShapes.jInvalid] }
end JoinBodyRF

theorem ev_of_body (term : Instruction) (hnp : term.opcode ≠ Opcode.PHI) (bb : BasicBlock)
    (hbb : bb.instructions = [Min.pP, JoinBody.bSst, term]) :
    evalPhis JoinBody.vs bb.instructions
      = ExecResult.OK (updateVar "p" Min.av JoinBody.vs) := by
  rw [hbb]
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis JoinBody.vs [JoinBody.bSst, term] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis JoinBody.vs [JoinBody.bSst, term] = ExecResult.OK JoinBody.vs from by
    unfold evalPhis; rw [if_pos (by decide)]]

/-- The post-phi body runs (`SSTORE d p` — reading the phi's output) and then the block reverts. -/
theorem joinrev_res (f : Nat) (ctx : VenomContext) :
    execBlock (f + 1 + 1) ctx JoinBodyRF.bRev JoinBody.sPhi1
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata
            (readMemory 0 0 { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })
            { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })) := by
  rw [execBlock_step_nonterm (f + 1) ctx JoinBodyRF.bRev JoinBody.sPhi1
        (sstore JoinBody.dv Min.av JoinBody.sPhi1) JoinBody.bSst (by rfl) (by rfl) (by decide)]
  exact execBlock_step_abort f ctx JoinBodyRF.bRev _ _ JoinShapes.jRevert _ (by rfl) rfl

/-- **`hstep_join_revert` composes**, on a join whose body consumes the phi. -/
theorem joinrev_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {asm : AsmState} {N f : Nat}
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
      venomAsmTerminalRel
        (revertState (setReturndata
          (readMemory 0 0 { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })
          { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinBodyRF.bRev asm N
      (runBlock (f + 1 + 1) ctx JoinBodyRF.bRev JoinBody.vs) :=
  hstep_join_revert (ev_of_body JoinShapes.jRevert (by decide) _ rfl)
    (by rw [show phiPrefixLength JoinBodyRF.bRev.instructions = 1 from by decide]
        exact joinrev_res f ctx) hasm

/-- The same block, faulting. -/
theorem joinflt_res (f : Nat) (ctx : VenomContext) :
    execBlock (f + 1 + 1) ctx JoinBodyRF.bFlt JoinBody.sPhi1
      = ExecResult.Abort AbortType.ExHaltAbort
          (haltState (setReturndata ByteArray.empty
            { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })) := by
  rw [execBlock_step_nonterm (f + 1) ctx JoinBodyRF.bFlt JoinBody.sPhi1
        (sstore JoinBody.dv Min.av JoinBody.sPhi1) JoinBody.bSst (by rfl) (by rfl) (by decide)]
  exact execBlock_step_abort f ctx JoinBodyRF.bFlt _ _ JoinShapes.jInvalid _ (by rfl) rfl

/-- **`hstep_join_fault` composes**, likewise. -/
theorem joinflt_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {asm : AsmState} {N f : Nat}
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
      venomAsmTerminalRel
        (haltState (setReturndata ByteArray.empty
          { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinBodyRF.bFlt asm N
      (runBlock (f + 1 + 1) ctx JoinBodyRF.bFlt JoinBody.vs) :=
  hstep_join_fault (ev_of_body JoinShapes.jInvalid (by decide) _ rfl)
    (by rw [show phiPrefixLength JoinBodyRF.bFlt.instructions = 1 from by decide]
        exact joinflt_res f ctx) hasm

/-! ## The generic `hobliv` discharger — which consumes the whole `stepObliv` family

Consuming the seventeen `StepObliv` lemmas one at a time, on bodies invented to contain them, would be
theatre: it would clear the 0-consumer flag without making any of them useful.

`stepObliv_of_oblivious` is what a caller actually wants. `ObliviousOpcode` is a decidable predicate, so
`hobliv` for a concrete body becomes `by decide` — the caller names no lemma at all, and adding an opcode
to the set extends every existing caller at once. Compare `joinbody2_hobliv` above, which had to dispatch
by hand.

This consumes all seventeen, and it is the first thing in this development that makes the coverage matrix
mean something to a user of it rather than to its author. -/
/-- The opcodes for which instruction-index obliviousness is discharged. Decidable, so a caller checks it
by `decide` rather than by hand. -/
def ObliviousOpcode : Opcode → Bool
  | Opcode.ADD | Opcode.ISZERO | Opcode.ADDMOD | Opcode.SLOAD | Opcode.SSTORE | Opcode.CALLER
  | Opcode.ASSIGN | Opcode.NOP | Opcode.MCOPY | Opcode.ISTORE | Opcode.ASSERT
  | Opcode.SHA3 | Opcode.CALLDATACOPY | Opcode.CODECOPY | Opcode.EXTCODECOPY
  | Opcode.RETURNDATACOPY | Opcode.LOG => true
  | _ => false

/-- **The generic `hobliv` discharger.** One lemma per opcode is what `StepObliv` needs; this dispatches
over them, so a caller with a concrete body discharges `hobliv` by `decide` on each instruction's opcode
instead of naming a lemma. -/
theorem stepObliv_of_oblivious {inst : Instruction}
    (h : ObliviousOpcode inst.opcode = true) : StepObliv inst := by
  cases hop : inst.opcode <;>
    first
      | exact stepObliv_add hop
      | exact stepObliv_iszero hop
      | exact stepObliv_addmod hop
      | exact stepObliv_sload hop
      | exact stepObliv_sstore hop
      | exact stepObliv_caller hop
      | exact stepObliv_assign hop
      | exact stepObliv_nop hop
      | exact stepObliv_mcopy hop
      | exact stepObliv_istore hop
      | exact stepObliv_assert hop
      | exact stepObliv_sha3 hop
      | exact stepObliv_calldatacopy hop
      | exact stepObliv_codecopy hop
      | exact stepObliv_extcodecopy hop
      | exact stepObliv_returndatacopy hop
      | exact stepObliv_log hop
      | (rw [hop] at h; exact absurd h (by decide))

/-- **`hobliv` for a whole body, by `decide`.** This is the form `execBodyThread_instIdx_congr` wants. -/
theorem hobliv_of_body {body : List Instruction}
    (h : body.all (fun i => ObliviousOpcode i.opcode) = true) :
    ∀ inst ∈ body, ∀ (t t' : VenomState) (j : Nat),
      stepInstBase inst t = ExecResult.OK t' →
      stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j } := by
  intro inst hi
  exact stepObliv_of_oblivious (by simpa using List.all_eq_true.mp h inst hi)

/-- **The whole point, in one line.** `hobliv` for `JoinBody2`'s body is now `by decide` — the caller
names no lemma, and adding an opcode to `ObliviousOpcode` extends every such caller at once. Compare
`joinbody2_hobliv`, which had to dispatch by hand. -/
theorem joinbody2_hobliv_by_decide :
    ∀ inst ∈ JoinBody2.body, ∀ (t t' : VenomState) (j : Nat),
      stepInstBase inst t = ExecResult.OK t' →
      stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j } :=
  hobliv_of_body (by decide)

/-- And it scales: a body of five different opcodes, all discharged by one `decide`. -/
def wideBody : List Instruction :=
  [{ id := 80, opcode := Opcode.SHA3, operands := [], outputs := [] },
   { id := 81, opcode := Opcode.CALLDATACOPY, operands := [], outputs := [] },
   { id := 82, opcode := Opcode.MCOPY, operands := [], outputs := [] },
   { id := 83, opcode := Opcode.LOG, operands := [], outputs := [] },
   { id := 84, opcode := Opcode.ASSERT, operands := [], outputs := [] }]

theorem wideBody_hobliv :
    ∀ inst ∈ wideBody, ∀ (t t' : VenomState) (j : Nat),
      stepInstBase inst t = ExecResult.OK t' →
      stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j } :=
  hobliv_of_body (by decide)

/-! ## The three `hgood`-free drop-ins, consumed on the one function that needs them

The sweep found `hpreuniq_of_blockPlan_fresh`, `labelOffset_of_blockPlan_fresh` and
`jumpTarget_of_blockPlan_fresh` with no consumers — which for a drop-in is a fair question, since a
replacement nothing calls has not been shown to replace anything.

They are consumed here, on `Dj.fn`. That is the discriminating case rather than a convenient one: the
`hgood` forms *cannot* be applied to this function at all, because `dj_hgood_false` proves their hypothesis
unsatisfiable. So these three are doing a job nothing else in the development can do. -/
/-- **`hpreuniq` from a block plan, for the `DJMP` function.** The `hgood` form
(`hpreuniq_of_blockPlan`) *cannot* be applied here — `dj_hgood_false` shows its hypothesis is
unsatisfiable — so this is the drop-in doing the job nothing else can. -/
theorem dj_hpreuniq_of_blockPlan {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {blockOps : List StackOp} {psB ps' : PlanState} {bb : BasicBlock}
    (hbb : bb ∈ Dj.fn.blocks)
    (hbp : generateBlockPlan L D C Dj.fn bb psB = some (blockOps, ps')) :
    ∀ preOps tailOps, Dj.ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_of_blockPlan_fresh (fuel := fnPlanFuel Dj.fn) (fnEom := 0) (lblCtr := 0)
    (dj_labels_not_fresh bb hbb) rfl hbp

/-- **The whole jump-target family (`hoff_lk` + `hidx_lk` + `hidxeq`), for the `DJMP` function.** Same
story: the `hgood` form is inapplicable, and the naming condition carries it through. -/
theorem dj_jumpTarget_of_blockPlan {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {pre suf blockOps : List StackOp} {psB ps' : PlanState} {bb : BasicBlock}
    (hbb : bb ∈ Dj.fn.blocks)
    (hbp : generateBlockPlan L D C Dj.fn bb psB = some (blockOps, ps'))
    (hseg : Dj.ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan Dj.ops)).2 bb.label
        = some (((executePlan pre).map asmInstSize).sum) ∧
    AssocList.lookup Nat Nat (asmResolve (executePlan Dj.ops)).2
        (((executePlan pre).map asmInstSize).sum) = some (executePlan pre).length ∧
    pcOfLabel (asmResolve (executePlan Dj.ops)).1 bb.label = (executePlan pre).length :=
  jumpTarget_of_blockPlan_fresh (fuel := fnPlanFuel Dj.fn) (fnEom := 0) (lblCtr := 0)
    (dj_labels_not_fresh bb hbb) rfl hbp hseg

/-- …and `hoff_lk` alone. -/
theorem dj_labelOffset_of_blockPlan {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {pre suf blockOps : List StackOp} {psB ps' : PlanState} {bb : BasicBlock}
    (hbb : bb ∈ Dj.fn.blocks)
    (hbp : generateBlockPlan L D C Dj.fn bb psB = some (blockOps, ps'))
    (hseg : Dj.ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan Dj.ops)).2 bb.label
      = some (((executePlan pre).map asmInstSize).sum) :=
  labelOffset_of_blockPlan_fresh (fuel := fnPlanFuel Dj.fn) (fnEom := 0) (lblCtr := 0)
    (dj_labels_not_fresh bb hbb) rfl hbp hseg

/-! ## The compiler-level join route, consumed

`WalkStep_join_of_genBlockSim_terminal` composes `genBlockSimulation_join_self` with the terminal transfer
in one step, and had no consumer — `min_walkstep_join_of_genBlockSim` reached the same conclusion by doing
the composition inline, which left the lemma unexercised.

This feeds it `Min`'s `evalPhis` and its post-phi block simulation directly and gets the walk's obligation
for a phi-headed block, with nothing left assumed. -/
/-- `Min`'s post-phi block simulation — the `hres` input `genBlockSimulation_join_self` takes. -/
theorem min_join_hres {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {asm : AsmState} (f : Nat) (ctx : VenomContext)
    (hrel : venomAsmRel lo Min.ps Min.vs asm) (hpc : asm.pc = 0) :
    BlockSim lo Min.ps offsetToPc (asmResolve (executePlan Min.ops)).1 asm
      (execBlock (f + 1) ctx Min.bJ
        { (updateVar "p" Min.av Min.vs) with instIdx := phiPrefixLength Min.bJ.instructions }) := by
  have hpost : venomAsmRel lo Min.ps (updateVar "p" Min.av Min.vs) asm :=
    venomAsmRel_phi_join' (outs := ["p"]) (phis := Min.bJ.instructions)
      hrel rfl rfl min_ev
      (fun w hw => lookupVar_updateVar_ne Min.vs "p" w Min.av (by simpa using hw))
      (fun op off hlk _ _ => absurd hlk (by simp [Min.ps, AssocList.lookup]))
      ⟨hrel.1.1, fun i hi => absurd hi (by simp [Min.ps])⟩
  rw [min_phiPrefixLength, min_self_run f ctx (updateVar "p" Min.av Min.vs)]
  show ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
    (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmHalt as' ∧
    venomAsmTerminalRel (haltState { (updateVar "p" Min.av Min.vs) with instIdx := 1 }) as'
  refine hasm_stop (l := "join") (ps := Min.ps)
    (venomAsmRel_congr (a := updateVar "p" Min.av Min.vs) (by unfold sameUpToIdx; rfl) hpost) ?_ ?_
  · rw [min_prog, hpc]
    refine ⟨by rfl, ?_⟩
    intro j hj
    simp only [Nat.zero_add, Min.ops]
  · rw [min_proglen]

/-- **`WalkStep_join_of_genBlockSim_terminal`, consumed.** The lemma composes
`genBlockSimulation_join_self` with the terminal transfer in one step; this feeds it `Min`'s `evalPhis`
and post-phi simulation and gets the walk's obligation for a phi-headed block. Nothing left assumed. -/
theorem min_walkstep_join_via_lemma (f : Nat) (ctx : VenomContext) (fn : IrFunction)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (offsetToPc : AssocList Nat Nat) :
    WalkStep fn pcOf psOf wOf [] offsetToPc (asmResolve (executePlan Min.ops)).1
      Min.bJ Min.asm ((asmResolve (executePlan Min.ops)).1.length)
      (runBlock (f + 1) ctx Min.bJ Min.vs) := by
  have hrb : runBlock (f + 1) ctx Min.bJ Min.vs
      = ExecResult.Halt (haltState { updateVar "p" Min.av Min.vs with instIdx := 1 }) := by
    rw [runBlock_eq_execBlock_of_phis min_ev, min_phiPrefixLength]
    exact min_self_run f ctx _
  exact WalkStep_join_of_genBlockSim_terminal (ops := Min.ops) pcOf psOf wOf rfl
    (fun w h => by rw [hrb] at h; exact absurd h (by simp))
    min_ev (min_join_hres f ctx min_rel_on_arrival rfl)

/-! ## What a universal recipe from `genBlockSimulation` still needs

`WalkStep_of_BlockSimAt` takes a block's simulation *against the whole program* and produces the walk's
obligation with no case analysis. That is the dispatcher. What it does not do — and what a genuinely
universal recipe would — is *produce* that simulation from `genBlockSimulation`.

The obstacle is concrete, and it is worth stating as a fact rather than as a difficulty.
`genBlockSimulation` runs the **block's own** resolved program, with pcs starting at zero. The walk runs
the **function's** program, with the block sitting at some base. The instructions agree —
`asmBlockAt_same_inst` proves the whole program presents exactly what the block's does at the
corresponding offset — so a replay is possible in principle.

But the pc shift is **not uniform**. A sequential instruction advances the pc by one, *relative* to where
it sits, so the two runs differ by `base`. A `JUMP` sets the pc from `offsetToPc`, which is the
whole-function map, so its target is *absolute* and the two runs coincide. The invariant relating the two
runs therefore changes shape at the terminator, which is why `runAsm` cannot simply be transported and why
the `hstep` family takes whole-program asm hypotheses directly instead of lifting them.

`dia_then_pc_shift_is_not_uniform` exhibits it on a real block: `then` sits at pc 13 in the whole program
and at pc 0 in its own, yet both land at `join`'s absolute index 11, because the `JUMP` reads the same
`offsetToPc`.

That lemma — a `runAsm` segment lift with a terminator-aware invariant — is the last thing between
`genBlockSimulation` and a per-block recipe for an arbitrary CFG. It is real work, not assembly, and this
section says so instead of implying otherwise. -/
/-- **The core of the segment lift.** At a pc inside a block's segment, the *whole* program presents the
same instruction the *block's* program does at the corresponding offset. This is what would let a block's
isolated asm run be replayed inside the function's program. -/
theorem asmBlockAt_same_inst {prog blk : List AsmInst} {base j : Nat}
    (hblk : asmBlockAt prog base blk) (hj : j < blk.length) :
    prog[base + j]? = blk[j]? :=
  hblk.2 j hj

/-- …and the instruction is really there, as a `get`. -/
theorem asmBlockAt_get_eq {prog blk : List AsmInst} {base j : Nat}
    (hblk : asmBlockAt prog base blk) (hj : j < blk.length)
    (hlt : base + j < prog.length) :
    prog.get ⟨base + j, hlt⟩ = blk.get ⟨j, hj⟩ := by
  have h := asmBlockAt_same_inst hblk hj
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hj] at h
  simpa using h

/-- **Why the lift is not mechanical, stated as a fact rather than a claim.**

A sequential instruction advances the pc by one — *relative* to where it sits. A `JUMP` sets the pc from
`offsetToPc`, which is the **whole-function** map, so its target is *absolute* and identical in both
programs.

So a block's isolated run and its run inside the function agree on every instruction (above) but their pcs
differ by `base` for the sequential part and coincide after a jump. The shift is therefore **not uniform**,
which is exactly why `runAsm` cannot simply be transported: the invariant relating the two runs changes
shape at the terminator.

`Dia.bThen` exhibits it. Inside the whole program the block starts at pc 13; its own asm, taken alone,
starts at pc 0. Both land at `join`'s absolute index 11, because the `JUMP` reads the same `offsetToPc`. -/
theorem dia_then_pc_shift_is_not_uniform :
    -- the block sits at 13 in the whole program
    Dia.pcOf Dia.bThen.label = 13 ∧
    -- and the jump lands at join's ABSOLUTE index, the same number either way
    AssocList.lookup Nat Nat Dia.o2pc 17 = some 11 ∧
    Dia.pcOf Dia.bJoin.label = 11 :=
  ⟨rfl, dia_o2pc_join, rfl⟩

/-! ## The asm-side pc-obliviousness the segment lift needs

The previous section said the segment lift is real work and named why: the pc shift is not uniform. This
section supplies the reusable half of it.

`asmStep` dispatches on the instruction and hands the state to one of 27 helpers. Most of them read the
state's non-pc fields and put `asmNext s` back — so moving the input pc to `p` moves the output pc to
`p + 1` and changes nothing else. That is `withPc (p + 1)`, and it is the asm-side counterpart of
`StepObliv`: the Venom side needed obliviousness because a join resumes at a nonzero `instIdx`; the asm
side needs it because a block sits at a nonzero base.

**I first wrote "every helper but the jumps" here, and that is FALSE** — see the exceptions below. The
uniform law is the weaker `sameUpToPc`; `withPc (p+1)` holds only for the helpers that actually call
`asmNext`, and I did not check all 27 before generalising from the ten I had read.

`asmJump_pc` is the contrast, and it is the one to read. `asmJump` does **not** build its result from
`asmNext`. It reads its target from `offsetToPc` — the whole-function map — and sets the pc absolutely, so
moving the input pc changes nothing about the output. That is why the invariant relating a block's isolated
run to its run inside the function changes shape at the terminator, and it is the whole content of what
remains. -/
/-- Overwrite the pc of whatever state an `AsmResult` carries. -/
def withPc (p : Nat) : AsmResult → AsmResult
  | AsmResult.AsmOK s     => AsmResult.AsmOK { s with pc := p }
  | AsmResult.AsmHalt s   => AsmResult.AsmHalt { s with pc := p }
  | AsmResult.AsmRevert s => AsmResult.AsmRevert { s with pc := p }
  | AsmResult.AsmFault s  => AsmResult.AsmFault { s with pc := p }
  | r => r

/-! ### The asm helpers are pc-oblivious except for the increment

Each helper reads the state's non-pc fields and puts `asmNext s` back — so moving the input pc to `p`
moves the output pc to `p + 1`, and changes nothing else. This is the asm-side counterpart of `StepObliv`,
and it is what a `runAsm` segment lift needs for every non-jump instruction. -/

theorem asmPushVal_pc (v : bytes32) (s : AsmState) (p : Nat) :
    asmPushVal v { s with pc := p } = withPc (p + 1) (asmPushVal v s) := rfl

theorem asmPop_pc (s : AsmState) (p : Nat) :
    asmPop { s with pc := p } = withPc (p + 1) (asmPop s) := by
  unfold asmPop withPc; cases s.stack <;> rfl

theorem asmBinop_pc (f : bytes32 → bytes32 → bytes32) (s : AsmState) (p : Nat) :
    asmBinop f { s with pc := p } = withPc (p + 1) (asmBinop f s) := by
  unfold asmBinop withPc
  match hs : s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem asmUnop_pc (f : bytes32 → bytes32) (s : AsmState) (p : Nat) :
    asmUnop f { s with pc := p } = withPc (p + 1) (asmUnop f s) := by
  unfold asmUnop withPc; cases s.stack <;> rfl

theorem asmTernop_pc (f : bytes32 → bytes32 → bytes32 → bytes32) (s : AsmState) (p : Nat) :
    asmTernop f { s with pc := p } = withPc (p + 1) (asmTernop f s) := by
  unfold asmTernop withPc
  match hs : s.stack with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem asmDup_pc (n : Nat) (s : AsmState) (p : Nat) :
    asmDup n { s with pc := p } = withPc (p + 1) (asmDup n s) := by
  unfold asmDup withPc
  split_ifs <;> rfl

theorem asmSwap_pc (n : Nat) (s : AsmState) (p : Nat) :
    asmSwap n { s with pc := p } = withPc (p + 1) (asmSwap n s) := by
  unfold asmSwap withPc
  split_ifs <;> rfl

theorem asmMload_pc (s : AsmState) (p : Nat) :
    asmMload { s with pc := p } = withPc (p + 1) (asmMload s) := by
  unfold asmMload withPc; cases s.stack <;> rfl

theorem asmMstore_pc (s : AsmState) (p : Nat) :
    asmMstore { s with pc := p } = withPc (p + 1) (asmMstore s) := by
  unfold asmMstore withPc
  match hs : s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem asmSload_pc (s : AsmState) (p : Nat) :
    asmSload { s with pc := p } = withPc (p + 1) (asmSload s) := by
  unfold asmSload withPc; cases s.stack <;> rfl

/-! ### …and the jump, which is exactly where the shift breaks

`asmJump` does not build its result from `asmNext`. It reads the target from `offsetToPc` — the
whole-function map — and sets the pc to it **absolutely**. So it is *not* `withPc (p + 1)` of anything:
moving the input pc changes nothing about the output pc at all.

That asymmetry is the whole content of the remaining segment-lift lemma. Every non-jump instruction shifts
with its block; the terminator does not, because it was already speaking in whole-function coordinates. -/
theorem asmJump_pc (o2pc : AssocList Nat Nat) (s : AsmState) (p : Nat) :
    asmJump o2pc { s with pc := p } = asmJump o2pc s := by
  unfold asmJump
  cases s.stack <;> rfl

/-! ### The rest of the helpers — and the three exceptions -/


theorem toVenomState_pc (s : AsmState) (p : Nat) :
    AsmState.toVenomState { s with pc := p } = s.toVenomState := rfl

theorem withPc_withPc (a b : Nat) (r : AsmResult) :
    withPc a (withPc b r) = withPc a r := by cases r <;> rfl

theorem asmMstore8_pc (s : AsmState) (p : Nat) :
    asmMstore8 { s with pc := p } = withPc (p + 1) (asmMstore8 s) := by
  unfold asmMstore8 withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem asmSstore_pc (s : AsmState) (p : Nat) :
    asmSstore { s with pc := p } = withPc (p + 1) (asmSstore s) := by
  unfold asmSstore withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem asmSha3_pc (s : AsmState) (p : Nat) :
    asmSha3 { s with pc := p } = withPc (p + 1) (asmSha3 s) := by
  unfold asmSha3 withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem asmMcopy_pc (s : AsmState) (p : Nat) :
    asmMcopy { s with pc := p } = withPc (p + 1) (asmMcopy s) := by
  unfold asmMcopy withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem asmCopyToMem_pc (src : List byte) (s : AsmState) (p : Nat) :
    asmCopyToMem src { s with pc := p } = withPc (p + 1) (asmCopyToMem src s) := by
  unfold asmCopyToMem withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- RETURN **does not** call `asmNext`: a halt keeps the pc it halted at. So the shift is
`withPc p`, not `withPc (p+1)`. -/
theorem asmReturnOp_pc (s : AsmState) (p : Nat) :
    asmReturnOp { s with pc := p } = withPc p (asmReturnOp s) := by
  unfold asmReturnOp withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- Same for REVERT. -/
theorem asmRevertOp_pc (s : AsmState) (p : Nat) :
    asmRevertOp { s with pc := p } = withPc p (asmRevertOp s) := by
  unfold asmRevertOp withPc
  match s.stack with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- RETURNDATACOPY is the mixed case: its OK branch goes through `asmNext` (pc+1) but its
    **fault** branch does not (pc preserved). So NO single `withPc k` describes it. -/
theorem asmReturndatacopy_pc_ok (s : AsmState) (p : Nat) (s' : AsmState)
    (h : asmReturndatacopy { s with pc := p } = AsmResult.AsmOK s') : s'.pc = p + 1 := by
  revert h; unfold asmReturndatacopy
  match s.stack with
  | [] => intro h; cases h
  | [_] => intro h; cases h
  | [_, _] => intro h; cases h
  | a :: b :: c :: _ =>
    simp only []
    split
    · intro h; cases h
    · intro h; cases h; rfl

theorem asmSelfdestruct_pc (s : AsmState) (p : Nat) :
    asmSelfdestruct { s with pc := p } = withPc (p + 1) (asmSelfdestruct s) := by
  unfold asmSelfdestruct withPc
  match s.stack with
  | [] => rfl
  | _ :: _ => rfl

theorem asmExtcodecopy_pc (s : AsmState) (p : Nat) :
    asmExtcodecopy { s with pc := p } = withPc (p + 1) (asmExtcodecopy s) := by
  unfold asmExtcodecopy
  match s.stack with
  | [] => rfl
  | a :: r =>
    show asmCopyToMem _ { { s with stack := r } with pc := p } = _
    rw [asmCopyToMem_pc]

/-! ### The invariant that IS uniform -/

/-- Two results agree up to the pc. -/
def sameUpToPc (r₁ r₂ : AsmResult) : Prop := withPc 0 r₁ = withPc 0 r₂


theorem asmReturndatacopy_same (s : AsmState) (p : Nat) :
    sameUpToPc (asmReturndatacopy { s with pc := p }) (asmReturndatacopy s) := by
  unfold sameUpToPc
  match hs : s.stack with
  | [] => simp [asmReturndatacopy, hs]
  | [_] => simp [asmReturndatacopy, hs]
  | [_, _] => simp [asmReturndatacopy, hs]
  | a :: b :: c :: r =>
    by_cases h : UInt256.toNat b + UInt256.toNat c > s.returndata.size
    · simp [asmReturndatacopy, hs, h, withPc]
    · simp [asmReturndatacopy, hs, h, withPc, asmNext]

/-! ### JUMPI is both

A JUMPI's **taken** branch reads its target from `offsetToPc` and sets the pc absolutely, exactly like
JUMP — so moving the input pc changes nothing. Its **fall-through** branch goes through `asmNext` and is
an ordinary increment. So JUMPI is not classifiable as "jump" or "non-jump": which of the two shift laws
applies depends on the *value on the stack*, not on the opcode. -/
theorem asmJumpi_pc_notTaken (o2pc : AssocList Nat Nat) (s : AsmState) (p : Nat)
    (dest cond : bytes32) (stk : List bytes32)
    (hs : s.stack = dest :: cond :: stk) (hc : cond = EvmYul.UInt256.ofNat 0) :
    asmJumpi o2pc { s with pc := p } = withPc (p + 1) (asmJumpi o2pc s) := by
  simp [asmJumpi, hs, hc, withPc, asmNext]

theorem asmJumpi_pc_taken (o2pc : AssocList Nat Nat) (s : AsmState) (p : Nat)
    (dest cond : bytes32) (stk : List bytes32)
    (hs : s.stack = dest :: cond :: stk) (hc : cond ≠ EvmYul.UInt256.ofNat 0) :
    asmJumpi o2pc { s with pc := p } = asmJumpi o2pc s := by
  simp only [asmJumpi, hs, if_neg hc]

/-! ### The call/create family, and the universal congruence

With every helper covered, the statement that is actually uniform can be proved: `asmStep` reads the pc
**only** to fetch the instruction. Two programs carrying the same instruction at different positions step
to the same result, up to the pc — over all 81 arms, jumps included. -/


theorem asmCall_pc (s : AsmState) (p : Nat) :
    asmCall { s with pc := p } = withPc (p + 1) (asmCall s) := by
  unfold asmCall withPc
  match s.stack with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] => rfl
  | _::_::_::_::_::_::_::_ => rfl

theorem asmStaticCall_pc (s : AsmState) (p : Nat) :
    asmStaticCall { s with pc := p } = withPc (p + 1) (asmStaticCall s) := by
  unfold asmStaticCall withPc
  match s.stack with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] => rfl
  | _::_::_::_::_::_::_ => rfl

theorem asmDelegateCall_pc (s : AsmState) (p : Nat) :
    asmDelegateCall { s with pc := p } = withPc (p + 1) (asmDelegateCall s) := by
  unfold asmDelegateCall withPc
  match s.stack with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] => rfl
  | _::_::_::_::_::_::_ => rfl

theorem asmCreate_pc (s : AsmState) (p : Nat) :
    asmCreate { s with pc := p } = withPc (p + 1) (asmCreate s) := by
  unfold asmCreate withPc
  match s.stack with
  | [] | [_] | [_,_] => rfl
  | _::_::_::_ => rfl

theorem asmCreate2_pc (s : AsmState) (p : Nat) :
    asmCreate2 { s with pc := p } = withPc (p + 1) (asmCreate2 s) := by
  unfold asmCreate2 withPc
  match s.stack with
  | [] | [_] | [_,_] | [_,_,_] => rfl
  | _::_::_::_::_ => rfl

theorem asmLog_pc (n : Nat) (s : AsmState) (p : Nat) :
    asmLog n { s with pc := p } = withPc (p + 1) (asmLog n s) := by
  unfold asmLog withPc
  split_ifs <;> rfl

theorem sameUpToPc_symm (r₁ r₂ : AsmResult) (h : sameUpToPc r₁ r₂) : sameUpToPc r₂ r₁ := h.symm

theorem sameUpToPc_trans (r₁ r₂ r₃ : AsmResult)
    (h₁ : sameUpToPc r₁ r₂) (h₂ : sameUpToPc r₂ r₃) : sameUpToPc r₁ r₃ := h₁.trans h₂

theorem asmReturndatacopy_same_pq (s : AsmState) (p q : Nat) :
    sameUpToPc (asmReturndatacopy { s with pc := p }) (asmReturndatacopy { s with pc := q }) :=
  sameUpToPc_trans _ _ _ (asmReturndatacopy_same s p)
    (sameUpToPc_symm _ _ (asmReturndatacopy_same s q))

/-- JUMPI's two laws collapse into one `sameUpToPc`: taken, both sides ignore the incoming pc;
    not-taken, both increment their own. Either way they agree up to the pc. -/
theorem asmJumpi_same_pq (o2pc : AssocList Nat Nat) (s : AsmState) (p q : Nat) :
    sameUpToPc (asmJumpi o2pc { s with pc := p }) (asmJumpi o2pc { s with pc := q }) := by
  unfold sameUpToPc
  match hs : s.stack with
  | [] => simp [asmJumpi, hs]
  | [_] => simp [asmJumpi, hs]
  | dest :: cond :: stk =>
    by_cases hc : cond = EvmYul.UInt256.ofNat 0
    · simp [asmJumpi, hs, hc, withPc, asmNext]
    · simp only [asmJumpi, hs, if_neg hc]


/-- **`asmStep` does not read the pc, except to fetch the instruction.**

If two programs carry the *same instruction* at positions `p` and `q`, then stepping either one from a
state sitting at its own position gives the same result up to the pc. This is uniform over all 81 arms —
jumps included, because a jump's result does not depend on the incoming pc at all.

This is the whole asm-side content of the segment lift: a block's asm behaves the same wherever it is
placed in the program. What the pc is *set to* differs, and that difference is exactly what the separate
pc-tracking lemmas describe. -/
theorem asmStep_sameUpToPc (o2pc : AssocList Nat Nat) (prog₁ prog₂ : List AsmInst)
    (s : AsmState) (p q : Nat) (hp : p < prog₁.length) (hq : q < prog₂.length)
    (heq : prog₁.get ⟨p, hp⟩ = prog₂.get ⟨q, hq⟩) :
    sameUpToPc (asmStep o2pc prog₁ { s with pc := p }) (asmStep o2pc prog₂ { s with pc := q }) := by
  unfold asmStep
  rw [dif_pos (show ({ s with pc := p } : AsmState).pc < prog₁.length from hp),
      dif_pos (show ({ s with pc := q } : AsmState).pc < prog₂.length from hq)]
  simp only [show (⟨({ s with pc := p } : AsmState).pc, hp⟩ : Fin prog₁.length) = ⟨p, hp⟩ from rfl,
             show (⟨({ s with pc := q } : AsmState).pc, hq⟩ : Fin prog₂.length) = ⟨q, hq⟩ from rfl, heq]
  split <;>
    first
      | (simp only [sameUpToPc, asmPushVal_pc, asmPop_pc, asmBinop_pc, asmUnop_pc, asmTernop_pc,
            asmDup_pc, asmSwap_pc, asmMload_pc, asmMstore_pc, asmMstore8_pc, asmSload_pc,
            asmSstore_pc, asmSha3_pc, asmMcopy_pc, asmCopyToMem_pc, asmExtcodecopy_pc,
            asmReturnOp_pc, asmRevertOp_pc, asmSelfdestruct_pc, asmJump_pc, asmCall_pc,
            asmStaticCall_pc, asmDelegateCall_pc, asmCreate_pc, asmCreate2_pc, withPc_withPc]
         done)
      | exact asmReturndatacopy_same_pq s p q
      | exact asmJumpi_same_pq o2pc s p q
      | (simp [sameUpToPc, withPc, asmNext]; done)
      | (repeat' split
         all_goals
           first
             | (simp only [sameUpToPc, asmDup_pc, asmSwap_pc, asmLog_pc, withPc_withPc]; done)
             | (simp [sameUpToPc, withPc]; done))
      | (rcases hst : s.stack with _ | ⟨a, _ | ⟨b, t⟩⟩ <;>
           simp [sameUpToPc, withPc, asmNext, asmStateUnop, AsmState.toVenomState,
                 toVenomState_pc, hst])


/-- **A block steps the same in the program as it does in isolation.**

If `blk` is placed at `base` in `prog`, then stepping the whole program from `base + j` and stepping the
block alone from `j` agree up to the pc — for every offset `j` inside the block, and for every opcode,
terminator included. This is `asmStep_sameUpToPc` fed by `asmBlockAt`: the placement hypothesis is exactly
the instruction-equality the congruence asks for. -/
theorem asmStep_of_blockAt (o2pc : AssocList Nat Nat) (prog blk : List AsmInst)
    (base j : Nat) (s : AsmState)
    (hblk : asmBlockAt prog base blk) (hj : j < blk.length) :
    sameUpToPc (asmStep o2pc prog { s with pc := base + j })
               (asmStep o2pc blk { s with pc := j }) := by
  have hlt : base + j < prog.length := by
    have := hblk.1
    omega
  exact asmStep_sameUpToPc o2pc prog blk s (base + j) j hlt hj
    (asmBlockAt_get_eq hblk hj hlt)

/-! ## The pc actually tracks

`sameUpToPc` says the two runs agree on everything *but* the pc — which is precisely the field the next
step reads. To iterate, I need the pc too: a non-jump instruction that yields `AsmOK` advances the pc by
exactly one, wherever it sits. -/

/-- The two opcodes whose OK result does not advance the pc by one. -/
def IsAsmJump : AsmInst → Bool
  | AsmInst.AsmOp "JUMP"  => true
  | AsmInst.AsmOp "JUMPI" => true
  | _ => false

theorem pc_of_withPc_ok (k : Nat) (r : AsmResult) (s' : AsmState)
    (h : withPc k r = AsmResult.AsmOK s') : s'.pc = k := by
  cases r <;> simp [withPc] at h <;> (subst h; rfl)

theorem asmReturnOp_not_ok (s s' : AsmState) : asmReturnOp s ≠ AsmResult.AsmOK s' := by
  unfold asmReturnOp
  match s.stack with
  | [] => simp
  | [_] => simp
  | _ :: _ :: _ => simp

theorem asmRevertOp_not_ok (s s' : AsmState) : asmRevertOp s ≠ AsmResult.AsmOK s' := by
  unfold asmRevertOp
  match s.stack with
  | [] => simp
  | [_] => simp
  | _ :: _ :: _ => simp

theorem asmSelfdestruct_not_ok (s s' : AsmState) : asmSelfdestruct s ≠ AsmResult.AsmOK s' := by
  unfold asmSelfdestruct
  match s.stack with
  | [] => simp
  | _ :: _ => simp

/-- **A non-jump instruction that succeeds advances the pc by exactly one, wherever it sits.**
Uniform over the other 79 arms. -/
theorem asmStateUnop_ok_pc (f : bytes32 → AsmState → bytes32) (s s' : AsmState) (p : Nat)
    (h : asmStateUnop f { s with pc := p } = AsmResult.AsmOK s') : s'.pc = p + 1 := by
  revert h; unfold asmStateUnop
  match s.stack with
  | [] => intro h; cases h
  | a :: tl => intro h; cases h; rfl

theorem asmStep_ok_pc (o2pc : AssocList Nat Nat) (prog : List AsmInst) (s s' : AsmState) (p : Nat)
    (hp : p < prog.length) (hnj : IsAsmJump (prog.get ⟨p, hp⟩) = false)
    (h : asmStep o2pc prog { s with pc := p } = AsmResult.AsmOK s') : s'.pc = p + 1 := by
  revert h hnj
  unfold asmStep
  rw [dif_pos (show ({ s with pc := p } : AsmState).pc < prog.length from hp)]
  simp only [show (⟨({ s with pc := p } : AsmState).pc, hp⟩ : Fin prog.length) = ⟨p, hp⟩ from rfl]
  split <;> intro hnj h
  all_goals
    first
      | (simp_all [IsAsmJump]; done)
      | exact absurd h (asmReturnOp_not_ok _ _)
      | exact absurd h (asmRevertOp_not_ok _ _)
      | exact absurd h (asmSelfdestruct_not_ok _ _)
      | (simp only [asmPushVal_pc, asmPop_pc, asmBinop_pc, asmUnop_pc, asmTernop_pc, asmDup_pc,
            asmSwap_pc, asmMload_pc, asmMstore_pc, asmMstore8_pc, asmSload_pc, asmSstore_pc,
            asmSha3_pc, asmMcopy_pc, asmCopyToMem_pc, asmExtcodecopy_pc, asmCall_pc,
            asmStaticCall_pc, asmDelegateCall_pc, asmCreate_pc, asmCreate2_pc, asmLog_pc] at h
         exact pc_of_withPc_ok _ _ _ h)
      | exact asmReturndatacopy_pc_ok s p s' h
      | exact asmStateUnop_ok_pc _ s s' p h
      | (cases h; rfl)
      | (repeat' (split at h)
         all_goals
           first
             | (simp only [asmDup_pc, asmSwap_pc, asmLog_pc] at h
                exact pc_of_withPc_ok _ _ _ h)
             | (simp at h)
         done)
      | (rcases hst : s.stack with _ | ⟨a, _ | ⟨b, t⟩⟩ <;>
           simp_all [asmNext]
         done)
      | (rcases hst : s.stack with _ | ⟨a, _ | ⟨b, t⟩⟩ <;>
           simp_all [asmNext] <;> subst h <;> rfl
         done)

/-! ## Putting the two halves together

`asmStep_sameUpToPc` gives everything but the pc; `asmStep_ok_pc` gives the pc. Together they say a
non-jump instruction of a placed block steps the program exactly as it steps the block, with the pc
displaced by `base`. -/

theorem asmState_of_setPc_eq (a b : AsmState) (k : Nat)
    (h : ({ a with pc := k } : AsmState) = { b with pc := k }) : a = { b with pc := a.pc } := by
  cases a; cases b; simp_all [AsmState.mk.injEq]


/-- **The segment step lemma.** A block placed at `base` steps the whole program exactly as it steps in
isolation — same state, pc displaced by `base` — for every non-jump instruction in it. -/
theorem asmStep_shift (o2pc : AssocList Nat Nat) (prog blk : List AsmInst)
    (base j : Nat) (s s' : AsmState)
    (hblk : asmBlockAt prog base blk) (hj : j < blk.length)
    (hnj : IsAsmJump (blk.get ⟨j, hj⟩) = false)
    (hstep : asmStep o2pc blk { s with pc := j } = AsmResult.AsmOK s') :
    asmStep o2pc prog { s with pc := base + j }
      = AsmResult.AsmOK { s' with pc := base + j + 1 } := by
  have hlt : base + j < prog.length := by have := hblk.1; omega
  have hgeti : prog.get ⟨base + j, hlt⟩ = blk.get ⟨j, hj⟩ := asmBlockAt_get_eq hblk hj hlt
  have hsame := asmStep_of_blockAt o2pc prog blk base j s hblk hj
  unfold sameUpToPc at hsame
  rw [hstep] at hsame
  -- the program-side step is an OK too …
  obtain ⟨u, hu⟩ : ∃ u, asmStep o2pc prog { s with pc := base + j } = AsmResult.AsmOK u := by
    cases hp : asmStep o2pc prog { s with pc := base + j } with
    | AsmOK u => exact ⟨u, rfl⟩
    | AsmHalt u   => rw [hp] at hsame; simp [withPc] at hsame
    | AsmRevert u => rw [hp] at hsame; simp [withPc] at hsame
    | AsmFault u  => rw [hp] at hsame; simp [withPc] at hsame
    | AsmError m  => rw [hp] at hsame; simp [withPc] at hsame
  rw [hu] at hsame ⊢
  -- … its pc is base + j + 1 …
  have hpc : u.pc = base + j + 1 := by
    refine asmStep_ok_pc o2pc prog s u (base + j) hlt ?_ hu
    rw [hgeti]; exact hnj
  -- … and every other field agrees with the block-side result.
  simp only [withPc] at hsame
  have := asmState_of_setPc_eq u s' 0 (by injection hsame)
  rw [this, hpc]

/-! ## The segment lift

The induction that the per-block recipe needs. -/


/-- An `AsmOK` step is evidence that the pc was in range: out of bounds, `asmStep` errors. -/
theorem asmStep_ok_inbounds (o2pc : AssocList Nat Nat) (prog : List AsmInst) (s s' : AsmState)
    (h : asmStep o2pc prog s = AsmResult.AsmOK s') : s.pc < prog.length := by
  by_contra hc
  rw [asmStep, dif_neg hc] at h
  cases h

/-- **The segment lift.** A jump-free block placed at `base` runs the whole program exactly as it
runs in isolation: same state throughout, pc displaced by `base`.

This is the induction the per-block recipe needs. The `IsAsmJump`-free hypothesis is what confines
it to a block's *body*; the terminator is where the displacement stops being uniform, which is
exactly what `asmJump_pc` says. -/
theorem runAsm_shift (n : Nat) (o2pc : AssocList Nat Nat) (prog blk : List AsmInst) (base : Nat)
    (hblk : asmBlockAt prog base blk)
    (hnj : ∀ j, (hj : j < blk.length) → IsAsmJump (blk.get ⟨j, hj⟩) = false) :
    ∀ (x s' : AsmState), runAsm n o2pc blk x = AsmResult.AsmOK s' →
      runAsm n o2pc prog { x with pc := base + x.pc }
        = AsmResult.AsmOK { s' with pc := base + s'.pc } := by
  induction n with
  | zero =>
    intro x s' h
    rw [runAsm] at h ⊢
    cases h
    rfl
  | succ n ih =>
    intro x s' h
    rw [runAsm] at h
    cases hstep : asmStep o2pc blk x with
    | AsmOK t =>
      rw [hstep] at h
      have hj : x.pc < blk.length := asmStep_ok_inbounds o2pc blk x t hstep
      have hx : ({ x with pc := x.pc } : AsmState) = x := rfl
      have hshift : asmStep o2pc prog { x with pc := base + x.pc }
          = AsmResult.AsmOK { t with pc := base + x.pc + 1 } := by
        have := asmStep_shift o2pc prog blk base x.pc x t hblk hj (hnj x.pc hj) (by rw [hx]; exact hstep)
        exact this
      have htpc : t.pc = x.pc + 1 :=
        asmStep_ok_pc o2pc blk x t x.pc hj (hnj x.pc hj) (by rw [hx]; exact hstep)
      rw [runAsm, hshift]
      have : ({ t with pc := base + x.pc + 1 } : AsmState) = { t with pc := base + t.pc } := by
        rw [htpc, Nat.add_assoc]
      rw [this]
      exact ih t s' h
    | AsmHalt t   => rw [hstep] at h; cases h
    | AsmRevert t => rw [hstep] at h; cases h
    | AsmFault t  => rw [hstep] at h; cases h
    | AsmError m  => rw [hstep] at h; cases h

/-! ## Firing the lift on the compiler's own output

At a **nonzero** base — 13, not 0. A base of 0 would make the displacement law degenerate and prove
nothing. -/


/-- The `then` block's jump-free body, as the compiler laid it out: `Dia.prog[13..17)`.
    `Dia.prog[17]` is the `JUMP` — the body runs right up to the terminator and stops. -/
def Dia.thenBody : List AsmInst := (Dia.prog.drop 13).take 4

theorem dia_thenBody_shape :
    Dia.thenBody = [AsmInst.AsmLabel "then", AsmInst.AsmOp "CALLVALUE",
                    AsmInst.AsmOp "POP", Dia.prog[16]!] := by rfl

theorem dia_thenBody_at : asmBlockAt Dia.prog 13 Dia.thenBody := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have : j < 4 := hj
  interval_cases j <;> rfl

theorem dia_thenBody_nojump :
    ∀ j, (hj : j < Dia.thenBody.length) → IsAsmJump (Dia.thenBody.get ⟨j, hj⟩) = false := by
  decide

/-- **The lift, fired on the compiler's own output, at a nonzero base.** -/
theorem dia_then_lift (x s' : AsmState)
    (h : runAsm 4 Dia.o2pc Dia.thenBody x = AsmResult.AsmOK s') :
    runAsm 4 Dia.o2pc Dia.prog { x with pc := 13 + x.pc }
      = AsmResult.AsmOK { s' with pc := 13 + s'.pc } :=
  runAsm_shift 4 Dia.o2pc Dia.prog Dia.thenBody 13 dia_thenBody_at dia_thenBody_nojump x s' h

/-- **Non-vacuous, and it lands where it should.** Running the `then` block's body in isolation for
four steps and running `Dia.prog` from pc 13 for four steps give the same state — and the program-side
pc ends at **17**, which is exactly the index of that block's `JUMP`.

So the lift carries a real compiled block, at a base of 13, right up to its terminator and stops there.
The terminator is where it stops because the terminator is where it *must* stop: `asmJump_pc` says a
JUMP's target is absolute, so no displacement law can cross it. -/
theorem dia_then_lift_fires (x : AsmState) :
    ∃ s', runAsm 4 Dia.o2pc Dia.thenBody { x with pc := 0 } = AsmResult.AsmOK s' ∧
          runAsm 4 Dia.o2pc Dia.prog { x with pc := 13 }
            = AsmResult.AsmOK { s' with pc := 13 + s'.pc } :=
  ⟨_, rfl, dia_then_lift { x with pc := 0 } _ rfl⟩

theorem dia_then_lift_lands_on_the_jump (x : AsmState) :
    ∃ s', runAsm 4 Dia.o2pc Dia.prog { x with pc := 13 } = AsmResult.AsmOK s'
        ∧ s'.pc = 17 ∧ Dia.prog[17]! = AsmInst.AsmOp "JUMP" := by
  exact ⟨_, dia_then_lift { x with pc := 0 } _ rfl, rfl, rfl⟩

/-! ## What the lift buys: the per-block asm hypothesis, without an absolute-pc trace -/


/-- The state the `then` block's body reaches when run **in isolation**. Left as the result of the run
    rather than spelled out: the word it pushes (`Dia.prog[16] = AsmPush [0,17]`) is a `wordOfBytes` over
    a 32-byte pad that does not kernel-reduce, and it does not need to — nothing below normalises it. -/
def Dia.thenS (asm : AsmState) : AsmState :=
  match runAsm 4 Dia.o2pc Dia.thenBody { asm with pc := 0 } with
  | AsmResult.AsmOK s => s
  | _ => asm

/-- The body's isolated run is a `rfl`: a block is a short literal list. -/
theorem dia_thenBody_run (asm : AsmState) :
    runAsm 4 Dia.o2pc Dia.thenBody { asm with pc := 0 } = AsmResult.AsmOK (Dia.thenS asm) := rfl

/-- Its pc lands at 4 — the block's length. This is a *projection*, so it reduces even though the pushed
    word above does not. -/
theorem dia_thenS_pc (asm : AsmState) : (Dia.thenS asm).pc = 4 := rfl

/-- **The recipe, on a real block.**

The per-block asm hypotheses the `hstep` family consumes (`dia_hasm_then` and friends) were proved by a
hand-rolled instruction-by-instruction trace through the *whole program* at absolute pcs, juggling
`Fin.ext` at every step — about thirty lines a block, and nothing about it generalises.

Here is the body of that same block through the lift instead: run it **in isolation**, where it is a
`rfl`, then displace it to base 13. No absolute pc appears in the proof. The only thing specific to this
block is which four instructions it has — everything else is `runAsm_shift`.

It stops at 17 because 17 is the block's `JUMP`, and the terminator is not the lift's business: that is
what the seven canonical `hstep`s are for. -/
theorem dia_then_body_in_prog (asm : AsmState) (hpc : asm.pc = 13) :
    runAsm 4 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { Dia.thenS asm with pc := 17 } := by
  have hlift := dia_then_lift { asm with pc := 0 } (Dia.thenS asm) (dia_thenBody_run asm)
  have hid : ({ asm with pc := 13 + ({ asm with pc := 0 } : AsmState).pc } : AsmState) = asm := by
    show ({ asm with pc := 13 } : AsmState) = asm
    rw [← hpc]
  rw [hid, dia_thenS_pc] at hlift
  exact hlift


/-! ## Which generated instructions can be a jump?

`runAsm_shift` takes jump-freeness of the block's body as a HYPOTHESIS. For a per-block recipe it has to
be a THEOREM. Working out which opcodes can emit a `JUMP`/`JUMPI` is the content — and the answer is not
the one I assumed. -/

theorem log_name_ne_jump (k : Nat) : ("LOG" ++ toString k) ≠ "JUMP" := by
  intro h
  have hd : ("LOG" ++ toString k).toList = "JUMP".toList := by rw [h]
  rw [String.toList_append] at hd
  simp [show "LOG".toList = ['L','O','G'] from rfl,
        show "JUMP".toList = ['J','U','M','P'] from rfl] at hd

theorem log_name_ne_jumpi (k : Nat) : ("LOG" ++ toString k) ≠ "JUMPI" := by
  intro h
  have hd : ("LOG" ++ toString k).toList = "JUMPI".toList := by rw [h]
  rw [String.toList_append] at hd
  simp [show "LOG".toList = ['L','O','G'] from rfl,
        show "JUMPI".toList = ['J','U','M','P','I'] from rfl] at hd

theorem swapName_not_jump (n : Nat) : IsAsmJump (AsmInst.AsmOp (swapName n)) = false := by
  unfold swapName
  simp only [apply_ite (f := fun s => IsAsmJump (AsmInst.AsmOp s))]
  simp only [show IsAsmJump (AsmInst.AsmOp "SWAP1") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP2") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP3") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP4") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP5") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP6") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP7") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP8") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP9") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP10") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP11") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP12") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP13") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP14") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP15") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP16") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "SWAP?") = false from rfl,
             ite_self]

theorem dupName_not_jump (n : Nat) : IsAsmJump (AsmInst.AsmOp (dupName n)) = false := by
  unfold dupName
  simp only [apply_ite (f := fun s => IsAsmJump (AsmInst.AsmOp s))]
  simp only [show IsAsmJump (AsmInst.AsmOp "DUP1") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP2") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP3") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP4") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP5") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP6") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP7") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP8") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP9") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP10") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP11") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP12") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP13") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP14") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP15") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP16") = false from rfl,
             show IsAsmJump (AsmInst.AsmOp "DUP?") = false from rfl,
             ite_self]

theorem IsAsmJump_op_false (s : String) (h1 : s ≠ "JUMP") (h2 : s ≠ "JUMPI") :
    IsAsmJump (AsmInst.AsmOp s) = false := by
  unfold IsAsmJump
  split <;> simp_all

/-- **The direct-emit table never names a jump.** `opcodeToEvmName` maps Venom opcodes to EVM mnemonics;
    no arm produces `JUMP` or `JUMPI`. Those are minted only by the control-flow branches below. -/
theorem opcodeToEvmName_not_jump (opc : Opcode) (name : String)
    (h : opcodeToEvmName opc = some name) : IsAsmJump (AsmInst.AsmOp name) = false := by
  refine IsAsmJump_op_false name ?_ ?_ <;>
    (cases opc <;> simp_all [opcodeToEvmName] <;> (subst h; decide))

/-- A `StackOp` that is not an explicit `SOEmit "JUMP"`/`SOEmit "JUMPI"`. -/
def SOJumpFree (op : StackOp) : Prop :=
  op ≠ StackOp.SOEmit "JUMP" ∧ op ≠ StackOp.SOEmit "JUMPI"

/-- **A jump-free `StackOp` executes to jump-free asm.** Every other constructor emits either a fixed
    mnemonic (POP/MSTORE/MLOAD), a `swapName`/`dupName`, a push, or a label — never a jump. -/
theorem execStackOp_not_jump (op : StackOp) (h : SOJumpFree op) :
    ∀ a ∈ execStackOp op, IsAsmJump a = false := by
  cases op with
  | SOPush o =>
    intro a ha
    cases o <;> simp [execStackOp] at ha <;> subst ha <;> rfl
  | SOPop n =>
    intro a ha
    rw [show execStackOp (StackOp.SOPop n) = List.replicate n (AsmInst.AsmOp "POP") from rfl] at ha
    rw [List.eq_of_mem_replicate ha]; rfl
  | SOSwap n => intro a ha; simp [execStackOp] at ha; subst ha; exact swapName_not_jump n
  | SODup n  => intro a ha; simp [execStackOp] at ha; subst ha; exact dupName_not_jump n
  | SOPoke _ _ => intro a ha; simp [execStackOp] at ha
  | SOSpill off => intro a ha; simp [execStackOp] at ha; rcases ha with h | h <;> subst h <;> rfl
  | SORestore off => intro a ha; simp [execStackOp] at ha; rcases ha with h | h <;> subst h <;> rfl
  | SOEmit opc =>
    intro a ha
    simp [execStackOp] at ha
    subst ha
    exact IsAsmJump_op_false opc
      (fun hc => h.1 (by rw [hc])) (fun hc => h.2 (by rw [hc]))
  | SOLabel l => intro a ha; simp [execStackOp] at ha; subst ha; rfl
  | SOPushLabel l => intro a ha; simp [execStackOp] at ha; subst ha; rfl
  | SOPushOfst l o => intro a ha; simp [execStackOp] at ha; subst ha; rfl

/-- …and so does a jump-free plan. -/
theorem executePlan_not_jump (ops : List StackOp) (h : ∀ op ∈ ops, SOJumpFree op) :
    ∀ a ∈ executePlan ops, IsAsmJump a = false := by
  intro a ha
  simp only [executePlan, List.bind_eq_flatMap, List.mem_flatMap] at ha
  obtain ⟨op, hop, ha⟩ := ha
  exact execStackOp_not_jump op (h op hop) a ha

/-- **The three body opcodes that emit a jump.**

This is the part I would have got wrong by assuming. A block's *body* is not automatically jump-free:

* `ASSERT` emits `ISZERO; PUSH revert; JUMPI` — a conditional abort, and it is **not** a terminator.
* `ASSERT_UNREACHABLE` emits `PUSH end; JUMPI; INVALID; end:` — also not a terminator.
* `INVOKE` emits `PUSH ret; PUSH f; JUMP; ret:` — a call, also not a terminator.

`isTerminator` is exactly `JMP JNZ DJMP RET RETURN REVERT STOP SINK SELFDESTRUCT INVALID`, so all three
sit in the middle of a block and jump from there. Everything *else* a body can contain routes through
`opcodeToEvmName`, `LOG`, or `ISTORE`, none of which names a jump. -/
def BodyJumpFree (opc : Opcode) : Prop :=
  isTerminator opc = false ∧ opc ≠ Opcode.ASSERT ∧ opc ≠ Opcode.ASSERT_UNREACHABLE
    ∧ opc ≠ Opcode.INVOKE

theorem generateEmitOps_not_jump (inst : Instruction) (k : Nat) (ps : PlanState)
    (h : BodyJumpFree inst.opcode) :
    ∀ op ∈ (generateEmitOps inst k ps).1, SOJumpFree op := by
  obtain ⟨hterm, hassert, hunreach, hinvoke⟩ := h
  have hjmp : inst.opcode ≠ Opcode.JMP := by
    intro hc; rw [hc] at hterm; exact absurd hterm (by decide)
  have hjnz : inst.opcode ≠ Opcode.JNZ := by
    intro hc; rw [hc] at hterm; exact absurd hterm (by decide)
  have hdjmp : inst.opcode ≠ Opcode.DJMP := by
    intro hc; rw [hc] at hterm; exact absurd hterm (by decide)
  have hret : inst.opcode ≠ Opcode.RET := by
    intro hc; rw [hc] at hterm; exact absurd hterm (by decide)
  intro op hop
  simp only [generateEmitOps] at hop
  cases hname : opcodeToEvmName inst.opcode with
  | some name =>
    rw [hname] at hop
    simp only [List.mem_singleton] at hop
    subst hop
    have hnj := opcodeToEvmName_not_jump _ name hname
    refine ⟨?_, ?_⟩ <;> intro hc <;>
      (rw [StackOp.SOEmit.inj hc] at hnj; simp [IsAsmJump] at hnj)
  | none =>
    rw [hname] at hop
    simp only [if_neg hjnz, if_neg hjmp, if_neg hdjmp, if_neg hinvoke, if_neg hret,
               if_neg hassert, if_neg hunreach] at hop
    split_ifs at hop
    · -- LOG: the only body opcode whose mnemonic is computed rather than a literal
      simp only [List.mem_singleton] at hop
      subst hop
      exact ⟨fun hc => log_name_ne_jump k (StackOp.SOEmit.inj hc),
             fun hc => log_name_ne_jumpi k (StackOp.SOEmit.inj hc)⟩
    · -- ISTORE: SWAP1; MSTORE
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with hc | hc <;> subst hc <;> exact ⟨by decide, by decide⟩
    · -- OFFSET (non-data-section form): a plain ADD
      simp only [List.mem_singleton] at hop
      subst hop
      exact ⟨by decide, by decide⟩
    · simp at hop

/-! ### …and the exclusions are NECESSARY, not merely cautious

If ASSERT/ASSERT_UNREACHABLE/INVOKE were terminators, or if they did not really jump, `BodyJumpFree`
would be excluding them for nothing. They are not, and they do. -/

theorem assert_not_terminator : isTerminator Opcode.ASSERT = false := by decide
theorem assert_unreachable_not_terminator : isTerminator Opcode.ASSERT_UNREACHABLE = false := by decide
theorem invoke_not_terminator : isTerminator Opcode.INVOKE = false := by decide

/-- `ASSERT` is a **body** opcode and it emits a `JUMPI`. -/
theorem assert_emits_jumpi (inst : Instruction) (h : inst.opcode = Opcode.ASSERT)
    (k : Nat) (ps : PlanState) :
    StackOp.SOEmit "JUMPI" ∈ (generateEmitOps inst k ps).1 := by
  simp [generateEmitOps, h, opcodeToEvmName]

/-- So a block whose body contains an `ASSERT` is **not** jump-free, and `runAsm_shift` genuinely does
    not apply to it. The hypothesis is doing work. -/
theorem assert_not_bodyJumpFree : ¬ BodyJumpFree Opcode.ASSERT := by
  intro h; exact h.2.1 rfl


/-- `runAsm_shift` wants jump-freeness **indexed by position**; `executePlan_not_jump` gives it by
    membership. This is the adapter, and with it a jump-free plan's assembly is a legal segment. -/
theorem executePlan_nojump_indexed (ops : List StackOp) (h : ∀ op ∈ ops, SOJumpFree op) :
    ∀ j, (hj : j < (executePlan ops).length) →
      IsAsmJump ((executePlan ops).get ⟨j, hj⟩) = false := by
  intro j hj
  exact executePlan_not_jump ops h _ (List.get_mem _ _)

/-- **The lift applies to any jump-free plan's assembly, placed anywhere.** This is `runAsm_shift`
    with its hypothesis discharged from the plan rather than assumed. -/
theorem runAsm_shift_of_plan (n : Nat) (o2pc : AssocList Nat Nat) (prog : List AsmInst)
    (ops : List StackOp) (base : Nat)
    (hblk : asmBlockAt prog base (executePlan ops))
    (hops : ∀ op ∈ ops, SOJumpFree op) :
    ∀ (x s' : AsmState), runAsm n o2pc (executePlan ops) x = AsmResult.AsmOK s' →
      runAsm n o2pc prog { x with pc := base + x.pc }
        = AsmResult.AsmOK { s' with pc := base + s'.pc } :=
  runAsm_shift n o2pc prog (executePlan ops) base hblk (executePlan_nojump_indexed ops hops)

/-! ## The stack planners emit nothing — so a body instruction's plan is jump-free -/


/-- A `StackOp` that is not an `SOEmit` at all. The stack planners in `PlanOps` build only
    `SOSwap`/`SODup`/`SOPop`/`SOSpill`/`SORestore`; `emitOneInput` builds only `SOPush`/`SOPushLabel`.
    None of them can name an EVM opcode, so none of them can be a jump. -/
def NoEmit (op : StackOp) : Prop := ∀ s, op ≠ StackOp.SOEmit s

theorem SOJumpFree_of_noEmit (op : StackOp) (h : NoEmit op) : SOJumpFree op :=
  ⟨h "JUMP", h "JUMPI"⟩

/-- The generic fold invariant: a left fold that only ever *appends* `NoEmit` ops to its op list
    preserves "every op is a NoEmit". Every planner below is such a fold. -/
theorem foldl_mem_noEmit {α β : Type} (l : List α)
    (f : (List StackOp × β) → α → (List StackOp × β))
    (hf : ∀ acc a, (∀ op ∈ acc.1, NoEmit op) → ∀ op ∈ (f acc a).1, NoEmit op)
    (init : List StackOp × β) (hinit : ∀ op ∈ init.1, NoEmit op) :
    ∀ op ∈ (l.foldl f init).1, NoEmit op := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons a t ih => exact ih (f init a) (hf init a hinit)

theorem doSwap_noEmit (dist : Nat) (ps : PlanState) :
    ∀ op ∈ (doSwap dist ps).1, NoEmit op := by
  unfold doSwap
  split_ifs with h0 h16
  · intro op hop; simp at hop
  · intro op hop; simp at hop; subst hop; intro s; simp
  · intro op hop
    simp only [] at hop
    rcases List.mem_append.mp hop with hs | hr
    · -- the spill fold: only SOSpill
      revert hs
      refine foldl_mem_noEmit _ _ ?_ _ (by intro op hop; simp at hop) op
      intro acc a hacc op hop
      rcases List.mem_append.mp hop with h | h
      · exact hacc op h
      · simp at h; subst h; intro s; simp
    · -- the restores: only SORestore
      simp only [List.mem_map] at hr
      obtain ⟨i, _, hi⟩ := hr
      subst hi; intro s; simp

theorem doDup_noEmit (dist : Nat) (ps : PlanState) :
    ∀ op ∈ (doDup dist ps).1, NoEmit op := by
  unfold doDup
  split_ifs with h15
  · intro op hop; simp at hop; subst hop; intro s; simp
  · intro op hop
    simp only [] at hop
    rcases List.mem_append.mp hop with hs | hr
    · revert hs
      refine foldl_mem_noEmit _ _ ?_ _ (by intro op hop; simp at hop) op
      intro acc a hacc op hop
      rcases List.mem_append.mp hop with h | h
      · exact hacc op h
      · simp at h; subst h; intro s; simp
    · simp only [List.mem_map] at hr
      obtain ⟨i, _, hi⟩ := hr
      subst hi; intro s; simp

theorem doRestore_noEmit (o : Operand) (ps : PlanState) :
    ∀ op ∈ (doRestore o ps).1, NoEmit op := by
  unfold doRestore
  split
  · intro op hop; simp at hop
  · intro op hop; simp at hop; subst hop; intro s; simp

theorem reorderOne_noEmit (d : Unit) (targetOps : List Operand) (idx : Nat) (o : Operand)
    (ps : PlanState) : ∀ op ∈ (reorderOne d targetOps idx o ps).1, NoEmit op := by
  simp only [reorderOne]
  repeat' split
  all_goals intro op hop
  all_goals
    first
      | (simp at hop; done)
      | (exact doRestore_noEmit o _ op hop)
      | (rcases List.mem_append.mp hop with h | h
         · rcases List.mem_append.mp h with h | h
           · first
               | (simp at h; done)
               | exact doRestore_noEmit o _ op h
           · exact doSwap_noEmit _ _ op h
         · exact doSwap_noEmit _ _ op h)

theorem reorderPlan_noEmit (targetOps : List Operand) (ps : PlanState) :
    ∀ op ∈ (reorderPlan targetOps ps).1, NoEmit op := by
  unfold reorderPlan
  refine foldl_mem_noEmit _ _ ?_ _ (by intro op hop; simp at hop)
  rintro ⟨ops, ps'⟩ ⟨idx, o⟩ hacc op hop
  rcases List.mem_append.mp hop with h | h
  · exact hacc op h
  · exact reorderOne_noEmit () targetOps idx o ps' op h

theorem popmanyPlan_noEmit (toPop : List Operand) (ps : PlanState) :
    ∀ op ∈ (popmanyPlan toPop ps).1, NoEmit op := by
  simp only [popmanyPlan]
  repeat' split
  all_goals
    first
      | (intro op hop; simp at hop; done)
      | (intro op hop
         rcases List.mem_append.mp hop with h | h
         · exact doSwap_noEmit _ _ op h
         · simp at h; subst h; intro s; simp)
      | (refine foldl_mem_noEmit _ _ ?_ _ (by intro op hop; simp at hop)
         rintro ⟨ops, ps'⟩ v hacc op hop
         simp only [] at hop
         split at hop
         · exact hacc op hop
         · rcases List.mem_append.mp hop with h | h
           · rcases List.mem_append.mp h with h | h
             · exact hacc op h
             · revert h
               split
               · intro h; simp at h
               · exact doSwap_noEmit _ _ op
           · simp at h; subst h; intro s; simp)

theorem emitOneInput_noEmit (opc : Opcode) (nl : List String) (o : Operand) (ps : PlanState) :
    ∀ op ∈ (emitOneInput opc nl o ps).1, NoEmit op := by
  simp only [emitOneInput]
  repeat' split
  all_goals
    intro op hop
    first
      | (simp at hop; done)
      | (exact doRestore_noEmit _ _ op hop)
      | (rcases List.mem_append.mp hop with h | h
         · first
             | (simp at h; done)
             | exact doRestore_noEmit _ _ op h
         · first
             | (simp at h; subst h; intro s; simp)
             | exact doDup_noEmit _ _ op h)

theorem emitInputPlan_noEmit (opc : Opcode) (ops : List Operand) (nl : List String)
    (ps : PlanState) : ∀ op ∈ (emitInputPlan opc ops nl ps).1, NoEmit op := by
  unfold emitInputPlan
  refine foldl_mem_noEmit _ _ ?_ _ (by intro op hop; simp at hop)
  intro acc o hacc op hop
  simp only [] at hop
  rcases List.mem_append.mp hop with h | h
  · exact hacc op h
  · exact emitOneInput_noEmit opc nl o acc.2 op h

theorem optimisticSwapPlan_noEmit (dfg : DfgAnalysis) (inst : Instruction) (nl : List String)
    (nt : Bool) (ps : PlanState) :
    ∀ op ∈ (optimisticSwapPlan dfg inst nl nt ps).1, NoEmit op := by
  simp only [optimisticSwapPlan]
  repeat' split
  all_goals first | (intro op hop; simp at hop) | exact doSwap_noEmit _ _

set_option maxHeartbeats 2000000 in
/-- **A body instruction's whole plan is jump-free.**

`generateRegularInstPlan` is `inputOps ++ joinOps ++ reorderOps ++ emitOps ++ popOps ++ optOps`.
Five of the six come from the stack planners, which build only swaps, dups, pops, spills, restores
and pushes — never an `SOEmit`, so never a jump. The sixth is `generateEmitOps`, and that is exactly
where `BodyJumpFree` earns its keep. -/
theorem generateRegularInstPlan_not_jump (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    (h : BodyJumpFree inst.opcode) :
    ∀ op ∈ (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
              nextIsTerminator curBbLabel ps).1, SOJumpFree op := by
  simp only [generateRegularInstPlan]
  repeat' split
  all_goals intro op hop
  all_goals simp only [List.mem_append] at hop
  all_goals repeat' (rcases hop with hop | hop)
  all_goals
    first
      | exact SOJumpFree_of_noEmit _ (emitInputPlan_noEmit _ _ _ _ _ hop)
      | exact SOJumpFree_of_noEmit _ (reorderPlan_noEmit _ _ _ hop)
      | exact SOJumpFree_of_noEmit _ (popmanyPlan_noEmit _ _ _ hop)
      | exact SOJumpFree_of_noEmit _ (optimisticSwapPlan_noEmit _ _ _ _ _ _ hop)
      | exact generateEmitOps_not_jump _ _ _ h _ hop
      | (simp at hop)


/-- **The chain, closed.** A body instruction's compiled assembly, placed anywhere in the program,
runs there exactly as it runs alone.

No jump-freeness is assumed: it is *derived* from the opcode, via `generateRegularInstPlan_not_jump`
(the plan emits no jump) and `runAsm_shift_of_plan` (a jump-free plan's asm is a liftable segment).
The only hypotheses left are `BodyJumpFree` — which excludes exactly ASSERT, ASSERT_UNREACHABLE,
INVOKE and the terminators, and excludes them because they really do jump — and the placement itself. -/
theorem runAsm_shift_of_bodyInst (n : Nat) (o2pc : AssocList Nat Nat) (prog : List AsmInst)
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (inst : Instruction) (nextLiveness : List String) (isHalting nextIsTerminator : Bool)
    (curBbLabel : String) (ps : PlanState) (base : Nat)
    (hbody : BodyJumpFree inst.opcode)
    (hblk : asmBlockAt prog base
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).1)) :
    ∀ (x s' : AsmState),
      runAsm n o2pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
        isHalting nextIsTerminator curBbLabel ps).1) x = AsmResult.AsmOK s' →
      runAsm n o2pc prog { x with pc := base + x.pc }
        = AsmResult.AsmOK { s' with pc := base + s'.pc } :=
  runAsm_shift_of_plan n o2pc prog _ base hblk
    (generateRegularInstPlan_not_jump liveness dfg cfg fn inst nextLiveness isHalting
      nextIsTerminator curBbLabel ps hbody)

/-! ## From one instruction to a block: the dispatcher and the block-body fold -/


theorem generatePhiPlan_noEmit (inst : Instruction) (nl : List String) (ps : PlanState) :
    ∀ op ∈ (generatePhiPlan inst nl ps).1, NoEmit op := by
  simp only [generatePhiPlan]
  repeat' split
  all_goals intro op hop
  all_goals
    first
      | (simp at hop; done)
      | (simp at hop; subst hop; intro s; simp)
      | (rcases List.mem_append.mp hop with h | h
         · exact doDup_noEmit _ _ op h
         · simp at h; subst h; intro s; simp)

theorem generateOffsetPlan_noEmit (inst : Instruction) (ps : PlanState) :
    ∀ op ∈ (generateOffsetPlan inst ps).1, NoEmit op := by
  simp only [generateOffsetPlan]
  repeat' split
  all_goals intro op hop
  all_goals first | (simp at hop; done) | (simp at hop; subst hop; intro s; simp)

theorem prepareParamsPlan_noEmit (liveness : DfState (List String)) (fn : IrFunction)
    (ps : PlanState) : ∀ op ∈ (prepareParamsPlan liveness fn ps).1, NoEmit op := by
  simp only [prepareParamsPlan]
  repeat' split
  all_goals intro op hop
  all_goals
    first
      | (simp at hop; done)
      | (rcases List.mem_append.mp hop with h | h
         · exact popmanyPlan_noEmit _ _ op h
         · exact optimisticSwapPlan_noEmit _ _ _ _ _ op h)

theorem cleanStackPlan_noEmit (liveness : DfState (List String)) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) :
    ∀ op ∈ (cleanStackPlan liveness cfg fn bb ps).1, NoEmit op := by
  simp only [cleanStackPlan]
  repeat' split
  all_goals intro op hop
  all_goals first | (simp at hop; done) | (exact popmanyPlan_noEmit _ _ op hop)

/-- **The dispatcher.** `generateInstPlan` routes to phi / offset / param / nop / regular. The first
four are pure stack shuffling and cannot emit at all; only the regular path can, and there
`BodyJumpFree` does the work. -/
theorem generateInstPlan_not_jump (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    (h : BodyJumpFree inst.opcode) (ops : List StackOp) (ps' : PlanState)
    (hsome : generateInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
      curBbLabel ps = some (ops, ps')) :
    ∀ op ∈ ops, SOJumpFree op := by
  revert hsome
  simp only [generateInstPlan]
  split_ifs
  · intro hsome; simp at hsome
  all_goals intro hsome op hop
  all_goals
    (have hq : _ = ops := (Prod.ext_iff.mp (Option.some.inj hsome)).1
     rw [← hq] at hop)
  · exact SOJumpFree_of_noEmit _ (generatePhiPlan_noEmit _ _ _ op hop)
  · exact SOJumpFree_of_noEmit _ (generateOffsetPlan_noEmit _ _ op hop)
  · exact generateRegularInstPlan_not_jump _ _ _ _ _ _ _ _ _ _ h op hop
  · simp at hop
  · simp at hop
  · exact generateRegularInstPlan_not_jump _ _ _ _ _ _ _ _ _ _ h op hop

/-! ## The block-body fold

`generateBlockPlan` folds `generateInstPlan` over **all** the block's instructions — terminator included
— so the block's plan is emphatically **not** jump-free, and a theorem saying it was would be false.
What is true, and what the recipe needs, is that the fold stays jump-free as long as the instructions it
has consumed so far are body instructions. -/

/-- The invariant: an `Option` plan accumulator whose ops are all jump-free. -/
def AccJumpFree (acc : Option (List StackOp × PlanState)) : Prop :=
  ∀ ops ps, acc = some (ops, ps) → ∀ op ∈ ops, SOJumpFree op

/-- Generic: a left fold over an `Option` accumulator preserves `AccJumpFree`, provided every element
    it consumes does. -/
theorem foldl_option_jumpfree {α : Type} (P : α → Prop) (l : List α)
    (F : Option (List StackOp × PlanState) → α → Option (List StackOp × PlanState))
    (hF : ∀ acc a, P a → AccJumpFree acc → AccJumpFree (F acc a))
    (acc : Option (List StackOp × PlanState)) (hacc : AccJumpFree acc)
    (hl : ∀ a ∈ l, P a) : AccJumpFree (l.foldl F acc) := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons a t ih =>
    exact ih (F acc a) (hF acc a (hl a (by simp)) hacc) (fun b hb => hl b (by simp [hb]))

/-- The step function `generateBlockPlan` folds. Mirrors the compiler's lambda exactly; the
    correspondence is `generateBlockPlan_fold_eq` below, proved by `rfl`. A definition I write to mirror
    the compiler proves nothing until that lemma exists. -/
def blockFoldStep (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction) (isHalting : Bool) (nParams : Nat)
    (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat)
    : Option (List StackOp × PlanState) :=
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
    | some (stepOps, ps') => some (ops ++ stepOps, ps')

/-- One fold step keeps the accumulator jump-free, when the instruction it consumes is a body one. -/
theorem blockFoldStep_jumpfree (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (acc : Option (List StackOp × PlanState))
    (instI : Instruction × Nat) (hbody : BodyJumpFree instI.1.opcode) (hacc : AccJumpFree acc) :
    AccJumpFree (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams acc instI) := by
  unfold AccJumpFree blockFoldStep
  cases acc with
  | none => intro ops ps h; simp at h
  | some p =>
    obtain ⟨ops0, ps0⟩ := p
    obtain ⟨inst, i⟩ := instI
    simp only []
    split
    · intro ops ps h; simp at h
    · rename_i stepOps ps' hgen
      intro ops ps h
      have hq : ops0 ++ stepOps = ops := (Prod.ext_iff.mp (Option.some.inj h)).1
      subst hq
      intro op hop
      rcases List.mem_append.mp hop with hm | hm
      · exact hacc ops0 ps0 rfl op hm
      · exact generateInstPlan_not_jump _ _ _ _ _ _ _ _ _ _ hbody _ _ hgen op hm

/-- **A run of body instructions folds to a jump-free plan.** -/
theorem blockFold_jumpfree (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (l : List (Instruction × Nat))
    (hl : ∀ p ∈ l, BodyJumpFree p.1.opcode)
    (acc : Option (List StackOp × PlanState)) (hacc : AccJumpFree acc) :
    AccJumpFree (l.foldl (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) acc) :=
  foldl_option_jumpfree (fun p => BodyJumpFree p.1.opcode) l _
    (fun acc a hp hA => blockFoldStep_jumpfree _ _ _ _ _ _ _ _ acc a hp hA) acc hacc hl


/-- **The correspondence.** `blockFoldStep` really is the lambda `generateBlockPlan` folds. Without this
    the previous lemmas would be about a definition of mine and nothing else. -/
theorem generateBlockPlan_eq_fold (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) :
    generateBlockPlan liveness dfg cfg fn bb ps =
      (let labelOp := [StackOp.SOLabel bb.label]
       let (paramOps, ps1) :=
         if (fn.blocks.head?.map (·.label)) == some bb.label then prepareParamsPlan liveness fn ps
         else ([], ps)
       let (cleanOps, ps2) :=
         if (cfg.predsOf bb.label).length = 1 then cleanStackPlan liveness cfg fn bb ps1
         else ([], ps1)
       let insts := nonParamInsts bb
       let isHalting := bbIsHalting bb
       let nParams := (getParams bb.instructions).length
       match insts.zipIdx.foldl
           (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps2)) with
       | none => none
       | some (instOps, ps3) => some (labelOp ++ paramOps ++ cleanOps ++ instOps, ps3)) := rfl

/-- The fold splits at the last instruction: everything before the terminator, then the terminator. -/
theorem zipIdx_foldl_split {β : Type} (l : List Instruction) (x : Instruction)
    (F : β → Instruction × Nat → β) (acc : β) :
    (l ++ [x]).zipIdx.foldl F acc = F (l.zipIdx.foldl F acc) (x, l.length) := by
  rw [List.zipIdx_append]
  simp

/-- `p ∈ l.zipIdx → p.1 ∈ l`. Not in the library under a name `exact?` finds. -/
theorem fst_mem_of_mem_zipIdx {α : Type} (l : List α) (p : α × Nat) (hp : p ∈ l.zipIdx) :
    p.1 ∈ l := by
  simp only [List.mem_zipIdx_iff_getElem?] at hp
  exact List.mem_of_getElem? hp

/-- The empty accumulator is jump-free. -/
theorem AccJumpFree_nil (ps : PlanState) : AccJumpFree (some ([], ps)) := by
  intro ops ps' h op hop
  cases h; simp at hop

/-- **The accumulator entering the terminator step is jump-free.**

This is what the recipe needs, and it is the strongest true statement: `generateBlockPlan` folds over
*all* the block's instructions, so its final plan contains the terminator's `JUMP` and is not jump-free.
Everything the fold has built **before** that last step is. -/
theorem blockFold_preTerminator_jumpfree (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (body : List Instruction) (ps : PlanState)
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode) :
    AccJumpFree (body.zipIdx.foldl
      (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps))) := by
  refine blockFold_jumpfree liveness dfg cfg fn bb insts isHalting nParams _ ?_ _
    (AccJumpFree_nil ps)
  intro p hp
  exact hbody p.1 (fst_mem_of_mem_zipIdx _ p hp)

/-- …and the whole fold is that accumulator, put through one more step for the terminator. -/
theorem blockFold_eq_preTerminator (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (body : List Instruction) (term : Instruction)
    (ps : PlanState) :
    (body ++ [term]).zipIdx.foldl
        (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps))
      = blockFoldStep liveness dfg cfg fn bb insts isHalting nParams
          (body.zipIdx.foldl (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams)
            (some ([], ps)))
          (term, body.length) :=
  zipIdx_foldl_split body term _ _

/-! ## Fired on a real block -/


/-- `BodyJumpFree` is decidable — it is a conjunction of an equality on `Bool` and three
    disequalities on `Opcode`. So for any concrete block it is `by decide`. -/
instance BodyJumpFree_decidable (opc : Opcode) : Decidable (BodyJumpFree opc) := by
  unfold BodyJumpFree; infer_instance

/-- Dia's `then` block is `[tA, dJmpT]`: one body instruction, then the terminator. -/
theorem dia_then_body_jumpfree :
    ∀ inst ∈ (nonParamInsts Dia.bThen).dropLast, BodyJumpFree inst.opcode := by decide

/-- …and the terminator itself is **not** — it is a `JMP`. So the whole block's plan really does
    contain a jump, `blockFold_preTerminator_jumpfree` really is the strongest true statement, and the
    hypothesis it carries is not timidity. -/
theorem dia_then_terminator_not_jumpfree :
    ¬ BodyJumpFree (nonParamInsts Dia.bThen).getLast!.opcode := by decide

/-- The block splits as body ++ [terminator]. -/
theorem dia_then_split :
    nonParamInsts Dia.bThen
      = (nonParamInsts Dia.bThen).dropLast ++ [(nonParamInsts Dia.bThen).getLast!] := by rfl

/-- **Fired on a real block.** Everything Dia's `then` block's plan builds before its terminator step
is jump-free — hence a liftable segment — while the block's plan as a whole is not, because the
terminator is a `JMP`. The two theorems above are the two halves of that, and they meet exactly at the
block boundary. -/
theorem dia_then_preTerminator_jumpfree (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (insts : List Instruction) (isHalting : Bool)
    (nParams : Nat) (ps : PlanState) :
    AccJumpFree ((nonParamInsts Dia.bThen).dropLast.zipIdx.foldl
      (blockFoldStep liveness dfg cfg fn Dia.bThen insts isHalting nParams) (some ([], ps))) :=
  blockFold_preTerminator_jumpfree liveness dfg cfg fn Dia.bThen insts isHalting nParams _ ps
    dia_then_body_jumpfree


/-! ## Placement is a theorem, not a hypothesis

`runAsm_shift` takes `asmBlockAt prog base blk` as a hypothesis: "the block's assembly really sits at
`base` in the program." For a concrete function that is `by decide`, but for the recipe it has to be
*derived* from how the compiler lays a function out. It can be, and the reason is structural:
`executePlan` is a flatMap, so it distributes over `++`; and `asmResolve` is a **map**, so it preserves
positions exactly. -/

/-- A slice sits where the prefix ends. -/
theorem asmBlockAt_of_append (pre blk post : List AsmInst) :
    asmBlockAt (pre ++ blk ++ post) pre.length blk := by
  constructor
  · simp
  · intro j hj
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp [List.getElem?_append_left hj]

/-- `resolveInst` only rewrites `AsmPushLabel`/`AsmPushOfst` into pushes, so it cannot create — or
    destroy — a jump. -/
theorem resolveInst_not_jump (offs : AssocList String Nat) (a : AsmInst)
    (h : IsAsmJump a = false) : IsAsmJump (resolveInst offs a) = false := by
  cases a <;>
    first
      | (simpa [resolveInst] using h)
      | (simp only [resolveInst]; split <;> rfl)
      | (simp [resolveInst, IsAsmJump])

theorem asmResolve_eq_map (asm : List AsmInst) :
    (asmResolve asm).1 = asm.map (resolveInst (computeLabelOffsets asm).2) := rfl

/-- **A block's assembly really is where the prefix ends.** No `asmBlockAt` hypothesis: it is derived.

If the function's plan is `pre ++ blk ++ post`, then in the assembled, symbol-resolved program the
block's own assembly sits at exactly `(executePlan pre).length`. `executePlan` distributes over `++`
because it is a flatMap; `asmResolve` preserves the position because it is a map. -/
theorem blockAsm_placed_gen (f : AsmInst → AsmInst) (pre blk post : List StackOp) :
    asmBlockAt ((executePlan (pre ++ blk ++ post)).map f) (executePlan pre).length
      ((executePlan blk).map f) := by
  rw [executePlan_append, executePlan_append, List.map_append, List.map_append]
  simpa using asmBlockAt_of_append
    ((executePlan pre).map f) ((executePlan blk).map f) ((executePlan post).map f)

/-- The compiler's own layout: `asmResolve` is a map, so the block's assembly is at the prefix length. -/
theorem blockAsm_placed (pre blk post : List StackOp) :
    asmBlockAt (asmResolve (executePlan (pre ++ blk ++ post))).1 (executePlan pre).length
      ((executePlan blk).map
        (resolveInst (computeLabelOffsets (executePlan (pre ++ blk ++ post))).2)) := by
  rw [asmResolve_eq_map]
  exact blockAsm_placed_gen _ pre blk post

/-- …and that assembly is jump-free, if the block's plan is. -/
theorem blockAsm_placed_nojump (offs : AssocList String Nat) (blk : List StackOp)
    (hops : ∀ op ∈ blk, SOJumpFree op) :
    ∀ j, (hj : j < ((executePlan blk).map (resolveInst offs)).length) →
      IsAsmJump (((executePlan blk).map (resolveInst offs)).get ⟨j, hj⟩) = false := by
  intro j hj
  have hmem : ((executePlan blk).map (resolveInst offs)).get ⟨j, hj⟩ ∈
      (executePlan blk).map (resolveInst offs) := List.get_mem _ _
  rw [List.mem_map] at hmem
  obtain ⟨a, ha, hres⟩ := hmem
  rw [← hres]
  exact resolveInst_not_jump offs a (executePlan_not_jump blk hops a ha)

/-- **The lift, with nothing assumed about the assembly.**

Give it a function plan split as `pre ++ blk ++ post` where `blk` emits no jump, and it says: the
block's assembly, as the compiler actually lays it out and resolves it, runs inside the whole program
exactly as it runs alone — displaced by the length of everything before it.

`asmBlockAt` is gone. It used to be a hypothesis, discharged per-function by `decide`; now it is
`blockAsm_placed`, a theorem about how `executePlan` and `asmResolve` compose. The only hypothesis left
is about the *plan*: `blk` emits no `SOEmit "JUMP"`/`"JUMPI"` — which, for a block body,
`blockFold_preTerminator_jumpfree` supplies from the Venom opcodes. -/
theorem runAsm_shift_placed (n : Nat) (o2pc : AssocList Nat Nat)
    (pre blk post : List StackOp) (hops : ∀ op ∈ blk, SOJumpFree op) :
    ∀ (x s' : AsmState),
      runAsm n o2pc ((executePlan blk).map
          (resolveInst (computeLabelOffsets (executePlan (pre ++ blk ++ post))).2)) x
        = AsmResult.AsmOK s' →
      runAsm n o2pc (asmResolve (executePlan (pre ++ blk ++ post))).1
          { x with pc := (executePlan pre).length + x.pc }
        = AsmResult.AsmOK { s' with pc := (executePlan pre).length + s'.pc } :=
  runAsm_shift n o2pc (asmResolve (executePlan (pre ++ blk ++ post))).1
    ((executePlan blk).map
      (resolveInst (computeLabelOffsets (executePlan (pre ++ blk ++ post))).2))
    (executePlan pre).length
    (blockAsm_placed pre blk post)
    (blockAsm_placed_nojump _ blk hops)


/-- **The per-block recipe.**

Take a block's body — its instructions up to but not including the terminator — and let `bodyOps` be
what the compiler's own fold plans for them. Then, wherever that sits inside the function's plan, the
assembly it compiles to runs inside the whole program exactly as it runs alone, displaced by the length
of everything before it.

Every hypothesis is about the **Venom source**, not the assembly:
* `hbody` — the body instructions are `BodyJumpFree` (decidable; excludes exactly the terminators plus
  ASSERT / ASSERT_UNREACHABLE / INVOKE, which really do jump mid-block).
* `hfold` — `bodyOps` is what the compiler's fold produces (`blockFoldStep`, tied to `generateBlockPlan`
  by `generateBlockPlan_eq_fold`).
* the split `pre ++ bodyOps ++ post` — where the function's plan puts it.

`asmBlockAt`, `IsAsmJump`-freeness of the assembly, and the pc displacement are all *derived*. -/
theorem runAsm_shift_blockBody (n : Nat) (o2pc : AssocList Nat Nat)
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (insts : List Instruction) (isHalting : Bool) (nParams : Nat)
    (body : List Instruction) (ps0 ps1 : PlanState) (bodyOps pre post : List StackOp)
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode)
    (hfold : body.zipIdx.foldl
      (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps0))
        = some (bodyOps, ps1)) :
    ∀ (x s' : AsmState),
      runAsm n o2pc ((executePlan bodyOps).map
          (resolveInst (computeLabelOffsets (executePlan (pre ++ bodyOps ++ post))).2)) x
        = AsmResult.AsmOK s' →
      runAsm n o2pc (asmResolve (executePlan (pre ++ bodyOps ++ post))).1
          { x with pc := (executePlan pre).length + x.pc }
        = AsmResult.AsmOK { s' with pc := (executePlan pre).length + s'.pc } :=
  runAsm_shift_placed n o2pc pre bodyOps post
    (blockFold_preTerminator_jumpfree liveness dfg cfg fn bb insts isHalting nParams body ps0
      hbody bodyOps ps1 hfold)

/-! ## A block's plan splits as prologue ++ body ++ terminator -/


/-- One `blockFoldStep` on a `some` accumulator appends. -/
theorem blockFoldStep_append (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (ops : List StackOp) (ps : PlanState)
    (instI : Instruction × Nat) (out : List StackOp) (psOut : PlanState)
    (h : blockFoldStep liveness dfg cfg fn bb insts isHalting nParams (some (ops, ps)) instI
          = some (out, psOut)) :
    ∃ stepOps, out = ops ++ stepOps := by
  revert h
  unfold blockFoldStep
  obtain ⟨inst, i⟩ := instI
  simp only []
  split
  · intro h; simp at h
  · rename_i stepOps ps' hgen
    intro h
    exact ⟨stepOps, ((Prod.ext_iff.mp (Option.some.inj h)).1).symm⟩

/-- **A block's instruction-fold splits as body ++ terminator.** The fold over `body ++ [term]` is the
    fold over `body` — the jump-free part — with the terminator's ops appended. -/
theorem blockFold_body_slice (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (insts : List Instruction)
    (isHalting : Bool) (nParams : Nat) (body : List Instruction) (term : Instruction)
    (ps : PlanState) (ops : List StackOp) (psOut : PlanState)
    (h : (body ++ [term]).zipIdx.foldl
      (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps))
        = some (ops, psOut)) :
    ∃ bodyOps psB termOps,
      body.zipIdx.foldl (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams)
          (some ([], ps)) = some (bodyOps, psB)
      ∧ ops = bodyOps ++ termOps := by
  rw [blockFold_eq_preTerminator] at h
  cases hb : body.zipIdx.foldl
      (blockFoldStep liveness dfg cfg fn bb insts isHalting nParams) (some ([], ps)) with
  | none => rw [hb] at h; simp [blockFoldStep] at h
  | some p =>
    obtain ⟨bodyOps, psB⟩ := p
    rw [hb] at h
    obtain ⟨termOps, hterm⟩ := blockFoldStep_append liveness dfg cfg fn bb insts isHalting nParams
      bodyOps psB (term, body.length) ops psOut h
    exact ⟨bodyOps, psB, termOps, rfl, hterm⟩

/-- **A block's plan splits as prologue ++ body ++ terminator**, and the middle is jump-free whenever
the body instructions are. This is the split `runAsm_shift_blockBody` wants, and note the prologue is
generally *non-empty* — it always contains at least the block's own `SOLabel` — so even the entry
block's body sits at a **nonzero** offset. A slice at offset 0 would make the displacement law
degenerate. -/
theorem generateBlockPlan_body_slice (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (ps : PlanState)
    (body : List Instruction) (term : Instruction)
    (hsplit : nonParamInsts bb = body ++ [term])
    (ops : List StackOp) (ps3 : PlanState)
    (h : generateBlockPlan liveness dfg cfg fn bb ps = some (ops, ps3)) :
    ∃ pre bodyOps termOps,
      ops = pre ++ bodyOps ++ termOps
      ∧ ((∀ inst ∈ body, BodyJumpFree inst.opcode) → ∀ op ∈ bodyOps, SOJumpFree op) := by
  rw [generateBlockPlan_eq_fold] at h
  simp only [hsplit] at h
  split at h
  · simp at h
  · rename_i instOps psF hfold
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hops, -⟩ := h
    subst hops
    obtain ⟨bodyOps, psB, termOps, hbf, hio⟩ :=
      blockFold_body_slice _ _ _ _ _ _ _ _ body term _ _ _ hfold
    subst hio
    exact ⟨_, bodyOps, termOps, (List.append_assoc _ _ _).symm,
      fun hbody => blockFold_preTerminator_jumpfree _ _ _ _ _ _ _ _ body _ hbody bodyOps psB hbf⟩

/-! ## End to end: from the Venom source to the running program -/


/-- **A block's body is a jump-free slice of the function's plan.**

Composes the DFS layout (`generateFnPlanAux_head_prefix`, already in the codebase: the head block's
plan is a *prefix* of the DFS output) with the in-block split (`generateBlockPlan_body_slice`:
prologue ++ body ++ terminator). The result: the function's plan really is `pre ++ bodyOps ++ post`
with `bodyOps` jump-free — the split `runAsm_shift_placed` needs, now a theorem. -/
theorem fnPlan_body_slice {fuel : Nat} {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {lbl : String} {visited : List String} {ps : PlanState}
    {bb : BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {body : List Instruction} {term : Instruction}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hblock : generateBlockPlan L D C fn bb ps = some (blockOps, ps'))
    (hsplit : nonParamInsts bb = body ++ [term])
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode) :
    ∃ pre bodyOps post vF psF,
      generateFnPlanAux (fuel + 1) L D C fn [lbl] visited ps
          = some (pre ++ bodyOps ++ post, vF, psF)
      ∧ (∀ op ∈ bodyOps, SOJumpFree op) := by
  obtain ⟨tailOps, vF, psF, hdfs⟩ :=
    generateFnPlanAux_head_prefix (fuel := fuel) hfn hvis hfind hblock
  obtain ⟨pre, bodyOps, termOps, hops, hjf⟩ :=
    generateBlockPlan_body_slice L D C fn bb ps body term hsplit blockOps ps' hblock
  refine ⟨pre, bodyOps, termOps ++ tailOps, vF, psF, ?_, hjf hbody⟩
  rw [hdfs, hops]
  simp [List.append_assoc]

/-- **End to end.** The compiler plans a function; a block's body occupies a slice of that plan; the
assembly that slice compiles to runs inside the whole assembled, symbol-resolved program exactly as it
runs alone, displaced by the length of everything before it.

Every hypothesis is about the **Venom source**: the block is found and unvisited, its instructions are
`body ++ [term]`, and the body instructions are `BodyJumpFree` (decidable). Nothing is assumed about
the plan, the assembly, the label offsets, or the program counter — the layout (`blockAsm_placed`), the
jump-freeness of the emitted instructions (`blockFold_preTerminator_jumpfree` + `resolveInst_not_jump`)
and the displacement (`runAsm_shift`) are all derived. -/
theorem blockBody_runs_in_program {fuel : Nat} {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {lbl : String} {visited : List String} {ps : PlanState}
    {bb : BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {body : List Instruction} {term : Instruction}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hblock : generateBlockPlan L D C fn bb ps = some (blockOps, ps'))
    (hsplit : nonParamInsts bb = body ++ [term])
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode)
    (n : Nat) (o2pc : AssocList Nat Nat) :
    ∃ pre bodyOps post vF psF,
      generateFnPlanAux (fuel + 1) L D C fn [lbl] visited ps
          = some (pre ++ bodyOps ++ post, vF, psF)
      ∧ ∀ (x s'' : AsmState),
          runAsm n o2pc ((executePlan bodyOps).map
              (resolveInst (computeLabelOffsets (executePlan (pre ++ bodyOps ++ post))).2)) x
            = AsmResult.AsmOK s'' →
          runAsm n o2pc (asmResolve (executePlan (pre ++ bodyOps ++ post))).1
              { x with pc := (executePlan pre).length + x.pc }
            = AsmResult.AsmOK { s'' with pc := (executePlan pre).length + s''.pc } := by
  obtain ⟨pre, bodyOps, post, vF, psF, hdfs, hjf⟩ :=
    fnPlan_body_slice (fuel := fuel) hfn hvis hfind hblock hsplit hbody
  exact ⟨pre, bodyOps, post, vF, psF, hdfs,
    runAsm_shift_placed n o2pc pre bodyOps post hjf⟩

/-! ## The DFS lays every block down contiguously — and so the recipe is general -/


/-- `ops` contains `bb`'s generated plan as a contiguous slice. The plan state it was generated from is
    existential — the DFS threads it, and the slice property does not care which one it was. -/
def BlockSliceOf (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (ops : List StackOp) (bb : BasicBlock) : Prop :=
  ∃ psb blockOps psb' pre post,
    generateBlockPlan L D C fn bb psb = some (blockOps, psb') ∧ ops = pre ++ blockOps ++ post

theorem BlockSliceOf_append_left {L D C fn ops bb} (a : List StackOp)
    (h : BlockSliceOf L D C fn ops bb) : BlockSliceOf L D C fn (a ++ ops) bb := by
  obtain ⟨psb, blockOps, psb', pre, post, hbp, hops⟩ := h
  exact ⟨psb, blockOps, psb', a ++ pre, post, hbp, by rw [hops]; simp [List.append_assoc]⟩

theorem BlockSliceOf_append_right {L D C fn ops bb} (b : List StackOp)
    (h : BlockSliceOf L D C fn ops bb) : BlockSliceOf L D C fn (ops ++ b) bb := by
  obtain ⟨psb, blockOps, psb', pre, post, hbp, hops⟩ := h
  exact ⟨psb, blockOps, psb', pre, post ++ b, hbp, by rw [hops]; simp [List.append_assoc]⟩

theorem generateSuccsPlan_cons_gen (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (ss : List Operand) (sp : SpilledMap) (succ : String)
    (rest visited : List String) (psG : PlanState) :
    generateSuccsPlan (fuel + 1) L D C fn ss sp (succ :: rest) visited psG =
    (match generateFnPlanAux fuel L D C fn [succ] visited
        { psG with stack := ss, spilled := sp } with
     | none => none
     | some (sOps, vAfter, psAfter) =>
       match generateSuccsPlan fuel L D C fn ss sp rest vAfter
               { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
       | none => none
       | some (restOps, vF, psF) => some (sOps ++ restOps, vF, psF)) := rfl

theorem contains_cons_false {l : List String} {x a : String} (hne : ¬ (x = a))
    (h : l.contains a = false) : (x :: l).contains a = false := by
  have h' : a ∉ l := by simpa using h
  simp [Ne.symm hne, h']

/-- **Every block the DFS plans has its plan as a contiguous slice of the DFS's output.**

Mutual induction on the fuel, over `generateFnPlanAux` and `generateSuccsPlan` together. No
visited-set monotonicity lemma is needed — at each recursive call the proof simply case-splits on
whether the label in question landed in the intermediate `visited` set, which decides which sub-call
planned it. -/
theorem dfs_block_slice (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) : ∀ fuel : Nat,
    (∀ wl visited ps ops v ps2,
      generateFnPlanAux fuel L D C fn wl visited ps = some (ops, v, ps2) →
      ∀ lbl bb, fn.blocks.find? (·.label == lbl) = some bb →
        v.contains lbl = true → visited.contains lbl = false →
        BlockSliceOf L D C fn ops bb)
    ∧
    (∀ ss sp succs visited ps ops v ps2,
      generateSuccsPlan fuel L D C fn ss sp succs visited ps = some (ops, v, ps2) →
      ∀ lbl bb, fn.blocks.find? (·.label == lbl) = some bb →
        v.contains lbl = true → visited.contains lbl = false →
        BlockSliceOf L D C fn ops bb) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro wl visited ps ops v ps2 h lbl bb _ hv hnv
      rw [show generateFnPlanAux 0 L D C fn wl visited ps = some ([], visited, ps) from rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hveq, -⟩ := h
      rw [← hveq, hnv] at hv; simp at hv
    · intro ss sp succs visited ps ops v ps2 h lbl bb _ hv hnv
      rw [show generateSuccsPlan 0 L D C fn ss sp succs visited ps = some ([], visited, ps) from rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hveq, -⟩ := h
      rw [← hveq, hnv] at hv; simp at hv
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    constructor
    · -- generateFnPlanAux (n+1)
      intro wl visited ps ops v ps2 h lbl bb hfind hv hnv
      cases wl with
      | nil =>
        rw [generateFnPlanAux_nil] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hveq, -⟩ := h
        rw [← hveq, hnv] at hv; simp at hv
      | cons lbl0 rest =>
        by_cases hv0 : visited.contains lbl0 = true
        · rw [generateFnPlanAux_skip_visited n L D C fn lbl0 rest visited ps hv0] at h
          exact ihA rest visited ps ops v ps2 h lbl bb hfind hv hnv
        · simp only [Bool.not_eq_true] at hv0
          cases hfind0 : fn.blocks.find? (·.label == lbl0) with
          | none =>
            rw [generateFnPlanAux_find_none n L D C fn lbl0 rest visited ps hv0 hfind0] at h
            have hne : ¬ (lbl0 = lbl) := by
              intro he; rw [he, hfind] at hfind0; simp at hfind0
            have hnv' : (lbl0 :: visited).contains lbl = false := contains_cons_false hne hnv
            exact ihA rest (lbl0 :: visited) ps ops v ps2 h lbl bb hfind hv hnv'
          | some bb0 =>
            rw [generateFnPlanAux_visit_block n L D C fn lbl0 rest visited ps bb0 hv0 hfind0] at h
            split at h
            · simp at h
            · rename_i blockOps ps' hbp
              split at h
              · simp at h
              · rename_i succOps visited'' ps'' hsp
                split at h
                · simp at h
                · rename_i restOps vF psF hrp
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hops, hveq, -⟩ := h
                  by_cases hlbl : lbl0 = lbl
                  · -- the block just planned
                    subst hlbl
                    rw [hfind0] at hfind
                    cases hfind
                    exact ⟨ps, blockOps, ps', [], succOps ++ restOps, hbp, by
                      rw [← hops]; simp [List.append_assoc]⟩
                  · have hnv' : (lbl0 :: visited).contains lbl = false :=
                      contains_cons_false hlbl hnv
                    by_cases hv'' : visited''.contains lbl = true
                    · have := ihB ps'.stack ps'.spilled (C.succsOf lbl0) (lbl0 :: visited) ps'
                        succOps visited'' ps'' hsp lbl bb hfind hv'' hnv'
                      rw [← hops]
                      exact BlockSliceOf_append_right restOps
                        (BlockSliceOf_append_left blockOps this)
                    · simp only [Bool.not_eq_true] at hv''
                      have := ihA rest visited'' ps'' restOps vF psF hrp lbl bb hfind
                        (by rw [← hveq] at hv; exact hv) hv''
                      rw [← hops, List.append_assoc]
                      exact BlockSliceOf_append_left blockOps
                        (BlockSliceOf_append_left succOps this)
    · -- generateSuccsPlan (n+1)
      intro ss sp succs visited ps ops v ps2 h lbl bb hfind hv hnv
      cases succs with
      | nil =>
        rw [generateSuccsPlan_nil] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hveq, -⟩ := h
        rw [← hveq, hnv] at hv; simp at hv
      | cons succ rest =>
        rw [generateSuccsPlan_cons_gen n L D C fn ss sp succ rest visited ps] at h
        split at h
        · simp at h
        · rename_i sOps vAfter psAfter hfa
          split at h
          · simp at h
          · rename_i restOps vF psF hsr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hops, hveq, -⟩ := h
            by_cases hva : vAfter.contains lbl = true
            · have := ihA [succ] visited { ps with stack := ss, spilled := sp } sOps vAfter psAfter
                hfa lbl bb hfind hva hnv
              rw [← hops]
              exact BlockSliceOf_append_right restOps this
            · simp only [Bool.not_eq_true] at hva
              have := ihB ss sp rest vAfter
                { ps with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
                restOps vF psF hsr lbl bb hfind (by rw [← hveq] at hv; exact hv) hva
              rw [← hops]
              exact BlockSliceOf_append_left sOps this

/-- **Any block's body is a jump-free slice of the DFS's plan.** No longer just the head of the
    worklist: `dfs_block_slice` handles an arbitrary block the DFS visits. -/
theorem fnPlan_body_slice_any {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {fn : IrFunction} {fuel : Nat} {wl visited : List String} {ps : PlanState}
    {ops : List StackOp} {v : List String} {ps2 : PlanState}
    (h : generateFnPlanAux fuel L D C fn wl visited ps = some (ops, v, ps2))
    {lbl : String} {bb : BasicBlock}
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hv : v.contains lbl = true) (hnv : visited.contains lbl = false)
    {body : List Instruction} {term : Instruction}
    (hsplit : nonParamInsts bb = body ++ [term])
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode) :
    ∃ pre bodyOps post,
      ops = pre ++ bodyOps ++ post ∧ (∀ op ∈ bodyOps, SOJumpFree op) := by
  obtain ⟨psb, blockOps, psb', pre0, post0, hbp, hops⟩ :=
    (dfs_block_slice L D C fn fuel).1 wl visited ps ops v ps2 h lbl bb hfind hv hnv
  obtain ⟨pre1, bodyOps, termOps, hblk, hjf⟩ :=
    generateBlockPlan_body_slice L D C fn bb psb body term hsplit blockOps psb' hbp
  refine ⟨pre0 ++ pre1, bodyOps, termOps ++ post0, ?_, hjf hbody⟩
  rw [hops, hblk]
  simp [List.append_assoc]

/-- **End to end, for any block of the function.**

The DFS plans a function; *any* block it visits has its body as a jump-free contiguous slice of that
plan; and the assembly that slice compiles to runs inside the whole assembled, symbol-resolved program
exactly as it runs alone, displaced by the length of everything before it.

Every hypothesis is about the Venom source. This is the general form of `blockBody_runs_in_program`,
which was stated only for the block at the head of the DFS worklist. -/
theorem blockBody_runs_in_program_any {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {fn : IrFunction} {fuel : Nat} {wl visited : List String} {ps : PlanState}
    {ops : List StackOp} {v : List String} {ps2 : PlanState}
    (h : generateFnPlanAux fuel L D C fn wl visited ps = some (ops, v, ps2))
    {lbl : String} {bb : BasicBlock}
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hv : v.contains lbl = true) (hnv : visited.contains lbl = false)
    {body : List Instruction} {term : Instruction}
    (hsplit : nonParamInsts bb = body ++ [term])
    (hbody : ∀ inst ∈ body, BodyJumpFree inst.opcode)
    (n : Nat) (o2pc : AssocList Nat Nat) :
    ∃ pre bodyOps post,
      ops = pre ++ bodyOps ++ post
      ∧ ∀ (x s'' : AsmState),
          runAsm n o2pc ((executePlan bodyOps).map
              (resolveInst (computeLabelOffsets (executePlan (pre ++ bodyOps ++ post))).2)) x
            = AsmResult.AsmOK s'' →
          runAsm n o2pc (asmResolve (executePlan (pre ++ bodyOps ++ post))).1
              { x with pc := (executePlan pre).length + x.pc }
            = AsmResult.AsmOK { s'' with pc := (executePlan pre).length + s''.pc } := by
  obtain ⟨pre, bodyOps, post, hops, hjf⟩ :=
    fnPlan_body_slice_any h hfind hv hnv hsplit hbody
  exact ⟨pre, bodyOps, post, hops, runAsm_shift_placed n o2pc pre bodyOps post hjf⟩

/-! ## …fired on a block the DFS reaches through a successor edge -/


/-- The DFS state Dia's compilation actually runs with. -/
abbrev Dia.L := livenessAnalyzeFuel (fnPlanFuel Dia.fn) Dia.fn
abbrev Dia.D := DfgAnalysis.buildFunction Dia.fn
abbrev Dia.C := cfgAnalyze Dia.fn
abbrev Dia.PS : PlanState := { initPlanState 0 with labelCounter := 0 }

/-- The DFS really does visit `then`, and it is **not** the head of the worklist — it is reached
    through `generateSuccsPlan`, which is exactly the path the mutual induction was needed for. -/
theorem dia_dfs_visits_then :
    ∃ ops v ps2,
      generateFnPlanAux (fnPlanFuel Dia.fn) Dia.L Dia.D Dia.C Dia.fn ["entry"] [] Dia.PS
        = some (ops, v, ps2)
      ∧ v.contains "then" = true
      ∧ ([] : List String).contains "then" = false := by
  refine ⟨_, _, _, rfl, ?_, rfl⟩
  rfl

/-- **The general recipe, fired on a block the DFS reaches through a successor edge.**

`then` is not the head of the worklist — the DFS gets to it via `generateSuccsPlan` — so this witness
exercises exactly the case that `generateFnPlanAux_head_prefix` could not reach and the mutual induction
was built for. Firing on the entry block would have proved nothing about the generalisation. -/
theorem dia_then_runs_in_program (n : Nat) (o2pc : AssocList Nat Nat) :
    ∃ ops v ps2,
      generateFnPlanAux (fnPlanFuel Dia.fn) Dia.L Dia.D Dia.C Dia.fn ["entry"] [] Dia.PS
        = some (ops, v, ps2)
      ∧ ∃ pre bodyOps post,
          ops = pre ++ bodyOps ++ post
          ∧ ∀ (x s'' : AsmState),
              runAsm n o2pc ((executePlan bodyOps).map
                  (resolveInst (computeLabelOffsets (executePlan (pre ++ bodyOps ++ post))).2)) x
                = AsmResult.AsmOK s'' →
              runAsm n o2pc (asmResolve (executePlan (pre ++ bodyOps ++ post))).1
                  { x with pc := (executePlan pre).length + x.pc }
                = AsmResult.AsmOK { s'' with pc := (executePlan pre).length + s''.pc } := by
  refine ⟨_, _, _, rfl, ?_⟩
  exact blockBody_runs_in_program_any (L := Dia.L) (D := Dia.D) (C := Dia.C)
    (fn := Dia.fn) (fuel := fnPlanFuel Dia.fn) (wl := ["entry"]) (visited := []) (ps := Dia.PS)
    rfl (lbl := "then") (bb := Dia.bThen) rfl (by rfl) rfl
    dia_then_split dia_then_body_jumpfree n o2pc

/-! ## The recipe composes with the terminator: reconstructing a whole-block trace -/


/-- The `then` block's **jump-free** body: `Dia.prog[13..16)` = `[AsmLabel "then", CALLVALUE, POP]`.
    This excludes the terminator's `PUSH join` (pc 16) and `JUMP` (pc 17) — the label push belongs to
    the JMP's plan, not to a body instruction. -/
def Dia.thenBody3 : List AsmInst := (Dia.prog.drop 13).take 3

theorem dia_thenBody3_at : asmBlockAt Dia.prog 13 Dia.thenBody3 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have : j < 3 := hj
  interval_cases j <;> rfl

theorem dia_thenBody3_nojump :
    ∀ j, (hj : j < Dia.thenBody3.length) → IsAsmJump (Dia.thenBody3.get ⟨j, hj⟩) = false := by
  decide

/-- The body run in isolation: `CALLVALUE` then `POP` cancel, so the stack returns to `asm.stack` and
    the state is `asm` at pc 3. A `rfl` — nothing here is an irreducible push. -/
theorem dia_thenBody3_run (asm : AsmState) :
    runAsm 3 Dia.o2pc Dia.thenBody3 { asm with pc := 0 }
      = AsmResult.AsmOK { asm with pc := 3 } := by cases asm; rfl

/-- Placed: the body runs the whole program from pc 13 to pc 16, leaving the state otherwise `asm`. -/
theorem dia_thenBody3_in_prog (asm : AsmState) (hpc : asm.pc = 13) :
    runAsm 3 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 16 } := by
  have hlift := dia_thenBody3_run { asm with pc := 0 }
  have hshift := runAsm_shift 3 Dia.o2pc Dia.prog Dia.thenBody3 13 dia_thenBody3_at
    dia_thenBody3_nojump { asm with pc := 0 } _ hlift
  have hid : ({ asm with pc := 13 + ({ asm with pc := 0 } : AsmState).pc } : AsmState) = asm := by
    show ({ asm with pc := 13 } : AsmState) = asm; rw [← hpc]
  rw [hid] at hshift
  simpa using hshift

/-! ### Body-then-terminator composition, one core plus one lemma per terminator kind -/


/-- **The body-then-continuation core.** A jump-free body placed at `base` runs from `base` to
    `base + body.length` (segment lift), and whatever the terminator does from there — `runAsm k` to any
    result `R` — the whole placed run does the same. Every terminator composition is an instance: the
    body half is shared, only the continuation `hcont` differs. -/
theorem runAsm_body_then (o2pc : AssocList Nat Nat) (prog body : List AsmInst) (base : Nat)
    (x bodyEnd : AsmState) (k : Nat) (R : AsmResult)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hcont : runAsm k o2pc prog { bodyEnd with pc := base + body.length } = R) :
    runAsm (body.length + k) o2pc prog { x with pc := base } = R := by
  have hshift := runAsm_shift body.length o2pc prog body base hblk hnj x bodyEnd hbodyrun
  rw [hx0] at hshift
  simp only [Nat.add_zero] at hshift
  rw [hbodyEndpc] at hshift
  rw [runAsm_append_ok hshift, hcont]

/-- Body then `STOP`: the block halts, in the body's end state advanced one pc. -/
theorem runAsm_body_then_stop (o2pc : AssocList Nat Nat) (prog body : List AsmInst) (base : Nat)
    (x bodyEnd : AsmState)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hstop1 : base + body.length < prog.length)
    (hstop : prog.get ⟨base + body.length, hstop1⟩ = AsmInst.AsmOp "STOP") :
    runAsm (body.length + 1) o2pc prog { x with pc := base }
      = AsmResult.AsmHalt (asmNext { bodyEnd with pc := base + body.length }) := by
  refine runAsm_body_then o2pc prog body base x bodyEnd 1 _ hblk hnj hx0 hbodyrun hbodyEndpc ?_
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm]
  rw [asmStep, dif_pos (by simpa using hstop1)]
  simp only [show (⟨({ bodyEnd with pc := base + body.length } : AsmState).pc, by simpa using hstop1⟩
    : Fin prog.length) = ⟨base + body.length, hstop1⟩ from rfl, hstop]

/-- Body then `RETURN`: the block halts, via the existing `runAsm_return`. Existential in the halt
    state — the `venomAsmTerminalRel` that pins it down is discharged separately by the walk. -/
theorem runAsm_body_then_return (o2pc : AssocList Nat Nat) (prog body : List AsmInst) (base : Nat)
    (x bodyEnd : AsmState) (off sz : bytes32) (rest : List bytes32)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hret1 : base + body.length < prog.length)
    (hret : prog.get ⟨base + body.length, hret1⟩ = AsmInst.AsmOp "RETURN")
    (hstk : bodyEnd.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ bodyEnd.memory.size) :
    ∃ as', runAsm (body.length + 1) o2pc prog { x with pc := base } = AsmResult.AsmHalt as' := by
  have hcont := runAsm_return (offsetToPc := o2pc) (prog := prog)
    (asMid := { bodyEnd with pc := base + body.length }) 0
    (by simpa using hret1) (by simpa using hret) (by simpa using hstk) (by simpa using hcov)
  exact ⟨_, runAsm_body_then o2pc prog body base x bodyEnd 1 _ hblk hnj hx0 hbodyrun hbodyEndpc hcont⟩

/-- Body then `REVERT`: the block reverts, via the existing `runAsm_revert`. -/
theorem runAsm_body_then_revert (o2pc : AssocList Nat Nat) (prog body : List AsmInst) (base : Nat)
    (x bodyEnd : AsmState) (off sz : bytes32) (rest : List bytes32)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hrev1 : base + body.length < prog.length)
    (hrev : prog.get ⟨base + body.length, hrev1⟩ = AsmInst.AsmOp "REVERT")
    (hstk : bodyEnd.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ bodyEnd.memory.size) :
    ∃ as', runAsm (body.length + 1) o2pc prog { x with pc := base } = AsmResult.AsmRevert as' := by
  have hcont := runAsm_revert (offsetToPc := o2pc) (prog := prog)
    (asMid := { bodyEnd with pc := base + body.length }) 0
    (by simpa using hrev1) (by simpa using hrev) (by simpa using hstk) (by simpa using hcov)
  exact ⟨_, runAsm_body_then o2pc prog body base x bodyEnd 1 _ hblk hnj hx0 hbodyrun hbodyEndpc hcont⟩

/-- Body then `INVALID`: the block faults. -/
theorem runAsm_body_then_invalid (o2pc : AssocList Nat Nat) (prog body : List AsmInst) (base : Nat)
    (x bodyEnd : AsmState)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hinv1 : base + body.length < prog.length)
    (hinv : prog.get ⟨base + body.length, hinv1⟩ = AsmInst.AsmOp "INVALID") :
    ∃ as', runAsm (body.length + 1) o2pc prog { x with pc := base } = AsmResult.AsmFault as' := by
  have hcont : runAsm 1 o2pc prog { bodyEnd with pc := base + body.length }
      = AsmResult.AsmFault { asmNext { bodyEnd with pc := base + body.length } with
          returndata := ByteArray.empty } := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runAsm]
    rw [asmStep, dif_pos (by simpa using hinv1)]
    simp only [show (⟨({ bodyEnd with pc := base + body.length } : AsmState).pc, by simpa using hinv1⟩
      : Fin prog.length) = ⟨base + body.length, hinv1⟩ from rfl, hinv]
  exact ⟨_, runAsm_body_then o2pc prog body base x bodyEnd 1 _ hblk hnj hx0 hbodyrun hbodyEndpc hcont⟩

/-- **Generic: a jump-free body composes with a resolved JMP terminator.**

If `body` is a jump-free block placed at `base`, running in isolation from pc 0 to `bodyEnd` (which,
being `body.length` jump-free steps, ends at pc `body.length`); and the terminator `PUSH target; JUMP`
sits at `base + body.length`, with `target` resolving through the label map to `off` and `off` mapping
to the successor pc `idx`; then the whole placed block runs from `base` to `idx`, in the body's end
state.

The general form of the reconstruction below: the segment lift for the body, the existing
`resolved_jump_sim` for the terminator, glued by `runAsm_append_ok`. Nothing depends on the particular
block. -/
theorem runAsm_body_then_jmp (o2pc : AssocList Nat Nat) (offsets : AssocList String Nat)
    (prog body : List AsmInst) (base : Nat) (x bodyEnd : AsmState)
    (target : String) (off idx : Nat)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hpush1 : base + body.length < prog.length)
    (hpush : prog.get ⟨base + body.length, hpush1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : base + body.length + 1 < prog.length)
    (hjump : prog.get ⟨base + body.length + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some idx) :
    runAsm (body.length + 2) o2pc prog { x with pc := base }
      = AsmResult.AsmOK { bodyEnd with pc := idx } := by
  refine runAsm_body_then o2pc prog body base x bodyEnd 2 _ hblk hnj hx0 hbodyrun hbodyEndpc ?_
  exact resolved_jump_sim (s := { bodyEnd with pc := base + body.length })
    (by simpa using hpush1) (by simpa using hpush) hoff_lk hoff
    (by simpa using hjump1) (by simpa using hjump) hidx_lk


/-- **Body then JNZ, branch taken.** The condition the body leaves on the stack is nonzero, so the
    resolved `PUSH ifNz; JUMPI` pair jumps to `ifNz`'s pc, consuming the condition. -/
theorem runAsm_body_then_jnz_taken (o2pc : AssocList Nat Nat) (offsets : AssocList String Nat)
    (prog body : List AsmInst) (base : Nat) (x bodyEnd : AsmState)
    (ifNz : String) (off idx : Nat) (cond : bytes32) (stk : List bytes32)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hstk : bodyEnd.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpush1 : base + body.length < prog.length)
    (hpush : prog.get ⟨base + body.length, hpush1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hjumpi1 : base + body.length + 1 < prog.length)
    (hjumpi : prog.get ⟨base + body.length + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some idx) :
    runAsm (body.length + 2) o2pc prog { x with pc := base }
      = AsmResult.AsmOK { bodyEnd with stack := stk, pc := idx } := by
  refine runAsm_body_then o2pc prog body base x bodyEnd 2 _ hblk hnj hx0 hbodyrun hbodyEndpc ?_
  exact resolved_jumpi_taken_sim (s := { bodyEnd with pc := base + body.length })
    (by simpa using hstk) hcond (by simpa using hpush1) (by simpa using hpush) hoff_lk hoff
    (by simpa using hjumpi1) (by simpa using hjumpi) hidx_lk

/-- **Body then JNZ, branch not taken.** The condition is zero: the `PUSH ifNz; JUMPI` pair falls
    through (consuming the condition), and the following `PUSH ifZ; JUMP` jumps to `ifZ`'s pc. Four
    terminator instructions. -/
theorem runAsm_body_then_jnz_nottaken (o2pc : AssocList Nat Nat) (offsets : AssocList String Nat)
    (prog body : List AsmInst) (base : Nat) (x bodyEnd : AsmState)
    (ifNz ifZ : String) (offN offZ idxZ : Nat) (stk : List bytes32)
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hstk : bodyEnd.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpush1 : base + body.length < prog.length)
    (hpushN : prog.get ⟨base + body.length, hpush1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hjumpi1 : base + body.length + 1 < prog.length)
    (hjumpi : prog.get ⟨base + body.length + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hpush2 : base + body.length + 2 < prog.length)
    (hpushZ : prog.get ⟨base + body.length + 2, hpush2⟩
      = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hjump1 : base + body.length + 2 + 1 < prog.length)
    (hjump : prog.get ⟨base + body.length + 2 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some idxZ) :
    runAsm (body.length + 4) o2pc prog { x with pc := base }
      = AsmResult.AsmOK { bodyEnd with stack := stk, pc := idxZ } := by
  refine runAsm_body_then o2pc prog body base x bodyEnd 4 _ hblk hnj hx0 hbodyrun hbodyEndpc ?_
  have hjumpi_step := resolved_jumpi_nottaken_sim (offsetToPc := o2pc) (prog := prog)
    (s := { bodyEnd with pc := base + body.length })
    (by simpa using hstk) (by simpa using hpush1) (by simpa using hpushN) hoffN_lk hoffN
    (by simpa using hjumpi1) (by simpa using hjumpi)
  have hjump_step := resolved_jump_sim
    (s := { bodyEnd with stack := stk, pc := base + body.length + 2 })
    (by simpa using hpush2) (by simpa using hpushZ) hoffZ_lk hoffZ
    (by simpa using hjump1) (by simpa using hjump) hidxZ_lk
  rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hjumpi_step, hjump_step]


/-- **`dia_hasm_then`, reconstructed through the recipe.** The jump-free body via the segment lift
    (`dia_thenBody3_in_prog`, no absolute-pc trace) composed with the terminator's `PUSH join; JUMP`
    pair via `runAsm_body_then_jmp` — the same conclusion the original hand-rolled proof reaches, but
    the composition is the general brick, fired here on a block the DFS reaches through a branch. -/
theorem dia_hasm_then_via_recipe {asm : AsmState} (hpc : asm.pc = 13) :
    runAsm 5 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 11 } := by
  have hid : ({ asm with pc := 13 } : AsmState) = asm := by rw [← hpc]
  have h := runAsm_body_then_jmp Dia.o2pc Dia.lo Dia.prog Dia.thenBody3 13
    { asm with pc := 0 } { asm with pc := 3 } "join" 17 11
    dia_thenBody3_at dia_thenBody3_nojump rfl
    (dia_thenBody3_run asm) rfl
    (by decide) rfl dia_lo_join (by decide) (by decide) rfl dia_o2pc_join
  rw [hid] at h
  exact h

/-! ## The recipe plugs into the walk: recipe → hrun → WalkStep -/


/-- **The recipe plugs into the walk's JMP step.**

`hstep_jmp_block_ws` produces a `WalkStep` from a whole-block `hrun` (plus the Venom-side relation
facts). This feeds that `hrun` from the recipe: the jump-free body via the segment lift, the JMP
terminator via `resolved_jump_sim`, composed by `runAsm_body_then_jmp`. So a block's `WalkStep` is
obtained with no absolute-pc asm trace — the asm run is assembled from the compiler's own layout, and
only the Venom-side simulation facts (`hrb`, `hrel`, the plan-state agreements, the well-founded
decrease) remain as inputs. -/
theorem WalkStep_jmp_via_recipe {fn : IrFunction} {ctx : VenomContext}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog body : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {x bodyEnd : AsmState} {psPostBody : PlanState}
    {N f' base : Nat} {target : String} {off : Nat}
    -- asm side: the recipe
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hpush1 : base + body.length < prog.length)
    (hpush : prog.get ⟨base + body.length, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : base + body.length + 1 < prog.length)
    (hjump : prog.get ⟨base + body.length + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf bb'.label))
    -- Venom side: the block simulation facts hstep_jmp_block consumes
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrel : venomAsmRel labelOffsets psPostBody s' { bodyEnd with pc := pcOf bb'.label })
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hle : body.length + 2 ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + (body.length + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb { x with pc := base } N
      (runBlock f' ctx bb s) := by
  have hrun := runAsm_body_then_jmp o2pc offsets prog body base x bodyEnd target off (pcOf bb'.label)
    hblk hnj hx0 hbodyrun hbodyEndpc hpush1 hpush hoff_lk hoff hjump1 hjump hidx_lk
  exact hstep_jmp_block_ws pcOf psOf wOf hrb hnh hrun hrel hstk hsp hfe hno rfl hle rfl hlk' hwdec

/-- **The asm half discharged on a real block.** For Dia's `then` — reached through a branch, base 13 —
    every asm-side input of `WalkStep_jmp_via_recipe` is filled from the compiler's own output, leaving
    exactly the Venom-side simulation facts as the remaining hypotheses. This is a witness that the asm
    half of the walk's JMP step is complete and non-vacuous; the residue is precisely the
    `genBlockSimulation` work. -/
theorem dia_then_WalkStep_asm_discharged
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {ctx : VenomContext} {s s' : VenomState} {psPostBody : PlanState} {N f' : Nat}
    (asm : AsmState)
    (hpcThen : pcOf "join" = 11)
    (hrb : runBlock f' ctx Dia.bThen s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrel : venomAsmRel Dia.lo psPostBody s' { { asm with pc := 3 } with pc := pcOf "join" })
    (hstk : psPostBody.stack = (psOf "join").stack)
    (hsp : psPostBody.spilled = (psOf "join").spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf "join").alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf "join").alloc.nextOffset)
    (hle : 3 + 2 ≤ N)
    (hlk' : lookupBlock s'.currentBb Dia.fn.blocks = some Dia.bJoin)
    (hbjoin : Dia.bJoin.label = "join")
    (hwdec : wOf "join" + (3 + 2) ≤ wOf Dia.bThen.label) :
    WalkStep Dia.fn pcOf psOf wOf Dia.lo Dia.o2pc Dia.prog Dia.bThen
      { asm with pc := 13 } N (runBlock f' ctx Dia.bThen s) := by
  have hbase : (13 : Nat) = 0 + 13 := rfl
  refine WalkStep_jmp_via_recipe (bb' := Dia.bJoin) (target := "join") (off := 17)
    (x := { asm with pc := 0 }) (bodyEnd := { asm with pc := 3 })
    (psPostBody := psPostBody) pcOf psOf wOf
    dia_thenBody3_at dia_thenBody3_nojump rfl (dia_thenBody3_run asm) rfl
    (by decide) rfl dia_lo_join (by decide) (by decide) rfl
    (by rw [hbjoin, hpcThen]; exact dia_o2pc_join)

    hrb hnh ?_ ?_ ?_ ?_ ?_ hle hlk' ?_
  · rw [hbjoin]; exact hrel
  · rw [hbjoin]; exact hstk
  · rw [hbjoin]; exact hsp
  · rw [hbjoin]; exact hfe
  · rw [hbjoin]; exact hno
  · rw [hbjoin]; exact hwdec

/-! ## …and into the halting steps: recipe halt-run → WalkStep -/


/-- **The recipe plugs into the walk's halting steps.** Given a block that halts on the Venom side
    (`hrb`), a body-then-halting-terminator asm run reaching `AsmHalt`/`AsmRevert`/`AsmFault` (from the
    recipe), and the Venom-side `venomAsmTerminalRel` on that exact end state, the `WalkStep` holds. The
    recipe's run is at step count `body.length + 1`; the walk's budget `N` is at least that, and a
    halted run stays halted, so it lifts (`runAsm_le_of_ne_ok`). -/
theorem WalkStep_halt_of_run {fn pcOf psOf wOf labelOffsets o2pc prog bb asm N f' ctx}
    {s s' : VenomState} {haltAsm : AsmState} {n : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt s')
    (hrun : runAsm n o2pc prog asm = AsmResult.AsmHalt haltAsm)
    (hle : n ≤ N)
    (hrel : venomAsmTerminalRel s' haltAsm) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb asm N (runBlock f' ctx bb s) := by
  rw [hrb]
  refine ⟨haltAsm, ?_, hrel⟩
  exact runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun

theorem WalkStep_revert_of_run {fn pcOf psOf wOf labelOffsets o2pc prog bb asm N f' ctx}
    {s s' : VenomState} {rvAsm : AsmState} {n : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.Abort AbortType.RevertAbort s')
    (hrun : runAsm n o2pc prog asm = AsmResult.AsmRevert rvAsm)
    (hle : n ≤ N)
    (hrel : venomAsmTerminalRel s' rvAsm) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb asm N (runBlock f' ctx bb s) := by
  rw [hrb]
  refine ⟨rvAsm, ?_, hrel⟩
  exact runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun

theorem WalkStep_fault_of_run {fn pcOf psOf wOf labelOffsets o2pc prog bb asm N f' ctx}
    {s s' : VenomState} {fltAsm : AsmState} {n : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.Abort AbortType.ExHaltAbort s')
    (hrun : runAsm n o2pc prog asm = AsmResult.AsmFault fltAsm)
    (hle : n ≤ N)
    (hrel : venomAsmTerminalRel s' fltAsm) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb asm N (runBlock f' ctx bb s) := by
  rw [hrb]
  refine ⟨fltAsm, ?_, hrel⟩
  exact runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun

/-! ## The walk relations ignore the asm pc — so the Venom-side input is program-position-free -/


/-- `venomAsmTerminalRel` ignores the asm pc — it constrains only accounts/transient/returndata/logs. -/
theorem venomAsmTerminalRel_setPc (vs : VenomState) (as : AsmState) (p : Nat) :
    venomAsmTerminalRel vs { as with pc := p } = venomAsmTerminalRel vs as := rfl

/-- `asmNext` only advances the pc, so it leaves the terminal relation unchanged. -/
theorem venomAsmTerminalRel_asmNext (vs : VenomState) (as : AsmState) :
    venomAsmTerminalRel vs (asmNext as) = venomAsmTerminalRel vs as := rfl

/-- And it leaves `venomAsmRel` unchanged too — `asmNext` touches nothing the relation reads. -/
theorem venomAsmRel_asmNext (lo : AssocList String Nat) (ps : PlanState) (vs : VenomState)
    (as : AsmState) :
    venomAsmRel lo ps vs (asmNext as) = venomAsmRel lo ps vs as := rfl

/-- **The JMP walk bridge with a pc-free Venom relation.** Same as `WalkStep_jmp_via_recipe`, but the
    Venom-side `hrel` is stated on the plain body-end state `bodyEnd`, not on the displaced
    `{bodyEnd with pc := pcOf bb'.label}`. Since `venomAsmRel` ignores the pc, the two are interchangeable
    — and this is the form a `genBlockSimulation` produces, which knows the block's stack and memory but
    not where the block sits in the program. -/
theorem WalkStep_jmp_via_recipe_pcfree {fn : IrFunction} {ctx : VenomContext}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog body : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {x bodyEnd : AsmState} {psPostBody : PlanState}
    {N f' base : Nat} {target : String} {off : Nat}
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hpush1 : base + body.length < prog.length)
    (hpush : prog.get ⟨base + body.length, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : base + body.length + 1 < prog.length)
    (hjump : prog.get ⟨base + body.length + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf bb'.label))
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrel : venomAsmRel labelOffsets psPostBody s' bodyEnd)
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hle : body.length + 2 ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + (body.length + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb { x with pc := base } N
      (runBlock f' ctx bb s) :=
  WalkStep_jmp_via_recipe pcOf psOf wOf hblk hnj hx0 hbodyrun hbodyEndpc hpush1 hpush hoff_lk hoff
    hjump1 hjump hidx_lk hrb hnh (venomAsmRel_setPc hrel) hstk hsp hfe hno hle hlk' hwdec

/-! ## JNZ walk bridges — the same generic hstep, fed the branching recipe run -/


/-- **The JNZ-taken walk step from the recipe.** `hstep_jmp_block_ws` is terminator-agnostic — its
    OK-continuing conclusion needs only `runBlock = OK s'`, the successor block, the whole-block asm
    run, and the relation; nothing about the terminator being a `JMP`. So the JNZ recipe's run
    (`runAsm_body_then_jnz_taken`, condition nonzero → jumps to `ifNz`) feeds the same hstep. The
    Venom relation is taken position-free (`venomAsmRel_setPc`). -/
theorem WalkStep_jnz_taken_via_recipe {fn : IrFunction} {ctx : VenomContext}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog body : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {x bodyEnd : AsmState} {psPostBody : PlanState}
    {N f' base : Nat} {ifNz : String} {off : Nat} {cond : bytes32} {stk : List bytes32}
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hstk_c : bodyEnd.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpush1 : base + body.length < prog.length)
    (hpush : prog.get ⟨base + body.length, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hjumpi1 : base + body.length + 1 < prog.length)
    (hjumpi : prog.get ⟨base + body.length + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf bb'.label))
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrel : venomAsmRel labelOffsets psPostBody s' { bodyEnd with stack := stk })
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hle : body.length + 2 ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + (body.length + 2) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb { x with pc := base } N
      (runBlock f' ctx bb s) := by
  have hrun := runAsm_body_then_jnz_taken o2pc offsets prog body base x bodyEnd ifNz off
    (pcOf bb'.label) cond stk hblk hnj hx0 hbodyrun hbodyEndpc hstk_c hcond hpush1 hpush hoff_lk
    hoff hjumpi1 hjumpi hidx_lk
  exact hstep_jmp_block_ws pcOf psOf wOf hrb hnh hrun (venomAsmRel_setPc hrel) hstk hsp hfe hno
    rfl hle rfl hlk' hwdec

/-- **The JNZ-not-taken walk step from the recipe.** Condition zero: the JUMPI falls through and the
    following `PUSH ifZ; JUMP` jumps to `ifZ`. Same generic hstep, fed the four-instruction not-taken
    run. -/
theorem WalkStep_jnz_nottaken_via_recipe {fn : IrFunction} {ctx : VenomContext}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog body : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {x bodyEnd : AsmState} {psPostBody : PlanState}
    {N f' base : Nat} {ifNz ifZ : String} {offN offZ : Nat} {stk : List bytes32}
    (hblk : asmBlockAt prog base body)
    (hnj : ∀ j, (hj : j < body.length) → IsAsmJump (body.get ⟨j, hj⟩) = false)
    (hx0 : x.pc = 0)
    (hbodyrun : runAsm body.length o2pc body x = AsmResult.AsmOK bodyEnd)
    (hbodyEndpc : bodyEnd.pc = body.length)
    (hstk_c : bodyEnd.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpush1 : base + body.length < prog.length)
    (hpushN : prog.get ⟨base + body.length, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hjumpi1 : base + body.length + 1 < prog.length)
    (hjumpi : prog.get ⟨base + body.length + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hpush2 : base + body.length + 2 < prog.length)
    (hpushZ : prog.get ⟨base + body.length + 2, hpush2⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hjump1 : base + body.length + 2 + 1 < prog.length)
    (hjump : prog.get ⟨base + body.length + 2 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf bb'.label))
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrel : venomAsmRel labelOffsets psPostBody s' { bodyEnd with stack := stk })
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hle : body.length + 4 ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + (body.length + 4) ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets o2pc prog bb { x with pc := base } N
      (runBlock f' ctx bb s) := by
  have hrun := runAsm_body_then_jnz_nottaken o2pc offsets prog body base x bodyEnd ifNz ifZ offN
    offZ (pcOf bb'.label) stk hblk hnj hx0 hbodyrun hbodyEndpc hstk_c hpush1 hpushN hoffN_lk hoffN
    hjumpi1 hjumpi hpush2 hpushZ hoffZ_lk hoffZ hjump1 hjump hidxZ_lk
  exact hstep_jmp_block_ws pcOf psOf wOf hrb hnh hrun (venomAsmRel_setPc hrel) hstk hsp hfe hno
    rfl hle rfl hlk' hwdec

/-! ## The recipe supplies codegen_correct's hbsim arms directly -/


/-- **The recipe's block run supplies `codegen_correct`'s `hbsim` OK-continuing arm.**

`hbsim`'s continuing arm is `∃ asm' N', runAsm N prog asm = runAsm N' prog asm' ∧ Entry s' asm' N'` — a
walk-continuation form. A block whose asm runs to `AsmOK asm'` in `blockLen` steps supplies it directly:
`runAsm_append_ok` turns `runAsm blockLen prog asm = AsmOK asm'` into `runAsm (blockLen + N') prog asm =
runAsm N' prog asm'`, so with the budget `N = blockLen + N'` the walk resumes from `asm'`. The successor
invariant `Entry s' asm' N'` is the input the block simulation provides. -/
theorem hbsim_OK_continue_of_run {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm asm' : AsmState} {s' : VenomState}
    {blockLen N' : Nat}
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmOK asm')
    (hEntry : Entry s' asm' N') :
    ∃ asm'' N'', runAsm (blockLen + N') o2pc prog asm = runAsm N'' o2pc prog asm''
      ∧ Entry s' asm'' N'' :=
  ⟨asm', N', runAsm_append_ok hrun, hEntry⟩

/-- The halting arms: a block that halts/reverts/faults in `blockLen ≤ N` steps supplies the terminal
    arm at the walk's budget `N` (a terminal run is absorbing under extra fuel). -/
theorem hbsim_halt_of_run {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm haltAsm : AsmState}
    {s' : VenomState} {blockLen N : Nat}
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmHalt haltAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' haltAsm) :
    ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm' :=
  ⟨haltAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

theorem hbsim_revert_of_run {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm rvAsm : AsmState}
    {s' : VenomState} {blockLen N : Nat}
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmRevert rvAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' rvAsm) :
    ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm' :=
  ⟨rvAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

theorem hbsim_fault_of_run {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm fltAsm : AsmState}
    {s' : VenomState} {blockLen N : Nat}
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmFault fltAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' fltAsm) :
    ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm' :=
  ⟨fltAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

/-- **Non-vacuous on the compiler's own output.** Dia's `then` block runs (via the recipe reconstruction
    `dia_hasm_then_via_recipe`) to `AsmOK {asm with pc := 11}` in 5 steps, so for any successor invariant
    `Entry` holding at the join, the `hbsim` OK-continuing arm holds — the walk resumes at the join. -/
theorem dia_then_hbsim_continue {Entry : VenomState → AsmState → Nat → Prop} {s' : VenomState}
    {asm : AsmState} {N' : Nat} (hpc : asm.pc = 13)
    (hEntry : Entry s' { asm with pc := 11 } N') :
    ∃ asm'' N'', runAsm (5 + N') Dia.o2pc Dia.prog asm = runAsm N'' Dia.o2pc Dia.prog asm''
      ∧ Entry s' asm'' N'' :=
  hbsim_OK_continue_of_run (dia_hasm_then_via_recipe hpc) hEntry

/-! ## The full hbsim match, supplied from the recipe (with the correspondence proof) -/


/-- The exact `hbsim` match shape `codegen_correct` requires, abbreviated. -/
def HbsimMatch (Entry : VenomState → AsmState → Nat → Prop) (o2pc : AssocList Nat Nat)
    (prog : List AsmInst) (asm : AsmState) (N : Nat) (r : ExecResult) : Prop :=
  match r with
  | ExecResult.OK s' =>
      if s'.halted then
        ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      else
        ∃ asm' N', runAsm N o2pc prog asm = runAsm N' o2pc prog asm' ∧ Entry s' asm' N'
  | ExecResult.Halt s' =>
      ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.RevertAbort s' =>
      ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.ExHaltAbort s' =>
      ∃ asm', runAsm N o2pc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
  | _ => True

/-- **A continuing block supplies the whole `hbsim` match.** Given the block continues on the Venom side
    (`runBlock = OK s'`, not halted), its asm runs to `AsmOK asm'` at the budget's head, and the successor
    invariant holds, the entire `HbsimMatch` holds. This is the shape `codegen_correct`'s `hbsim` argument
    is, produced directly from the recipe. -/
theorem HbsimMatch_of_OK_continue {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm asm' : AsmState}
    {f' blockLen N' : Nat} {ctx : VenomContext} {bb : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s') (hnh : s'.halted = false)
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmOK asm')
    (hEntry : Entry s' asm' N') :
    HbsimMatch Entry o2pc prog asm (blockLen + N') (runBlock f' ctx bb s) := by
  rw [hrb]; simp only [HbsimMatch, hnh, Bool.false_eq_true, if_false]
  exact ⟨asm', N', runAsm_append_ok hrun, hEntry⟩

/-- A halting block supplies the whole match: `runBlock = Halt s'`, asm halts within budget. -/
theorem HbsimMatch_of_halt {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm haltAsm : AsmState}
    {f' blockLen N : Nat} {ctx : VenomContext} {bb : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt s')
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmHalt haltAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' haltAsm) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) := by
  rw [hrb]; exact ⟨haltAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

theorem HbsimMatch_of_revert {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm rvAsm : AsmState}
    {f' blockLen N : Nat} {ctx : VenomContext} {bb : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.Abort AbortType.RevertAbort s')
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmRevert rvAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' rvAsm) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) := by
  rw [hrb]; exact ⟨rvAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

theorem HbsimMatch_of_fault {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm fltAsm : AsmState}
    {f' blockLen N : Nat} {ctx : VenomContext} {bb : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.Abort AbortType.ExHaltAbort s')
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmFault fltAsm) (hle : blockLen ≤ N)
    (hrel : venomAsmTerminalRel s' fltAsm) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) := by
  rw [hrb]; exact ⟨fltAsm, runAsm_le_of_ne_ok (by intro s hs; cases hs) hle hrun, hrel⟩

/-- **CORRESPONDENCE: `HbsimMatch` IS `codegen_correct`'s hbsim match.** The exact inline match from
    `codegen_correct` (with `prog`/`o2pc` = the resolved whole-function plan) is discharged from
    `HbsimMatch` by `exact` (definitional equality). So the suppliers above produce the real `hbsim`
    hypothesis, not a private mirror of it. -/
theorem HbsimMatch_is_hbsim {ops : List StackOp} {asm : AsmState} {N : Nat}
    {Entry : VenomState → AsmState → Nat → Prop} {r : ExecResult}
    (h : HbsimMatch Entry (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm N r) :
    (match r with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
             = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ asm' N', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
             = runAsm N' (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm' ∧ Entry s' asm' N'
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
           = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
           = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
           = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  unfold HbsimMatch at h
  cases r with
  | OK s' => exact h
  | Halt s' => exact h
  | Abort a s' => cases a <;> exact h
  | IntRet _ _ => exact h
  | Error _ => exact h

/-- **Non-vacuous full match on the compiler's own output.** Dia's `then` (a continuing JMP block) supplies
    the whole `hbsim` match — `runBlock = OK s'` non-halting, asm run via the recipe reconstruction. -/
theorem dia_then_HbsimMatch {Entry : VenomState → AsmState → Nat → Prop}
    {f' N' : Nat} {ctx : VenomContext} {s s' : VenomState} {asm : AsmState}
    (hrb : runBlock f' ctx Dia.bThen s = ExecResult.OK s') (hnh : s'.halted = false)
    (hpc : asm.pc = 13) (hEntry : Entry s' { asm with pc := 11 } N') :
    HbsimMatch Entry Dia.o2pc Dia.prog asm (5 + N') (runBlock f' ctx Dia.bThen s) :=
  HbsimMatch_of_OK_continue hrb hnh (dia_hasm_then_via_recipe hpc) hEntry

/-! ## A halting block's hbsim from venomAsmRel — the terminal relation is derived, not assumed -/


/-- **STOP's terminal relation follows from `venomAsmRel` at the body-end.** No assumed terminal
    relation: the block simulation's `venomAsmRel` (which the body-fold produces) already gives the four
    observable equalities, and neither `haltState` (Venom) nor `asmNext` (asm) disturbs them. -/
theorem terminalRel_stop_of_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} (h : venomAsmRel lo ps vs as) :
    venomAsmTerminalRel (haltState vs) (asmNext as) := by
  refine venomAsmTerminalRel_haltState ?_
  rw [venomAsmTerminalRel_asmNext]
  exact venomAsmRel_terminal lo ps vs as h

/-- **INVALID's terminal relation** similarly. Both sides set returndata to empty, so the returndata
    conjunct is `empty = empty`; the other three come from `venomAsmRel`. -/
theorem terminalRel_invalid_of_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} (h : venomAsmRel lo ps vs as) :
    venomAsmTerminalRel (haltState (setReturndata ByteArray.empty vs))
      { asmNext as with returndata := ByteArray.empty } := by
  obtain ⟨_, _, _, hacc, htr, _, hlog, _, _, _, _, _⟩ := h
  exact ⟨hacc, htr, rfl, hlog⟩

/-- **A STOP block's full `hbsim` match from `venomAsmRel` at the body-end** — nothing about the terminal
    state assumed. Combines the STOP recipe run (`AsmHalt (asmNext …)`) with `terminalRel_stop_of_rel`.
    The Venom-side input is now just the body simulation's relation. -/
theorem HbsimMatch_stop_of_rel {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asBodyEnd : AsmState} {f' blockLen N : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s vsBodyEnd : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt (haltState vsBodyEnd))
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmHalt (asmNext asBodyEnd)) (hle : blockLen ≤ N)
    (hrel : venomAsmRel lo ps vsBodyEnd asBodyEnd) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) :=
  HbsimMatch_of_halt hrb hrun hle (terminalRel_stop_of_rel hrel)

/-- An INVALID block's full match from `venomAsmRel`, likewise (fault arm). -/
theorem HbsimMatch_invalid_of_rel {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asBodyEnd : AsmState} {f' blockLen N : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s vsBodyEnd : VenomState}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vsBodyEnd)))
    (hrun : runAsm blockLen o2pc prog asm
      = AsmResult.AsmFault { asmNext asBodyEnd with returndata := ByteArray.empty }) (hle : blockLen ≤ N)
    (hrel : venomAsmRel lo ps vsBodyEnd asBodyEnd) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) :=
  HbsimMatch_of_fault hrb hrun hle (terminalRel_invalid_of_rel hrel)

/-! ## RETURN/REVERT terminal relation from venomAsmRel + memory-safety -/


/-- **RETURN's terminal relation from `venomAsmRel` + memory-safety.** Both sides set returndata to
    `memory.readWithPadding off sz` on their own memory; under `venomAsmRel`'s `memoryRel` and the
    read region below the spill area (`off + sz ≤ fnEom`, the honest memory-safety input), the two
    reads agree (`memoryRel_readWithPadding_slice`), and the other three observables come from the
    relation. -/
theorem terminalRel_return_of_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {off sz : Nat} {rest : List bytes32}
    (h : venomAsmRel lo ps vs as)
    (hbelow : off + sz ≤ ps.alloc.fnEom) (hlen : sz < USize.size) :
    venomAsmTerminalRel
      (haltState (setReturndata (readMemory off sz vs) vs))
      { as with stack := rest, returndata := as.memory.readWithPadding off sz } := by
  obtain ⟨_, _, hmem, hacc, htr, _, hlog, _, _, _, _, _⟩ := h
  exact ⟨hacc, htr, (memoryRel_readWithPadding_slice hmem hbelow hlen).symm, hlog⟩

/-- REVERT is the same shape (revertState only sets `halted`; the asm side reverts). -/
theorem terminalRel_revert_of_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {off sz : Nat} {rest : List bytes32}
    (h : venomAsmRel lo ps vs as)
    (hbelow : off + sz ≤ ps.alloc.fnEom) (hlen : sz < USize.size) :
    venomAsmTerminalRel
      (revertState (setReturndata (readMemory off sz vs) vs))
      { as with stack := rest, returndata := as.memory.readWithPadding off sz } := by
  obtain ⟨_, _, hmem, hacc, htr, _, hlog, _, _, _, _, _⟩ := h
  exact ⟨hacc, htr, (memoryRel_readWithPadding_slice hmem hbelow hlen).symm, hlog⟩

/-- RETURN block's full `hbsim` match from `venomAsmRel` + memory-safety. -/
theorem HbsimMatch_return_of_rel {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asBodyEnd : AsmState} {f' blockLen N off sz : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb : BasicBlock} {s vsBodyEnd : VenomState}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Halt (haltState (setReturndata (readMemory off sz vsBodyEnd) vsBodyEnd)))
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmHalt
      { asBodyEnd with stack := rest, returndata := asBodyEnd.memory.readWithPadding off sz })
    (hle : blockLen ≤ N)
    (hrel : venomAsmRel lo ps vsBodyEnd asBodyEnd)
    (hbelow : off + sz ≤ ps.alloc.fnEom) (hlen : sz < USize.size) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) :=
  HbsimMatch_of_halt hrb hrun hle (terminalRel_return_of_rel hrel hbelow hlen)

/-- REVERT block's full match, likewise (revert arm). -/
theorem HbsimMatch_revert_of_rel {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asBodyEnd : AsmState} {f' blockLen N off sz : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb : BasicBlock} {s vsBodyEnd : VenomState}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata (readMemory off sz vsBodyEnd) vsBodyEnd)))
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmRevert
      { asBodyEnd with stack := rest, returndata := asBodyEnd.memory.readWithPadding off sz })
    (hle : blockLen ≤ N)
    (hrel : venomAsmRel lo ps vsBodyEnd asBodyEnd)
    (hbelow : off + sz ≤ ps.alloc.fnEom) (hlen : sz < USize.size) :
    HbsimMatch Entry o2pc prog asm N (runBlock f' ctx bb s) :=
  HbsimMatch_of_revert hrb hrun hle (terminalRel_revert_of_rel hrel hbelow hlen)


end EvmYul.Venom.Hol.Codegen

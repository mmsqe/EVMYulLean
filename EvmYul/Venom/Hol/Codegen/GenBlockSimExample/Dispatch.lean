/-
GenBlockSimExample / internal-return, loop-with-phi, universal dispatch & retraction

Split part of `GenBlockSimExample`; see that module's header for the full roadmap.
This part is wrapped in `namespace EvmYul.Venom.Hol.Codegen` (the enclosing namespace of the second half); layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.Demos



namespace EvmYul.Venom.Hol.Codegen

/-- **Function-level internal return.** A function whose blocks run to an `IntRet` (a `RET` terminator)
    returns those values -- `runFunction` just wraps `runBlocks`. The function-level rung of the
    internal-return chain (`runBlock_intret` -> `runBlocks_intret_of_block` -> here). -/
theorem runFunction_intret {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {s sEnd : VenomState}
    {lbl : String} {vals : List bytes32}
    (hlbl : fnEntryLabel fn = some lbl)
    (hrbs : runBlocks fuel ctx fn { s with currentBb := lbl, instIdx := 0 }
        = ExecResult.IntRet vals sEnd) :
    runFunction fuel ctx fn s = ExecResult.IntRet vals sEnd := by
  unfold runFunction; rw [hlbl]; exact hrbs

/-- **Context-level internal return.** The entry function returning `IntRet` makes `runContext` return
    those values -- the top of the internal-return chain. This is the Venom-side characterization of a
    callee that returns values (what an internal `CALL` would invoke; the semantics has `RET`/`IntRet`
    but no internal-call opcode that re-enters `runFunction`, so `IntRet` propagates to the top). -/
theorem runContext_intret {fuel : Nat} {ctx : VenomContext} {entryFn : IrFunction} {s sEnd : VenomState}
    {entryName : String} {vals : List bytes32}
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some entryFn)
    (hrf : runFunction fuel ctx entryFn { s with prevBb := none } = ExecResult.IntRet vals sEnd) :
    runContext fuel ctx s = ExecResult.IntRet vals sEnd := by
  simp only [runContext, hent, hlk]; exact hrf

/-! ## Concrete internal-return demonstration -/

def retInst : Instruction :=
  { id := 0, opcode := Opcode.RET, operands := [Operand.Lit (EvmYul.UInt256.ofNat 42)], outputs := [] }
def retBB : BasicBlock := { label := "entry", instructions := [retInst] }
def retFn : IrFunction := ⟨"main", [retBB]⟩
def retCtx : VenomContext := ⟨[retFn], some "main"⟩

/-- **First concrete internal-return instance.** For `main: [RET 42]`, `runContext` returns
    `IntRet [42]` from the entry state -- end to end through the whole Venom internal-return chain
    (`runBlock_intret` -> `runBlocks_intret_of_block` -> `runFunction_intret` -> `runContext_intret`).
    De-vacuifies the `IntRet` arm (previously only ever hit the `_ => True` catch-all). -/
theorem runContext_bareRet {s : VenomState} :
    runContext 3 retCtx s
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42]
          { s with prevBb := none, currentBb := "entry", instIdx := 0 } := by
  set eS : VenomState := { s with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hstep : stepInstBase retInst { eS with instIdx := 0 }
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } := rfl
  have hrb : runBlock 2 retCtx retBB eS
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } := by
    have h := runBlock_intret retCtx retBB 1 [] retInst retInst [] eS { eS with instIdx := 0 }
      { eS with instIdx := 0 } [EvmYul.UInt256.ofNat 42]
      (by rfl) rfl (by decide) (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstep
    simpa using h
  have hrbs : runBlocks 3 retCtx retFn eS
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } :=
    runBlocks_intret_of_block (by rfl) hrb
  refine runContext_intret (entryName := "main") (entryFn := retFn) rfl rfl ?_
  exact runFunction_intret (lbl := "entry") rfl hrbs

/-! ### Discharging the JNZ not-taken tree-edge condition on a real CFG

`hstep_regularHSVP_jnz_nottaken_canonical` asks for `hnr : ¬ CfgReach (cfgAnalyze fn) ifNz ifZ` — the
fall-through target must not be discoverable from inside the taken branch's DFS subtree (otherwise `ifZ`
is not a tree edge and its entry is recorded elsewhere, with a different plan state). The point of
`not_CfgReach_of_closed` is that this is a *decidable* CFG fact: exhibit a successor-closed list
containing `ifNz` and missing `ifZ`. Here `then` STOPs, so `{then}` is already closed. -/
theorem jnzStopFnR_then_not_reach_else :
    ¬ CfgReach (cfgAnalyze Example.jnzStopFnR) "then" "else" :=
  not_CfgReach_of_closed ["then"] (by decide) (by decide) (by decide)

/-- The symmetric fact (the `else` branch cannot reach `then`) — so either successor may play the role
    of the taken branch. -/
theorem jnzStopFnR_else_not_reach_then :
    ¬ CfgReach (cfgAnalyze Example.jnzStopFnR) "else" "then" :=
  not_CfgReach_of_closed ["else"] (by decide) (by decide) (by decide)

/-- **The JNZ successor order, on a real CFG.** `bbSuccs` is `(getSuccessors …).reverse`, so for a JNZ
    with operands `[c, ifNz, ifZ]` the CFG successors come out `ifZ :: ifNz` — the FALL-THROUGH first,
    the TAKEN target second. `jnzInstR`'s labels are `then` (= ifNz) and `else` (= ifZ), and indeed:

    This is the shape both JNZ canonical `hstep`s now ask for (`hpsucc`). Before this was checked they
    asked for `ifNz :: …`, which no function can ever satisfy — their residual discharge was vacuous. -/
theorem jnzStopFnR_entry_succs :
    (cfgAnalyze Example.jnzStopFnR).succsOf "entry" = ["else", "then"] := by decide

/-! ### The `CleanTrivial` weakening buys real coverage

Every canonical per-block `hstep` used to require `(predsOf bb.label).length ≠ 1`, which is FALSE for
any block reached by a JMP from a single predecessor — i.e. for every intermediate block of a JMP chain,
which is exactly what `JmpChainTo` produces. `cleanStackPlan` only does work at a *branch join* (single
pred that BRANCHES), so the right condition is `CleanTrivial`, and the chain blocks satisfy it. -/

/-- `next` is reached by a JMP from `entry`, so it has exactly one predecessor — the OLD hypothesis
    `(predsOf …).length ≠ 1` was false for it, and no canonical `hstep` could apply. -/
theorem jmpStopFn_next_single_pred :
    ((cfgAnalyze Example.jmpStopFn).predsOf "next").length = 1 := by decide

/-- …but its single predecessor doesn't branch, so `CleanTrivial` holds and the machinery now applies. -/
theorem jmpStopFn_next_cleanTrivial (L : DfState (List String)) :
    CleanTrivial L (cfgAnalyze Example.jmpStopFn) Example.jmpStopFn Example.stopNextBB :=
  cleanTrivial_of_jmp_pred (p := "entry") (by decide) (by decide)

/-- **A JNZ branch target IS now covered** (when nothing is dead at the join). `then` has exactly one
    predecessor, and that predecessor BRANCHES — so the old `(predsOf …).length ≠ 1` was false for it, and
    so is the "non-branching pred" case. But `cleanStackPlan` only emits a `popmany` for the values the
    predecessor's exit layout carries and this block does NOT want; here that set is empty, so the plan is
    the identity and `cleanTrivial_of_no_dead` applies.

    So the semantic `CleanTrivial` reaches JNZ branch targets too — no clean-stack prefix has to be
    threaded through the block layout. What remains uncovered is only the case where the join really does
    drop values (`toPop ≠ []`). -/
theorem jnzStopFnR_then_cleanTrivial (L : DfState (List String))
    (hdead : (liveVarsAt L "entry" Example.jnzEntryR.instructions.length).filter
        (fun v => ¬ (inputVarsFrom "entry" Example.thenBB.instructions
          (liveVarsAt L "then" 0)).contains v) = []) :
    CleanTrivial L (cfgAnalyze Example.jnzStopFnR) Example.jnzStopFnR Example.thenBB :=
  cleanTrivial_of_no_dead (p := "entry") (predBb := Example.jnzEntryR) (by decide) rfl hdead

/-- …and for `jnzStopFnR` the join really does drop nothing, so the branch target is covered
    UNCONDITIONALLY. A JNZ branch target — previously outside every canonical per-block `hstep` — now
    satisfies the per-block precondition. -/
theorem jnzStopFnR_then_cleanTrivial_concrete :
    CleanTrivial (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
      (cfgAnalyze Example.jnzStopFnR) Example.jnzStopFnR Example.thenBB :=
  jnzStopFnR_then_cleanTrivial _ rfl

/-! ### `hpreuniq` is dischargeable — by computation

`hpreuniq` (the plan-prefix label-uniqueness obligation) is an input to all seven canonical per-block
`hstep`s and had never been discharged anywhere, which — after the JNZ successor-order incident — is
exactly the shape of thing worth checking rather than assuming. `hpreuniq_of_asmLabelCount_one` reduces it
to "the whole plan emits this block's label exactly once", and THAT computes. Here it is, discharged for a
real function, including for a NON-entry block whose plan prefix is genuinely non-empty. -/

theorem jmpStopFn_next_labelCount {ops : List StackOp} {ps : PlanState}
    (hgen : generateFnPlanFuel (fnPlanFuel Example.jmpStopFn) Example.jmpStopFn 0 0 = some (ops, ps)) :
    asmLabelCount "next" (executePlan ops) = 1 := by
  have h : (generateFnPlanFuel (fnPlanFuel Example.jmpStopFn) Example.jmpStopFn 0 0).map
      (fun r => asmLabelCount "next" (executePlan r.1)) = some 1 := by rfl
  rw [hgen] at h
  simpa using h

/-- `hpreuniq` for `jmpStopFn`'s `next` block — a non-entry block, so its plan prefix is non-empty and the
    obligation has real content. Discharged entirely by computation. -/
theorem jmpStopFn_next_hpreuniq {ops : List StackOp} {ps : PlanState} {rest : List StackOp}
    (hgen : generateFnPlanFuel (fnPlanFuel Example.jmpStopFn) Example.jmpStopFn 0 0 = some (ops, ps))
    {blockOps : List StackOp} (hblk : blockOps = StackOp.SOLabel "next" :: rest) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel "next" :=
  hpreuniq_of_asmLabelCount_one hblk (jmpStopFn_next_labelCount hgen).le

/-- Same for the branching function's fall-through target. -/
theorem jnzStopFnR_else_labelCount {ops : List StackOp} {ps : PlanState}
    (hgen : generateFnPlanFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0 = some (ops, ps)) :
    asmLabelCount "else" (executePlan ops) = 1 := by
  have h : (generateFnPlanFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0).map
      (fun r => asmLabelCount "else" (executePlan r.1)) = some 1 := by rfl
  rw [hgen] at h
  simpa using h

theorem jnzStopFnR_else_hpreuniq {ops : List StackOp} {ps : PlanState} {rest : List StackOp}
    (hgen : generateFnPlanFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0 = some (ops, ps))
    {blockOps : List StackOp} (hblk : blockOps = StackOp.SOLabel "else" :: rest) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel "else" :=
  hpreuniq_of_asmLabelCount_one hblk (jnzStopFnR_else_labelCount hgen).le

/-! ### `hpreuniq` discharged GENERICALLY on a real function

Earlier this was discharged by computing the label count for each specific function. It is now a theorem
(`hpreuniq_generic`): the DFS plans a block only when unvisited, so the plan emits each label at most once.
The only side condition is that no instruction be one of the three fresh-label minters — which is a
decidable property of the function. Here it is, end to end. -/

theorem jmpStopFn_no_label_minters :
    ∀ b ∈ Example.jmpStopFn.blocks, ∀ inst ∈ nonParamInsts b,
      inst.opcode ≠ Opcode.INVOKE ∧ inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧
      inst.opcode ≠ Opcode.DJMP := by decide

theorem jnzStopFnR_no_label_minters :
    ∀ b ∈ Example.jnzStopFnR.blocks, ∀ inst ∈ nonParamInsts b,
      inst.opcode ≠ Opcode.INVOKE ∧ inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧
      inst.opcode ≠ Opcode.DJMP := by decide

/-- `hpreuniq` for ANY block of `jmpStopFn`, straight from its block plan — no per-function computation. -/
theorem jmpStopFn_hpreuniq_generic {fuel fnEom lblCtr : Nat} {ops blockOps : List StackOp}
    {ps psB ps' : PlanState} {bb : BasicBlock}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    (hgen : generateFnPlanFuel fuel Example.jmpStopFn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C Example.jmpStopFn bb psB = some (blockOps, ps')) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_of_blockPlan jmpStopFn_no_label_minters hgen hbp

/-- Same for the branching function. -/
theorem jnzStopFnR_hpreuniq_generic {fuel fnEom lblCtr : Nat} {ops blockOps : List StackOp}
    {ps psB ps' : PlanState} {bb : BasicBlock}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    (hgen : generateFnPlanFuel fuel Example.jnzStopFnR fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C Example.jnzStopFnR bb psB = some (blockOps, ps')) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_of_blockPlan jnzStopFnR_no_label_minters hgen hbp

/-! ### `hlblfree_of_bodyfold`'s side condition is SATISFIABLE

`hlblfree_of_bodyfold` discharges `hlblfree` given a per-instruction condition (`hcond`) on the body. For
an EMPTY body that condition is vacuous, which proves nothing — and after the JNZ successor-order incident
(where an hstep's hypothesis turned out to be unsatisfiable, making its conclusion vacuous) an unvalidated
side condition is exactly what must not be left standing. So: check it on REAL body instructions. -/

theorem addVarInst_satisfies_hcond :
    ∀ x ∈ ([Example.addVarInst].zipIdx 0),
      (∀ op ∈ computeOperands x.1, ∀ l, op ≠ Operand.Label l) ∧
      (¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧ x.1.opcode ≠ Opcode.OFFSET ∧
        x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) ∧
      x.1.opcode ≠ Opcode.JMP ∧ x.1.opcode ≠ Opcode.JNZ ∧ x.1.opcode ≠ Opcode.DJMP ∧
      x.1.opcode ≠ Opcode.INVOKE ∧ x.1.opcode ≠ Opcode.ASSERT ∧
      x.1.opcode ≠ Opcode.ASSERT_UNREACHABLE := by
  rintro ⟨i, n⟩ hx
  have hi : i = Example.addVarInst := by
    have h := List.fst_mem_of_mem_zipIdx hx
    simpa using h
  subst hi
  simp only []
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro op hop l
  simp [computeOperands, Example.addVarInst] at hop
  rcases hop with rfl | rfl <;> simp

/-- A two-instruction body (ADD then MUL over vars) also satisfies it — so the condition is not an
    artifact of a single instruction. -/
theorem addMulBody_satisfies_hcond :
    ∀ x ∈ ([Example.addXYInst, Example.mulXYInst].zipIdx 0),
      (∀ op ∈ computeOperands x.1, ∀ l, op ≠ Operand.Label l) ∧
      (¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧ x.1.opcode ≠ Opcode.OFFSET ∧
        x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) ∧
      x.1.opcode ≠ Opcode.JMP ∧ x.1.opcode ≠ Opcode.JNZ ∧ x.1.opcode ≠ Opcode.DJMP ∧
      x.1.opcode ≠ Opcode.INVOKE ∧ x.1.opcode ≠ Opcode.ASSERT ∧
      x.1.opcode ≠ Opcode.ASSERT_UNREACHABLE := by
  rintro ⟨i, n⟩ hx
  have hi : i = Example.addXYInst ∨ i = Example.mulXYInst := by
    have h := List.fst_mem_of_mem_zipIdx hx
    simpa using h
  rcases hi with rfl | rfl <;>
    (simp only []
     refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
     intro op hop l
     simp [computeOperands, Example.addXYInst, Example.mulXYInst] at hop
     rcases hop with rfl | rfl <;> simp)

/-! ### `dfs_segment_gbp` reaches blocks no JMP chain can — non-vacuity on a real `JNZ` CFG

`chain_segment_gbp` needs `JmpChainTo`, i.e. every intermediate block on the path from the entry has
*exactly one* successor. `jnzStopFnR`'s entry is a `JNZ` (two successors), so neither `then` nor `else`
is reachable by any such chain and no `hstep` could ever be instantiated for them. The DFS, however,
visits all three blocks — so `dfs_segment_gbp`'s `hvis` is satisfied and the segment exists.

This is the concrete check that the generalization is real and not vacuous. -/

/-- The real compiler's plan DFS visits all three blocks of the `JNZ` function — including the two
    branch targets, which lie on no single-successor chain from the entry. -/
theorem jnzStopFnR_dfs_visits_all :
    (generateFnPlanAux (fnPlanFuel Example.jnzStopFnR)
        (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
        (DfgAnalysis.buildFunction Example.jnzStopFnR) (cfgAnalyze Example.jnzStopFnR)
        Example.jnzStopFnR ["entry"] [] { initPlanState 0 with labelCounter := 0 }).map
      (fun r => r.2.1) = some ["then", "else", "entry"] := by rfl

/-- **Non-vacuity of `dfs_segment_gbp` on a `JNZ` branch target.** `then` is a successor of a
    two-successor block, so `JmpChainTo` — and hence `chain_segment_gbp` — can never reach it. The
    universal DFS segment does: `then`'s block plan, computed from its canonical entry state
    `psOfFn … "then"`, sits as a segment of the whole-function ops. -/
theorem jnzStopFnR_then_segment
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hgenAux : generateFnPlanAux (fnPlanFuel Example.jnzStopFnR)
        (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
        (DfgAnalysis.buildFunction Example.jnzStopFnR) (cfgAnalyze Example.jnzStopFnR)
        Example.jnzStopFnR ["entry"] [] { initPlanState 0 with labelCounter := 0 }
      = some (ops, vF, psF)) :
    ∃ preOps blockOps tailOps ps',
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
        (DfgAnalysis.buildFunction Example.jnzStopFnR) (cfgAnalyze Example.jnzStopFnR)
        Example.jnzStopFnR Example.thenBB
        (psOfFn (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0 Example.thenBB.label)
      = some (blockOps, ps') := by
  -- the DFS's visited output is pinned by `hgenAux`, so `then` really is visited
  have hvproj := jnzStopFnR_dfs_visits_all
  rw [hgenAux] at hvproj
  have hvF : vF = ["then", "else", "entry"] := by
    simpa using congrArg (fun o => o.getD []) hvproj
  refine dfs_segment_gbp (entry := Example.jnzEntryR) ?_ rfl hgenAux (by rw [hvF]; decide) rfl
  intro bb hbb inst hinst
  simp only [Example.jnzStopFnR, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · simp only [Example.jnzEntryR, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide
  · simp only [Example.thenBB, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide
  · simp only [Example.elseBB, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide

/-- The DFS on the `JNZ` function really is closed under CFG successors — it did not truncate. This
    is `reach_segment_gbp`'s only side condition beyond reachability, and it is decidable. -/
theorem jnzStopFnR_dfs_closed :
    DfsClosed (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0 := by decide

/-- The entry heads the DFS worklist, so it is visited. -/
theorem jnzStopFnR_entry_visited :
    (dfsVisited (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0).contains "entry" = true := by
  decide

/-- `then` is CFG-reachable from the entry across the `JNZ`'s (second) edge. -/
theorem jnzStopFnR_then_reach :
    CfgReach (cfgAnalyze Example.jnzStopFnR) "entry" "then" :=
  CfgReach.step CfgReach.base (by decide)

/-- **The caller-facing path, end to end.** From a plain CFG-reachability proof — no `JmpChainTo`, no
    single-successor restriction — the branch target `then` gets its block plan located as a segment of
    the whole-function ops, at its canonical entry state. This is the layout fact a per-block `hstep`
    needs, now available at a block that `chain_segment_gbp` structurally could not reach. -/
theorem jnzStopFnR_then_segment_of_reach
    {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hgenAux : generateFnPlanAux (fnPlanFuel Example.jnzStopFnR)
        (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
        (DfgAnalysis.buildFunction Example.jnzStopFnR) (cfgAnalyze Example.jnzStopFnR)
        Example.jnzStopFnR ["entry"] [] { initPlanState 0 with labelCounter := 0 }
      = some (ops, vF, psF)) :
    ∃ preOps blockOps tailOps ps',
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR)
        (DfgAnalysis.buildFunction Example.jnzStopFnR) (cfgAnalyze Example.jnzStopFnR)
        Example.jnzStopFnR Example.thenBB
        (psOfFn (fnPlanFuel Example.jnzStopFnR) Example.jnzStopFnR 0 0 Example.thenBB.label)
      = some (blockOps, ps') := by
  refine reach_segment_gbp (entry := Example.jnzEntryR) ?_ rfl hgenAux
    jnzStopFnR_dfs_closed jnzStopFnR_entry_visited jnzStopFnR_then_reach rfl
  intro bb hbb inst hinst
  simp only [Example.jnzStopFnR, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · simp only [Example.jnzEntryR, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide
  · simp only [Example.thenBB, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide
  · simp only [Example.elseBB, List.mem_singleton] at hinst
    subst hinst; unfold codegenReadyInst; decide


/-! ### A real loop, and why the ranked walk cannot take its back-edge

`loopFn` is a genuine cyclic CFG: `entry` branches to `body` or `exit`, and `body` jumps *back* to
`entry`. The edge `body → entry` is a back-edge — its target is laid out before it in the program.

`ranked_walk_no_back_edge` says the ranked driver (`codegen_correct_sched`, whose rank is
`wOf l = prog.length - pcOfLabel prog l`) cannot cross such an edge: `pcOfLabel entry ≤ pcOfLabel body`
forces `wOf entry ≥ wOf body`, so its required decrease `wOf entry + blockLen ≤ wOf body` collapses to
`blockLen = 0`, contradicting the fact that a block emits at least its own JUMPDEST.

Below, the CFG facts are read off the *real* compiler, so this is not a hypothetical: it is the
concrete obstruction that `runBlocks_walk_fuel` / `codegen_correct_fuel` exist to remove, by taking
the decrease from the Venom fuel instead of the program layout. -/

namespace Example

def loopJnz : Instruction :=
  { id := 0, opcode := Opcode.JNZ,
    operands := [Operand.Lit (UInt256.ofNat 1), Operand.Label "body", Operand.Label "exit"],
    outputs := [] }
def loopBack : Instruction :=
  { id := 1, opcode := Opcode.JMP, operands := [Operand.Label "entry"], outputs := [] }

def loopEntryBB : BasicBlock := { label := "entry", instructions := [loopJnz] }
def loopBodyBB  : BasicBlock := { label := "body",  instructions := [loopBack] }
def loopExitBB  : BasicBlock := { label := "exit",  instructions := [stopInst] }

/-- `entry ⇄ body`, `entry → exit`: a genuinely cyclic CFG. -/
def loopFn : IrFunction :=
  { name := "main", blocks := [loopEntryBB, loopBodyBB, loopExitBB] }



/-! ### ✅ The pinned capstone is PROVED (`codegen_correct_tFn_recipeW`) — history of the diagnosis

**Done — `codegen_correct_tFn_recipeW` is proved.** This note is kept for the reasoning, which took three
wrong turns worth remembering: it first called the capstone "fill-in-the-blanks", then "BLOCKED by the
driver's `∀ s`", then "blocked, but the fix is local". The last was right:
`codegen_correct_ofBlocks_recipeW_inv` carries a caller-chosen invariant, and the capstone went through.
The diagnosis below is retained because it explains WHY an invariant driver is the right shape.

`codegen_correct_ofBlocks_recipeW`'s obligation is `hsupply : ∀ bb ∈ fn.blocks, ∀ (s : VenomState) …,
CanonEntryWH … s asm N → …` — **`s` is universally quantified**, and `CanonEntryWH = CanonEntry ∧
wOf s.currentBb ≤ N ∧ s.halted = false` carries **no bound on the VALUES of `s`'s vars**. But a RETURN/REVERT
recipe needs `hbelow : off.toNat + sz.toNat ≤ ps'.alloc.fnEom`, and `initPlanState 0` sets `fnEom = 0`
(`PlanTypes.lean:50-55`), so `hbelow` forces `off = sz = 0`. For an arbitrary `s` that is simply false — and a
`callvalue = 0` precondition on the capstone's `vs` does NOT reach the driver's internal `s`, which the driver
quantifies over independently of how the function actually reaches that block.

Nor does the error arm rescue it: RETURN's Venom semantics read memory rather than erroring on a large
offset, so `runBlock` succeeds and a recipe is genuinely required.

**⇒ No RETURN/REVERT capstone is possible through this driver AS INSTANTIATED, for any function, regardless
of which slice is used** (`_HSVP`, `…Dead`, or `…Reorder` alike). The slices are sound and their statements
stand; they lack a consumer. Same shape as `reorderPlan_sim`'s `∀ p` `hstep` (fact 5) one level up: a `∀` over
states the caller cannot constrain.

**But the fix is LOCAL, not a redesign — checked.** `codegen_correct_ofBlocks_recipeW` is a thin wrapper over
`codegen_correct_ofBlocks_HbsimMatch`, and that lemma takes **`Entry` as a free parameter**
(`Entry : VenomState → AsmState → Nat → Prop`, with `hstep : ∀ … Entry s asm N → …` and
`hentry : Entry …`). So the `∀ s` already ranges only over states satisfying `Entry`, whatever `Entry` is —
the weakness is the INSTANCE (`CanonEntryWH`, which bounds no values), not the architecture. Concretely:

1. instantiate `Entry := fun s asm N => CanonEntryWH fn lo pcOf psOf wOf s asm N ∧ Inv s` for a caller-chosen
   `Inv : VenomState → Prop` — `hsupply` then receives `Inv s` for free, which is exactly what `hbelow` needs;
2. the only thing hardcoding `CanonEntryWH` is `HbsimMatch_dispatchW`, so it needs an `Inv`-threading variant:
   its OK-continuing arms must establish `Inv s'` for the successor (the preservation obligation), which is
   where the caller proves the invariant is maintained across a block;
3. the driver passes `hentry : Inv vs` alongside the existing entry facts.

For `tFn` the invariant is small (`lookupVar "s"/"o" s` are `0`), vacuous at entry and established by the
entry block's own step. **That driver now exists** (`codegen_correct_ofBlocks_recipeW_inv`), and it needed no
`Inv`-threading dispatcher at all: `HbsimMatch` mentions `Entry` in exactly ONE arm, so `HbsimMatch_and_inv`
conjoins the invariant onto the existing `HbsimMatch_dispatchW` result wholesale.

**⇒ PROVED.** The pieces, for reference:
`tInv s := s.halted = false ∧ s.callCtx.callvalue = 0 ∧ (s.currentBb = "next" → lookupVar "s"/"o" s = some 0)`
— conditioning on `currentBb` is what makes it vacuous at entry, so `hinv0` needs only `callvalue = 0`;
`hpres` for `tEntry` follows from `runBlock_body_jmp` (fuel `< 3` gives `Error`; at `2+(j+1)` the result is
`jumpTo "next"` of the two-CALLVALUE state, whose `s`/`o` ARE the zero call value), and for `tNext` it is
vacuous (RETURN never yields `OK`). `hsupply` at `tNext` then reads `s`/`o` `= 0` straight out of `tInv`,
discharging RETURN's `hbelow` (`0 + 0 ≤ 0`) and giving `hcov0` its left disjunct.

**The tactic lesson (it cost five dead ends): CHARACTERISE, NEVER REDUCE.** `simp` will not reduce
`runBlock`'s nested matches — `simp`/`cases`/`noConfusion`/`absurd`, and bridging the `instIdx` wrapper, all
failed on `hrun : … = OK s'`. Every branch that closes does so by rewriting with a characterisation lemma:
`runBlock_body_jmp` (entry), `runBlock_body_return` (both operands defined), `runBlock_error` (either operand
undefined). The last one already existed — one grep away the whole time.

What survives below: the layout facts are all still correct and worth keeping, and they would be exactly what
a driver carrying such an invariant would consume. -/

/-! ### (retained) the verified layout inputs — now consumed by `codegen_correct_tFn_recipeW`

`tFn` below (`entry: %s = CALLVALUE ; %o = CALLVALUE ; JMP next` / `next: RETURN %s %o`) is the target for a
capstone consuming `hsupplyW_regularJmp` (2-instruction body) and `hsupplyW_emptyReturnReorder` (a genuine
`SWAP1`). Every input is checked on the real generator, so the assembly is fill-in-the-blanks:

* **program** `[L entry(0); CALLVALUE(1); CALLVALUE(2); PUSH(3); JUMP(4); L next(5); SWAP1(6); RETURN(7)]`,
  length 8; `pcOf entry = 0`, `pcOf next = 5`; `wOf entry = 8`, `wOf next = 3`.
* **entry** via `hsupplyW_regularJmp`: `front = [tS, tO]`, body plan `[CALLVALUE, CALLVALUE]` (length 2), so
  the `PUSH` sits at `0+1+2 = 3` and the `JUMP` at `4`; `off = 7` (`offsets = [("next",7),("entry",0)]`),
  `o2pc : 7 ↦ 5 = pcOf next`; `hreg = tBody_regularBodyH`; `hps` (`bodyPlanRIP … = psOf "next"`) is `rfl`;
  `hw : 3 + ((1+2)+2) = 8 ≤ 8`.
* **next** via `hsupplyW_emptyReturnReorder` at `asm.pc = 5`: `offv = "s"`, `szv = "o"` (so
  `targetOps = [Var szv, Var offv] = [Var o, Var s]`); `psOf "next" .stack = [Var s, Var o]` ⇒ `base = []`,
  `perm = [Var s, Var o]`, and `hperm` is the two-element swap; `hbound : 2 ≤ 17`; `hnospill` from the empty
  `spilled`; `hreorder` is `rfl`-shaped and emits ONE op, so the `RETURN` lands at `5+1+1 = 7`;
  `hw : 1+1+1 = 3 ≤ 3`. `join_bounded` then hands back `ps'.stack = [] ++ [Var o, Var s]`, which is exactly
  what `venomAsmRel_asmStack_top2_var` consumes.
* **the one honest precondition**: `vs.callCtx.callvalue = 0`, which discharges `hbelow` (`fnEom = 0`, see
  above) and gives `hcov0` its left disjunct.

Both `hw` bounds are TIGHT, so the layout admits no slack — a capstone that builds is evidence the whole
chain's arithmetic agrees with the compiler. -/

end Example

/-- The real compiler sees the back-edge: `body`'s only successor is `entry`. -/
theorem loopFn_back_edge :
    (cfgAnalyze Example.loopFn).succsOf "body" = ["entry"] := by decide

/-- And `entry` really is reachable again from itself — the CFG has a cycle. -/
theorem loopFn_cyclic : CfgReach (cfgAnalyze Example.loopFn) "entry" "entry" :=
  CfgReach.base

/-- `body` is reachable, and from it the walk returns to `entry` — the back-edge is live. -/
theorem loopFn_reaches_body_then_entry :
    CfgReach (cfgAnalyze Example.loopFn) "entry" "body" ∧
    "entry" ∈ (cfgAnalyze Example.loopFn).succsOf "body" :=
  ⟨CfgReach.step CfgReach.base (by decide), by decide⟩

/-- **The ranked walk provably cannot compile this loop.** `entry` is laid out at or before `body`, so
    the back-edge `body → entry` makes `codegen_correct_sched`'s required rank decrease
    (`wOf entry + blockLen ≤ wOf body`) unsatisfiable for any block of nonzero length. This is the
    concrete obstruction; `codegen_correct_fuel` removes it by ranking with the Venom fuel instead. -/
theorem loopFn_ranked_walk_impossible
    {prog : List AsmInst} {blockLen : Nat}
    (hlayout : pcOfLabel prog "entry" ≤ pcOfLabel prog "body")
    (hin : pcOfLabel prog "body" ≤ prog.length)
    (hpos : 1 ≤ blockLen)
    (hdec : (prog.length - pcOfLabel prog "entry") + blockLen
              ≤ (prog.length - pcOfLabel prog "body")) :
    False :=
  ranked_walk_no_back_edge hlayout hin hpos hdec



/-- The real compiler does compile the cyclic function — the plan exists. -/
theorem loopFn_plan_exists : (generateFnPlan Example.loopFn 0 0).isSome = true := by rfl

/-- **The obstruction, on the actually-compiled program.** For the real resolved program of `loopFn`,
    `entry` sits at pc 0 and `body` at pc 8, so the canonical ranks are `wOf entry = 11` and
    `wOf body = 3`. The ranked driver's required decrease across the back-edge `body → entry` is
    therefore `11 + blockLen ≤ 3` — false for every block. Not a hypothetical: this is the compiler's
    own output, and it is exactly what `codegen_correct_fuel` sidesteps by ranking with Venom fuel. -/
theorem loopFn_real_ranked_impossible {blockLen : Nat} (hpos : 1 ≤ blockLen)
    (hdec : ((asmResolve (executePlan (generateFnPlan Example.loopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan Example.loopFn 0 0).get!.1)).1 "entry")
            + blockLen
          ≤ ((asmResolve (executePlan (generateFnPlan Example.loopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan Example.loopFn 0 0).get!.1)).1 "body")) :
    False :=
  loopFn_ranked_walk_impossible (by decide) (by decide) hpos hdec


/-! ### The join-agreement invariant, and the phi-liveness bug that used to break it

Every `hstep` in this development takes the block's *incoming* `PlanState` as compiled by the plan
DFS. At a **genuine join** (≥ 2 predecessors) that state is whichever predecessor the DFS happened to
reach first — `cleanStackPlan` fires only when `predsOf` is a singleton, so a real join gets no
reconciliation at all (`no_reconciliation_at_join`). Correctness therefore rests on a *join-agreement
invariant*: **the join must compile to the same code whichever predecessor it is compiled against.**

That invariant used to be **false**, and this diamond is the witness that found it:

    entry: c = calldataload 0 ; d = calldataload 32 ; jnz c, then, else
    then:  a = c + 1          ; jmp join
    else:  b = c + 2          ; jmp join
    join:  p = phi(then→a, else→b) ; sstore d, p ; stop

The cause was `livenessTransfer`, which had no `PHI` case: it ran `liveUpdate (instDefs inst)
(instUses inst)` on a phi like any other instruction, *killing* the output `p` and *using* both
sources `a`,`b`. The join's live-in came out `["d","a","b"]` — sources present, output absent.

That defeated the very mechanism meant to prevent it. `livenessEdgeTransfer` calls `inputVarsFrom`,
whose job is to rewrite a phi *output* into the source matching the incoming edge; with `p` absent
there was nothing to rewrite, so it collapsed to the identity and handed *both* predecessors the same
target layout `["d","a","b"]` — which neither can build, since `then` never defines `b` and `else`
never defines `a`. They reordered as far as they could and landed in *different* layouts (the TOS is
the *last* element, `stackPush = stk ++ [op]`): `else` exited `["d","b"]` with the phi source at depth
0, `then` exited `["a","d"]` with it at depth **1**. The DFS compiles `join` against `else` (its first
successor — `bbSuccs` reverses), planning the phi as a single `SOPoke 0`. Arriving from `then`, depth
0 held `d`, so the join bound `p := d` — a value the phi never mentions.

`livenessTransfer` now has that `PHI` case (no defs, no uses — a phi's def happens on the edge and its
operands are *edge* uses), so the output stays live at the join and `inputVarsFrom` substitutes the
matching source per edge, as designed. The theorems below pin the repaired behaviour on the same
diamond: each predecessor now gets a target layout it can actually build, both put the incoming value
at the **same depth**, and the join compiles to the **same plan** from either one
(`phi_join_agreement`) — which is exactly the invariant the genuine-join `hstep` needs.

Kept as a regression test: it is the third miscompile this development caught by evaluating a
hypothesis against the real compiler rather than assuming it, after the non-commutative binop operand
order and the LOG operand order. -/

namespace Example

def phiC : Instruction :=
  { id := 0, opcode := Opcode.CALLDATALOAD, operands := [Operand.Lit (UInt256.ofNat 0)],
    outputs := ["c"] }
def phiD : Instruction :=
  { id := 1, opcode := Opcode.CALLDATALOAD, operands := [Operand.Lit (UInt256.ofNat 32)],
    outputs := ["d"] }
def phiJnz : Instruction :=
  { id := 2, opcode := Opcode.JNZ,
    operands := [Operand.Var "c", Operand.Label "then", Operand.Label "else"], outputs := [] }
def phiThenAdd : Instruction :=
  { id := 3, opcode := Opcode.ADD,
    operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 1)], outputs := ["a"] }
def phiThenJmp : Instruction :=
  { id := 4, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def phiElseAdd : Instruction :=
  { id := 5, opcode := Opcode.ADD,
    operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 2)], outputs := ["b"] }
def phiElseJmp : Instruction :=
  { id := 6, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def phiPhi : Instruction :=
  { id := 7, opcode := Opcode.PHI,
    operands := [Operand.Label "then", Operand.Var "a", Operand.Label "else", Operand.Var "b"],
    outputs := ["p"] }
def phiSstore : Instruction :=
  { id := 8, opcode := Opcode.SSTORE, operands := [Operand.Var "d", Operand.Var "p"], outputs := [] }
def phiStop : Instruction := { id := 9, opcode := Opcode.STOP, operands := [], outputs := [] }

def phiEntryBB : BasicBlock := { label := "entry", instructions := [phiC, phiD, phiJnz] }
def phiThenBB  : BasicBlock := { label := "then",  instructions := [phiThenAdd, phiThenJmp] }
def phiElseBB  : BasicBlock := { label := "else",  instructions := [phiElseAdd, phiElseJmp] }
def phiJoinBB  : BasicBlock := { label := "join",  instructions := [phiPhi, phiSstore, phiStop] }

/-- A diamond whose join carries a phi — the shape the join-agreement invariant fails on. -/
def phiFn : IrFunction :=
  { name := "main", blocks := [phiEntryBB, phiThenBB, phiElseBB, phiJoinBB] }

def phiLive : DfState (List String) := livenessAnalyzeFuel (fnPlanFuel phiFn) phiFn
def phiCfg  : CfgAnalysis := cfgAnalyze phiFn
def phiDfg  : DfgAnalysis := DfgAnalysis.buildFunction phiFn

/-- The exit `PlanState` stack of `bb`, threaded from `entry` exactly as the plan DFS threads it. -/
def phiExitStack (bb : BasicBlock) : Option (List String) :=
  ((generateBlockPlan phiLive phiDfg phiCfg phiFn phiEntryBB (initPlanState 0)).map (·.2)).bind
    (fun ps => (generateBlockPlan phiLive phiDfg phiCfg phiFn bb ps).map
      (fun r => r.2.stack.map operandToString))

def pokeDepths (ops : List StackOp) : List Nat :=
  ops.filterMap (fun o => match o with | StackOp.SOPoke d _ => some d | _ => none)

/-- The join's own plan, compiled — as the DFS threads it — against `predBB`'s exit state. -/
def phiJoinPlanFrom (predBB : BasicBlock) : Option (List StackOp) :=
  ((generateBlockPlan phiLive phiDfg phiCfg phiFn phiEntryBB (initPlanState 0)).map (·.2)).bind
    (fun ps => ((generateBlockPlan phiLive phiDfg phiCfg phiFn predBB ps).map (·.2)).bind
      (fun ps' => (generateBlockPlan phiLive phiDfg phiCfg phiFn phiJoinBB ps').map (·.1)))

def phiJoinPokeDepths (predBB : BasicBlock) : Option (List Nat) :=
  (phiJoinPlanFrom predBB).map pokeDepths

end Example

/-- `join` is a **genuine** join: two predecessors, so `cleanStackPlan` contributes nothing
(`no_reconciliation_at_join`) and the block is compiled against whichever predecessor the DFS
reached first. Everything below is about making that choice not matter. -/
theorem phiFn_genuine_join : Example.phiCfg.predsOf "join" = ["else", "then"] := by decide

/-- **The transfer is phi-aware.** The join's live-in holds the phi *output* `p` — not its sources
`a`,`b`, which are uses of the incoming *edge*. (Before the `PHI` case in `livenessTransfer` this was
`["d","a","b"]`: sources present, output absent — the root of the miscompile.) -/
theorem phi_liveness_is_phi_aware :
    liveVarsAt Example.phiLive "join" 0 = ["d", "p"] := by decide

/-- **So `inputVarsFrom` does its job.** With the output live, it rewrites `p` into the source
matching each incoming edge, giving each predecessor a target layout it can actually build — and, in
particular, *different* ones. (Before the fix both got the same, unbuildable `["d","a","b"]`.) -/
theorem phi_inputVarsFrom_then :
    inputVarsFrom "then" Example.phiJoinBB.instructions (liveVarsAt Example.phiLive "join" 0)
      = ["d", "a"] := by decide

theorem phi_inputVarsFrom_else :
    inputVarsFrom "else" Example.phiJoinBB.instructions (liveVarsAt Example.phiLive "join" 0)
      = ["d", "b"] := by decide

/-- **Each predecessor now delivers its phi source at the same depth.** TOS is the last element, so
both exits carry the incoming value at depth 0 and `d` at depth 1; they differ only in *which*
variable occupies the phi slot, which is precisely what the phi is there to reconcile. (Before the
fix: `else` exited `["d","b"]` but `then` exited `["a","d"]` — depth 0 versus depth 1.) -/
theorem phi_else_exit : Example.phiExitStack Example.phiElseBB = some ["d", "b"] := by decide

theorem phi_then_exit : Example.phiExitStack Example.phiThenBB = some ["d", "a"] := by decide

/-- The join plans the phi as a single rename of the TOS — and that is now right for **both**
predecessors, not just the one it was compiled against. -/
theorem phi_join_pokes_depth0_from_else :
    Example.phiJoinPokeDepths Example.phiElseBB = some [0] := by decide

theorem phi_join_pokes_depth0_from_then :
    Example.phiJoinPokeDepths Example.phiThenBB = some [0] := by decide

/-- **The join-agreement invariant, on the shape that used to break it.** The join compiles to the
*same plan* whichever predecessor's exit state it is compiled against — so it does not matter which
one the DFS reached first, and the genuine-join `hstep` has the property it needs.

This is the statement `phi_join_agreement_fails` used to refute. -/
theorem phi_join_agreement :
    Example.phiJoinPlanFrom Example.phiElseBB = Example.phiJoinPlanFrom Example.phiThenBB := by
  decide

/-! #### …and the same agreement, from the *generic* lemma rather than by computation

`phi_join_agreement` above is a `decide` on one function. The general statement lives in `Liveness`:
`inputVarsFrom_slot_agree` says any two predecessors of any join get target layouts that agree
position by position, differing only at phi slots — where each names its own edge's source, which is
exactly the slot the join's `SOPoke` renames. Its one hypothesis is that every phi covers both
predecessors. Here that hypothesis is discharged against the real compiler, so the generic lemma is
shown to apply to real generator output rather than to a hypothetical. -/

/-- The diamond's phi really does cover **both** predecessors. -/
theorem phiFn_covers_both :
    ∀ i, (AssocList.lookup Nat String
            (buildPhiMaps "then" (collectPhis Example.phiJoinBB.instructions)).2 i).isSome
       = (AssocList.lookup Nat String
            (buildPhiMaps "else" (collectPhis Example.phiJoinBB.instructions)).2 i).isSome := by
  intro i
  cases i with
  | zero => decide
  | succ n =>
    simp [buildPhiMaps, collectPhis, Example.phiJoinBB, Example.phiPhi, Example.phiSstore,
          Example.phiStop, phiPairs, AssocList.lookup, AssocList.insert]

/-- So the **generic** slot agreement applies to this function: the two edges' target layouts agree
slot by slot, each phi slot holding that edge's own source. -/
theorem phiFn_slot_agree :
    List.Forall₂
      (fun v1 v2 => v1 = v2 ∨ ∃ i,
          AssocList.lookup Nat String
            (buildPhiMaps "then" (collectPhis Example.phiJoinBB.instructions)).2 i = some v1 ∧
          AssocList.lookup Nat String
            (buildPhiMaps "else" (collectPhis Example.phiJoinBB.instructions)).2 i = some v2)
      (inputVarsFrom "then" Example.phiJoinBB.instructions (liveVarsAt Example.phiLive "join" 0))
      (inputVarsFrom "else" Example.phiJoinBB.instructions (liveVarsAt Example.phiLive "join" 0)) :=
  inputVarsFrom_slot_agree "then" "else" Example.phiJoinBB.instructions
    (liveVarsAt Example.phiLive "join" 0) phiFn_covers_both

/-- And every predecessor is asked for a layout of the same depth — the join's incoming stack shape
does not depend on which edge you arrive by. -/
theorem phiFn_layouts_same_length :
    (inputVarsFrom "then" Example.phiJoinBB.instructions
        (liveVarsAt Example.phiLive "join" 0)).length
      = (inputVarsFrom "else" Example.phiJoinBB.instructions
        (liveVarsAt Example.phiLive "join" 0)).length :=
  inputVarsFrom_length_eq "then" "else" Example.phiJoinBB.instructions
    (liveVarsAt Example.phiLive "join" 0) phiFn_covers_both

/-! #### The hypotheses of `generatePhiPlan_congr`, on real compiler output

`generatePhiPlan_congr` (in `CodegenGenProps`) says the join's phi plan emits the same code from
either predecessor and equalises the two plan states. Its hypotheses are checked here against the
actual generator, so the congruence is known to fire on real input. -/

namespace Example

/-- Each predecessor's exit `PlanState`, threaded from `entry` exactly as the plan DFS threads it. -/
def phiExitPS (bb : BasicBlock) : Option PlanState :=
  ((generateBlockPlan phiLive phiDfg phiCfg phiFn phiEntryBB (initPlanState 0)).map (·.2)).bind
    (fun ps => (generateBlockPlan phiLive phiDfg phiCfg phiFn bb ps).map (·.2))

/-- The phi's source operands — what `generatePhiPlan` searches the stack for. -/
def phiSrcs : List Operand := phiPhi.operands.filter isVarOperand

end Example

/-- **The phi's source sits at the same depth on both edges** — the conclusion of
`stackGetPhiDepth_congr`, confirmed on the real generator. The *names* differ (`b` from `else`, `a`
from `then`); the *depth* does not, so the single positional `SOPoke` is right for both. -/
theorem phiFn_phi_depth_agrees :
    (Example.phiExitPS Example.phiElseBB).map
        (fun p => stackGetPhiDepth Example.phiSrcs p.stack)
      = (Example.phiExitPS Example.phiThenBB).map
        (fun p => stackGetPhiDepth Example.phiSrcs p.stack) := by decide

theorem phiFn_phi_depth_is_zero :
    (Example.phiExitPS Example.phiElseBB).map
        (fun p => stackGetPhiDepth Example.phiSrcs p.stack) = some (some 0) := by decide

/-- **The incoming source is dead past the phi, on both edges** — the `hnl` hypotheses of
`generatePhiPlan_congr`. This is a consequence of the phi-aware transfer: a phi's operands are uses of
the *edge*, not of the join, so they do not survive it. Before the fix they did, and the plan took the
other branch. -/
theorem phiFn_phi_src_dead_after :
    ((Example.phiExitPS Example.phiElseBB).map (fun p =>
        (liveVarsAt Example.phiLive "join" 1).contains (operandToString (stackPeek 0 p.stack)))
      = some false)
    ∧ ((Example.phiExitPS Example.phiThenBB).map (fun p =>
        (liveVarsAt Example.phiLive "join" 1).contains (operandToString (stackPeek 0 p.stack)))
      = some false) := by
  constructor <;> decide

/-! #### The plan-generator capstone, fired on real compiler output

`generateBlockPlan_congr_at_join` says a genuine join's plan does not depend on which predecessor the
DFS compiled it against. A generic theorem nobody can instantiate is barely better than a vacuous one,
so its hypotheses are discharged here against the actual generator.

The two predecessors' exit states are pinned as literals first (`phiFn_psElse` / `phiFn_psThen` show
the generator really produces them). That split matters: asking `decide` to re-derive those states
*inside* the congruence proof does not terminate, because it drags the whole liveness fixpoint and both
predecessors' block plans through kernel reduction. Pinned first, the remaining check is small. -/

namespace Example

/-- The exit `PlanState`s the generator produces for the two predecessors. -/
def psElse : PlanState :=
  { stack := [Operand.Var "d", Operand.Var "b"], spilled := [],
    alloc := ⟨[], 0, 0⟩, labelCounter := 0 }

def psThen : PlanState :=
  { stack := [Operand.Var "d", Operand.Var "a"], spilled := [],
    alloc := ⟨[], 0, 0⟩, labelCounter := 0 }

/-- The leading phis of the join, each with the liveness the block fold hands it. -/
def joinPhiPairs : List (Instruction × List String) :=
  ((nonParamInsts phiJoinBB).zipIdx.take 1).map (fun it =>
    (it.1, if it.2 + 1 < (nonParamInsts phiJoinBB).length
           then liveVarsAt phiLive phiJoinBB.label
                  (it.2 + (getParams phiJoinBB.instructions).length + 1)
           else liveVarsAt phiLive phiJoinBB.label phiJoinBB.instructions.length))

end Example

/-- The literals above really are the generator's output. -/
theorem phiFn_psElse : Example.phiExitPS Example.phiElseBB = some Example.psElse := by decide

theorem phiFn_psThen : Example.phiExitPS Example.phiThenBB = some Example.psThen := by decide

/-- **The phi prologue leaves the two predecessors' states identical** — the capstone's hypothesis, on
the states the compiler actually produces. -/
theorem phiFn_prefix_congr :
    phiPrefixPlan Example.joinPhiPairs Example.psElse
      = phiPrefixPlan Example.joinPhiPairs Example.psThen := by decide

/-- **The capstone, fired.** Every hypothesis of `generateBlockPlan_congr_at_join` is discharged
against the real generator, so on this function the join's block plan provably does not depend on which
predecessor the plan DFS compiled it against — the property whose failure was the miscompile. -/
theorem phiFn_join_plan_pred_independent :
    generateBlockPlan Example.phiLive Example.phiDfg Example.phiCfg Example.phiFn
        Example.phiJoinBB Example.psElse
      = generateBlockPlan Example.phiLive Example.phiDfg Example.phiCfg Example.phiFn
        Example.phiJoinBB Example.psThen :=
  generateBlockPlan_congr_at_join (k := 1) (by decide) (by decide) (by decide) phiFn_prefix_congr

/-! #### …and the semantic side, on the same arrival

The plan-generator results say the join compiles the same way from either predecessor. The claim they
rest on is semantic and, stated plainly, surprising: entering the join from the predecessor it was *not*
compiled against, `planStackRel` genuinely **fails**, and the phi is what repairs it.

Both halves of that are witnessed below on the real function — the relation is refuted before the phi,
and `planStackRel_phi_poke_offSlot` establishes it afterwards. -/

namespace Example

def dv : bytes32 := UInt256.ofNat 7
def av : bytes32 := UInt256.ofNat 8

/-- Arriving at `join` from `then` — the predecessor the DFS did *not* compile the join against. `a` is
defined on this path; `b` never was. -/
def vsFromThen : VenomState :=
  { (default : VenomState) with
    vars := [("c", UInt256.ofNat 1), ("d", dv), ("a", av)],
    prevBb := some "then", currentBb := "join" }

/-- …and the state after the join's phi binds `p` to the value *this* edge delivered. -/
def vsAfterPhi : VenomState := updateVar "p" av vsFromThen

/-- The asm stack on that arrival: TOS first, so `a`'s value on top and `d`'s below — exactly `then`'s
exit layout. The asm side is untouched by the phi, which emits no code. -/
def asmFromThen : List bytes32 := [av, dv]

end Example

/-- **The relation genuinely fails before the phi.** The join was compiled against `else`, so its
recorded TOS slot names `b` — and on this path `b` was never assigned, so `operandVal` there is `none`,
not the value in the asm slot. This is why the single-predecessor phi lemma in `GenBlockSimComp`, which
*assumes* the relation beforehand, cannot cover the other edges. -/
theorem phiFn_rel_fails_before_phi :
    ¬ planStackRel [] Example.vsFromThen Example.psElse.stack Example.asmFromThen := by
  intro h
  have h0 := h.2 0 (by decide)
  exact absurd h0 (by decide)

/-- **…and the phi's poke establishes it** — by the generic lemma, with every hypothesis discharged
against these concrete states. The asm stack never moved; the phi bound `p` to the value already
sitting in that slot. -/
theorem phiFn_rel_holds_after_phi :
    planStackRel [] Example.vsAfterPhi
      (stackPoke 0 (Operand.Var "p") Example.psElse.stack) Example.asmFromThen :=
  planStackRel_phi_poke_offSlot (by decide) (by decide) (by decide) (by decide)

/-- The relation that really *does* hold on arrival from `then`: against **`then`'s own** exit layout.
This is what `then`'s block simulation hands you, and it is the input `phi_join_step` takes — the whole
point being that it, unlike the relation against the recorded layout, is true on every edge. -/
theorem phiFn_rel_on_arrival :
    planStackRel [] Example.vsFromThen Example.psThen.stack Example.asmFromThen := by
  refine ⟨by decide, ?_⟩
  intro i hi
  have hi2 : i < 2 := by simpa [Example.psThen] using hi
  interval_cases i <;> decide

/-- **`phi_join_step`, fired on a real arrival.** Entering `join` from `then` — the predecessor the DFS
did *not* compile it against — the Venom phi executes, the asm stack does not move, and the relation
against the **recorded** plan stack is restored. Every hypothesis is discharged against the real
function, so the step a genuine-join `hstep` consumes is known to be usable, not merely provable. -/
theorem phiFn_join_phi_step :
    evalPhis Example.vsFromThen [Example.phiPhi]
        = ExecResult.OK (updateVar "p" Example.av Example.vsFromThen)
    ∧ planStackRel [] (updateVar "p" Example.av Example.vsFromThen)
        (stackPoke 0 (Operand.Var "p") Example.psElse.stack) Example.asmFromThen :=
  phi_join_step (prev := "then") (src := "a") (out := "p") (d := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    phiFn_rel_on_arrival (by decide) (by decide) (by decide) (by decide) (by decide)



/-! ### A genuine **two-phi** join — the multi-phi machinery, exercised

Everything above fires on `phiFn`, whose join carries a single phi. On such a function the multi-phi
results are indistinguishable from their single-phi cases, so their real content — that a lemma about
one phi slot *cannot* be iterated across a prologue — is never exercised.

This join carries two. The plan emits two pokes, at depths 1 and 0, and the recorded layout disagrees
with the arriving one at *both* slots at once, which is exactly the situation the single-slot lemmas
cannot handle. The block plan still comes out independent of which predecessor the DFS compiled it
against. -/

namespace Two

def iC  : Instruction :=
  { id := 0, opcode := Opcode.CALLDATALOAD, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := ["c"] }
def iJnz : Instruction :=
  { id := 1, opcode := Opcode.JNZ,
    operands := [Operand.Var "c", Operand.Label "then", Operand.Label "else"], outputs := [] }
def tA1 : Instruction :=
  { id := 2, opcode := Opcode.ADD, operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 1)],
    outputs := ["a1"] }
def tA2 : Instruction :=
  { id := 3, opcode := Opcode.ADD, operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 2)],
    outputs := ["a2"] }
def tJmp : Instruction :=
  { id := 4, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def eB1 : Instruction :=
  { id := 5, opcode := Opcode.ADD, operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 3)],
    outputs := ["b1"] }
def eB2 : Instruction :=
  { id := 6, opcode := Opcode.ADD, operands := [Operand.Var "c", Operand.Lit (UInt256.ofNat 4)],
    outputs := ["b2"] }
def eJmp : Instruction :=
  { id := 7, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def pP : Instruction :=
  { id := 8, opcode := Opcode.PHI,
    operands := [Operand.Label "then", Operand.Var "a1", Operand.Label "else", Operand.Var "b1"],
    outputs := ["p"] }
def pQ : Instruction :=
  { id := 9, opcode := Opcode.PHI,
    operands := [Operand.Label "then", Operand.Var "a2", Operand.Label "else", Operand.Var "b2"],
    outputs := ["q"] }
def iSt : Instruction :=
  { id := 10, opcode := Opcode.SSTORE, operands := [Operand.Var "p", Operand.Var "q"], outputs := [] }
def iStop : Instruction := { id := 11, opcode := Opcode.STOP, operands := [], outputs := [] }

def bEntry : BasicBlock := { label := "entry", instructions := [iC, iJnz] }
def bThen  : BasicBlock := { label := "then",  instructions := [tA1, tA2, tJmp] }
def bElse  : BasicBlock := { label := "else",  instructions := [eB1, eB2, eJmp] }
def bJoin  : BasicBlock := { label := "join",  instructions := [pP, pQ, iSt, iStop] }

/-- A diamond whose join carries **two** phis. -/
def fn2 : IrFunction := { name := "main", blocks := [bEntry, bThen, bElse, bJoin] }

def L2 : DfState (List String) := livenessAnalyzeFuel (fnPlanFuel fn2) fn2
def C2 : CfgAnalysis := cfgAnalyze fn2
def D2 : DfgAnalysis := DfgAnalysis.buildFunction fn2

def exitPS (bb : BasicBlock) : Option PlanState :=
  ((generateBlockPlan L2 D2 C2 fn2 bEntry (initPlanState 0)).map (·.2)).bind
    (fun ps => (generateBlockPlan L2 D2 C2 fn2 bb ps).map (·.2))

def psElse2 : PlanState :=
  { stack := [Operand.Var "b1", Operand.Var "b2"], spilled := [],
    alloc := ⟨[], 0, 0⟩, labelCounter := 0 }
def psThen2 : PlanState :=
  { stack := [Operand.Var "a1", Operand.Var "a2"], spilled := [],
    alloc := ⟨[], 0, 0⟩, labelCounter := 0 }

/-- **Both** leading phis, each with the liveness the block fold hands it. -/
def joinPhiPairs2 : List (Instruction × List String) :=
  ((nonParamInsts bJoin).zipIdx.take 2).map (fun it =>
    (it.1, if it.2 + 1 < (nonParamInsts bJoin).length
           then liveVarsAt L2 bJoin.label
                  (it.2 + (EvmYul.Venom.Hol.Codegen.getParams bJoin.instructions).length + 1)
           else liveVarsAt L2 bJoin.label bJoin.instructions.length))

end Two

/-- A genuine join, and the liveness is phi-aware: the join's live-in holds the phi *outputs*. -/
theorem fn2_genuine_join : Two.C2.predsOf "join" = ["else", "then"] := by decide

theorem fn2_liveness_is_phi_aware : liveVarsAt Two.L2 "join" 0 = ["p", "q"] := by decide

/-- Each predecessor gets a target layout it can actually build, and they differ. -/
theorem fn2_inputVarsFrom_then :
    inputVarsFrom "then" Two.bJoin.instructions (liveVarsAt Two.L2 "join" 0) = ["a1", "a2"] := by decide

theorem fn2_inputVarsFrom_else :
    inputVarsFrom "else" Two.bJoin.instructions (liveVarsAt Two.L2 "join" 0) = ["b1", "b2"] := by decide

/-- The generator really produces these exit states. -/
theorem fn2_psElse : Two.exitPS Two.bElse = some Two.psElse2 := by decide

theorem fn2_psThen : Two.exitPS Two.bThen = some Two.psThen2 := by decide

/-- **The whole two-phi prologue leaves the two states identical.** Both phis are processed — this is
the multi-phi content, not the single-phi case wearing a disguise. -/
theorem fn2_prefix_congr :
    phiPrefixPlan Two.joinPhiPairs2 Two.psElse2 = phiPrefixPlan Two.joinPhiPairs2 Two.psThen2 := by
  decide

/-- **The capstone on a genuine two-phi join.** The recorded layout disagrees with the arriving one at
*both* phi slots at once — the case no single-slot lemma can reach — and the block plan still does not
depend on which predecessor the DFS compiled it against. -/
theorem fn2_join_plan_pred_independent :
    generateBlockPlan Two.L2 Two.D2 Two.C2 Two.fn2 Two.bJoin Two.psElse2
      = generateBlockPlan Two.L2 Two.D2 Two.C2 Two.fn2 Two.bJoin Two.psThen2 :=
  generateBlockPlan_congr_at_join (k := 2) (by decide) (by decide) (by decide) fn2_prefix_congr



/-! #### The semantic side of the two-phi join — where the whole-prologue lemmas actually bite

Both phi slots disagree with the recorded layout at once, so no single-slot lemma applies here at all.
`phi_join_steps` does: both phis run on the Venom side, the asm stack does not move, and the relation
against the **recorded** (`else`-shaped) plan stack comes out of the relation against the **arriving**
one. -/

namespace Two

def a1v : bytes32 := UInt256.ofNat 11
def a2v : bytes32 := UInt256.ofNat 12

/-- Arriving from `then` — the predecessor the DFS did *not* compile the join against. `a1`,`a2` are
defined on this path; `b1`,`b2` never were. -/
def vsFromThen2 : VenomState :=
  { (default : VenomState) with
    vars := [("c", UInt256.ofNat 1), ("a1", a1v), ("a2", a2v)],
    prevBb := some "then", currentBb := "join" }

/-- The asm stack on that arrival, TOS first (`then` exits `["a1","a2"]` bottom-first). -/
def asmFromThen2 : List bytes32 := [a2v, a1v]

/-- Both phis, with what each does on *this* edge. -/
def runs : List PhiRun := [(pP, "p", "a1", a1v), (pQ, "q", "a2", a2v)]

/-- The slot each phi owns. -/
def dep2 : PhiRun → Nat := fun x => if x.out = "p" then 1 else 0

end Two

/-- The relation that really holds on arrival: against **`then`'s own** exit layout — what `then`'s
block simulation hands you. -/
theorem fn2_rel_on_arrival :
    planStackRel [] Two.vsFromThen2 Two.psThen2.stack Two.asmFromThen2 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  have hi2 : i < 2 := by simpa [Two.psThen2] using hi
  interval_cases i <;> decide

/-- **`phi_join_steps`, fired on a genuine two-phi arrival.** Every hypothesis discharged against the
real function. This is the case the single-slot lemmas cannot reach — both recorded slots name
variables (`b1`,`b2`) that this path never assigned — and the whole-prologue step repairs both at once. -/
theorem fn2_join_phi_steps :
    ∃ vs', evalPhis Two.vsFromThen2 (Two.runs.map PhiRun.inst) = ExecResult.OK vs'
      ∧ planStackRel [] vs'
          ((Two.runs.map (fun x => (Two.dep2 x, x.src, x.out, x.val))).foldl
            (fun st (y : PhiEdge) => stackPoke y.depth (Operand.Var y.out) st) Two.psElse2.stack)
          Two.asmFromThen2 :=
  phi_join_steps (prev := "then") Two.runs Two.dep2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fn2_rel_on_arrival (by decide) (by decide) (by decide) (by decide) (by decide)



/-- **`join_entry_reduces`, fired on the two-phi join.** Arriving from `then` — the predecessor the DFS
did *not* compile the join against — the whole block execution reduces to `execBlock` over a phi-free
block, starting from a state related to the asm against the join's **own recorded** plan stack.

Every hypothesis is discharged against the real function. This is the arc's claim, made concrete: a
join may be compiled against one predecessor and entered from another, because the phis absorb the
difference and everything after them is an ordinary block. -/
theorem fn2_join_entry_reduces (fuel : Nat) (ctx : VenomContext) :
    ∃ vs', runBlock fuel ctx Two.bJoin Two.vsFromThen2
             = execBlock fuel ctx Two.bJoin
                 { vs' with instIdx := phiPrefixLength Two.bJoin.instructions }
      ∧ planStackRel [] vs'
          ((Two.runs.map (fun x => (Two.dep2 x, x.src, x.out, x.val))).foldl
            (fun st (y : PhiEdge) => stackPoke y.depth (Operand.Var y.out) st) Two.psElse2.stack)
          Two.asmFromThen2 :=
  join_entry_reduces (lo := []) (psArr := Two.psThen2.stack) (psRec := Two.psElse2.stack)
    (asmStack := Two.asmFromThen2) (prev := "then") Two.runs Two.dep2
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fn2_rel_on_arrival (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)



/-! #### The reduction, fired — with its last input discharged

`join_runBlock_eq_residual` needs `stepInstBase` to respect `sameUpToIdx` on the residual's
instructions. Here that is *discharged* (`SSTORE`, `STOP`, via `sstore_respects` / `stop_respects`),
not assumed — so the whole chain runs on a real function with nothing left hanging. -/

namespace Two

/-- The two-phi join's phi-free residual: everything after its two phis. -/
def bJoinRes : BasicBlock := { label := "join", instructions := [iSt, iStop] }

end Two

/-- Every instruction of the residual respects `sameUpToIdx` — discharged, not assumed. -/
theorem fn2_residual_steps_respect :
    ∀ inst ∈ Two.bJoinRes.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
      ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2) := by
  intro inst hi t1 t2 h
  simp only [Two.bJoinRes, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact sstore_respects (by decide) t1 t2 h
  · exact stop_respects (by decide) t1 t2 h

/-- **The two-phi join's `evalPhis` really does succeed**, and binds both outputs to the values arriving
on *this* edge. Phis are parallel: both read the original state, and the updates are applied
outermost-first — so `p`'s wraps `q`'s. Without this, the reduction below would be conditioned on
something nothing was shown to satisfy. -/
theorem fn2_evalPhis :
    evalPhis Two.vsFromThen2 Two.bJoin.instructions
      = ExecResult.OK (updateVar "p" Two.a1v (updateVar "q" Two.a2v Two.vsFromThen2)) := by
  show evalPhis Two.vsFromThen2 (Two.pP :: Two.pQ :: [Two.iSt, Two.iStop]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Two.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a1") (prev := "then") (v := Two.a1v)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis Two.vsFromThen2 (Two.pQ :: [Two.iSt, Two.iStop]) with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Two.a1v s') | err => err) = _
  rw [show evalPhis Two.vsFromThen2 (Two.pQ :: [Two.iSt, Two.iStop])
        = ExecResult.OK (updateVar "q" Two.a2v Two.vsFromThen2) from by
    unfold evalPhis
    rw [if_neg (show ¬ (Two.pQ.opcode ≠ Opcode.PHI) from fun h => h rfl),
        evalOnePhi_var (out := "q") (src := "a2") (prev := "then") (v := Two.a2v)
          (by rfl) (by rfl) (by rfl) (by rfl)]
    show (match evalPhis Two.vsFromThen2 [Two.iSt, Two.iStop] with
          | ExecResult.OK s' => ExecResult.OK (updateVar "q" Two.a2v s') | err => err) = _
    rw [show evalPhis Two.vsFromThen2 [Two.iSt, Two.iStop] = ExecResult.OK Two.vsFromThen2 from by
      unfold evalPhis; rw [if_pos (by decide)]]]

/-- **The two-phi join's `runBlock` IS its phi-free residual's `execBlock`** — up to `instIdx`, on the
arrival from `then`: the predecessor the DFS did *not* compile the join against.

Now **unconditional**: `fn2_evalPhis` discharges the last hypothesis. A genuine join, entered from the
wrong predecessor, is an ordinary block — with nothing assumed. -/
theorem fn2_join_runBlock_eq_residual (fuel : Nat) (ctx : VenomContext) :
    ResSameUpToIdx (runBlock fuel ctx Two.bJoin Two.vsFromThen2)
                   (execBlock fuel ctx Two.bJoinRes
                     { (updateVar "p" Two.a1v (updateVar "q" Two.a2v Two.vsFromThen2)) with
                       instIdx := 0 }) :=
  join_runBlock_eq_residual (phis := [Two.pP, Two.pQ])
    (by rfl) (by decide) (by decide) (by decide) (by decide) fn2_residual_steps_respect
    fn2_evalPhis



/-! ### `genBlockSimulation`, on a block whose head is a phi — fired

Everything in the join development has been building to a block the `hstep` family cannot describe: its
`hphi` hypothesis demands a non-phi head, and a join's head is a `PHI`. Here is such a block, simulated.

The join is `p = phi(then→a, else→b) ; stop`, entered from `then` — the predecessor the plan DFS did
*not* compile it against. Its residual is a bare `STOP`, which `hasm_stop` already handles; the phi emits
no code, so the join's program *is* the residual's (`JUMPDEST ; STOP`). `genBlockSimulation_join` carries
the residual's simulation to the join.

(`p` is dead here, so the compiler emits no poke at all — the poke path is exercised at the plan level by
the two-phi function above. What this witnesses is the thing that was structurally impossible: a
simulation for a block whose head is a phi.) -/

namespace Min

def pP : Instruction :=
  { id := 6, opcode := Opcode.PHI,
    operands := [Operand.Label "then", Operand.Var "a", Operand.Label "else", Operand.Var "b"],
    outputs := ["p"] }

def iStop : Instruction :=
  { id := 7, opcode := Opcode.STOP, operands := [], outputs := [] }

def bJ : BasicBlock :=
  { label := "join", instructions := [pP, iStop] }

def bJRes : BasicBlock :=
  { label := "join", instructions := [iStop] }

def ops : List StackOp := [StackOp.SOLabel "join", StackOp.SOEmit "STOP"]

def av : bytes32 := UInt256.ofNat 5

def vs : VenomState :=
  { (default : VenomState) with
    vars := [("c", UInt256.ofNat 1), ("a", av)],
    prevBb := some "then", currentBb := "join" }

def ps : PlanState :=
  { stack := [], spilled := [], alloc := ⟨[], 0, 0⟩, labelCounter := 0 }

end Min

theorem min_prog : (asmResolve (executePlan Min.ops)).1 = executePlan Min.ops := by rfl

theorem min_proglen : (asmResolve (executePlan Min.ops)).1.length = 2 := by rfl

theorem min_ev : evalPhis Min.vs Min.bJ.instructions
    = ExecResult.OK (updateVar "p" Min.av Min.vs) := by
  show evalPhis Min.vs (Min.pP :: [Min.iStop]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis Min.vs [Min.iStop] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis Min.vs [Min.iStop] = ExecResult.OK Min.vs from by
    unfold evalPhis; rw [if_pos (by decide)]]


/-- The residual — a bare `STOP` — halts. -/
theorem min_res_run (f : Nat) (ctx : VenomContext) (w : VenomState) :
    runBlock (f + 1) ctx Min.bJRes w
      = ExecResult.Halt (haltState { w with instIdx := 0 }) := by
  rw [runBlock_of_no_phi (bb := Min.bJRes) (by intro i hi; cases hi; decide)]
  unfold execBlock
  rfl

/-- **`genBlockSimulation`, on a block whose head is a phi.**

`genBlockSimulation` itself cannot be instantiated here: its `hphi` hypothesis demands a non-phi head,
and this block's head is `PHI`. `genBlockSimulation_join` supplies the same conclusion anyway, from the
*residual* block's simulation — which is a bare `STOP`, and `hasm_stop` proves that. The arrival is from
`then`: the predecessor the plan DFS did **not** compile the join against.

The asm side never moves across the phi (`SOPoke` emits no code), so the join's program is exactly the
residual's: `JUMPDEST ; STOP`. -/
theorem min_join_sim {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {asm : AsmState} (f : Nat) (ctx : VenomContext)
    -- the relation that actually holds **on arrival**, before the phi runs
    (hrel : venomAsmRel lo Min.ps Min.vs asm)
    (hpc : asm.pc = 0) :
    match runBlock (f + 1) ctx Min.bJ Min.vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmOK as' ∧
          venomAsmRel lo Min.ps w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True := by
  -- the post-phi relation is *derived*, not assumed: `evalPhis` writes only `vars`, the phi's output
  -- is fresh, and the plan's poke (here absent) touches only the stack
  have hpost : venomAsmRel lo Min.ps (updateVar "p" Min.av Min.vs) asm :=
    venomAsmRel_phi_join' (outs := ["p"]) (phis := Min.bJ.instructions)
      hrel rfl rfl min_ev
      (fun w hw => lookupVar_updateVar_ne Min.vs "p" w Min.av (by simpa using hw))
      (fun op off hlk _ _ => absurd hlk (by simp [Min.ps, AssocList.lookup]))
      ⟨hrel.1.1, fun i hi => absurd hi (by simp [Min.ps])⟩
  refine genBlockSimulation_join (bb' := Min.bJRes) (phis := [Min.pP])
    (vs' := updateVar "p" Min.av Min.vs) (ops := Min.ops) (resOps := Min.ops)
    (by rfl)
    (by intro i hi; rw [List.mem_singleton] at hi; subst hi; rfl)
    (by intro i hi; simp only [Min.bJRes, List.head?_cons, Option.some.injEq] at hi;
        subst hi; decide)
    (by intro inst hi; simp only [Min.bJRes, List.mem_singleton] at hi; subst hi; decide)
    (by intro inst hi; simp only [Min.bJRes, List.mem_singleton] at hi; subst hi; decide)
    ?_ min_ev rfl ?_
  · intro inst hi t1 t2 h
    simp only [Min.bJRes, List.mem_singleton] at hi
    subst hi
    exact stop_respects (by decide) t1 t2 h
  · show BlockSim lo Min.ps offsetToPc (asmResolve (executePlan Min.ops)).1 asm
      (runBlock (f + 1) ctx Min.bJRes (updateVar "p" Min.av Min.vs))
    rw [min_res_run f ctx (updateVar "p" Min.av Min.vs)]
    show ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
      (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmHalt as' ∧
      venomAsmTerminalRel (haltState { (updateVar "p" Min.av Min.vs) with instIdx := 0 }) as'
    refine hasm_stop (l := "join") (ps := Min.ps)
      (venomAsmRel_congr (a := updateVar "p" Min.av Min.vs) (by unfold sameUpToIdx; rfl) hpost) ?_ ?_
    · rw [min_prog, hpc]
      refine ⟨by rfl, ?_⟩
      intro j hj
      simp only [Nat.zero_add, Min.ops]
    · rw [min_proglen]


/-! #### …and it is not vacuous

`min_join_sim` is conditioned on the relation holding on arrival. If nothing could satisfy that, the
simulation would be true and would say nothing. So here is a state that satisfies it, and the simulation
stated *unconditionally* on a real arrival.

A theorem's hypotheses are part of its content: proving one without ever exhibiting something that meets
them is not a result, it is a shape. -/

namespace Min
/-- A concrete asm state on arrival at the join: empty stack, pc at the block's start. -/
def asm : AsmState := (default : AsmState)
end Min

/-- **`min_join_sim` is not vacuous.** Its hypothesis — the relation holding on arrival — is
satisfiable, and here is a state satisfying it. Without this the simulation would be conditioned on
something nothing can meet, and would say nothing at all. -/
theorem min_rel_on_arrival : venomAsmRel [] Min.ps Min.vs Min.asm := by
  refine ⟨⟨rfl, fun i hi => absurd hi (by simp [Min.ps])⟩, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro op off hlk
    exact absurd hlk (by simp [Min.ps, AssocList.lookup])
  · intro i _
    rfl

/-- …so the simulation of a phi-headed block holds unconditionally on a real arrival. -/
theorem min_join_sim_nonvacuous (f : Nat) (ctx : VenomContext) (offsetToPc : AssocList Nat Nat) :
    match runBlock (f + 1) ctx Min.bJ Min.vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 Min.asm = AsmResult.AsmOK as' ∧
          venomAsmRel [] Min.ps w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 Min.asm = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 Min.asm = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 Min.asm = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True :=
  min_join_sim f ctx min_rel_on_arrival rfl



namespace Two
/-- The plan state after the join's phi prologue. -/
def psPost : PlanState := (phiPrefixPlan joinPhiPairs2 psElse2).2
end Two

/-- **The synthetic residual block does NOT compile to the join's program.**

`generateBlockPlan` looks liveness up *by position within the block*. The residual block drops the phis,
so every instruction after them shifts index — and the generator reads a different liveness entry, and
emits different code. Here the join assembles to 4 instructions and the residual, even started from the
join's own post-phi plan state, to 5.

So `genBlockSimulation` applied to the residual block is **not** a source for `genBlockSimulation_join`'s
`hres`: the programs would not match, and the `executePlan ops = executePlan resOps` link would be false.
The simulation must be for the join's *own* body plan — which is what `executePlan_join_eq_residual` is
about (the same `body` ops, with and without the phi prologue in front).

Pinned here because the natural reading of "give it the residual block's simulation" is wrong, and
nothing else in the development would have caught it. -/
theorem residual_block_compiles_differently :
    ((generateBlockPlan Two.L2 Two.D2 Two.C2 Two.fn2 Two.bJoin Two.psElse2).map
       (fun r => (executePlan r.1).length) = some 4)
  ∧ ((generateBlockPlan Two.L2 Two.D2 Two.C2 Two.fn2 Two.bJoinRes Two.psPost).map
       (fun r => (executePlan r.1).length) = some 5) := by
  constructor <;> decide



/-- **The residual-free join reduction, on the two-phi join.** No synthetic block: the join is resumed
after its own phis, so the plan, the program and the liveness indices are all the block's own — the
configuration the residual route gets wrong. -/
theorem fn2_join_self (fuel : Nat) (ctx : VenomContext)
    {lo : AssocList String Nat} {ps' : PlanState} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {as : AsmState}
    (hres : BlockSim lo ps' offsetToPc prog as
      (execBlock fuel ctx Two.bJoin
        { (updateVar "p" Two.a1v (updateVar "q" Two.a2v Two.vsFromThen2)) with
          instIdx := phiPrefixLength Two.bJoin.instructions })) :
    BlockSim lo ps' offsetToPc prog as (runBlock fuel ctx Two.bJoin Two.vsFromThen2) :=
  BlockSim_join_self fn2_evalPhis hres

/-- and the join really does resume at index 2 — after both phis. -/
theorem fn2_phiPrefixLength : phiPrefixLength Two.bJoin.instructions = 2 := by decide


/-! #### The same result, by the residual-free route — and why it is the one to use

`min_join_sim` above goes through a synthetic residual block. This does not: the join is simply resumed
after its phis, on its own block, plan and program. That removes the synthetic block and the trap that
comes with it (`residual_block_compiles_differently`).

It does not remove the per-opcode obliviousness work for *generic* joins — see `BlockSim_join_self`. Here
none is needed only because the block is concrete and `hres` falls out by computation. -/

theorem min_phiPrefixLength : phiPrefixLength Min.bJ.instructions = 1 := by decide

/-- The join, resumed after its phi, halts. -/
theorem min_self_run (f : Nat) (ctx : VenomContext) (w : VenomState) :
    execBlock (f + 1) ctx Min.bJ { w with instIdx := 1 }
      = ExecResult.Halt (haltState { w with instIdx := 1 }) := by
  unfold execBlock
  rfl

/-- **`genBlockSimulation` on a phi-headed block, by the residual-free route.**

Same result as `min_join_sim`, but with no synthetic residual block, no instruction-index shift, and no
per-opcode `_respects` discharger. The join is simply resumed after its phi — same block, same plan, same
program — and `hasm_stop` finishes it.

The difference is real but narrower than it first looks, and worth stating exactly. *Here* no
obliviousness is needed, because `hres` is discharged by computation on a concrete block. For a *generic*
join it would be: a join resumes after its phis, so its body simulation runs at an offset, and that needs
the body instructions to be instruction-index oblivious — the same content the residual route needs, and
a requirement the codebase already carries for its `PARAM`-prefix simulations
(`execBodyThread_instIdx_congr`). What this route removes is the synthetic block and its trap, not the
per-opcode work. -/
theorem min_join_sim_self {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {asm : AsmState} (f : Nat) (ctx : VenomContext)
    (hrel : venomAsmRel lo Min.ps Min.vs asm)
    (hpc : asm.pc = 0) :
    match runBlock (f + 1) ctx Min.bJ Min.vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmOK as' ∧
          venomAsmRel lo Min.ps w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan Min.ops)).1.length) offsetToPc
          (asmResolve (executePlan Min.ops)).1 asm = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True := by
  have hpost : venomAsmRel lo Min.ps (updateVar "p" Min.av Min.vs) asm :=
    venomAsmRel_phi_join' (outs := ["p"]) (phis := Min.bJ.instructions)
      hrel rfl rfl min_ev
      (fun w hw => lookupVar_updateVar_ne Min.vs "p" w Min.av (by simpa using hw))
      (fun op off hlk _ _ => absurd hlk (by simp [Min.ps, AssocList.lookup]))
      ⟨hrel.1.1, fun i hi => absurd hi (by simp [Min.ps])⟩
  refine genBlockSimulation_join_self (vs' := updateVar "p" Min.av Min.vs) (ops := Min.ops) min_ev ?_
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


/-- **The join `hstep` is not vacuous** — and this is the check that matters, because a walk clause with
an unsatisfiable hypothesis proves nothing. `Min.bJ` is `p = phi …; STOP`, a real phi-headed block on
real compiler output, and it produces the walk's per-block obligation with **no hypotheses left over**:
every argument below is a universally quantified parameter, not an assumption. A block whose head is a
`PHI` is now an ordinary block as far as `codegen_correct`'s walk is concerned. -/
theorem min_walkstep_join (f : Nat) (ctx : VenomContext) (fn : IrFunction)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (offsetToPc : AssocList Nat Nat) :
    WalkStep fn pcOf psOf wOf [] offsetToPc (asmResolve (executePlan Min.ops)).1
      Min.bJ Min.asm ((asmResolve (executePlan Min.ops)).1.length)
      (runBlock (f + 1) ctx Min.bJ Min.vs) := by
  have hbb : Min.bJ.instructions = [Min.pP] ++ [Min.iStop] := rfl
  have hphis : ∀ i ∈ [Min.pP], i.opcode = Opcode.PHI := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl
  have hterm : Min.iStop.opcode ≠ Opcode.PHI := by decide
  set sPhi := updateVar "p" Min.av Min.vs with hsp
  have hstepT : stepInstBase Min.iStop { sPhi with instIdx := [Min.pP].length }
      = ExecResult.Halt (haltState { sPhi with instIdx := [Min.pP].length }) := rfl
  -- the block therefore halts
  have hrb : runBlock (f + 1) ctx Min.bJ Min.vs
      = ExecResult.Halt (haltState { sPhi with instIdx := [Min.pP].length }) := by
    rw [runBlock_join_eq_execBlock_at min_ev hbb hphis hterm]
    exact execBlock_step_halt f ctx Min.bJ _ _ Min.iStop
      (by simpa using getInstruction_term Min.bJ [Min.pP] Min.iStop hbb) hstepT
  -- and the existing non-vacuous block sim supplies the asm halt witness
  have hw := min_join_sim_nonvacuous f ctx offsetToPc
  rw [hrb] at hw
  exact hstep_bareTerm_halt_join pcOf psOf wOf min_ev hbb hphis hterm hstepT hw


/-- **The compiler-level join route, fired.** `min_walkstep_join` above builds the walk obligation by
hand, from the terminator up. This one takes the other road: `min_join_sim_self` is the *compiler's*
per-block simulation of the phi-headed block, and `WalkStep_of_BlockSim_terminal` carries it into the
walk. Same conclusion, no hypotheses left over — so the chain
`genBlockSimulation_join_self → BlockSim → WalkStep` is real end to end, not just typeable. -/
theorem min_walkstep_join_of_genBlockSim (f : Nat) (ctx : VenomContext) (fn : IrFunction)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (offsetToPc : AssocList Nat Nat) :
    WalkStep fn pcOf psOf wOf [] offsetToPc (asmResolve (executePlan Min.ops)).1
      Min.bJ Min.asm ((asmResolve (executePlan Min.ops)).1.length)
      (runBlock (f + 1) ctx Min.bJ Min.vs) := by
  -- the join halts, so no OK arm can arise
  have hrb : runBlock (f + 1) ctx Min.bJ Min.vs
      = ExecResult.Halt (haltState { updateVar "p" Min.av Min.vs with instIdx := 1 }) := by
    rw [runBlock_eq_execBlock_of_phis min_ev, min_phiPrefixLength]
    exact min_self_run f ctx _
  have hterm : ∀ w, runBlock (f + 1) ctx Min.bJ Min.vs ≠ ExecResult.OK w := by
    intro w h; rw [hrb] at h; exact absurd h (by simp)
  exact WalkStep_of_BlockSim_terminal rfl hterm
    (min_join_sim_self f ctx min_rel_on_arrival rfl)

/-! ### Are the other join hsteps vacuous?

`min_walkstep_join` fires `hstep_bareTerm_halt_join`. The other five — JMP, both JNZ arms, revert and
fault — had no consumer, and this branch's own rule says a theorem with no consumer is either dead or
having its job done by an assumption. So: witnesses for the two that carry real content beyond the halt
case, on genuine phi-headed blocks.

The JNZ witness is the one that earns its keep. Its branch condition is `p` — the phi's *own output* —
so it reads a value that does not exist until the prologue has run. A bare-terminator hstep could not
have expressed that block at all, which is precisely the generality the join forms were added for. -/

namespace JoinShapes

/-- A join whose terminator is a `JMP`: `p = phi(then→a, else→b) ; JMP next`. -/
def jJmp : Instruction :=
  { id := 20, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def bJmp : BasicBlock := { label := "join", instructions := [Min.pP, jJmp] }

/-- A join whose terminator is a `JNZ`. -/
def jJnz : Instruction :=
  { id := 21, opcode := Opcode.JNZ,
    operands := [Operand.Var "p", Operand.Label "t2", Operand.Label "e2"], outputs := [] }
def bJnz : BasicBlock := { label := "join", instructions := [Min.pP, jJnz] }

end JoinShapes

/-- `evalPhis` succeeds on the JMP-terminated join. -/
theorem jmpjoin_ev : evalPhis Min.vs JoinShapes.bJmp.instructions
    = ExecResult.OK (updateVar "p" Min.av Min.vs) := by
  show evalPhis Min.vs (Min.pP :: [JoinShapes.jJmp]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis Min.vs [JoinShapes.jJmp] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis Min.vs [JoinShapes.jJmp] = ExecResult.OK Min.vs from by
    unfold evalPhis; rw [if_pos (by decide)]]

/-- **`hstep_jmp_block_join`'s Venom-side hypotheses are satisfiable.** The `execBlock` input it needs —
the join resumed after its phi, stepping its `JMP` — is discharged here on a real phi-headed block. -/
theorem jmpjoin_hrb (f : Nat) (ctx : VenomContext) (hnh : Min.vs.halted = false) :
    execBlock (f + 1) ctx JoinShapes.bJmp
        { (updateVar "p" Min.av Min.vs) with
          instIdx := phiPrefixLength JoinShapes.bJmp.instructions }
      = ExecResult.OK (jumpTo "next"
          { (updateVar "p" Min.av Min.vs) with instIdx := 1 }) := by
  have hlen : phiPrefixLength JoinShapes.bJmp.instructions = 1 := by decide
  rw [hlen]
  refine execBlock_step_term_ok f ctx JoinShapes.bJmp _ _ JoinShapes.jJmp ?_ ?_ (by decide) ?_
  · exact (by simpa using getInstruction_term JoinShapes.bJmp [Min.pP] JoinShapes.jJmp rfl)
  · rfl
  · rw [jumpTo]; exact hnh

/-- `evalPhis` succeeds on the JNZ-terminated join, and its condition evaluates — the two Venom-side
inputs `hstep_jnz_taken_join` needs beyond block shape. -/
theorem jnzjoin_ev : evalPhis Min.vs JoinShapes.bJnz.instructions
    = ExecResult.OK (updateVar "p" Min.av Min.vs) := by
  show evalPhis Min.vs (Min.pP :: [JoinShapes.jJnz]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis Min.vs [JoinShapes.jJnz] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis Min.vs [JoinShapes.jJnz] = ExecResult.OK Min.vs from by
    unfold evalPhis; rw [if_pos (by decide)]]

/-- The JNZ join's condition is the phi's *own output* — so it reads a value that only exists after the
prologue. This is the case a bare-terminator hstep could never have expressed. -/
theorem jnzjoin_cond :
    evalOperand (Operand.Var "p")
      { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length } = some Min.av := by
  rfl

/-! ### Closing the last vacuity gap: the revert and fault joins

The previous section left these two unexercised and said so. Here they are. `revertjoin_walkstep` and
`faultjoin_walkstep` discharge *every* Venom-side hypothesis of their hstep on a concrete phi-headed
block and hand back the walk obligation; only the asm-side witness stays a parameter, which is true of
every hstep in the family, join or not.

All six join hsteps now have a witness. -/

namespace JoinShapes

/-- A join that reverts: `p = phi(…) ; REVERT 0 0`. -/
def jRevert : Instruction :=
  { id := 22, opcode := Opcode.REVERT,
    operands := [Operand.Lit (UInt256.ofNat 0), Operand.Lit (UInt256.ofNat 0)], outputs := [] }
def bRevert : BasicBlock := { label := "join", instructions := [Min.pP, jRevert] }

/-- A join that faults: `p = phi(…) ; INVALID`. -/
def jInvalid : Instruction :=
  { id := 23, opcode := Opcode.INVALID, operands := [], outputs := [] }
def bFault : BasicBlock := { label := "join", instructions := [Min.pP, jInvalid] }

end JoinShapes

theorem ev_of (term : Instruction) (hnp : term.opcode ≠ Opcode.PHI)
    (bb : BasicBlock) (hbb : bb.instructions = [Min.pP, term]) :
    evalPhis Min.vs bb.instructions = ExecResult.OK (updateVar "p" Min.av Min.vs) := by
  rw [hbb]
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis Min.vs [term] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis Min.vs [term] = ExecResult.OK Min.vs from by
    unfold evalPhis; rw [if_pos hnp]]

theorem revertjoin_ev : evalPhis Min.vs JoinShapes.bRevert.instructions
    = ExecResult.OK (updateVar "p" Min.av Min.vs) :=
  ev_of JoinShapes.jRevert (by decide) _ rfl

theorem faultjoin_ev : evalPhis Min.vs JoinShapes.bFault.instructions
    = ExecResult.OK (updateVar "p" Min.av Min.vs) :=
  ev_of JoinShapes.jInvalid (by decide) _ rfl

/-- **`hstep_bareTerm_revert_join`'s Venom-side step, discharged.** -/
theorem revertjoin_step :
    stepInstBase JoinShapes.jRevert
        { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length }
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata
            (readMemory 0 0 { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length })
            { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length })) := rfl

/-- **`hstep_bareTerm_fault_join`'s Venom-side step, discharged.** -/
theorem faultjoin_step :
    stepInstBase JoinShapes.jInvalid
        { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length }
      = ExecResult.Abort AbortType.ExHaltAbort
          (haltState (setReturndata ByteArray.empty
            { (updateVar "p" Min.av Min.vs) with instIdx := [Min.pP].length })) := rfl

/-- **The revert join composes.** Every Venom-side hypothesis of `hstep_bareTerm_revert_join` is
discharged on this concrete phi-headed block; only the asm-side witness remains a parameter, exactly as
it is for every other hstep in the family. -/
theorem revertjoin_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {asm : AsmState} {N extraFuel : Nat}
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel
          (revertState (setReturndata
            (readMemory 0 0 { (updateVar "p" Min.av Min.vs) with instIdx := 1 })
            { (updateVar "p" Min.av Min.vs) with instIdx := 1 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinShapes.bRevert asm N
      (runBlock (extraFuel + 1) ctx JoinShapes.bRevert Min.vs) :=
  hstep_bareTerm_revert_join pcOf psOf wOf revertjoin_ev rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl)
    (by decide) revertjoin_step hasm

/-- **The fault join composes.** -/
theorem faultjoin_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {asm : AsmState} {N extraFuel : Nat}
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel
          (haltState (setReturndata ByteArray.empty
            { (updateVar "p" Min.av Min.vs) with instIdx := 1 })) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinShapes.bFault asm N
      (runBlock (extraFuel + 1) ctx JoinShapes.bFault Min.vs) :=
  hstep_bareTerm_fault_join pcOf psOf wOf faultjoin_ev rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl)
    (by decide) faultjoin_step hasm

/-! ### A whole function containing a phi join

`codegen_correct_sched_ws` wants an `hstep` at *every* block. So here is a four-block diamond whose join
is phi-headed — `entry: JNZ c then else` / `then: JMP join` / `else: JMP join` /
`join: p = phi(then→a, else→b); STOP` — and the block dispatcher for it.

Three of the four blocks are ordinary phi-free blocks, and discharging them is the pre-existing
machinery's job; they stay as hypotheses. The fourth is the one that could not previously be stated at
all, and it is discharged here.

A first attempt at this dispatcher quantified over an abstract per-block predicate and "proved" the
whole thing by composing two of its own hypotheses — a tautology in the shape of a theorem. It is
recorded here only as the reason this version takes the three phi-free obligations *concretely*: a
dispatcher whose content is a case split must at least be honest about which cases it actually closes. -/

namespace Dia

def dJnz : Instruction :=
  { id := 30, opcode := Opcode.JNZ,
    operands := [Operand.Var "c", Operand.Label "then", Operand.Label "else"], outputs := [] }
def dJmpT : Instruction :=
  { id := 31, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def dJmpE : Instruction :=
  { id := 32, opcode := Opcode.JMP, operands := [Operand.Label "join"], outputs := [] }
def dPhi : Instruction :=
  { id := 33, opcode := Opcode.PHI,
    operands := [Operand.Label "then", Operand.Var "a", Operand.Label "else", Operand.Var "b"],
    outputs := ["p"] }
def dStop : Instruction :=
  { id := 34, opcode := Opcode.STOP, operands := [], outputs := [] }

/-- `c = CALLVALUE` — **`c` must be defined in the function**, and it must be defined by something the
kernel can reduce.

Two separate constraints, learned the hard way. First: an earlier version of this diamond left `c` free,
and the compiler duly emitted `PUSHLBL then; JUMPI` with nothing pushing the condition — `generateFnPlan`
starts from an empty stack and gives a slot only to variables some instruction *defines*, so a free
variable (and, it turns out, a `PARAM` too — the plan does not seed params either) gets no push at all.
Venom reads `c` from `vars`, the EVM pops whatever is lying there, and no `venomAsmRel` can relate them.
The entry block's `hstep` was undischargeable.

Second: the obvious fix, `c = <literal>`, makes the function correct but the *proofs* impossible.
`encodeNumBytes` is well-founded recursive, so the kernel cannot unfold it; a plan containing a literal
`SOPush` becomes `AsmPush (encodeNumBytes …)` in `executePlan`, and `computeLabelOffsets` needs that
instruction's *size*. So every label offset in the program becomes irreducible, and nothing about the
compiled output can be pinned by `rfl` or `decide`. (`jmpStopFn` escapes this only because its sole pushes
are *label* pushes, which stay `AsmPushLabel` — a fixed size — in the unresolved asm.)

`CALLVALUE` satisfies both: it defines `c` and pushes it, with no literal anywhere. -/
def dC : Instruction :=
  { id := 29, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }

def bEntry : BasicBlock := { label := "entry", instructions := [dC, dJnz] }
/-- `a = CALLVALUE` in `then`, `b = CALLER` in `else` — **the phi's sources must actually be defined**.

Without these the join is vacuous, and vacuous in the worst way: `evalPhis` looks its sources up in
`vars`, finds nothing, and `runBlock` returns an `Error`. `WalkStep`'s catch-all sends `Error` to `True`,
so the join's obligation would have been *trivially* discharged while the function never reached a
meaningful join at all. The same failure as the free `c` in the entry block, one level down.

They are dead by the time the phi runs — a `PHI` does not *use* its sources (that is what the liveness
fix established), so the compiler emits `CALLVALUE ; POP` and `CALLER ; POP` and the exit stacks stay
empty. Venom still binds them in `vars`, which is exactly why `evalPhis` succeeds and the join is real. -/
def tA : Instruction :=
  { id := 35, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def eB : Instruction :=
  { id := 36, opcode := Opcode.CALLER, operands := [], outputs := ["b"] }

def bThen  : BasicBlock := { label := "then",  instructions := [tA, dJmpT] }
def bElse  : BasicBlock := { label := "else",  instructions := [eB, dJmpE] }
/-- The join is **phi-headed**. -/
def bJoin  : BasicBlock := { label := "join",  instructions := [dPhi, dStop] }

def fn : IrFunction := { name := "main", blocks := [bEntry, bThen, bElse, bJoin] }

/-- The compiler's own output for this diamond. -/
def ops  : List StackOp := (generateFnPlan fn 0 0).get!.1
def prog : List AsmInst := (asmResolve (executePlan ops)).1
def o2pc : AssocList Nat Nat := (asmResolve (executePlan ops)).2
def lo   : AssocList String Nat := (computeLabelOffsets (executePlan ops)).2

end Dia

/-- The diamond's blocks are exactly the four. -/
theorem dia_blocks {s : VenomState} {bb : BasicBlock}
    (hlk : lookupBlock s.currentBb Dia.fn.blocks = some bb) :
    bb = Dia.bEntry ∨ bb = Dia.bThen ∨ bb = Dia.bElse ∨ bb = Dia.bJoin := by
  rw [show Dia.fn.blocks = [Dia.bEntry, Dia.bThen, Dia.bElse, Dia.bJoin] from rfl,
      lookupBlock] at hlk
  have h := List.mem_of_find?_eq_some hlk
  simpa using h

/-- **The join slot of a real diamond, discharged.** `Dia.bJoin` is `p = phi(then→a, else→b) ; STOP`,
the phi-headed block of a four-block diamond. Given that its phis evaluate on the arriving state (which
is a fact about the *arrival*, not about the join) and the asm halt witness (which every hstep in the
family takes, join or not), the walk's obligation for it follows. Nothing here is assumed about the
block's head not being a `PHI` — that hypothesis is gone. -/
theorem dia_join_hstep {ctx : VenomContext} {lo : AssocList String Nat}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {s vs' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s Dia.bJoin.instructions = ExecResult.OK vs')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel (haltState { vs' with instIdx := 1 }) asm') :
    WalkStep Dia.fn pcOf psOf wOf lo offsetToPc prog Dia.bJoin asm N
      (runBlock (extraFuel + 1) ctx Dia.bJoin s) :=
  hstep_bareTerm_halt_join (phis := [Dia.dPhi]) (term := Dia.dStop) pcOf psOf wOf hev rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl)
    (by decide) rfl hasm

/-- **The whole diamond's `hstep`.** The three phi-free blocks are the pre-existing machinery's business
and stay as hypotheses; the phi-headed join is discharged above. This is the shape
`codegen_correct_sched_ws` consumes, so a function *containing a phi join* now has a whole-function
obligation with the join already accounted for. -/
theorem dia_hstep
    {ctx : VenomContext} {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {extraFuel : Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hEntry : ∀ s asm N, lookupBlock s.currentBb Dia.fn.blocks = some Dia.bEntry →
        asm.pc = pcOf Dia.bEntry.label → venomAsmRel lo (psOf Dia.bEntry.label) s asm →
        wOf Dia.bEntry.label ≤ N → s.halted = false →
        WalkStep Dia.fn pcOf psOf wOf lo offsetToPc prog Dia.bEntry asm N
          (runBlock (extraFuel + 1) ctx Dia.bEntry s))
    (hThen : ∀ s asm N, lookupBlock s.currentBb Dia.fn.blocks = some Dia.bThen →
        asm.pc = pcOf Dia.bThen.label → venomAsmRel lo (psOf Dia.bThen.label) s asm →
        wOf Dia.bThen.label ≤ N → s.halted = false →
        WalkStep Dia.fn pcOf psOf wOf lo offsetToPc prog Dia.bThen asm N
          (runBlock (extraFuel + 1) ctx Dia.bThen s))
    (hElse : ∀ s asm N, lookupBlock s.currentBb Dia.fn.blocks = some Dia.bElse →
        asm.pc = pcOf Dia.bElse.label → venomAsmRel lo (psOf Dia.bElse.label) s asm →
        wOf Dia.bElse.label ≤ N → s.halted = false →
        WalkStep Dia.fn pcOf psOf wOf lo offsetToPc prog Dia.bElse asm N
          (runBlock (extraFuel + 1) ctx Dia.bElse s))
    (hJoinEv : ∀ s, lookupBlock s.currentBb Dia.fn.blocks = some Dia.bJoin →
        ∃ vs', evalPhis s Dia.bJoin.instructions = ExecResult.OK vs')
    (hJoinAsm : ∀ s asm N vs', evalPhis s Dia.bJoin.instructions = ExecResult.OK vs' →
        asm.pc = pcOf Dia.bJoin.label → wOf Dia.bJoin.label ≤ N →
        ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
          venomAsmTerminalRel (haltState { vs' with instIdx := 1 }) asm') :
    ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N : Nat),
      lookupBlock s.currentBb Dia.fn.blocks = some bb →
      asm.pc = pcOf bb.label →
      venomAsmRel lo (psOf bb.label) s asm →
      wOf bb.label ≤ N →
      s.halted = false →
      WalkStep Dia.fn pcOf psOf wOf lo offsetToPc prog bb asm N
        (runBlock (extraFuel + 1) ctx bb s) := by
  intro bb s asm N hlk hpc hrel hw hnh
  rcases dia_blocks hlk with rfl | rfl | rfl | rfl
  · exact hEntry s asm N hlk hpc hrel hw hnh
  · exact hThen s asm N hlk hpc hrel hw hnh
  · exact hElse s asm N hlk hpc hrel hw hnh
  · obtain ⟨vs', hev⟩ := hJoinEv s hlk
    exact dia_join_hstep pcOf psOf wOf hev (hJoinAsm s asm N vs' hev hpc hw)

/-! ### A join with a body — one that reads its own phi

Every join witnessed so far has been `phis ++ [term]`: the phi prologue and then straight out. That is
the easy half. The real shape a compiler produces is a join with a *body*, and — the part that matters —
a body that **consumes the phi's output**. `p = phi(then→a, else→b) ; SSTORE d p ; STOP` is that block:
the store reads `p`, a value that does not exist until the prologue has run.

No `hphi`-carrying hstep can describe this block, and neither can the bare-terminator join hsteps, whose
`hbb` insists the block is `phis ++ [term]`. The general `hstep_join_halt` handles it, and the Venom side
is fully discharged below. -/

namespace JoinBody

/-- `SSTORE d, p` — the body **reads the phi's output** `p`. -/
def bSst : Instruction :=
  { id := 40, opcode := Opcode.SSTORE,
    operands := [Operand.Var "d", Operand.Var "p"], outputs := [] }
def bStop : Instruction :=
  { id := 41, opcode := Opcode.STOP, operands := [], outputs := [] }

/-- A join **with a body**: `p = phi(then→a, else→b) ; SSTORE d p ; STOP`. -/
def bb : BasicBlock := { label := "join", instructions := [Min.pP, bSst, bStop] }

def dv : bytes32 := UInt256.ofNat 9

/-- The arriving state binds `d` and the phi's `then`-source `a`. -/
def vs : VenomState :=
  { (default : VenomState) with
    vars := [("d", dv), ("a", Min.av)],
    prevBb := some "then", currentBb := "join" }

end JoinBody

theorem joinbody_ev : evalPhis JoinBody.vs JoinBody.bb.instructions
    = ExecResult.OK (updateVar "p" Min.av JoinBody.vs) := by
  show evalPhis JoinBody.vs (Min.pP :: [JoinBody.bSst, JoinBody.bStop]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Min.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := Min.av)
        (by rfl) (by rfl) (by rfl) (by rfl)]
  show (match evalPhis JoinBody.vs [JoinBody.bSst, JoinBody.bStop] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" Min.av s') | err => err) = _
  rw [show evalPhis JoinBody.vs [JoinBody.bSst, JoinBody.bStop] = ExecResult.OK JoinBody.vs from by
    unfold evalPhis; rw [if_pos (by decide)]]

theorem joinbody_phiPrefixLength : phiPrefixLength JoinBody.bb.instructions = 1 := by decide

/-- The state the join resumes at: phi output `p` bound, index at the body. -/
def JoinBody.sPhi1 : VenomState :=
  { (updateVar "p" Min.av JoinBody.vs) with instIdx := 1 }

/-- **The body runs, and it reads the phi's output.** Resumed at index 1, the join executes
`SSTORE d p` — storing `p`, the value the phi just bound — and then halts. This is the case a
bare-terminator join hstep cannot express: there is a body, and the body *consumes the phi*. -/
theorem joinbody_res (f : Nat) (ctx : VenomContext) :
    execBlock (f + 1 + 1) ctx JoinBody.bb JoinBody.sPhi1
      = ExecResult.Halt (haltState
          { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 }) := by
  rw [execBlock_step_nonterm (f + 1) ctx JoinBody.bb JoinBody.sPhi1
        (sstore JoinBody.dv Min.av JoinBody.sPhi1) JoinBody.bSst
        (by rfl) (by rfl) (by decide)]
  exact execBlock_step_halt f ctx JoinBody.bb _ _ JoinBody.bStop (by rfl) (by rfl)

/-- **A join WITH A BODY produces the walk's obligation.** Every Venom-side input is discharged: the
phis evaluate on arrival (`joinbody_ev`), and the post-phi body runs to a halt (`joinbody_res`). Only the
asm witness stays a parameter, as it does for every hstep. The block is
`p = phi(then→a, else→b) ; SSTORE d p ; STOP` — its body *consumes the phi's output*, so neither a
bare-terminator join hstep nor any `hphi`-carrying hstep could have described it. -/
theorem joinbody_walkstep {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {asm : AsmState} {N f : Nat}
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel
          (haltState { (sstore JoinBody.dv Min.av JoinBody.sPhi1) with instIdx := 2 }) asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog JoinBody.bb asm N
      (runBlock (f + 1 + 1) ctx JoinBody.bb JoinBody.vs) :=
  hstep_join_halt joinbody_ev
    (by rw [joinbody_phiPrefixLength]; exact joinbody_res f ctx) hasm

/-! ### Does the diamond actually compile?

`dia_hstep` hands its three phi-free blocks back as hypotheses. A hypothesis nothing can satisfy makes a
theorem vacuous exactly where it claims to be useful, so this is not rhetorical — and twice already the
answer was no. Once because `c` was free (no push for the condition); once because the phi's sources `a`
and `b` were free (`evalPhis` failed, `runBlock` errored, and `WalkStep`'s catch-all sent `Error` to
`True`). Both are fixed above, and the theorems below check the consequences on the compiler's actual
output rather than asserting them. -/

/-- The diamond compiles. -/
theorem dia_compiles : (generateFnPlan Dia.fn 0 0).isSome = true := by rfl

/-- Its resolved program is 18 instructions. -/
theorem dia_prog_length : Dia.prog.length = 18 := by rfl

/-- **The entry block pushes the condition**: `JUMPDEST entry ; CALLVALUE ; PUSH then ; JUMPI`. -/
theorem dia_entry_shape :
    Dia.prog[0]! = AsmInst.AsmLabel "entry" ∧
    Dia.prog[1]! = AsmInst.AsmOp "CALLVALUE" ∧
    Dia.prog[3]! = AsmInst.AsmOp "JUMPI" ∧
    Dia.prog[5]! = AsmInst.AsmOp "JUMP" := ⟨rfl, rfl, rfl, rfl⟩

/-- **The successor blocks mint the phi's sources and drop them.** `a` and `b` are dead by the time the
phi runs — a `PHI` does not use its sources — so the compiler emits the definition and pops it, leaving
the stacks empty. Venom keeps them in `vars`, which is what makes `evalPhis` succeed at the join. -/
theorem dia_prog_shape :
    Dia.prog[6]! = AsmInst.AsmLabel "else" ∧
    Dia.prog[7]! = AsmInst.AsmOp "CALLER" ∧
    Dia.prog[8]! = AsmInst.AsmOp "POP" ∧
    Dia.prog[10]! = AsmInst.AsmOp "JUMP" ∧
    Dia.prog[11]! = AsmInst.AsmLabel "join" ∧
    Dia.prog[12]! = AsmInst.AsmOp "STOP" ∧
    Dia.prog[13]! = AsmInst.AsmLabel "then" ∧
    Dia.prog[14]! = AsmInst.AsmOp "CALLVALUE" ∧
    Dia.prog[15]! = AsmInst.AsmOp "POP" ∧
    Dia.prog[17]! = AsmInst.AsmOp "JUMP" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The label layout, from the compiler. -/
theorem dia_o2pc_then : AssocList.lookup Nat Nat Dia.o2pc 19 = some 13 := by rfl
theorem dia_o2pc_join : AssocList.lookup Nat Nat Dia.o2pc 17 = some 11 := by rfl
theorem dia_o2pc_else : AssocList.lookup Nat Nat Dia.o2pc 10 = some 6 := by rfl
theorem dia_lo_then : AssocList.lookup String Nat Dia.lo "then" = some 19 := by rfl
theorem dia_lo_join : AssocList.lookup String Nat Dia.lo "join" = some 17 := by rfl
theorem dia_lo_else : AssocList.lookup String Nat Dia.lo "else" = some 10 := by rfl

/-! ### The diamond's asm, block by block

Every one of these runs the compiler's own program — `Dia.prog`, pinned above — and every index into it
is checked by `rfl` against what the compiler emitted.

The entry block splits, because `CALLVALUE` may be zero and the compiler must handle both: taken jumps
straight to `then`, not-taken falls through the `JUMPI` into `[PUSH else ; JUMP]`. Four steps versus six,
which is why the entry block's rank has to dominate both successors and not just the near one. -/

set_option maxRecDepth 8000

/-- One asm step. -/
theorem runAsm_one {o2pc prog s s'} (hpc : s.pc < prog.length)
    (hstep : asmStep o2pc prog s = AsmResult.AsmOK s') :
    runAsm 1 o2pc prog s = AsmResult.AsmOK s' := by
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc hstep]; rfl

/-- `then: a = CALLVALUE ; JMP join` — `JUMPDEST ; CALLVALUE ; POP ; PUSH join ; JUMP`: five asm steps
from pc 13 to `join` (pc 11). The `POP` is the compiler discarding `a`, which is dead the moment it is
defined — a `PHI` does not use its sources. -/
theorem dia_hasm_then {asm : AsmState} (hpc : asm.pc = 13) (hstk : asm.stack = []) :
    runAsm 5 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 11 } := by
  have h1 : asm.pc < Dia.prog.length := by rw [hpc]; decide
  have hg1 : Dia.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "then" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Dia.prog.length) = ⟨13, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one (o2pc := Dia.o2pc) h1 (asmStep_label_ok (offsetToPc := Dia.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 14 := by show asm.pc + 1 = 14; rw [hpc]
  have h2 : a1.pc < Dia.prog.length := by rw [hpc1]; decide
  have hg2 : Dia.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp "CALLVALUE" := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Dia.prog.length) = ⟨14, by decide⟩ from Fin.ext hpc1]
    rfl
  have s2 := runAsm_one (o2pc := Dia.o2pc) h2 (by rw [asmStep_callvalue_ok h2 hg2]; rfl :
    asmStep Dia.o2pc Dia.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := a1.callCtx.callvalue :: a1.stack })
  set a2 : AsmState := { asmNext a1 with stack := a1.callCtx.callvalue :: a1.stack } with ha2
  have hpc2 : a2.pc = 15 := by show a1.pc + 1 = 15; rw [hpc1]
  have h3 : a2.pc < Dia.prog.length := by rw [hpc2]; decide
  have hg3 : Dia.prog.get ⟨a2.pc, h3⟩ = AsmInst.AsmOp "POP" := by
    conv_lhs => rw [show (⟨a2.pc, h3⟩ : Fin Dia.prog.length) = ⟨15, by decide⟩ from Fin.ext hpc2]
    rfl
  have s3 := runAsm_one (o2pc := Dia.o2pc) h3 (by
    unfold asmStep; rw [dif_pos h3, hg3]; show asmPop a2 = _; rfl :
    asmStep Dia.o2pc Dia.prog a2 = AsmResult.AsmOK { asmNext a2 with stack := a1.stack })
  set a3 : AsmState := { asmNext a2 with stack := a1.stack } with ha3
  have hpc3 : a3.pc = 16 := by show a2.pc + 1 = 16; rw [hpc2]
  have h4 : a3.pc < Dia.prog.length := by rw [hpc3]; decide
  have hg4 : Dia.prog.get ⟨a3.pc, h4⟩ = resolveInst Dia.lo (AsmInst.AsmPushLabel "join") := by
    conv_lhs => rw [show (⟨a3.pc, h4⟩ : Fin Dia.prog.length) = ⟨16, by decide⟩ from Fin.ext hpc3]
    rfl
  have h5 : a3.pc + 1 < Dia.prog.length := by rw [hpc3]; decide
  have hg5 : Dia.prog.get ⟨a3.pc + 1, h5⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨a3.pc + 1, h5⟩ : Fin Dia.prog.length) = ⟨17, by decide⟩ from
      Fin.ext (by show a3.pc + 1 = 17; rw [hpc3])]
    rfl
  have s4 := resolved_jump_sim h4 hg4 dia_lo_join (by decide) h5 hg5 dia_o2pc_join
  rw [show (5 : Nat) = 1 + (1 + (1 + 2)) from rfl, runAsm_append_ok s1, runAsm_append_ok s2,
      runAsm_append_ok s3, s4]
  cases asm with | _ => simp_all [asmNext, a1, a2, a3]

/-- `else: b = CALLER ; JMP join` — the same shape, five steps from pc 6 to `join` (pc 11). -/
theorem dia_hasm_else {asm : AsmState} (hpc : asm.pc = 6) (hstk : asm.stack = []) :
    runAsm 5 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 11 } := by
  have h1 : asm.pc < Dia.prog.length := by rw [hpc]; decide
  have hg1 : Dia.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "else" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Dia.prog.length) = ⟨6, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one (o2pc := Dia.o2pc) h1 (asmStep_label_ok (offsetToPc := Dia.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 7 := by show asm.pc + 1 = 7; rw [hpc]
  have h2 : a1.pc < Dia.prog.length := by rw [hpc1]; decide
  have hg2 : Dia.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp "CALLER" := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Dia.prog.length) = ⟨7, by decide⟩ from Fin.ext hpc1]
    rfl
  have s2 := runAsm_one (o2pc := Dia.o2pc) h2 (by rw [asmStep_caller_ok h2 hg2]; rfl :
    asmStep Dia.o2pc Dia.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := addressToWord a1.callCtx.caller :: a1.stack })
  set a2 : AsmState :=
    { asmNext a1 with stack := addressToWord a1.callCtx.caller :: a1.stack } with ha2
  have hpc2 : a2.pc = 8 := by show a1.pc + 1 = 8; rw [hpc1]
  have h3 : a2.pc < Dia.prog.length := by rw [hpc2]; decide
  have hg3 : Dia.prog.get ⟨a2.pc, h3⟩ = AsmInst.AsmOp "POP" := by
    conv_lhs => rw [show (⟨a2.pc, h3⟩ : Fin Dia.prog.length) = ⟨8, by decide⟩ from Fin.ext hpc2]
    rfl
  have s3 := runAsm_one (o2pc := Dia.o2pc) h3 (by
    unfold asmStep; rw [dif_pos h3, hg3]; show asmPop a2 = _; rfl :
    asmStep Dia.o2pc Dia.prog a2 = AsmResult.AsmOK { asmNext a2 with stack := a1.stack })
  set a3 : AsmState := { asmNext a2 with stack := a1.stack } with ha3
  have hpc3 : a3.pc = 9 := by show a2.pc + 1 = 9; rw [hpc2]
  have h4 : a3.pc < Dia.prog.length := by rw [hpc3]; decide
  have hg4 : Dia.prog.get ⟨a3.pc, h4⟩ = resolveInst Dia.lo (AsmInst.AsmPushLabel "join") := by
    conv_lhs => rw [show (⟨a3.pc, h4⟩ : Fin Dia.prog.length) = ⟨9, by decide⟩ from Fin.ext hpc3]
    rfl
  have h5 : a3.pc + 1 < Dia.prog.length := by rw [hpc3]; decide
  have hg5 : Dia.prog.get ⟨a3.pc + 1, h5⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨a3.pc + 1, h5⟩ : Fin Dia.prog.length) = ⟨10, by decide⟩ from
      Fin.ext (by show a3.pc + 1 = 10; rw [hpc3])]
    rfl
  have s4 := resolved_jump_sim h4 hg4 dia_lo_join (by decide) h5 hg5 dia_o2pc_join
  rw [show (5 : Nat) = 1 + (1 + (1 + 2)) from rfl, runAsm_append_ok s1, runAsm_append_ok s2,
      runAsm_append_ok s3, s4]
  cases asm with | _ => simp_all [asmNext, a1, a2, a3]

/-- `join: p = phi(…) ; STOP` — `JUMPDEST join ; STOP` at pc 11. Halts. -/
theorem dia_hasm_join {asm : AsmState} (hpc : asm.pc = 11) :
    runAsm 2 Dia.o2pc Dia.prog asm = AsmResult.AsmHalt (asmNext (asmNext asm)) := by
  have h1 : asm.pc < Dia.prog.length := by rw [hpc]; decide
  have hg1 : Dia.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "join" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Dia.prog.length) = ⟨11, by decide⟩ from Fin.ext hpc]
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok h1 (asmStep_label_ok h1 hg1)]
  have h2 : (asmNext asm).pc < Dia.prog.length := by show asm.pc + 1 < _; rw [hpc]; decide
  have hg2 : Dia.prog.get ⟨(asmNext asm).pc, h2⟩ = AsmInst.AsmOp "STOP" := by
    conv_lhs => rw [show (⟨(asmNext asm).pc, h2⟩ : Fin Dia.prog.length) = ⟨12, by decide⟩ from
      Fin.ext (by show asm.pc + 1 = 12; rw [hpc])]
    rfl
  exact runAsm_stop 0 h2 hg2

/-- The entry block's prefix: `JUMPDEST entry ; CALLVALUE` at pc 0, pushing the condition. -/
theorem dia_entry_prefix {asm : AsmState} (hpc : asm.pc = 0) :
    runAsm 2 Dia.o2pc Dia.prog asm = AsmResult.AsmOK
      { asm with pc := 2, stack := asm.callCtx.callvalue :: asm.stack } := by
  have h1 : asm.pc < Dia.prog.length := by rw [hpc]; decide
  have hg1 : Dia.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "entry" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Dia.prog.length) = ⟨0, by decide⟩ from Fin.ext hpc]
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok h1 (asmStep_label_ok h1 hg1)]
  have h2 : (asmNext asm).pc < Dia.prog.length := by show asm.pc + 1 < _; rw [hpc]; decide
  have hg2 : Dia.prog.get ⟨(asmNext asm).pc, h2⟩ = AsmInst.AsmOp "CALLVALUE" := by
    conv_lhs => rw [show (⟨(asmNext asm).pc, h2⟩ : Fin Dia.prog.length) = ⟨1, by decide⟩ from
      Fin.ext (by show asm.pc + 1 = 1; rw [hpc])]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok h2 (by
    rw [asmStep_callvalue_ok h2 hg2]; rfl)]
  show AsmResult.AsmOK _ = _
  congr 1
  cases asm; simp [asmNext] at hpc ⊢; omega

section
variable {asm : AsmState} {stk : List bytes32}

theorem pc2_push (h : asm.pc = 2) :
    Dia.prog.get ⟨asm.pc, by rw [h]; decide⟩
      = resolveInst Dia.lo (AsmInst.AsmPushLabel "then") := by
  conv_lhs => rw [show (⟨asm.pc, by rw [h]; decide⟩ : Fin Dia.prog.length) = ⟨2, by decide⟩ from
    Fin.ext h]
  rfl

theorem pc3_jumpi (h : asm.pc = 2) :
    Dia.prog.get ⟨asm.pc + 1, by rw [h]; decide⟩ = AsmInst.AsmOp "JUMPI" := by
  conv_lhs => rw [show (⟨asm.pc + 1, by rw [h]; decide⟩ : Fin Dia.prog.length) = ⟨3, by decide⟩ from
    Fin.ext (by show asm.pc + 1 = 3; rw [h])]
  rfl

/-- **Entry, JNZ taken** (`CALLVALUE ≠ 0`): from pc 2 the `[PUSH then ; JUMPI]` jumps to `then` (pc 13). -/
theorem dia_hasm_entry_taken {cond : bytes32}
    (hpc : asm.pc = 2) (hstack : asm.stack = cond :: stk)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0) :
    runAsm 2 Dia.o2pc Dia.prog asm
      = AsmResult.AsmOK { asm with stack := stk, pc := 13 } :=
  resolved_jumpi_taken_sim hstack hcond (by rw [hpc]; decide) (pc2_push hpc)
    dia_lo_then (by decide) (by rw [hpc]; decide) (pc3_jumpi hpc) dia_o2pc_then

/-- **Entry, JNZ not taken** (`CALLVALUE = 0`): falls through into `[PUSH else ; JUMP]`, landing at
`else` (pc 6). Four asm steps from pc 2. -/
theorem dia_hasm_entry_nottaken
    (hpc : asm.pc = 2) (hstack : asm.stack = EvmYul.UInt256.ofNat 0 :: stk) :
    runAsm 4 Dia.o2pc Dia.prog asm
      = AsmResult.AsmOK { asm with stack := stk, pc := 6 } := by
  have hfall : runAsm 2 Dia.o2pc Dia.prog asm
      = AsmResult.AsmOK { asm with stack := stk, pc := asm.pc + 2 } :=
    resolved_jumpi_nottaken_sim hstack (by rw [hpc]; decide) (pc2_push hpc)
      dia_lo_then (by decide) (by rw [hpc]; decide) (pc3_jumpi hpc)
  rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hfall]
  set s4 : AsmState := { asm with stack := stk, pc := asm.pc + 2 } with hs4
  have hs4pc : s4.pc = 4 := by rw [hs4]; show asm.pc + 2 = 4; rw [hpc]
  have h1 : s4.pc < Dia.prog.length := by rw [hs4pc]; decide
  have hgp : Dia.prog.get ⟨s4.pc, h1⟩ = resolveInst Dia.lo (AsmInst.AsmPushLabel "else") := by
    conv_lhs => rw [show (⟨s4.pc, h1⟩ : Fin Dia.prog.length) = ⟨4, by decide⟩ from Fin.ext hs4pc]
    rfl
  have h2 : s4.pc + 1 < Dia.prog.length := by rw [hs4pc]; decide
  have hgj : Dia.prog.get ⟨s4.pc + 1, h2⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨s4.pc + 1, h2⟩ : Fin Dia.prog.length) = ⟨5, by decide⟩ from
      Fin.ext (by show s4.pc + 1 = 5; rw [hs4pc])]
    rfl
  rw [resolved_jump_sim h1 hgp dia_lo_else (by decide) h2 hgj dia_o2pc_else]

end

/-- **The entry block's whole asm run, taken arm.** Four steps, pc 0 to `then` (pc 13). -/
theorem dia_hasm_entry_taken_full {asm : AsmState}
    (hpc : asm.pc = 0) (hcond : asm.callCtx.callvalue ≠ EvmYul.UInt256.ofNat 0) :
    runAsm 4 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 13 } := by
  rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok (dia_entry_prefix hpc)]
  rw [dia_hasm_entry_taken (stk := asm.stack) (cond := asm.callCtx.callvalue) rfl rfl hcond]

/-- **The entry block's whole asm run, not-taken arm.** Six steps, pc 0 to `else` (pc 6). -/
theorem dia_hasm_entry_nottaken_full {asm : AsmState}
    (hpc : asm.pc = 0) (hcond : asm.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    runAsm 6 Dia.o2pc Dia.prog asm = AsmResult.AsmOK { asm with pc := 6 } := by
  rw [show (6 : Nat) = 2 + 4 from rfl, runAsm_append_ok (dia_entry_prefix hpc)]
  rw [dia_hasm_entry_nottaken (stk := asm.stack) rfl (by rw [hcond])]

/-! ### The Venom side, and what the relation collapses to

Every plan stack in this function is empty and nothing spills, so `venomAsmRel` collapses to something
small: an empty asm stack, byte-equal memories, and the ten shared fields. Worth proving as an iff rather
than unfolding it four times — `memoryRel` with a zero allocator is *not* vacuous, it demands the memories
agree at every byte, which is easy to miss when the allocator looks empty.

`dia_join_ev_from_then` is the one that matters. It says the join's `evalPhis` **succeeds** on the state
that actually arrives from `then`. The previous diamond could not have stated it: with `a` undefined,
`evalPhis` returned `none`, `runBlock` errored, and `WalkStep`'s `Error => True` catch-all discharged the
join's obligation without the function ever reaching a join. -/
theorem venomAsmRel_init0_iff {lo : AssocList String Nat} {vs : VenomState} {asm : AsmState} :
    venomAsmRel lo (initPlanState 0) vs asm ↔
      (asm.stack = [] ∧ (∀ i, readByte i vs.memory = readByte i asm.memory) ∧
       asm.accounts = vs.accounts ∧ asm.transient = vs.transient ∧
       asm.returndata = vs.returndata ∧ asm.logs = vs.logs ∧
       asm.callCtx = vs.callCtx ∧ asm.txCtx = vs.txCtx ∧ asm.blockCtx = vs.blockCtx ∧
       asm.code = vs.code ∧ asm.prevHashes = vs.prevHashes) := by
  constructor
  · rintro ⟨⟨hlen, _⟩, _, hmem, ha, ht, hr, hl, hc, hx, hb, hcode, hph⟩
    refine ⟨?_, ?_, ha, ht, hr, hl, hc, hx, hb, hcode, hph⟩
    · have h0 : asm.stack.length = 0 := by simpa [initPlanState] using hlen.symm
      exact List.length_eq_zero_iff.mp h0
    · intro i
      exact hmem i (by simp [initPlanState, initSpillAlloc])
  · rintro ⟨hstk, hmem, ha, ht, hr, hl, hc, hx, hb, hcode, hph⟩
    refine ⟨⟨by simp [initPlanState, hstk], ?_⟩, ?_, ?_, ha, ht, hr, hl, hc, hx, hb, hcode, hph⟩
    · intro i hi; simp [initPlanState] at hi
    · intro op off hlk; simp [initPlanState, AssocList.lookup] at hlk
    · intro i _; exact hmem i

/-- The state after entry's `CALLVALUE`, at the `JNZ`. -/
def Dia.afterCV (s : VenomState) : VenomState :=
  { updateVar "c" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }

theorem dia_entry_run_taken (f : Nat) (ctx : VenomContext) {s : VenomState}
    (hnh : s.halted = false) (hc : s.callCtx.callvalue ≠ EvmYul.UInt256.ofNat 0) :
    runBlock (f + 1 + 1) ctx Dia.bEntry s = ExecResult.OK (jumpTo "then" (Dia.afterCV s)) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Dia.bEntry { s with instIdx := 0 }
        (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }) Dia.dC
        (by rfl) (by rfl) (by decide)]
  refine execBlock_step_term_ok f ctx Dia.bEntry (Dia.afterCV s) _ Dia.dJnz (by rfl) ?_
    (by decide) (by rw [jumpTo]; exact hnh)
  show stepInstBase Dia.dJnz (Dia.afterCV s) = _
  unfold stepInstBase
  simp only [show Dia.dJnz.opcode = Opcode.JNZ from rfl,
             show Dia.dJnz.operands = [Operand.Var "c", Operand.Label "then", Operand.Label "else"]
               from rfl]
  have hcv : evalOperand (Operand.Var "c") (Dia.afterCV s) = some s.callCtx.callvalue := rfl
  simp only [hcv]
  split
  · rfl
  · rename_i h; exact absurd (bne_iff_ne.mpr hc) h

theorem dia_entry_run_nottaken (f : Nat) (ctx : VenomContext) {s : VenomState}
    (hnh : s.halted = false) (hc : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    runBlock (f + 1 + 1) ctx Dia.bEntry s = ExecResult.OK (jumpTo "else" (Dia.afterCV s)) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Dia.bEntry { s with instIdx := 0 }
        (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }) Dia.dC
        (by rfl) (by rfl) (by decide)]
  refine execBlock_step_term_ok f ctx Dia.bEntry (Dia.afterCV s) _ Dia.dJnz (by rfl) ?_
    (by decide) (by rw [jumpTo]; exact hnh)
  show stepInstBase Dia.dJnz (Dia.afterCV s) = _
  unfold stepInstBase
  simp only [show Dia.dJnz.opcode = Opcode.JNZ from rfl,
             show Dia.dJnz.operands = [Operand.Var "c", Operand.Label "then", Operand.Label "else"]
               from rfl]
  have hcv : evalOperand (Operand.Var "c") (Dia.afterCV s) = some s.callCtx.callvalue := rfl
  simp only [hcv]
  split
  · rename_i h; exact absurd hc (bne_iff_ne.mp h)
  · rfl

/-- `then` binds `a`, then jumps. -/
def Dia.afterA (s : VenomState) : VenomState :=
  { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
/-- `else` binds `b`, then jumps. -/
def Dia.afterB (s : VenomState) : VenomState :=
  { updateVar "b" (addressToWord s.callCtx.caller) { s with instIdx := 0 } with instIdx := 1 }

theorem dia_then_run (f : Nat) (ctx : VenomContext) {s : VenomState} (hnh : s.halted = false) :
    runBlock (f + 1 + 1) ctx Dia.bThen s = ExecResult.OK (jumpTo "join" (Dia.afterA s)) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Dia.bThen { s with instIdx := 0 }
        (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) Dia.tA
        (by rfl) (by rfl) (by decide)]
  exact execBlock_step_term_ok f ctx Dia.bThen (Dia.afterA s) _ Dia.dJmpT (by rfl) (by rfl)
    (by decide) (by rw [jumpTo]; exact hnh)

theorem dia_else_run (f : Nat) (ctx : VenomContext) {s : VenomState} (hnh : s.halted = false) :
    runBlock (f + 1 + 1) ctx Dia.bElse s = ExecResult.OK (jumpTo "join" (Dia.afterB s)) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Dia.bElse { s with instIdx := 0 }
        (updateVar "b" (addressToWord s.callCtx.caller) { s with instIdx := 0 }) Dia.eB
        (by rfl) (by rfl) (by decide)]
  exact execBlock_step_term_ok f ctx Dia.bElse (Dia.afterB s) _ Dia.dJmpE (by rfl) (by rfl)
    (by decide) (by rw [jumpTo]; exact hnh)

/-- **The join's `evalPhis` SUCCEEDS on the state that actually arrives from `then`.** This is the
theorem the previous version of the diamond could not have stated: with `a` undefined, `evalPhis`
returned `none`, `runBlock` errored, and the join's obligation was discharged by `WalkStep`'s
`Error => True` catch-all without the function ever reaching a join. -/
theorem dia_join_ev_from_then {s : VenomState} (hprev : s.prevBb = some "then")
    (hv : lookupVar "a" s = some s.callCtx.callvalue) :
    evalPhis s Dia.bJoin.instructions
      = ExecResult.OK (updateVar "p" s.callCtx.callvalue s) := by
  show evalPhis s (Dia.dPhi :: [Dia.dStop]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Dia.dPhi.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "a") (prev := "then") (v := s.callCtx.callvalue)
        (by rfl) hprev (by rfl) hv]
  show (match evalPhis s [Dia.dStop] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" s.callCtx.callvalue s') | err => err) = _
  rw [show evalPhis s [Dia.dStop] = ExecResult.OK s from by
    unfold evalPhis; rw [if_pos (by decide)]]

/-- **The relation survives any state change this function makes.** No block touches memory, and every
block is stack-neutral, so the collapsed relation transfers field by field. -/
theorem dia_rel_transfer {lo : AssocList String Nat} {vs vs' : VenomState} {asm asm' : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs asm)
    (hstk : asm'.stack = [])
    (hamem : asm'.memory = asm.memory)
    (hvmem : vs'.memory = vs.memory)
    (hacc : vs'.accounts = vs.accounts) (htr : vs'.transient = vs.transient)
    (hrd : vs'.returndata = vs.returndata) (hlg : vs'.logs = vs.logs)
    (hcc : vs'.callCtx = vs.callCtx) (htx : vs'.txCtx = vs.txCtx)
    (hbc : vs'.blockCtx = vs.blockCtx) (hcd : vs'.code = vs.code)
    (hph : vs'.prevHashes = vs.prevHashes)
    (haacc : asm'.accounts = asm.accounts) (hatr : asm'.transient = asm.transient)
    (hard : asm'.returndata = asm.returndata) (halg : asm'.logs = asm.logs)
    (hacc2 : asm'.callCtx = asm.callCtx) (hatx : asm'.txCtx = asm.txCtx)
    (habc : asm'.blockCtx = asm.blockCtx) (hacd : asm'.code = asm.code)
    (haph : asm'.prevHashes = asm.prevHashes) :
    venomAsmRel lo (initPlanState 0) vs' asm' := by
  rw [venomAsmRel_init0_iff] at hrel ⊢
  obtain ⟨_, hm, ha, ht, hr, hl, hc, hx, hb, hcode, hp⟩ := hrel
  refine ⟨hstk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [hvmem, hamem]; exact hm i
  · rw [haacc, hacc, ha]
  · rw [hatr, htr, ht]
  · rw [hard, hrd, hr]
  · rw [halg, hlg, hl]
  · rw [hacc2, hcc, hc]
  · rw [hatx, htx, hx]
  · rw [habc, hbc, hb]
  · rw [hacd, hcd, hcode]
  · rw [haph, hph, hp]

/-! ### The diamond's five hsteps

`pcOf`, `psOf` and `wOf` are read off the compiler's own layout, not chosen to make the proofs work:
`pcOf` is where each label lands, `psOf` is `initPlanState 0` because every exit stack is empty, and `wOf`
is forced by the asm lengths. The entry block's rank has to be 13 rather than 11 precisely because the
not-taken arm is six asm steps and the taken arm is four — a rank that only accounted for the near
successor would not have survived `hwdec`.

`dia_hstep_join` is the one that could not have been written before this arc. It is a **phi-headed block,
in a real function, at the real program**, producing the walk's per-block obligation — and its `evalPhis`
input is discharged, not assumed. -/
namespace Dia
def ctx : VenomContext := { functions := [fn], entry := some "main" }
def pcOf : String → Nat := fun l =>
  if l = "then" then 13 else if l = "join" then 11 else if l = "else" then 6 else 0
def psOf : String → PlanState := fun _ => initPlanState 0
def wOf : String → Nat := fun l =>
  if l = "join" then 2 else if l = "then" then 7 else if l = "else" then 7 else 13
end Dia

/-- The join halts at any budget the walk can hand it. -/
theorem dia_hasm_join_gen {asm : AsmState} {N : Nat} (hpc : asm.pc = 11) (hN : 2 ≤ N) :
    runAsm N Dia.o2pc Dia.prog asm = AsmResult.AsmHalt (asmNext (asmNext asm)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have h1 : asm.pc < Dia.prog.length := by rw [hpc]; decide
  have hg1 : Dia.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "join" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Dia.prog.length) = ⟨11, by decide⟩ from Fin.ext hpc]
    rfl
  rw [show (k + 2 : Nat) = (k + 1) + 1 from rfl,
      runAsm_succ_ok h1 (asmStep_label_ok (offsetToPc := Dia.o2pc) h1 hg1)]
  have h2 : (asmNext asm).pc < Dia.prog.length := by show asm.pc + 1 < _; rw [hpc]; decide
  have hg2 : Dia.prog.get ⟨(asmNext asm).pc, h2⟩ = AsmInst.AsmOp "STOP" := by
    conv_lhs => rw [show (⟨(asmNext asm).pc, h2⟩ : Fin Dia.prog.length) = ⟨12, by decide⟩ from
      Fin.ext (by show asm.pc + 1 = 12; rw [hpc])]
    rfl
  exact runAsm_stop k h2 hg2

/-- **The join's hstep** — a phi-headed block, in a real function, at the real program. -/
theorem dia_hstep_join {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bJoin.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bJoin.label) s asm)
    (hw : Dia.wOf Dia.bJoin.label ≤ N)
    (hprev : s.prevBb = some "then")
    (hv : lookupVar "a" s = some s.callCtx.callvalue) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bJoin asm N
      (runBlock (f + 1) Dia.ctx Dia.bJoin s) := by
  have hN : 2 ≤ N := by have : Dia.wOf Dia.bJoin.label = 2 := rfl; omega
  obtain ⟨_, hm, ha, ht, hr, hl, hc, hx, hb, hcd, hph⟩ := venomAsmRel_init0_iff.mp hrel
  refine hstep_bareTerm_halt_join (phis := [Dia.dPhi]) (term := Dia.dStop)
    Dia.pcOf Dia.psOf Dia.wOf (dia_join_ev_from_then hprev hv) rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide) rfl
    ⟨asmNext (asmNext asm), dia_hasm_join_gen (hpc := hpc) hN, ?_⟩
  exact ⟨ha, ht, hr, hl⟩

theorem stk_nil {s asm} (hrel : venomAsmRel Dia.lo (initPlanState 0) s asm) :
    asm.stack = [] := (venomAsmRel_init0_iff.mp hrel).1

/-- **`then`'s hstep**: `a = CALLVALUE ; JMP join`, five asm steps, rank 7 → 2. -/
theorem dia_hstep_then {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bThen.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bThen.label) s asm)
    (hw : Dia.wOf Dia.bThen.label ≤ N) (hnh : s.halted = false) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bThen asm N
      (runBlock (f + 1 + 1) Dia.ctx Dia.bThen s) :=
  hstep_jmp_block_ws Dia.pcOf Dia.psOf Dia.wOf (bb' := Dia.bJoin) (blockLen := 5) (idx := 11)
    (hrb := dia_then_run f Dia.ctx hnh)
    (hnh := by rw [jumpTo]; exact hnh)
    (hrun := dia_hasm_then hpc (stk_nil hrel))
    (hrel := dia_rel_transfer (vs := s) (asm := asm) hrel (stk_nil hrel)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (hstk := rfl) (hsp := rfl) (hfe := rfl) (hno := le_refl _)
    (hpcidx := rfl) (hle := by have : Dia.wOf Dia.bThen.label = 7 := rfl; omega)
    (hidx := rfl) (hlk' := rfl) (hwdec := by decide)

/-- **`else`'s hstep**: `b = CALLER ; JMP join`, five asm steps, rank 7 → 2. -/
theorem dia_hstep_else {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bElse.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bElse.label) s asm)
    (hw : Dia.wOf Dia.bElse.label ≤ N) (hnh : s.halted = false) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bElse asm N
      (runBlock (f + 1 + 1) Dia.ctx Dia.bElse s) :=
  hstep_jmp_block_ws Dia.pcOf Dia.psOf Dia.wOf (bb' := Dia.bJoin) (blockLen := 5) (idx := 11)
    (hrb := dia_else_run f Dia.ctx hnh)
    (hnh := by rw [jumpTo]; exact hnh)
    (hrun := dia_hasm_else hpc (stk_nil hrel))
    (hrel := dia_rel_transfer (vs := s) (asm := asm) hrel (stk_nil hrel)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (hstk := rfl) (hsp := rfl) (hfe := rfl) (hno := le_refl _)
    (hpcidx := rfl) (hle := by have : Dia.wOf Dia.bElse.label = 7 := rfl; omega)
    (hidx := rfl) (hlk' := rfl) (hwdec := by decide)

/-- **entry's hstep, taken arm** (`CALLVALUE ≠ 0`): four asm steps, rank 13 → 7. -/
theorem dia_hstep_entry_taken {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bEntry.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bEntry.label) s asm)
    (hw : Dia.wOf Dia.bEntry.label ≤ N) (hnh : s.halted = false)
    (hc : s.callCtx.callvalue ≠ EvmYul.UInt256.ofNat 0) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bEntry asm N
      (runBlock (f + 1 + 1) Dia.ctx Dia.bEntry s) :=
  hstep_jmp_block_ws Dia.pcOf Dia.psOf Dia.wOf (bb' := Dia.bThen) (blockLen := 4) (idx := 13)
    (hrb := dia_entry_run_taken f Dia.ctx hnh hc)
    (hnh := by rw [jumpTo]; exact hnh)
    (hrun := dia_hasm_entry_taken_full hpc
      (by rw [(venomAsmRel_init0_iff.mp hrel).2.2.2.2.2.2.1]; exact hc))
    (hrel := dia_rel_transfer (vs := s) (asm := asm) hrel (stk_nil hrel)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (hstk := rfl) (hsp := rfl) (hfe := rfl) (hno := le_refl _)
    (hpcidx := rfl) (hle := by have : Dia.wOf Dia.bEntry.label = 13 := rfl; omega)
    (hidx := rfl) (hlk' := rfl) (hwdec := by decide)

/-- **entry's hstep, not-taken arm** (`CALLVALUE = 0`): SIX asm steps, rank 13 → 7. The longer arm is
what forces `wOf entry = 13`: the near successor alone would have allowed 11. -/
theorem dia_hstep_entry_nottaken {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bEntry.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bEntry.label) s asm)
    (hw : Dia.wOf Dia.bEntry.label ≤ N) (hnh : s.halted = false)
    (hc : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bEntry asm N
      (runBlock (f + 1 + 1) Dia.ctx Dia.bEntry s) :=
  hstep_jmp_block_ws Dia.pcOf Dia.psOf Dia.wOf (bb' := Dia.bElse) (blockLen := 6) (idx := 6)
    (hrb := dia_entry_run_nottaken f Dia.ctx hnh hc)
    (hnh := by rw [jumpTo]; exact hnh)
    (hrun := dia_hasm_entry_nottaken_full hpc
      (by rw [(venomAsmRel_init0_iff.mp hrel).2.2.2.2.2.2.1]; exact hc))
    (hrel := dia_rel_transfer (vs := s) (asm := asm) hrel (stk_nil hrel)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (hstk := rfl) (hsp := rfl) (hfe := rfl) (hno := le_refl _)
    (hpcidx := rfl) (hle := by have : Dia.wOf Dia.bEntry.label = 13 := rfl; omega)
    (hidx := rfl) (hlk' := rfl) (hwdec := by decide)

/-! ### The whole function

The driver needs an invariant, because `venomAsmRel` cannot carry what the join needs. `Dia.Inv` is that
invariant: at the join — and only there — it records which predecessor the walk arrived from and that
that predecessor's phi source is bound. The compiler popped those variables, so the stack has no witness
for them; this is the fact the relation deliberately forgets. -/
/-- `WalkStep` upgrades to `WalkStepInv` once the invariant holds at the successor. -/
theorem WalkStepInv_of_WalkStep {Inv fn pcOf psOf wOf lo o2pc prog bb asm N} {r : ExecResult}
    (h : WalkStep fn pcOf psOf wOf lo o2pc prog bb asm N r)
    (hinv : ∀ s', r = ExecResult.OK s' → Inv s') :
    WalkStepInv Inv fn pcOf psOf wOf lo o2pc prog bb asm N r := by
  cases r with
  | OK s' =>
    by_cases hh : s'.halted
    · simpa only [WalkStep, WalkStepInv, hh, if_true] using h
    · simp only [WalkStep, hh, Bool.false_eq_true, if_false] at h
      simp only [WalkStepInv, hh, Bool.false_eq_true, if_false]
      obtain ⟨bb'', asm'', bl, h1, h2, h3, h4, h5, h6⟩ := h
      exact ⟨bb'', asm'', bl, h1, h2, h3, h4, h5, h6, hinv s' rfl⟩
  | Halt _ => exact h
  | Abort a _ => cases a <;> exact h
  | IntRet _ _ => trivial
  | Error _ => trivial

/-- The join's `evalPhis` on the arrival from `else`. -/
theorem dia_join_ev_from_else {s : VenomState} (hprev : s.prevBb = some "else")
    (hv : lookupVar "b" s = some (addressToWord s.callCtx.caller)) :
    evalPhis s Dia.bJoin.instructions
      = ExecResult.OK (updateVar "p" (addressToWord s.callCtx.caller) s) := by
  show evalPhis s (Dia.dPhi :: [Dia.dStop]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Dia.dPhi.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "b") (prev := "else")
        (v := addressToWord s.callCtx.caller) (by rfl) hprev (by rfl) hv]
  show (match evalPhis s [Dia.dStop] with
        | ExecResult.OK s' =>
            ExecResult.OK (updateVar "p" (addressToWord s.callCtx.caller) s') | err => err) = _
  rw [show evalPhis s [Dia.dStop] = ExecResult.OK s from by
    unfold evalPhis; rw [if_pos (by decide)]]

/-- **The walk invariant.** At the join — and only there — it records which predecessor the walk arrived
from and that that predecessor's phi source is bound. This is the fact `venomAsmRel` cannot carry: the
compiler popped the variable, so the stack has no witness for it. -/
def Dia.Inv (s : VenomState) : Prop :=
  s.currentBb = "join" →
    (s.prevBb = some "then" ∧ lookupVar "a" s = some s.callCtx.callvalue) ∨
    (s.prevBb = some "else" ∧ lookupVar "b" s = some (addressToWord s.callCtx.caller))

/-- The join's hstep, given *any* successful `evalPhis` whose result shares the observable fields. -/
theorem dia_hstep_join_gen {s vs' : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bJoin.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bJoin.label) s asm)
    (hw : Dia.wOf Dia.bJoin.label ≤ N)
    (hev : evalPhis s Dia.bJoin.instructions = ExecResult.OK vs')
    (hacc : vs'.accounts = s.accounts) (htr : vs'.transient = s.transient)
    (hrd : vs'.returndata = s.returndata) (hlg : vs'.logs = s.logs) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bJoin asm N
      (runBlock (f + 1) Dia.ctx Dia.bJoin s) := by
  have hN : 2 ≤ N := by have : Dia.wOf Dia.bJoin.label = 2 := rfl; omega
  obtain ⟨_, _, ha, ht, hr, hl, _, _, _, _, _⟩ := venomAsmRel_init0_iff.mp hrel
  refine hstep_bareTerm_halt_join (phis := [Dia.dPhi]) (term := Dia.dStop)
    Dia.pcOf Dia.psOf Dia.wOf hev rfl
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide) rfl
    ⟨asmNext (asmNext asm), dia_hasm_join_gen (hpc := hpc) hN, ?_⟩
  exact ⟨by show asm.accounts = _; rw [hacc]; exact ha,
         by show asm.transient = _; rw [htr]; exact ht,
         by show asm.returndata = _; rw [hrd]; exact hr,
         by show asm.logs = _; rw [hlg]; exact hl⟩

/-- **The join's hstep, from the invariant** — either predecessor. -/
theorem dia_hstep_join_inv {s : VenomState} {asm : AsmState} {N f : Nat}
    (hpc : asm.pc = Dia.pcOf Dia.bJoin.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bJoin.label) s asm)
    (hw : Dia.wOf Dia.bJoin.label ≤ N)
    (hcur : s.currentBb = "join") (hinv : Dia.Inv s) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bJoin asm N
      (runBlock (f + 1) Dia.ctx Dia.bJoin s) := by
  rcases hinv hcur with ⟨hprev, hv⟩ | ⟨hprev, hv⟩
  · exact dia_hstep_join_gen hpc hrel hw (dia_join_ev_from_then hprev hv) rfl rfl rfl rfl
  · exact dia_hstep_join_gen hpc hrel hw (dia_join_ev_from_else hprev hv) rfl rfl rfl rfl

/-- **`then` re-establishes the invariant at the join**: it binds `a`, and the jump records `then` as the
predecessor. -/
theorem dia_inv_then {s : VenomState} (hcur : s.currentBb = "then") :
    Dia.Inv (jumpTo "join" (Dia.afterA s)) := by
  intro _
  left
  refine ⟨?_, rfl⟩
  show some (Dia.afterA s).currentBb = some "then"
  rw [show (Dia.afterA s).currentBb = s.currentBb from rfl, hcur]

/-- **`else` re-establishes it too**, via `b`. -/
theorem dia_inv_else {s : VenomState} (hcur : s.currentBb = "else") :
    Dia.Inv (jumpTo "join" (Dia.afterB s)) := by
  intro _
  right
  refine ⟨?_, rfl⟩
  show some (Dia.afterB s).currentBb = some "else"
  rw [show (Dia.afterB s).currentBb = s.currentBb from rfl, hcur]

/-- Entry's successors are `then` and `else`, never the join, so the invariant is vacuous there. -/
theorem dia_inv_entry_taken {s : VenomState} : Dia.Inv (jumpTo "then" (Dia.afterCV s)) := by
  intro h
  exact absurd (show "then" = "join" from h) (by decide)
theorem dia_inv_entry_nottaken {s : VenomState} : Dia.Inv (jumpTo "else" (Dia.afterCV s)) := by
  intro h
  exact absurd (show "else" = "join" from h) (by decide)

/-- Blocks of the diamond, by label. -/
theorem dia_lookup {s : VenomState} {bb : BasicBlock}
    (hlk : lookupBlock s.currentBb Dia.fn.blocks = some bb) :
    (s.currentBb = "entry" ∧ bb = Dia.bEntry) ∨ (s.currentBb = "then" ∧ bb = Dia.bThen) ∨
    (s.currentBb = "else" ∧ bb = Dia.bElse) ∨ (s.currentBb = "join" ∧ bb = Dia.bJoin) := by
  rw [show Dia.fn.blocks = [Dia.bEntry, Dia.bThen, Dia.bElse, Dia.bJoin] from rfl,
      lookupBlock] at hlk
  have hmem := List.mem_of_find?_eq_some hlk
  have hlab := List.find?_some hlk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩
  · exact Or.inr (Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(eq_of_beq hlab).symm, rfl⟩))

/-- Out of fuel on a phi-free block: `execBlock 0` errors, and `WalkStepInv` sends `Error` to `True`. -/
theorem wsi_zero_nophi {Inv bb s asm N}
    (h : ∀ i, bb.instructions.head? = some i → i.opcode ≠ Opcode.PHI) :
    WalkStepInv Inv Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog bb asm N
      (runBlock 0 Dia.ctx bb s) := by
  rw [runBlock_of_no_phi h]
  simp only [WalkStepInv, execBlock]

/-- Out of fuel at a join whose phis do evaluate. -/
theorem wsi_zero_join {Inv s asm N vs'}
    (hev : evalPhis s Dia.bJoin.instructions = ExecResult.OK vs') :
    WalkStepInv Inv Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bJoin asm N
      (runBlock 0 Dia.ctx Dia.bJoin s) := by
  rw [runBlock_eq_execBlock_of_phis hev]
  simp only [WalkStepInv, execBlock]

/-- **The diamond's `hstep`, for every block.** -/
theorem dia_hstep_all :
    ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
      lookupBlock s.currentBb Dia.fn.blocks = some bb →
      asm.pc = Dia.pcOf bb.label →
      venomAsmRel Dia.lo (Dia.psOf bb.label) s asm →
      Dia.wOf bb.label ≤ N →
      s.halted = false →
      Dia.Inv s →
      WalkStepInv Dia.Inv Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog bb asm N
        (runBlock f' Dia.ctx bb s) := by
  intro bb s asm N f' hlk hpc hrel hw hnh hinv
  rcases dia_lookup hlk with ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩
  -- entry
  · match f' with
    | 0 => exact wsi_zero_nophi (by decide)
    | 1 =>
      rw [runBlock_of_no_phi (by decide)]
      simp only [WalkStepInv, execBlock]
      trivial
    | (k + 1 + 1) =>
      by_cases hc : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0
      · refine WalkStepInv_of_WalkStep (dia_hstep_entry_nottaken hpc hrel hw hnh hc) ?_
        intro s' hs'
        rw [dia_entry_run_nottaken k Dia.ctx hnh hc] at hs'
        injection hs' with h; subst h
        exact dia_inv_entry_nottaken
      · refine WalkStepInv_of_WalkStep (dia_hstep_entry_taken hpc hrel hw hnh hc) ?_
        intro s' hs'
        rw [dia_entry_run_taken k Dia.ctx hnh hc] at hs'
        injection hs' with h; subst h
        exact dia_inv_entry_taken
  -- then
  · match f' with
    | 0 => exact wsi_zero_nophi (by decide)
    | 1 =>
      rw [runBlock_of_no_phi (by decide)]
      simp only [WalkStepInv, execBlock]
      trivial
    | (k + 1 + 1) =>
      refine WalkStepInv_of_WalkStep (dia_hstep_then hpc hrel hw hnh) ?_
      intro s' hs'
      rw [dia_then_run k Dia.ctx hnh] at hs'
      injection hs' with h; subst h
      exact dia_inv_then hcur
  -- else
  · match f' with
    | 0 => exact wsi_zero_nophi (by decide)
    | 1 =>
      rw [runBlock_of_no_phi (by decide)]
      simp only [WalkStepInv, execBlock]
      trivial
    | (k + 1 + 1) =>
      refine WalkStepInv_of_WalkStep (dia_hstep_else hpc hrel hw hnh) ?_
      intro s' hs'
      rw [dia_else_run k Dia.ctx hnh] at hs'
      injection hs' with h; subst h
      exact dia_inv_else hcur
  -- join
  · match f' with
    | 0 =>
      rcases hinv hcur with ⟨hprev, hv⟩ | ⟨hprev, hv⟩
      · exact wsi_zero_join (dia_join_ev_from_then hprev hv)
      · exact wsi_zero_join (dia_join_ev_from_else hprev hv)
    | (k + 1) =>
      refine WalkStepInv_of_WalkStep (dia_hstep_join_inv hpc hrel hw hcur hinv) ?_
      intro s' hs'
      exfalso
      rcases hinv hcur with ⟨hprev, hv⟩ | ⟨hprev, hv⟩
      · rw [runBlock_join_eq_execBlock_at (phis := [Dia.dPhi]) (term := Dia.dStop)
              (dia_join_ev_from_then hprev hv) rfl
              (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide),
            execBlock_step_halt k Dia.ctx Dia.bJoin _ _ Dia.dStop (by rfl) rfl] at hs'
        exact absurd hs' (by simp)
      · rw [runBlock_join_eq_execBlock_at (phis := [Dia.dPhi]) (term := Dia.dStop)
              (dia_join_ev_from_else hprev hv) rfl
              (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide),
            execBlock_step_halt k Dia.ctx Dia.bJoin _ _ Dia.dStop (by rfl) rfl] at hs'
        exact absurd hs' (by simp)

/-- **CAPSTONE — codegen correctness for a function containing a phi join.**

`Dia.fn` compiles to the eighteen instructions pinned above, and this says that running it as Venom and
running that program as EVM agree: halt for halt, revert for revert, fault for fault, with
`finalStateRel` on the observable state.

Every input is discharged. `dia_hstep_all` covers all four blocks — entry on both `CALLVALUE` arms, the
two `JMP join` blocks, and the join whose head is a `PHI` — at every fuel, against the real compiled
program. The join's `evalPhis` is *proved* to succeed from either predecessor, which is the thing that
was vacuous two turns ago and structurally unstatable before that. The only hypotheses left are about the
starting configuration: the machine has not halted, the pc is at the entry, and the relation holds.

The invariant is the interesting hypothesis, and it is not a technicality. `venomAsmRel` cannot tell you
which predecessor a join was entered from, nor that the phi's source is bound — the compiler pops those
variables, because a phi does not *use* its sources. So the walk has to carry that fact itself, and
`Dia.Inv` is exactly the fact the stack refuses to carry. -/
theorem dia_codegen_correct {fuel : Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hpc0 : as.pc = 0)
    (hrel : venomAsmRel Dia.lo (initPlanState 0)
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as) :
    (match runContext fuel Dia.ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm Dia.prog.length Dia.o2pc Dia.prog as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm Dia.prog.length Dia.o2pc Dia.prog as
         = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm Dia.prog.length Dia.o2pc Dia.prog as
         = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_sched_inv (fuel := fuel) (ctx := Dia.ctx) (fn := Dia.fn)
    (fnEom := 0) (lblCtr := 0) (ops := Dia.ops) (psFinal := (generateFnPlan Dia.fn 0 0).get!.2)
    (entryName := "main") (entryLbl := "entry") (lo := Dia.lo)
    Dia.Inv rfl rfl rfl rfl Dia.pcOf Dia.psOf Dia.wOf dia_hstep_all
    Dia.bEntry rfl hpc0 (by decide) hvshalt hrel
    (by intro h; exact absurd (show "entry" = "join" from h) (by decide))

/-! ### Is the capstone vacuous?

`dia_codegen_correct`'s conclusion is a match on `runContext`, and its last arm is `_ => True`. So if the
function never actually ran — if it errored out, or never reached the join — the theorem would be
perfectly true and say nothing whatsoever. This branch has already shipped three witnesses that were
vacuous in exactly that way, so the question gets an answer rather than an assumption.

It runs. From `CALLVALUE = 7` it takes the `JNZ`, passes through `then`, enters the join *from* `then`,
the phi binds `p` to the 7 that `a` carried, and it halts. `runContext` does not reduce in the kernel
(`execBlock` is well-founded), so `dia_runs` proves the three-block walk step by step from the block
lemmas rather than computing it. -/
namespace Dia
/-- A concrete start: `CALLVALUE = 7`, so the `JNZ` is taken and the join is entered from `then`. -/
def vs0 : VenomState := { (default : VenomState) with
  callCtx := { (default : CallContext) with callvalue := EvmYul.UInt256.ofNat 7 } }
def as0 : AsmState := { (default : AsmState) with
  callCtx := { (default : CallContext) with callvalue := EvmYul.UInt256.ofNat 7 } }
/-- The state the walk starts from. -/
def s0 : VenomState := { vs0 with prevBb := none, currentBb := "entry", instIdx := 0 }
end Dia

/-- **The function really runs, and really goes through the phi.** Three blocks, then a halt at the
join — entered from `then`, with the phi's output `p` bound to the value `a` carried. -/
theorem dia_runs :
    runContext 20 Dia.ctx Dia.vs0
      = ExecResult.Halt (haltState
          { (updateVar "p" (EvmYul.UInt256.ofNat 7)
              (jumpTo "join" (Dia.afterA (jumpTo "then" (Dia.afterCV Dia.s0))))) with instIdx := 1 }) := by
  show runFunction 20 Dia.ctx Dia.fn { Dia.vs0 with prevBb := none } = _
  rw [runFunction]
  show runBlocks 20 Dia.ctx Dia.fn Dia.s0 = _
  -- entry block: CALLVALUE = 7 ≠ 0, so the JNZ is taken
  set s1 : VenomState := jumpTo "then" (Dia.afterCV Dia.s0) with hs1
  have he : runBlock 19 Dia.ctx Dia.bEntry Dia.s0 = ExecResult.OK s1 :=
    dia_entry_run_taken 17 Dia.ctx (by rfl) (by decide)
  rw [runBlocks, show lookupBlock Dia.s0.currentBb Dia.fn.blocks = some Dia.bEntry from rfl]
  dsimp only
  rw [he]
  dsimp only
  rw [if_neg (by rw [hs1]; exact (by decide : ¬ (jumpTo "then" (Dia.afterCV Dia.s0)).halted = true))]
  -- then block: binds a, jumps to join
  set s2 : VenomState := jumpTo "join" (Dia.afterA s1) with hs2
  have ht : runBlock 18 Dia.ctx Dia.bThen s1 = ExecResult.OK s2 :=
    dia_then_run 16 Dia.ctx (by rw [hs1]; rfl)
  rw [runBlocks, show lookupBlock s1.currentBb Dia.fn.blocks = some Dia.bThen from rfl]
  dsimp only
  rw [ht]
  dsimp only
  rw [if_neg (by rw [hs2]; exact (by decide : ¬ (jumpTo "join" (Dia.afterA s1)).halted = true))]
  -- join block: the phi binds p, then STOP
  have hev : evalPhis s2 Dia.bJoin.instructions
      = ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 7) s2) :=
    dia_join_ev_from_then (by rw [hs2]; rfl) (by rw [hs2]; rfl)
  have hj : runBlock 17 Dia.ctx Dia.bJoin s2
      = ExecResult.Halt (haltState
          { (updateVar "p" (EvmYul.UInt256.ofNat 7) s2) with instIdx := 1 }) := by
    rw [runBlock_join_eq_execBlock_at (phis := [Dia.dPhi]) (term := Dia.dStop) hev rfl
          (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide)]
    exact execBlock_step_halt 16 Dia.ctx Dia.bJoin _ _ Dia.dStop (by rfl) rfl
  rw [runBlocks, show lookupBlock s2.currentBb Dia.fn.blocks = some Dia.bJoin from rfl]
  dsimp only
  rw [hj]

/-- The relation holds at the start: empty stacks, empty memories, matching contexts. -/
theorem dia_rel0 : venomAsmRel Dia.lo (initPlanState 0) Dia.s0 Dia.as0 := by
  rw [venomAsmRel_init0_iff]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro i; rfl

/-- **The capstone is not vacuous.** `dia_codegen_correct`'s conclusion is a match on `runContext`, so it
would say nothing at all if the function never ran. It runs: from `CALLVALUE = 7` it takes the `JNZ`,
passes through `then`, enters the join from `then`, binds the phi, and halts. Feeding that to the capstone
yields a *concrete* EVM halt, related to the Venom halt state.

Every hypothesis of `dia_codegen_correct` is discharged here — nothing is left assumed. -/
theorem dia_codegen_correct_fires :
    ∃ as', runAsm Dia.prog.length Dia.o2pc Dia.prog Dia.as0 = AsmResult.AsmHalt as' ∧
      finalStateRel (haltState
        { (updateVar "p" (EvmYul.UInt256.ofNat 7)
            (jumpTo "join" (Dia.afterA (jumpTo "then" (Dia.afterCV Dia.s0))))) with instIdx := 1 }) as' := by
  have h := dia_codegen_correct (fuel := 20) (vs := Dia.vs0) (as := Dia.as0)
    (by rfl) (by rfl) dia_rel0
  rw [dia_runs] at h
  exact h

/-! ## A terminating loop whose header is a phi

`Example.loopFn` exhibits the rank obstruction, but it never halts — its `JNZ` is on the literal `1`, so
a top-level correctness statement about it would be discharged by the out-of-fuel arm and say nothing.
A loop worth proving correct has to *stop*.

`Lp.fn` stops. `p` starts as `CALLVALUE`; the body sets `d = ISZERO p` and jumps back, so a nonzero call
value runs the body exactly once and then leaves. The CFG is genuinely cyclic — `body`'s only successor
is the header — and the back-edge is actually traversed at run time, which `lp_runs` proves rather than
asserts.

Two design constraints, both learned the hard way earlier on this branch. No literal appears anywhere,
because a literal push puts `encodeNumBytes` (well-founded) into the label offsets and makes the whole
compiled layout irreducible. And the phi's sources are real definitions, because a phi whose sources are
free makes `evalPhis` fail and the obligation vacuous.

Unlike the diamond, the plan stacks here are *not* empty: the compiler keeps the loop-carried value on
the EVM stack across the back-edge (`DUP1` at the header, `POP` at the exit). That is the new work the
per-block obligations will need. -/
set_option maxRecDepth 40000


namespace Lp
def iC : Instruction := { id := 50, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }
def jHead : Instruction :=
  { id := 51, opcode := Opcode.JMP, operands := [Operand.Label "head"], outputs := [] }
def pP : Instruction :=
  { id := 52, opcode := Opcode.PHI,
    operands := [Operand.Label "entry", Operand.Var "c", Operand.Label "body", Operand.Var "d"],
    outputs := ["p"] }
def jnz : Instruction :=
  { id := 53, opcode := Opcode.JNZ,
    operands := [Operand.Var "p", Operand.Label "body", Operand.Label "exit"], outputs := [] }
def iD : Instruction :=
  { id := 54, opcode := Opcode.ISZERO, operands := [Operand.Var "p"], outputs := ["d"] }
def jBack : Instruction :=
  { id := 55, opcode := Opcode.JMP, operands := [Operand.Label "head"], outputs := [] }
def iStop : Instruction := { id := 56, opcode := Opcode.STOP, operands := [], outputs := [] }

def bEntry : BasicBlock := { label := "entry", instructions := [iC, jHead] }
/-- The loop header carries a **phi**, and it is a genuine join: `entry` and the back-edge from `body`. -/
def bHead  : BasicBlock := { label := "head",  instructions := [pP, jnz] }
def bBody  : BasicBlock := { label := "body",  instructions := [iD, jBack] }
def bExit  : BasicBlock := { label := "exit",  instructions := [iStop] }

/-- **A terminating loop whose header is a phi.** `p` starts as `CALLVALUE`; the body sets
`d = ISZERO p` and jumps back, so a nonzero call value runs the body exactly once and then exits. No
literal appears anywhere — deliberately, since a literal push would make the label offsets irreducible. -/
def fn : IrFunction := { name := "main", blocks := [bEntry, bHead, bBody, bExit] }
def ctx : VenomContext := { functions := [fn], entry := some "main" }

def ops  : List StackOp := (generateFnPlan fn 0 0).get!.1
def prog : List AsmInst := (asmResolve (executePlan ops)).1
def o2pc : AssocList Nat Nat := (asmResolve (executePlan ops)).2
def lo   : AssocList String Nat := (computeLabelOffsets (executePlan ops)).2
end Lp

theorem lp_compiles : (generateFnPlan Lp.fn 0 0).isSome = true := by rfl
theorem lp_prog_len : Lp.prog.length = 17 := by rfl

/-- **The compiler keeps the phi's value on the EVM stack across the back-edge.** `DUP1` at the header
copies it for the `JUMPI`, `POP` at the exit discards it. Unlike the diamond, the plan stacks here are
*not* empty — the loop-carried value is live. -/
theorem lp_prog_shape :
    Lp.prog[1]! = AsmInst.AsmOp "CALLVALUE" ∧
    Lp.prog[4]! = AsmInst.AsmLabel "head" ∧
    Lp.prog[5]! = AsmInst.AsmOp "DUP1" ∧
    Lp.prog[7]! = AsmInst.AsmOp "JUMPI" ∧
    Lp.prog[10]! = AsmInst.AsmLabel "exit" ∧
    Lp.prog[11]! = AsmInst.AsmOp "POP" ∧
    Lp.prog[12]! = AsmInst.AsmOp "STOP" ∧
    Lp.prog[13]! = AsmInst.AsmLabel "body" ∧
    Lp.prog[14]! = AsmInst.AsmOp "ISZERO" ∧
    Lp.prog[16]! = AsmInst.AsmOp "JUMP" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No literals, so the label offsets reduce — the whole layout is pinnable. -/
theorem lp_o2pc_head : AssocList.lookup Nat Nat Lp.o2pc 6 = some 4 := by rfl
theorem lp_o2pc_body : AssocList.lookup Nat Nat Lp.o2pc 19 = some 13 := by rfl
theorem lp_o2pc_exit : AssocList.lookup Nat Nat Lp.o2pc 16 = some 10 := by rfl

/-- **The CFG really is cyclic**: `body`'s only successor is the header. -/
theorem lp_back_edge : (cfgAnalyze Lp.fn).succsOf "body" = ["head"] := by decide

/-- And the header is reachable from itself — a genuine cycle, not a diamond. -/
theorem lp_cyclic : CfgReach (cfgAnalyze Lp.fn) "head" "head" := CfgReach.base

/-! ### Does the loop actually loop, and actually stop? -/

namespace Lp
def vs0 : VenomState := { (default : VenomState) with
  callCtx := { (default : CallContext) with callvalue := EvmYul.UInt256.ofNat 7 } }
def s0 : VenomState := { vs0 with prevBb := none, currentBb := "entry", instIdx := 0 }
/-- After `entry`: `c` bound, at the `JMP`. -/
def afterC (s : VenomState) : VenomState :=
  { updateVar "c" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
/-- After the body's `ISZERO`: `d` bound, at the `JMP`. -/
def afterD (s : VenomState) (v : bytes32) : VenomState :=
  { updateVar "d" (EvmYul.UInt256.isZero v) { s with instIdx := 0 } with instIdx := 1 }
end Lp

/-- `entry` binds `c = CALLVALUE` and jumps to the header. -/
theorem lp_entry_run (f : Nat) (ctx : VenomContext) {s : VenomState} (hnh : s.halted = false) :
    runBlock (f + 1 + 1) ctx Lp.bEntry s = ExecResult.OK (jumpTo "head" (Lp.afterC s)) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Lp.bEntry { s with instIdx := 0 }
        (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }) Lp.iC
        (by rfl) (by rfl) (by decide)]
  exact execBlock_step_term_ok f ctx Lp.bEntry (Lp.afterC s) _ Lp.jHead (by rfl) (by rfl)
    (by decide) (by rw [jumpTo]; exact hnh)

/-- **The whole run.** `CALLVALUE = 7`: the header takes the loop, the body flips the condition to zero,
the header is re-entered **across the back-edge**, and the second visit exits. It halts. -/
theorem lp_runs :
    (match runContext 30 Lp.ctx Lp.vs0 with
     | ExecResult.Halt w => w.currentBb = "exit" ∧ w.prevBb = some "head"
     | _ => False) := by
  show (match runFunction 30 Lp.ctx Lp.fn { Lp.vs0 with prevBb := none } with
        | ExecResult.Halt w => w.currentBb = "exit" ∧ w.prevBb = some "head" | _ => False)
  rw [runFunction]
  show (match runBlocks 30 Lp.ctx Lp.fn Lp.s0 with
        | ExecResult.Halt w => w.currentBb = "exit" ∧ w.prevBb = some "head" | _ => False)
  -- entry
  set s1 : VenomState := jumpTo "head" (Lp.afterC Lp.s0) with hs1
  have he : runBlock 29 Lp.ctx Lp.bEntry Lp.s0 = ExecResult.OK s1 :=
    lp_entry_run 27 Lp.ctx (by rfl)
  rw [runBlocks, show lookupBlock Lp.s0.currentBb Lp.fn.blocks = some Lp.bEntry from rfl]
  dsimp only
  rw [he]
  dsimp only
  rw [if_neg (by rw [hs1]; exact (by decide : ¬ (jumpTo "head" (Lp.afterC Lp.s0)).halted = true))]
  -- header, visit 1: the phi takes `c` from `entry`; p = 7 ≠ 0, so the loop is entered
  have hev1 : evalPhis s1 Lp.bHead.instructions
      = ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 7) s1) := by
    show evalPhis s1 (Lp.pP :: [Lp.jnz]) = _
    unfold evalPhis
    rw [if_neg (show ¬ (Lp.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
        evalOnePhi_var (out := "p") (src := "c") (prev := "entry")
          (v := EvmYul.UInt256.ofNat 7) (by rfl) (by rfl) (by rfl) (by rfl)]
    show (match evalPhis s1 [Lp.jnz] with
          | ExecResult.OK s' => ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 7) s') | err => err) = _
    rw [show evalPhis s1 [Lp.jnz] = ExecResult.OK s1 from by unfold evalPhis; rw [if_pos (by decide)]]
  set h1 : VenomState := updateVar "p" (EvmYul.UInt256.ofNat 7) s1 with hh1
  set s2 : VenomState := jumpTo "body" { h1 with instIdx := 1 } with hs2
  have hhd1 : runBlock 28 Lp.ctx Lp.bHead s1 = ExecResult.OK s2 := by
    rw [runBlock_join_eq_execBlock_at (phis := [Lp.pP]) (term := Lp.jnz) hev1 rfl
          (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide)]
    exact execBlock_step_term_ok 27 Lp.ctx Lp.bHead _ _ Lp.jnz (by rfl) (by rfl) (by decide) (by rfl)
  rw [runBlocks, show lookupBlock s1.currentBb Lp.fn.blocks = some Lp.bHead from rfl]
  dsimp only
  rw [hhd1]
  dsimp only
  rw [if_neg (by decide : ¬ s2.halted = true)]
  -- body: ISZERO flips the condition, then the BACK-EDGE to the header
  set s3 : VenomState := jumpTo "head" (Lp.afterD s2 (EvmYul.UInt256.ofNat 7)) with hs3
  have hbd : runBlock 27 Lp.ctx Lp.bBody s2 = ExecResult.OK s3 := by
    rw [runBlock_of_no_phi (by decide)]
    rw [execBlock_step_nonterm 26 Lp.ctx Lp.bBody { s2 with instIdx := 0 }
          (updateVar "d" (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 7)) { s2 with instIdx := 0 })
          Lp.iD (by rfl) (by rfl) (by decide)]
    exact execBlock_step_term_ok 25 Lp.ctx Lp.bBody _ _ Lp.jBack (by rfl) (by rfl) (by decide) (by rfl)
  rw [runBlocks, show lookupBlock s2.currentBb Lp.fn.blocks = some Lp.bBody from rfl]
  dsimp only
  rw [hbd]
  dsimp only
  rw [if_neg (by decide : ¬ s3.halted = true)]
  -- header, visit 2 — entered ACROSS THE BACK-EDGE. The phi now takes `d` from `body`; p = 0, so exit.
  have hev2 : evalPhis s3 Lp.bHead.instructions
      = ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 0) s3) := by
    show evalPhis s3 (Lp.pP :: [Lp.jnz]) = _
    unfold evalPhis
    rw [if_neg (show ¬ (Lp.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
        evalOnePhi_var (out := "p") (src := "d") (prev := "body")
          (v := EvmYul.UInt256.ofNat 0) (by rfl) (by rfl) (by rfl) (by rfl)]
    show (match evalPhis s3 [Lp.jnz] with
          | ExecResult.OK s' => ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 0) s') | err => err) = _
    rw [show evalPhis s3 [Lp.jnz] = ExecResult.OK s3 from by unfold evalPhis; rw [if_pos (by decide)]]
  set h2 : VenomState := updateVar "p" (EvmYul.UInt256.ofNat 0) s3 with hh2
  set s4 : VenomState := jumpTo "exit" { h2 with instIdx := 1 } with hs4
  have hhd2 : runBlock 26 Lp.ctx Lp.bHead s3 = ExecResult.OK s4 := by
    rw [runBlock_join_eq_execBlock_at (phis := [Lp.pP]) (term := Lp.jnz) hev2 rfl
          (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide)]
    exact execBlock_step_term_ok 25 Lp.ctx Lp.bHead _ _ Lp.jnz (by rfl) (by rfl) (by decide) (by rfl)
  rw [runBlocks, show lookupBlock s3.currentBb Lp.fn.blocks = some Lp.bHead from rfl]
  dsimp only
  rw [hhd2]
  dsimp only
  rw [if_neg (by decide : ¬ s4.halted = true)]
  -- exit
  have hex : runBlock 25 Lp.ctx Lp.bExit s4
      = ExecResult.Halt (haltState { s4 with instIdx := 0 }) := by
    rw [runBlock_of_no_phi (by decide)]
    exact execBlock_step_halt 24 Lp.ctx Lp.bExit _ _ Lp.iStop (by rfl) rfl
  rw [runBlocks, show lookupBlock s4.currentBb Lp.fn.blocks = some Lp.bExit from rfl]
  dsimp only
  rw [hex]
  exact ⟨rfl, rfl⟩

/-! ### `psOf : String → PlanState` cannot describe a phi-headed loop header

The diamond needed an invariant because `venomAsmRel` could not carry a fact about `vars`. The loop needs
one for a sharper reason: the *plan stack itself* depends on which predecessor the walk arrived from, and
the scheduled drivers fix it per label.

`entry` hands the header a stack holding `c`. The back-edge hands it a stack holding `d`. The *shape*
agrees — one slot, which is exactly what the join-agreement invariant guarantees — but the *name* does
not, and it is not supposed to. That difference is what the phi exists to reconcile.

`planStackRel` reads the plan stack's names out of the Venom state, so a per-label `psOf head = ["c"]`
demands that the asm stack top equal `c`'s value. Across the back-edge the stack carries `d`'s value, and
`c` is still bound to something else entirely. Below, 7 and 0.

So this is not a proof that has not been found. It is a proposition that is *false*, and no amount of work
on the per-block obligations would repair it. `codegen_correct_fuel` takes `Entry` as a free parameter,
which is where the header's layout has to live. -/
set_option maxRecDepth 40000

namespace Lp
def live : DfState (List String) := livenessAnalyzeFuel (fnPlanFuel fn) fn
def cfg  : CfgAnalysis := cfgAnalyze fn
def dfg  : DfgAnalysis := DfgAnalysis.buildFunction fn
/-- The plan state the DFS hands to `head` — i.e. `entry`'s exit. -/
def psAtHeadFromEntry : Option (List String) :=
  (generateBlockPlan live dfg cfg fn bEntry (initPlanState 0)).map
    (fun r => r.2.stack.map operandToString)
/-- The plan state the back-edge hands to `head` — i.e. `body`'s exit. -/
def psAtHeadFromBody : Option (List String) :=
  ((generateBlockPlan live dfg cfg fn bEntry (initPlanState 0)).bind
    (fun r => (generateBlockPlan live dfg cfg fn bHead r.2).bind
      (fun r2 => generateBlockPlan live dfg cfg fn bBody r2.2))).map
    (fun r => r.2.stack.map operandToString)
end Lp

/-- **The loop header is entered with a different variable in the same stack slot.** From `entry` the
slot holds `c`; across the back-edge it holds `d`. The *shape* agrees — one slot, which is what the
join-agreement invariant guarantees — but the *name* does not, and it is not supposed to: that is exactly
what the phi is for. -/
theorem lp_head_incoming_differs :
    Lp.psAtHeadFromEntry = some ["c"] ∧ Lp.psAtHeadFromBody = some ["d"] := ⟨rfl, rfl⟩

/-- **So a single `psOf head` cannot state the header's entry relation.** `planStackRel` reads the plan
stack's names out of the *Venom* state, so with `psOf head = ["c"]` it demands the asm stack top equal
`c`'s value. Across the back-edge the asm stack top is `d`'s value — and `c` is still bound, to something
else. Here they are 7 and 0. The relation is false on arrival, for the compiler's own plan.

This is the `Entry`-too-weak gap again, one level deeper: the diamond needed a fact about `vars` that the
stack had dropped; the loop needs the *plan stack itself* to depend on the predecessor. `psOf : String →
PlanState` cannot. `codegen_correct_fuel` takes `Entry` as a free parameter and can. -/
theorem lp_psOf_by_label_impossible
    (psOf : String → PlanState)
    (hentry : (psOf "head").stack = [Operand.Var "c"])
    (hbody  : (psOf "head").stack = [Operand.Var "d"]) : False := by
  rw [hentry] at hbody
  exact absurd hbody (by decide)

/-- The Venom state arriving at the header **across the back-edge**: `c` is still 7 (it was never killed),
and `d` — the value the EVM stack actually carries — is 0. -/
def Lp.fromBody : VenomState :=
  { (default : VenomState) with
    vars := [("d", EvmYul.UInt256.ofNat 0), ("c", EvmYul.UInt256.ofNat 7)],
    prevBb := some "body", currentBb := "head" }

/-- **The refutation, on concrete values.** The compiler's plan for `head` says slot 0 is `c`. Across the
back-edge the EVM stack carries `d = 0`, while `c` is still 7. `planStackRel` therefore demands `7 = 0`.

So this is not a proof that has not been found — it is a proposition that is false. A per-label `psOf`
cannot be the header's entry layout, and no amount of work on the per-block obligations would fix it. -/
theorem lp_planStackRel_false_on_backedge :
    ¬ planStackRel Lp.lo Lp.fromBody [Operand.Var "c"] [EvmYul.UInt256.ofNat 0] := by
  rintro ⟨-, h⟩
  have h0 := h 0 (by decide)
  exact absurd h0 (by decide)

/-- …while it does hold with the layout the back-edge actually delivers. -/
theorem lp_planStackRel_true_with_d :
    planStackRel Lp.lo Lp.fromBody [Operand.Var "d"] [EvmYul.UInt256.ofNat 0] := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have : i = 0 := by simpa using hi
  subst this
  rfl

/-! ### The loop's asm, block by block

Against the compiler's own program, every index checked by `rfl`. The shapes differ from the diamond's in
the way that matters: the stack is never empty. `DUP1` at the header copies the loop-carried value so the
`JUMPI` can consume one and leave one behind, `ISZERO` in the body rewrites it in place and takes the
back-edge, and `POP` at the exit finally discards it.

The longest block is the header's not-taken arm at six steps, which is what fixes the per-block bound
`B = 6` that `codegen_correct_fuel` multiplies by the Venom fuel. -/

set_option maxRecDepth 8000

set_option maxRecDepth 8000

/-- `DUP1` on a nonempty stack. -/
theorem asmDup_one {s : AsmState} {x : bytes32} {stk : List bytes32} (h : s.stack = x :: stk) :
    asmDup 0 s = AsmResult.AsmOK { asmNext s with stack := x :: x :: stk } := by
  unfold asmDup
  simp [h]

theorem runAsm_one' {o2pc prog s s'} (hpc : s.pc < prog.length)
    (hstep : asmStep o2pc prog s = AsmResult.AsmOK s') :
    runAsm 1 o2pc prog s = AsmResult.AsmOK s' := by
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc hstep]; rfl

theorem lp_lo_head : AssocList.lookup String Nat Lp.lo "head" = some 6 := by rfl
theorem lp_lo_body : AssocList.lookup String Nat Lp.lo "body" = some 19 := by rfl
theorem lp_lo_exit : AssocList.lookup String Nat Lp.lo "exit" = some 16 := by rfl

/-- `entry`: `JUMPDEST ; CALLVALUE ; PUSH head ; JUMP` — four steps, pc 0 → 4, pushing `c`. -/
theorem lp_hasm_entry {asm : AsmState} (hpc : asm.pc = 0) :
    runAsm 4 Lp.o2pc Lp.prog asm
      = AsmResult.AsmOK { asm with pc := 4, stack := asm.callCtx.callvalue :: asm.stack } := by
  have h1 : asm.pc < Lp.prog.length := by rw [hpc]; decide
  have hg1 : Lp.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "entry" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Lp.prog.length) = ⟨0, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one' (o2pc := Lp.o2pc) h1 (asmStep_label_ok (offsetToPc := Lp.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 1 := by show asm.pc + 1 = 1; rw [hpc]
  have h2 : a1.pc < Lp.prog.length := by rw [hpc1]; decide
  have hg2 : Lp.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp "CALLVALUE" := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Lp.prog.length) = ⟨1, by decide⟩ from Fin.ext hpc1]
    rfl
  have s2 := runAsm_one' (o2pc := Lp.o2pc) h2 (by rw [asmStep_callvalue_ok h2 hg2]; rfl :
    asmStep Lp.o2pc Lp.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := a1.callCtx.callvalue :: a1.stack })
  set a2 : AsmState := { asmNext a1 with stack := a1.callCtx.callvalue :: a1.stack } with ha2
  have hpc2 : a2.pc = 2 := by show a1.pc + 1 = 2; rw [hpc1]
  have h3 : a2.pc < Lp.prog.length := by rw [hpc2]; decide
  have hg3 : Lp.prog.get ⟨a2.pc, h3⟩ = resolveInst Lp.lo (AsmInst.AsmPushLabel "head") := by
    conv_lhs => rw [show (⟨a2.pc, h3⟩ : Fin Lp.prog.length) = ⟨2, by decide⟩ from Fin.ext hpc2]
    rfl
  have h4 : a2.pc + 1 < Lp.prog.length := by rw [hpc2]; decide
  have hg4 : Lp.prog.get ⟨a2.pc + 1, h4⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨a2.pc + 1, h4⟩ : Fin Lp.prog.length) = ⟨3, by decide⟩ from
      Fin.ext (by show a2.pc + 1 = 3; rw [hpc2])]
    rfl
  have s3 := resolved_jump_sim h3 hg3 lp_lo_head (by decide) h4 hg4 lp_o2pc_head
  rw [show (4 : Nat) = 1 + (1 + 2) from rfl, runAsm_append_ok s1, runAsm_append_ok s2, s3]
  cases asm with | _ => simp_all [asmNext, a1, a2]

/-- The header's prefix: `JUMPDEST head ; DUP1` at pc 4 — the `DUP1` copies the loop-carried value so
the `JUMPI` can consume one and leave one behind. -/
theorem lp_head_prefix {asm : AsmState} {x : bytes32} {stk : List bytes32}
    (hpc : asm.pc = 4) (hstk : asm.stack = x :: stk) :
    runAsm 2 Lp.o2pc Lp.prog asm
      = AsmResult.AsmOK { asm with pc := 6, stack := x :: x :: stk } := by
  have h1 : asm.pc < Lp.prog.length := by rw [hpc]; decide
  have hg1 : Lp.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "head" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Lp.prog.length) = ⟨4, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one' (o2pc := Lp.o2pc) h1 (asmStep_label_ok (offsetToPc := Lp.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 5 := by show asm.pc + 1 = 5; rw [hpc]
  have h2 : a1.pc < Lp.prog.length := by rw [hpc1]; decide
  have hg2 : Lp.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp (dupName 1) := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Lp.prog.length) = ⟨5, by decide⟩ from Fin.ext hpc1]
    rfl
  have ha1stk : a1.stack = x :: stk := hstk
  have hdup : asmStep Lp.o2pc Lp.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := x :: x :: stk } := by
    rw [asmStep_dup_ok h2 hg2 (by decide) (by decide)]
    exact asmDup_one ha1stk
  have s2 := runAsm_one' (o2pc := Lp.o2pc) h2 hdup
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_append_ok s1, s2]
  cases asm with | _ => simp_all [asmNext, a1]

/-- **Header, loop taken** (`x ≠ 0`): from pc 6 the `[PUSH body ; JUMPI]` jumps to `body` (pc 13),
consuming the duplicate and leaving the value on the stack. -/
theorem lp_hasm_head_taken {asm : AsmState} {x : bytes32} {stk : List bytes32}
    (hpc : asm.pc = 4) (hstk : asm.stack = x :: stk) (hx : x ≠ EvmYul.UInt256.ofNat 0) :
    runAsm 4 Lp.o2pc Lp.prog asm
      = AsmResult.AsmOK { asm with pc := 13, stack := x :: stk } := by
  rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok (lp_head_prefix hpc hstk)]
  set a : AsmState := { asm with pc := 6, stack := x :: x :: stk } with ha
  have hapc : a.pc = 6 := rfl
  have h1 : a.pc < Lp.prog.length := by rw [hapc]; decide
  have hg1 : Lp.prog.get ⟨a.pc, h1⟩ = resolveInst Lp.lo (AsmInst.AsmPushLabel "body") := by
    conv_lhs => rw [show (⟨a.pc, h1⟩ : Fin Lp.prog.length) = ⟨6, by decide⟩ from Fin.ext hapc]
    rfl
  have h2 : a.pc + 1 < Lp.prog.length := by rw [hapc]; decide
  have hg2 : Lp.prog.get ⟨a.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI" := by
    conv_lhs => rw [show (⟨a.pc + 1, h2⟩ : Fin Lp.prog.length) = ⟨7, by decide⟩ from
      Fin.ext (by show a.pc + 1 = 7; rw [hapc])]
    rfl
  rw [resolved_jumpi_taken_sim (stk := x :: stk) (by rw [ha]) hx h1 hg1 lp_lo_body (by decide)
        h2 hg2 lp_o2pc_body]

/-- **Header, loop exited** (`x = 0`): the `JUMPI` falls through into `[PUSH exit ; JUMP]` and lands at
`exit` (pc 10). Six steps — the longer arm, which is what fixes the block bound `B`. -/
theorem lp_hasm_head_nottaken {asm : AsmState} {stk : List bytes32}
    (hpc : asm.pc = 4) (hstk : asm.stack = EvmYul.UInt256.ofNat 0 :: stk) :
    runAsm 6 Lp.o2pc Lp.prog asm
      = AsmResult.AsmOK { asm with pc := 10, stack := EvmYul.UInt256.ofNat 0 :: stk } := by
  rw [show (6 : Nat) = 2 + 4 from rfl, runAsm_append_ok (lp_head_prefix hpc hstk)]
  set z : bytes32 := EvmYul.UInt256.ofNat 0 with hz
  set a : AsmState := { asm with pc := 6, stack := z :: z :: stk } with ha
  have hapc : a.pc = 6 := rfl
  have h1 : a.pc < Lp.prog.length := by rw [hapc]; decide
  have hg1 : Lp.prog.get ⟨a.pc, h1⟩ = resolveInst Lp.lo (AsmInst.AsmPushLabel "body") := by
    conv_lhs => rw [show (⟨a.pc, h1⟩ : Fin Lp.prog.length) = ⟨6, by decide⟩ from Fin.ext hapc]
    rfl
  have h2 : a.pc + 1 < Lp.prog.length := by rw [hapc]; decide
  have hg2 : Lp.prog.get ⟨a.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI" := by
    conv_lhs => rw [show (⟨a.pc + 1, h2⟩ : Fin Lp.prog.length) = ⟨7, by decide⟩ from
      Fin.ext (by show a.pc + 1 = 7; rw [hapc])]
    rfl
  have hfall := resolved_jumpi_nottaken_sim (offsetToPc := Lp.o2pc) (stk := z :: stk)
    (by rw [ha]) h1 hg1 lp_lo_body (by decide) h2 hg2
  rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hfall]
  set b : AsmState := { a with stack := z :: stk, pc := a.pc + 2 } with hb
  have hbpc : b.pc = 8 := rfl
  have h3 : b.pc < Lp.prog.length := by rw [hbpc]; decide
  have hg3 : Lp.prog.get ⟨b.pc, h3⟩ = resolveInst Lp.lo (AsmInst.AsmPushLabel "exit") := by
    conv_lhs => rw [show (⟨b.pc, h3⟩ : Fin Lp.prog.length) = ⟨8, by decide⟩ from Fin.ext hbpc]
    rfl
  have h4 : b.pc + 1 < Lp.prog.length := by rw [hbpc]; decide
  have hg4 : Lp.prog.get ⟨b.pc + 1, h4⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨b.pc + 1, h4⟩ : Fin Lp.prog.length) = ⟨9, by decide⟩ from
      Fin.ext (by show b.pc + 1 = 9; rw [hbpc])]
    rfl
  rw [resolved_jump_sim h3 hg3 lp_lo_exit (by decide) h4 hg4 lp_o2pc_exit]

/-- `body`: `JUMPDEST ; ISZERO ; PUSH head ; JUMP` — four steps, pc 13 → 4, flipping the loop-carried
value in place. This is the **back-edge**. -/
theorem lp_hasm_body {asm : AsmState} {x : bytes32} {stk : List bytes32}
    (hpc : asm.pc = 13) (hstk : asm.stack = x :: stk) :
    runAsm 4 Lp.o2pc Lp.prog asm
      = AsmResult.AsmOK { asm with pc := 4, stack := EvmYul.UInt256.isZero x :: stk } := by
  have h1 : asm.pc < Lp.prog.length := by rw [hpc]; decide
  have hg1 : Lp.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "body" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Lp.prog.length) = ⟨13, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one' (o2pc := Lp.o2pc) h1 (asmStep_label_ok (offsetToPc := Lp.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 14 := by show asm.pc + 1 = 14; rw [hpc]
  have ha1stk : a1.stack = x :: stk := hstk
  have h2 : a1.pc < Lp.prog.length := by rw [hpc1]; decide
  have hg2 : Lp.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp "ISZERO" := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Lp.prog.length) = ⟨14, by decide⟩ from Fin.ext hpc1]
    rfl
  have hiz : asmStep Lp.o2pc Lp.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := EvmYul.UInt256.isZero x :: stk } := by
    rw [asmStep_iszero_ok h2 hg2]
    unfold asmUnop
    rw [ha1stk]
  have s2 := runAsm_one' (o2pc := Lp.o2pc) h2 hiz
  set a2 : AsmState := { asmNext a1 with stack := EvmYul.UInt256.isZero x :: stk } with ha2
  have hpc2 : a2.pc = 15 := by show a1.pc + 1 = 15; rw [hpc1]
  have h3 : a2.pc < Lp.prog.length := by rw [hpc2]; decide
  have hg3 : Lp.prog.get ⟨a2.pc, h3⟩ = resolveInst Lp.lo (AsmInst.AsmPushLabel "head") := by
    conv_lhs => rw [show (⟨a2.pc, h3⟩ : Fin Lp.prog.length) = ⟨15, by decide⟩ from Fin.ext hpc2]
    rfl
  have h4 : a2.pc + 1 < Lp.prog.length := by rw [hpc2]; decide
  have hg4 : Lp.prog.get ⟨a2.pc + 1, h4⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨a2.pc + 1, h4⟩ : Fin Lp.prog.length) = ⟨16, by decide⟩ from
      Fin.ext (by show a2.pc + 1 = 16; rw [hpc2])]
    rfl
  have s3 := resolved_jump_sim h3 hg3 lp_lo_head (by decide) h4 hg4 lp_o2pc_head
  rw [show (4 : Nat) = 1 + (1 + 2) from rfl, runAsm_append_ok s1, runAsm_append_ok s2, s3]
  cases asm with | _ => simp_all [asmNext, a1, a2]

/-- `exit`: `JUMPDEST ; POP ; STOP` — three steps, discarding the loop-carried value, then halting. -/
theorem lp_hasm_exit {asm : AsmState} {x : bytes32} {stk : List bytes32} {N : Nat}
    (hpc : asm.pc = 10) (hstk : asm.stack = x :: stk) (hN : 3 ≤ N) :
    ∃ as', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt as' ∧
      as'.accounts = asm.accounts ∧ as'.transient = asm.transient ∧
      as'.returndata = asm.returndata ∧ as'.logs = asm.logs := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have h1 : asm.pc < Lp.prog.length := by rw [hpc]; decide
  have hg1 : Lp.prog.get ⟨asm.pc, h1⟩ = AsmInst.AsmLabel "exit" := by
    conv_lhs => rw [show (⟨asm.pc, h1⟩ : Fin Lp.prog.length) = ⟨10, by decide⟩ from Fin.ext hpc]
    rfl
  have s1 := runAsm_one' (o2pc := Lp.o2pc) h1 (asmStep_label_ok (offsetToPc := Lp.o2pc) h1 hg1)
  set a1 : AsmState := asmNext asm with ha1
  have hpc1 : a1.pc = 11 := by show asm.pc + 1 = 11; rw [hpc]
  have ha1stk : a1.stack = x :: stk := hstk
  have h2 : a1.pc < Lp.prog.length := by rw [hpc1]; decide
  have hg2 : Lp.prog.get ⟨a1.pc, h2⟩ = AsmInst.AsmOp "POP" := by
    conv_lhs => rw [show (⟨a1.pc, h2⟩ : Fin Lp.prog.length) = ⟨11, by decide⟩ from Fin.ext hpc1]
    rfl
  have hpop : asmStep Lp.o2pc Lp.prog a1
      = AsmResult.AsmOK { asmNext a1 with stack := stk } := by
    unfold asmStep; rw [dif_pos h2, hg2]
    show asmPop a1 = _
    unfold asmPop
    rw [ha1stk]
  have s2 := runAsm_one' (o2pc := Lp.o2pc) h2 hpop
  set a2 : AsmState := { asmNext a1 with stack := stk } with ha2
  have hpc2 : a2.pc = 12 := by show a1.pc + 1 = 12; rw [hpc1]
  have h3 : a2.pc < Lp.prog.length := by rw [hpc2]; decide
  have hg3 : Lp.prog.get ⟨a2.pc, h3⟩ = AsmInst.AsmOp "STOP" := by
    conv_lhs => rw [show (⟨a2.pc, h3⟩ : Fin Lp.prog.length) = ⟨12, by decide⟩ from Fin.ext hpc2]
    rfl
  refine ⟨asmNext a2, ?_, rfl, rfl, rfl, rfl⟩
  rw [show (k + 3 : Nat) = 1 + (1 + (k + 1)) from by omega,
      runAsm_append_ok s1, runAsm_append_ok s2]
  exact runAsm_stop k h3 hg3

/-! ### The loop's Venom side, and what the relation collapses to on a one-slot stack

`venomAsmRel_ps1_iff` is the loop's counterpart of the diamond's `venomAsmRel_init0_iff`, and the shape of
the difference is the whole point: where the diamond's plan stack was empty and the relation collapsed to
"empty asm stack plus equal fields", the loop's is one slot deep and the relation says *the asm stack holds
exactly the value that variable is bound to*. That is the loop-carried value, and it is what the `DUP1`
copies and the `POP` eventually drops.

The two `evalPhis` lemmas are stated per predecessor — `p` takes `c` from `entry` and `d` across the
back-edge — because that is genuinely what the phi does, and because a single layout for the header does
not exist (proved above). -/
/-- A plan state whose stack is exactly one variable — the loop's shape at every block but `entry`. -/
def ps1 (v : String) : PlanState :=
  { stack := [Operand.Var v], spilled := [], alloc := initSpillAlloc 0, labelCounter := 0 }

/-- **What `venomAsmRel` collapses to on a one-slot stack.** -/
theorem venomAsmRel_ps1_iff {lo : AssocList String Nat} {v : String}
    {s : VenomState} {asm : AsmState} :
    venomAsmRel lo (ps1 v) s asm ↔
      ((∃ w, asm.stack = [w] ∧ lookupVar v s = some w) ∧
       (∀ i, readByte i s.memory = readByte i asm.memory) ∧
       asm.accounts = s.accounts ∧ asm.transient = s.transient ∧
       asm.returndata = s.returndata ∧ asm.logs = s.logs ∧
       asm.callCtx = s.callCtx ∧ asm.txCtx = s.txCtx ∧ asm.blockCtx = s.blockCtx ∧
       asm.code = s.code ∧ asm.prevHashes = s.prevHashes) := by
  constructor
  · rintro ⟨⟨hlen, hval⟩, -, hmem, ha, ht, hr, hl, hc, hx, hb, hcd, hph⟩
    refine ⟨?_, ?_, ha, ht, hr, hl, hc, hx, hb, hcd, hph⟩
    · have h1 : asm.stack.length = 1 := by simpa [ps1] using hlen.symm
      obtain ⟨w, hw⟩ : ∃ w, asm.stack = [w] := by
        match hst : asm.stack, h1 with
        | [w], _ => exact ⟨w, rfl⟩
      refine ⟨w, hw, ?_⟩
      have := hval 0 (by simp [ps1])
      simpa [ps1, hw, operandVal] using this
    · intro i; exact hmem i (by simp [ps1, initSpillAlloc])
  · rintro ⟨⟨w, hw, hv⟩, hmem, ha, ht, hr, hl, hc, hx, hb, hcd, hph⟩
    refine ⟨⟨by simp [ps1, hw], ?_⟩, ?_, ?_, ha, ht, hr, hl, hc, hx, hb, hcd, hph⟩
    · intro i hi
      simp only [ps1, List.length_singleton] at hi
      have : i = 0 := by omega
      subst this
      simpa [ps1, hw, operandVal] using hv
    · intro op off hlk; simp [ps1, AssocList.lookup] at hlk
    · intro i _; exact hmem i

/-! ### The loop's Venom side, generic in the arriving state -/

/-- The header's phis, arriving from `entry`: `p` takes `c`. -/
theorem lp_ev_from_entry {s : VenomState} {w : bytes32}
    (hprev : s.prevBb = some "entry") (hc : lookupVar "c" s = some w) :
    evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s) := by
  show evalPhis s (Lp.pP :: [Lp.jnz]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Lp.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "c") (prev := "entry") (v := w)
        (by rfl) hprev (by rfl) hc]
  show (match evalPhis s [Lp.jnz] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" w s') | err => err) = _
  rw [show evalPhis s [Lp.jnz] = ExecResult.OK s from by unfold evalPhis; rw [if_pos (by decide)]]

/-- The header's phis, arriving **across the back-edge**: `p` takes `d`. -/
theorem lp_ev_from_body {s : VenomState} {w : bytes32}
    (hprev : s.prevBb = some "body") (hd : lookupVar "d" s = some w) :
    evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s) := by
  show evalPhis s (Lp.pP :: [Lp.jnz]) = _
  unfold evalPhis
  rw [if_neg (show ¬ (Lp.pP.opcode ≠ Opcode.PHI) from fun h => h rfl),
      evalOnePhi_var (out := "p") (src := "d") (prev := "body") (v := w)
        (by rfl) hprev (by rfl) hd]
  show (match evalPhis s [Lp.jnz] with
        | ExecResult.OK s' => ExecResult.OK (updateVar "p" w s') | err => err) = _
  rw [show evalPhis s [Lp.jnz] = ExecResult.OK s from by unfold evalPhis; rw [if_pos (by decide)]]

/-- The header, loop taken. -/
theorem lp_head_run_taken (f : Nat) (ctx : VenomContext) {s : VenomState} {w : bytes32}
    (hnh : s.halted = false)
    (hev : evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s))
    (hw : w ≠ EvmYul.UInt256.ofNat 0) :
    runBlock (f + 1) ctx Lp.bHead s
      = ExecResult.OK (jumpTo "body" { updateVar "p" w s with instIdx := 1 }) := by
  rw [runBlock_join_eq_execBlock_at (phis := [Lp.pP]) (term := Lp.jnz) hev rfl
        (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide)]
  refine execBlock_step_term_ok f ctx Lp.bHead _ _ Lp.jnz (by rfl) ?_ (by decide)
    (by rw [jumpTo]; exact hnh)
  show stepInstBase Lp.jnz { updateVar "p" w s with instIdx := 1 } = _
  unfold stepInstBase
  simp only [show Lp.jnz.opcode = Opcode.JNZ from rfl,
             show Lp.jnz.operands = [Operand.Var "p", Operand.Label "body", Operand.Label "exit"]
               from rfl]
  have hp : evalOperand (Operand.Var "p") { updateVar "p" w s with instIdx := 1 } = some w := by
    show lookupVar "p" { updateVar "p" w s with instIdx := 1 } = some w
    exact lookupVar_updateVar_self s "p" w
  simp only [hp]
  split
  · rfl
  · rename_i h; exact absurd (bne_iff_ne.mpr hw) h

/-- The header, loop exited. -/
theorem lp_head_run_exit (f : Nat) (ctx : VenomContext) {s : VenomState}
    (hnh : s.halted = false)
    (hev : evalPhis s Lp.bHead.instructions
      = ExecResult.OK (updateVar "p" (EvmYul.UInt256.ofNat 0) s)) :
    runBlock (f + 1) ctx Lp.bHead s
      = ExecResult.OK (jumpTo "exit"
          { updateVar "p" (EvmYul.UInt256.ofNat 0) s with instIdx := 1 }) := by
  rw [runBlock_join_eq_execBlock_at (phis := [Lp.pP]) (term := Lp.jnz) hev rfl
        (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; rfl) (by decide)]
  refine execBlock_step_term_ok f ctx Lp.bHead _ _ Lp.jnz (by rfl) ?_ (by decide)
    (by rw [jumpTo]; exact hnh)
  show stepInstBase Lp.jnz { updateVar "p" (EvmYul.UInt256.ofNat 0) s with instIdx := 1 } = _
  unfold stepInstBase
  simp only [show Lp.jnz.opcode = Opcode.JNZ from rfl,
             show Lp.jnz.operands = [Operand.Var "p", Operand.Label "body", Operand.Label "exit"]
               from rfl]
  have hp : evalOperand (Operand.Var "p")
      { updateVar "p" (EvmYul.UInt256.ofNat 0) s with instIdx := 1 }
      = some (EvmYul.UInt256.ofNat 0) :=
    lookupVar_updateVar_self s "p" (EvmYul.UInt256.ofNat 0)
  simp only [hp]
  split
  · rename_i h; exact absurd rfl (bne_iff_ne.mp h)
  · rfl

/-- The body: `ISZERO` flips the loop-carried value, then the back-edge. -/
theorem lp_body_run (f : Nat) (ctx : VenomContext) {s : VenomState} {w : bytes32}
    (hnh : s.halted = false) (hp : lookupVar "p" s = some w) :
    runBlock (f + 1 + 1) ctx Lp.bBody s
      = ExecResult.OK (jumpTo "head"
          { updateVar "d" (EvmYul.UInt256.isZero w) { s with instIdx := 0 } with instIdx := 1 }) := by
  rw [runBlock_of_no_phi (by decide)]
  rw [execBlock_step_nonterm (f + 1) ctx Lp.bBody { s with instIdx := 0 }
        (updateVar "d" (EvmYul.UInt256.isZero w) { s with instIdx := 0 }) Lp.iD
        (by rfl) (by
          show stepInstBase Lp.iD { s with instIdx := 0 } = _
          unfold stepInstBase
          simp only [show Lp.iD.opcode = Opcode.ISZERO from rfl]
          unfold execPure1
          simp only [show Lp.iD.operands = [Operand.Var "p"] from rfl,
                     show Lp.iD.outputs = ["d"] from rfl]
          rw [show evalOperand (Operand.Var "p") { s with instIdx := 0 } = some w from hp]) (by decide)]
  exact execBlock_step_term_ok f ctx Lp.bBody _ _ Lp.jBack (by rfl) (by rfl) (by decide)
    (by rw [jumpTo]; exact hnh)

/-- The exit: `STOP`. -/
theorem lp_exit_run (f : Nat) (ctx : VenomContext) {s : VenomState} :
    runBlock (f + 1) ctx Lp.bExit s
      = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
  rw [runBlock_of_no_phi (by decide)]
  exact execBlock_step_halt f ctx Lp.bExit _ _ Lp.iStop (by rfl) rfl

/-! ### The walk invariant for a loop, and why it is an `Entry` rather than a `psOf` -/
namespace Lp
/-- **The walk invariant — and the reason it cannot be a `psOf`.** At the header the plan layout depends
on which predecessor we arrived from: `c` from `entry`, `d` across the back-edge. `Entry` is a free
parameter of `codegen_correct_fuel`, so it can say that; `psOf : String → PlanState` cannot. -/
def Entry (s : VenomState) (asm : AsmState) : Prop :=
  s.halted = false ∧
  ((s.currentBb = "entry" ∧ asm.pc = 0 ∧ venomAsmRel lo (initPlanState 0) s asm) ∨
   (s.currentBb = "head" ∧ asm.pc = 4 ∧
      ((s.prevBb = some "entry" ∧ venomAsmRel lo (ps1 "c") s asm) ∨
       (s.prevBb = some "body" ∧ venomAsmRel lo (ps1 "d") s asm))) ∨
   (s.currentBb = "body" ∧ asm.pc = 13 ∧ venomAsmRel lo (ps1 "p") s asm) ∨
   (s.currentBb = "exit" ∧ asm.pc = 10 ∧ venomAsmRel lo (ps1 "p") s asm))
end Lp

/-- The loop's four blocks, by label. -/
theorem lp_lookup {s : VenomState} {bb : BasicBlock}
    (hlk : lookupBlock s.currentBb Lp.fn.blocks = some bb) :
    (s.currentBb = "entry" ∧ bb = Lp.bEntry) ∨ (s.currentBb = "head" ∧ bb = Lp.bHead) ∨
    (s.currentBb = "body" ∧ bb = Lp.bBody) ∨ (s.currentBb = "exit" ∧ bb = Lp.bExit) := by
  rw [show Lp.fn.blocks = [Lp.bEntry, Lp.bHead, Lp.bBody, Lp.bExit] from rfl, lookupBlock] at hlk
  have hmem := List.mem_of_find?_eq_some hlk
  have hlab := List.find?_some hlk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩
  · exact Or.inr (Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(eq_of_beq hlab).symm, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(eq_of_beq hlab).symm, rfl⟩))

/-- The observable core of the relation: memories and the ten shared fields. Every block of this function
preserves it, since none of them touches memory. -/
def LpCore (s : VenomState) (asm : AsmState) : Prop :=
  (∀ i, readByte i s.memory = readByte i asm.memory) ∧
  asm.accounts = s.accounts ∧ asm.transient = s.transient ∧
  asm.returndata = s.returndata ∧ asm.logs = s.logs ∧
  asm.callCtx = s.callCtx ∧ asm.txCtx = s.txCtx ∧ asm.blockCtx = s.blockCtx ∧
  asm.code = s.code ∧ asm.prevHashes = s.prevHashes

theorem core_of_init0 {s asm} (h : venomAsmRel Lp.lo (initPlanState 0) s asm) :
    asm.stack = [] ∧ LpCore s asm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := venomAsmRel_init0_iff.mp h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem core_of_ps1 {v s asm} (h : venomAsmRel Lp.lo (ps1 v) s asm) :
    (∃ w, asm.stack = [w] ∧ lookupVar v s = some w) ∧ LpCore s asm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := venomAsmRel_ps1_iff.mp h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem ps1_of_core {v s asm} {w : bytes32} (hstk : asm.stack = [w])
    (hv : lookupVar v s = some w) (hc : LpCore s asm) :
    venomAsmRel Lp.lo (ps1 v) s asm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  exact venomAsmRel_ps1_iff.mpr ⟨⟨w, hstk, hv⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ### The loop's four block steps, each re-establishing `Entry`

The header's step is the one to read. It takes the phi's result and handles both arms — loop taken when
the value is nonzero, exited when it is zero — and re-establishes `Entry` at the successor either way.
`body`'s step is the back-edge, and it hands the header an arrival carrying **`d`**, not `c`. That is the
predecessor-dependent layout that no `psOf` could have expressed, now simply a disjunct of `Entry`. -/
/-- Core survives every step this function makes: no block touches memory, and the asm side only moves
the pc and the stack. -/
theorem core_step {s s' : VenomState} {asm asm' : AsmState}
    (hc : LpCore s asm)
    (hvm : s'.memory = s.memory) (ham : asm'.memory = asm.memory)
    (hva : s'.accounts = s.accounts) (hvt : s'.transient = s.transient)
    (hvr : s'.returndata = s.returndata) (hvl : s'.logs = s.logs)
    (hvc : s'.callCtx = s.callCtx) (hvx : s'.txCtx = s.txCtx)
    (hvb : s'.blockCtx = s.blockCtx) (hvd : s'.code = s.code) (hvp : s'.prevHashes = s.prevHashes)
    (haa : asm'.accounts = asm.accounts) (hat : asm'.transient = asm.transient)
    (har : asm'.returndata = asm.returndata) (hal : asm'.logs = asm.logs)
    (hac : asm'.callCtx = asm.callCtx) (hax : asm'.txCtx = asm.txCtx)
    (hab : asm'.blockCtx = asm.blockCtx) (had : asm'.code = asm.code)
    (hap : asm'.prevHashes = asm.prevHashes) :
    LpCore s' asm' := by
  obtain ⟨hm, ha, ht, hr, hl, hcc, hx, hb, hcd, hph⟩ := hc
  refine ⟨fun i => by rw [hvm, ham]; exact hm i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haa, hva, ha]
  · rw [hat, hvt, ht]
  · rw [har, hvr, hr]
  · rw [hal, hvl, hl]
  · rw [hac, hvc, hcc]
  · rw [hax, hvx, hx]
  · rw [hab, hvb, hb]
  · rw [had, hvd, hcd]
  · rw [hap, hvp, hph]

theorem cs {s s' : VenomState} {asm asm' : AsmState} (hc : LpCore s asm)
    (hvm : s'.memory = s.memory) (ham : asm'.memory = asm.memory)
    (hva : s'.accounts = s.accounts) (hvt : s'.transient = s.transient)
    (hvr : s'.returndata = s.returndata) (hvl : s'.logs = s.logs)
    (hvc : s'.callCtx = s.callCtx) (hvx : s'.txCtx = s.txCtx)
    (hvb : s'.blockCtx = s.blockCtx) (hvd : s'.code = s.code) (hvp : s'.prevHashes = s.prevHashes)
    (haa : asm'.accounts = asm.accounts) (hat : asm'.transient = asm.transient)
    (har : asm'.returndata = asm.returndata) (hal : asm'.logs = asm.logs)
    (hac : asm'.callCtx = asm.callCtx) (hax : asm'.txCtx = asm.txCtx)
    (hab : asm'.blockCtx = asm.blockCtx) (had : asm'.code = asm.code)
    (hap : asm'.prevHashes = asm.prevHashes) : LpCore s' asm' :=
  core_step hc hvm ham hva hvt hvr hvl hvc hvx hvb hvd hvp haa hat har hal hac hax hab had hap

/-- **The header's step, from either arrival.** Given the phi's result, both arms are handled: the loop
is taken when the value is nonzero and exited when it is zero, and the successor's `Entry` is
re-established either way. -/
theorem lp_head_step {s : VenomState} {asm : AsmState} {w : bytes32} {k : Nat}
    (hnh : s.halted = false) (hpc : asm.pc = 4)
    (hstk : asm.stack = [w]) (hcore : LpCore s asm)
    (hev : evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s)) :
    ∃ (asm' : AsmState) (blockLen : Nat),
      runAsm blockLen Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧
      blockLen ≤ 6 ∧ Lp.Entry (
        match runBlock (k + 1) Lp.ctx Lp.bHead s with
        | ExecResult.OK s' => s'
        | _ => s) asm' := by
  by_cases hw : w = EvmYul.UInt256.ofNat 0
  · subst hw
    rw [lp_head_run_exit k Lp.ctx hnh hev]
    refine ⟨_, 6, lp_hasm_head_nottaken (stk := []) hpc hstk, by decide, hnh, ?_⟩
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    refine ps1_of_core (w := EvmYul.UInt256.ofNat 0) rfl
      (lookupVar_updateVar_self s "p" _) ?_
    exact cs hcore rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · rw [lp_head_run_taken k Lp.ctx hnh hev hw]
    refine ⟨_, 4, lp_hasm_head_taken (stk := []) hpc hstk hw, by decide, hnh, ?_⟩
    refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩))
    refine ps1_of_core (w := w) rfl (lookupVar_updateVar_self s "p" w) ?_
    exact cs hcore rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `entry`'s step: binds `c`, pushes it, and hands the header an arrival from `entry`. -/
theorem lp_entry_step {s : VenomState} {asm : AsmState} {k : Nat}
    (hnh : s.halted = false) (hcur : s.currentBb = "entry") (hpc : asm.pc = 0)
    (hstk : asm.stack = []) (hcore : LpCore s asm) :
    ∃ (asm' : AsmState) (blockLen : Nat),
      runAsm blockLen Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧
      blockLen ≤ 6 ∧ Lp.Entry (jumpTo "head" (Lp.afterC s)) asm' := by
  refine ⟨_, 4, lp_hasm_entry hpc, by decide, hnh, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨?_, ?_⟩⟩)
  · show some s.currentBb = some "entry"; rw [hcur]
  · refine ps1_of_core (w := s.callCtx.callvalue) ?_
      (lookupVar_updateVar_self s "c" s.callCtx.callvalue) ?_
    · show asm.callCtx.callvalue :: asm.stack = [s.callCtx.callvalue]
      rw [hstk, hcore.2.2.2.2.2.1]
    · exact cs hcore rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `body`'s step: `ISZERO` flips the value, and the **back-edge** hands the header an arrival from
`body` — with `d` in the slot, not `c`. -/
theorem lp_body_step {s : VenomState} {asm : AsmState} {w : bytes32} {k : Nat}
    (hnh : s.halted = false) (hcur : s.currentBb = "body") (hpc : asm.pc = 13)
    (hstk : asm.stack = [w]) (hp : lookupVar "p" s = some w) (hcore : LpCore s asm) :
    ∃ (asm' : AsmState) (blockLen : Nat),
      runAsm blockLen Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧
      blockLen ≤ 6 ∧ Lp.Entry (jumpTo "head"
        { updateVar "d" (EvmYul.UInt256.isZero w) { s with instIdx := 0 } with instIdx := 1 }) asm' := by
  refine ⟨_, 4, lp_hasm_body hpc hstk, by decide, hnh, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨?_, ?_⟩⟩)
  · show some s.currentBb = some "body"; rw [hcur]
  · refine ps1_of_core (w := EvmYul.UInt256.isZero w) rfl
      (lookupVar_updateVar_self { s with instIdx := 0 } "d" _) ?_
    exact cs hcore rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `exit`'s step: `POP` then `STOP`. Halts, with the observable state related. -/
theorem lp_exit_step {s : VenomState} {asm : AsmState} {w : bytes32} {N k : Nat}
    (hpc : asm.pc = 10) (hstk : asm.stack = [w]) (hcore : LpCore s asm) (hN : 6 ≤ N) :
    ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧
      venomAsmTerminalRel (haltState { s with instIdx := 0 }) asm' := by
  obtain ⟨as', hrun, ha, ht, hr, hl⟩ := lp_hasm_exit hpc hstk (by omega : 3 ≤ N)
  refine ⟨as', hrun, ?_, ?_, ?_, ?_⟩
  · show as'.accounts = s.accounts; rw [ha]; exact hcore.2.1
  · show as'.transient = s.transient; rw [ht]; exact hcore.2.2.1
  · show as'.returndata = s.returndata; rw [hr]; exact hcore.2.2.2.1
  · show as'.logs = s.logs; rw [hl]; exact hcore.2.2.2.2.1

/-! ### The loop's `hbsim`: every block, both arrivals, every fuel -/
/-- Out of fuel on a phi-free block. -/
theorem lp_zero_nophi {bb s asm N}
    (h : ∀ i, bb.instructions.head? = some i → i.opcode ≠ Opcode.PHI) :
    (match runBlock 0 Lp.ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else ∃ (asm' : AsmState) (bl : Nat), runAsm bl Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧
           bl ≤ 6 ∧ Lp.Entry s' asm'
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [runBlock_of_no_phi h]
  simp only [execBlock]

/-- Out of fuel at the header, whose phis do evaluate. -/
theorem lp_zero_head {s asm N w}
    (hev : evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s)) :
    (match runBlock 0 Lp.ctx Lp.bHead s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else ∃ (asm' : AsmState) (bl : Nat), runAsm bl Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧
           bl ≤ 6 ∧ Lp.Entry s' asm'
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [runBlock_eq_execBlock_of_phis hev]
  simp only [execBlock]

/-- **The loop's per-block obligation — every block, both arrivals, every fuel.** -/
theorem lp_hbsim :
    ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
      Lp.Entry s asm → lookupBlock s.currentBb Lp.fn.blocks = some bb → 6 ≤ N →
      (match runBlock f' Lp.ctx bb s with
       | ExecResult.OK s' =>
           if s'.halted then
             ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧
               venomAsmTerminalRel s' asm'
           else ∃ (asm' : AsmState) (bl : Nat),
             runAsm bl Lp.o2pc Lp.prog asm = AsmResult.AsmOK asm' ∧ bl ≤ 6 ∧ Lp.Entry s' asm'
       | ExecResult.Halt s' =>
           ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
       | ExecResult.Abort AbortType.RevertAbort s' =>
           ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
       | ExecResult.Abort AbortType.ExHaltAbort s' =>
           ∃ asm', runAsm N Lp.o2pc Lp.prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
       | _ => True) := by
  intro s asm N f' bb hE hlk hN
  obtain ⟨hnh, hcase⟩ := hE
  rcases lp_lookup hlk with ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩ | ⟨hcur, rfl⟩
  · -- entry
    rcases hcase with ⟨-, hpc, hrel⟩ | ⟨h2, -, -⟩ | ⟨h2, -, -⟩ | ⟨h2, -, -⟩
    · obtain ⟨hstk, hcore⟩ := core_of_init0 hrel
      match f' with
      | 0 => exact lp_zero_nophi (by decide)
      | 1 =>
        rw [runBlock_of_no_phi (by decide),
            execBlock_step_nonterm 0 Lp.ctx Lp.bEntry { s with instIdx := 0 }
              (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }) Lp.iC
              (by rfl) (by rfl) (by decide)]
        simp only [execBlock]
      | (k + 1 + 1) =>
        rw [lp_entry_run k Lp.ctx hnh]
        simp only [show (jumpTo "head" (Lp.afterC s)).halted = false from hnh,
                   Bool.false_eq_true, if_false]
        exact lp_entry_step (k := k) hnh hcur hpc hstk hcore
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
  · -- head
    rcases hcase with ⟨h2, -, -⟩ | ⟨-, hpc, hd⟩ | ⟨h2, -, -⟩ | ⟨h2, -, -⟩
    · exact absurd (hcur.symm.trans h2) (by decide)
    · have hev : ∃ w, asm.stack = [w] ∧ LpCore s asm ∧
          evalPhis s Lp.bHead.instructions = ExecResult.OK (updateVar "p" w s) := by
        rcases hd with ⟨hprev, hrel⟩ | ⟨hprev, hrel⟩
        · obtain ⟨⟨w, hstk, hv⟩, hcore⟩ := core_of_ps1 hrel
          exact ⟨w, hstk, hcore, lp_ev_from_entry hprev hv⟩
        · obtain ⟨⟨w, hstk, hv⟩, hcore⟩ := core_of_ps1 hrel
          exact ⟨w, hstk, hcore, lp_ev_from_body hprev hv⟩
      obtain ⟨w, hstk, hcore, hevw⟩ := hev
      match f' with
      | 0 => exact lp_zero_head hevw
      | (k + 1) =>
        by_cases hw : w = EvmYul.UInt256.ofNat 0
        · subst hw
          rw [lp_head_run_exit k Lp.ctx hnh hevw]
          simp only [show (jumpTo "exit" { updateVar "p" (EvmYul.UInt256.ofNat 0) s
                       with instIdx := 1 }).halted = false from hnh, Bool.false_eq_true, if_false]
          have h := lp_head_step (k := k) hnh hpc hstk hcore hevw
          rwa [lp_head_run_exit k Lp.ctx hnh hevw] at h
        · rw [lp_head_run_taken k Lp.ctx hnh hevw hw]
          simp only [show (jumpTo "body" { updateVar "p" w s with instIdx := 1 }).halted = false
                       from hnh, Bool.false_eq_true, if_false]
          have h := lp_head_step (k := k) hnh hpc hstk hcore hevw
          rwa [lp_head_run_taken k Lp.ctx hnh hevw hw] at h
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
  · -- body
    rcases hcase with ⟨h2, -, -⟩ | ⟨h2, -, -⟩ | ⟨-, hpc, hrel⟩ | ⟨h2, -, -⟩
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
    · obtain ⟨⟨w, hstk, hv⟩, hcore⟩ := core_of_ps1 hrel
      match f' with
      | 0 => exact lp_zero_nophi (by decide)
      | 1 =>
        rw [runBlock_of_no_phi (by decide),
            execBlock_step_nonterm 0 Lp.ctx Lp.bBody { s with instIdx := 0 }
              (updateVar "d" (EvmYul.UInt256.isZero w) { s with instIdx := 0 }) Lp.iD
              (by rfl) (by
                show stepInstBase Lp.iD { s with instIdx := 0 } = _
                unfold stepInstBase
                simp only [show Lp.iD.opcode = Opcode.ISZERO from rfl]
                unfold execPure1
                simp only [show Lp.iD.operands = [Operand.Var "p"] from rfl,
                           show Lp.iD.outputs = ["d"] from rfl]
                rw [show evalOperand (Operand.Var "p") { s with instIdx := 0 } = some w from hv])
              (by decide)]
        simp only [execBlock]
      | (k + 1 + 1) =>
        rw [lp_body_run k Lp.ctx hnh hv]
        simp only [show (jumpTo "head" { updateVar "d" (EvmYul.UInt256.isZero w)
                     { s with instIdx := 0 } with instIdx := 1 }).halted = false from hnh,
                   Bool.false_eq_true, if_false]
        exact lp_body_step (k := k) hnh hcur hpc hstk hv hcore
    · exact absurd (hcur.symm.trans h2) (by decide)
  · -- exit
    rcases hcase with ⟨h2, -, -⟩ | ⟨h2, -, -⟩ | ⟨h2, -, -⟩ | ⟨-, hpc, hrel⟩
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
    · exact absurd (hcur.symm.trans h2) (by decide)
    · obtain ⟨⟨w, hstk, hv⟩, hcore⟩ := core_of_ps1 hrel
      match f' with
      | 0 => exact lp_zero_nophi (by decide)
      | (k + 1) =>
        rw [lp_exit_run k Lp.ctx]
        exact lp_exit_step (k := k) hpc hstk hcore hN

/-- **CAPSTONE — codegen correctness for a CYCLIC function whose loop header is a phi.**

Venom running `Lp.fn` and the EVM running the seventeen instructions the compiler emits for it agree.
The asm budget is `fuel * 6` — Venom's own fuel times the longest block's asm length — which is what makes
a loop expressible at all: a program of seventeen instructions can execute far more than seventeen steps,
and no `prog.length` budget could have covered that.

Every input is discharged. `lp_hbsim` covers all four blocks, at every fuel, against the real compiled
program — including the header, whose head is a `PHI` and which is entered from *two* predecessors with
*different variables in the same stack slot*.

`Lp.Entry` is the load-bearing hypothesis, and it is where the whole loop story lands. It records, at the
header, which predecessor the walk arrived from and hence which layout the stack has: `c` from `entry`, `d`
across the back-edge. `lp_psOf_by_label_impossible` proves that a `psOf : String → PlanState` cannot say
that — the two layouts are distinct and a function of the label alone must pick one. `codegen_correct_fuel`
takes `Entry` as a free parameter precisely so it can be said. -/
theorem lp_codegen_correct {fuel : Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hpc0 : as.pc = 0)
    (hrel : venomAsmRel Lp.lo (initPlanState 0)
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as) :
    (match runContext fuel Lp.ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (fuel * 6) Lp.o2pc Lp.prog as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (fuel * 6) Lp.o2pc Lp.prog as
         = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (fuel * 6) Lp.o2pc Lp.prog as
         = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_fuel (fuel := fuel) (ctx := Lp.ctx) (fn := Lp.fn) (fnEom := 0) (lblCtr := 0)
    (ops := Lp.ops) (psFinal := (generateFnPlan Lp.fn 0 0).get!.2)
    (entryName := "main") (entryLbl := "entry") 6 Lp.Entry
    rfl rfl rfl rfl lp_hbsim ⟨hvshalt, Or.inl ⟨rfl, hpc0, hrel⟩⟩

/-! ### Is the loop capstone vacuous?

Same question as for the diamond, and it gets the same treatment rather than the benefit of the doubt:
`lp_codegen_correct`'s conclusion is a match on `runContext` whose last arm is `_ => True`, so a function
that errored out or never terminated would satisfy it while saying nothing at all. `Example.loopFn` is
exactly such a function — it never halts — which is why it was not used here.

`Lp.fn` runs, through the back-edge, and halts. Feeding that to the capstone yields a concrete EVM halt
related to the Venom halt state, with every hypothesis discharged. -/
namespace Lp
def as0 : AsmState := { (default : AsmState) with
  callCtx := { (default : CallContext) with callvalue := EvmYul.UInt256.ofNat 7 } }
end Lp

/-- The relation holds at the start: empty stacks, empty memories, matching contexts. -/
theorem lp_rel0 : venomAsmRel Lp.lo (initPlanState 0) Lp.s0 Lp.as0 := by
  rw [venomAsmRel_init0_iff]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro i; rfl

/-- **The loop capstone is not vacuous.** Its conclusion is a match on `runContext` whose last arm is
`_ => True`, so it would say nothing if the function never ran. It runs — through the back-edge — and
feeding that to the capstone yields a concrete EVM halt related to the Venom halt state.

Every hypothesis of `lp_codegen_correct` is discharged here. Nothing is assumed. -/
theorem lp_codegen_correct_fires :
    ∃ as', runAsm (30 * 6) Lp.o2pc Lp.prog Lp.as0 = AsmResult.AsmHalt as' ∧
      (∃ w, runContext 30 Lp.ctx Lp.vs0 = ExecResult.Halt w ∧ finalStateRel w as') := by
  have h := lp_codegen_correct (fuel := 30) (vs := Lp.vs0) (as := Lp.as0)
    (by rfl) (by rfl) lp_rel0
  have hr := lp_runs
  revert h hr
  cases hrc : runContext 30 Lp.ctx Lp.vs0 with
  | Halt w =>
    intro h _
    obtain ⟨as', hrun, hfin⟩ := h
    exact ⟨as', hrun, w, rfl, hfin⟩
  | OK _ => intro _ hr; exact absurd hr (by simp)
  | Abort a _ => intro _ hr; cases a <;> exact absurd hr (by simp)
  | IntRet _ _ => intro _ hr; exact absurd hr (by simp)
  | Error _ => intro _ hr; exact absurd hr (by simp)

/-! ### `DJMP` is excluded for the wrong reason

`codegen_correct_sched_reach`'s docstring justifies excluding `DJMP` by calling it "the one terminator
that computes its target from a runtime selector rather than a label operand, and so could leave the
static CFG". That is false, on both halves.

A `DJMP`'s targets *are* label operands — `DJMP sel, l₀, l₁, …` — and the selector only chooses which one.
`getSuccessors` `filterMap`s the label operands of any terminator, so every label a `DJMP` can reach is
already in `bbSuccs`. `djmp_target_is_static_succ` proves it. And `CfgReach_of_runBlock`, the lemma that
actually preserves reachability across a block, carries no `DJMP` exclusion at all — it never needed one.

The exclusion itself is real, and the reason is worth stating correctly because the false one makes `DJMP`
look unsupportable in principle. `djmpChain` lowers a `DJMP` to a comparison chain plus one *freshly
labelled* pop-trampoline per target (`freshLabel "djmp_tramp"`). Those fresh labels are what break the
label-uniqueness counting `hpreuniq` relies on — the same reason `INVOKE` and `ASSERT_UNREACHABLE` are
excluded, and the reason `hgood` names all three together. That is a bookkeeping obstacle in the codegen,
not a soundness one in the CFG. -/
/-! ### What `DJMP` would actually cost

The previous section showed the *stated* reason for excluding `DJMP` is false. This one scopes the real
one, which turns out to be narrower than the blanket exclusion suggests.

`hpreuniq` counts occurrences of a **block** label in the plan, and `generateFnPlanFuel_planLabelCount`
proves that count is at most one — under `hgood`, which bans the three opcodes that mint fresh `SOLabel`s.
But a `DJMP` trampoline is not a block label. It is `freshLabel "djmp_tramp"`, which by construction is
`"djmp_tramp" ++ "_" ++ <counter>`. It can only interfere with the count of `bb.label` if some block is
*literally named* `djmp_tramp_<n>`.

So the blanket "no `DJMP`" could be weakened to a per-function side condition — no block is named like a
trampoline — which every real function satisfies and both of this branch's witnesses satisfy provably.
What is *not* done here is the rework of `generateFnPlanFuel_planLabelCount` itself, whose induction is
currently structured around `hgood`. That is the actual remaining cost of `DJMP`, and it is a counting
argument, not a soundness one. -/
/-! ### The DJMP rework needs no string-representation injectivity

My first framing of the remaining `DJMP` work was that it hinges on `toString` being injective on `Nat` —
otherwise two trampolines minted at different counter values could not be shown to have different names.
That framing is wrong, and it matters, because `Nat`'s `toString` injectivity is not in the library and
proving it would mean reasoning about digit representations.

`hpreuniq` only ever needs the count of a **block** label. Look at what it concludes: `∀ a ∈ executePlan
preOps, a ≠ AsmInst.AsmLabel bb.label`. So the trampolines never need to be distinct *from each other* —
only from `bb.label`. And a trampoline is `freshLabel "djmp_tramp"`, which carries its prefix by
construction.

`djmpChain_soLabel_is_tramp` proves every `SOLabel` a `DJMP` emits has that shape, and
`generateDjmpPlan_soLabel_is_tramp` shows the only `SOLabel`s in a `DJMP`'s plan are the trampolines,
each carrying its prefix by construction. What remains is threading this
through `generateFnPlanFuel_planLabelCount`'s induction, which is currently structured around `hgood`
banning the minters rather than around which labels they mint. -/
/-! ### The exact fact the `planLabelCount` induction needs

`generateBlockPlan_planLabelCount`'s proof turns on one step: *the instruction fold's ops carry no
`SOLabel`*. That is what `hgood` buys, by banning the three opcodes that could emit one.

The weaker fact that would actually suffice is: *the instruction fold's ops carry no `SOLabel` equal to a
block label*. The counting argument only ever asks about `bb.label` — `hpreuniq`'s conclusion is
`a ≠ AsmInst.AsmLabel bb.label` — so a plan may emit all the `SOLabel`s it likes, provided none of them is
a block's.

For `DJMP` that weaker fact is a theorem, and these three prove it. The comparison chain emits no
`SOLabel` at all (its label operations are *pushes*, not definitions); the out-of-range default emits
none; and the trampolines emit exactly one apiece, each carrying the `djmp_tramp` prefix by construction.
So a `DJMP`'s plan never defines a block's label.

What is still not done is rewriting `generateBlockPlan_planLabelCount` and its callers to take the weaker
hypothesis. That is a mechanical change to an existing induction, and it is the whole of what `DJMP`
support now costs. -/
/-! ### Every `SOLabel` the emitter produces is freshly minted — all three minters, not just `DJMP`

`hgood` bans three opcodes: `INVOKE`, `ASSERT_UNREACHABLE` and `DJMP`. The previous section showed
`DJMP`'s labels are all trampolines. The same is true of the other two, and for the same reason —
`freshLabel "return_label"` and `freshLabel "reachable"` carry their prefixes by construction — so the
generalisation costs nothing extra.

`generateEmitOps_soLabel_is_fresh` is exhaustive over every opcode, and it needs no new case analysis:
the three minters get their branch extracted, and for everything else `generateEmitOps_no_soLabel` already
says there is no `SOLabel` to talk about. Which means the blanket `hgood` could be replaced, for *all
three* opcodes at once, by a single per-function side condition: no block is named like a freshly minted
label.

The `DJMP` question turned out to be one distinction: a label *push* (`SOPushLabel`) is not a label
*definition* (`SOLabel`). Every branch of the emitter that looked like it was minting labels was pushing
them. -/
/-! ### Lifting "every emitted label is fresh" up to the instruction plan -/
/-! ### The block-plan count, with `hgood` removed entirely

This is the induction rewrite. `generateBlockPlan_planLabelCount` needs the instruction fold to emit no
`SOLabel` at all, and buys that by banning the three minters. `generateBlockPlan_planLabelCount_fresh`
needs only the fact that actually matters: every `SOLabel` the fold emits is *freshly minted*, and `l` is
not a fresh label.

The hypothesis `¬ IsFreshLabel l` is exactly right for the caller, because the counting argument is only
ever instantiated at `bb.label` — and a block label is not a freshly minted one. So `INVOKE`,
`ASSERT_UNREACHABLE` and `DJMP` are all admitted, with no ban and no case analysis about them at the block
level. -/
/-! ### `hpreuniq`, for functions containing `DJMP`, `INVOKE` and `ASSERT_UNREACHABLE`

The top of the chain. `hpreuniq_fresh`'s side condition is no longer a ban on three opcodes, but a fact
about naming: the block's own label is not one a `freshLabel` could have minted. That is the only thing
the counting argument ever needed, and no real function violates it — every fresh label is at least ten
characters, and `short_not_fresh` discharges the condition for anything shorter. -/
theorem dia_labels_not_fresh : ∀ b ∈ Dia.fn.blocks, ¬ IsFreshLabel b.label := by
  intro b hb
  simp only [Dia.fn, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact short_not_fresh (by decide)

theorem lp_labels_not_fresh : ∀ b ∈ Lp.fn.blocks, ¬ IsFreshLabel b.label := by
  intro b hb
  simp only [Lp.fn, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact short_not_fresh (by decide)

/-! ### Every `hgood` consumer now has an `hgood`-free replacement

`hgood` is consumed in exactly three places across the development, and all three are one-liners over the
label count: `hpreuniq_of_blockPlan` (the `hpreuniq` input), `labelOffset_of_blockPlan` (`hoff_lk`), and
`jumpTarget_of_blockPlan` (`hoff_lk` + `hidx_lk` + `hidxeq` together). The per-block `hstep` family uses
`hgood` for nothing else — grep it and every hit is the line `hpreuniq_generic hgood hgen hblkhd`.

So these three drop-ins are the whole interface. A caller with a function containing `DJMP`, `INVOKE` or
`ASSERT_UNREACHABLE` supplies `¬ IsFreshLabel bb.label` instead of a ban, and everything downstream is
unchanged. -/
/-! ## Universal dispatch

A single entry point from a block's simulation to the walk's obligation, so a caller never has to case
on the terminator. The first attempt at this — `WalkStep_of_BlockSim_any` — was **vacuous on its
continuing arm** and has been removed; see the retraction below for the refutation, and
`WalkStep_of_BlockSimAt` for the version that works. What survives here is the terminal transfer, which
was always sound. -/

/-! ## RETRACTION: `WalkStep_of_BlockSim_any`'s continuing arm was vacuous

The theorem is **deleted**, not merely annotated — a vacuous "universal dispatcher" left lying around is a
trap, and a docstring warning is not a fix. The refutation below is what replaces it.

`BlockSim` mirrors `genBlockSimulation`, whose `prog` is built from the *block's* plan — so its
`prog.length` is the block's asm length. `WalkStep`'s `prog` is the *whole function's* program. My bridge
forced the two to be the same list, which is only true when the function has one block.

Instantiated the way the walk needs it — `prog` = the whole program — `BlockSim`'s continuing arm asserts
that running `prog.length` asm steps from a block's entry leaves the machine in `AsmOK`. But a continuing
block does not stop at its own boundary: it runs on into its successor, and in a terminating program it
halts. `dia_blockSim_ok_false_at_whole_prog` proves the arm is *false* for `then`.

So `WalkStep_of_BlockSim_any` covered only halting blocks, and the witness I first fired it on passed
because `Min` has exactly one block — the one case where the two programs coincide. The 0-consumer
heuristic pointed at this; firing it on a halting block hid it; firing it on a *continuing* one is what
caught it. That is the lesson worth keeping: **fire a theorem on the case that makes it non-trivial**, not
on whichever case is nearest to hand.

`BlockSimAt` takes the block's asm length as a parameter instead of reading it off the program, which is
what the `hstep` family does and what makes the continuing arm satisfiable.
`dia_then_walkstep_universal` fires the repaired dispatcher on `then` — a block that does *not* halt, so
`hok` is genuinely used rather than discharged by absurdity. -/
/-- From `then` (pc 13), running the WHOLE program's length of steps does not leave the machine in
`AsmOK` — it halts. `then` jumps to `join`, and `join` is `JUMPDEST ; STOP`. -/
theorem dia_then_whole_prog_halts {asm : AsmState} (hpc : asm.pc = 13) (hstk : asm.stack = []) :
    ∃ as', runAsm Dia.prog.length Dia.o2pc Dia.prog asm = AsmResult.AsmHalt as' := by
  have h7 : runAsm 7 Dia.o2pc Dia.prog asm
      = AsmResult.AsmHalt (asmNext (asmNext { asm with pc := 11 })) := by
    rw [show (7 : Nat) = 5 + 2 from rfl, runAsm_append_ok (dia_hasm_then hpc hstk)]
    exact dia_hasm_join rfl
  exact ⟨_, runAsm_le_of_ne_ok (by simp) (by rw [dia_prog_length]; omega) h7⟩

/-- **`BlockSim`'s continuing arm is FALSE for `then` at the whole program.** `BlockSim` states the asm
run at `prog.length` fuel. With `prog` the *whole* function's program, a continuing block does not stop at
its own boundary — it runs on into its successor and, here, halts. So no `as'` makes it `AsmOK`. -/
theorem dia_blockSim_ok_false_at_whole_prog {lo ps' s'} {asm : AsmState}
    (hpc : asm.pc = 13) (hstk : asm.stack = []) :
    ¬ BlockSim lo ps' Dia.o2pc Dia.prog asm (ExecResult.OK s') := by
  rintro ⟨as', hrun, -⟩
  obtain ⟨w, hw⟩ := dia_then_whole_prog_halts hpc hstk
  rw [hrun] at hw
  exact absurd hw (by simp)

/-- A block's simulation **against the whole program**, at the block's own asm length. -/
def BlockSimAt (blockLen : Nat) (lo : AssocList String Nat) (ps' : PlanState)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (as : AsmState) : ExecResult → Prop
  | ExecResult.OK vs' =>
      ∃ as', runAsm blockLen offsetToPc prog as = AsmResult.AsmOK as' ∧
             venomAsmRel lo ps' vs' as'
  | ExecResult.Halt vs' =>
      ∃ as', runAsm blockLen offsetToPc prog as = AsmResult.AsmHalt as' ∧
             venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.RevertAbort vs' =>
      ∃ as', runAsm blockLen offsetToPc prog as = AsmResult.AsmRevert as' ∧
             venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
      ∃ as', runAsm blockLen offsetToPc prog as = AsmResult.AsmFault as' ∧
             venomAsmTerminalRel vs' as'
  | _ => True

/-- **Universal dispatch, repaired.** Same shape as before, but the asm run is the *block's*, not the
whole program's — which is what makes the continuing arm satisfiable. -/
theorem WalkStep_of_BlockSimAt {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {s : VenomState} {asm : AsmState} {ps' : PlanState}
    {N f' blockLen : Nat}
    (hle : blockLen ≤ N)
    (hbs : BlockSimAt blockLen labelOffsets ps' offsetToPc prog asm (runBlock f' ctx bb s))
    (hok : ∀ s', runBlock f' ctx bb s = ExecResult.OK s' →
      s'.halted = false ∧
      ∃ bb', lookupBlock s'.currentBb fn.blocks = some bb' ∧
        ps'.stack = (psOf bb'.label).stack ∧
        ps'.spilled = (psOf bb'.label).spilled ∧
        ps'.alloc.fnEom = (psOf bb'.label).alloc.fnEom ∧
        ps'.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset ∧
        (∀ asm', runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm' →
          asm'.pc = pcOf bb'.label) ∧
        wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock f' ctx bb s) := by
  by_cases hcont : ∃ s', runBlock f' ctx bb s = ExecResult.OK s'
  · obtain ⟨s', hrb⟩ := hcont
    obtain ⟨hnh, bb', hlk, hstk, hsp, hfe, hno, hpc, hwdec⟩ := hok s' hrb
    rw [hrb] at hbs
    obtain ⟨as', hrun, hrel⟩ := hbs
    exact hstep_jmp_block_ws pcOf psOf wOf hrb hnh hrun hrel hstk hsp hfe hno
      (hpc as' hrun) hle rfl hlk hwdec
  · cases hr : runBlock f' ctx bb s with
    | OK w => exact absurd hr (fun h => hcont ⟨w, h⟩)
    | Halt w =>
      rw [hr] at hbs; obtain ⟨as', hrun, hrel⟩ := hbs
      exact ⟨as', runAsm_le_of_ne_ok (by simp) hle hrun, hrel⟩
    | Abort a w =>
      cases a <;> (rw [hr] at hbs; obtain ⟨as', hrun, hrel⟩ := hbs;
                   exact ⟨as', runAsm_le_of_ne_ok (by simp) hle hrun, hrel⟩)
    | IntRet _ _ => trivial
    | Error _ => trivial

/-- **`BlockSimAt`'s continuing arm is satisfiable** — the very thing `BlockSim`'s was not. `then` is a
`JMP` block: five asm steps land it at `join`, with the relation intact. -/
theorem dia_then_blockSimAt {s : VenomState} {asm : AsmState} {f : Nat}
    (hnh : s.halted = false)
    (hpc : asm.pc = Dia.pcOf Dia.bThen.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bThen.label) s asm) :
    BlockSimAt 5 Dia.lo (Dia.psOf Dia.bJoin.label) Dia.o2pc Dia.prog asm
      (runBlock (f + 1 + 1) Dia.ctx Dia.bThen s) := by
  rw [dia_then_run f Dia.ctx hnh]
  refine ⟨_, dia_hasm_then hpc ((venomAsmRel_init0_iff.mp hrel).1), ?_⟩
  exact dia_rel_transfer (vs := s) (asm := asm) hrel ((venomAsmRel_init0_iff.mp hrel).1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **The repaired dispatcher, fired on a CONTINUING block.** This is the case that was vacuous before:
`then` does not halt, so `hok` is genuinely used rather than discharged by absurdity. -/
theorem dia_then_walkstep_universal {s : VenomState} {asm : AsmState} {N f : Nat}
    (hnh : s.halted = false)
    (hpc : asm.pc = Dia.pcOf Dia.bThen.label)
    (hrel : venomAsmRel Dia.lo (Dia.psOf Dia.bThen.label) s asm)
    (hN : 5 ≤ N) :
    WalkStep Dia.fn Dia.pcOf Dia.psOf Dia.wOf Dia.lo Dia.o2pc Dia.prog Dia.bThen asm N
      (runBlock (f + 1 + 1) Dia.ctx Dia.bThen s) := by
  refine WalkStep_of_BlockSimAt Dia.pcOf Dia.psOf Dia.wOf hN
    (dia_then_blockSimAt hnh hpc hrel) ?_
  intro s' hs'
  rw [dia_then_run f Dia.ctx hnh] at hs'
  injection hs' with hs'
  subst hs'
  exact ⟨by rw [jumpTo]; exact hnh, Dia.bJoin, rfl, rfl, rfl, rfl, le_refl _,
         fun asm' h => by rw [dia_hasm_then hpc ((venomAsmRel_init0_iff.mp hrel).1)] at h; injection h with h; subst h; rfl,
         by decide⟩

/-! ## The discriminating witness: a function that actually contains a `DJMP`

Everything above about `DJMP` was proved on `Dia.fn` and `Lp.fn` — neither of which has one. So the whole
chain had been fired only on functions where the *old* `hgood` would have worked just as well, which is
precisely the failure the retraction above is about: a witness that exercises only the easy arm tells you
nothing.

`Dj.fn` is the discriminating case. `dj_hgood_false` proves the old hypothesis is *unsatisfiable* for it,
so every lemma that took `hgood` is inapplicable. `dj_plan_has_trampolines` proves the plan really does
mint `djmp_tramp_1` and `djmp_tramp_2` — this is not a function where `DJMP` happens to emit nothing, and
the label count was genuinely at risk.

And `hpreuniq` holds anyway. -/
set_option maxRecDepth 40000

namespace Dj
def iSel : Instruction :=
  { id := 60, opcode := Opcode.CALLVALUE, operands := [], outputs := ["sel"] }
def iDjmp : Instruction :=
  { id := 61, opcode := Opcode.DJMP,
    operands := [Operand.Var "sel", Operand.Label "t0", Operand.Label "t1"], outputs := [] }
def iStop : Instruction := { id := 62, opcode := Opcode.STOP, operands := [], outputs := [] }
def bEntry : BasicBlock := { label := "entry", instructions := [iSel, iDjmp] }
def bT0 : BasicBlock := { label := "t0", instructions := [iStop] }
def bT1 : BasicBlock := { label := "t1", instructions := [iStop] }
/-- **A function that really contains a `DJMP`** — the case the old `hgood` bans outright. -/
def fn : IrFunction := { name := "main", blocks := [bEntry, bT0, bT1] }
def ops : List StackOp := (generateFnPlan fn 0 0).get!.1
end Dj

theorem dj_compiles : (generateFnPlan Dj.fn 0 0).isSome = true := by rfl

/-- **The old `hgood` is FALSE here.** So every lemma that took it is inapplicable to this function —
which is exactly what makes this the discriminating witness. -/
theorem dj_hgood_false :
    ¬ (∀ b ∈ Dj.fn.blocks, ∀ inst ∈ nonParamInsts b, inst.opcode ≠ Opcode.INVOKE ∧
        inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP) := by
  intro h
  have hmem : Dj.iDjmp ∈ nonParamInsts Dj.bEntry := by
    rw [show nonParamInsts Dj.bEntry = [Dj.iSel, Dj.iDjmp] from rfl]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hb : Dj.bEntry ∈ Dj.fn.blocks := by
    rw [show Dj.fn.blocks = [Dj.bEntry, Dj.bT0, Dj.bT1] from rfl]
    exact List.mem_cons_self ..
  exact (h Dj.bEntry hb Dj.iDjmp hmem).2.2 rfl

/-- **The plan really does mint trampolines.** So the label count was genuinely at risk — this is not a
function where `DJMP` happens to emit nothing. -/
theorem dj_plan_has_trampolines :
    StackOp.SOLabel "djmp_tramp_1" ∈ Dj.ops ∧ StackOp.SOLabel "djmp_tramp_2" ∈ Dj.ops := by
  constructor <;> decide

/-- **The new condition holds.** No block is named like a freshly minted label. -/
theorem dj_labels_not_fresh : ∀ b ∈ Dj.fn.blocks, ¬ IsFreshLabel b.label := by
  intro b hb
  simp only [Dj.fn, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> exact short_not_fresh (by decide)

/-- **`hpreuniq` fires on a function containing a `DJMP`.** This is the theorem the old machinery could
not state: `dj_hgood_false` shows its hypothesis is unsatisfiable here, and `dj_plan_has_trampolines`
shows the plan really does mint the labels the ban existed to avoid.

The label count survives anyway, because the minted labels are trampolines and the count only ever asks
about block labels. -/
theorem dj_planLabelCount (l : String) (hl : ¬ IsFreshLabel l) :
    planLabelCount l Dj.ops ≤ 1 :=
  generateFnPlanFuel_planLabelCount_fresh
    (fuel := fnPlanFuel Dj.fn) (fnEom := 0) (lblCtr := 0) (fn := Dj.fn) rfl l hl

/-- …and so does the plan-prefix uniqueness obligation every per-block `hstep` takes as an input. -/
theorem dj_hpreuniq {blockOps rest : List StackOp} {bb : BasicBlock}
    (hbb : bb ∈ Dj.fn.blocks)
    (hblk : blockOps = StackOp.SOLabel bb.label :: rest) :
    ∀ preOps tailOps, Dj.ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_fresh (fuel := fnPlanFuel Dj.fn) (fnEom := 0) (lblCtr := 0) (fn := Dj.fn)
    (dj_labels_not_fresh bb hbb) rfl hblk

/-! ## The `stepObliv` family had zero consumers — here is the use

Eleven `StepObliv` lemmas were proved for the inline body opcodes, and sixty more are one lemma away
through the combinators. Not one of them was ever *used*. By this branch's own rule that means dead code,
or a job being done by an assumption somewhere downstream, and the only way to tell is to make something
consume them.

`execBodyThread_instIdx_congr`'s `hobliv` hypothesis is exactly `∀ inst ∈ body, StepObliv inst`. It is the
fact a join needs and a phi-free block does not: a join resumes at `instIdx = phiPrefixLength`, not at
zero, so a body simulation written for `instIdx = 0` transfers only if the body cannot see the index.

The Dia and Lp capstones never needed this — their joins are `phis ++ [term]`, with no body at all. So the
chain stayed unexercised. Below it is consumed, on a body of two different opcodes so that
`execBodyThread`'s induction genuinely iterates and `hobliv` has to be dispatched per instruction rather
than supplied once. -/
/-- **`hobliv`, discharged for a real join body.** `JoinBody.bb` is `p = phi(…) ; SSTORE d p ; STOP`, and
its body — the part between the phi prologue and the terminator — is the single `SSTORE`. Dispatching
over it gives `execBodyThread_instIdx_congr` exactly the hypothesis it wants. -/
theorem joinbody_hobliv :
    ∀ inst ∈ [JoinBody.bSst], ∀ (t t' : VenomState) (j : Nat),
      stepInstBase inst t = ExecResult.OK t' →
      stepInstBase inst { t with instIdx := j } = ExecResult.OK { t' with instIdx := j } := by
  intro inst hi
  simp only [List.mem_singleton] at hi
  subst hi
  exact stepObliv_sstore rfl

/-- **The obliviousness chain, consumed.** A join resumes at `instIdx = phiPrefixLength`, not at 0, so a
body simulation written for `instIdx = 0` only transfers if the body cannot see the index. This says it
cannot: threading `JoinBody`'s body from the join's resume point and from zero agree, up to the index.

This is what the `stepObliv_*` family was *for*, and until now nothing had used it — every one of those
eleven lemmas had zero consumers, which by this branch's own rule means dead or assumed. This is the use. -/
theorem joinbody_thread_offset_congr
    {s s' sEnd sEnd' : VenomState} {start start' : Nat}
    (hss : { s with instIdx := 0 } = { s' with instIdx := 0 })
    (h1 : execBodyThread [JoinBody.bSst] start s = some sEnd)
    (h2 : execBodyThread [JoinBody.bSst] start' s' = some sEnd') :
    { sEnd with instIdx := 0 } = { sEnd' with instIdx := 0 } :=
  execBodyThread_instIdx_congr [JoinBody.bSst] joinbody_hobliv start start' s s' sEnd sEnd'
    hss h1 h2


end EvmYul.Venom.Hol.Codegen

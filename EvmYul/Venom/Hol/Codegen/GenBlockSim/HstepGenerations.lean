import EvmYul.Venom.Hol.Codegen.GenBlockSim.HstepCanonical

/-!
# GenBlockSim -- HstepGenerations

The later hstep generations: chain-free reach, fuel-shaped loop-capable, and
clean-stack-prologue variants.
-/

open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/-- **Per-block REVERT `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_revert_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_revert_reach
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
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
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


/-- **Per-block JNZ-taken `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_jnz_taken_canonical`: layout from `reach_segment_gbp_fn` (plain
    `CfgReach` + the decidable `DfsClosed`/entry-visited facts) rather than `JmpChainTo`.

    The taken branch targets `ifNz`, which is the CFG's *second* successor (`bbSuccs` reverses the
    terminator's labels, so a JNZ's successors are `ifZ :: ifNz` — fall-through first). The DFS
    therefore records it from a widened allocator, and the scheduling residual is a four-part
    *relation* (stack/spilled/fnEom equal, nextOffset only `≤`), not an equation. It is taken as the
    input `hres2` here, exactly the shape `adapter_lgfold_rel_psOfFn_succ2_jnz_general` derives from a
    chain. `hpreuniq` is derived, not assumed. -/
theorem hstep_regularHSVP_jnz_taken_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
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
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres2 : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = (psOfFn fuel fn fnEom lblCtr ifNz).stack ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = (psOfFn fuel fn fnEom lblCtr ifNz).spilled ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom = (psOfFn fuel fn fnEom lblCtr ifNz).alloc.fnEom ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.nextOffset ≤ (psOfFn fuel fn fnEom lblCtr ifNz).alloc.nextOffset)
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
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
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
  -- the scheduling residual is supplied directly (`hres2`), not derived from a chain
  obtain ⟨hstk, hsp, hfe, hno⟩ := hres2
  exact hstep_regularHSVP_jnz_taken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hle hwdec


/-- **Per-block JNZ-not-taken `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_jnz_nottaken_canonical`: layout from `reach_segment_gbp_fn` (plain
    `CfgReach` + the decidable `DfsClosed`/entry-visited facts) rather than `JmpChainTo`.

    The not-taken branch targets `ifZ`, the CFG's *first* successor, so its residual is a plain
    plan-state equation (`hres`) like the JMP case — taken as an input here, exactly the shape
    `adapter_lgfold_eq_psOfFn_succ_jnz_general` derives from a chain. `hpreuniq` is derived. -/
theorem hstep_regularHSVP_jnz_nottaken_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
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
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr ifZ)
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
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
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
  -- the scheduling residual is supplied directly (`hres`), not derived from a chain
  exact hstep_regularHSVP_jnz_nottaken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec



/-- **Mid-layer JMP `hstep`, fuel-shaped.** Same block simulation as `hstep_regularHSVP_jmp` — the
    underlying `genBlockSimulation_regularHSVP_jmp` never mentioned a rank — but it hands off to
    `hstep_jmp_block_fuel`, so the block owes only the uniform bound `blockLen ≤ B` instead of a
    strict rank decrease. This is the whole difference between the two drivers at the block level. -/
theorem hstep_regularHSVP_jmp_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
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
    (hleB : bodyLen + 2 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Per-block JMP `hstep`: chain-free *and* loop-capable.** The composition of this session's two
    generalizations — the layout comes from `reach_segment_gbp_fn` (plain `CfgReach`, so a block behind
    a `JNZ` qualifies) and the budget discipline is the uniform `blockLen ≤ B` of the fuel-ranked driver
    (so a back-edge has nothing to violate). This is the hstep `codegen_correct_fuel_sched` consumes.

    Everything else is unchanged from `hstep_regularHSVP_jmp_reach`: the block simulation underneath
    never mentioned a rank, so dropping it costs nothing. -/
theorem hstep_regularHSVP_jmp_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
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
    (hleB : bodyLen + 2 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
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
  exact hstep_regularHSVP_jmp_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hleB


/-- **Every terminating block's `hstep` converts from the ranked driver to the fuel driver for free.**

    The ranked and fuel `hstep` matches differ *only* in the OK-continue arm (`blockLen ≤ N` + rank
    decrease vs. the uniform `blockLen ≤ B`). Their Halt / Abort-Revert / Abort-Fault arms are literally
    the same proposition — neither mentions the budget discipline.

    So for a block whose `runBlock` never yields a non-halted `OK` — every one of STOP, INVALID, RETURN,
    REVERT — the ranked hstep *is* the fuel hstep: `rw [hrb]` lands both in the same arm. All four
    halting terminators therefore get their loop-capable `hstep` from the existing
    `hstep_regularHSVP_*_reach` theorems with no new proof, at any `wOf` the caller likes (the arm that
    mentions it is unreachable). Only JMP and JNZ need genuinely new work, which is
    `hstep_regularHSVP_jmp_reach_fuel` and its JNZ siblings. -/
theorem hstep_fuel_of_sched_terminal {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {s : VenomState} {as0 : AsmState} {B N f' : Nat}
    (hterm : ∀ s', runBlock f' ctx bb s ≠ ExecResult.OK s')
    (h :
      WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
        (runBlock f' ctx bb s)) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock f' ctx bb s) := by
  cases hrb : runBlock f' ctx bb s with
  | OK s' => exact absurd hrb (hterm s')
  | Halt s' => rw [hrb] at h; exact h
  | Abort a s' => rw [hrb] at h; cases a <;> exact h
  | IntRet _ _ => trivial
  | Error _ => trivial



/-- **Mid-layer JNZ-taken `hstep`, fuel-shaped.** As `hstep_regularHSVP_jnz_taken`, but handing off to
    `hstep_jmp_block_fuel`: the block owes the uniform `blockLen ≤ B` rather than a rank decrease, so a
    taken branch may target a block laid out *before* it — i.e. a loop back-edge. -/
theorem hstep_regularHSVP_jnz_taken_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
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
    (hleB : bodyLen + 3 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Mid-layer JNZ-not-taken `hstep`, fuel-shaped.** The fall-through counterpart of
    `hstep_regularHSVP_jnz_taken_fuel`; same swap of the rank decrease for the uniform bound. -/
theorem hstep_regularHSVP_jnz_nottaken_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
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
    (hleB : bodyLen + 5 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Per-block JNZ-taken `hstep`: chain-free *and* loop-capable.** Both generalizations composed —
    layout from `CfgReach` (so this fires behind a JNZ), budget from the fuel rank (so the taken branch
    may jump *backwards*, which is exactly a loop back-edge). -/
theorem hstep_regularHSVP_jnz_taken_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
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
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres2 : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = (psOfFn fuel fn fnEom lblCtr ifNz).stack ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = (psOfFn fuel fn fnEom lblCtr ifNz).spilled ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom = (psOfFn fuel fn fnEom lblCtr ifNz).alloc.fnEom ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.nextOffset ≤ (psOfFn fuel fn fnEom lblCtr ifNz).alloc.nextOffset)
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
    (hnr : ¬ CfgReach (cfgAnalyze fn) ifZ ifNz)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
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
  obtain ⟨hstk, hsp, hfe, hno⟩ := hres2
  exact hstep_regularHSVP_jnz_taken_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hleB


/-- **Per-block JNZ-not-taken `hstep`: chain-free *and* loop-capable.** The fall-through counterpart;
    same composition. -/
theorem hstep_regularHSVP_jnz_nottaken_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
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
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr ifZ)
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
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idxZ = pcOf bb'.label)
    (hleB : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
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
  exact hstep_regularHSVP_jnz_nottaken_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hleB


/-- **Mid-layer JMP `hstep` through a clean-stack prologue, fuel-shaped** — the composition of *all
    three* of this session's generalizations at the block level:

      * the block may carry a non-empty clean-stack prologue (`toPop ≠ []`, a join that drops values),
        via `genBlockSimulation_regularHSVP_jmp_clean`;
      * it owes only the uniform bound `blockLen ≤ B`, so it may branch *backwards* — a loop back-edge;
      * (with `reach_segment_gbp_fn` supplying its layout) it may sit anywhere CFG-reachable, including
        behind a `JNZ`.

    The pc arithmetic the prologue forces is absorbed entirely into `bodyLen`, which is *defined* as the
    length of the prologue-and-body asm — so the terminator still lands at `as0.pc + bodyLen` and no
    jump-target lemma changes. The residual (`hstk`/`hsp`/`hfe`/`hno`) is now about the fold from the
    post-pop state `ps2`, which is where the body actually starts. -/
theorem hstep_regularHSVP_jmp_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled
      = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom
      = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset
      ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 2 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront
      hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock hbodyLenEq hpc1 hpush hoff_lk
      hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'



/-- Per-block STOP `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_stop`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_stop_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
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
    hasm_regularHSVP_stop_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop
      hshallow hlenPop hblock hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block INVALID `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_invalid`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_invalid_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
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
    hasm_regularHSVP_invalid_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop
      hshallow hlenPop hblock hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block RETURN `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_return`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_return_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
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
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    hasm_regularHSVP_return_var_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread
      hpop hshallowPS hlenPop
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block REVERT `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_revert`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_revert_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
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
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    hasm_regularHSVP_revert_var_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread
      hpop hshallowPS hlenPop
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block JNZ-taken `hstep` through a clean-stack prologue, fuel-shaped — the full composition:
    dropping join + loop-capable budget. -/
theorem hstep_regularHSVP_jnz_taken_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = base ++ [Operand.Var c])
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
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 3 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd2 hsv2
      hspM2 hrel0 hthread hpop hshallow hlenPop hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- Per-block JNZ-not-taken `hstep` through a clean-stack prologue, fuel-shaped. -/
theorem hstep_regularHSVP_jnz_nottaken_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = base ++ [Operand.Var c])
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
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idxZ = pcOf bb'.label)
    (hleB : bodyLen + 5 ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd2 hsv2
      hspM2 hrel0 hthread hpop hshallow hlenPop hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


set_option maxHeartbeats 1000000 in
/-- **Per-block DJMP `hstep`, fuel-shaped.** The seventh-and-last terminator. `hstep_jmp_block_fuel` is
    terminator-agnostic — it only wants "the Venom block stepped to a non-halting `OK` and the asm ran to
    the successor's entry, still related" — and `genBlockSimulation_regularHSVP_djmp` supplies exactly
    that. The plan side ends at the body's output with the selector popped, so the scheduling residual
    (`hstk`/`hsp`/`hfe`/`hno`) is stated against `stackPop 1` of the fold output.

    Loop-capable by construction: the obligation is the uniform `blockLen ≤ B`, so a DJMP may select a
    block laid out *before* it. That is sound precisely because DJMP cannot leave the static CFG
    (`stepInstBase_term_currentBb_mem_succs`), so the walk's reachability invariant survives it. -/
theorem hstep_regularHSVP_djmp_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
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
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target)
    -- the walk's successor + the scheduling residual (the plan side popped the selector)
    (hlk' : lookupBlock (jumpTo tgtLbl sEnd).currentBb fn.blocks = some bb')
    (hstk : stackPop 1 (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : target = pcOf bb'.label)
    (hleB : bodyLen + (5 * pre.length + 5 + 4) ≤ B) :
    WalkStepFuel fn pcOf psOf lo offsetToPc prog as0 N B
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel⟩ :=
    genBlockSimulation_regularHSVP_djmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hselval pre hpre hmatch hsel hidx_lk
      ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


end EvmYul.Venom.Hol.Codegen

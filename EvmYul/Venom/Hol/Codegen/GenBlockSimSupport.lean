import EvmYul.Venom.Hol.Codegen.CodegenPipeline
import EvmYul.Venom.Hol.Exec

/-!
# Block-plan structural support (towards `genBlockSimulation`)

Sorry-free structural lemmas that the block simulation proof composes on top of —
ported from `vyper-hol/venom/codegen/proofs/genBlockSimScript.sml` (the
`non_param_insts_all_neq` / `get_params_nil` / `prepare_params_plan_nil` /
`gen_block_plan_decompose` layer). These are pure unfolding/induction facts about the
*generator*; they carry no simulation content, so they stand independently of the
(still-admitted) `genBlockSimulation` capstone.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- When a block has no PARAM instructions, `nonParamInsts` is the identity. -/
theorem nonParamInsts_all_neq (bb : BasicBlock)
    (h : ∀ inst ∈ bb.instructions, inst.opcode ≠ Opcode.PARAM) :
    nonParamInsts bb = bb.instructions := by
  unfold nonParamInsts
  apply List.filter_eq_self.mpr
  intro inst hinst
  rw [bne_iff_ne]
  exact h inst hinst

/-- When the leading instruction is not PARAM, `getParams` is empty. -/
theorem getParams_nil_hd (inst : Instruction) (rest : List Instruction)
    (h : inst.opcode ≠ Opcode.PARAM) : getParams (inst :: rest) = [] := by
  unfold getParams
  rw [if_neg h]

/-- When no instruction is PARAM, `getParams` is empty. -/
theorem getParams_nil : ∀ (insts : List Instruction), insts ≠ [] →
    (∀ inst ∈ insts, inst.opcode ≠ Opcode.PARAM) → getParams insts = []
  | [], h, _ => absurd rfl h
  | inst :: _, _, h => getParams_nil_hd inst _ (h inst List.mem_cons_self)

/-- `prepare_params_plan` is a no-op when the entry block has no params. -/
theorem prepareParamsPlan_nil (liveness : DfState (List String)) (fn : IrFunction) (ps : PlanState)
    (h : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = []) :
    prepareParamsPlan liveness fn ps = ([], ps) := by
  unfold prepareParamsPlan
  split
  · rfl
  · rename_i entry tail heq
    have hp : getParams entry.instructions = [] := h entry (by rw [heq]; rfl)
    rw [hp]
    rfl

/-- Structural decomposition of `generate_block_plan` for a non-empty, PARAM-free
    block (port of `gen_block_plan_decompose`): the plan is exactly
    `[SOLabel] ++ cleanOps ++ instOps`, where `cleanOps` is the (possibly empty)
    clean-stack prefix and `instOps` is the per-instruction fold. `hentry` discharges
    the entry-params branch (a PARAM-free block that *is* the entry has no params). -/
theorem generateBlockPlan_decompose
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 instOps,
      ((cfg.predsOf bb.label).length = 1 ∧ cleanStackPlan liveness cfg fn bb ps = (cleanOps, ps2) ∨
       (cfg.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
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
        (some ([], ps2))) = some (instOps, ps') ∧
      blockOps = StackOp.SOLabel bb.label :: cleanOps ++ instOps := by
  unfold generateBlockPlan at hplan
  rw [prepareParamsPlan_nil liveness fn ps hentry, ite_self] at hplan
  dsimp only at hplan
  -- Name the clean-stack result; then case on the per-instruction fold.
  set cl := if (cfg.predsOf bb.label).length = 1 then cleanStackPlan liveness cfg fn bb ps
            else ([], ps) with hcl
  split at hplan
  · -- fold = none: contradicts `= some (blockOps, ps')`
    simp at hplan
  · rename_i instOps ps3 hf
    -- hf : <fold> = some (instOps, ps3);  hplan : some (…, ps3) = some (blockOps, ps')
    simp only [Option.some.injEq, Prod.mk.injEq] at hplan
    obtain ⟨hblk, hps⟩ := hplan
    subst hps
    refine ⟨cl.1, cl.2, instOps, ?_, ?_, ?_⟩
    · by_cases hc : (cfg.predsOf bb.label).length = 1
      · exact Or.inl ⟨hc, by rw [hcl, if_pos hc]⟩
      · exact Or.inr ⟨hc, by rw [hcl, if_neg hc], by rw [hcl, if_neg hc]⟩
    · -- conclusion fold = hf up to the closure's defeq (`let (inst,i)` vs `instI.1/.2`)
      exact hf
    · rw [← hblk]; simp

/-- The per-instruction Option-threading fold body inside `generateBlockPlan` /
    `generateBlockPlan_decompose`, named so `generateBlockPlan_split_term` can refer to it. -/
def instFoldF (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) :
    Option (List StackOp × PlanState) → Instruction × Nat → Option (List StackOp × PlanState) :=
  fun acc instI =>
    match acc with
    | none => none
    | some (ops, psc) =>
      let (inst, i) := instI
      let nextLive :=
        if i + 1 < (nonParamInsts bb).length then
          liveVarsAt L bb.label (i + (getParams bb.instructions).length + 1)
        else liveVarsAt L bb.label bb.instructions.length
      let nextIsTerm :=
        if i + 1 < (nonParamInsts bb).length then
          isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
      match generateInstPlan L D C fn inst nextLive (bbIsHalting bb) nextIsTerm bb.label psc with
      | none => none
      | some (stepOps, psn) => some (ops ++ stepOps, psn)

/-- **The block's clean-stack plan is trivially empty.** `cleanStackPlan` only does work at a *branch
    join*: a block with exactly one predecessor whose predecessor **branches** (≥2 successors). So it is
    `([], ps)` whenever either
      * the block is not a single-predecessor block (entry, or a real join with ≥2 preds), or
      * its single predecessor doesn't branch (a JMP pred — its exit layout already IS this block's entry).

    The second case is what makes the per-block machinery apply to the *intermediate blocks of a JMP
    chain*, which have exactly one predecessor and were previously excluded by the over-strong
    `(predsOf bb.label).length ≠ 1`. -/
def CleanTrivial (L : DfState (List String)) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) : Prop :=
  ∀ ps : PlanState, cleanStackPlan L C fn bb ps = ([], ps)

/-- Not a single-pred block (entry, or a real join with ≥2 preds) ⇒ nothing to clean. -/
theorem cleanTrivial_of_multi {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} (h : (C.predsOf bb.label).length ≠ 1) : CleanTrivial L C fn bb := by
  intro ps
  unfold cleanStackPlan
  split
  · rename_i p heq; rw [heq] at h; simp at h
  · rfl

/-- **A single, non-branching predecessor (a JMP pred)** ⇒ nothing to clean: the predecessor's exit
    layout already IS this block's entry. This is every intermediate block of a JMP chain. -/
theorem cleanTrivial_of_jmp_pred {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {p : String}
    (hp : C.predsOf bb.label = [p]) (hs : (C.succsOf p).length ≤ 1) : CleanTrivial L C fn bb := by
  intro ps
  unfold cleanStackPlan
  rw [hp]
  exact if_pos hs

/-- The single predecessor isn't a block of `fn` ⇒ nothing to clean. -/
theorem cleanTrivial_of_pred_missing {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {p : String}
    (hp : C.predsOf bb.label = [p]) (hf : fn.blocks.find? (·.label == p) = none) :
    CleanTrivial L C fn bb := by
  intro ps
  unfold cleanStackPlan
  rw [hp]
  simp only []
  by_cases hs : (C.succsOf p).length ≤ 1
  · rw [if_pos hs]
  · rw [if_neg hs, hf]

/-- **Nothing dead at the join** ⇒ nothing to clean, EVEN at a branch target. `cleanStackPlan` pops the
    values the branching predecessor's exit layout carries but this block doesn't want; when that set is
    empty (`popmanyPlan [] = ([], ps)`) the plan is the identity. Crucially `toPop` depends only on the
    liveness/CFG — not on the plan state — so this is a static condition.

    This is what lets a JNZ's *branch target* (single pred, and that pred branches) be covered without
    threading a clean-stack prefix through the block layout. -/
theorem cleanTrivial_of_no_dead {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {p : String} {predBb : BasicBlock}
    (hp : C.predsOf bb.label = [p])
    (hf : fn.blocks.find? (·.label == p) = some predBb)
    (hdead : (liveVarsAt L p predBb.instructions.length).filter
        (fun v => ¬ (inputVarsFrom p bb.instructions (liveVarsAt L bb.label 0)).contains v) = []) :
    CleanTrivial L C fn bb := by
  intro ps
  unfold cleanStackPlan
  rw [hp]
  simp only []
  by_cases hs : (C.succsOf p).length ≤ 1
  · rw [if_pos hs]
  · rw [if_neg hs, hf]
    simp only []
    rw [hdead]
    simp [popmanyPlan]

/-- The condition `generateBlockPlan_split_term` actually needs. -/
theorem cleanStackPlan_nil_of_cleanTrivial (L : DfState (List String)) (C : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) (h : CleanTrivial L C fn bb) :
    cleanStackPlan L C fn bb ps = ([], ps) := h ps

/-- **`generateBlockPlan` terminator-split** (multi-pred, phi/param-free block whose
    `nonParamInsts` is `front ++ [term]`): the per-instruction fold factors as a body-fold over
    `front` (`instFoldF`) followed by the single terminator step
    `generateInstPlan term (liveVarsAt … instructions.length) … false`, and the block's output plan
    state `ps'` is exactly that terminator step applied to the body-fold output `ps_body`.

    This is the structural spine of the plan-representation bridge: with `psOfFn_entry_succ` /
    `psOfFn_chain` (which give `psOf successor = ps'`, the predecessor's full-block output), the
    per-block `hstep` residual `body-fold = psOf successor` is pinned precisely to the terminator's
    plan effect — for a JMP, the join-reorder (`reorderPlan targetStack`) plus `releaseDeadSpills`. -/
theorem generateBlockPlan_split_term
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ bodyOps ps_body termOps,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) = some (bodyOps, ps_body) ∧
      generateInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
        (bbIsHalting bb) false bb.label ps_body = some (termOps, ps') ∧
      blockOps = StackOp.SOLabel bb.label :: bodyOps ++ termOps := by
  obtain ⟨cleanOps, ps2, instOps, hclean, hfold, hblk⟩ :=
    generateBlockPlan_decompose L D C fn bb ps blockOps ps' hentry hplan
  have hcn := cleanStackPlan_nil_of_cleanTrivial L C fn bb ps hmulti
  have hc : cleanOps = [] ∧ ps2 = ps := by
    rcases hclean with ⟨_, hcs⟩ | ⟨_, hce, hps2⟩
    · rw [hcn] at hcs; simp only [Prod.mk.injEq] at hcs; exact ⟨hcs.1.symm, hcs.2.symm⟩
    · exact ⟨hce, hps2⟩
  obtain ⟨hce, hps2⟩ := hc
  subst hce
  rw [hps2] at hfold
  have hzi : (nonParamInsts bb).zipIdx 0 = front.zipIdx 0 ++ [(term, front.length)] := by
    rw [hnp, List.zipIdx_append]; simp
  have hlen : (nonParamInsts bb).length = front.length + 1 := by rw [hnp]; simp
  rw [hzi, List.foldl_append] at hfold
  simp only [List.foldl_cons, List.foldl_nil] at hfold
  change instFoldF L D C fn bb
    ((front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps))) (term, front.length)
      = some (instOps, ps') at hfold
  have hlt : ¬ front.length + 1 < (nonParamInsts bb).length := by omega
  rcases hbr : (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps)) with _ | ⟨bodyOps, ps_body⟩
  · rw [hbr] at hfold; simp [instFoldF] at hfold
  · rw [hbr] at hfold
    simp only [instFoldF] at hfold
    rw [if_neg hlt, if_neg hlt] at hfold
    rcases hts : generateInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
        (bbIsHalting bb) false bb.label ps_body with _ | ⟨termOps, psT⟩
    · rw [hts] at hfold; simp at hfold
    · rw [hts] at hfold
      simp only [Option.some.injEq, Prod.mk.injEq] at hfold
      obtain ⟨hops, hpsT⟩ := hfold
      exact ⟨bodyOps, ps_body, termOps, rfl, by rw [hts, hpsT], by rw [hblk, ← hops]; simp⟩

/-- **`generateBlockPlan_split_term` without `CleanTrivial` — the clean-stack prefix is kept.**

    `generateBlockPlan_split_term` assumes `CleanTrivial`, i.e. that the block's clean-stack prologue
    is empty, and so pins the body fold to start at the block's *entry* state `ps` and the body's asm
    to start right after the label. That is false at a join that genuinely drops values: a block with
    exactly one predecessor which itself has several successors (a JNZ target) pops every variable that
    was live at the predecessor's exit but is not an input here (`cleanStackPlan` → `popmanyPlan`).

    This version keeps that prefix. The body fold starts at `ps2` — the state *after* the pops — and the
    block's ops are `SOLabel :: cleanOps ++ bodyOps ++ termOps`. Every downstream layout lemma's pc
    arithmetic has to shift by `(executePlan cleanOps).length` accordingly; the semantic side is already
    available (`popmanyPlan_sim`, which leaves the Venom state untouched — popping dead variables is
    invisible to Venom). Specialising `cleanOps = []`/`ps2 = ps` recovers the old statement. -/
theorem generateBlockPlan_split_term_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 bodyOps ps_body termOps,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      generateInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
        (bbIsHalting bb) false bb.label ps_body = some (termOps, ps') ∧
      blockOps = StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++ termOps := by
  obtain ⟨cleanOps, ps2, instOps, hclean, hfold, hblk⟩ :=
    generateBlockPlan_decompose L D C fn bb ps blockOps ps' hentry hplan
  have hzi : (nonParamInsts bb).zipIdx 0 = front.zipIdx 0 ++ [(term, front.length)] := by
    rw [hnp, List.zipIdx_append]; simp
  have hlen : (nonParamInsts bb).length = front.length + 1 := by rw [hnp]; simp
  rw [hzi, List.foldl_append] at hfold
  simp only [List.foldl_cons, List.foldl_nil] at hfold
  change instFoldF L D C fn bb
    ((front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2))) (term, front.length)
      = some (instOps, ps') at hfold
  have hlt : ¬ front.length + 1 < (nonParamInsts bb).length := by omega
  rcases hbr : (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) with _ | ⟨bodyOps, ps_body⟩
  · rw [hbr] at hfold; simp [instFoldF] at hfold
  · rw [hbr] at hfold
    simp only [instFoldF] at hfold
    rw [if_neg hlt, if_neg hlt] at hfold
    rcases hts : generateInstPlan L D C fn term (liveVarsAt L bb.label bb.instructions.length)
        (bbIsHalting bb) false bb.label ps_body with _ | ⟨termOps, psT⟩
    · rw [hts] at hfold; simp at hfold
    · rw [hts] at hfold
      simp only [Option.some.injEq, Prod.mk.injEq] at hfold
      obtain ⟨hops, hpsT⟩ := hfold
      exact ⟨cleanOps, ps2, bodyOps, ps_body, termOps, hclean, hbr, by rw [hts, hpsT],
        by rw [hblk, ← hops]; simp⟩

/-! ## Venom-side `runBlock` decomposition (phi-free blocks)

The execution-side counterpart to `generateBlockPlan_decompose`: for a block whose first
instruction is not a PHI, the phi prefix is empty, so `evalPhis` is a no-op and `runBlock`
reduces to `execBlock` from `instIdx := 0`. This is the shape `genBlockSimulation` pairs with
the generator's `[SOLabel] ++ cleanOps ++ instOps`. -/

/-- `evalPhis` is a no-op when the block's first instruction is not a PHI (phis are a prefix,
    so a non-PHI head means no phis to evaluate). -/
theorem evalPhis_ok_of_hd_ne_phi (s : VenomState) (inst : Instruction) (rest : List Instruction)
    (h : inst.opcode ≠ Opcode.PHI) : evalPhis s (inst :: rest) = ExecResult.OK s := by
  unfold evalPhis; rw [if_pos h]

/-- A non-PHI head means an empty phi prefix. -/
theorem phiPrefixLength_zero_of_hd_ne_phi (inst : Instruction) (rest : List Instruction)
    (h : inst.opcode ≠ Opcode.PHI) : phiPrefixLength (inst :: rest) = 0 := by
  unfold phiPrefixLength; rw [if_neg h]

/-- **Venom-side decomposition of `runBlock` for a phi-free block** (mirrors
    `generateBlockPlan_decompose`): when the first instruction is not a PHI, the phi prefix is
    empty and `runBlock` is just `execBlock` from `instIdx := 0`. -/
theorem runBlock_no_phi (fuel : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState)
    (inst : Instruction) (rest : List Instruction)
    (hbb : bb.instructions = inst :: rest) (hphi : inst.opcode ≠ Opcode.PHI) :
    runBlock fuel ctx bb s = execBlock fuel ctx bb { s with instIdx := 0 } := by
  unfold runBlock
  rw [hbb, evalPhis_ok_of_hd_ne_phi s inst rest hphi,
      phiPrefixLength_zero_of_hd_ne_phi inst rest hphi]

/-- `getInstruction` is list indexing: `getInstruction bb i = bb.instructions[i]?`. Bridges
    `execBlock`'s `instIdx` lookups to the generator's positional `zipIdx` fold. -/
theorem getInstruction_eq (bb : BasicBlock) (i : Nat) :
    getInstruction bb i = bb.instructions[i]? := by
  unfold getInstruction
  split
  · rename_i h; rw [List.getElem?_eq_getElem h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by omega)]

/-! ## `execBlock` single-step lemmas

The unfoldings the block-simulation fold induction iterates over: one `execBlock` step on a
non-terminator advances `instIdx`; on a terminator it returns `OK`/`Halt` per `halted`. -/

/-- One `execBlock` step on a non-terminator: step the instruction, advance `instIdx`. -/
theorem execBlock_step_nonterm (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.OK s')
    (hterm : isTerminator inst.opcode = false) :
    execBlock (fuel' + 1) ctx bb s = execBlock fuel' ctx bb { s' with instIdx := s.instIdx + 1 } := by
  simp only [execBlock, hget, hstep, hterm, Bool.false_eq_true, if_false]

/-- One `execBlock` step on a terminator that does not halt: returns `OK s'`. -/
theorem execBlock_step_term_ok (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.OK s')
    (hterm : isTerminator inst.opcode = true)
    (hhalt : s'.halted = false) :
    execBlock (fuel' + 1) ctx bb s = ExecResult.OK s' := by
  simp only [execBlock, hget, hstep, hterm, if_true, hhalt, Bool.false_eq_true, if_false]

/-- One `execBlock` step on a terminator that halts: returns `Halt s'`. -/
theorem execBlock_step_term_halt (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.OK s')
    (hterm : isTerminator inst.opcode = true)
    (hhalt : s'.halted = true) :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Halt s' := by
  simp only [execBlock, hget, hstep, hterm, if_true, hhalt]

/-! ## Venom-side `runBlocks` (CFG walk) decomposition

The structural unfoldings the *function*-level simulation (`genFnSimulation`) composes over: one
iteration of `runBlocks` looks up the current block, runs it, and on `OK` either halts (if the
block set `halted`) or recurses into the next block; non-`OK` block results pass straight through.
These mirror the per-block `runBlock` step but at the inter-block (CFG) level, and carry no
simulation content — they are pure `runBlocks` unfoldings. -/

/-- One `runBlocks` iteration on a block that returns `OK s'` *without* halting: recurse into the
    next block (`s'.currentBb`, set by the terminator) with one less fuel. -/
theorem runBlocks_unfold_ok (fuel' : Nat) (ctx : VenomContext) (fn : IrFunction)
    (s s' : VenomState) (bb : BasicBlock)
    (hlook : lookupBlock s.currentBb fn.blocks = some bb)
    (hrun : runBlock fuel' ctx bb s = ExecResult.OK s')
    (hhalt : s'.halted = false) :
    runBlocks (fuel' + 1) ctx fn s = runBlocks fuel' ctx fn s' := by
  simp only [runBlocks, hlook, hrun, hhalt, Bool.false_eq_true, if_false]

/-- One `runBlocks` iteration on a block that returns `OK s'` and *halts*: stop with `Halt s'`. -/
theorem runBlocks_unfold_halt (fuel' : Nat) (ctx : VenomContext) (fn : IrFunction)
    (s s' : VenomState) (bb : BasicBlock)
    (hlook : lookupBlock s.currentBb fn.blocks = some bb)
    (hrun : runBlock fuel' ctx bb s = ExecResult.OK s')
    (hhalt : s'.halted = true) :
    runBlocks (fuel' + 1) ctx fn s = ExecResult.Halt s' := by
  simp only [runBlocks, hlook, hrun, hhalt, if_true]

/-- One `runBlocks` iteration on a block that returns `IntRet`: propagate the internal return. -/
theorem runBlocks_unfold_intret (fuel' : Nat) (ctx : VenomContext) (fn : IrFunction)
    (s s' : VenomState) (bb : BasicBlock) (vals : List bytes32)
    (hlook : lookupBlock s.currentBb fn.blocks = some bb)
    (hrun : runBlock fuel' ctx bb s = ExecResult.IntRet vals s') :
    runBlocks (fuel' + 1) ctx fn s = ExecResult.IntRet vals s' := by
  simp only [runBlocks, hlook, hrun]

/-- One `runBlocks` iteration on a block that `Halt`s, `Abort`s, or `Error`s: pass the result
    through unchanged (the `OK`/`IntRet` cases are handled by the lemmas above). -/
theorem runBlocks_unfold_term (fuel' : Nat) (ctx : VenomContext) (fn : IrFunction)
    (s : VenomState) (bb : BasicBlock) (r : ExecResult)
    (hlook : lookupBlock s.currentBb fn.blocks = some bb)
    (hrun : runBlock fuel' ctx bb s = r)
    (hnotok : ∀ s', r ≠ ExecResult.OK s')
    (hnotret : ∀ vals s', r ≠ ExecResult.IntRet vals s') :
    runBlocks (fuel' + 1) ctx fn s = r := by
  cases r with
  | OK s' => exact absurd rfl (hnotok s')
  | IntRet vals s' => exact absurd rfl (hnotret vals s')
  | Halt s' => simp only [runBlocks, hlook, hrun]
  | Abort t s' => simp only [runBlocks, hlook, hrun]
  | Error e => simp only [runBlocks, hlook, hrun]

/-! ## `asmResolve` characterization (label-resolution layer)

Towards lifting `genBlockSimulation` to the *resolved* program: `resolveInst` only rewrites
label/offset pushes, so it is the identity on the entire (label-push-free) instruction body —
hence every body sim over the unresolved `executePlan` transfers verbatim to the resolved
program, and only the control-flow terminator's push needs new reasoning. -/

theorem resolveInst_AsmOp (offsets) (n : String) :
    resolveInst offsets (AsmInst.AsmOp n) = AsmInst.AsmOp n := rfl

theorem resolveInst_AsmPush (offsets) (b : List byte) :
    resolveInst offsets (AsmInst.AsmPush b) = AsmInst.AsmPush b := rfl

theorem resolveInst_AsmLabel (offsets) (l : String) :
    resolveInst offsets (AsmInst.AsmLabel l) = AsmInst.AsmLabel l := rfl

/-- A label push resolves to a concrete value push of the label's byte offset. -/
theorem resolveInst_AsmPushLabel {offsets} {lbl : String} {off : Nat}
    (h : AssocList.lookup String Nat offsets lbl = some off) :
    resolveInst offsets (AsmInst.AsmPushLabel lbl)
      = AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes off)) := by
  simp [resolveInst, h]

/-- `resolveInst` is the identity on any instruction that is not a label/offset push. -/
theorem resolveInst_self_of_ne (offsets) (a : AsmInst)
    (h1 : ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (h2 : ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    resolveInst offsets a = a := by
  cases a <;> simp_all [resolveInst]

/-- For a label-push-free program, resolution is the identity — so every body sim over the
    unresolved `executePlan` transfers verbatim to the resolved program. -/
theorem map_resolveInst_eq_self (offsets) (L : List AsmInst)
    (h1 : ∀ a ∈ L, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (h2 : ∀ a ∈ L, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    L.map (resolveInst offsets) = L := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons,
        resolveInst_self_of_ne offsets a (h1 a List.mem_cons_self) (h2 a List.mem_cons_self),
        ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
           (fun x hx => h2 x (List.mem_cons_of_mem _ hx))]

end EvmYul.Venom.Hol.Codegen

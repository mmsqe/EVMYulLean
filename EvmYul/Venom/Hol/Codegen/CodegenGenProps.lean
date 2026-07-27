import EvmYul.Venom.Hol.Codegen.CodegenPipeline

/-!
# Generator totality (stage 4b)

Towards de-vacuifying `codegen_correct`: its premise `codegen ctx = some bytecode` is
only meaningful if the generator actually *succeeds* on codegen-ready input. The
generator returns `none` only when it meets a pre-codegen opcode (`ALLOCA` / `SINK` /
`DLOAD` / `DLOADBYTES`), which `codegenReady` forbids.

This file proves the whole totality chain — `inst → block → fn → context → bytes`:
the generator (and the full `codegenFuel` pipeline) succeeds on every codegen-ready
context. That is the concrete non-vacuity `codegen_correct` needs, plus the
`codegenFuel_eq_assemble` bridge tying the output bytes to the generated plan.

(The *correctness* of the produced plan — that its execution simulates the Venom
semantics, composing PlanSim's sims — is the separate, harder remainder of stage 4b.)
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `generate_inst_plan` succeeds (`some`) on any codegen-ready instruction: every
    dispatch branch except the pre-codegen one returns `some`. -/
theorem generateInstPlan_isSome
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (inst : Instruction) (nextLive : List String) (isHalting nextIsTerm : Bool)
    (curBb : String) (ps : PlanState) (h : codegenReadyInst inst) :
    (generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps).isSome := by
  unfold codegenReadyInst at h
  unfold generateInstPlan
  rw [if_neg h]
  repeat' split
  all_goals rfl

/-! ## Block level

Lifting the base case through `generate_block_plan`. A block's plan folds
`generate_inst_plan` over its non-PARAM instructions; the fold stays `some` as long
as every step does, and the final repackaging match preserves that. -/

/-- The per-instruction fold inside `generate_block_plan` stays `some` when every
    folded instruction is codegen-ready (`generate_inst_plan` never returns `none`).
    Stated over an arbitrary suffix `l` and initial accumulator `init` so it proves
    by structural induction on `l`. -/
theorem genBlockFold_isSome
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (insts : List Instruction) (nParams : Nat) (isHalting : Bool)
    (l : List (Instruction × Nat)) :
    ∀ (init : List StackOp × PlanState), (∀ x ∈ l, codegenReadyInst x.1) →
    (l.foldl
      (fun (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat) =>
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
          | some (stepOps, ps') => some (ops ++ stepOps, ps'))
      (some init)).isSome := by
  induction l with
  | nil => intro init _; rfl
  | cons hd tl ih =>
    intro init hl
    rw [List.foldl_cons]
    obtain ⟨inst, i⟩ := hd
    obtain ⟨ops, ps⟩ := init
    have hready : codegenReadyInst inst := hl (inst, i) List.mem_cons_self
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
      (generateInstPlan_isSome liveness dfg cfg fn inst
        (if i + 1 < insts.length then liveVarsAt liveness bb.label (i + nParams + 1)
         else liveVarsAt liveness bb.label bb.instructions.length)
        isHalting
        (if i + 1 < insts.length then isTerminator insts[i + 1]!.opcode else false)
        bb.label ps hready)
    obtain ⟨stepOps, ps'⟩ := r
    simp only [hr]
    exact ih (ops ++ stepOps, ps') (fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-- The final repackaging match in `generate_block_plan` preserves `isSome`. -/
theorem blockPlan_repack_isSome
    (o : Option (List StackOp × PlanState))
    (f : List StackOp → PlanState → List StackOp × PlanState) (h : o.isSome) :
    (match o with | none => none | some (a, b) => some (f a b)).isSome := by
  rcases o with _ | ⟨a, b⟩
  · simp at h
  · rfl

/-- `generate_block_plan` succeeds on a block whose instructions are all
    codegen-ready: the per-instruction fold stays `some` and the final repackaging
    match preserves that. -/
theorem generateBlockPlan_isSome
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState)
    (hbb : ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    (generateBlockPlan liveness dfg cfg fn bb ps).isSome := by
  have hmem : ∀ x ∈ (nonParamInsts bb).zipIdx, codegenReadyInst x.1 :=
    fun x hx => hbb x.1 (List.mem_of_mem_filter (List.fst_mem_of_mem_zipIdx hx))
  unfold generateBlockPlan
  exact blockPlan_repack_isSome _ _
    (genBlockFold_isSome liveness dfg cfg fn bb (nonParamInsts bb)
      ((getParams bb.instructions).length) (bbIsHalting bb) (nonParamInsts bb).zipIdx _ hmem)

/-! ## Function level

Lifting through the per-function CFG DFS (`generate_fn_plan_aux` / `generate_succs_plan`,
mutual fuel recursion). The DFS returns `none` only when some block's plan does; since
every block of a ready function is ready, both halves preserve `some`. -/

set_option maxHeartbeats 1000000 in
/-- The per-function CFG DFS never returns `none` on a codegen-ready function: both
    `generate_fn_plan_aux` (the worklist walk) and `generate_succs_plan` (the per-edge
    branch) preserve `some`. Proved by a single induction on `fuel`, carrying both
    halves so each can use the other's IH at the predecessor fuel. -/
theorem generateFnPlanAux_generateSuccsPlan_isSome
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (fuel : Nat),
      (∀ worklist visited ps,
        (generateFnPlanAux fuel liveness dfg cfg fn worklist visited ps).isSome) ∧
      (∀ savedStack savedSpilled succs visited ps,
        (generateSuccsPlan fuel liveness dfg cfg fn savedStack savedSpilled succs visited ps).isSome) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited ps => ?_, fun ss sp succs visited ps => ?_⟩
    · simp only [generateFnPlanAux, Option.isSome_some]
    · simp only [generateSuccsPlan, Option.isSome_some]
  | succ fuel ih =>
    obtain ⟨ihAux, ihSuccs⟩ := ih
    refine ⟨fun worklist visited ps => ?_, fun ss sp succs visited ps => ?_⟩
    · -- generateFnPlanAux (fuel+1)
      cases worklist with
      | nil => simp only [generateFnPlanAux, Option.isSome_some]
      | cons lbl rest =>
        simp only [generateFnPlanAux]
        split
        · exact ihAux rest visited ps
        · split
          · exact ihAux rest _ ps
          · rename_i bb hfind
            have hbb : ∀ inst ∈ bb.instructions, codegenReadyInst inst :=
              hfn bb (List.mem_of_find?_eq_some hfind)
            obtain ⟨⟨bo, ps'⟩, hb⟩ := Option.isSome_iff_exists.mp
              (generateBlockPlan_isSome liveness dfg cfg fn bb ps hbb)
            simp only [hb]
            obtain ⟨⟨so, v'', ps''⟩, hs⟩ := Option.isSome_iff_exists.mp
              (ihSuccs ps'.stack ps'.spilled (cfg.succsOf lbl) (lbl :: visited) ps')
            simp only [hs]
            obtain ⟨⟨ro, vF, psF⟩, hrest⟩ := Option.isSome_iff_exists.mp
              (ihAux rest v'' ps'')
            simp only [hrest, Option.isSome_some]
    · -- generateSuccsPlan (fuel+1)
      cases succs with
      | nil => simp only [generateSuccsPlan, Option.isSome_some]
      | cons succ rest =>
        simp only [generateSuccsPlan]
        obtain ⟨⟨so, vAfter, psAfter⟩, ha⟩ := Option.isSome_iff_exists.mp
          (ihAux [succ] visited { ps with stack := ss, spilled := sp })
        simp only [ha]
        obtain ⟨⟨ro, vF, psF⟩, hr⟩ := Option.isSome_iff_exists.mp
          (ihSuccs ss sp rest vAfter
            { ps with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter })
        simp only [hr, Option.isSome_some]

/-- The final repackaging match in `generate_context_plan_fuel` preserves `isSome`. -/
theorem ctxPlan_repack_isSome
    (o : Option (List StackOp × Nat)) (f : List StackOp → Nat → List StackOp) (h : o.isSome) :
    (match o with | none => none | some (a, b) => some (f a b)).isSome := by
  rcases o with _ | ⟨a, b⟩
  · simp at h
  · rfl

/-- `generate_fn_plan_fuel` succeeds on a codegen-ready function. -/
theorem generateFnPlanFuel_isSome (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    (generateFnPlanFuel fuel fn fnEom lblCtr).isSome := by
  unfold generateFnPlanFuel
  split
  · simp only [Option.isSome_some]
  · rename_i lbl _
    obtain ⟨⟨ops, v, ps'⟩, h⟩ := Option.isSome_iff_exists.mp
      ((generateFnPlanAux_generateSuccsPlan_isSome (livenessAnalyzeFuel fuel fn)
        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn hfn fuel).1
        [lbl] [] { initPlanState fnEom with labelCounter := lblCtr })
    simp only [h, Option.isSome_some]

/-- `generate_fn_plan` succeeds on a codegen-ready function. -/
theorem generateFnPlan_isSome (fn : IrFunction) (fnEom lblCtr : Nat)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    (generateFnPlan fn fnEom lblCtr).isSome :=
  generateFnPlanFuel_isSome _ fn fnEom lblCtr hfn

/-! ## Context level

The non-vacuity `codegen_correct` needs: `generate_context_plan_fuel` (the real,
executable codegen used by `codegenFuel`) succeeds on any codegen-ready context. -/

/-- The per-function fold inside `generate_context_plan_fuel` stays `some` when every
    function is codegen-ready. -/
theorem genCtxFold_isSome (fuel : Nat) (fnEomMap : AssocList String Nat) (fns : List IrFunction)
    (hfns : ∀ fn ∈ fns, codegenReadyFn fn) :
    ∀ (init : List StackOp × Nat),
    (fns.foldl
      (fun (acc : Option (List StackOp × Nat)) fn =>
        match acc with
        | none => none
        | some (ops, lblCtr) =>
          let eom := (AssocList.lookup String Nat fnEomMap fn.name).getD 0
          match generateFnPlanFuel fuel fn eom lblCtr with
          | none => none
          | some (fnOps, ps) => some (ops ++ fnOps, ps.labelCounter))
      (some init)).isSome := by
  induction fns with
  | nil => intro init; rfl
  | cons hd tl ih =>
    intro init
    rw [List.foldl_cons]
    obtain ⟨ops, lblCtr⟩ := init
    obtain ⟨⟨fnOps, ps⟩, hf⟩ := Option.isSome_iff_exists.mp
      (generateFnPlanFuel_isSome fuel hd
        ((AssocList.lookup String Nat fnEomMap hd.name).getD 0) lblCtr
        (hfns hd List.mem_cons_self).1)
    simp only [hf]
    exact ih (fun fn hfn => hfns fn (List.mem_cons_of_mem _ hfn)) (ops ++ fnOps, ps.labelCounter)

/-- `generate_context_plan_fuel` (the real, executable codegen used by `codegenFuel`)
    succeeds on a codegen-ready context — the concrete non-vacuity. -/
theorem generateContextPlanFuel_isSome (fuel : Nat) (ctx : VenomContext)
    (fnEomMap : AssocList String Nat) (h : codegenReady ctx) :
    (generateContextPlanFuel fuel ctx fnEomMap).isSome := by
  unfold generateContextPlanFuel
  exact ctxPlan_repack_isSome _ _ (genCtxFold_isSome fuel fnEomMap ctx.functions h ([], 0))

/-! ## Byte-pipeline level

The full `codegenFuel` pipeline = plan generation ▸ `executePlan` ▸ `assemble`. Plan
generation is total on ready contexts (above) and the back end is unconditionally
total, so the whole pipeline succeeds; and its output bytes are exactly the assembled
plan. The latter is the bridge for eventually tying `codegen_correct`'s `prog` to the
actual codegen result. -/

/-- The full byte-level codegen pipeline succeeds on a codegen-ready context:
    plan generation succeeds (`generateContextPlanFuel_isSome`) and `executePlan` /
    `assemble` are total. -/
theorem codegenFuel_isSome (fuel : Nat) (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) (h : codegenReady ctx) :
    (codegenFuel fuel ctx fnEomMap dataSeg).isSome := by
  unfold codegenFuel
  obtain ⟨plan, hp⟩ := Option.isSome_iff_exists.mp
    (generateContextPlanFuel_isSome fuel ctx fnEomMap h)
  simp only [hp, Option.isSome_some]

/-- Bytecode produced by the fuel pipeline is exactly the assembled plan — the bridge
    that ties a codegen output to the generated stack plan (groundwork for tying
    `codegen_correct`'s `prog` to the actual codegen result). -/
theorem codegenFuel_eq_assemble (fuel : Nat) (ctx : VenomContext)
    (fnEomMap : AssocList String Nat) (dataSeg : List DataSection) (plan : List StackOp)
    (hp : generateContextPlanFuel fuel ctx fnEomMap = some plan) :
    codegenFuel fuel ctx fnEomMap dataSeg
      = some (assemble (executePlan plan ++ dataSeg.flatMap dataSectionAsm)) := by
  unfold codegenFuel
  simp only [hp]

/-! ## Plan structure — the entry block's plan is the function plan's prefix

`generateFnPlanFuel` processes the entry block first (the initial DFS worklist is `[entryLabel]`), so a
successful function plan is `entryBlockOps ++ succOps` — the entry block's `generateBlockPlan` output is
a prefix. Combined with `asmBlockAt_of_labelFree_plan` (`pre = []`, so pc 0), this discharges the block
sims' `hblock` obligation for the entry block *from the actual `generateFnPlan` output*, not as an
assumption. -/

/-- The DFS on an empty worklist returns the empty plan. -/
theorem generateFnPlanAux_nil (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (visited : List String) (ps : PlanState) :
    generateFnPlanAux fuel L D C fn [] visited ps = some ([], visited, ps) := by
  cases fuel <;> rfl

/-! ### DFS plan-state threading — the well-scheduling plan-match, structurally

`generateFnPlanAux`/`generateSuccsPlan` thread the plan state across the CFG so that a first-visited
successor's block plan is generated from its predecessor's **exit** plan state. These unfolding lemmas
read that off the definitions — the definitional core of the well-scheduling plan-match
(`psPostBody = psOf bb'` on DFS-tree edges; join points / multi-pred blocks additionally need the JMP
reorder). -/

/-- Setting `stack`/`spilled` to their own values is the identity (structure eta) — the reason the
    `generateSuccsPlan` branch state equals the incoming plan state. -/
theorem planState_eta_stack_spilled (ps : PlanState) :
    ({ ps with stack := ps.stack, spilled := ps.spilled } : PlanState) = ps := rfl

/-- **`generateSuccsPlan` branches the first successor from the predecessor's exit plan state.** When
    the saved stack/spilled come from the same `ps'` threaded as `psG` (exactly how `generateFnPlanAux`
    invokes it after `generateBlockPlan`), the branch plan state `{ psG with stack := savedStack,
    spilled := savedSpilled }` is `ps'` itself — so the first successor's `generateFnPlanAux` runs from
    `ps'`. The definitional core of the well-scheduling plan-match: successor entry plan = predecessor
    exit plan. -/
theorem generateSuccsPlan_cons_from_exit (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (succ : String) (rest visited : List String) (ps' : PlanState) :
    generateSuccsPlan (fuel + 1) L D C fn ps'.stack ps'.spilled (succ :: rest) visited ps' =
    (match generateFnPlanAux fuel L D C fn [succ] visited ps' with
     | none => none
     | some (sOps, vAfter, psAfter) =>
       match generateSuccsPlan fuel L D C fn ps'.stack ps'.spilled rest vAfter
               { ps' with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
       | none => none
       | some (restOps, vF, psF) => some (sOps ++ restOps, vF, psF)) := rfl

/-- **`generateFnPlanAux` visit-block unfolding.** For a not-yet-visited `lbl` found as `bb`, the DFS
    generates `bb`'s plan from the incoming plan state `ps` (`generateBlockPlan … bb ps`), then its
    successors from the *exit* plan state `ps'` (`generateSuccsPlan … ps'.stack ps'.spilled …`), then
    the rest of the worklist. Reads the DFS branch structure off `generateFnPlanAux`'s definition. -/
theorem generateFnPlanAux_visit_block (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String) (ps : PlanState)
    (bb : BasicBlock)
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb) :
    generateFnPlanAux (fuel + 1) L D C fn (lbl :: rest) visited ps =
    (match generateBlockPlan L D C fn bb ps with
     | none => none
     | some (blockOps, ps') =>
       match generateSuccsPlan fuel L D C fn ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited) ps' with
       | none => none
       | some (succOps, visited'', ps'') =>
         match generateFnPlanAux fuel L D C fn rest visited'' ps'' with
         | none => none
         | some (restOps, vF, psF) => some (blockOps ++ succOps ++ restOps, vF, psF)) := by
  conv_lhs => rw [generateFnPlanAux]
  rw [if_neg (by rw [hvis]; simp)]
  simp only [hfind]
  rfl

/-- **First-visit successor is scheduled from the predecessor's exit plan state.** The `[succ]`
    specialisation of `generateFnPlanAux_visit_block` — exactly what `generateSuccsPlan` invokes per
    successor. If `succ` is not yet visited (a DFS-tree edge, not a join back-edge), its block plan is
    generated from the incoming `ps'` (the predecessor's exit plan state). This is the well-scheduling
    plan-match on tree edges: `psPostBody (= ps') = psOf succ`. -/
theorem succ_blockPlan_from_pred_exit (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (succ : String) (visited : List String) (ps' : PlanState)
    (succBB : BasicBlock)
    (hvis : visited.contains succ = false)
    (hfind : fn.blocks.find? (·.label == succ) = some succBB) :
    generateFnPlanAux (fuel + 1) L D C fn [succ] visited ps' =
    (match generateBlockPlan L D C fn succBB ps' with
     | none => none
     | some (blockOps, psS) =>
       match generateSuccsPlan fuel L D C fn psS.stack psS.spilled (C.succsOf succ) (succ :: visited) psS with
       | none => none
       | some (succOps, visited'', ps'') =>
         match generateFnPlanAux fuel L D C fn [] visited'' ps'' with
         | none => none
         | some (restOps, vF, psF) => some (blockOps ++ succOps ++ restOps, vF, psF)) :=
  generateFnPlanAux_visit_block fuel L D C fn succ [] visited ps' succBB hvis hfind

/-- **`generateFnPlanAux` skips an already-visited block.** When `lbl ∈ visited` (a DFS back-edge /
    join re-entry), the DFS generates no plan for it and moves to the rest of the worklist — so a join
    point's entry plan state is fixed by its *first* predecessor's visit, not re-derived from later
    predecessors. Each other predecessor instead reorders its exit stack to that fixed entry layout at
    its JMP (`generateRegularInstPlan`'s `joinOps`: `reorderPlan (targetStack.map Operand.Var)`, where
    `targetStack = inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt … target 0)` is the
    target's expected entry stack). That per-predecessor join reorder — not the DFS entry-plan — is what
    reconciles the multi-pred join. -/
theorem generateFnPlanAux_skip_visited (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String) (ps : PlanState)
    (hvis : visited.contains lbl = true) :
    generateFnPlanAux (fuel + 1) L D C fn (lbl :: rest) visited ps =
    generateFnPlanAux fuel L D C fn rest visited ps := by
  conv_lhs => rw [generateFnPlanAux]
  rw [if_pos (by rw [hvis])]

/-- **DFS assembly: a first-visit successor's plan is a prefix beginning with its `generateBlockPlan`
    run on the predecessor's exit.** Composes `generateSuccsPlan_cons_from_exit` (first successor
    branched from `ps'`) with `succ_blockPlan_from_pred_exit` (branch generated from `ps'`) and the
    totality lemmas (`generateBlockPlan_isSome`, `generateFnPlanAux_generateSuccsPlan_isSome`) to
    collapse the nested DFS matches. The result: in the `generateSuccsPlan` the DFS invokes after a
    block whose exit is `ps'`, the first successor `succBB`'s `generateBlockPlan` runs on **`ps'`** — the
    concrete realisation of the well-scheduling plan-match `psPostBody (= ps') = psOf succ` on a tree
    edge, extracted from an actual (codegen-ready) generator run. -/
theorem generateSuccsPlan_first_succ_prefix (fuel : Nat) (L : DfState (List String))
    (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction) (succ : String) (rest visited : List String)
    (ps' : PlanState) (succBB : BasicBlock)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hsvis : visited.contains succ = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB) :
    ∃ succBlockOps psS tailOps vF psF,
      generateBlockPlan L D C fn succBB ps' = some (succBlockOps, psS) ∧
      generateSuccsPlan (fuel + 2) L D C fn ps'.stack ps'.spilled (succ :: rest) visited ps'
        = some (succBlockOps ++ tailOps, vF, psF) := by
  rw [generateSuccsPlan_cons_from_exit (fuel + 1) L D C fn succ rest visited ps',
      succ_blockPlan_from_pred_exit fuel L D C fn succ visited ps' succBB hsvis hsfind]
  have hready : ∀ inst ∈ succBB.instructions, codegenReadyInst inst :=
    hfn succBB (List.mem_of_find?_eq_some hsfind)
  obtain ⟨⟨succBlockOps, psS⟩, hbp⟩ :=
    Option.isSome_iff_exists.mp (generateBlockPlan_isSome L D C fn succBB ps' hready)
  obtain ⟨ihAux, ihSuccs⟩ := generateFnPlanAux_generateSuccsPlan_isSome L D C fn hfn fuel
  obtain ⟨⟨so2, v2, ps2⟩, hs2⟩ :=
    Option.isSome_iff_exists.mp (ihSuccs psS.stack psS.spilled (C.succsOf succ) (succ :: visited) psS)
  obtain ⟨⟨ro, v3, ps3⟩, h3⟩ := Option.isSome_iff_exists.mp (ihAux [] v2 ps2)
  obtain ⟨ihAux1, ihSuccs1⟩ := generateFnPlanAux_generateSuccsPlan_isSome L D C fn hfn (fuel + 1)
  obtain ⟨⟨restOps, vF, psF⟩, hr⟩ :=
    Option.isSome_iff_exists.mp (ihSuccs1 ps'.stack ps'.spilled rest v3
      { ps' with alloc := ps3.alloc, labelCounter := ps3.labelCounter })
  refine ⟨succBlockOps, psS, so2 ++ ro ++ restOps, vF, psF, hbp, ?_⟩
  simp only [hbp, hs2, h3, hr, List.append_assoc]

/-- **The entry block's plan is the prefix of a successful function plan.** A successful
    `generateFnPlanFuel` is `entryBlockOps ++ succOps` where `entryBlockOps` is the entry block's
    `generateBlockPlan` output — obtained via the totality lemmas (`generateBlockPlan_isSome`,
    `generateFnPlanAux_generateSuccsPlan_isSome`) and the singleton-worklist computation. -/
theorem generateFnPlanFuel_entry_isPrefix {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hfuel : 0 < fuel) (hentry : fn.blocks.head? = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ blockOps ps' rest,
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
        entry { initPlanState fnEom with labelCounter := lblCtr } = some (blockOps, ps') ∧
      ops = blockOps ++ rest := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨tl, hblocks⟩ := List.head?_eq_some_iff.mp hentry
  have hbbmem : entry ∈ fn.blocks := by rw [hblocks]; exact List.mem_cons_self
  have hfind : fn.blocks.find? (fun b => b.label == entry.label) = some entry := by
    rw [hblocks, List.find?_cons_of_pos (by simp)]
  obtain ⟨⟨bo, ps'⟩, hbp⟩ := Option.isSome_iff_exists.mp
    (generateBlockPlan_isSome (livenessAnalyzeFuel (f + 1) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr }
      (fun inst h => hfn entry hbbmem inst h))
  obtain ⟨⟨so, v'', ps''⟩, hsp⟩ := Option.isSome_iff_exists.mp
    ((generateFnPlanAux_generateSuccsPlan_isSome (livenessAnalyzeFuel (f + 1) fn)
      (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn hfn f).2
      ps'.stack ps'.spilled ((cfgAnalyze fn).succsOf entry.label) [entry.label] ps')
  have hfnplan : generateFnPlanFuel (f + 1) fn fnEom lblCtr = some (bo ++ so, ps'') := by
    simp only [generateFnPlanFuel, entryBlock, hentry, Option.map_some, generateFnPlanAux,
      List.contains_nil, Bool.false_eq_true, if_false, hfind, hbp, hsp, generateFnPlanAux_nil,
      List.append_nil]
  rw [hfnplan] at hgen
  simp only [Option.some.injEq, Prod.mk.injEq] at hgen
  exact ⟨bo, ps', so, hbp, hgen.1.symm⟩

/-- `generateFnPlan` corollary of `generateFnPlanFuel_entry_isPrefix` (the generous `fnPlanFuel` is
    positive): the entry block's plan is a prefix of the whole-function plan. -/
theorem generateFnPlan_entry_isPrefix {fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hentry : fn.blocks.head? = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps)) :
    ∃ blockOps ps' rest,
      generateBlockPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr } = some (blockOps, ps') ∧
      ops = blockOps ++ rest := by
  unfold generateFnPlan at hgen
  exact generateFnPlanFuel_entry_isPrefix (by simp only [fnPlanFuel]; omega) hentry hfn hgen

/-! ## Two-block layout — a non-entry block's plan is a segment

`generateFnPlan_entry_isPrefix` locates the *entry* block (pc 0). To reach a **non-entry** block we
need its plan's position in the whole-function output. This is the base case: a 2-block function
`[entry, next]` where `entry`'s only successor is a terminal `next`. Unfolding the CFG-DFS
(`generateFnPlanAux`/`generateSuccsPlan`) one level into the successor, the plan is exactly
`entryOps ++ nextOps` — so `next`'s plan sits at `pc = (executePlan entryOps).length`. This is what a
non-entry block sim (a JMP predecessor leaving live vars on the stack) needs for its `hblock`/`hget`. -/

/-- **Two-block function plan = `entryOps ++ nextOps`** (fuel form). For `fn.blocks = [entry, next]`
    with `entry`'s single successor the terminal `next`, the successful plan splits as the entry block's
    plan followed by `next`'s (generated from `entry`'s post-state). -/
theorem generateFnPlanFuel_twoBlock_split {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry next : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hfuel : 3 ≤ fuel)
    (hblocks : fn.blocks = [entry, next])
    (hsucc : (cfgAnalyze fn).succsOf entry.label = [next.label])
    (hnextterm : (cfgAnalyze fn).succsOf next.label = [])
    (hne : (entry.label == next.label) = false)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ entryOps ps1 nextOps ps2,
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr } = some (entryOps, ps1) ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn next ps1 = some (nextOps, ps2) ∧
      ops = entryOps ++ nextOps := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  have hentry : fn.blocks.head? = some entry := by rw [hblocks]; rfl
  have hem : entry ∈ fn.blocks := by rw [hblocks]; simp
  have hnm : next ∈ fn.blocks := by rw [hblocks]; simp
  obtain ⟨⟨entryOps, ps1⟩, hbpE⟩ := Option.isSome_iff_exists.mp
    (generateBlockPlan_isSome (livenessAnalyzeFuel (f+3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr }
      (fun inst h => hfn entry hem inst h))
  obtain ⟨⟨nextOps, ps2⟩, hbpN⟩ := Option.isSome_iff_exists.mp
    (generateBlockPlan_isSome (livenessAnalyzeFuel (f+3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn next ps1 (fun inst h => hfn next hnm inst h))
  refine ⟨entryOps, ps1, nextOps, ps2, hbpE, hbpN, ?_⟩
  have hfindE : fn.blocks.find? (fun b => b.label == entry.label) = some entry := by
    rw [hblocks, List.find?_cons_of_pos (by simp)]
  have hne' : (next.label == entry.label) = false := by
    rw [beq_eq_false_iff_ne] at hne ⊢; exact fun h => hne h.symm
  have hSuccNil : ∀ (ff : Nat) (ss sp : _) (vis : List String) (p : PlanState),
      generateSuccsPlan ff (livenessAnalyzeFuel (f+3) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn ss sp [] vis p = some ([], vis, p) := by
    intro ff ss sp vis p; cases ff <;> rfl
  have hfindN : fn.blocks.find? (fun b => b.label == next.label) = some next := by
    rw [hblocks, List.find?_cons_of_neg (by simp [hne]), List.find?_cons_of_pos (by simp)]
  simp only [generateFnPlanFuel, entryBlock, hentry, Option.map_some,
    generateFnPlanAux, List.contains_nil, Bool.false_eq_true, if_false, hfindE, hbpE,
    generateSuccsPlan, hsucc, List.contains_cons, hne', List.contains_nil, Bool.or_false,
    hfindN, hbpN, hnextterm, generateFnPlanAux_nil, hSuccNil, List.append_nil] at hgen
  simp only [Option.some.injEq, Prod.mk.injEq] at hgen
  exact hgen.1.symm

/-- `generateFnPlan` corollary of `generateFnPlanFuel_twoBlock_split` (`fnPlanFuel ≥ 3`). -/
theorem generateFnPlan_twoBlock_split {fnEom lblCtr : Nat} {fn : IrFunction}
    {entry next : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hblocks : fn.blocks = [entry, next])
    (hsucc : (cfgAnalyze fn).succsOf entry.label = [next.label])
    (hnextterm : (cfgAnalyze fn).succsOf next.label = [])
    (hne : (entry.label == next.label) = false)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps)) :
    ∃ entryOps ps1 nextOps ps2,
      generateBlockPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr } = some (entryOps, ps1) ∧
      generateBlockPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn next ps1 = some (nextOps, ps2) ∧
      ops = entryOps ++ nextOps := by
  unfold generateFnPlan at hgen
  exact generateFnPlanFuel_twoBlock_split (by simp only [fnPlanFuel]; omega)
    hblocks hsucc hnextterm hne hfn hgen


/- **Instrumented entry-recording DFS.** Mirrors `generateFnPlanAux`/`generateSuccsPlan` exactly —
    same worklist/visited/plan-state threading, same `generateBlockPlan` calls — but drops the plan-op
    accumulation and instead records each block's *entry* plan state (the `ps` at first visit) into a
    label→PlanState table. psOf is read off this table. -/
mutual
def dfsEntriesAux : Nat → DfState (List String) → DfgAnalysis → CfgAnalysis → IrFunction →
    List String → List String → AssocList String PlanState → PlanState →
    Option (List String × AssocList String PlanState × PlanState)
  | 0,        _, _, _, _,  _,           visited, tbl, ps => some (visited, tbl, ps)
  | _ + 1,    _, _, _, _,  [],          visited, tbl, ps => some (visited, tbl, ps)
  | fuel + 1, L, D, C, fn, lbl :: rest, visited, tbl, ps =>
    if visited.contains lbl then dfsEntriesAux fuel L D C fn rest visited tbl ps
    else
      let visited' := lbl :: visited
      let tbl' := AssocList.insert String PlanState tbl lbl ps
      match fn.blocks.find? (·.label == lbl) with
      | none => dfsEntriesAux fuel L D C fn rest visited' tbl' ps
      | some bb =>
        match generateBlockPlan L D C fn bb ps with
        | none => none
        | some (_, ps') =>
          match dfsSuccsEntries fuel L D C fn ps'.stack ps'.spilled
                  (C.succsOf lbl) visited' tbl' ps' with
          | none => none
          | some (visited'', tbl'', ps'') =>
            dfsEntriesAux fuel L D C fn rest visited'' tbl'' ps''
def dfsSuccsEntries : Nat → DfState (List String) → DfgAnalysis → CfgAnalysis → IrFunction →
    List Operand → SpilledMap → List String → List String → AssocList String PlanState → PlanState →
    Option (List String × AssocList String PlanState × PlanState)
  | 0,        _, _, _, _, _,          _,            _,           visited, tbl, ps => some (visited, tbl, ps)
  | _ + 1,    _, _, _, _, _,          _,            [],          visited, tbl, ps => some (visited, tbl, ps)
  | fuel + 1, L, D, C, fn, savedStack, savedSpilled, succ :: rest, visited, tbl, psG =>
    let psBranch := { psG with stack := savedStack, spilled := savedSpilled }
    match dfsEntriesAux fuel L D C fn [succ] visited tbl psBranch with
    | none => none
    | some (vAfter, tblAfter, psAfter) =>
      let psG' := { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
      match dfsSuccsEntries fuel L D C fn savedStack savedSpilled rest vAfter tblAfter psG' with
      | none => none
      | some (vF, tblF, psF) => some (vF, tblF, psF)
end

/-- Visit-block unfolding for `dfsEntriesAux` (mirror of `generateFnPlanAux_visit_block`). -/
theorem dfsEntriesAux_visit_block (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (bb : BasicBlock)
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb) :
    dfsEntriesAux (fuel + 1) L D C fn (lbl :: rest) visited tbl ps =
    (match generateBlockPlan L D C fn bb ps with
     | none => none
     | some (_, ps') =>
       match dfsSuccsEntries fuel L D C fn ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited)
               (AssocList.insert String PlanState tbl lbl ps) ps' with
       | none => none
       | some (visited'', tbl'', ps'') =>
         dfsEntriesAux fuel L D C fn rest visited'' tbl'' ps'') := by
  conv_lhs => rw [dfsEntriesAux]
  rw [if_neg (by rw [hvis]; simp)]
  simp only [hfind]

/-- Skip-unfolding for `dfsEntriesAux` (already-visited block). -/
theorem dfsEntriesAux_skip (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState) (hvis : visited.contains lbl = true) :
    dfsEntriesAux (fuel + 1) L D C fn (lbl :: rest) visited tbl ps
      = dfsEntriesAux fuel L D C fn rest visited tbl ps := by
  conv_lhs => rw [dfsEntriesAux]
  rw [if_pos (by rw [hvis])]

/-- Find?-none unfolding for `dfsEntriesAux`. -/
theorem dfsEntriesAux_find_none (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String)
    (tbl : AssocList String PlanState) (ps : PlanState)
    (hvis : visited.contains lbl = false) (hfind : fn.blocks.find? (·.label == lbl) = none) :
    dfsEntriesAux (fuel + 1) L D C fn (lbl :: rest) visited tbl ps
      = dfsEntriesAux fuel L D C fn rest (lbl :: visited)
          (AssocList.insert String PlanState tbl lbl ps) ps := by
  conv_lhs => rw [dfsEntriesAux]
  rw [if_neg (by rw [hvis]; simp)]
  simp only [hfind]

/-- Find?-none unfolding for `generateFnPlanAux`. -/
theorem generateFnPlanAux_find_none (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (lbl : String) (rest visited : List String) (ps : PlanState)
    (hvis : visited.contains lbl = false) (hfind : fn.blocks.find? (·.label == lbl) = none) :
    generateFnPlanAux (fuel + 1) L D C fn (lbl :: rest) visited ps
      = generateFnPlanAux fuel L D C fn rest (lbl :: visited) ps := by
  conv_lhs => rw [generateFnPlanAux]
  rw [if_neg (by rw [hvis]; simp)]
  simp only [hfind]

/-- Lift an IH `(visited,ps)` equality through the base DFS's op-recombination on the RHS (the
    recombine only touches `r.1`, invisible to the `(r.2.1, r.2.2)` projection). -/
theorem recombine_lift_A (Dd : Option (List String × AssocList String PlanState × PlanState))
    (G : Option (List StackOp × List String × PlanState)) (pre : List StackOp)
    (h : Dd.map (fun r => (r.1, r.2.2)) = G.map (fun r => (r.2.1, r.2.2))) :
    Dd.map (fun r => (r.1, r.2.2))
      = (match G with | none => none | some (o, v, p) => some (pre ++ o, v, p)).map
          (fun (r : List StackOp × List String × PlanState) => (r.2.1, r.2.2)) := by
  cases G with
  | none => simpa using h
  | some rg => obtain ⟨o, v, p⟩ := rg; simpa using h

/-- Like `recombine_lift_A` but the LHS also carries the (identity) repackaging of the succs DFS. -/
theorem recombine_lift_S (Dd : Option (List String × AssocList String PlanState × PlanState))
    (G : Option (List StackOp × List String × PlanState)) (pre : List StackOp)
    (h : Dd.map (fun r => (r.1, r.2.2)) = G.map (fun r => (r.2.1, r.2.2))) :
    (match Dd with | none => none | some (v, t, p) => some (v, t, p)).map
        (fun (r : List String × AssocList String PlanState × PlanState) => (r.1, r.2.2))
      = (match G with | none => none | some (o, v, p) => some (pre ++ o, v, p)).map
          (fun (r : List StackOp × List String × PlanState) => (r.2.1, r.2.2)) := by
  cases Dd with
  | none => cases G with | none => rfl | some rg => obtain ⟨o, v, p⟩ := rg; simp at h
  | some rd =>
    obtain ⟨v, t, p⟩ := rd
    cases G with
    | none => simp at h
    | some rg =>
      obtain ⟨o, v', p'⟩ := rg
      simpa using h

set_option linter.unusedSimpArgs false in
/-- **Faithful instrumentation.** `dfsEntriesAux`/`dfsSuccsEntries` thread `(visited, ps)` identically
    to `generateFnPlanAux`/`generateSuccsPlan` — same DFS, same plan-state thread; the entry table is
    passive. So the entry plans recorded are exactly those the real codegen assigns. -/
theorem dfsEntries_faithful (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState),
      (dfsEntriesAux fuel L D C fn worklist visited tbl ps).map (fun r => (r.1, r.2.2))
        = (generateFnPlanAux fuel L D C fn worklist visited ps).map (fun r => (r.2.1, r.2.2)))
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState),
      (dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG).map
          (fun r => (r.1, r.2.2))
        = (generateSuccsPlan fuel L D C fn savedStack savedSpilled succs visited psG).map
          (fun r => (r.2.1, r.2.2))) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited tbl ps => ?_, fun ss sp succs visited tbl psG => ?_⟩ <;> rfl
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨fun worklist visited tbl ps => ?_, fun ss sp succs visited tbl psG => ?_⟩
    · cases worklist with
      | nil => rfl
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis,
              generateFnPlanAux_skip_visited _ _ _ _ _ _ _ _ _ hvis]
          exact ihA rest visited tbl ps
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfind,
                generateFnPlanAux_find_none _ _ _ _ _ _ _ _ _ hvisf hfind]
            exact ihA rest (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps
          | some bb =>
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfind,
                generateFnPlanAux_visit_block _ _ _ _ _ _ _ _ _ _ hvisf hfind]
            cases hbp : generateBlockPlan L D C fn bb ps with
            | none => rfl
            | some r =>
              obtain ⟨blockOps, ps'⟩ := r
              have hs := ihS ps'.stack ps'.spilled (C.succsOf lbl) (lbl :: visited)
                (AssocList.insert String PlanState tbl lbl ps) ps'
              cases hgs : generateSuccsPlan n L D C fn ps'.stack ps'.spilled (C.succsOf lbl)
                  (lbl :: visited) ps' with
              | none =>
                rw [hgs] at hs
                cases hds : dfsSuccsEntries n L D C fn ps'.stack ps'.spilled (C.succsOf lbl)
                    (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps' with
                | none => simp [hgs, hds]
                | some rd => rw [hds] at hs; simp at hs
              | some rg =>
                obtain ⟨succOps, visited'', ps''⟩ := rg
                rw [hgs] at hs
                cases hds : dfsSuccsEntries n L D C fn ps'.stack ps'.spilled (C.succsOf lbl)
                    (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) ps' with
                | none => rw [hds] at hs; simp at hs
                | some rd =>
                  obtain ⟨visited''e, tbl''e, ps''e⟩ := rd
                  rw [hds] at hs
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
                  obtain ⟨hv, hp⟩ := hs
                  simp only [hds, hgs]
                  rw [hv, hp]
                  exact recombine_lift_A _ _ (blockOps ++ succOps) (ihA rest visited'' tbl''e ps'')
    · cases succs with
      | nil => rfl
      | cons succ rest =>
        conv_lhs => rw [dfsSuccsEntries]
        conv_rhs => rw [generateSuccsPlan]
        have ha := ihA [succ] visited tbl { psG with stack := ss, spilled := sp }
        cases hga : generateFnPlanAux n L D C fn [succ] visited { psG with stack := ss, spilled := sp } with
        | none =>
          rw [hga] at ha
          cases hda : dfsEntriesAux n L D C fn [succ] visited tbl { psG with stack := ss, spilled := sp } with
          | none => simp [hga, hda]
          | some rd => rw [hda] at ha; simp at ha
        | some rg =>
          obtain ⟨sOps, vAfter, psAfter⟩ := rg
          rw [hga] at ha
          cases hda : dfsEntriesAux n L D C fn [succ] visited tbl { psG with stack := ss, spilled := sp } with
          | none => rw [hda] at ha; simp at ha
          | some rd =>
            obtain ⟨vAfterE, tblAfterE, psAfterE⟩ := rd
            rw [hda] at ha
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
            obtain ⟨hv, hp⟩ := ha
            simp only [hda, hga]
            rw [hv, hp]
            exact recombine_lift_S _ _ sOps (ihS ss sp rest vAfter tblAfterE
              { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter })

/-- **Per-block entry-plan table** for a function: run the instrumented DFS from the entry block and
    collect the label→entry-PlanState map. Mirrors `generateFnPlanFuel`'s setup exactly (same liveness/
    dfg/cfg/initial plan), so — by `dfsEntries_faithful` — the plan-state thread is the real codegen's. -/
def blockEntryTable (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat) : AssocList String PlanState :=
  let liveness := livenessAnalyzeFuel fuel fn
  let dfg := DfgAnalysis.buildFunction fn
  let cfg := cfgAnalyze fn
  let ps := { initPlanState fnEom with labelCounter := lblCtr }
  match (entryBlock fn).map (·.label) with
  | none => []
  | some lbl =>
    match dfsEntriesAux fuel liveness dfg cfg fn [lbl] [] [] ps with
    | none => []
    | some (_, tbl, _) => tbl

/-- **Concrete `psOf`**: the total per-label entry plan-state function that instantiates
    `hfsim_venomAsmRelSched`'s abstract `psOf` parameter. Looks each block's entry plan up in the DFS
    entry table (`default` off-CFG). -/
def psOfFn (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat) (lbl : String) : PlanState :=
  (AssocList.lookup String PlanState (blockEntryTable fuel fn fnEom lblCtr) lbl).getD default


/-! ## General DFS plan decomposition — a JMP-chain target's plan is a segment

The entry-prefix / two-block lemmas above locate pc-0 and a single successor. These generalize to an
arbitrary-length single-successor (JMP) chain: the head-prefix base, the single-successor nesting step
(`ops[lbl] = bbBlock ++ ops[succ]`), and their induction (`generateFnPlanAux_chain_segment`) place any
chain-reachable block's plan as a segment of the whole-function output — the layout fact a non-entry
block sim needs at its `pcOfLabel`. -/

/-- **Entry's first successor is a segment (any function).** Generalizes `twoBlock_split`: no
    2-block restriction — for any codegen-ready function whose entry has a fresh first successor `succ`,
    the plan is `entryOps ++ succBlockOps ++ rest`, so `succ`'s plan sits at `pc = (executePlan entryOps).length`. -/
theorem generateFnPlanFuel_first_succ_segment {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry succBB : BasicBlock} {succ : String} {succRest : List String}
    {ops : List StackOp} {ps : PlanState}
    (hfuel : 3 ≤ fuel)
    (hentry : fn.blocks.head? = some entry)
    (hsucc : (cfgAnalyze fn).succsOf entry.label = succ :: succRest)
    (hne : (succ == entry.label) = false)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ entryOps ps' succBlockOps psS rest,
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr } = some (entryOps, ps') ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn succBB ps' = some (succBlockOps, psS) ∧
      ops = entryOps ++ succBlockOps ++ rest := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  obtain ⟨tl, hblocks⟩ := List.head?_eq_some_iff.mp hentry
  have hbbmem : entry ∈ fn.blocks := by rw [hblocks]; exact List.mem_cons_self
  have hfind : fn.blocks.find? (fun b => b.label == entry.label) = some entry := by
    rw [hblocks, List.find?_cons_of_pos (by simp)]
  obtain ⟨⟨entryOps, ps'⟩, hbp⟩ := Option.isSome_iff_exists.mp
    (generateBlockPlan_isSome (livenessAnalyzeFuel (f + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn entry { initPlanState fnEom with labelCounter := lblCtr }
      (fun inst h => hfn entry hbbmem inst h))
  have hsvis : ([entry.label] : List String).contains succ = false := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false]; exact hne
  obtain ⟨succBlockOps, psS, tailOps, vF, psF, hbpS, hsp⟩ :=
    generateSuccsPlan_first_succ_prefix f (livenessAnalyzeFuel (f + 3) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn succ succRest [entry.label] ps' succBB hfn hsvis hsfind
  have hfnplan : generateFnPlanFuel (f + 3) fn fnEom lblCtr = some (entryOps ++ (succBlockOps ++ tailOps), psF) := by
    simp only [generateFnPlanFuel, entryBlock, hentry, Option.map_some, generateFnPlanAux,
      List.contains_nil, Bool.false_eq_true, if_false, hfind, hbp, hsucc, hsp,
      List.append_nil]
  rw [hfnplan] at hgen
  simp only [Option.some.injEq, Prod.mk.injEq] at hgen
  exact ⟨entryOps, ps', succBlockOps, psS, tailOps, hbp, hbpS, by rw [List.append_assoc]; exact hgen.1.symm⟩

/-- `generateSuccsPlan` on an empty successor list returns the identity (any fuel). -/
theorem generateSuccsPlan_nil (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (ss : List Operand) (sp : SpilledMap)
    (visited : List String) (ps : PlanState) :
    generateSuccsPlan fuel L D C fn ss sp [] visited ps = some ([], visited, ps) := by
  cases fuel <;> rfl

/-- **Single-successor nesting step (the JMP-chain recursive core).** For a fresh block `lbl` (found as
    `bb`) whose *only* CFG successor is `succ`, the DFS output for `[lbl]` is `bb`'s block plan followed
    verbatim by the DFS output for `[succ]` run from `bb`'s exit plan state `ps'` — `ops[lbl] =
    bbBlockOps ++ ops[succ]`. Iterating this along a JMP chain nests each block's plan as a segment. -/
theorem generateFnPlanAux_single_succ_step {fuel : Nat} {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {lbl succ : String} {visited : List String} {ps : PlanState}
    {bb : BasicBlock} {bbBlockOps : List StackOp} {ps' : PlanState}
    {succDfsOps : List StackOp} {vAfter : List String} {psAfter : PlanState}
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hsucc : C.succsOf lbl = [succ])
    (hblock : generateBlockPlan L D C fn bb ps = some (bbBlockOps, ps'))
    (hsuccdfs : generateFnPlanAux fuel L D C fn [succ] (lbl :: visited) ps' = some (succDfsOps, vAfter, psAfter)) :
    generateFnPlanAux (fuel + 2) L D C fn [lbl] visited ps
      = some (bbBlockOps ++ succDfsOps, vAfter,
          { ps' with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }) := by
  rw [generateFnPlanAux_visit_block (fuel + 1) L D C fn lbl [] visited ps bb hvis hfind]
  simp only [hblock, hsucc]
  rw [generateSuccsPlan_cons_from_exit fuel L D C fn succ [] (lbl :: visited) ps']
  simp only [hsuccdfs, generateSuccsPlan_nil, generateFnPlanAux_nil, List.append_nil]

/-- **Head-prefix (chain base case).** A fresh, found block's plan is a prefix of the DFS output for
    its own singleton worklist `[lbl]` — `ops[lbl] = bbBlockOps ++ tailOps`. -/
theorem generateFnPlanAux_head_prefix {fuel : Nat} {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {lbl : String} {visited : List String} {ps : PlanState}
    {bb : BasicBlock} {bbBlockOps : List StackOp} {ps' : PlanState}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hvis : visited.contains lbl = false)
    (hfind : fn.blocks.find? (·.label == lbl) = some bb)
    (hblock : generateBlockPlan L D C fn bb ps = some (bbBlockOps, ps')) :
    ∃ tailOps vF psF,
      generateFnPlanAux (fuel + 1) L D C fn [lbl] visited ps = some (bbBlockOps ++ tailOps, vF, psF) := by
  rw [generateFnPlanAux_visit_block fuel L D C fn lbl [] visited ps bb hvis hfind]
  simp only [hblock]
  obtain ⟨⟨succOps, v'', ps''⟩, hsp⟩ := Option.isSome_iff_exists.mp
    ((generateFnPlanAux_generateSuccsPlan_isSome L D C fn hfn fuel).2 ps'.stack ps'.spilled
      (C.succsOf lbl) (lbl :: visited) ps')
  simp only [hsp, generateFnPlanAux_nil, List.append_nil]
  exact ⟨succOps, v'', ps'', rfl⟩

/-- **Single-successor (JMP) chain threading** from `(visited, ps)` down to target label `tgtLbl`.
    `path` is the list of intermediate blocks (head-first, excluding the target). Each intermediate
    block is fresh, found, has the *next* block (or the target) as its single successor, and threads its
    exit plan state forward; the base case asserts the target is fresh, found, and its block plan is
    `(tgtBlockOps, tgtPs')` from the threaded plan state. -/
def JmpChainTo (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (tgtLbl : String) (tgtBlockOps : List StackOp) (tgtPs' : PlanState) :
    List BasicBlock → List String → PlanState → Prop
  | [], visited, ps =>
      visited.contains tgtLbl = false ∧
      (∃ tgtBB, fn.blocks.find? (·.label == tgtLbl) = some tgtBB ∧
        generateBlockPlan L D C fn tgtBB ps = some (tgtBlockOps, tgtPs'))
  | bb :: rest, visited, ps =>
      visited.contains bb.label = false ∧
      fn.blocks.find? (·.label == bb.label) = some bb ∧
      C.succsOf bb.label = [(rest.head?.map (·.label)).getD tgtLbl] ∧
      (∃ block ps', generateBlockPlan L D C fn bb ps = some (block, ps') ∧
        JmpChainTo L D C fn tgtLbl tgtBlockOps tgtPs' rest (bb.label :: visited) ps')

/-- **Chain-segment decomposition.** A target reached from the DFS head via a single-successor (JMP)
    chain has its block plan as a *segment* of the DFS output: `ops = preOps ++ tgtBlockOps ++ tailOps`.
    Base = head-prefix (target is the head); step = single-successor nesting (`ops[bb] = bbBlock ++
    ops[succ]`), accumulating `bbBlock` into `preOps`. Each JMP step costs 2 DFS fuel, hence `2·len+1`. -/
theorem generateFnPlanAux_chain_segment {L : DfState (List String)} {D : DfgAnalysis}
    {C : CfgAnalysis} {fn : IrFunction} {tgtLbl : String} {tgtBlockOps : List StackOp} {tgtPs' : PlanState}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (path : List BasicBlock) (fuel : Nat) (visited : List String) (ps : PlanState),
      2 * path.length + 1 ≤ fuel →
      JmpChainTo L D C fn tgtLbl tgtBlockOps tgtPs' path visited ps →
      ∃ preOps tailOps vF psF,
        generateFnPlanAux fuel L D C fn [(path.head?.map (·.label)).getD tgtLbl] visited ps
          = some (preOps ++ tgtBlockOps ++ tailOps, vF, psF) := by
  intro path
  induction path with
  | nil =>
    intro fuel visited ps hfuel hchain
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, tgtBB, hfind, hblock⟩ := hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨tailOps, vF, psF, hgen⟩ := generateFnPlanAux_head_prefix hfn hvis hfind hblock
    refine ⟨[], tailOps, vF, psF, ?_⟩
    simpa only [List.head?_nil, Option.map_none, Option.getD_none, List.nil_append] using hgen
  | cons bb rest ih =>
    intro fuel visited ps hfuel hchain
    simp only [JmpChainTo] at hchain
    obtain ⟨hvis, hfind, hsucc, block, ps', hblock, hchain'⟩ := hchain
    obtain ⟨fr, rfl⟩ : ∃ fr, fuel = fr + 2 := ⟨fuel - 2, by simp only [List.length_cons] at hfuel; omega⟩
    have hfr : 2 * rest.length + 1 ≤ fr := by simp only [List.length_cons] at hfuel; omega
    obtain ⟨preOps', tailOps', vF, psF, hgenR⟩ := ih fr (bb.label :: visited) ps' hfr hchain'
    have hstep := generateFnPlanAux_single_succ_step hvis hfind hsucc hblock hgenR
    refine ⟨block ++ preOps', tailOps', vF, { ps' with alloc := psF.alloc, labelCounter := psF.labelCounter }, ?_⟩
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    rw [hstep]; simp only [List.append_assoc]

/-- **Whole-function chain-segment decomposition.** For a target reached via a JMP chain whose head is
    the entry block, the *whole-function* plan `ops` decomposes as `preOps ++ tgtBlockOps ++ tailOps` —
    so the target's plan sits at `pc = (executePlan preOps).length`. This is the layout fact a non-entry
    block sim needs, now for an arbitrary-length JMP chain (not just the 2-block base case). -/
theorem generateFnPlanFuel_chain_segment {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {tgtLbl : String} {tgtBlockOps : List StackOp} {tgtPs' : PlanState}
    {path : List BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hentry : fn.blocks.head? = some entry)
    (hpathhead : (path.head?.map (·.label)).getD tgtLbl = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      tgtLbl tgtBlockOps tgtPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ preOps tailOps, ops = preOps ++ tgtBlockOps ++ tailOps := by
  obtain ⟨preOps, tailOps, vF, psF, hgenAux⟩ :=
    generateFnPlanAux_chain_segment hfn path fuel [] { initPlanState fnEom with labelCounter := lblCtr } hfuel hchain
  rw [hpathhead] at hgenAux
  rw [show generateFnPlanFuel fuel fn fnEom lblCtr = some (preOps ++ tgtBlockOps ++ tailOps, psF) from by
    simp only [generateFnPlanFuel, entryBlock, hentry, Option.map_some, hgenAux]] at hgen
  simp only [Option.some.injEq, Prod.mk.injEq] at hgen
  exact ⟨preOps, tailOps, hgen.1.symm⟩


/-- **Linear single-successor spec.** `LinSucc C tgtLbl path` says each block in `path` (head-first) has
    the *next* block (or `tgtLbl`) as its single CFG successor — the successor half of a JMP chain,
    matching `JmpChainTo`'s per-step condition. -/
def LinSucc (C : CfgAnalysis) (tgtLbl : String) : List BasicBlock → Prop
  | [] => True
  | bb :: rest => C.succsOf bb.label = [(rest.head?.map (·.label)).getD tgtLbl] ∧ LinSucc C tgtLbl rest

/-- **`JmpChainTo` constructor (supply from a linear chain).** For a codegen-ready function, a linear
    single-successor chain `path` to `tgtLbl` — every block found, the successor spec `LinSucc`, the
    chain fresh w.r.t. `visited` and internally distinct — yields a `JmpChainTo` witness (with the block
    plans threaded by `generateBlockPlan`). This is what feeds `generateFnPlanFuel_chain_segment` (layout)
    and `psOfFn_chain` (canonical `psOf`) for a walk-reached block. -/
theorem jmpChainTo_of_chain {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {fn : IrFunction} {tgtLbl : String}
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) :
    ∀ (path : List BasicBlock) (visited : List String) (ps : PlanState),
      (∀ b ∈ path, fn.blocks.find? (·.label == b.label) = some b) →
      (fn.blocks.find? (·.label == tgtLbl)).isSome →
      LinSucc C tgtLbl path →
      (∀ b ∈ path, visited.contains b.label = false) →
      visited.contains tgtLbl = false →
      ((path.map (·.label)) ++ [tgtLbl]).Nodup →
      ∃ tgtBlockOps tgtPs', JmpChainTo L D C fn tgtLbl tgtBlockOps tgtPs' path visited ps := by
  intro path
  induction path with
  | nil =>
    intro visited ps _ htgt _ _ hvistgt _
    simp only [JmpChainTo]
    obtain ⟨tgtBB, hfindtgt⟩ := Option.isSome_iff_exists.mp htgt
    have hready := hfn tgtBB (List.mem_of_find?_eq_some hfindtgt)
    obtain ⟨⟨tgtBlockOps, tgtPs'⟩, hbp⟩ :=
      Option.isSome_iff_exists.mp (generateBlockPlan_isSome L D C fn tgtBB ps hready)
    exact ⟨tgtBlockOps, tgtPs', hvistgt, tgtBB, hfindtgt, hbp⟩
  | cons bb rest ih =>
    intro visited ps hfound htgt hsucc hfresh hvistgt hnodup
    have hbbfound : fn.blocks.find? (·.label == bb.label) = some bb := hfound bb List.mem_cons_self
    obtain ⟨hbbsucc, hsuccrest⟩ := hsucc
    have hready := hfn bb (List.mem_of_find?_eq_some hbbfound)
    obtain ⟨⟨block, ps'⟩, hbp⟩ :=
      Option.isSome_iff_exists.mp (generateBlockPlan_isSome L D C fn bb ps hready)
    -- Nodup split: bb.label ∉ rest.map ++ [tgtLbl], and the tail is Nodup.
    have hnc : (bb.label :: (rest.map (·.label) ++ [tgtLbl])).Nodup := by simpa using hnodup
    obtain ⟨hbbnotin, hnodup'⟩ := List.nodup_cons.mp hnc
    have hbbne : ∀ x ∈ rest.map (·.label) ++ [tgtLbl], (x == bb.label) = false := by
      intro x hx; rw [beq_eq_false_iff_ne]; intro h; exact hbbnotin (h ▸ hx)
    obtain ⟨tgtBlockOps, tgtPs', hrec⟩ := ih (bb.label :: visited) ps'
      (fun b hb => hfound b (List.mem_cons_of_mem _ hb)) htgt hsuccrest
      (by
        intro b hb
        simp only [List.contains_cons, Bool.or_eq_false_iff]
        exact ⟨hbbne b.label (List.mem_append_left _ (List.mem_map_of_mem hb)),
               hfresh b (List.mem_cons_of_mem _ hb)⟩)
      (by
        simp only [List.contains_cons, Bool.or_eq_false_iff]
        exact ⟨hbbne tgtLbl (List.mem_append_right _ List.mem_cons_self), hvistgt⟩)
      hnodup'
    have hbbfresh : visited.contains bb.label = false := hfresh bb List.mem_cons_self
    exact ⟨tgtBlockOps, tgtPs', by
      simp only [JmpChainTo]
      exact ⟨hbbfresh, hbbfound, hbbsucc, block, ps', hbp, hrec⟩⟩


/-- **A block plan starts with the block's `SOLabel` (its JUMPDEST).** `generateBlockPlan` prepends
    `labelOp = [SOLabel bb.label]` to the param/clean/instruction ops, so the output begins with
    `SOLabel bb.label`. -/
theorem generateBlockPlan_head {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {fn : IrFunction} {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    (h : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ tl, blockOps = StackOp.SOLabel bb.label :: tl := by
  rw [generateBlockPlan] at h
  dsimp only at h
  repeat' first
    | split at h
    | simp only [reduceCtorEq] at h
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩)

end EvmYul.Venom.Hol.Codegen

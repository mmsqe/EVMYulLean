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

end EvmYul.Venom.Hol.Codegen

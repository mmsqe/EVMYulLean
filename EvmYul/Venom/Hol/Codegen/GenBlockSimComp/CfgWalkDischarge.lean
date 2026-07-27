/-
GenBlockSimComp / CfgWalk / the hpreuniq/hoff/hwdec/hlblfree discharges & the universal DFS plan decomposition

Sub-split of `GenBlockSimComp/CfgWalk` (phase 6, the CFG walk); see `GenBlockSimComp`'s
header for the full roadmap. Continues the `EvmYul.Venom.Hol.Codegen` namespace and imports the previous
part — layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.CfgWalkLayout

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ### Discharging `hpreuniq` — the plan-prefix label-uniqueness obligation

Every canonical per-block `hstep` takes `hpreuniq` as an INPUT: for every decomposition of the whole
function plan as `ops = preOps ++ blockOps ++ tailOps`, the prefix must not already emit the block's own
`AsmLabel` (otherwise `pcOfLabel` — which finds the FIRST occurrence — would point before the block).
Quantified over all decompositions it is awkward to prove directly. But it follows from a single *count*:
the whole plan emits `AsmLabel bb.label` exactly once. That count is COMPUTABLE, so a concrete function
discharges it by `rfl`/`decide`, and in general it is the (true) statement that the DFS visits each block
once and fresh labels never collide with block labels. -/

/-- How many times a resolved plan emits `AsmLabel l`. Uses `countP` (not `count`) because `AsmInst` has
    no `DecidableEq`; the predicate is decidable via `String`'s `BEq`. -/
def asmLabelCount (l : String) (asm : List AsmInst) : Nat :=
  asm.countP (fun a => match a with | AsmInst.AsmLabel m => m == l | _ => false)

theorem asmLabelCount_append (l : String) (a b : List AsmInst) :
    asmLabelCount l (a ++ b) = asmLabelCount l a + asmLabelCount l b := by
  unfold asmLabelCount; exact List.countP_append ..

theorem asmLabelCount_eq_zero (l : String) (asm : List AsmInst) (h : asmLabelCount l asm = 0) :
    ∀ a ∈ asm, a ≠ AsmInst.AsmLabel l := by
  intro a ha hcontra
  have := (List.countP_eq_zero).mp h a ha
  rw [hcontra] at this
  simp at this

/-- A block plan starts with its own label, so its asm emits that label once more than its tail. -/
theorem asmLabelCount_executePlan_label (l : String) (rest : List StackOp) :
    asmLabelCount l (executePlan (StackOp.SOLabel l :: rest))
      = 1 + asmLabelCount l (executePlan rest) := by
  have hcons : (StackOp.SOLabel l :: rest) = [StackOp.SOLabel l] ++ rest := rfl
  rw [hcons, executePlan_append, asmLabelCount_append]
  congr 1
  simp [asmLabelCount, executePlan, execStackOp]

/-- The asm-level label count is just the plan-level count of `SOLabel l` — `execStackOp` emits an
    `AsmLabel` for `SOLabel` and for nothing else. So the whole obligation lives at the plan level. -/
def planLabelCount (l : String) (ops : List StackOp) : Nat :=
  ops.countP (fun o => match o with | StackOp.SOLabel m => m == l | _ => false)

theorem asmLabelCount_execStackOp (l : String) (o : StackOp) :
    asmLabelCount l (execStackOp o)
      = (if (match o with | StackOp.SOLabel m => m == l | _ => false) then 1 else 0) := by
  cases o with
  | SOPush op => cases op <;> simp [asmLabelCount, execStackOp]
  | SOPop n => simp [asmLabelCount, execStackOp, List.countP_eq_zero, List.mem_replicate]
  | SOSwap n => simp [asmLabelCount, execStackOp]
  | SODup n => simp [asmLabelCount, execStackOp]
  | SOPoke a b => simp [asmLabelCount, execStackOp]
  | SOSpill off => simp [asmLabelCount, execStackOp]
  | SORestore off => simp [asmLabelCount, execStackOp]
  | SOEmit opc => simp [asmLabelCount, execStackOp]
  | SOLabel m => simp [asmLabelCount, execStackOp]
  | SOPushLabel m => simp [asmLabelCount, execStackOp]
  | SOPushOfst m off => simp [asmLabelCount, execStackOp]

theorem asmLabelCount_executePlan (l : String) (ops : List StackOp) :
    asmLabelCount l (executePlan ops) = planLabelCount l ops := by
  induction ops with
  | nil => rfl
  | cons o rest ih =>
    show asmLabelCount l (executePlan ([o] ++ rest)) = planLabelCount l (o :: rest)
    rw [executePlan_append, asmLabelCount_append, ih]
    have h1 : executePlan [o] = execStackOp o := by simp [executePlan]
    rw [h1, asmLabelCount_execStackOp]
    unfold planLabelCount
    rw [List.countP_cons]
    exact Nat.add_comm _ _

theorem planLabelCount_append (l : String) (a b : List StackOp) :
    planLabelCount l (a ++ b) = planLabelCount l a + planLabelCount l b := by
  unfold planLabelCount; exact List.countP_append ..

/-- A `SOLabel`-free plan contributes nothing to any label's count. -/
theorem planLabelCount_eq_zero (l : String) (ops : List StackOp)
    (h : ∀ so ∈ ops, ∀ m, so ≠ StackOp.SOLabel m) : planLabelCount l ops = 0 := by
  unfold planLabelCount
  rw [List.countP_eq_zero]
  intro a ha
  cases a <;> first | exact absurd rfl (h _ ha _) | simp

theorem planLabelCount_soLabel (l m : String) :
    planLabelCount l [StackOp.SOLabel m] = if m == l then 1 else 0 := by
  simp [planLabelCount, List.countP_cons]

/-- Membership-aware `foldl` invariant (the step may use `x ∈ l`). -/
theorem foldl_invariant_mem {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ acc x, x ∈ l → P acc → P (f acc x)) → P (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb _; exact hb
  | cons hd tl ih =>
    intro b hb hf
    exact ih (f b hd) (hf b hd (List.mem_cons_self ..) hb)
      (fun acc x hx hacc => hf acc x (List.mem_cons_of_mem hd hx) hacc)

/-- **A block plan emits its own label exactly once, and no other.** The leading `SOLabel bb.label` is
    the only one: the param/clean prefixes and every per-instruction plan are `SOLabel`-free, provided no
    instruction is one of the three fresh-label minters (INVOKE / ASSERT_UNREACHABLE / DJMP). -/
theorem generateBlockPlan_planLabelCount (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (bb : BasicBlock) (ps : PlanState)
    {blockOps : List StackOp} {ps' : PlanState}
    (hgood : ∀ inst ∈ nonParamInsts bb, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) (l : String) :
    planLabelCount l blockOps = if bb.label == l then 1 else 0 := by
  unfold generateBlockPlan at hplan
  simp only [] at hplan
  split at hplan
  · exact absurd hplan (by simp)
  · rename_i instOps ps3 hres
    simp only [Option.some.injEq, Prod.ext_iff] at hplan
    obtain ⟨rfl, -⟩ := hplan
    -- the instruction fold's ops carry no SOLabel
    have hinst : ∀ so ∈ instOps, ∀ m, so ≠ StackOp.SOLabel m := by
      refine foldl_invariant_mem
        (fun acc : Option (List StackOp × PlanState) =>
          ∀ oo pp, acc = some (oo, pp) → ∀ so ∈ oo, ∀ m, so ≠ StackOp.SOLabel m)
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
            have hmem : inst ∈ nonParamInsts bb := List.fst_mem_of_mem_zipIdx hx
            obtain ⟨h1, h2, h3⟩ := hgood inst hmem
            rcases hso with h | h
            · exact hacc aops aps rfl so h
            · exact generateInstPlan_no_soLabel _ _ _ _ _ _ _ _ _ _ h1 h2 h3 hgen so h
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
        planLabelCount_eq_zero l _ hclean, planLabelCount_eq_zero l _ hinst]
    simp

/-- **The whole function plan emits each block label AT MOST ONCE.** The DFS plans a block only when it
    is unvisited and then marks it visited, so no label can be planted twice. Mutual induction on fuel over
    `generateFnPlanAux` / `generateSuccsPlan`, carrying a 4-way invariant:
      (a) already-visited ⇒ this call emits the label 0 times,
      (b) this call emits it at most once,
      (c) if it emitted it, the label is in the output visited-set,
      (d) visited-monotonicity (the DFS only ever adds).
    (c) is the load-bearing one: it is what makes the `rest` recursion contribute 0 after a successor
    subtree has already emitted the label. Requires no instruction to be a fresh-label minter
    (INVOKE / ASSERT_UNREACHABLE / DJMP), since those are the only other `SOLabel` sources. -/
theorem generateFnPlan_planLabelCount (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction)
    (hgood : ∀ bb ∈ fn.blocks, ∀ inst ∈ nonParamInsts bb, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (ps : PlanState) (ops : List StackOp)
       (v' : List String) (ps' : PlanState),
      generateFnPlanAux fuel L D C fn worklist visited ps = some (ops, v', ps') →
      ∀ l, (visited.contains l = true → planLabelCount l ops = 0)
         ∧ planLabelCount l ops ≤ 1
         ∧ (1 ≤ planLabelCount l ops → v'.contains l = true)
         ∧ (visited.contains l = true → v'.contains l = true))
    ∧
    (∀ (ss : List Operand) (sp : SpilledMap) (succs visited : List String) (psG : PlanState)
       (ops : List StackOp) (v' : List String) (ps' : PlanState),
      generateSuccsPlan fuel L D C fn ss sp succs visited psG = some (ops, v', ps') →
      ∀ l, (visited.contains l = true → planLabelCount l ops = 0)
         ∧ planLabelCount l ops ≤ 1
         ∧ (1 ≤ planLabelCount l ops → v'.contains l = true)
         ∧ (visited.contains l = true → v'.contains l = true)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun worklist visited ps ops v' ps' h l => ?_,
            fun ss sp succs visited psG ops v' ps' h l => ?_⟩
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
    refine ⟨fun worklist visited ps ops v' ps' h l => ?_,
            fun ss sp succs visited psG ops v' ps' h l => ?_⟩
    · cases worklist with
      | nil =>
        rw [generateFnPlanAux] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨fun _ => rfl, by simp [planLabelCount], by simp [planLabelCount], fun hv => hv⟩
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [generateFnPlanAux_skip_visited _ _ _ _ _ _ _ _ _ hvis] at h
          exact ihA rest visited ps ops v' ps' h l
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfind : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [generateFnPlanAux_find_none _ _ _ _ _ _ _ _ _ hvisf hfind] at h
            obtain ⟨hA, hB, hCc, hD⟩ := ihA rest (lbl :: visited) ps ops v' ps' h l
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
                  have hcB := generateBlockPlan_planLabelCount L D C fn bb ps (hgood bb hmemb) hbp l
                  rw [hlbl] at hcB
                  obtain ⟨hSa, hSb, hSc, hSd⟩ :=
                    ihS psB.stack psB.spilled (C.succsOf lbl) (lbl :: visited) psB succOps v2 ps2
                      hsucc l
                  obtain ⟨hRa, hRb, hRc, hRd⟩ := ihA rest v2 ps2 restOps vF psF hrest l
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
              ihA [succ] visited { psG with stack := ss, spilled := sp } sOps vAfter psAfter hga l
            have psG' : PlanState :=
              { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
            obtain ⟨hRa, hRb, hRc, hRd⟩ :=
              ihS ss sp rest vAfter _ restOps vF psF hgs l
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

/-- **`hpreuniq`, from a count.** If the whole function plan emits the block's label AT MOST once, then no
    decomposition can put that label in the prefix — which is exactly the `hpreuniq` every canonical
    `hstep` asks for. Reduces an awkward ∀-over-decompositions obligation to a count. -/
theorem hpreuniq_of_asmLabelCount_one {ops blockOps rest : List StackOp} {l : String}
    (hblk : blockOps = StackOp.SOLabel l :: rest)
    (hcount : asmLabelCount l (executePlan ops) ≤ 1) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel l := by
  intro preOps tailOps hseg a ha
  have hsplit : asmLabelCount l (executePlan ops)
      = asmLabelCount l (executePlan preOps)
        + (1 + asmLabelCount l (executePlan rest))
        + asmLabelCount l (executePlan tailOps) := by
    rw [hseg, hblk, executePlan_append, executePlan_append, asmLabelCount_append,
        asmLabelCount_append, asmLabelCount_executePlan_label]
  have hzero : asmLabelCount l (executePlan preOps) = 0 := by omega
  exact asmLabelCount_eq_zero l _ hzero a ha

/-- **The whole-function plan emits each label at most once.** Entry point of the DFS count. -/
theorem generateFnPlanFuel_planLabelCount {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {ops : List StackOp} {ps : PlanState}
    (hgood : ∀ bb ∈ fn.blocks, ∀ inst ∈ nonParamInsts bb, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) (l : String) :
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
      exact ((generateFnPlan_planLabelCount (livenessAnalyzeFuel fuel fn)
        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn hgood fuel).1
        _ [] _ _ _ _ haux l).2.1

/-- Every block plan starts with the block's own label — the shape `hpreuniq_generic` needs. -/
theorem generateBlockPlan_head_label (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) {blockOps : List StackOp} {ps' : PlanState}
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ rest, blockOps = StackOp.SOLabel bb.label :: rest := by
  unfold generateBlockPlan at hplan
  simp only [] at hplan
  split at hplan
  · exact absurd hplan (by simp)
  · rename_i instOps ps3 hres
    simp only [Option.some.injEq, Prod.ext_iff] at hplan
    obtain ⟨rfl, -⟩ := hplan
    exact ⟨_, rfl⟩

/-- **`hpreuniq`, DISCHARGED GENERICALLY.** For any function whose instructions include none of the three
    fresh-label minters (INVOKE / ASSERT_UNREACHABLE / DJMP), the plan-prefix label-uniqueness obligation
    that every canonical per-block `hstep` takes as an input is a THEOREM. Chain: the DFS plans a block
    only when unvisited (`generateFnPlan_planLabelCount`) ⇒ the plan emits each label at most once ⇒
    (`asmLabelCount_executePlan`) the assembly does too ⇒ (`hpreuniq_of_asmLabelCount_one`) no
    decomposition can put the label in the prefix. -/
theorem hpreuniq_generic {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {ops blockOps rest : List StackOp} {ps : PlanState} {bb : BasicBlock}
    (hgood : ∀ b ∈ fn.blocks, ∀ inst ∈ nonParamInsts b, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hblk : blockOps = StackOp.SOLabel bb.label :: rest) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label :=
  hpreuniq_of_asmLabelCount_one hblk
    (by rw [asmLabelCount_executePlan]
        exact generateFnPlanFuel_planLabelCount hgood hgen bb.label)

/-- **`hpreuniq` in the form a caller actually has it**: it holds `hgen` (the whole-function plan) and
    `hbp` (this block's plan), and wants `hpreuniq` for this block. One-liner discharge. -/
theorem hpreuniq_of_blockPlan {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hgood : ∀ b ∈ fn.blocks, ∀ inst ∈ nonParamInsts b, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps')) :
    ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  exact hpreuniq_generic hgood hgen hrest

/-! ### Discharging the jump-target lookup (`hoff_lk`)

`hoff_lk` asserts the target label HAS a byte offset in the resolved program. `computeLabelOffsets`
inserts an entry for every `AsmLabel`, and `computeLabelOffsets_lookup` already turns a decomposition
`pre ++ AsmLabel lbl :: suf` (with `lbl` absent from `suf`) into the offset. Both halves are now available:
the block plan starts with its own `SOLabel` (`generateBlockPlan_head_label`), and the plan emits each
label at most once (`generateFnPlanFuel_planLabelCount`), which is exactly the absent-from-`suf` side
condition. -/

/-- A compiled plan never contains a data-section header. -/
theorem executePlan_no_dataHeader (ops : List StackOp) :
    ∀ a ∈ executePlan ops, ∀ l, a ≠ AsmInst.AsmDataHeader l := by
  intro a ha l hc
  subst hc
  induction ops with
  | nil => simp [executePlan] at ha
  | cons o rest ih =>
    have hcons : (o :: rest) = [o] ++ rest := rfl
    rw [hcons, executePlan_append, List.mem_append] at ha
    rcases ha with h | h
    · have h1 : executePlan [o] = execStackOp o := by simp [executePlan]
      rw [h1] at h
      cases o with
      | SOPush op => cases op <;> simp [execStackOp] at h
      | SOPop n => simp [execStackOp, List.mem_replicate] at h
      | _ => simp [execStackOp] at h
    · exact ih h

/-- **The target label's byte offset exists.** From a plan segment whose middle is the target block's
    plan (which starts with its own `SOLabel`) and the at-most-once label count. -/
theorem labelOffset_of_plan {ops pre blockOps rest suf : List StackOp} {lbl : String}
    (hseg : ops = pre ++ blockOps ++ suf)
    (hblk : blockOps = StackOp.SOLabel lbl :: rest)
    (hcount : planLabelCount lbl ops ≤ 1) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan ops)).2 lbl
      = some (((executePlan pre).map asmInstSize).sum) := by
  have hasm : executePlan ops
      = executePlan pre ++ AsmInst.AsmLabel lbl :: (executePlan rest ++ executePlan suf) := by
    rw [hseg, hblk, executePlan_append, executePlan_append]
    have h1 : executePlan (StackOp.SOLabel lbl :: rest)
        = AsmInst.AsmLabel lbl :: executePlan rest := by
      have hcons : (StackOp.SOLabel lbl :: rest) = [StackOp.SOLabel lbl] ++ rest := rfl
      rw [hcons, executePlan_append]
      rfl
    rw [h1]
    simp
  -- the label appears nowhere after the block's own marker
  have hzero : asmLabelCount lbl (executePlan rest ++ executePlan suf) = 0 := by
    have hsplit : asmLabelCount lbl (executePlan ops)
        = asmLabelCount lbl (executePlan pre)
          + (1 + asmLabelCount lbl (executePlan rest ++ executePlan suf)) := by
      rw [hasm, asmLabelCount_append]
      congr 1
      have hcons2 : (AsmInst.AsmLabel lbl :: (executePlan rest ++ executePlan suf))
          = [AsmInst.AsmLabel lbl] ++ (executePlan rest ++ executePlan suf) := rfl
      rw [hcons2, asmLabelCount_append]
      simp [asmLabelCount]
    rw [asmLabelCount_executePlan] at hsplit
    omega
  rw [hasm]
  refine computeLabelOffsets_lookup _ _ _ (fun inst hinst => ⟨?_, ?_⟩)
  · exact asmLabelCount_eq_zero lbl _ hzero inst hinst
  · rw [List.mem_append] at hinst
    rcases hinst with h | h
    · exact executePlan_no_dataHeader rest inst h lbl
    · exact executePlan_no_dataHeader suf inst h lbl

/-- **`hoff_lk`, DISCHARGED.** The form a caller has: the whole-function plan (`hgen`), the target
    block's plan (`hbp`), and a segment placing it inside the whole plan (`hseg`) — which is exactly what
    the placement lemmas (`generateFnPlanFuel_chain_segment` / `_first_succ_segment`) produce. The byte
    offset then exists, and is the prefix's encoded size. -/
theorem labelOffset_of_blockPlan {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops pre suf blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hgood : ∀ b ∈ fn.blocks, ∀ inst ∈ nonParamInsts b, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps'))
    (hseg : ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan ops)).2 bb.label
      = some (((executePlan pre).map asmInstSize).sum) := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  exact labelOffset_of_plan hseg hrest (generateFnPlanFuel_planLabelCount hgood hgen bb.label)

/-- `resolveInst` rewrites only the two push forms; an `AsmLabel` passes through. -/
theorem resolveInst_asmLabel (offsets : AssocList String Nat) (l : String) :
    resolveInst offsets (AsmInst.AsmLabel l) = AsmInst.AsmLabel l := rfl

/-- …and nothing else resolves TO an `AsmLabel`, so label positions are exactly preserved. -/
theorem eq_asmLabel_of_resolveInst {offsets : AssocList String Nat} {x : AsmInst} {l : String}
    (h : resolveInst offsets x = AsmInst.AsmLabel l) : x = AsmInst.AsmLabel l := by
  cases x <;> simp_all [resolveInst] <;> split at h <;> simp_all

/-- **`hidx_lk` + `hidxeq`, DISCHARGED.** The `offsetToPc` entry for the target's byte offset is its
    instruction index, and that index IS `pcOfLabel` of the resolved program. Note `buildOffsetToPc_lookup`
    needs no side condition at all; `pcOfLabel_of_decomp` needs "no `AsmLabel` in the prefix", which is
    exactly `hpreuniq` — now a theorem. -/
theorem idxOfLabel_of_plan {ops pre blockOps rest suf : List StackOp} {lbl : String}
    (hseg : ops = pre ++ blockOps ++ suf)
    (hblk : blockOps = StackOp.SOLabel lbl :: rest)
    (hcount : planLabelCount lbl ops ≤ 1) :
    AssocList.lookup Nat Nat (asmResolve (executePlan ops)).2
        (((executePlan pre).map asmInstSize).sum) = some (executePlan pre).length
      ∧ pcOfLabel (asmResolve (executePlan ops)).1 lbl = (executePlan pre).length := by
  have hasm : executePlan ops
      = executePlan pre ++ AsmInst.AsmLabel lbl :: (executePlan rest ++ executePlan suf) := by
    rw [hseg, hblk, executePlan_append, executePlan_append]
    have h1 : executePlan (StackOp.SOLabel lbl :: rest)
        = AsmInst.AsmLabel lbl :: executePlan rest := by
      have hcons : (StackOp.SOLabel lbl :: rest) = [StackOp.SOLabel lbl] ++ rest := rfl
      rw [hcons, executePlan_append]; rfl
    rw [h1]; simp
  -- the prefix has no occurrence of the label (this is `hpreuniq`)
  have hpre : ∀ x ∈ executePlan pre, x ≠ AsmInst.AsmLabel lbl := by
    have hsplit : asmLabelCount lbl (executePlan ops)
        = asmLabelCount lbl (executePlan pre)
          + (1 + asmLabelCount lbl (executePlan rest ++ executePlan suf)) := by
      rw [hasm, asmLabelCount_append]
      congr 1
      have hcons2 : (AsmInst.AsmLabel lbl :: (executePlan rest ++ executePlan suf))
          = [AsmInst.AsmLabel lbl] ++ (executePlan rest ++ executePlan suf) := rfl
      rw [hcons2, asmLabelCount_append]
      simp [asmLabelCount]
    rw [asmLabelCount_executePlan] at hsplit
    exact asmLabelCount_eq_zero lbl _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [asmResolve_snd, hasm]
    exact buildOffsetToPc_lookup _ _ _
  · rw [asmResolve_fst, hasm]
    simp only [List.map_append, List.map_cons, resolveInst_asmLabel]
    rw [pcOfLabel_of_decomp _ _ _ (fun x hx hc => ?_), List.length_map]
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hpre y hy (eq_asmLabel_of_resolveInst hc)

/-- **The jump-target family, in the form a caller has it.** From the whole-function plan (`hgen`), the
    target block's plan (`hbp`), and its placement (`hseg`) — all three of which the existing machinery
    already produces — the target's byte offset, its `offsetToPc` index, and `pcOfLabel` all follow. That
    is `hoff_lk`, `hidx_lk` and `hidxeq` together. -/
theorem jumpTarget_of_blockPlan {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis}
    {ops pre suf blockOps : List StackOp} {ps psB ps' : PlanState} {bb : BasicBlock}
    (hgood : ∀ b ∈ fn.blocks, ∀ inst ∈ nonParamInsts b, inst.opcode ≠ Opcode.INVOKE ∧
      inst.opcode ≠ Opcode.ASSERT_UNREACHABLE ∧ inst.opcode ≠ Opcode.DJMP)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hbp : generateBlockPlan L D C fn bb psB = some (blockOps, ps'))
    (hseg : ops = pre ++ blockOps ++ suf) :
    AssocList.lookup String Nat (computeLabelOffsets (executePlan ops)).2 bb.label
        = some (((executePlan pre).map asmInstSize).sum) ∧
    AssocList.lookup Nat Nat (asmResolve (executePlan ops)).2
        (((executePlan pre).map asmInstSize).sum) = some (executePlan pre).length ∧
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan pre).length := by
  obtain ⟨rest, hrest⟩ := generateBlockPlan_head_label L D C fn bb psB hbp
  have hcount := generateFnPlanFuel_planLabelCount hgood hgen bb.label
  obtain ⟨h2, h3⟩ := idxOfLabel_of_plan hseg hrest hcount
  exact ⟨labelOffset_of_plan hseg hrest hcount, h2, h3⟩

/-! ### Discharging the forward-edge ranking (`hwdec`)

`hwdec` is the well-foundedness fact the whole-function walk needs: the successor's remaining-work
measure plus this block's own length does not exceed this block's measure. With `wOf l := prog.length −
pcOfLabel prog l` and the DFS laying a block's successor plan IMMEDIATELY after it, this is not an
inequality to be assumed — it holds with EQUALITY, and the proof is pure `pcOfLabel` arithmetic, which is
now available (`idxOfLabel_of_plan`). This is exactly the piece loops will have to replace, since a
back-edge's target sits BEFORE the block. -/

/-- **`hwdec`, DISCHARGED for a forward edge.** Given the plan places the successor's block right after
    this one, `wOf succ + |this block's asm| = wOf bb` exactly. -/
theorem wdec_of_segment {ops pre blockOps succBlockOps suf rest srest : List StackOp}
    {bb succBB : BasicBlock}
    (hseg : ops = pre ++ blockOps ++ (succBlockOps ++ suf))
    (hblk : blockOps = StackOp.SOLabel bb.label :: rest)
    (hsblk : succBlockOps = StackOp.SOLabel succBB.label :: srest)
    (hc : planLabelCount bb.label ops ≤ 1)
    (hc' : planLabelCount succBB.label ops ≤ 1) :
    ((asmResolve (executePlan ops)).1.length
        - pcOfLabel (asmResolve (executePlan ops)).1 succBB.label)
      + (executePlan blockOps).length
    ≤ (asmResolve (executePlan ops)).1.length
        - pcOfLabel (asmResolve (executePlan ops)).1 bb.label := by
  -- this block sits at |executePlan pre|
  obtain ⟨-, hpcbb⟩ := idxOfLabel_of_plan hseg hblk hc
  -- the successor's block sits right after it
  have hseg' : ops = (pre ++ blockOps) ++ succBlockOps ++ suf := by rw [hseg]; simp
  obtain ⟨-, hpcsucc⟩ := idxOfLabel_of_plan hseg' hsblk hc'
  rw [executePlan_append, List.length_append] at hpcsucc
  -- the program is at least as long as the prefix through this block
  have hlen : (asmResolve (executePlan ops)).1.length
      = (executePlan pre).length + (executePlan blockOps).length
        + ((executePlan succBlockOps).length + (executePlan suf).length) := by
    rw [asmResolve_length, hseg, executePlan_append, executePlan_append, executePlan_append]
    simp [List.length_append]
    omega
  rw [hpcbb, hpcsucc, hlen]
  omega

/-- **`hoff`, DISCHARGED** (modulo the program fitting in the EVM address space, which is the natural
    caller obligation): a label's byte offset is a prefix sum, hence at most the whole program's encoded
    size. -/
theorem labelOffset_lt_of_total {ops pre suf blockOps : List StackOp} {bound : Nat}
    (hseg : ops = pre ++ blockOps ++ suf)
    (hbound : ((executePlan ops).map asmInstSize).sum < bound) :
    ((executePlan pre).map asmInstSize).sum < bound := by
  rw [hseg, executePlan_append, executePlan_append, List.map_append, List.map_append,
      List.sum_append, List.sum_append] at hbound
  omega

/-! ### Discharging `hlblfree` — the body's asm carries no label push

The other never-discharged `hstep` input. `AsmPushLabel`/`AsmPushOfst` arise only from
`SOPushLabel` / `SOPushOfst` / `SOPush (Operand.Label _)` (`executePlan_no_label`), and among the plan
operations only `generateEmitOps` emits those — for JMP / JNZ / DJMP / INVOKE / ASSERT /
ASSERT_UNREACHABLE. A *body* instruction is a non-terminator, which already excludes JMP / JNZ / DJMP;
the other three plus "operands carry no label" are the side conditions. -/

/-- The body-fold's ops are label-push-free. -/
theorem bodyfold_no_label (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (front : List Instruction) (ps0 : PlanState)
    {bodyOps : List StackOp} {ps_body : PlanState}
    (hcond : ∀ x ∈ front.zipIdx 0,
      (∀ op ∈ computeOperands x.1, ∀ l, op ≠ Operand.Label l) ∧
      (¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧ x.1.opcode ≠ Opcode.OFFSET ∧
        x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) ∧
      x.1.opcode ≠ Opcode.JMP ∧ x.1.opcode ≠ Opcode.JNZ ∧ x.1.opcode ≠ Opcode.DJMP ∧
      x.1.opcode ≠ Opcode.INVOKE ∧ x.1.opcode ≠ Opcode.ASSERT ∧
      x.1.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (hfold : (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps0))
      = some (bodyOps, ps_body)) :
    ∀ so ∈ bodyOps, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  refine foldl_invariant_mem
    (fun acc : Option (List StackOp × PlanState) =>
      ∀ oo pp, acc = some (oo, pp) →
        ∀ so ∈ oo, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
          ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)))
    _ _ _ ?_ ?_ bodyOps ps_body hfold
  · intro oo pp h
    simp only [Option.some.injEq, Prod.ext_iff] at h
    obtain ⟨rfl, -⟩ := h
    exact fun so hso => absurd hso List.not_mem_nil
  · intro acc x hx hacc oo pp heq so hso
    cases acc with
    | none => simp [instFoldF] at heq
    | some aval =>
      obtain ⟨aops, aps⟩ := aval
      unfold instFoldF at heq
      simp only [] at heq
      split at heq
      · exact absurd heq (by simp)
      · rename_i stepOps aps' hgen
        simp only [Option.some.injEq, Prod.ext_iff] at heq
        obtain ⟨rfl, -⟩ := heq
        rw [List.mem_append] at hso
        obtain ⟨hop, hreg, h1, h2, h3, h4, h5, h6⟩ := hcond x hx
        rcases hso with h | h
        · exact hacc aops aps rfl so h
        · exact generateInstPlan_no_label _ _ _ _ _ _ _ _ _ _ hop hreg h1 h2 h3 h4 h5 h6 hgen so h

/-- **`hlblfree`, DISCHARGED.** The asm of `[SOLabel bb.label] ++ bodyOps` emits no `AsmPushLabel` /
    `AsmPushOfst` — the block's own `SOLabel` compiles to an `AsmLabel` (a jump *destination*, not a push),
    and the body plan is label-push-free. -/
theorem hlblfree_of_bodyfold (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (front : List Instruction) (ps0 : PlanState)
    {bodyOps : List StackOp} {ps_body : PlanState}
    (hcond : ∀ x ∈ front.zipIdx 0,
      (∀ op ∈ computeOperands x.1, ∀ l, op ≠ Operand.Label l) ∧
      (¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧ x.1.opcode ≠ Opcode.OFFSET ∧
        x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) ∧
      x.1.opcode ≠ Opcode.JMP ∧ x.1.opcode ≠ Opcode.JNZ ∧ x.1.opcode ≠ Opcode.DJMP ∧
      x.1.opcode ≠ Opcode.INVOKE ∧ x.1.opcode ≠ Opcode.ASSERT ∧
      x.1.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (hfold : (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps0))
      = some (bodyOps, ps_body)) :
    ∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps),
      (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl) ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) := by
  refine executePlan_no_label _ (fun so hso => ?_)
  rw [List.mem_append] at hso
  rcases hso with h | h
  · simp only [List.mem_singleton] at h
    subst h
    exact ⟨by simp, by simp, by simp⟩
  · exact bodyfold_no_label L D C fn bb front ps0 hcond hfold so h


/-- **Shared placement prefix for the per-block canonical `hstep`s.** From a JMP chain to `bb` and the
    whole-function plan, extracts the segment decomposition (`ops = preOps ++ blockOps ++ tailOps`) and the
    block plan generated at `bb`'s *canonical* `psOfFn` entry state — the identical opening every
    `hstep_regularHSVP_*_canonical` (JMP/STOP/INVALID/RETURN/REVERT/JNZ) shares. Composes
    `generateFnPlanFuel_chain_segment` (segment) + `psOfFn_chain` (canonical block plan) + the
    `find?`-injectivity `tgtBB = bb`. -/
theorem chain_segment_gbp {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb) :
    ∃ preOps tailOps,
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn bb
        (psOfFn fuel fn fnEom lblCtr bb.label) = some (blockOps, ps') := by
  have hhead : fn.blocks.head? = some entry := hentry
  obtain ⟨preOps, tailOps, hseg⟩ :=
    generateFnPlanFuel_chain_segment hhead hpathhead hfuel hfn hchain hgen
  obtain ⟨tgtBB, hfindT, hgbp0⟩ := psOfFn_chain hentry hpathhead hfuel hfn hchain
  have htgt : tgtBB = bb := by rw [hpfind] at hfindT; exact (Option.some.inj hfindT).symm
  rw [htgt] at hgbp0
  exact ⟨preOps, tailOps, hseg, hgbp0⟩

/-- **Chain-reached aligned-JMP block: generateBlockPlan output = body-fold output.** The chain analog
    of `generateBlockPlan_ps'_eq_bodyfold_jmp`: for a block reached from the entry via a JMP chain,
    generated at its own `psOfFn` entry state (`psOfFn_chain`), its `generateBlockPlan` output `tgtPs'`
    equals the body-fold output when the body has no spills. The per-block generation fact for non-entry
    aligned-JMP blocks (the successor-recording `psOfFn succ = pred output` is separate DFS machinery). -/
theorem psOfFn_chain_aligned_jmp_bodyfold
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry tgtBB : BasicBlock} {tgtLbl : String} {tgtBlockOps : List StackOp} {tgtPs' : PlanState}
    {path : List BasicBlock} {front : List Instruction} {term : Instruction} {target : String}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD tgtLbl = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      tgtLbl tgtBlockOps tgtPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hfind : fn.blocks.find? (·.label == tgtLbl) = some tgtBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn tgtBB)
    (hnp : nonParamInsts tgtBB = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom tgtBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = []) :
    ∃ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn tgtBB) (some ([], psOfFn fuel fn fnEom lblCtr tgtLbl)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) → tgtPs' = ps_body) := by
  obtain ⟨tgtBB', hfind', hbp⟩ := psOfFn_chain hentry hpathhead hfuel hfn hchain
  rw [hfind] at hfind'; obtain rfl := Option.some.inj hfind'
  exact generateBlockPlan_ps'_eq_bodyfold_jmp (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn tgtBB (psOfFn fuel fn fnEom lblCtr tgtLbl) tgtBlockOps tgtPs' front term target
    hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hbp

/-- **General non-entry successor-recording residual.** For an aligned-JMP block `pred` reached from
    the entry via a JMP chain (arbitrary depth), with fresh successor `succ`, `psOfFn succ = pred's
    body-fold output`. Composes `dfsEntriesAux_chain_succ_records` (records `succ ↦ pred's exit`),
    `psOfFn_chain` (`generateBlockPlan predBB (psOfFn pred) = (blockOps, predPs')`), and the aligned
    composite (`generateBlockPlan_ps'_eq_bodyfold_jmp`: `predPs' = body-fold`). Closes the residual side
    for all non-entry aligned-JMP blocks. -/
theorem psOfFn_succ_eq_bodyfold_jmp_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction} {target : String}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom predBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) ∧
      psOfFn fuel fn fnEom lblCtr succ = ps_body := by
  have hsome' : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [(path.head?.map (·.label)).getD pred] [] []
      { initPlanState fnEom with labelCounter := lblCtr } = some result := by rw [hpathhead]; exact hsome
  obtain ⟨hrecS, _⟩ := dfsEntriesAux_chain_succ_records hfn path fuel [] [] _ result pred succ succBB
    blockOps predPs' succRest hfuel hchain hpsucc hsfind hsfresh (by simp) hsne hsome'
  have hpsof_succ : psOfFn fuel fn fnEom lblCtr succ = predPs' := by
    unfold psOfFn blockEntryTable
    simp only [hentry, Option.map_some, hsome, hrecS, Option.getD_some]
  obtain ⟨predBB', hpfind', hbp⟩ := psOfFn_chain hentry hpathhead (by omega) hfn hchain
  rw [hpfind] at hpfind'; obtain rfl := Option.some.inj hpfind'
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_ps'_eq_bodyfold_jmp (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn predBB (psOfFn fuel fn fnEom lblCtr pred) blockOps predPs' fr term target
      hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hbp
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hpsof_succ, himp (hnospill bodyOps ps_body hbody)]

/-- **`psOfFn ifNz = body-fold output` for a chain-reached aligned-JNZ block (taken branch).** The JNZ
    analogue of `psOfFn_succ_eq_bodyfold_jmp_general`: the DFS records the *first* successor (`ifNz`) of
    `pred` with `pred`'s exit (`dfsEntriesAux_chain_succ_records` — terminator-agnostic), and
    `generateBlockPlan_ps'_eq_bodyfold_jnz` gives that exit `= body-fold`. So `psOfFn ifNz = body-fold`,
    the JNZ taken scheduling-residual on the real DFS table. (The not-taken branch `ifZ` = second successor
    needs a two-successor recording, still open.) -/
theorem psOfFn_succ_eq_bodyfold_jnz_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred c ifNz ifZ succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) ∧
      psOfFn fuel fn fnEom lblCtr succ = ps_body := by
  have hsome' : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [(path.head?.map (·.label)).getD pred] [] []
      { initPlanState fnEom with labelCounter := lblCtr } = some result := by rw [hpathhead]; exact hsome
  obtain ⟨hrecS, _⟩ := dfsEntriesAux_chain_succ_records hfn path fuel [] [] _ result pred succ succBB
    blockOps predPs' succRest hfuel hchain hpsucc hsfind hsfresh (by simp) hsne hsome'
  have hpsof_succ : psOfFn fuel fn fnEom lblCtr succ = predPs' := by
    unfold psOfFn blockEntryTable
    simp only [hentry, Option.map_some, hsome, hrecS, Option.getD_some]
  obtain ⟨predBB', hpfind', hbp⟩ := psOfFn_chain hentry hpathhead (by omega) hfn hchain
  rw [hpfind] at hpfind'; obtain rfl := Option.some.inj hpfind'
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_ps'_eq_bodyfold_jnz (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn predBB (psOfFn fuel fn fnEom lblCtr pred) blockOps predPs' fr term c ifNz ifZ
      hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS hbp
  refine ⟨bodyOps, ps_body, hbody, ?_⟩
  rw [hpsof_succ, himp (hnospill bodyOps ps_body hbody)]

/-- **The JNZ not-taken (second-successor) join relation on the canonical schedule.** For any
    chain-reached JNZ block `pred` with successors `ifNz :: ifZ :: succRest`, the canonical entry state
    of the *fall-through* target `ifZ` agrees with the block's body-fold output on stack and spilled, and
    its allocator is `AllocInv`-related (fnEom fixed, nextOffset non-decreasing). Unlike the taken branch
    — where `psOfFn ifNz = ps_body` outright (`psOfFn_succ_eq_bodyfold_jnz_general`) — `ifZ`'s allocator
    is the one threaded through `ifNz`'s whole subtree, so only the `AllocInv` relation holds. These four
    facts are exactly `hstep_regularHSVP_jnz_nottaken`'s `hstk`/`hsp`/`hfe`/`hno`. -/
theorem psOfFn_succ2_rel_bodyfold_jnz_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB1 succBB2 : BasicBlock} {pred c ifNz ifZ succ1 succ2 : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 4 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ1 :: succ2 :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == succ1) = some succBB1)
    (hsfind2 : fn.blocks.find? (·.label == succ2) = some succBB2)
    (hsfresh1 : ∀ b ∈ path, b.label ≠ succ1) (hsne1 : succ1 ≠ pred)
    (hsfresh2 : ∀ b ∈ path, b.label ≠ succ2) (hsne2 : succ2 ≠ pred)
    (hnr : ¬ CfgReach (cfgAnalyze fn) succ1 succ2)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) ∧
      ps_body.stack = (psOfFn fuel fn fnEom lblCtr succ2).stack ∧
      ps_body.spilled = (psOfFn fuel fn fnEom lblCtr succ2).spilled ∧
      AllocInv ps_body.alloc (psOfFn fuel fn fnEom lblCtr succ2).alloc := by
  have hsome' : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [(path.head?.map (·.label)).getD pred] [] []
      { initPlanState fnEom with labelCounter := lblCtr } = some result := by rw [hpathhead]; exact hsome
  obtain ⟨psS, hrecS, hstkS, hspS, halloS, _⟩ :=
    dfsEntriesAux_chain_succ2_records hfn path fuel [] [] _ result pred succ1 succ2 succBB1 succBB2
      blockOps predPs' succRest hfuel hchain hpsucc hsfind1 hsfind2 hsfresh1 (by simp) hsne1
      hsfresh2 (by simp) hsne2
      (fun f vis tb r hv hs => dfsEntriesAux_not_reach_fresh (livenessAnalyzeFuel fuel fn)
        (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn f succ1 succ2 vis tb predPs' r hnr hv hs)
      hsome'
  have hpsof_succ2 : psOfFn fuel fn fnEom lblCtr succ2 = psS := by
    unfold psOfFn blockEntryTable
    simp only [hentry, Option.map_some, hsome, hrecS, Option.getD_some]
  obtain ⟨predBB', hpfind', hbp⟩ := psOfFn_chain hentry hpathhead (by omega) hfn hchain
  rw [hpfind] at hpfind'; obtain rfl := Option.some.inj hpfind'
  obtain ⟨bodyOps, ps_body, hbody, himp⟩ :=
    generateBlockPlan_ps'_eq_bodyfold_jnz (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn predBB (psOfFn fuel fn fnEom lblCtr pred) blockOps predPs' fr term c ifNz ifZ
      hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS hbp
  have hpb : predPs' = ps_body := himp (hnospill bodyOps ps_body hbody)
  refine ⟨bodyOps, ps_body, hbody, ?_, ?_, ?_⟩
  · rw [hpsof_succ2, hstkS, hpb]
  · rw [hpsof_succ2, hspS, hpb]
  · rw [hpsof_succ2, ← hpb]; exact halloS

/-- **Canonical-schedule residual for a general aligned-JMP block.** The adapter's positional gp-fold
    output equals `psOfFn succ`, for any chain-reached aligned-JMP block `pred`. Composes
    `psOfFn_succ_eq_bodyfold_jmp_general` (`instFoldF` body-fold = `psOfFn succ`) with `instFoldF_regular_fold`
    (`instFoldF` fold = `some` of the raw positional gp-fold). The four per-block `hstep` residuals
    `hstk/hsp/hfe/hno` are its projections — the JMP residual on the real schedule for ALL blocks. -/
theorem positional_gpfold_eq_psOfFn_succ_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction} {target : String}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom predBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ((fr.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
        let nextLive := if x.2 + 1 < (nonParamInsts predBB).length then
            liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label (x.2 + (getParams predBB.instructions).length + 1)
          else liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length
        let nextIsTerm := if x.2 + 1 < (nonParamInsts predBB).length then
            isTerminator (nonParamInsts predBB)[x.2 + 1]!.opcode else false
        let r := generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn x.1 nextLive (bbIsHalting predBB) nextIsTerm predBB.label acc.2
        (acc.1 ++ r.1, r.2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2
      = psOfFn fuel fn fnEom lblCtr succ := by
  obtain ⟨bodyOps, ps_body, hbody, hpsof⟩ :=
    psOfFn_succ_eq_bodyfold_jmp_general hentry hpathhead hfuel hfn hchain hpsucc hsfind hsfresh hsne
      hsome hpfind hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hnospill
  have hlift := instFoldF_regular_fold (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn predBB (fr.zipIdx 0) (psOfFn fuel fn fnEom lblCtr pred) hreg
  rw [hbody] at hlift
  have hps_body : ps_body = _ := congrArg Prod.snd (Option.some.inj hlift)
  rw [← hps_body, hpsof]

/-- **Adapter `lg`-fold residual on the canonical schedule.** For any chain-reached aligned-JMP block
    `pred`, the per-block adapter's `lg`-fold (with `gp` = the positional `generateRegularInstPlan`
    generator, `lg.map Prod.fst = fr.zipIdx 0`) output equals `psOfFn succ`. Composes `adapter_fold_eq_zipIdx`
    (`lg`-fold = positional `fr.zipIdx` fold) with `positional_gpfold_eq_psOfFn_succ_general`. The four
    `hstep_regularHSVP_jmp` residuals `hstk/hsp/hfe/hno` on the real schedule are its projections. -/
theorem adapter_lgfold_eq_psOfFn_succ_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction} {target : String}
    {lg : List ((Instruction × Nat) × List String)}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom predBB.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hfront : lg.map Prod.fst = fr.zipIdx 0)
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label (y.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length)
          (bbIsHalting predBB)
          (if y.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[y.2 + 1]!.opcode else false)
          predBB.label ps) :
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2
      = psOfFn fuel fn fnEom lblCtr succ := by
  rw [adapter_fold_eq_zipIdx gp lg fr (psOfFn fuel fn fnEom lblCtr pred) hfront, hgp]
  exact positional_gpfold_eq_psOfFn_succ_general hentry hpathhead hfuel hfn hchain hpsucc hsfind
    hsfresh hsne hsome hpfind hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hreg hnospill

/-- **Canonical-schedule residual for a general aligned-JNZ block (taken branch).** The positional gp-fold
    output equals `psOfFn ifNz`. JNZ analogue of `positional_gpfold_eq_psOfFn_succ_general`: composes
    `psOfFn_succ_eq_bodyfold_jnz_general` with `instFoldF_regular_fold`. -/
theorem positional_gpfold_eq_psOfFn_succ_jnz_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred c ifNz ifZ succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ((fr.zipIdx 0).foldl (fun (acc : List StackOp × PlanState) (x : Instruction × Nat) =>
        let nextLive := if x.2 + 1 < (nonParamInsts predBB).length then
            liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label (x.2 + (getParams predBB.instructions).length + 1)
          else liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length
        let nextIsTerm := if x.2 + 1 < (nonParamInsts predBB).length then
            isTerminator (nonParamInsts predBB)[x.2 + 1]!.opcode else false
        let r := generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn x.1 nextLive (bbIsHalting predBB) nextIsTerm predBB.label acc.2
        (acc.1 ++ r.1, r.2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2
      = psOfFn fuel fn fnEom lblCtr succ := by
  obtain ⟨bodyOps, ps_body, hbody, hpsof⟩ :=
    psOfFn_succ_eq_bodyfold_jnz_general hentry hpathhead hfuel hfn hchain hpsucc hsfind hsfresh hsne
      hsome hpfind hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS hnospill
  have hlift := instFoldF_regular_fold (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn predBB (fr.zipIdx 0) (psOfFn fuel fn fnEom lblCtr pred) hreg
  rw [hbody] at hlift
  have hps_body : ps_body = _ := congrArg Prod.snd (Option.some.inj hlift)
  rw [← hps_body, hpsof]

/-- **Adapter `lg`-fold residual on the canonical schedule for an aligned-JNZ block (taken).** The adapter's
    `lg`-fold output equals `psOfFn ifNz`. JNZ analogue of `adapter_lgfold_eq_psOfFn_succ_general`. -/
theorem adapter_lgfold_eq_psOfFn_succ_jnz_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB : BasicBlock} {pred c ifNz ifZ succ : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction}
    {lg : List ((Instruction × Nat) × List String)}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ :: succRest)
    (hsfind : fn.blocks.find? (·.label == succ) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ succ) (hsne : succ ≠ pred)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hfront : lg.map Prod.fst = fr.zipIdx 0)
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label (y.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length)
          (bbIsHalting predBB)
          (if y.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[y.2 + 1]!.opcode else false)
          predBB.label ps) :
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2
      = psOfFn fuel fn fnEom lblCtr succ := by
  rw [adapter_fold_eq_zipIdx gp lg fr (psOfFn fuel fn fnEom lblCtr pred) hfront, hgp]
  exact positional_gpfold_eq_psOfFn_succ_jnz_general hentry hpathhead hfuel hfn hchain hpsucc hsfind
    hsfresh hsne hsome hpfind hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS
    hreg hnospill

/-- **Adapter `lg`-fold residual on the canonical schedule for an aligned-JNZ block (NOT-taken).** The
    four `hstep_regularHSVP_jnz_nottaken` residuals — `hstk`/`hsp` (stack/spilled equalities) and
    `hfe`/`hno` (allocator `fnEom` fixed, `nextOffset` non-decreasing) — for the fall-through target
    `ifZ`, on the real schedule, for any chain-reached JNZ block. Composes
    `psOfFn_succ2_rel_bodyfold_jnz_general` with the two standard lifts (`adapter_fold_eq_zipIdx` to the
    positional fold, `instFoldF_regular_fold` to the `instFoldF` body-fold).

    Note it delivers a *relation*, not the whole-PlanState equality the taken branch enjoys: `ifZ`'s
    entry carries the allocator threaded through `ifNz`'s subtree. -/
theorem adapter_lgfold_rel_psOfFn_succ2_jnz_general
    {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry predBB succBB1 succBB2 : BasicBlock} {pred c ifNz ifZ succ1 succ2 : String} {path : List BasicBlock}
    {blockOps : List StackOp} {predPs' : PlanState} {succRest : List String}
    {result : List String × AssocList String PlanState × PlanState}
    {fr : List Instruction} {term : Instruction}
    {lg : List ((Instruction × Nat) × List String)}
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD pred = entry.label)
    (hfuel : 2 * path.length + 4 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      pred blockOps predPs' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hpsucc : (cfgAnalyze fn).succsOf pred = succ1 :: succ2 :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == succ1) = some succBB1)
    (hsfind2 : fn.blocks.find? (·.label == succ2) = some succBB2)
    (hsfresh1 : ∀ b ∈ path, b.label ≠ succ1) (hsne1 : succ1 ≠ pred)
    (hsfresh2 : ∀ b ∈ path, b.label ≠ succ2) (hsne2 : succ2 ≠ pred)
    (hnr : ¬ CfgReach (cfgAnalyze fn) succ1 succ2)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hpfind : fn.blocks.find? (·.label == pred) = some predBB)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn predBB)
    (hnp : nonParamInsts predBB = fr ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (fr.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn predBB) (some ([], psOfFn fuel fn fnEom lblCtr pred)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hfront : lg.map Prod.fst = fr.zipIdx 0)
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label (y.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) predBB.label predBB.instructions.length)
          (bbIsHalting predBB)
          (if y.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[y.2 + 1]!.opcode else false)
          predBB.label ps) :
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2.stack
        = (psOfFn fuel fn fnEom lblCtr succ2).stack ∧
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2.spilled
        = (psOfFn fuel fn fnEom lblCtr succ2).spilled ∧
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2.alloc.fnEom
        = (psOfFn fuel fn fnEom lblCtr succ2).alloc.fnEom ∧
    (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], psOfFn fuel fn fnEom lblCtr pred)).2.alloc.nextOffset
        ≤ (psOfFn fuel fn fnEom lblCtr succ2).alloc.nextOffset := by
  rw [adapter_fold_eq_zipIdx gp lg fr (psOfFn fuel fn fnEom lblCtr pred) hfront, hgp]
  obtain ⟨bodyOps, ps_body, hbody, hstk, hsp, hallo⟩ :=
    psOfFn_succ2_rel_bodyfold_jnz_general hentry hpathhead hfuel hfn hchain hpsucc hsfind1 hsfind2
      hsfresh1 hsne1 hsfresh2 hsne2 hnr hsome hpfind hentry0 hmulti hnp hterm_jnz hterm_ops
      hterm_outs hterm_reg hemit hreorderS hnospill
  have hlift := instFoldF_regular_fold (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn predBB (fr.zipIdx 0) (psOfFn fuel fn fnEom lblCtr pred) hreg
  rw [hbody] at hlift
  have hps_body : ps_body = _ := congrArg Prod.snd (Option.some.inj hlift)
  rw [← hps_body]
  exact ⟨hstk, hsp, hallo.1.symm, hallo.2⟩

/-- **Adapter `lg`-fold = `instFoldF` body-fold (canonical form).** For `gp` = the positional
    `generateRegularInstPlan` generator (`hgp`), `lg.map Prod.fst = fr.zipIdx 0` (`hfront`), and an
    all-regular body (`hreg`), the per-block adapter's raw `lg`-fold equals the `some`-content of the
    `instFoldF` body-fold. So `(lg.foldl gp)` = the body-fold output `(bodyOps, ps_body)` — giving both
    `hstep_regularHSVP_jmp`'s `hblock` (`.1 = bodyOps`) and residual (`.2`). Via `adapter_fold_eq_zipIdx`
    (`lg`-fold = positional `fr.zipIdx` fold) + `instFoldF_regular_fold` (defeq to the positional fold). -/
theorem adapter_lgfold_eq_instfold
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {predBB : BasicBlock} {fr : List Instruction} {ps0 : PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan L D C fn y.1
          (if y.2 + 1 < (nonParamInsts predBB).length then
              liveVarsAt L predBB.label (y.2 + (getParams predBB.instructions).length + 1)
            else liveVarsAt L predBB.label predBB.instructions.length)
          (bbIsHalting predBB)
          (if y.2 + 1 < (nonParamInsts predBB).length then
              isTerminator (nonParamInsts predBB)[y.2 + 1]!.opcode else false)
          predBB.label ps)
    (hfront : lg.map Prod.fst = fr.zipIdx 0)
    (hreg : ∀ x ∈ fr.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    some (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0))
      = (fr.zipIdx 0).foldl (instFoldF L D C fn predBB) (some ([], ps0)) := by
  rw [adapter_fold_eq_zipIdx gp lg fr ps0 hfront, hgp]
  exact (instFoldF_regular_fold L D C fn predBB (fr.zipIdx 0) ps0 hreg).symm

/-- **Per-block layout + canonical `psOf`, from a linear chain (the walk-supplied fact).** For a
    codegen-ready function and a linear single-successor chain to `tgtLbl` from the entry, the
    whole-function plan `ops` decomposes as `preOps ++ tgtBlockOps ++ tailOps` where `tgtBlockOps` is
    exactly `tgt`'s block plan generated from the *canonical* `psOfFn tgtLbl`. This bundles
    `jmpChainTo_of_chain` (construct the chain witness) + `generateFnPlanFuel_chain_segment` (layout) +
    `psOfFn_chain` (canonical `psOf`) — the single fact a walk-reached block's `hstep` consumes:
    its plan sits at `pc = (executePlan preOps).length` and is generated from `psOfFn` of that block. -/
theorem linChain_layout_psOf {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {tgtLbl : String} {path : List BasicBlock}
    {ops : List StackOp} {ps : PlanState}
    (hentry : fn.blocks.head? = some entry)
    (hpathhead : (path.head?.map (·.label)).getD tgtLbl = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hfoundpath : ∀ b ∈ path, fn.blocks.find? (·.label == b.label) = some b)
    (htgt : (fn.blocks.find? (·.label == tgtLbl)).isSome)
    (hlinsucc : LinSucc (cfgAnalyze fn) tgtLbl path)
    (hnodup : ((path.map (·.label)) ++ [tgtLbl]).Nodup)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ tgtBB preOps tailOps tgtBlockOps tgtPs',
      fn.blocks.find? (·.label == tgtLbl) = some tgtBB ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn tgtBB
        (psOfFn fuel fn fnEom lblCtr tgtLbl) = some (tgtBlockOps, tgtPs') ∧
      ops = preOps ++ tgtBlockOps ++ tailOps := by
  obtain ⟨tgtBlockOps, tgtPs', hchain⟩ := jmpChainTo_of_chain (L := livenessAnalyzeFuel fuel fn)
    (D := DfgAnalysis.buildFunction fn) (C := cfgAnalyze fn) hfn path []
    { initPlanState fnEom with labelCounter := lblCtr }
    hfoundpath htgt hlinsucc (fun b _ => rfl) rfl hnodup
  obtain ⟨preOps, tailOps, hops⟩ :=
    generateFnPlanFuel_chain_segment hentry hpathhead hfuel hfn hchain hgen
  obtain ⟨tgtBB, hfindtgt, hbpT⟩ :=
    psOfFn_chain hentry hpathhead hfuel hfn hchain
  exact ⟨tgtBB, preOps, tailOps, tgtBlockOps, tgtPs', hfindtgt, hbpT, hops⟩

/-- **The entry block's canonical `psOf` is the initial plan state.** The DFS starts at `[entry.label]`
    from the initial plan state and records `entry.label ↦ init` on its first (head) visit, so
    `psOfFn … entry.label = { initPlanState fnEom with labelCounter := lblCtr }`. This discharges
    `codegen_correct_sched`'s entry relation when instantiated with the canonical `psOf := psOfFn`:
    `venomAsmRel (psOf entry) = venomAsmRel init`. -/
theorem psOfFn_entry {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hfuel : 0 < fuel) :
    psOfFn fuel fn fnEom lblCtr entry.label = { initPlanState fnEom with labelCounter := lblCtr } := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hhd : fn.blocks.head? = some entry := hentry
  obtain ⟨tl, hblocks⟩ := List.head?_eq_some_iff.mp hhd
  have hfound : fn.blocks.find? (fun b => b.label == entry.label) = some entry := by
    rw [hblocks, List.find?_cons_of_pos (by simp)]
  obtain ⟨⟨rv, rtbl, rps⟩, hdfs⟩ := Option.isSome_iff_exists.mp
    ((dfsEntriesAux_dfsSuccsEntries_isSome (livenessAnalyzeFuel (f + 1) fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn hfn (f + 1)).1 [entry.label] [] []
      { initPlanState fnEom with labelCounter := lblCtr })
  have hrec := dfsEntriesAux_head_records f (livenessAnalyzeFuel (f + 1) fn) (DfgAnalysis.buildFunction fn)
    (cfgAnalyze fn) fn entry.label [] [] [] { initPlanState fnEom with labelCounter := lblCtr } entry
    (rv, rtbl, rps) (by simp) hfound hdfs
  unfold psOfFn blockEntryTable
  simp only [hentry, Option.map_some, hdfs, hrec, Option.getD_some]

/-- **The entry block's JUMPDEST is at pc 0** (`hpc0zero` for `codegen_correct_canonical`). The entry
    block's plan is the prefix of the whole-function plan (`generateFnPlan_entry_isPrefix`) and starts
    with `SOLabel entry.label` (`generateBlockPlan_head`), which `executePlan` turns into `AsmLabel
    entry.label` at position 0 and `asmResolve` leaves in place (it only rewrites label *pushes*). So
    `pcOfLabel` finds the entry marker at index 0. -/
theorem pcOfLabel_entry_zero {fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    {ops : List StackOp} {psFinal : PlanState}
    (hentry : fn.blocks.head? = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, psFinal)) :
    pcOfLabel (asmResolve (executePlan ops)).1 entry.label = 0 := by
  obtain ⟨blockOps, ps', rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hentry hfn hgen
  obtain ⟨tl, hbo⟩ := generateBlockPlan_head hbp
  subst hops hbo
  rw [List.cons_append, executePlan_cons]
  simp only [execStackOp, List.singleton_append, asmResolve, List.map_cons, resolveInst,
    pcOfLabel, List.findIdx_cons, beq_self_eq_true, cond_true]





/-- **`memoryRel` is monotone in the spill high-water mark.** A larger `nextOffset` (same `fnEom`)
    *excludes more* of memory from the agreement requirement, so it is a weaker relation: `memoryRel`
    with the smaller alloc implies it with the larger. -/
theorem memoryRel_mono_alloc {alloc alloc' : SpillAlloc} {vm am : ByteArray}
    (hfe : alloc.fnEom = alloc'.fnEom) (hno : alloc.nextOffset ≤ alloc'.nextOffset)
    (h : memoryRel alloc vm am) : memoryRel alloc' vm am := by
  intro i hi
  exact h i (fun hc => hi ⟨hfe ▸ hc.1, lt_of_lt_of_le hc.2 hno⟩)

/-- **`venomAsmRel` survives widening the spill allocator (the JNZ-alloc resolution).** Replacing a
    plan state's `alloc` by one with the same `fnEom` and a larger `nextOffset` preserves `venomAsmRel`:
    the stack (`planStackRel`) and spilled map (`planSpillRel`) are untouched, and `memoryRel` only gets
    weaker (`memoryRel_mono_alloc`). This is exactly the situation of a JNZ's second successor, whose DFS
    entry differs from the predecessor's exit only by a wider `alloc` (spill slots threaded past the
    first successor's subtree) — so the walk's `venomAsmRel` at the predecessor's exit implies
    `venomAsmRel` at `psOfFn (2nd succ)`. -/
theorem venomAsmRel_alloc_widen {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    {as : AsmState} {alloc' : SpillAlloc}
    (hfe : ps.alloc.fnEom = alloc'.fnEom) (hno : ps.alloc.nextOffset ≤ alloc'.nextOffset)
    (h : venomAsmRel lo ps vs as) :
    venomAsmRel lo { ps with alloc := alloc' } vs as := by
  obtain ⟨hstk, hspill, hmem, hrest⟩ := h
  exact ⟨hstk, hspill, memoryRel_mono_alloc hfe hno hmem, hrest⟩

/-- **Phi-free JMP exit is the *uniform* (predecessor-independent) canonical layout.** For a target
    block with **no phis**, the reordered exit stack is `(liveVarsAt liveness target 0).map Var` — and
    crucially this expression carries **no `curBbLabel` dependence**. So *every* predecessor's JMP into
    `target` lands the same var-layout on the stack: the join-block entry is uniform.

    This is the precise reason the whole-function `psOfFn`-based capstone works cleanly for **phi-free
    CFGs**: `psOfFn succ` (whichever predecessor the DFS first entered from) equals *every* other
    predecessor's exit, so the per-block entry relation `hplan` holds for **all** edges — tree *and*
    join — with no traversal-dependent value lift. (With phis, `inputVarsFrom` substitutes each phi's
    *source for `curBbLabel`*, making the entry layout predecessor-dependent — the fundamental obstacle
    to a fixed `psOf` at a phi-join.) -/
theorem jmp_exit_stack_liveness_no_phi
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock} {S : List String}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hsv : StackIsVars S ps)
    (hnd : S.Nodup)
    (hnophi : collectPhis targetBb.instructions = [])
    (hsched : S = liveVarsAt liveness target 0) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps).2.stack
      = (liveVarsAt liveness target 0).map Operand.Var := by
  rw [generateRegularInstPlan_jmp_eq_of_stackIsVars_no_phi hjmp hops houts htgt hsv hnd hnophi hsched]
  show (releaseDeadSpills nextLiveness ps).stack = _
  rw [releaseDeadSpills_stack]
  rw [show ps.stack = S.map Operand.Var from hsv, hsched]

/-- **A var-layout entry relation defines its variables.** If `venomAsmRel` holds at a plan state whose
    stack is exactly a list of variables `S.map Var` (the canonical layout a JMP predecessor leaves, and
    what a var-reading successor block expects), then every `x ∈ S` is **defined** in the Venom state.
    Extracted from the `planStackRel` conjunct: each stack position's operand value is `some` asm value,
    and `operandVal … (Var x) = lookupVar x`. This is the reusable ingredient that lets a var-reading
    block's per-block `hstep` (`codegen_correct_sched`) recover its incoming variables' values from the
    entry relation alone — no separate definedness hypotheses. -/
theorem varStack_lookupVar_defined {lo : AssocList String Nat} {ps : PlanState}
    {s : VenomState} {asm : AsmState} {S : List String}
    (hrel : venomAsmRel lo { ps with stack := S.map Operand.Var } s asm) :
    ∀ x ∈ S, ∃ v, lookupVar x s = some v := by
  obtain ⟨⟨hlen, hpos⟩, _⟩ := hrel
  intro x hx
  have hmem : Operand.Var x ∈ (S.map Operand.Var).reverse := by
    rw [List.mem_reverse]; exact List.mem_map_of_mem hx
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hi' : i < (S.map Operand.Var).length := by
    rw [List.length_reverse] at hi; exact hi
  have hpi := hpos i hi'
  rw [getElem!_pos _ i (by rw [List.length_reverse]; exact hi'), hget] at hpi
  exact ⟨_, hpi⟩

/-- **Asm-side sim for a real param-function's var-reading block.** For the *actual* codegen of
    `[PARAM x; PARAM y; SSTORE x y; STOP]` — the resolved program `[JUMPDEST; SWAP1; SSTORE; STOP]` — a
    run from an entry `venomAsmRel` at the var-layout `[Var x, Var y]` halts with the terminal relation
    to `haltState (sstore vx vy vs)`. The `SWAP1` reorders `[vy, vx]` on the asm stack to `[vx, vy]` so
    the `SSTORE` pops `key = vx, value = vy` — exactly the Venom `SSTORE x y = sstore vx vy` (matching
    `runBlock_paramSstore_venom`). Composes `soLabel_sim` + `doSwap_sim` + `emit_sstore_sim` + `runAsm_stop`,
    with the SSTORE operands extracted from the post-swap relation via `asmStack_top2_of_planStackRel`.
    Carries the 2 M1 FFI axioms through `doSwap_sim` (the documented active-swap boundary); no sorryAx. -/
theorem asm_paramSstore_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 4 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (sstore vx vy vs)) as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"]
    with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  -- step 1: JUMPDEST at pc 0
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  -- step 2: SWAP1 at pc 1
  have hdoSwap : doSwap 1 psE
      = ([StackOp.SOSwap 1], { psE with stack := [Operand.Var "y", Operand.Var "x"] }) := by
    rw [hpsE]; unfold doSwap; simp [stackSwap]
  have hlen : (1 : Nat) < psE.stack.length := by rw [hpsE]; decide
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 1]) := by
    rw [hpc1']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hdoSwap hrel1 hlen hblock1 (by intro h; omega)
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  -- step 3: SSTORE at pc 2 — extract as2.stack = vx :: vy :: rest
  have hstk2 : ∃ rest, as2.stack = vx :: vy :: rest :=
    asmStack_top2_of_planStackRel hrel2.1 (by rw [hpsE]; decide) rfl rfl hxdef hydef
  obtain ⟨rest, hstk2'⟩ := hstk2
  have hblock2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by
    rw [hpc2']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ :=
    emit_sstore_sim (offsetToPc := offsetToPc) hrel2 hstk2' hblock2
      (fun h hg => asmStep_sstore_ok h hg)
  have hr3 : runAsm 1 offsetToPc prog as2 = AsmResult.AsmOK as3 := hrun3
  have hpc3' : as3.pc = 3 := by rw [hpc3, hpc2']; rfl
  -- step 4: STOP at pc 3
  have hlt3 : as3.pc < prog.length := by rw [hpc3']; decide
  have hget3 : prog.get ⟨as3.pc, hlt3⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as3.pc, hlt3⟩ : Fin prog.length) = ⟨3, by decide⟩ from Fin.ext hpc3']; rfl
  refine ⟨asmNext as3, ?_, ?_⟩
  · rw [show (4 : Nat) = 1 + (1 + (1 + 1)) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2,
        runAsm_add_ok hr3]
    exact runAsm_stop 0 hlt3 hget3
  · exact venomAsmRel_terminal lo _ _ _ hrel3

/-- **Asm-side var-reading SSTORE block at an arbitrary pc.** The pc-general form of
    `asm_paramSstore_sim`: given the `[JUMPDEST l; SWAP1; SSTORE; STOP]` segment placed at `as.pc` in a
    whole program (`hb0`/`hb1`/`hb2`/`hget3`) and an entry `venomAsmRel` at the var-layout, 4 asm steps
    reach `AsmHalt` with the terminal relation to `haltState (sstore vx vy vs)`. This is the `next`-block
    half of a multi-block var-passing param function (the entry half is `hentryAsm_bare_jmp`). -/
theorem asm_paramSstore_block {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {vx vy : bytes32} {l : String}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (hb0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel l]))
    (hb1 : asmBlockAt prog (as.pc + 1) (executePlan [StackOp.SOSwap 1]))
    (hb2 : asmBlockAt prog (as.pc + 2) (executePlan [StackOp.SOEmit "SSTORE"]))
    (hlt3 : as.pc + 3 < prog.length)
    (hget3 : prog.get ⟨as.pc + 3, hlt3⟩ = AsmInst.AsmOp "STOP") :
    ∃ as', runAsm 4 offsetToPc prog as = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (sstore vx vy vs)) as' := by
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog l hrel hb0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = as.pc + 1 := by rw [hpc1]; rfl
  have hdoSwap : doSwap 1 psE
      = ([StackOp.SOSwap 1], { psE with stack := [Operand.Var "y", Operand.Var "x"] }) := by
    rw [hpsE]; unfold doSwap; simp [stackSwap]
  have hlen : (1 : Nat) < psE.stack.length := by rw [hpsE]; decide
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpc1']; exact hb1
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hdoSwap hrel1 hlen hblock1 (by intro h; omega)
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = as.pc + 2 := by rw [hpc2, hpc1']; rfl
  have hstk2 : ∃ rest, as2.stack = vx :: vy :: rest :=
    asmStack_top2_of_planStackRel hrel2.1 (by rw [hpsE]; decide) rfl rfl hxdef hydef
  obtain ⟨rest, hstk2'⟩ := hstk2
  have hblock2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by rw [hpc2']; exact hb2
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ :=
    emit_sstore_sim (offsetToPc := offsetToPc) hrel2 hstk2' hblock2
      (fun h hg => asmStep_sstore_ok h hg)
  have hr3 : runAsm 1 offsetToPc prog as2 = AsmResult.AsmOK as3 := hrun3
  have hpc3' : as3.pc = as.pc + 3 := by rw [hpc3, hpc2']; rfl
  have hlt3' : as3.pc < prog.length := by rw [hpc3']; exact hlt3
  have hget3' : prog.get ⟨as3.pc, hlt3'⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as3.pc, hlt3'⟩ : Fin prog.length) = ⟨as.pc + 3, hlt3⟩ from Fin.ext hpc3']; exact hget3
  refine ⟨asmNext as3, ?_, ?_⟩
  · rw [show (4 : Nat) = 1 + (1 + (1 + 1)) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2,
        runAsm_add_ok hr3]
    exact runAsm_stop 0 hlt3' hget3'
  · exact venomAsmRel_terminal lo _ _ _ hrel3


/-- **Generic OK-continue clause for the arbitrary-CFG driver (`runBlocks_walk`).** Any block that runs
    `blockLen ≤ N` asm steps to a successor entry `asm'` at which the walk invariant is re-established
    (`Entry s' asm' (N - blockLen)`) supplies `runBlocks_walk`'s continuation clause: `runAsm N` from
    `asm` equals `runAsm (N - blockLen)` from `asm'` (the block's steps are a prefix, `runAsm_add_ok`),
    so the driver resumes at the successor. The reusable block→CFG bridge for the continue case
    (JMP/JNZ blocks): compose with the halting-block clause and feed to `runBlocks_walk` to drive an
    arbitrary control-flow graph. -/
theorem hbsim_continue_clause {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asm' : AsmState} {blockLen N : Nat} {s' : VenomState}
    (Entry : VenomState → AsmState → Nat → Prop)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hle : blockLen ≤ N)
    (hEntry' : Entry s' asm' (N - blockLen)) :
    ∃ asm'' N', runAsm N offsetToPc prog asm = runAsm N' offsetToPc prog asm'' ∧ Entry s' asm'' N' := by
  refine ⟨asm', N - blockLen, ?_, hEntry'⟩
  have h := runAsm_add_ok (m := N - blockLen) hrun
  rw [show blockLen + (N - blockLen) = N from by omega] at h
  exact h

/-- **Per-block `hbsim` OK-continue clause for a JMP-continue H-fold block.** Packages
    `hasm_regularHN_jmp` (asm side) into the exact `match runBlock … with …` clause `runBlocks_walk`
    consumes, for a block whose Venom run is `OK (jumpTo target sEnd)` (a non-halting body + JMP). The
    body may contain the memory copies / LOG (`RegularBodyH`). The caller supplies the Venom evaluation
    `hrunBlock` and the successor-`Entry` re-establishment `hEntry'` (given the post-jump `venomAsmRel`
    on the body's final plan state + the target pc — this is where any join reconciliation enters);
    everything else (the asm run + budget transition via `hbsim_continue_clause`) is discharged here. -/
theorem hbsim_regularHN_jmp_clause
    (Entry : VenomState → AsmState → Nat → Prop)
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {N f' : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel target : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem off idx : Nat}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { s with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { s with instIdx := 0 } = some sEnd)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hpc1 : asm.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨asm.pc + bodyLen, hpc1⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asm.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨asm.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hrunBlock : runBlock f' ctx bb s = ExecResult.OK (jumpTo target sEnd))
    (hnothalt : sEnd.halted = false)
    (hle : bodyLen + 2 ≤ N)
    (hEntry' : ∀ asm', venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2 sEnd asm' → asm'.pc = idx →
        Entry (jumpTo target sEnd) asm' (N - (bodyLen + 2))) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ asm' N', runAsm N offsetToPc prog asm = runAsm N' offsetToPc prog asm' ∧ Entry s' asm' N'
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [hrunBlock]
  have hjhalt : (jumpTo target sEnd).halted = false := by unfold jumpTo; exact hnothalt
  simp only [hjhalt, Bool.false_eq_true, if_false]
  obtain ⟨asm', hrun, hrel, hpc⟩ :=
    hasm_regularHN_jmp hbody hsd0 hsv0 hrel0 hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  exact hbsim_continue_clause Entry hrun hle (hEntry' asm' hrel hpc)

/-- **Aligned-JMP layout in `hstep_regularHSVP_jmp`'s exact shape.** Reformulates
    `blockplan_aligned_jmp_layout` (raw `bodyOps` at segment offset `(executePlan preOps).length`) into
    the per-block `hstep`'s hypotheses: `hblock`/`hpush`/`hjump` phrased with `as0.pc` (`= as0pc`, given by
    `pcOfLabel_aligned_jmp_block`) and the *adapter* `lg`-fold body `(lg.foldl gp ([], ps_in)).1`
    (`= bodyOps`, via `adapter_lgfold_eq_instfold`). This packages the trickiest matching — position
    arithmetic + the fold identity — so the per-block JMP `hstep` on the canonical schedule needs only the
    residual (`adapter_lgfold_eq_psOfFn_succ_general`), jump-target, body-sim, Venom and forward-edge facts. -/
theorem hstep_jmp_layout_canonical
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps_in : PlanState} {ops preOps tailOps blockOps : List StackOp} {ps' : PlanState}
    {front : List Instruction} {term : Instruction} {target : String}
    {lg : List ((Instruction × Nat) × List String)} {as0pc : Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (has0pc : as0pc = (executePlan preOps).length)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan L D C fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1 as0pc
        (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)) ∧
    ∃ (h1 : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length
          < (asmResolve (executePlan ops)).1.length),
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length, h1⟩
        = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel target) ∧
      ∃ (h2 : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 1
          < (asmResolve (executePlan ops)).1.length),
        (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 1, h2⟩
        = AsmInst.AsmOp "JUMP" := by
  obtain ⟨bodyOps, ps_body, hbody, hblk, ⟨hh1, hpush⟩, ⟨hh2, hjump⟩⟩ :=
    blockplan_aligned_jmp_layout L D C fn bb ps_in ops preOps tailOps blockOps ps' front term target
      hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp hseg hnospill hlblfree
  have hfeq := adapter_lgfold_eq_instfold (predBB := bb) (ps0 := ps_in) hgp hfront hreg
  rw [hbody] at hfeq
  have hfst : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1
      = bodyOps := by rw [Option.some.inj hfeq]
  rw [hfst, has0pc]
  exact ⟨hblk, hh1, hpush, hh2, hjump⟩

/-- **Aligned-JMP layout in `hstep` shape, straight from a JMP chain to the block.** Bundles the
    placement (`generateFnPlanFuel_chain_segment` → segment, `psOfFn_chain` → `generateBlockPlan` at the
    canonical `psOfFn` entry state, `pcOfLabel_aligned_jmp_block` → block pc = segment offset) with
    `hstep_jmp_layout_canonical`, so the per-block JMP `hstep` gets `hblock`/`hpush`/`hjump` at
    `pcOfLabel prog bb.label` (`= as0.pc`) directly from `hchain`, with no segment/gbp/pc plumbing.
    `hpreuniq` is quantified over the (essentially unique) segment decomposition — the one open
    label-uniqueness fact the caller supplies. -/
theorem hstep_jmp_layout_from_chain {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {path : List BasicBlock}
    {blockOps : List StackOp} {ps' : PlanState} {ops : List StackOp} {ps : PlanState}
    {front : List Instruction} {term : Instruction} {target : String}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
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
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1
        (pcOfLabel (asmResolve (executePlan ops)).1 bb.label)
        (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)) ∧
    ∃ (h1 : pcOfLabel (asmResolve (executePlan ops)).1 bb.label + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
          < (asmResolve (executePlan ops)).1.length),
      (asmResolve (executePlan ops)).1.get ⟨pcOfLabel (asmResolve (executePlan ops)).1 bb.label
          + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length, h1⟩
        = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel target) ∧
      ∃ (h2 : pcOfLabel (asmResolve (executePlan ops)).1 bb.label + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 1
          < (asmResolve (executePlan ops)).1.length),
        (asmResolve (executePlan ops)).1.get ⟨pcOfLabel (asmResolve (executePlan ops)).1 bb.label
          + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 1, h2⟩
        = AsmInst.AsmOp "JUMP" := by
  have hhead : fn.blocks.head? = some entry := hentry
  obtain ⟨preOps, tailOps, hseg⟩ :=
    generateFnPlanFuel_chain_segment hhead hpathhead hfuel hfn hchain hgen
  obtain ⟨tgtBB, hfindT, hgbp0⟩ := psOfFn_chain hentry hpathhead hfuel hfn hchain
  have htgt : tgtBB = bb := by rw [hpfind] at hfindT; exact (Option.some.inj hfindT).symm
  rw [htgt] at hgbp0
  have hpc : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  exact hstep_jmp_layout_canonical
    (as0pc := pcOfLabel (asmResolve (executePlan ops)).1 bb.label)
    hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill hlblfree hpc hgp hfront hreg

/-- **Aligned bare-halting (STOP/INVALID) layout in `hstep_regularHSVP_{stop,invalid}`'s exact shape.**
    Reformulates `blockplan_aligned_bareHalt_layout` into `hblock` + `hget` (`AsmOp name` at
    `as0.pc + bodyLen`) phrased with `as0.pc` (`= as0pc`) and the adapter `lg`-fold body
    (`= bodyOps`, via `adapter_lgfold_eq_instfold`). Bare-op analogue of `hstep_jmp_layout_canonical`. -/
theorem hstep_bareHalt_layout_canonical
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps_in : PlanState} {ops preOps tailOps blockOps : List StackOp} {ps' : PlanState}
    {front : List Instruction} {term : Instruction} {name : String}
    {lg : List ((Instruction × Nat) × List String)} {as0pc : Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (has0pc : as0pc = (executePlan preOps).length)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan L D C fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1 as0pc
        (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)) ∧
    ∃ (h1 : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length
          < (asmResolve (executePlan ops)).1.length),
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length, h1⟩
        = AsmInst.AsmOp name := by
  obtain ⟨bodyOps, ps_body, hbody, hblk, ⟨hh1, hget⟩⟩ :=
    blockplan_aligned_bareHalt_layout L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp hseg hnospill hlblfree
  have hfeq := adapter_lgfold_eq_instfold (predBB := bb) (ps0 := ps_in) hgp hfront hreg
  rw [hbody] at hfeq
  have hfst : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1
      = bodyOps := by rw [Option.some.inj hfeq]
  rw [hfst, has0pc]
  exact ⟨hblk, hh1, hget⟩

/-- **Aligned bare-halting layout in `hstep` shape, straight from a JMP chain to the block.** Bare-op
    analogue of `hstep_jmp_layout_from_chain`: placement (`generateFnPlanFuel_chain_segment` +
    `psOfFn_chain` + `pcOfLabel_aligned_bareHalt_block`) + `hstep_bareHalt_layout_canonical` → `hblock` +
    `hget` at `pcOfLabel prog bb.label` (`= as0.pc`) directly from `hchain`. -/
theorem hstep_bareHalt_layout_from_chain {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {path : List BasicBlock}
    {blockOps : List StackOp} {ps' : PlanState} {ops : List StackOp} {ps : PlanState}
    {front : List Instruction} {term : Instruction} {name : String}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
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
    (hname : opcodeToEvmName term.opcode = some name)
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
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1
        (pcOfLabel (asmResolve (executePlan ops)).1 bb.label)
        (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)) ∧
    ∃ (h1 : pcOfLabel (asmResolve (executePlan ops)).1 bb.label + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
          < (asmResolve (executePlan ops)).1.length),
      (asmResolve (executePlan ops)).1.get ⟨pcOfLabel (asmResolve (executePlan ops)).1 bb.label
          + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length, h1⟩
        = AsmInst.AsmOp name := by
  have hhead : fn.blocks.head? = some entry := hentry
  obtain ⟨preOps, tailOps, hseg⟩ :=
    generateFnPlanFuel_chain_segment hhead hpathhead hfuel hfn hchain hgen
  obtain ⟨tgtBB, hfindT, hgbp0⟩ := psOfFn_chain hentry hpathhead hfuel hfn hchain
  have htgt : tgtBB = bb := by rw [hpfind] at hfindT; exact (Option.some.inj hfindT).symm
  rw [htgt] at hgbp0
  have hpc : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term name hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  exact hstep_bareHalt_layout_canonical
    (as0pc := pcOfLabel (asmResolve (executePlan ops)).1 bb.label)
    hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill hlblfree hpc hgp hfront hreg

/-- **Aligned RETURN/REVERT layout in `hstep_regularHSVP_return`'s exact shape.** Reformulates
    `blockplan_aligned_return_layout` into `hblock` (`asmBlockAt` for `([SOLabel l]++body) ++ emit`) + `hget`
    (`AsmOp name` at `as0.pc + bodyLen + emitLen`), phrased with `as0.pc` (`= as0pc`) and the adapter `lg`-fold
    body (`= bodyOps`, `.2 = ps_body` via `adapter_lgfold_eq_instfold`). Bridges the block-vs-append
    associativity and the `bodyLen + emitLen` length split. Operand-terminal analogue of
    `hstep_bareHalt_layout_canonical`. -/
theorem hstep_return_layout_canonical
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps_in : PlanState} {ops preOps tailOps blockOps : List StackOp} {ps' : PlanState}
    {front : List Instruction} {term : Instruction} {name offv szv : String}
    {lg : List ((Instruction × Nat) × List String)} {as0pc : Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (has0pc : as0pc = (executePlan preOps).length)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan L D C fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1 as0pc
        (executePlan (([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)
          ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length)
                (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).2).1)) ∧
    ∃ (hlt : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length
          + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length)
                (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).2).1).length
          < (asmResolve (executePlan ops)).1.length),
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length
          + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
                (liveVarsAt L bb.label bb.instructions.length)
                (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).2).1).length, hlt⟩
        = AsmInst.AsmOp name := by
  obtain ⟨bodyOps, ps_body, hbody, hblk, ⟨hh, hget⟩⟩ :=
    blockplan_aligned_return_layout L D C fn bb ps_in ops preOps tailOps blockOps ps' front term name
      offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp hseg hlblfree
  have hfeq := adapter_lgfold_eq_instfold (predBB := bb) (ps0 := ps_in) hgp hfront hreg
  rw [hbody] at hfeq
  have hfold : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in))
      = (bodyOps, ps_body) := Option.some.inj hfeq
  rw [hfold, has0pc]
  have hlen : (executePlan ([StackOp.SOLabel bb.label] ++ (bodyOps ++
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1))).length
      = (executePlan ([StackOp.SOLabel bb.label] ++ bodyOps)).length
        + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
            (liveVarsAt L bb.label bb.instructions.length) ps_body).1).length := by
    rw [show [StackOp.SOLabel bb.label] ++ (bodyOps ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1)
        = ([StackOp.SOLabel bb.label] ++ bodyOps) ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1 from by simp [List.append_assoc],
      executePlan_append, List.length_append]
  have hassoc : ([StackOp.SOLabel bb.label] ++ bodyOps) ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1
      = [StackOp.SOLabel bb.label] ++ (bodyOps ++ (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt L bb.label bb.instructions.length) ps_body).1) := by simp [List.append_assoc]
  rw [hassoc]
  refine ⟨hblk, ?_⟩
  rw [Nat.add_assoc, ← hlen]
  exact ⟨hh, hget⟩

/-- **Aligned JNZ layout in `hstep_regularHSVP_jnz_{taken,nottaken}`'s exact shape.** Reformulates
    `blockplan_aligned_jnz_layout` into `hblock` (label+body) + the five tail positions (`hdup`/`hpushNz`/
    `hjumpi`/`hpushZ`/`hjump`), phrased with `as0.pc` (`= as0pc`) and the adapter `lg`-fold body
    (`= bodyOps`, via `adapter_lgfold_eq_instfold`). Dual-successor analogue of `hstep_jmp_layout_canonical`;
    the taken hstep uses the first three, the not-taken all five. -/
theorem hstep_jnz_layout_canonical
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps_in : PlanState} {ops preOps tailOps blockOps : List StackOp} {ps' : PlanState}
    {front : List Instruction} {term : Instruction} {c ifNz ifZ : String}
    {lg : List ((Instruction × Nat) × List String)} {as0pc : Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial L C fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).1 = [StackOp.SODup 1])
    (hreorder : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt L bb.label bb.instructions.length) ps_body).2).1 = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (has0pc : as0pc = (executePlan preOps).length)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan L D C fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt L bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt L bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP) :
    asmBlockAt (asmResolve (executePlan ops)).1 as0pc
        (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)) ∧
    (∃ h : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length, h⟩
        = AsmInst.AsmOp "DUP1") ∧
    (∃ h : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 1
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 1, h⟩
        = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifNz)) ∧
    (∃ h : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 2
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 2, h⟩
        = AsmInst.AsmOp "JUMPI") ∧
    (∃ h : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 3
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 3, h⟩
        = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel ifZ)) ∧
    (∃ h : as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 4
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨as0pc + (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1)).length + 4, h⟩
        = AsmInst.AsmOp "JUMP") := by
  obtain ⟨bodyOps, ps_body, hbody, hblk, hdup, hpushNz, hjumpi, hpushZ, hjump⟩ :=
    blockplan_aligned_jnz_layout L D C fn bb ps_in ops preOps tailOps blockOps ps' front term c ifNz ifZ
      hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorder hgbp hseg hlblfree
  have hfeq := adapter_lgfold_eq_instfold (predBB := bb) (ps0 := ps_in) hgp hfront hreg
  rw [hbody] at hfeq
  have hfst : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps_in)).1
      = bodyOps := by rw [Option.some.inj hfeq]
  rw [hfst, has0pc]
  exact ⟨hblk, hdup, hpushNz, hjumpi, hpushZ, hjump⟩

/-! ## Universal DFS plan decomposition — *every* visited block's plan is a segment

`JmpChainTo`/`chain_segment_gbp` place a block's plan inside the whole-function ops only when the
block is reached from the entry along a chain of **single-successor** (JMP) blocks — every
intermediate block must satisfy `C.succsOf bb.label = [next]`. That excludes the branch targets of
any `JNZ` (their predecessor has two successors), so no `hstep` could be instantiated for them.

The lemmas below remove that restriction. The plan DFS (`generateFnPlanAux`/`generateSuccsPlan`) and
the entry-state DFS (`dfsEntriesAux`/`dfsSuccsEntries`) have *identical* control structure — same
worklist, same `visited`, same `generateBlockPlan` calls, same plan-state thread (`dfsEntries_faithful`);
the entry DFS merely drops the ops and records each block's entry plan state. Running them in lock-step
gives, for **every** block the DFS visits (JNZ targets included), both halves of what a per-block
`hstep` needs: its recorded entry state `psL`, and its block plan sitting as a *segment*
`ops = pre ++ blk ++ tail` planned from exactly that `psL`. -/

/-- Cons-unfolding for `generateSuccsPlan` (the `let psBranch`/`psG'` reduced) — the plan-side mirror
    of `dfsSuccsEntries_cons`. -/
theorem generateSuccsPlan_cons (fuel : Nat) (L : DfState (List String)) (D : DfgAnalysis)
    (C : CfgAnalysis) (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
    (succ : String) (rest visited : List String) (psG : PlanState) :
    generateSuccsPlan (fuel + 1) L D C fn savedStack savedSpilled (succ :: rest) visited psG =
    (match generateFnPlanAux fuel L D C fn [succ] visited
             { psG with stack := savedStack, spilled := savedSpilled } with
     | none => none
     | some (sOps, vAfter, psAfter) =>
       match generateSuccsPlan fuel L D C fn savedStack savedSpilled rest vAfter
               { psG with alloc := psAfter.alloc, labelCounter := psAfter.labelCounter } with
       | none => none
       | some (restOps, vF, psF) => some (sOps ++ restOps, vF, psF)) := rfl

/-- **Universal DFS segment + entry-state recording (the general CFG invariant).** Running the plan
    DFS and the entry-state DFS in lock-step from the same `(worklist, visited, ps)`: for **every**
    label `l` that this call *freshly visits* (`visited.contains l = false` on entry, `true` on exit)
    and that names a real block, the entry table records some `psL` for `l`, and `l`'s block plan —
    computed from exactly that recorded `psL` — is a **segment** of this call's ops.

    This is the general-CFG replacement for `generateFnPlanAux_chain_segment`, which only reaches
    blocks along a single-successor (JMP) chain. Here the branch (`generateSuccsPlan`) recursion is
    handled by the mutual `S` component, so a `JNZ`'s *second* successor is covered on the same
    footing as its first — the segment simply sits further right in `ops`.

    Proof: mutual induction on DFS fuel, mirroring the DFS's own recursion. At a fresh block the three
    cases are (i) `l` is the block itself — it is inserted into the table with the current `ps`, and
    both later sub-walks preserve that entry (`dfsEntries_table_mono`, since `l` is now visited), while
    its plan `blk` is the head of `ops = blk ++ succOps ++ restOps`; (ii) `l` is visited by the
    successor walk — `ihS` puts the segment inside `succOps`; (iii) `l` is visited by the worklist
    tail — `ihA` puts it inside `restOps`. `dfsEntries_faithful` aligns the two walks' `(visited, ps)`
    so the tail recursions of both sides start from the same state. -/
theorem dfsEntries_plan_segment (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis)
    (fn : IrFunction) :
    ∀ (fuel : Nat),
    (∀ (worklist visited : List String) (tbl : AssocList String PlanState) (ps : PlanState)
       (ops : List StackOp) (v' : List String) (ps' : PlanState)
       (vE : List String) (tblE : AssocList String PlanState) (psE : PlanState)
       (l : String) (bbL : BasicBlock),
      generateFnPlanAux fuel L D C fn worklist visited ps = some (ops, v', ps') →
      dfsEntriesAux fuel L D C fn worklist visited tbl ps = some (vE, tblE, psE) →
      visited.contains l = false →
      v'.contains l = true →
      fn.blocks.find? (·.label == l) = some bbL →
      ∃ (psL psL' : PlanState) (pre blk tail : List StackOp),
        AssocList.lookup String PlanState tblE l = some psL ∧
        generateBlockPlan L D C fn bbL psL = some (blk, psL') ∧
        ops = pre ++ blk ++ tail)
    ∧
    (∀ (savedStack : List Operand) (savedSpilled : SpilledMap) (succs visited : List String)
       (tbl : AssocList String PlanState) (psG : PlanState)
       (ops : List StackOp) (v' : List String) (ps' : PlanState)
       (vE : List String) (tblE : AssocList String PlanState) (psE : PlanState)
       (l : String) (bbL : BasicBlock),
      generateSuccsPlan fuel L D C fn savedStack savedSpilled succs visited psG = some (ops, v', ps') →
      dfsSuccsEntries fuel L D C fn savedStack savedSpilled succs visited tbl psG
        = some (vE, tblE, psE) →
      visited.contains l = false →
      v'.contains l = true →
      fn.blocks.find? (·.label == l) = some bbL →
      ∃ (psL psL' : PlanState) (pre blk tail : List StackOp),
        AssocList.lookup String PlanState tblE l = some psL ∧
        generateBlockPlan L D C fn bbL psL = some (blk, psL') ∧
        ops = pre ++ blk ++ tail) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro worklist visited tbl ps ops v' ps' vE tblE psE l bbL hg _hd hvf hv' _hfind
      rw [generateFnPlanAux] at hg
      have hveq : v' = visited := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
      rw [hveq, hvf] at hv'; simp at hv'
    · intro ss sp succs visited tbl psG ops v' ps' vE tblE psE l bbL hg _hd hvf hv' _hfind
      rw [generateSuccsPlan] at hg
      have hveq : v' = visited := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
      rw [hveq, hvf] at hv'; simp at hv'
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · -- plan-DFS / entry-DFS in lock-step on a worklist
      intro worklist visited tbl ps ops v' ps' vE tblE psE l bbL hg hd hvf hv' hfind
      cases worklist with
      | nil =>
        rw [generateFnPlanAux_nil] at hg
        have hveq : v' = visited := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
        rw [hveq, hvf] at hv'; simp at hv'
      | cons lbl rest =>
        by_cases hvis : visited.contains lbl
        · rw [generateFnPlanAux_skip_visited _ _ _ _ _ _ _ _ _ hvis] at hg
          rw [dfsEntriesAux_skip _ _ _ _ _ _ _ _ _ _ hvis] at hd
          exact ihA rest visited tbl ps ops v' ps' vE tblE psE l bbL hg hd hvf hv' hfind
        · have hvisf : visited.contains lbl = false := by
            simp only [Bool.not_eq_true] at hvis; exact hvis
          cases hfindl : fn.blocks.find? (·.label == lbl) with
          | none =>
            rw [generateFnPlanAux_find_none _ _ _ _ _ _ _ _ _ hvisf hfindl] at hg
            rw [dfsEntriesAux_find_none _ _ _ _ _ _ _ _ _ _ hvisf hfindl] at hd
            have hne : l ≠ lbl := by
              intro h; rw [h, hfindl] at hfind; exact absurd hfind (by simp)
            have hvf' : (lbl :: visited).contains l = false := by
              rw [List.contains_cons, hvf, Bool.or_false, beq_eq_false_iff_ne]; exact hne
            exact ihA rest (lbl :: visited) _ ps ops v' ps' vE tblE psE l bbL hg hd hvf' hv' hfind
          | some bb =>
            -- keep an un-destructed copy of the entry-DFS equation for the head-record lemma
            have hdhead : dfsEntriesAux (n + 1) L D C fn (lbl :: rest) visited tbl ps
                = some (vE, tblE, psE) := hd
            rw [generateFnPlanAux_visit_block _ _ _ _ _ _ _ _ _ _ hvisf hfindl] at hg
            rw [dfsEntriesAux_visit_block _ _ _ _ _ _ _ _ _ _ _ hvisf hfindl] at hd
            cases hbp : generateBlockPlan L D C fn bb ps with
            | none => rw [hbp] at hg; exact absurd hg (by simp)
            | some rbp =>
              obtain ⟨blockOps, psB⟩ := rbp
              rw [hbp] at hg hd; simp only [] at hg hd
              cases hgs : generateSuccsPlan n L D C fn psB.stack psB.spilled (C.succsOf lbl)
                  (lbl :: visited) psB with
              | none => rw [hgs] at hg; exact absurd hg (by simp)
              | some rgs =>
                obtain ⟨succOps, v2, ps2⟩ := rgs
                cases hds : dfsSuccsEntries n L D C fn psB.stack psB.spilled (C.succsOf lbl)
                    (lbl :: visited) (AssocList.insert String PlanState tbl lbl ps) psB with
                | none => rw [hds] at hd; exact absurd hd (by simp)
                | some rds =>
                  obtain ⟨vE2, tblE2, psE2⟩ := rds
                  rw [hgs] at hg; rw [hds] at hd; simp only [] at hg hd
                  -- both walks thread the same (visited, ps) through the successor recursion
                  have hfaith := (dfsEntries_faithful L D C fn n).2 psB.stack psB.spilled
                    (C.succsOf lbl) (lbl :: visited)
                    (AssocList.insert String PlanState tbl lbl ps) psB
                  rw [hgs, hds] at hfaith
                  simp only [Option.map_some] at hfaith
                  have hv2eq : vE2 = v2 := congrArg (fun r => r.1) (Option.some.inj hfaith)
                  have hp2eq : psE2 = ps2 := congrArg (fun r => r.2) (Option.some.inj hfaith)
                  rw [hv2eq, hp2eq] at hd
                  cases hgr : generateFnPlanAux n L D C fn rest v2 ps2 with
                  | none => rw [hgr] at hg; exact absurd hg (by simp)
                  | some rgr =>
                    obtain ⟨restOps, vF, psF⟩ := rgr
                    rw [hgr] at hg; simp only [] at hg
                    have hopseq : ops = blockOps ++ succOps ++ restOps :=
                      (congrArg (fun r => r.1) (Option.some.inj hg)).symm
                    have hvFeq : v' = vF := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
                    by_cases hl : l = lbl
                    · -- (i) `l` is this very block: entry table records `ps`; plan heads `ops`
                      subst hl
                      have hrec : AssocList.lookup String PlanState tblE l = some ps :=
                        dfsEntriesAux_head_records n L D C fn l rest visited tbl ps bb
                          (vE, tblE, psE) hvf hfindl hdhead
                      have hbbeq : bbL = bb := by
                        rw [hfindl] at hfind; exact (Option.some.inj hfind).symm
                      subst hbbeq
                      exact ⟨ps, psB, [], blockOps, succOps ++ restOps, hrec, hbp,
                        by rw [hopseq]; simp⟩
                    · have hvf' : (lbl :: visited).contains l = false := by
                        rw [List.contains_cons, hvf, Bool.or_false, beq_eq_false_iff_ne]; exact hl
                      by_cases hv2c : v2.contains l
                      · -- (ii) visited by the successor walk: segment sits inside `succOps`
                        obtain ⟨psL, psL', pre, blk, tail, hlk, hbpl, hseg⟩ :=
                          ihS psB.stack psB.spilled (C.succsOf lbl) (lbl :: visited)
                            (AssocList.insert String PlanState tbl lbl ps) psB succOps v2 ps2
                            v2 tblE2 ps2 l bbL hgs (by rw [← hv2eq, ← hp2eq]; exact hds)
                            hvf' hv2c hfind
                        have h2 := (dfsEntries_table_mono L D C fn n).1 rest v2 tblE2 ps2
                          (vE, tblE, psE) l hd hv2c
                        refine ⟨psL, psL', blockOps ++ pre, blk, tail ++ restOps,
                          by rw [h2, hlk], hbpl, ?_⟩
                        rw [hopseq, hseg]; simp [List.append_assoc]
                      · -- (iii) visited by the worklist tail: segment sits inside `restOps`
                        have hv2f : v2.contains l = false := by
                          simp only [Bool.not_eq_true] at hv2c; exact hv2c
                        obtain ⟨psL, psL', pre, blk, tail, hlk, hbpl, hseg⟩ :=
                          ihA rest v2 tblE2 ps2 restOps vF psF vE tblE psE l bbL hgr hd hv2f
                            (by rw [← hvFeq]; exact hv') hfind
                        refine ⟨psL, psL', blockOps ++ succOps ++ pre, blk, tail, hlk, hbpl, ?_⟩
                        rw [hopseq, hseg]; simp [List.append_assoc]
    · -- plan-DFS / entry-DFS in lock-step on a successor list
      intro ss sp succs visited tbl psG ops v' ps' vE tblE psE l bbL hg hd hvf hv' hfind
      cases succs with
      | nil =>
        rw [generateSuccsPlan_nil] at hg
        have hveq : v' = visited := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
        rw [hveq, hvf] at hv'; simp at hv'
      | cons succ rest =>
        rw [generateSuccsPlan_cons] at hg
        rw [dfsSuccsEntries_cons] at hd
        cases hga : generateFnPlanAux n L D C fn [succ] visited
            { psG with stack := ss, spilled := sp } with
        | none => rw [hga] at hg; exact absurd hg (by simp)
        | some rga =>
          obtain ⟨sOps, vA, psA⟩ := rga
          cases hda : dfsEntriesAux n L D C fn [succ] visited tbl
              { psG with stack := ss, spilled := sp } with
          | none => rw [hda] at hd; exact absurd hd (by simp)
          | some rda =>
            obtain ⟨vEA, tblEA, psEA⟩ := rda
            rw [hga] at hg; rw [hda] at hd; simp only [] at hg hd
            have hfaith := (dfsEntries_faithful L D C fn n).1 [succ] visited tbl
              { psG with stack := ss, spilled := sp }
            rw [hga, hda] at hfaith
            simp only [Option.map_some] at hfaith
            have hvAeq : vEA = vA := congrArg (fun r => r.1) (Option.some.inj hfaith)
            have hpAeq : psEA = psA := congrArg (fun r => r.2) (Option.some.inj hfaith)
            rw [hvAeq, hpAeq] at hd
            cases hgr : generateSuccsPlan n L D C fn ss sp rest vA
                { psG with alloc := psA.alloc, labelCounter := psA.labelCounter } with
            | none => rw [hgr] at hg; exact absurd hg (by simp)
            | some rgr =>
              obtain ⟨restOps, vF, psF⟩ := rgr
              rw [hgr] at hg; simp only [] at hg
              have hopseq : ops = sOps ++ restOps :=
                (congrArg (fun r => r.1) (Option.some.inj hg)).symm
              have hvFeq : v' = vF := (congrArg (fun r => r.2.1) (Option.some.inj hg)).symm
              -- `dfsSuccsEntries_cons` leaves an identity `match` around the tail call; peel it
              have hd' : dfsSuccsEntries n L D C fn ss sp rest vA tblEA
                  { psG with alloc := psA.alloc, labelCounter := psA.labelCounter }
                  = some (vE, tblE, psE) := by
                cases hx : dfsSuccsEntries n L D C fn ss sp rest vA tblEA
                    { psG with alloc := psA.alloc, labelCounter := psA.labelCounter } with
                | none => rw [hx] at hd; exact absurd hd (by simp)
                | some r =>
                  obtain ⟨v3, t3, p3⟩ := r
                  rw [hx] at hd; simp only [] at hd; exact hd
              by_cases hvAc : vA.contains l
              · -- visited by this successor's sub-DFS: segment inside `sOps`
                obtain ⟨psL, psL', pre, blk, tail, hlk, hbpl, hseg⟩ :=
                  ihA [succ] visited tbl { psG with stack := ss, spilled := sp } sOps vA psA
                    vA tblEA psA l bbL hga (by rw [← hvAeq, ← hpAeq]; exact hda)
                    hvf hvAc hfind
                have h2 := (dfsEntries_table_mono L D C fn n).2 ss sp rest vA tblEA
                  { psG with alloc := psA.alloc, labelCounter := psA.labelCounter }
                  (vE, tblE, psE) l hd' hvAc
                refine ⟨psL, psL', pre, blk, tail ++ restOps, by rw [h2, hlk], hbpl, ?_⟩
                rw [hopseq, hseg]; simp [List.append_assoc]
              · -- visited by a later successor: segment inside `restOps`
                have hvAf : vA.contains l = false := by
                  simp only [Bool.not_eq_true] at hvAc; exact hvAc
                obtain ⟨psL, psL', pre, blk, tail, hlk, hbpl, hseg⟩ :=
                  ihS ss sp rest vA tblEA
                    { psG with alloc := psA.alloc, labelCounter := psA.labelCounter }
                    restOps vF psF vE tblE psE l bbL hgr hd' hvAf (by rw [← hvFeq]; exact hv') hfind
                refine ⟨psL, psL', sOps ++ pre, blk, tail, hlk, hbpl, ?_⟩
                rw [hopseq, hseg]; simp [List.append_assoc]

/-- **Whole-function universal segment (`chain_segment_gbp` without the JMP-chain restriction).**
    For *any* block the DFS visits — no single-successor chain required, so `JNZ` branch targets are
    included — its block plan, computed from its canonical entry state `psOfFn ... bb.label`, is a
    segment of the whole-function ops. This is exactly the pair (`hseg`, `hgbp0`) that every
    `hstep_regularHSVP_*_canonical` consumes, so it is a drop-in replacement for `chain_segment_gbp`
    at a strictly larger set of blocks.

    Visitedness is supplied as `hvis` against the DFS's own output `visited` set: it is decidable per
    function, and it is precisely the condition under which the block *has* a plan in `ops` at all.
    (`dfsEntries_visited_reach` already gives visited ⇒ `CfgReach`; the converse — that the DFS with
    `fnPlanFuel` visits every reachable block — is a fuel-sufficiency fact, still open.) -/
theorem dfs_segment_gbp {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hentry : entryBlock fn = some entry)
    (hgenAux : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, psF))
    (hvis : vF.contains bb.label = true)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb) :
    ∃ preOps blockOps tailOps ps',
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn)
        fn bb (psOfFn fuel fn fnEom lblCtr bb.label) = some (blockOps, ps') := by
  -- the entry-state DFS on the same worklist always succeeds
  obtain ⟨⟨vE, tbl, psE⟩, hd⟩ := Option.isSome_iff_exists.mp
    ((dfsEntriesAux_dfsSuccsEntries_isSome (livenessAnalyzeFuel fuel fn)
      (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn hfn fuel).1 [entry.label] [] []
      { initPlanState fnEom with labelCounter := lblCtr })
  obtain ⟨psL, psL', pre, blk, tail, hlk, hbpl, hseg⟩ :=
    (dfsEntries_plan_segment (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn fuel).1 [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr }
      ops vF psF vE tbl psE bb.label bb hgenAux hd rfl hvis hpfind
  -- the recorded entry state *is* `psOfFn`
  have hps : psOfFn fuel fn fnEom lblCtr bb.label = psL := by
    show (AssocList.lookup String PlanState (blockEntryTable fuel fn fnEom lblCtr) bb.label).getD
      default = psL
    have htbl : blockEntryTable fuel fn fnEom lblCtr = tbl := by
      show (match (entryBlock fn).map (·.label) with
            | none => []
            | some lbl => match dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn)
                            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn [lbl] [] []
                            { initPlanState fnEom with labelCounter := lblCtr } with
                          | none => []
                          | some (_, t, _) => t) = tbl
      rw [hentry]; simp only [Option.map_some]; rw [hd]
    rw [htbl, hlk]; rfl
  exact ⟨pre, blk, tail, psL', hseg, by rw [hps]; exact hbpl⟩

/-! ### From `CfgReach` to DFS-visited — a decidable closure fact

`dfs_segment_gbp` is keyed on DFS-visitedness, but a caller reasons in terms of CFG reachability
(the Venom walk only ever enters blocks reachable from the entry). `dfsEntries_visited_reach` already
gives visited ⇒ `CfgReach`; the converse needs to know the DFS did not run out of fuel before
covering every successor.

Rather than prove fuel sufficiency for `fnPlanFuel` (a separate measure argument), that gap is
isolated into a single **decidable** side condition, `DfsClosed`: the DFS's own visited set is closed
under CFG successors. `DfsClosed` is a `∀ x ∈ list` statement over two computed lists, so a caller
discharges it with `by decide`; and it is exactly the statement "the DFS did not truncate". Given it,
`visited_of_CfgReach` turns any reachability proof into the `hvis` that `dfs_segment_gbp` wants. -/

/-- The plan DFS's final `visited` set for a whole function (mirrors `blockEntryTable`'s setup). -/
def dfsVisited (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat) : List String :=
  match (entryBlock fn).map (·.label) with
  | none => []
  | some lbl =>
    match generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
            (cfgAnalyze fn) fn [lbl] [] { initPlanState fnEom with labelCounter := lblCtr } with
    | none => []
    | some (_, v, _) => v

/-- **The DFS did not truncate**: its visited set is closed under CFG successors. Decidable (both
    quantifiers range over computed lists), and the *only* thing standing between `CfgReach` and
    DFS-visitedness — with enough fuel the DFS always recurses into every successor of every block
    it visits, so this holds for any `fuel` that suffices. -/
def DfsClosed (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat) : Prop :=
  ∀ l ∈ dfsVisited fuel fn fnEom lblCtr, ∀ s ∈ (cfgAnalyze fn).succsOf l,
    (dfsVisited fuel fn fnEom lblCtr).contains s = true

instance (fuel : Nat) (fn : IrFunction) (fnEom lblCtr : Nat) :
    Decidable (DfsClosed fuel fn fnEom lblCtr) := by unfold DfsClosed; infer_instance

/-- **Reachable ⇒ DFS-visited**, given the closure fact. Straight induction on `CfgReach`: the entry
    is visited (it heads the DFS's worklist), and closure carries visitedness along every CFG edge. -/
theorem visited_of_CfgReach {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entryLbl l : String}
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entryLbl = true)
    (hreach : CfgReach (cfgAnalyze fn) entryLbl l) :
    (dfsVisited fuel fn fnEom lblCtr).contains l = true := by
  induction hreach with
  | base => exact hent
  | step hp hs ih =>
    exact hclosed _ (by simpa using ih) _ hs

/-- **`CfgReach` ⇒ the block's plan is a segment.** The caller-facing form of `dfs_segment_gbp`: for
    any block *reachable in the CFG* from the entry — JNZ branch targets included — its block plan,
    computed from its canonical entry state `psOfFn`, sits as a segment of the whole-function ops.
    The `DfsClosed`/entry-visited side conditions are decidable per function. -/
theorem reach_segment_gbp {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {ops : List StackOp} {vF : List String} {psF : PlanState}
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hentry : entryBlock fn = some entry)
    (hgenAux : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, psF))
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb) :
    ∃ preOps blockOps tailOps ps',
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn)
        fn bb (psOfFn fuel fn fnEom lblCtr bb.label) = some (blockOps, ps') := by
  refine dfs_segment_gbp hfn hentry hgenAux ?_ hpfind
  -- `dfsVisited` *is* this run's visited set
  have hdv : dfsVisited fuel fn fnEom lblCtr = vF := by
    show (match (entryBlock fn).map (·.label) with
          | none => []
          | some lbl => match generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn)
                          (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn [lbl] []
                          { initPlanState fnEom with labelCounter := lblCtr } with
                        | none => []
                        | some (_, v, _) => v) = vF
    rw [hentry]; simp only [Option.map_some]; rw [hgenAux]
  rw [← hdv]
  exact visited_of_CfgReach hclosed hent hreach

/-- `generateFnPlanFuel` is the entry-worklist DFS: peel it to expose the underlying
    `generateFnPlanAux` run (whose `visited` output the segment lemmas are keyed on). -/
theorem generateFnPlanFuel_aux_of_entry {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hentry : entryBlock fn = some entry)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps)) :
    ∃ vF, generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr }
      = some (ops, vF, ps) := by
  rw [generateFnPlanFuel] at hgen
  simp only [hentry, Option.map_some] at hgen
  cases hga : generateFnPlanAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] { initPlanState fnEom with labelCounter := lblCtr } with
  | none => rw [hga] at hgen; exact absurd hgen (by simp)
  | some r =>
    obtain ⟨ops', vF, ps'⟩ := r
    rw [hga] at hgen; simp only [] at hgen
    refine ⟨vF, ?_⟩
    have h1 : ops' = ops := congrArg (fun r => r.1) (Option.some.inj hgen)
    have h2 : ps' = ps := congrArg (fun r => r.2) (Option.some.inj hgen)
    rw [h1, h2]

/-- **`chain_segment_gbp`, chain-free.** Same interface as `chain_segment_gbp` — same `hgen`, same
    `hpfind`, same `(hseg, hgbp0)` output — but `JmpChainTo path` (single-successor blocks only) is
    replaced by plain `CfgReach` plus the decidable `DfsClosed`/entry-visited facts. This is the form
    a per-block `hstep` should consume: it holds at *every* reachable block, JNZ branch targets and
    join blocks included. -/
theorem reach_segment_gbp_fn {fuel fnEom lblCtr : Nat} {fn : IrFunction}
    {entry bb : BasicBlock} {ops : List StackOp} {ps : PlanState}
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hentry : entryBlock fn = some entry)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb) :
    ∃ preOps blockOps tailOps ps',
      ops = preOps ++ blockOps ++ tailOps ∧
      generateBlockPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn)
        fn bb (psOfFn fuel fn fnEom lblCtr bb.label) = some (blockOps, ps') := by
  obtain ⟨vF, hgenAux⟩ := generateFnPlanFuel_aux_of_entry hentry hgen
  exact reach_segment_gbp hfn hentry hgenAux hclosed hent hreach hpfind

/-! ### The Entry invariant — the Venom walk never leaves the CFG

`reach_segment_gbp_fn` gives every *reachable* block its layout. To use it inside a per-block `hstep`,
the walk itself must stay reachable: whenever a block hands control to a successor, that successor must
be CFG-reachable too. That is exactly what `bbSuccs`/`cfgAnalyze` claim, but on the *Venom* side it is
a fact about `execBlock`, and it has to be proved, not assumed.

It holds because `execBlock` returns a non-halted `OK` in exactly one place — the terminator arm — and
a terminator's `stepInstBase` only ever lands on one of its own label operands. The one exception is
`DJMP`, whose target is computed from a runtime selector; it is excluded by the same `hgood` side
condition the `_reach` hsteps already carry. -/

/-- **`extractLabels` succeeds only on an all-`Label` operand list**, and then yields exactly those
    labels. So a `DJMP`'s runtime-selected target is always one of its own label operands. -/
theorem extractLabels_eq_filterMap :
    ∀ (ops : List Operand) (labels : List String),
      extractLabels ops = some labels → labels = ops.filterMap getLabel := by
  intro ops
  induction ops with
  | nil => intro labels h; rw [extractLabels] at h; injection h with h; exact h.symm
  | cons a rest ih =>
    intro labels h
    cases a with
    | Lit v => exact absurd h (by simp [extractLabels])
    | Var v => exact absurd h (by simp [extractLabels])
    | Label l =>
      rw [extractLabels] at h
      cases hr : extractLabels rest with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some ls =>
        rw [hr] at h; simp only [Option.some.injEq] at h
        subst h
        simp [getLabel, ih ls hr]

/-- The ten terminator opcodes, enumerated from `isTerminator`. -/
theorem isTerminator_cases {op : Opcode} (h : isTerminator op = true) :
    op = Opcode.JMP ∨ op = Opcode.JNZ ∨ op = Opcode.DJMP ∨ op = Opcode.RET ∨
    op = Opcode.RETURN ∨ op = Opcode.REVERT ∨ op = Opcode.STOP ∨ op = Opcode.SINK ∨
    op = Opcode.SELFDESTRUCT ∨ op = Opcode.INVALID := by
  revert h; cases op <;> decide

/-- **A terminator jumps only to its own labels.** If a non-`DJMP` terminator steps to `OK s'`, then
    `s'.currentBb` is one of the labels the CFG reads off that terminator (`getSuccessors`). Only
    `JMP`/`JNZ`/`DJMP` can produce `OK` at all — every other terminator halts, aborts, or internally
    returns — so with `DJMP` excluded the two jump arms are the whole content, and each lands on a
    `Label` operand it was given. -/
theorem stepInstBase_term_currentBb_mem_succs {inst : Instruction} {s s' : VenomState}
    (hterm : isTerminator inst.opcode = true)
    (hstep : stepInstBase inst s = ExecResult.OK s') :
    s'.currentBb ∈ getSuccessors inst := by
  have hsucc : getSuccessors inst = inst.operands.filterMap getLabel := by
    unfold getSuccessors; rw [if_pos hterm]
  rw [hsucc]
  rcases isTerminator_cases hterm with h|h|h|h|h|h|h|h|h|h
  -- JMP: operands must be `[Label lbl]`, and it jumps to `lbl`
  · unfold stepInstBase at hstep
    rw [h] at hstep
    cases hops : inst.operands with
    | nil => rw [hops] at hstep; simp at hstep
    | cons a rest =>
      cases a with
      | Label lbl =>
        cases rest with
        | nil =>
          rw [hops] at hstep
          simp only [] at hstep
          injection hstep with hs'; subst hs'
          simp [jumpTo, getLabel]
        | cons b r2 => rw [hops] at hstep; simp at hstep
      | Lit v => rw [hops] at hstep; simp at hstep
      | Var v => rw [hops] at hstep; simp at hstep
  -- JNZ: operands must be `[cond, Label ifNz, Label ifZ]`; it jumps to one of the two
  · unfold stepInstBase at hstep
    rw [h] at hstep
    cases hops : inst.operands with
    | nil => rw [hops] at hstep; simp at hstep
    | cons condOp rest1 =>
      cases rest1 with
      | nil => rw [hops] at hstep; simp at hstep
      | cons a rest2 =>
        cases a with
        | Lit v => rw [hops] at hstep; simp at hstep
        | Var v => rw [hops] at hstep; simp at hstep
        | Label ifNz =>
          cases rest2 with
          | nil => rw [hops] at hstep; simp at hstep
          | cons b rest3 =>
            cases b with
            | Lit v => rw [hops] at hstep; simp at hstep
            | Var v => rw [hops] at hstep; simp at hstep
            | Label ifZ =>
              cases rest3 with
              | cons c r => rw [hops] at hstep; simp at hstep
              | nil =>
                rw [hops] at hstep
                simp only [] at hstep
                split at hstep
                · next cond _ =>
                  split at hstep
                  · injection hstep with hs'; subst hs'
                    simp [jumpTo, getLabel]
                  · injection hstep with hs'; subst hs'
                    simp [jumpTo, getLabel]
                · exact absurd hstep (by simp)
  -- DJMP: its target is `labels.get i`, and `extractLabels` guarantees `labels` *is* the label list
  case _ =>
    unfold stepInstBase at hstep
    rw [h] at hstep
    cases hops : inst.operands with
    | nil => rw [hops] at hstep; simp at hstep
    | cons selOp labelOps =>
      rw [hops] at hstep
      simp only [] at hstep
      cases hev : evalOperand selOp s with
      | none => rw [hev] at hstep; simp at hstep
      | some idx =>
        cases hel : extractLabels labelOps with
        | none => rw [hev, hel] at hstep; simp at hstep
        | some labels =>
          rw [hev, hel] at hstep
          simp only [] at hstep
          split at hstep
          · next hi =>
            injection hstep with hs'; subst hs'
            have hlab : labels = labelOps.filterMap getLabel := extractLabels_eq_filterMap _ _ hel
            set x := labels.get ⟨idx.toNat, hi⟩ with hx
            have hmem : x ∈ labels := List.get_mem _ _
            rw [hlab] at hmem
            simp only [jumpTo, List.filterMap_cons]
            split <;> simp [hmem]
          · exact absurd hstep (by simp)
  -- every remaining terminator halts / aborts / internally returns: never `OK`
  all_goals (
    unfold stepInstBase at hstep
    rw [h] at hstep
    simp only [] at hstep
    repeat' split at hstep
    all_goals exact absurd hstep (by simp))

/-- **A block hands control only to a CFG successor.** `execBlock` produces a non-halted `OK` in exactly
    one place — the terminator arm — so the state it hands on was produced by that terminator's
    `stepInstBase`, and by `stepInstBase_term_currentBb_mem_succs` its `currentBb` is one of the
    terminator's own labels. With the block well-formed (its only terminator is its last instruction),
    those labels are exactly `bbSuccs bb`.

    The body arms (`INVOKE`, external calls, ordinary instructions) all recurse, so the induction
    carries. `DJMP` is excluded — it computes its target from a runtime selector rather than from a
    label operand, so it is the one terminator that could leave the static CFG. -/
theorem execBlock_OK_currentBb_mem_bbSuccs {ctx : VenomContext} {bb : BasicBlock}
    (hwf : ∀ inst ∈ bb.instructions, isTerminator inst.opcode = true →
        inst = bb.instructions.getLast!) :
    ∀ (fuel : Nat) (s s' : VenomState),
      execBlock fuel ctx bb s = ExecResult.OK s' → s'.currentBb ∈ bbSuccs bb := by
  intro fuel
  induction fuel with
  | zero => intro s s' h; rw [execBlock] at h; exact absurd h (by simp)
  | succ n ih =>
    intro s s' h
    rw [execBlock] at h
    cases hgi : getInstruction bb s.instIdx with
    | none => rw [hgi] at h; simp at h
    | some inst =>
      rw [hgi] at h; simp only [] at h
      have hmem : inst ∈ bb.instructions := by
        unfold getInstruction at hgi
        split at hgi
        · injection hgi with hh; subst hh; exact List.get_mem _ _
        · exact absurd hgi (by simp)
      cases hst : stepInstBase inst s with
      | OK s2 =>
        rw [hst] at h; simp only [] at h
        by_cases hterm : isTerminator inst.opcode
        · rw [if_pos hterm] at h
          by_cases hh : s2.halted
          · rw [if_pos hh] at h; simp at h
          · rw [if_neg hh] at h
            injection h with hs'; subst hs'
            have hsucc := stepInstBase_term_currentBb_mem_succs hterm hst
            have hlast := hwf inst hmem hterm
            have hne : bb.instructions ≠ [] := by
              intro hnil; rw [hnil] at hmem; simp at hmem
            have hbs : bbSuccs bb = (getSuccessors bb.instructions.getLast!).reverse.dedup := by
              unfold bbSuccs
              cases hins : bb.instructions with
              | nil => exact absurd hins hne
              | cons a r => simp only [hins]
            rw [hbs, ← hlast]
            simp [List.mem_dedup, List.mem_reverse, hsucc]
        · rw [if_neg hterm] at h
          exact ih _ _ h
      | IntRet _ _ => rw [hst] at h; simp at h
      | Halt _ => rw [hst] at h; simp at h
      | Abort _ _ => rw [hst] at h; simp at h
      | Error e =>
        rw [hst] at h; simp only [] at h
        by_cases hinv : inst.opcode = Opcode.INVOKE
        · rw [if_pos hinv] at h
          cases hsi : stepInvoke n ctx inst s with
          | OK s2 => rw [hsi] at h; simp only [] at h; exact ih _ _ h
          | IntRet _ _ => rw [hsi] at h; simp at h
          | Halt _ => rw [hsi] at h; simp at h
          | Abort _ _ => rw [hsi] at h; simp at h
          | Error _ => rw [hsi] at h; simp at h
        · rw [if_neg hinv] at h
          by_cases hext : isExternalCall inst.opcode
          · rw [if_pos hext] at h
            cases hse : stepExternalCall subEvmFuel inst s with
            | some s2 => rw [hse] at h; simp only [] at h; exact ih _ _ h
            | none => rw [hse] at h; simp at h
          · rw [if_neg hext] at h; simp at h

/-- **The Entry invariant: the Venom walk never leaves the reachable CFG.** If the walk is at a
    reachable block `bb` and `runBlock` hands control on, the next block is reachable too. `runBlock`
    is `evalPhis` followed by `execBlock`, so this is `execBlock_OK_currentBb_mem_bbSuccs` plus the
    `bbSuccs`/`cfgAnalyze` bridge, closed under `CfgReach.step`.

    This is what lets a per-block `hstep` *assume* `CfgReach entry.label bb.label` — the hypothesis the
    whole `_reach` hstep family takes — rather than having the caller re-establish it at every block. -/
theorem CfgReach_of_runBlock {fn : IrFunction} {ctx : VenomContext} {bb : BasicBlock}
    {fuel : Nat} {s s' : VenomState} {entryLbl : String}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hmem : bb ∈ fn.blocks)
    (hwf : ∀ inst ∈ bb.instructions, isTerminator inst.opcode = true →
        inst = bb.instructions.getLast!)
    (hreach : CfgReach (cfgAnalyze fn) entryLbl bb.label)
    (hrb : runBlock fuel ctx bb s = ExecResult.OK s') :
    CfgReach (cfgAnalyze fn) entryLbl s'.currentBb := by
  have hexec : ∃ sPhi : VenomState, execBlock fuel ctx bb
      { sPhi with instIdx := phiPrefixLength bb.instructions } = ExecResult.OK s' := by
    rw [runBlock] at hrb
    cases hp : evalPhis s bb.instructions with
    | OK sPhi => rw [hp] at hrb; simp only [] at hrb; exact ⟨sPhi, hrb⟩
    | IntRet _ _ => rw [hp] at hrb; simp at hrb
    | Halt _ => rw [hp] at hrb; simp at hrb
    | Abort _ _ => rw [hp] at hrb; simp at hrb
    | Error _ => rw [hp] at hrb; simp at hrb
  obtain ⟨sPhi, hexec⟩ := hexec
  have hbs := execBlock_OK_currentBb_mem_bbSuccs hwf fuel _ s' hexec
  exact CfgReach.step hreach (by rw [cfgAnalyze_succsOf_of_mem hnd hmem]; exact hbs)


/-- **Prefix + clean-stack + body simulation (HSVP).** The `toPop ≠ []` counterpart of
    `genBlockPrefixBodyHSVP_sim_inv`, which assumes the block's clean-stack prologue away.

    A block's plan is `SOLabel :: cleanOps ++ bodyOps ++ termOps`, and `cleanOps` is non-empty exactly
    at a join that genuinely drops values (one predecessor, that predecessor branches, and some variable
    live at its exit is not an input here). This runs the whole prologue — `soLabel_sim` over the
    JUMPDEST, then `popmanyPlan_sim_closed` over the pops — and hands the body its *real* starting
    point: pc `as0.pc + 1 + (executePlan cleanOps).length`, plan state `ps2`.

    The Venom state is untouched by the prologue, so `execBodyThread` still runs from `vs0`: `popmanyPlan`
    discards only *dead* variables, and Venom keeps every variable in `vars` whether or not it is on the
    operand stack. The body's invariants (`hsd2`/`hsv2`/`hspM2`) are stated at `ps2` — where the body
    fold actually begins — and transported across the prologue's asm run by `StackDiscHS.rebuild`.
    Taking `cleanOps = []`, `ps2 = ps0` recovers `genBlockPrefixBodyHSVP_sim_inv`. -/
theorem genBlockPrefixCleanBodyHSVP_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (lg : List ((Instruction × Nat) × List String))
    (front : List Instruction) (S0 : List String) (M0 : AssocList Operand Nat)
    (toPop : List Operand) (cleanOps : List StackOp)
    (ps0 ps2 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
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
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1))) :
    ∃ as', runAsm (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
              (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd as' ∧
           as'.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length ∧
           StackDiscHS P (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 sEnd as' ∧
           StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  -- `a ++ b ++ c` is `(a ++ b) ++ c`: the prologue is the left factor, the body the right
  rw [executePlan_append] at hblock
  obtain ⟨hpre, hbody⟩ := asmBlockAt_append hblock
  obtain ⟨as1, h1run, h1rel, h1pc⟩ :=
    blockPrologue_prefix_sim (lo := lo) (prog := prog) (l := l) hrel0 hpop hshallow hlenPop hpre
  have hsd1 : StackDiscHS (totalGain lg + P) ps2 vs0 as1 :=
    hsd2.rebuild (runAsm_memory_size_mono h1run) (fun _ _ h => h) hsd2.shallow hsd2.defined
  have hbody' : asmBlockAt prog as1.pc
      (executePlan (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1) := by
    rw [h1pc]; exact hbody
  obtain ⟨as', h2run, h2rel, h2pc, h2sd, h2sv⟩ :=
    genBlockBody_sim_inv_HSVP P gp lg S0 M0 ps2 vs0 as1 hready hsd1 hsv2 hspM2 h1rel hbody'
  have hveq : lg.foldl (fun v x => gvBodyStep x.1 v) vs0 = sEnd := by
    have h1 : lg.foldl (fun v x => gvBodyStep x.1 v) vs0
        = (lg.map Prod.fst).foldl (fun v x => gvBodyStep x v) vs0 := by
      rw [List.foldl_map]
    rw [h1, hfront]
    exact execBodyThread_eq_gvFold front 0 vs0 sEnd hthread
  rw [hveq] at h2rel h2sd
  obtain ⟨hrun, hrel, hpc⟩ := plan_seq_sim' h1run h1pc h2run h2rel h2pc
  exact ⟨as', hrun, hrel, hpc, h2sd, h2sv⟩



/-- **Spill-aware JMP entry segment *through* a clean-stack prologue.** The `toPop ≠ []` counterpart of
    `hasm_regularHSVP_jmp`: identical except that the block's asm is
    `[JUMPDEST] ++ cleanAsm ++ bodyAsm ++ [push-label ; JUMP]`, so `bodyLen` counts the pops too and the
    body fold runs from the post-pop plan state `ps2`.

    Everything downstream is unchanged — the terminator lands at `as0.pc + bodyLen` exactly as before,
    because `bodyLen` is *defined* as the length of the prologue-and-body asm. That is the whole content
    of the "pc arithmetic shift": it is absorbed into `bodyLen`, and no jump-target lemma needs touching.
    Taking `cleanOps = []`, `ps2 = ps0` recovers `hasm_regularHSVP_jmp`. -/
theorem hasm_regularHSVP_jmp_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
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
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (bodyLen + 2) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
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
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hpush' : prog.get ⟨asMid.pc, hpc1'⟩ = resolveInst lo (AsmInst.AsmPushLabel target) :=
    prog_get_transfer hbpc hpush
  have hpc2' : asMid.pc + 1 < prog.length := by rw [hbpc]; exact hpc2
  have hjump' : prog.get ⟨asMid.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hbpc]) hjump
  have hjrun : runAsm 2 offsetToPc prog asMid = AsmResult.AsmOK { asMid with pc := idx } :=
    resolved_jump_sim hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk
  refine ⟨{ asMid with pc := idx }, ?_, venomAsmRel_setPc hbrel, rfl,
    hbsd.rebuild (Nat.le_refl _) (fun _ _ h => h) hbsd.shallow hbsd.defined, hbsv⟩
  rw [runAsm_add_ok hbrun]; exact hjrun



/-- **Spill-aware per-block JMP simulation *through* a clean-stack prologue.** The `toPop ≠ []`
    counterpart of `genBlockSimulation_regularHSVP_jmp` — the block-level statement a per-block `hstep`
    consumes, now available at a join that genuinely drops values.

    The Venom side is completely unchanged (`runBlock … = OK (jumpTo target sEnd)`): the prologue is
    invisible to Venom, since it only discards dead variables. The asm side runs
    `[JUMPDEST] ++ cleanAsm ++ bodyAsm ++ [push-label ; JUMP]`, and the body fold runs from the post-pop
    state `ps2`. Taking `cleanOps = []`, `ps2 = ps0` recovers the original. -/
theorem genBlockSimulation_regularHSVP_jmp_clean
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat} (P : Nat)
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
    (hvs0 : vs0 = { vs0 with instIdx := 0 }) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo target sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 2) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧ asMid.pc = idx ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2
        (jumpTo target sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2
        (jumpTo target sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo target sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jmp_clean (vs0 := vs0) (target := target) P hfront hready hsd2 hsv2 hspM2 hrel0
      hthread hpop hshallow hlenPop hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩



/-- **Aligned-JMP block plan, clean-stack prologue kept.** The `toPop ≠ []` counterpart of
    `generateBlockPlan_aligned_jmp`: the block plan is
    `SOLabel :: cleanOps ++ bodyOps ++ [SOPushLabel target ; SOEmit "JUMP"]`, with the body fold running
    from the *post-pop* state `ps2`. Setting `cleanOps = []`, `ps2 = ps` recovers the original. -/
theorem generateBlockPlan_aligned_jmp_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) →
        blockOps = StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++
          [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] ∧ ps' = ps_body) := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, termOps, hclean, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term_clean L D C fn bb ps blockOps ps' front term hentry hnp hplan
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide)
      (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide) (by rw [hterm_jmp]; decide),
      generateRegularInstPlan_jmp_full hterm_jmp hterm_ops hterm_outs hjoin hsp] at hterm_step
  obtain ⟨htops, hps'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hterm_step
  exact ⟨by rw [hblk, ← htops], hps'.symm⟩

/-- **Whole-program asm structure of an aligned-JMP block *with* its clean-stack prologue.** The
    `toPop ≠ []` counterpart of `blockplan_aligned_jmp_prog_asm`: the block's asm is
    `[JUMPDEST] ++ cleanAsm ++ bodyAsm ++ [AsmPushLabel target ; JUMP]`. The pops sit inside the block's
    own segment, so the surrounding decomposition — and hence every jump-target and `pcOfLabel` fact
    downstream — is structurally unchanged. -/
theorem blockplan_aligned_jmp_prog_asm_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP)
    (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
            ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, himp⟩ :=
    generateBlockPlan_aligned_jmp_clean L D C fn bb ps_in blockOps ps' front term target hentry0 hnp
      hterm_jmp hterm_ops hterm_outs hjoin hgbp
  have hspill : ps_body.spilled = ([] : AssocList Operand Nat) := by
    rcases hclean with ⟨_, hcs⟩ | ⟨_, hce, hps2⟩
    · exact hnospill cleanOps ps2 bodyOps ps_body hcs hbody
    · subst hps2; exact hnospill0 bodyOps ps_body hbody
  obtain ⟨hblockOpsEq, _⟩ := himp hspill
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockOpsEq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: cleanOps ++ bodyOps
        ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"]
      = [StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)
        ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] := by
    simp [List.append_assoc]
  rw [heq, executePlan_aligned_jmp_block]



/-- **Asm layout of an aligned-JMP block *with* its clean-stack prologue.** The `toPop ≠ []` counterpart
    of `blockplan_aligned_jmp_layout`: the block's asm segment is `[JUMPDEST] ++ cleanAsm ++ bodyAsm`,
    sitting at `pc = (executePlan preOps).length`, and the terminator's `push-label ; JUMP` follows it.

    Note the shape of the conclusion: the pops are absorbed into the segment `[SOLabel] ++ (cleanOps ++
    bodyOps)`, so the push/jump offsets are still "segment length" and "segment length + 1". That is why
    no jump-target lemma downstream needed rewriting — the pc shift the prologue causes is entirely
    internal to the block's own segment. -/
theorem blockplan_aligned_jmp_layout_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
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
      (∃ h : (executePlan preOps).length
              + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length
            + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length]'h
          = resolveInst (computeLabelOffsets (executePlan ops)).2 (AsmInst.AsmPushLabel target)) ∧
      (∃ h : (executePlan preOps).length
              + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 1
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length
            + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length + 1]'h
          = AsmInst.AsmOp "JUMP") := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hprog⟩ :=
    blockplan_aligned_jmp_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      target hentry0 hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp hseg hnospill hnospill0
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
        ++ ([AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      ([AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps)
      (fun a ha lbl => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).2 lbl d)
  · have hpre : executePlan ops
        = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := (aligned_jmp_tail_resolved
      (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      (executePlan tailOps) target).1
    simpa [List.length_append] using this
  · have hpre : executePlan ops
        = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := (aligned_jmp_tail_resolved
      (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      (executePlan tailOps) target).2
    simpa [List.length_append] using this



/-- **`pcOfLabel` of an aligned-JMP block with a clean-stack prologue.** *Identical statement* to
    `pcOfLabel_aligned_jmp_block` — the block's label still sits at `(executePlan preOps).length`.

    That is the point: the clean-stack pops come *after* the JUMPDEST, inside the block's own segment,
    so they move the body but not the block's entry pc. Every `pcOfLabel`-based fact — the whole
    jump-target family, the canonical `pcOf` schedule — is therefore untouched by the prologue. -/
theorem pcOfLabel_aligned_jmp_block_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (target : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions (liveVarsAt L target 0) = [])
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, _hclean, _hbody, hprog⟩ :=
    blockplan_aligned_jmp_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front term
      target hentry0 hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp hseg hnospill hnospill0
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
      = AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps) := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps)
        ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan (cleanOps ++ bodyOps) ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"]
            ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]



/-! ### Clean-stack prologue: the bare-halting (STOP / INVALID) family

Exactly the JMP story, transposed: the pops sit after the JUMPDEST inside the block's own segment, so
`pcOfLabel` is unmoved and the terminal `AsmOp name` still lands at "segment length". -/

/-- Aligned bare-halting block plan with a clean-stack prologue: `SOLabel :: cleanOps ++ bodyOps ++
    [SOEmit name]`, body fold from the post-pop state. -/
theorem generateBlockPlan_aligned_bareHalt_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) (blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = [])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan L D C fn bb ps = some (blockOps, ps')) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      (ps_body.spilled = ([] : AssocList Operand Nat) →
        blockOps = StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++ [StackOp.SOEmit name] ∧
        ps' = ps_body) := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, termOps, hclean, hbody, hterm_step, hblk⟩ :=
    generateBlockPlan_split_term_clean L D C fn bb ps blockOps ps' front term hentry hnp hplan
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, fun hsp => ?_⟩
  rw [generateInstPlan_regular_eq hterm_reg.1 hterm_reg.2.1 hterm_reg.2.2.1 hterm_reg.2.2.2.1
      hterm_reg.2.2.2.2,
      generateRegularInstPlan_bareHalt_full hname hterm_ops hterm_outs hsp] at hterm_step
  obtain ⟨htops, hps'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hterm_step
  exact ⟨by rw [hblk, ← htops], hps'.symm⟩

/-- Whole-program asm of a bare-halting block with a clean-stack prologue. -/
theorem blockplan_aligned_bareHalt_prog_asm_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat)) :
    ∃ cleanOps ps2 bodyOps ps_body,
      ((C.predsOf bb.label).length = 1 ∧ cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) ∨
       (C.predsOf bb.label).length ≠ 1 ∧ cleanOps = [] ∧ ps2 = ps_in) ∧
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) ∧
      executePlan ops
        = executePlan preOps ++ (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
            ++ [AsmInst.AsmOp name]) ++ executePlan tailOps := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, himp⟩ :=
    generateBlockPlan_aligned_bareHalt_clean L D C fn bb ps_in blockOps ps' front term name hentry0 hnp
      hname hterm_ops hterm_outs hterm_reg hgbp
  have hspill : ps_body.spilled = ([] : AssocList Operand Nat) := by
    rcases hclean with ⟨_, hcs⟩ | ⟨_, hce, hps2⟩
    · exact hnospill cleanOps ps2 bodyOps ps_body hcs hbody
    · subst hps2; exact hnospill0 bodyOps ps_body hbody
  obtain ⟨hblockOpsEq, _⟩ := himp hspill
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_⟩
  rw [hseg, executePlan_append, executePlan_append, hblockOpsEq]
  congr 2
  have heq : StackOp.SOLabel bb.label :: cleanOps ++ bodyOps ++ [StackOp.SOEmit name]
      = [StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps) ++ [StackOp.SOEmit name] := by
    simp [List.append_assoc]
  rw [heq, executePlan_aligned_bareHalt_block]

/-- Asm layout of a bare-halting block with a clean-stack prologue. -/
theorem blockplan_aligned_bareHalt_layout_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
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
      (∃ h : (executePlan preOps).length
              + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length
              < (asmResolve (executePlan ops)).1.length,
        (asmResolve (executePlan ops)).1[(executePlan preOps).length
            + (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))).length]'h
          = AsmInst.AsmOp name) := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, hprog⟩ :=
    blockplan_aligned_bareHalt_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front
      term name hentry0 hnp hname hterm_ops hterm_outs hterm_reg hgbp hseg hnospill hnospill0
  refine ⟨cleanOps, ps2, bodyOps, ps_body, hclean, hbody, ?_, ?_⟩
  · have hAIB : executePlan ops = executePlan preOps
        ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
        ++ ([AsmInst.AsmOp name] ++ executePlan tailOps) := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hAIB]
    exact asmBlockAt_resolved_of_middle_no_label (executePlan preOps)
      (executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      ([AsmInst.AsmOp name] ++ executePlan tailOps)
      (fun a ha lbl => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).1 lbl)
      (fun a ha lbl d => (hlblfree cleanOps ps2 bodyOps ps_body hbody a ha).2 lbl d)
  · have hpre : executePlan ops
        = (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
        ++ [AsmInst.AsmOp name] ++ executePlan tailOps := by
      rw [hprog]; simp only [List.append_assoc]
    rw [hpre]
    have := aligned_bareHalt_tail_resolved
      (executePlan preOps ++ executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps)))
      (executePlan tailOps) name
    simpa [List.length_append] using this

/-- `pcOfLabel` of a bare-halting block with a clean-stack prologue — *identical statement* to the
    `CleanTrivial` version: the pops follow the JUMPDEST, so the block's entry pc is unmoved. -/
theorem pcOfLabel_aligned_bareHalt_block_clean
    (L : DfState (List String)) (D : DfgAnalysis) (C : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps_in : PlanState) (ops preOps tailOps blockOps : List StackOp) (ps' : PlanState)
    (front : List Instruction) (term : Instruction) (name : String)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hgbp : generateBlockPlan L D C fn bb ps_in = some (blockOps, ps'))
    (hseg : ops = preOps ++ blockOps ++ tailOps)
    (hnospill : ∀ cleanOps ps2 bodyOps ps_body,
      cleanStackPlan L C fn bb ps_in = (cleanOps, ps2) →
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps2)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hnospill0 : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF L D C fn bb) (some ([], ps_in)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hpreuniq : ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label) :
    pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length := by
  obtain ⟨cleanOps, ps2, bodyOps, ps_body, _hclean, _hbody, hprog⟩ :=
    blockplan_aligned_bareHalt_prog_asm_clean L D C fn bb ps_in ops preOps tailOps blockOps ps' front
      term name hentry0 hnp hname hterm_ops hterm_outs hterm_reg hgbp hseg hnospill hnospill0
  rw [pcOfLabel_asmResolve, hprog]
  have hlb : executePlan ([StackOp.SOLabel bb.label] ++ (cleanOps ++ bodyOps))
      = AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps) := by
    rw [executePlan_append]; simp [executePlan, execStackOp]
  rw [hlb]
  have hshape : executePlan preOps ++ (AsmInst.AsmLabel bb.label :: executePlan (cleanOps ++ bodyOps)
        ++ [AsmInst.AsmOp name]) ++ executePlan tailOps
      = executePlan preOps ++ AsmInst.AsmLabel bb.label ::
          (executePlan (cleanOps ++ bodyOps) ++ [AsmInst.AsmOp name] ++ executePlan tailOps) := by
    simp [List.append_assoc]
  rw [hshape, pcOfLabel_of_decomp _ _ _ hpreuniq]



/-- Spill-aware residual STOP segment *through* a clean-stack prologue — the `toPop ≠ []`
    counterpart of `hasm_regularHSVP_stop`. Only the prologue changes: the body fold runs from the
    post-pop state `ps2`, and `bodyLen` (defined as the prologue-and-body asm length) absorbs the pops,
    so the terminal op still lands at `as0.pc + bodyLen`. -/
theorem hasm_regularHSVP_stop_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen budget : Nat}
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState sEnd) as'  := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, _, _⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := prog_get_transfer hbpc hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog as0 = AsmResult.AsmHalt (asmNext asMid) := by
    rw [runAsm_append_ok hbrun]; exact runAsm_stop 0 hpc' hget'
  exact ⟨asmNext asMid, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         venomAsmRel_terminal lo _ sEnd asMid hbrel⟩

/-- Spill-aware residual INVALID segment *through* a clean-stack prologue — the `toPop ≠ []`
    counterpart of `hasm_regularHSVP_invalid`. Only the prologue changes: the body fold runs from the
    post-pop state `ps2`, and `bodyLen` (defined as the prologue-and-body asm length) absorbs the pops,
    so the terminal op still lands at `as0.pc + bodyLen`. -/
theorem hasm_regularHSVP_invalid_clean {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen budget : Nat}
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel (haltState (setReturndata ByteArray.empty sEnd)) as'  := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, _, _⟩ :=
    genBlockPrefixCleanBodyHSVP_sim_inv P l gp lg front S0 M0 toPop cleanOps ps0 ps2 vs0 sEnd as0
      hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "INVALID" := prog_get_transfer hbpc hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog as0
      = AsmResult.AsmFault { asmNext asMid with returndata := ByteArray.empty } := by
    rw [runAsm_append_ok hbrun]; exact runAsm_invalid 0 hpc' hget'
  obtain ⟨hacc, htr, _, hlog⟩ := venomAsmRel_terminal lo _ sEnd asMid hbrel
  exact ⟨{ asmNext asMid with returndata := ByteArray.empty },
         runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         ⟨hacc, htr, rfl, hlog⟩⟩

end EvmYul.Venom.Hol.Codegen

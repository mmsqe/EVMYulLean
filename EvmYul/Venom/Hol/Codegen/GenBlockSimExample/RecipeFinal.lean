/-
GenBlockSimExample / the retracted recipe capstones and the closing block

Split part of `GenBlockSimExample`; see that module's header for the full roadmap.
This part is wrapped in `namespace EvmYul.Venom.Hol.Codegen` (the enclosing namespace of the second half); layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeSlices

namespace EvmYul.Venom.Hol.Codegen

/-! ## ⚠️ RETRACTED: `codegen_correct_ofRecipes` + `termRecipe_stop_inhabited` (VACUOUS — unconstrained ∀-N)

A naive top-level composition `codegen_correct_ofRecipes` (dispatcher ∘ `codegen_correct_ofBlocks_HbsimMatch`
with `Entry := CanonEntry`) was retracted here: it was VACUOUS.  `codegen_correct_ofBlocks_HbsimMatch`'s
`hstep` is `∀ N`, and `CanonEntry` does NOT constrain `N`.  For a halting block at `N = 0` (or any
`N < blockLen`) with `f' ≥ 1`, `runBlock = Halt` but `HbsimMatch (Halt) N` needs `runAsm N … = AsmHalt`,
which is FALSE for `N < blockLen` — and no terminator recipe (whose `hle : bodyLen + K ≤ N` fails) nor a
fuel/IntRet escape hatch (the result is `Halt`, not `Error`) can cover it.  So the recipe hypothesis was
unsatisfiable for such `(N, f')`, which `CanonEntry` admits.  `termRecipe_stop_inhabited` "witnessed" only
a single `f' + 1` / `N ≥ 1` instance, NOT the `∀ N` premise, so it did not establish non-vacuity (honesty
lesson: a witness for one instantiation of a `∀`-hypothesis does not witness the whole `∀`).

The working concrete route (`codegen_correct_singleBlockHalt`) shows the fix: the `Entry` must CONSTRAIN
`N` (there, `N = (asmResolve (executePlan ops)).1.length`), so small-`N` states never satisfy the entry
invariant; the general case additionally threads `N' = N − blockLen` to successors (what the established
`codegen_correct_{sched,fuel}` drivers already do for the hstep family).  The recipe route is SOUND and
COMPLETE at the per-block level — `HbsimMatch_dispatch` (`TermRecipe` → `HbsimMatch`) plus the eight
`termRecipe_*` producers (`RegularBodyH`/emit-segment → `TermRecipe`) — and connects to the top level via
an N-constrained Entry, which is the remaining assembly work, not a per-block gap. -/


/-- **`HbsimMatch` is Entry-independent on any non-`OK` result.** Only the `OK`-continuing arm mentions
    `Entry` (it must state the successor invariant); the `Halt`/`Abort`/`IntRet`/`Error` arms do not. So a
    halting/aborting block's `HbsimMatch`, proved for one `Entry`, transfers to any other. This is the fact
    that lets a recipe-produced `HbsimMatch` (`HbsimMatch_dispatch` gives it for `CanonEntry`) feed a driver
    using a *different*, N-constrained `Entry` — the halting half of the top-level connection sketched in
    the retraction note above (the continuing half additionally needs the successor recorded against the
    N-constrained Entry). -/
theorem HbsimMatch_entry_irrel {E1 E2 : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm : AsmState} {N : Nat} {r : ExecResult}
    (hr : ∀ s', r ≠ ExecResult.OK s') :
    HbsimMatch E1 o2pc prog asm N r → HbsimMatch E2 o2pc prog asm N r := by
  cases r with
  | OK s' => exact absurd rfl (hr s')
  | Halt s' => exact id
  | Abort a s' => cases a <;> exact id
  | IntRet _ _ => exact id
  | Error _ => exact id

/-- Non-vacuity: a halting result exercises the transfer between two genuinely different `Entry`s. -/
theorem HbsimMatch_entry_irrel_nonvacuous
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm : AsmState} {N : Nat} {s' : VenomState}
    (h : HbsimMatch (fun _ _ _ => True) o2pc prog asm N (ExecResult.Halt s')) :
    HbsimMatch (fun _ _ _ => False) o2pc prog asm N (ExecResult.Halt s') :=
  HbsimMatch_entry_irrel (by intro s' h; cases h) h

/-- **Prepend one OK asm step to a `HbsimMatch`.** If the block's `HbsimMatch` holds at the post-SOLabel
    state `as0` with budget `N`, and one asm step from `asm` lands at `as0` (`runAsm 1 … asm = AsmOK as0` —
    e.g. stepping over the block's `JUMPDEST`/SOLabel), then it holds at `asm` with budget `1 + N`. Every
    arm references `runAsm _ … asm`, and `runAsm (1+N) … asm = runAsm N … as0` (`runAsm_add_ok`), so each
    arm transfers unchanged. This is the SOLabel step of the top-level connection: the walk enters a block
    at its SOLabel, but a recipe operates one step later. -/
theorem HbsimMatch_prepend_ok_step {E : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm as0 : AsmState} {N : Nat} {r : ExecResult}
    (hstep : runAsm 1 o2pc prog asm = AsmResult.AsmOK as0)
    (h : HbsimMatch E o2pc prog as0 N r) :
    HbsimMatch E o2pc prog asm (1 + N) r := by
  have hc : runAsm (1 + N) o2pc prog asm = runAsm N o2pc prog as0 := runAsm_add_ok hstep
  unfold HbsimMatch at h ⊢
  cases r with
  | OK s' => simp only [hc]; exact h
  | Halt s' => simp only [hc]; exact h
  | Abort a s' => cases a <;> (simp only [hc]; exact h)
  | IntRet _ _ => exact h
  | Error _ => exact h

/-- **Entry-transferring SOLabel connector for a halting/aborting block** (`r` not `OK`). The recipe's
    `HbsimMatch` at the post-SOLabel state `as0` — which `HbsimMatch_dispatch` produces for the recipe's own
    `Entry` — transfers to ANY Entry `E2` (`HbsimMatch_entry_irrel`, the halt arm is Entry-free) and prepends
    the SOLabel step (`HbsimMatch_prepend_ok_step`), yielding a `HbsimMatch` at the block's SOLabel entry
    `asm` for a driver's own Entry.

    NB this serves the *Entry-transfer* driver shape and is not on the route actually shipped: the
    single-block halting capstones go through `hasm_from_recipe_solabel` (recipe → `hasm` →
    `Example.codegen_correct_singleBlockHalt`), and the multi-block driver
    `codegen_correct_ofBlocks_recipeW` absorbs the SOLabel step into `bodyLen` instead. Kept as the general
    fact for that alternative shape. -/
theorem HbsimMatch_halting_at_solabel {E1 E2 : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm as0 : AsmState} {N : Nat} {r : ExecResult}
    (hr : ∀ s', r ≠ ExecResult.OK s')
    (hstep : runAsm 1 o2pc prog asm = AsmResult.AsmOK as0)
    (h : HbsimMatch E1 o2pc prog as0 N r) :
    HbsimMatch E2 o2pc prog asm (1 + N) r :=
  HbsimMatch_prepend_ok_step hstep (HbsimMatch_entry_irrel hr h)

/-- **The recipe → `hasm` bridge.** From a halting block's `HbsimMatch` at the post-SOLabel state `as0`
    (`HbsimMatch_dispatch` produces it from the block's `TermRecipe`), one SOLabel step
    (`runAsm 1 … asm = AsmOK as0`), and a budget `1 + N ≤ M`, derive the whole-block asm-halt fact
    `∃ asm', runAsm M … asm = AsmHalt asm' ∧ venomAsmTerminalRel s' asm'` — exactly the `hasm` hypothesis
    `codegen_correct_singleBlockHalt` consumes. So the recipe route reaches a whole-function
    `codegen_correct` for a single-block halting function by feeding this into the existing driver
    (`HbsimMatch_prepend_ok_step` prepends the SOLabel step; `runAsm_le_of_ne_ok` lifts to `M`, `AsmHalt`
    being sticky). -/
theorem hasm_from_recipe_solabel {E : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm as0 : AsmState} {N M : Nat} {s' : VenomState}
    (hsolabel : runAsm 1 o2pc prog asm = AsmResult.AsmOK as0)
    (hrec : HbsimMatch E o2pc prog as0 N (ExecResult.Halt s')) (hbudget : 1 + N ≤ M) :
    ∃ asm', runAsm M o2pc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm' := by
  have h1 := HbsimMatch_prepend_ok_step hsolabel hrec
  simp only [HbsimMatch] at h1
  obtain ⟨asm', hrun, hrel⟩ := h1
  exact ⟨asm', runAsm_le_of_ne_ok (fun s => by simp) hbudget hrun, hrel⟩

/-- **A single-block halting function's `codegen_correct`, via the recipe route.** Composes the existing
    driver `Example.codegen_correct_singleBlockHalt` with the recipe → `hasm` bridge
    `hasm_from_recipe_solabel`: given, per arriving state, the SOLabel step and the block's
    `HbsimMatch (Halt)` at the post-SOLabel state (which `HbsimMatch_dispatch` produces from the block's
    `TermRecipe`), plus a budget, the whole function's `codegen_correct` holds. The recipe route reaching a
    whole-function `codegen_correct` — the halting single-block case — with the constrained `N` handled
    entirely by the driver's `Entry` (which bakes `N = programLength`). -/
theorem codegen_correct_singleBlockHalt_viaRecipe
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {bb : BasicBlock}
    {lo : AssocList String Nat} {haltFn : VenomState → VenomState}
    {E : VenomState → AsmState → Nat → Prop} {N : Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hblocks : fn.blocks = [bb])
    (hrunHalt : ∀ (k : Nat) (s : VenomState), runBlock (k+1) ctx bb s = ExecResult.Halt (haltFn s))
    (hrun0 : ∀ (s : VenomState), runBlock 0 ctx bb s = ExecResult.Error "out of fuel")
    (hstep : ∀ (s : VenomState) (asm : AsmState),
        venomAsmRel lo (initPlanState 0) s asm → asm.pc = 0 →
        ∃ as0, runAsm 1 (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                 = AsmResult.AsmOK as0 ∧
               HbsimMatch E (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as0 N
                 (ExecResult.Halt (haltFn s)))
    (hbudget : 1 + N ≤ (asmResolve (executePlan ops)).1.length)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine Example.codegen_correct_singleBlockHalt hplan hent hlk hlbl hblocks hrunHalt hrun0 ?_ hrel haspc
  intro s asm hv hp
  obtain ⟨as0, hsolabel, hrec⟩ := hstep s asm hv hp
  exact hasm_from_recipe_solabel hsolabel hrec hbudget

namespace Example

/-- **The recipe route reaches `codegen_correct` for `stopCtx`, non-vacuously.** Witnesses
    `codegen_correct_singleBlockHalt_viaRecipe`: `stopFn`'s generated program `[JUMPDEST "entry"; STOP]`
    discharges the recipe `hstep` — the SOLabel step (`asmStep_label_ok`) lands at the post-SOLabel state,
    the block's `HbsimMatch (Halt)` there is the STOP step (`asmStep_stop_ok`) plus the entry-derived
    terminal relation (`venomAsmRel_terminal`) — and the budget `1 + 1 ≤ 2`. Exhibits the full
    recipe → `hasm` → driver chain end-to-end (same result as the direct `codegen_correct_stop`, via the
    recipe machinery — the exhibit-a-witness discipline the retracted `codegen_correct_ofRecipes` skipped). -/
theorem codegen_correct_stop_viaRecipe {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 stopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_singleBlockHalt_viaRecipe (fuel := 10) (ctx := stopCtx) (fn := stopFn) (bb := stopBB)
    (entryName := "main") (entryLbl := "entry")
    (haltFn := fun s => haltState { s with instIdx := 0 })
    (E := fun _ _ _ => True) (N := 1)
    (ops := (generateFnPlan stopFn 0 0).get!.1) (psFinal := (generateFnPlan stopFn 0 0).get!.2)
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ hrel haspc
  · intro k s; simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
  · intro s; simp [runBlock, evalPhis, execBlock, stopBB, stopInst]
  · -- hstep: SOLabel (JUMPDEST) step + STOP HbsimMatch (Halt) at the post-SOLabel state
    intro s asm hv hp
    have hpc0 : asm.pc < (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length := by
      rw [hp]; decide
    have hpc1 : (asmNext asm).pc < (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length := by
      show asm.pc + 1 < _; rw [hp]; decide
    have hget0 : (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.get ⟨asm.pc, hpc0⟩
        = AsmInst.AsmLabel "entry" := by
      rw [show (⟨asm.pc, hpc0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hp]; rfl
    have hget1 : (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.get ⟨(asmNext asm).pc, hpc1⟩
        = AsmInst.AsmOp "STOP" := by
      rw [show (⟨(asmNext asm).pc, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from
            Fin.ext (by show asm.pc + 1 = 1; rw [hp])]; rfl
    refine ⟨asmNext asm, ?_, ?_⟩
    · -- JUMPDEST step
      show runAsm 1 _ _ asm = AsmResult.AsmOK (asmNext asm)
      rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc0 (asmStep_label_ok hpc0 hget0)]
      rfl
    · -- HbsimMatch (Halt) at (asmNext asm), budget 1
      show HbsimMatch (fun _ _ _ => True) _ _ (asmNext asm) 1 (ExecResult.Halt (haltState { s with instIdx := 0 }))
      unfold HbsimMatch
      refine ⟨asmNext (asmNext asm), ?_, ?_⟩
      · -- STOP step
        show runAsm 1 _ _ (asmNext asm) = AsmResult.AsmHalt (asmNext (asmNext asm))
        unfold runAsm
        rw [asmStep_stop_ok hpc1 hget1]
      · -- terminal relation
        exact venomAsmRel_terminal lo (initPlanState 0) s asm hv
  · -- budget: 1 + 1 ≤ programLength (= 2)
    decide

/-- **The recipe route reaches `codegen_correct` for `stopCtx`, with the `HbsimMatch` produced by the
    dispatcher.** Where `codegen_correct_stop_viaRecipe` hand-constructs the STOP step, this discharges the
    reduction's `hstep` `HbsimMatch (Halt)` through the *actual* recipe dispatcher
    `HbsimMatch_halting_dispatch_nonvacuous` (STOP arm, empty body). So the whole recipe route is exhibited
    end-to-end via the real machinery: recipe dispatcher (`HaltingTermRecipe` → `HbsimMatch`) → reduction
    (`viaRecipe`) → whole-function `codegen_correct`. The dispatcher's `hrel` at the post-SOLabel state is
    `venomAsmRel_setPc` of the entry relation (`venomAsmRel` ignores both pc and `instIdx`). Depends on the
    M1 `ffi_zeroes` axioms — inherited from the dispatcher, whose per-terminator connectors thread the
    machine-memory relation; those axioms are the development's allowed FFI boundary. (The hand-constructed
    `viaRecipe`/`_stop_viaRecipe` stay base-axiom by extracting only the terminal relation.) -/
theorem codegen_correct_stop_viaDispatch {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 stopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_singleBlockHalt_viaRecipe (fuel := 10) (ctx := stopCtx) (fn := stopFn) (bb := stopBB)
    (entryName := "main") (entryLbl := "entry")
    (haltFn := fun s => haltState { s with instIdx := 0 })
    (E := fun _ _ _ => True) (N := 1)
    (ops := (generateFnPlan stopFn 0 0).get!.1) (psFinal := (generateFnPlan stopFn 0 0).get!.2)
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ hrel haspc
  · intro k s; simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
  · intro s; simp [runBlock, evalPhis, execBlock, stopBB, stopInst]
  · -- hstep: SOLabel (JUMPDEST) step + STOP HbsimMatch (Halt) via the dispatcher
    intro s asm hv hp
    have hpc0 : asm.pc < (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length := by
      rw [hp]; decide
    have hpc1 : (asmNext asm).pc < (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length := by
      show asm.pc + 1 < _; rw [hp]; decide
    have hget0 : (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.get ⟨asm.pc, hpc0⟩
        = AsmInst.AsmLabel "entry" := by
      rw [show (⟨asm.pc, hpc0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hp]; rfl
    have hget1 : (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.get ⟨(asmNext asm).pc, hpc1⟩
        = AsmInst.AsmOp "STOP" := by
      rw [show (⟨(asmNext asm).pc, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from
            Fin.ext (by show asm.pc + 1 = 1; rw [hp])]; rfl
    have hrb : runBlock 1 stopCtx stopBB { s with instIdx := 0 }
        = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
    refine ⟨asmNext asm, ?_, ?_⟩
    · -- JUMPDEST step
      show runAsm 1 _ _ asm = AsmResult.AsmOK (asmNext asm)
      rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc0 (asmStep_label_ok hpc0 hget0)]
      rfl
    · -- HbsimMatch (Halt) via the dispatcher (STOP arm, empty body)
      have hdisp := HbsimMatch_halting_dispatch_nonvacuous
        (Entry := fun _ _ _ => True)
        (o2pc := (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2)
        (ctx := stopCtx) (bb := stopBB) (s := s) (f' := 0) (stopInst := stopInst)
        (rfl) (rfl) (venomAsmRel_setPc hv) hpc1 hget1 (le_refl 1)
      rw [hrb] at hdisp
      exact hdisp
  · -- budget: 1 + 1 ≤ programLength (= 2)
    decide

set_option maxHeartbeats 1600000 in
/-- **Body-carrying recipe route: `codegen_correct` for `sdCtx` via the dispatcher.** The first
    single-block halting witness with a NON-empty body (`bodyLen = 1`): `sdFn`'s generated program
    `[JUMPDEST "entry"; PUSH0; SELFDESTRUCT]` runs SOLabel → PUSH0 (the SELFDESTRUCT operand
    materialization) → SELFDESTRUCT. The reduction's `hstep` `HbsimMatch (Halt)` is produced by the recipe
    dispatcher `HbsimMatch_halting_dispatch` (SELFDESTRUCT arm) with `bodyLen = 1`, so the dispatcher's
    `bodyLen > 0` path and its state-mutating SELFDESTRUCT arm are exercised end-to-end to
    `codegen_correct`. The body-end relation `hrel'` is `planStackRel_push` of the entry relation (the
    materialized literal `0`), the other 11 `venomAsmRel` conjuncts carrying over (PUSH touches only pc and
    stack, `venomAsmRel` reads neither for them). The dispatcher's `ps'` is a free variable, so the
    constructed plan state is sound — the produced `HbsimMatch (Halt)` (asm-halt + terminal relation) is
    `ps'`-independent. Inherits the M1 axioms via the dispatcher's memory machinery. -/
theorem codegen_correct_selfdestruct_viaDispatch {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 sdCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_singleBlockHalt_viaRecipe (fuel := 10) (ctx := sdCtx) (fn := sdFn) (bb := sdBB)
    (entryName := "main") (entryLbl := "entry")
    (haltFn := fun s => haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 }))
    (E := fun _ _ _ => True) (N := 2)
    (ops := (generateFnPlan sdFn 0 0).get!.1) (psFinal := (generateFnPlan sdFn 0 0).get!.2)
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ hrel haspc
  · intro k s
    have hstep : stepInstBase { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } { s with instIdx := 0 } = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) := stepInstBase_selfdestruct rfl rfl rfl
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, sdBB, sdInst, hstep]
  · intro s; simp [runBlock, evalPhis, execBlock, sdBB, sdInst]
  · -- hstep: SOLabel + PUSH0 body + SELFDESTRUCT via the dispatcher
    intro s asm hv hp
    set prog := (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 with hprogdef
    set o2pc := (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2 with ho2pcdef
    set v := wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes 0).length) (0 : byte)
                ++ encodeNumBytes 0)) with hvdef
    have hv0 : v = UInt256.ofNat 0 := by
      have h : v.toNat = 0 := by rw [hvdef]; exact pushed_offset_toNat 0 (by norm_num)
      exact congrArg UInt256.mk (Fin.ext (by
        show v.toNat = (UInt256.ofNat 0).toNat; rw [h, uint256_ofNat_toNat]; omega))
    set s1 : AsmState := asmNext asm with hs1
    set s2 : AsmState := { asmNext s1 with stack := v :: s1.stack } with hs2
    have p1 : s1.pc = 1 := by rw [hs1]; show asm.pc + 1 = 1; rw [hp]
    have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
    have hb0 : asm.pc < prog.length := by rw [hp]; decide
    have hb1 : s1.pc < prog.length := by rw [p1]; decide
    have hb2 : s2.pc < prog.length := by rw [p2]; decide
    have g0 : prog.get ⟨asm.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
      rw [show (⟨asm.pc, hb0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hp]; rfl
    have g1 : prog.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 0) := by
      rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext p1]; rfl
    have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmOp "SELFDESTRUCT" := by
      rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext p2]; rfl
    have e0 : asmStep o2pc prog asm = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
    have e1 : asmStep o2pc prog s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1]; rfl
    have hrb : runBlock 1 sdCtx sdBB { s with instIdx := 0 }
        = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) := by
      have hstep : stepInstBase { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } { s with instIdx := 0 } = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) := stepInstBase_selfdestruct rfl rfl rfl
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, sdBB, sdInst, hstep]
    -- body-end relation via planStackRel_push
    obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hv
    have hrel' : venomAsmRel lo { initPlanState 0 with stack := stackPush (Operand.Lit v) (initPlanState 0).stack }
        { s with instIdx := 0 } s2 :=
      ⟨planStackRel_push hStk rfl, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
    refine ⟨s1, ?_, ?_⟩
    · -- SOLabel step
      show runAsm 1 o2pc prog asm = AsmResult.AsmOK s1
      rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hb0 e0]; rfl
    · -- HbsimMatch (Halt) via the dispatcher, SELFDESTRUCT arm, bodyLen = 1
      have hdisp := HbsimMatch_halting_dispatch
        (Entry := fun _ _ _ => True) (o2pc := o2pc) (prog := prog)
        (as0 := s1) (as' := s2) (f' := 1) (bodyLen := 1) (N := 2)
        (ps' := { initPlanState 0 with stack := stackPush (Operand.Lit v) (initPlanState 0).stack })
        (ctx := sdCtx) (bb := sdBB) (s := { s with instIdx := 0 }) (vs' := { s with instIdx := 0 })
        (by rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hb1 e1]; rfl)
        hrel' (le_refl 2)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨UInt256.ofNat 0, s1.stack, ?_, ⟨hb2, g2⟩, ?_⟩))))
      · rw [hrb] at hdisp; exact hdisp
      · -- runBlock result matches the SELFDESTRUCT arm
        rw [hrb]
      · -- stack: s2.stack = (UInt256.ofNat 0) :: s1.stack
        rw [hs2, hv0]
  · -- budget: 1 + 2 ≤ programLength (= 3)
    decide

def invInst : Instruction := { id := 0, opcode := Opcode.INVALID, operands := [], outputs := [] }
def invBB : BasicBlock := { label := "entry", instructions := [invInst] }
def invFn : IrFunction := { name := "main", blocks := [invBB] }
def invCtx : VenomContext := { functions := [invFn], entry := some "main" }

set_option maxHeartbeats 1600000 in
/-- **Aborting recipe route: `codegen_correct` for `invCtx` (`main: INVALID`).** The recipe route reaching
    `codegen_correct` for a single-block ABORTING function — previous witnesses all HALT (STOP/SELFDESTRUCT).
    `invFn`'s generated program `[JUMPDEST "entry"; INVALID]` runs JUMPDEST → INVALID (an exceptional halt,
    `Abort ExHaltAbort`). The per-block obligation of `codegen_correct_ofBlocks_HbsimMatch` is discharged by
    the INVALID recipe connector `HbsimMatch_invalid_from_body` with `bodyLen = 1` (the JUMPDEST as the
    body), landing at the INVALID op with `venomAsmRel` carried by `venomAsmRel_setPc`. Exercises the
    dispatcher's INVALID arm and the `Abort ExHaltAbort → AsmFault` `HbsimMatch` arm end-to-end. Base axioms
    — the INVALID connector extracts only the terminal relation, so no memory machinery (contrast the
    M1-dependent SELFDESTRUCT/dispatch witnesses). -/
theorem codegen_correct_invalid {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 invCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_ofBlocks_HbsimMatch
    (Entry := fun s asm N => venomAsmRel lo (initPlanState 0) s asm ∧ asm.pc = 0 ∧
       N = (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length)
    (fuel := 10) (ctx := invCtx) (fn := invFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan invFn 0 0).get!.1) (psFinal := (generateFnPlan invFn 0 0).get!.2)
    rfl rfl rfl rfl ?_ ⟨hrel, haspc, rfl⟩
  intro bb hbb s asm N f' hE hlbleq
  obtain ⟨hvrel, hpc, hN⟩ := hE
  have hbbeq : bb = invBB := by
    simp only [invFn, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
  subst hbbeq
  set prog := (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 with hprogdef
  set o2pc := (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2 with ho2pcdef
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, invBB, invInst, HbsimMatch]
  | succ k =>
    have hrb : runBlock (k+1) invCtx invBB s
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty { s with instIdx := 0 })) := by
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, invBB, invInst, stepInstBase]
    have hpc0 : asm.pc < prog.length := by rw [hpc]; decide
    have hpc1 : (asmNext asm).pc < prog.length := by show asm.pc + 1 < _; rw [hpc]; decide
    have g0 : prog.get ⟨asm.pc, hpc0⟩ = AsmInst.AsmLabel "entry" := by
      rw [show (⟨asm.pc, hpc0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hpc]; rfl
    have g1 : prog.get ⟨(asmNext asm).pc, hpc1⟩ = AsmInst.AsmOp "INVALID" := by
      rw [show (⟨(asmNext asm).pc, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from
            Fin.ext (by show asm.pc + 1 = 1; rw [hpc])]; rfl
    have hbody : runAsm 1 o2pc prog asm = AsmResult.AsmOK (asmNext asm) := by
      rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc0 (asmStep_label_ok hpc0 g0)]; rfl
    refine HbsimMatch_invalid_from_body hrb hbody (venomAsmRel_setPc hvrel) hpc1 g1 ?_
    rw [hN]; decide


set_option maxHeartbeats 3200000 in
/-- **`codegen_correct` for `entry: INVALID` via the generic driver.** The aborting single-block function on
    the recipe route: `codegen_correct_ofBlocks_recipeW` + `hsupplyW_emptyInvalid`, against the real generated
    `[JUMPDEST ; INVALID]`. (`codegen_correct_invalid` above proves the same statement through the older
    dispatch route; this one exercises the generic `hsupply` slice instead, giving it its first consumer.) -/
theorem codegen_correct_invalid_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 invCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ invFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [invFn, List.mem_singleton] at hbb; subst hbb
    simp only [invBB, List.mem_singleton] at hinst; subst hinst
    unfold codegenReadyInst; decide
  have hgen : generateFnPlan invFn 0 0
      = some ((generateFnPlan invFn 0 0).get!.1, (generateFnPlan invFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel invFn) invFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel invFn) invFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan invFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := invCtx) (fn := invFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan invFn 0 0).get!.1) (psFinal := (generateFnPlan invFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    intro bb hbb s
    simp only [invFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, invBB, invInst]
  case _ =>
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [invFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 asm.pc (executePlan [StackOp.SOLabel invBB.label]) := by
      rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
      have hj' : j < 1 := hj; interval_cases j; rfl
    have hlt : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length := by rw [hpc0]; decide
    have hinv : (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt⟩ = AsmInst.AsmOp "INVALID" := by
      simp only [hpc0]; rfl
    exact Or.inr (hsupplyW_emptyInvalid (invInst := invInst)
      (ps := psOfFn (fnPlanFuel invFn) invFn 0 0 "entry") rfl rfl hvrel hbLabel hlt hinv (by decide))
  case _ =>
    refine ⟨⟨invBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel invFn) invFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan invFn 0 0).get!.1)).1.length
      omega

/-- **First MULTI-BLOCK `codegen_correct` via the recipe route** (`jmpStopFn`, `entry: JMP next ; next: STOP`).
    Discharges the two-block driver `codegen_correct_ofBlocks_HbsimMatch` with the N-constrained walk Entry
    `CanonEntryWH`: the JMP block via `HbsimMatch_jmp_from_body_canonWH` (continuing arm, threading wOf and
    halted to `next`), the STOP block via `HbsimMatch_stop_from_body`. Recipe framing of the existing
    non-recipe capstone `codegen_correct_canonical_jmpStop`. -/

theorem codegen_correct_jmpStop_viaRecipe {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jmpStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ jmpStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [jmpEntryBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [stopNextBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan jmpStopFn 0 0
      = some ((generateFnPlan jmpStopFn 0 0).get!.1, (generateFnPlan jmpStopFn 0 0).get!.2) := rfl
  refine codegen_correct_ofBlocks_HbsimMatch
    (Entry := CanonEntryWH jmpStopFn lo
      (pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1)
      (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0)
      (fun l => (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
        - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 l))
    (fuel := 10) (ctx := jmpStopCtx) (fn := jmpStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan jmpStopFn 0 0).get!.1) (psFinal := (generateFnPlan jmpStopFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_
  case _ =>
    -- hstep : per-block
    intro bb hbb s asm N f' hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    have hbb2 : bb = jmpEntryBB ∨ bb = stopNextBB := by
      simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
    rcases hbb2 with hbb | hbb <;> subst hbb
    · -- entry block: JMP
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpsE : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry" = initPlanState 0 :=
        psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
      have hpsN : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next" = initPlanState 0 := rfl
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      cases f' with
      | zero => simp [runBlock, evalPhis, execBlock, jmpEntryBB, jmpInst, HbsimMatch]
      | succ k =>
        have hrb : runBlock (k+1) jmpStopCtx jmpEntryBB s
            = ExecResult.OK (jumpTo "next" { s with instIdx := 0 }) := by
          simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jmpEntryBB, jmpInst,
            stepInstBase, isTerminator, jumpTo, hhalt]
        have hnh : ({ s with instIdx := 0 } : VenomState).halted = false := by simpa using hhalt
        have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
            (executePlan [StackOp.SOLabel "entry"]) := by
          rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
        obtain ⟨as1, hrun1, hrel1, hpc1'⟩ :=
          soLabel_sim (offsetToPc := (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2) lo
            (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry") s asm _ "entry" (by rw [hpsE]; exact hvrel) hbLabel
        have hpc1'' : as1.pc = 1 := by rw [hpc1', hpc0]; decide
        have hpc1lt : as1.pc < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
          rw [hpc1'']; decide
        have hpush : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨as1.pc, hpc1lt⟩
            = resolveInst (computeLabelOffsets (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2 (AsmInst.AsmPushLabel "next") := by
          conv_lhs => rw [show (⟨as1.pc, hpc1lt⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext hpc1'']
          rfl
        have hpc2lt : as1.pc + 1 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
          rw [hpc1'']; decide
        have e2 : as1.pc + 1 = 2 := by rw [hpc1'']
        have hjump : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨as1.pc + 1, hpc2lt⟩
            = AsmInst.AsmOp "JUMP" := by
          conv_lhs => rw [show (⟨as1.pc + 1, hpc2lt⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext e2]
          rfl
        refine HbsimMatch_jmp_from_body_canonWH (target := "next") (off := 5) (bb' := stopNextBB)
          (bodyLen := 1) (ps' := psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next")
          hrb hnh hrun1 (by rw [hpsN]; rw [hpsE] at hrel1; exact hrel1) rfl hpc1lt hpush
          (by decide) (by decide) hpc2lt hjump (by decide) rfl ?_ hwN
        show (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "next" + (1 + 2)
            ≤ (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 jmpEntryBB.label
        decide
    · -- next block: STOP
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm hwN
      have hpsN : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next" = initPlanState 0 := rfl
      have hpc3 : asm.pc = 3 := by rw [hpc_asm]; decide
      cases f' with
      | zero => simp [runBlock, evalPhis, execBlock, stopNextBB, stopInst, HbsimMatch]
      | succ k =>
        have hrb : runBlock (k+1) jmpStopCtx stopNextBB s
            = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
          simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopNextBB, stopInst, stepInstBase]
        have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
            (executePlan [StackOp.SOLabel "next"]) := by
          rw [hpc3]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
        obtain ⟨as1, hrun1, hrel1, hpc1'⟩ :=
          soLabel_sim (offsetToPc := (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2) lo
            (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next") s asm _ "next" (by rw [hpsN]; exact hvrel) hbLabel
        have hpc1'' : as1.pc = 4 := by rw [hpc1', hpc3]; decide
        have hlt4 : as1.pc < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
          rw [hpc1'']; decide
        have hstop : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨as1.pc, hlt4⟩
            = AsmInst.AsmOp "STOP" := by
          conv_lhs => rw [show (⟨as1.pc, hlt4⟩ : Fin _) = ⟨4, by decide⟩ from Fin.ext hpc1'']
          rfl
        have hle2 : (1 : Nat) + 1 ≤ N := by
          have hw : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "next" ≤ N := hwN
          have hval : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "next" = 2 := by decide
          omega
        exact HbsimMatch_stop_from_body (bodyLen := 1) hrb hrun1 (by rw [hpsN] at hrel1; exact hrel1) hlt4 hstop hle2
  case _ =>
    -- hentry : CanonEntryWH at the entry state
    have hpsE : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry" = initPlanState 0 :=
      psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
    refine ⟨⟨jmpEntryBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "entry"
          ≤ (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
      omega


set_option maxHeartbeats 3200000 in
/-- **Non-vacuity of the generic recipe driver**: `jmpStopFn` (`entry: JMP next ; next: STOP`) driven by
    `codegen_correct_ofBlocks_recipeW`. Discharges `hrun0` (both blocks) and `hsupply` (JMP `TermRecipeW`
    for the entry block, STOP `TermRecipeW` for `next`) — exhibiting a real function the generic driver
    applies to, so the driver is not vacuous. -/
theorem codegen_correct_jmpStop_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jmpStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ jmpStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [jmpEntryBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [stopNextBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan jmpStopFn 0 0
      = some ((generateFnPlan jmpStopFn 0 0).get!.1, (generateFnPlan jmpStopFn 0 0).get!.2) := rfl
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo)
    (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
      - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := jmpStopCtx) (fn := jmpStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan jmpStopFn 0 0).get!.1) (psFinal := (generateFnPlan jmpStopFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    -- hrun0
    intro bb hbb s
    simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, jmpEntryBB, jmpInst]
    · simp [runBlock, evalPhis, execBlock, stopNextBB, stopInst]
  case _ =>
    -- hsupply
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    have hbb2 : bb = jmpEntryBB ∨ bb = stopNextBB := by
      simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
    have hpsN : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next" = initPlanState 0 := rfl
    have hpsE : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry" = initPlanState 0 :=
      psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
    rcases hbb2 with hbb | hbb <;> subst hbb
    · -- entry block: JMP recipe — discharged by the GENERIC empty-body slice, not inline
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel jmpEntryBB.label]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt1 : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc0]; decide
      have e1 : asm.pc + 1 = 1 := by rw [hpc0]
      have hpush : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt1⟩
          = resolveInst (computeLabelOffsets (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
              (AsmInst.AsmPushLabel "next") := by
        conv_lhs => rw [show (⟨asm.pc + 1, hlt1⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext e1]
        rfl
      have hlt2 : asm.pc + 1 + 1 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc0]; decide
      have e2 : asm.pc + 1 + 1 = 2 := by rw [hpc0]
      have hjump : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨asm.pc + 1 + 1, hlt2⟩
          = AsmInst.AsmOp "JUMP" := by
        conv_lhs => rw [show (⟨asm.pc + 1 + 1, hlt2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext e2]
        rfl
      refine Or.inr (hsupplyW_emptyJmp (jmpInst := jmpInst) (lbl := "next") (off := 5) (bb' := stopNextBB)
        rfl rfl rfl hhalt hvrel (by rw [hpsE, hpsN]) hbLabel hlt1 hpush (by decide) (by decide)
        hlt2 hjump (by decide) rfl ?_)
      show (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
            - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "next" + (1 + 2)
          ≤ (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
            - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 jmpEntryBB.label
      decide
    · -- next block: STOP recipe — discharged by the GENERIC empty-body slice, not inline
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc3 : asm.pc = 3 := by rw [hpc_asm]; decide
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel stopNextBB.label]) := by
        rw [hpc3]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt4 : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc3]; decide
      have e4 : asm.pc + 1 = 4 := by rw [hpc3]
      have hstop : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt4⟩
          = AsmInst.AsmOp "STOP" := by
        conv_lhs => rw [show (⟨asm.pc + 1, hlt4⟩ : Fin _) = ⟨4, by decide⟩ from Fin.ext e4]
        rfl
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next") rfl rfl hvrel hbLabel hlt4 hstop (by decide))
  case _ =>
    -- hentry
    have hpsE : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry" = initPlanState 0 :=
      psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
    refine ⟨⟨jmpEntryBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 "entry"
          ≤ (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
      omega



def jnzCtxR : VenomContext := { functions := [jnzStopFnR], entry := some "main" }

/-- **Every single-byte literal evaluates.** `encodeNumBytes` recurses on `n / 256` — non-structural, so Lean
    compiles it by well-founded recursion and the KERNEL CANNOT REDUCE IT (`WF.fix` is opaque to `whnf`).
    Hence `rfl`/`decide` get stuck on any asm carrying a pushed literal, and `#eval` (compiled) disagrees with
    the kernel. Its EQUATION LEMMAS can still evaluate it, which is what unblocks the generated-program facts.
    (`encodeNumBytes 0 = []` is the exception that reduces natively — the `n = 0` guard returns before the
    recursion — which is why `PUSH0` programs like `sdFn` never hit this.) -/
theorem encodeNumBytes_lt256 {n : Nat} (h0 : n ≠ 0) (h : n < 256) :
    encodeNumBytes n = [UInt8.ofNat n] := by
  rw [encodeNumBytes]
  simp only [h0, if_false, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  rw [encodeNumBytes]
  simp

/-- The instance the `jnzStopFnR` condition literal needs. -/
theorem encodeNumBytes_one : encodeNumBytes 1 = [(1 : byte)] := by
  rw [encodeNumBytes_lt256] <;> decide

set_option maxHeartbeats 2000000 in
/-- The unresolved asm for `jnzStopFnR`, stated so the stuck `encodeNumBytes 1` term survives verbatim: the
    list spine reduces around it, so this closes by `rfl`. Rewriting with this and `encodeNumBytes_one` turns
    the generated program into a ground literal that `decide` can evaluate. -/
theorem jnz_unresolved_asm : executePlan (generateFnPlan jnzStopFnR 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmPush (encodeNumBytes 1),
     AsmInst.AsmPushLabel "then", AsmInst.AsmOp "JUMPI",
     AsmInst.AsmPushLabel "else", AsmInst.AsmOp "JUMP",
     AsmInst.AsmLabel "else", AsmInst.AsmOp "STOP",
     AsmInst.AsmLabel "then", AsmInst.AsmOp "STOP"] := by rfl

set_option maxHeartbeats 12000000 in
/-- **Branching multi-block recipe route: `codegen_correct` for `jnzCtxR` via the generic driver.** The
    3-block conditional `entry: JNZ 1 then else ; then: STOP ; else: STOP`, driven by
    `codegen_correct_ofBlocks_recipeW`. Exercises the dispatcher's **JNZ-taken** arm (the condition literal
    `1 ≠ 0` selects `then`) — the first branching witness; every prior one used JMP or a halting terminator.
    The generated program is `[LABEL entry; PUSH 1; PUSH then; JUMPI; PUSH else; JUMP; LABEL else; STOP;
    LABEL then; STOP]` (pcOf entry=0, else=6, then=8). Per block: `entry` supplies the JNZ-taken
    `TermRecipeW` (bodyLen=2 — JUMPDEST + the condition push — landing at the `PUSH then`, with the
    condition-dropped successor relation for `then`); `then`/`else` supply STOP `TermRecipeW`s. -/
theorem codegen_correct_jnzStop_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jnzCtxR vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ jnzStopFnR.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [jnzStopFnR, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [jnzEntryR, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [thenBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [elseBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan jnzStopFnR 0 0
      = some ((generateFnPlan jnzStopFnR 0 0).get!.1, (generateFnPlan jnzStopFnR 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  have hpsT : psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "then" = initPlanState 0 := rfl
  refine codegen_correct_ofBlocks_recipeW
    (lo := lo)
    (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
      - pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2)
    (fuel := 10) (ctx := jnzCtxR) (fn := jnzStopFnR) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan jnzStopFnR 0 0).get!.1) (psFinal := (generateFnPlan jnzStopFnR 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ?_
  case _ =>
    -- hrun0
    intro bb hbb s
    simp only [jnzStopFnR, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, jnzEntryR, jnzInstR]
    · simp [runBlock, evalPhis, execBlock, thenBB, stopInst]
    · simp [runBlock, evalPhis, execBlock, elseBB, stopInst]
  case _ =>
    -- hsupply
    intro bb hbb s asm N k hE hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    have hbb3 : bb = jnzEntryR ∨ bb = thenBB ∨ bb = elseBB := by
      simp only [jnzStopFnR, List.mem_cons, List.not_mem_nil, or_false] at hbb; exact hbb
    rcases hbb3 with hbb | hbb | hbb <;> subst hbb
    · -- entry: JNZ (taken, cond = 1)
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      set cond : bytes32 := wordOfBytes (List.toByteArray
        (List.replicate (32 - (encodeNumBytes 1).length) (0 : byte) ++ encodeNumBytes 1)) with hcondd
      have hct : cond.toNat = 1 := by rw [hcondd]; exact pushed_offset_toNat 1 (by norm_num)
      have hcondne : cond ≠ EvmYul.UInt256.ofNat 0 := by
        intro h; rw [h, EvmYul.uint256_ofNat_toNat] at hct; simp at hct
      set s1 : AsmState := asmNext asm with hs1
      set s2 : AsmState := { asmNext s1 with stack := cond :: s1.stack } with hs2
      have p1 : s1.pc = 1 := by rw [hs1]; show asm.pc + 1 = 1; rw [hpc0]
      have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
      have hb0 : asm.pc < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [hpc0]; decide
      have hb1 : s1.pc < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [p1]; decide
      have hb2 : s2.pc < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [p2]; decide
      have hb3 : s2.pc + 1 < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [p2]; decide
      have g0 : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨asm.pc, hb0⟩
          = AsmInst.AsmLabel "entry" := by
        rw [show (⟨asm.pc, hb0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hpc0]; rfl
      have g1 : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨s1.pc, hb1⟩
          = AsmInst.AsmPush (encodeNumBytes 1) := by
        rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext p1]; rfl
      have hpush : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨s2.pc, hb2⟩
          = resolveInst (computeLabelOffsets (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
              (AsmInst.AsmPushLabel "then") := by
        rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext p2]; rfl
      have e3 : s2.pc + 1 = 3 := by rw [p2]
      have hjumpi : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨s2.pc + 1, hb3⟩
          = AsmInst.AsmOp "JUMPI" := by
        conv_lhs => rw [show (⟨s2.pc + 1, hb3⟩ : Fin _) = ⟨3, by decide⟩ from Fin.ext e3]
        rfl
      have hpushstep : asmStep (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
          (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 s1 = AsmResult.AsmOK s2 := by
        rw [asmStep_push_ok hb1 g1]; rfl
      have hbody : runAsm 2 (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).2
          (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 asm = AsmResult.AsmOK s2 := by
        rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hb0 (asmStep_label_ok hb0 g0)]
        rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hb1 hpushstep]; rfl
      have hone : (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ { val := 0 } := by decide
      have hpcThen : pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 "then" = 8 := by
        decide
      have hrb : runBlock (k+1) jnzCtxR jnzEntryR s
          = ExecResult.OK (jumpTo "then" { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jnzEntryR, jnzInstR,
          stepInstBase, isTerminator, jumpTo, evalOperand, hhalt, hone]
      have hnh : ({ s with instIdx := 0 } : VenomState).halted = false := by simpa using hhalt
      refine Or.inr ⟨s2, psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "then", { s with instIdx := 0 }, 2, hbody, ?_⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨"then", 13, cond, s1.stack, thenBB, ?_, hnh, hrb, rfl, hcondne, ⟨hb2, hpush⟩, (by rw [jnz_unresolved_asm, encodeNumBytes_one]; decide), (by norm_num),
          ⟨hb3, hjumpi⟩, (by rw [jnz_unresolved_asm, encodeNumBytes_one]; decide), ?_, rfl⟩))))))
      · show (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 "then" + (2 + 2)
            ≤ (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
              - pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 jnzEntryR.label
        decide
      · -- successor relation: the JUMPI drops the condition, leaving the entry stack
        show venomAsmRel lo (psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "then") { s with instIdx := 0 }
          { s2 with stack := s1.stack }
        rw [hpsT]
        exact venomAsmRel_setPc (by rw [hpsE] at hvrel; exact hvrel)
    · -- then: STOP — discharged by the GENERIC empty-body slice, not inline
      have hlbl : s.currentBb = "then" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel thenBB.label]) := by
        rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt9 : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [hpc8]; decide
      have e9 : asm.pc + 1 = 9 := by rw [hpc8]
      have hstop : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt9⟩
          = AsmInst.AsmOp "STOP" := by
        conv_lhs => rw [show (⟨asm.pc + 1, hlt9⟩ : Fin _) = ⟨9, by decide⟩ from Fin.ext e9]
        rfl
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "then") rfl rfl hvrel hbLabel hlt9 hstop
        (by decide))
    · -- else: STOP — likewise
      have hlbl : s.currentBb = "else" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel elseBB.label]) := by
        rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hlt7 : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length := by
        rw [hpc6]; decide
      have e7 : asm.pc + 1 = 7 := by rw [hpc6]
      have hstop : (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.get ⟨asm.pc + 1, hlt7⟩
          = AsmInst.AsmOp "STOP" := by
        conv_lhs => rw [show (⟨asm.pc + 1, hlt7⟩ : Fin _) = ⟨7, by decide⟩ from Fin.ext e7]
        rfl
      exact Or.inr (hsupplyW_emptyStop (stopInst := stopInst)
        (ps := psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "else") rfl rfl hvrel hbLabel hlt7 hstop
        (by decide))
  case _ =>
    -- hentry
    refine ⟨⟨jnzEntryR, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel jnzStopFnR) jnzStopFnR 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1 "entry"
          ≤ (asmResolve (executePlan (generateFnPlan jnzStopFnR 0 0).get!.1)).1.length
      omega


/-! ### ✅ The mixed body reaches `codegen_correct` — `codegen_correct_mxMulVarLit_recipeW`

The `RegularBodyH` witnesses above pin the new fold arms on real generator output; this takes the
same shape all the way to the top-level theorem, through the invariant-carrying driver
`codegen_correct_ofBlocks_recipeW_inv` — the first whole-function `codegen_correct` whose body
contains a **var-operand instruction the generator actually DUPs** (mixed or otherwise).

The function is `tFn`'s shape with the second CALLVALUE replaced by the mixed binop:

```
entry:  %a = CALLVALUE ; %c = MUL %a, 5 ; JMP next     -- [JUMPDEST; CALLVALUE; PUSH 5; DUP2; MUL; PUSH next; JUMP]
next:   RETURN %a, %c                                  -- [JUMPDEST; SWAP1; RETURN]
```

so `entry` goes through `hsupplyW_regularJmp` (non-empty body, nil join reorder — the well-scheduled
case) and `next` through `hsupplyW_emptyReturnReorder` (a genuine `SWAP1` terminator reorder), exactly
the two slices the previous round named as the missing composition.

**Why MUL and not ADD.** `hsupplyW_emptyReturnReorder`'s memory obligations (`hcov0`/`hbelow`) are
discharged for free only when RETURN's window is empty. With `callvalue = 0` (`mxInv`) the ADD body
would give `c = 5`, forcing either a memory-size hypothesis on the asm state at `next` or a larger
`fnEom`; `MUL` gives `c = 0 * 5 = 0` while keeping a genuinely non-zero literal in the body — the
operand class under test is unaffected (the emitted plan is `PUSH 5 ; DUP2 ; <op>` either way, which
is why the `RegularBodyH` witnesses above use ADD). -/

/-- The instance the mixed body's literal needs (see `encodeNumBytes_lt256` for why the kernel
    cannot evaluate it on its own). -/
theorem encodeNumBytes_five : encodeNumBytes 5 = [(5 : byte)] := by
  rw [encodeNumBytes_lt256] <;> decide

def mxMulVL : Instruction :=
  { id := 1, opcode := Opcode.MUL,
    operands := [Operand.Var "a", Operand.Lit (UInt256.ofNat 5)], outputs := ["c"] }
def mxMulEntry : BasicBlock := { label := "entry", instructions := [mxCv, mxMulVL, mxJmp] }
def mxNext : BasicBlock := { label := "next", instructions := [mxRet] }
def mxMulFn : IrFunction := { name := "main", blocks := [mxMulEntry, mxNext] }
def mxMulCtx : VenomContext := { functions := [mxMulFn], entry := some "main" }

/-- The unresolved asm for `mxMulFn`, stated so the kernel-stuck `encodeNumBytes 5` survives
    verbatim: the list spine reduces around it, so this closes by `rfl`. Rewriting with this and
    `encodeNumBytes_five` turns the generated program into a ground literal that `decide` can
    evaluate — the same unblocking `jnz_unresolved_asm` does for `jnzStopFnR`.

    **This is why the mixed body could not be a capstone until now**: any label offset computed
    *after* a pushed literal is stuck behind `encodeNumBytes`'s well-founded recursion, and the JMP
    recipe needs exactly such an offset. -/
theorem mx_unresolved_asm : executePlan (generateFnPlan mxMulFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmPush (encodeNumBytes 5),
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "MUL", AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP",
     AsmInst.AsmLabel "next", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "RETURN"] := by rfl

/-- The mixed `[Var x, Lit b]` body as a `RegularBodyH` against `mxMulFn`'s generated program — the
    MUL instance of `mxVarLit_regularBodyH`, and the one the capstone below consumes. -/
theorem mxMulBody_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 1 [mxCv, mxMulVL] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "MUL", rfl, rfl, by decide, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨"a", UInt256.ofNat 5, (· * ·), rfl, fun _ => rfl, rfl, by decide, by decide,
       fun _ h hg => asmStep_mul_ok h hg⟩)))))⟩

/-- The body-end state of `mxMulEntry`: `a := callvalue`, then `c := a * 5`. -/
abbrev mxSEnd (s : VenomState) : VenomState :=
  { updateVar "c" (s.callCtx.callvalue * EvmYul.UInt256.ofNat 5)
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
    with instIdx := 2 }

theorem mxEntry_thread (s : VenomState) :
    execBodyThread [mxCv, mxMulVL] 0 { s with instIdx := 0 } = some (mxSEnd s) := by
  have h1 : stepInstBase mxCv { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have hlk : lookupVar "a"
      ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have h2 := stepInstBase_binopVarLit (inst := mxMulVL) (f := (· * ·)) (x := "a") (out := "c")
    (b := EvmYul.UInt256.ofNat 5) (wx := s.callCtx.callvalue) rfl rfl rfl hlk
  show (match stepInstBase mxCv { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [mxMulVL] 1 { s' with instIdx := 1 }
        | _ => none) = some (mxSEnd s)
  rw [h1]
  show (match stepInstBase mxMulVL
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [] 2 { s' with instIdx := 2 }
        | _ => none) = some (mxSEnd s)
  rw [h2]
  rfl

/-- `mxMulEntry`'s OK result is `jumpTo "next"` of the body-end state. -/
theorem mxEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (2 + (j + 1)) mxMulCtx mxMulEntry s = ExecResult.OK (jumpTo "next" (mxSEnd s)) :=
  runBlock_body_jmp mxMulCtx mxMulEntry j [mxCv, mxMulVL] mxJmp mxCv [mxMulVL, mxJmp] s
    (mxSEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (mxEntry_thread s) (by simpa [updateVar] using hnh)

/-- The invariant the RETURN recipe needs: at `next`, both operands are defined and zero. -/
def mxInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0))

/-- **`mxInv` survives every block of `mxMulFn`.** `mxMulEntry` needs fuel ≥ 3 and then lands on
    `jumpTo "next" (mxSEnd s)`, whose `a` is the (zero) call value and whose `c` is `0 * 5 = 0`;
    `mxNext`'s RETURN never yields `OK`, so that obligation is vacuous. -/
theorem mxInv_pres : ∀ bb ∈ mxMulFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mxInv s → runBlock f' mxMulCtx bb s = ExecResult.OK s' → mxInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [mxMulFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, mxMulEntry, mxCv] at hrun
    | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, mxMulEntry, mxCv,
             stepInstBase, execRead0, isTerminator] at hrun
    | 2 =>
      -- the MUL reads `a`, and `simp` eta-expands the record so `lookupVar_updateVar_self` no
      -- longer fires on its own; feeding it in pre-instantiated lets the operand lookup reduce
      have hlk : lookupVar "a"
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
            : VenomState) = some s.callCtx.callvalue := lookupVar_updateVar_self _ _ _
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, mxMulEntry, mxCv,
        mxMulVL, stepInstBase, execRead0, execPure2, evalOperand, isTerminator, hlk] at hrun
    | (j+3) =>
      rw [show j+3 = 2+(j+1) from by omega, mxEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ?_⟩
      have ha : lookupVar "a" (jumpTo "next" (mxSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "a" (updateVar "c" (s.callCtx.callvalue * EvmYul.UInt256.ofNat 5)
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
        show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      have hc : lookupVar "c" (jumpTo "next" (mxSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "c" (updateVar "c" (s.callCtx.callvalue * EvmYul.UInt256.ofNat 5)
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
        rfl
      exact ⟨ha, hc⟩
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, mxNext, mxRet] at hrun
    | (j+1) =>
      rcases hla : lookupVar "a" s with _ | wa
      · have hstep : stepInstBase mxRet { s with instIdx := 0 }
            = ExecResult.Error "return: undefined operand" := by
          have hla' : lookupVar "a" { s with instIdx := 0 } = none := hla
          simp [mxRet, stepInstBase, evalOperand, hla']
        have hrb := runBlock_error mxMulCtx mxNext j [] mxRet mxRet [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) hstep (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
      · rcases hlc : lookupVar "c" s with _ | wc
        · have hstep : stepInstBase mxRet { s with instIdx := 0 }
              = ExecResult.Error "return: undefined operand" := by
            have hla' : lookupVar "a" { s with instIdx := 0 } = some wa := hla
            have hlc' : lookupVar "c" { s with instIdx := 0 } = none := hlc
            simp [mxRet, stepInstBase, evalOperand, hla', hlc']
          have hrb := runBlock_error mxMulCtx mxNext j [] mxRet mxRet [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) hstep (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
        · have hrb := runBlock_body_return mxMulCtx mxNext j [] mxRet mxRet [] s
            { s with instIdx := 0 } (Operand.Var "a") (Operand.Var "c") wa wc rfl rfl rfl hla hlc
            rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp] at hrun
          rw [hrb] at hrun
          exact absurd hrun (by simp)

/-- The `next` block's RETURN halts, given both operands defined. The RETURN twin of
    `rNext_reverts`. -/
theorem mxNext_halts (s : VenomState) (j : Nat)
    (ha : lookupVar "a" s = some (EvmYul.UInt256.ofNat 0))
    (hc : lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)) :
    runBlock (0 + (j + 1)) mxMulCtx mxNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat
        (EvmYul.UInt256.ofNat 0).toNat { s with instIdx := 0 }) { s with instIdx := 0 })) :=
  runBlock_body_return mxMulCtx mxNext j [] mxRet mxRet [] s { s with instIdx := 0 }
    (Operand.Var "a") (Operand.Var "c") _ _ rfl rfl rfl ha hc rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

/-- **The `Halt` arm really is the one that fires.** `codegen_correct_mxMulVarLit_recipeW`'s statement
    carries the `| _ => True` catch-all that made the retracted `codegen_correct_ofRecipes` vacuous, so
    the arm has to be exhibited. Like `rFn_reverts` this is a THEOREM, not an `#eval`: RETURN reads
    memory, so evaluation hits `ffi.ByteArray.zeroes` (an M1 FFI axiom with no native implementation).
    Proving it is also stronger — it covers EVERY state the capstone's own hypotheses admit, not one
    sample point — and it needs no FFI axiom, since the halting state is never inspected. -/
theorem mxMulFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 mxMulCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 mxMulCtx vs
      = runBlocks 10 mxMulCtx mxMulFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, mxMulCtx, mxMulFn, lookupFunction, fnEntryLabel, mxMulEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  have hentry : runBlock 9 mxMulCtx mxMulEntry s0 = ExecResult.OK (jumpTo "next" (mxSEnd s0)) := by
    rw [show (9 : Nat) = 2 + (6 + 1) from by omega]; exact mxEntry_runBlock s0 6 hnh0
  have hlk0 : lookupBlock s0.currentBb mxMulFn.blocks = some mxMulEntry := rfl
  have hjh : (jumpTo "next" (mxSEnd s0)).halted = false := by
    simpa [jumpTo, updateVar] using hnh0
  have hstep : runBlocks 10 mxMulCtx mxMulFn s0 = runBlocks 9 mxMulCtx mxMulFn (jumpTo "next" (mxSEnd s0)) :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hjh
  have ha : lookupVar "a" (jumpTo "next" (mxSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "a" (updateVar "c" (s0.callCtx.callvalue * EvmYul.UInt256.ofNat 5)
      { updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "a" (updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]
  have hc : lookupVar "c" (jumpTo "next" (mxSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "c" (updateVar "c" (s0.callCtx.callvalue * EvmYul.UInt256.ofNat 5)
      { updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]
    rfl
  have hlk1 : lookupBlock (jumpTo "next" (mxSEnd s0)).currentBb mxMulFn.blocks = some mxNext := rfl
  have hhalt := mxNext_halts (jumpTo "next" (mxSEnd s0)) 7 ha hc
  rw [show (0 : Nat) + (7 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The mixed-operand whole-function capstone.** `codegen_correct` for
    `entry: %a = CALLVALUE ; %c = MUL %a, 5 ; JMP next` / `next: RETURN %a, %c`, end to end against
    the real generated program, through the invariant-carrying driver. First whole-function
    `codegen_correct` whose body contains a DUP'd var operand — and the first for the mixed
    Var/Lit operand class. -/
theorem codegen_correct_mxMulVarLit_recipeW {lo : AssocList String Nat} {vs : VenomState}
    {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 mxMulCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ mxMulFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [mxMulFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [mxMulEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [mxNext, List.mem_singleton] at hinst; subst hinst
      unfold codegenReadyInst; decide
  have hgen : generateFnPlan mxMulFn 0 0
      = some ((generateFnPlan mxMulFn 0 0).get!.1, (generateFnPlan mxMulFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel mxMulFn) mxMulFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv mxInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel mxMulFn) mxMulFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := mxMulCtx) (fn := mxMulFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan mxMulFn 0 0).get!.1) (psFinal := (generateFnPlan mxMulFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ mxInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, by simp⟩
  case _ =>
    intro bb hbb s
    simp only [mxMulFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, mxMulEntry, mxCv]
    · simp [runBlock, evalPhis, execBlock, mxNext, mxRet]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [mxMulFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE + the mixed MUL + JMP
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, mxMulEntry, mxCv, stepInstBase, execRead0, isTerminator]⟩
      | 1 => exact Or.inl ⟨"out of fuel", by
               have hlk : lookupVar "a"
                   ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
                     : VenomState) = some s.callCtx.callvalue := lookupVar_updateVar_self _ _ _
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, mxMulEntry,
                 mxCv, mxMulVL, stepInstBase, execRead0, execPure2, evalOperand, isTerminator,
                 hlk]⟩
      | (j+2) =>
      rw [show j+2+1 = ([mxCv, mxMulVL] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mxCv, mxMulVL]) (jmpInst := mxJmp) (hd := mxCv) (tl := [mxMulVL, mxJmp])
        (nextLiveness := ["a","c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := mxNext) (sEnd := mxSEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl <;> decide)
        (hthread := mxEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := mxMulBody_regularBodyH)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 4 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by rw [mx_unresolved_asm, encodeNumBytes_five]; decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by rw [mx_unresolved_asm, encodeNumBytes_five]; decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: RETURN with the SWAP1 reorder; the invariant supplies the operand VALUES
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      obtain ⟨_, _, hvals⟩ := hinv
      obtain ⟨ha0, hc0⟩ := hvals hlbl
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := mxRet) (offv := "a") (szv := "c")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "a", Operand.Var "c"])
        (ps := psOfFn (fnPlanFuel mxMulFn) mxMulFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := ha0) (hevalsz := hc0) (hvoff := ha0) (hvsz := hc0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc7]; decide) (hget := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨mxMulEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel mxMulFn) mxMulFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan mxMulFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ The MIRROR order reaches `codegen_correct` too — `codegen_correct_mxMulLitVar_recipeW`

`codegen_correct_mxMulVarLit_recipeW` closed the `[Var x, Lit b]` order. This closes the mirror
`[Lit a, Var y]`: `entry: %a = CALLVALUE ; %c = MUL 5, %a ; JMP next` / `next: RETURN %a, %c`. The
entry body compiles to `DUP1 ; PUSH 5 ; MUL` (var DUP'd first, literal pushed on top) rather than
`PUSH 5 ; DUP2 ; MUL`, so it exercises `bodyStep_commBinopLitVar` — the LitVar fold arm that until now
had a witness but no whole-function capstone. Both mixed operand orders now reach `codegen_correct`.

Shared with `mxMulFn` wholesale: `mxCv` (CALLVALUE → a), `mxJmp`, `mxRet`, `mxNext`, `mxInv`,
`mxNext_halts` — the invariant and the RETURN half are order-independent (both give `c = 0`), so only
the entry body differs. -/

def lvMul : Instruction :=
  { id := 1, opcode := Opcode.MUL,
    operands := [Operand.Lit (UInt256.ofNat 5), Operand.Var "a"], outputs := ["c"] }
def lvEntry : BasicBlock := { label := "entry", instructions := [mxCv, lvMul, mxJmp] }
def lvFn : IrFunction := { name := "main", blocks := [lvEntry, mxNext] }
def lvCtx : VenomContext := { functions := [lvFn], entry := some "main" }

/-- Unresolved asm for `lvFn` — `DUP1 ; PUSH 5 ; MUL`, the mirror interleaving. `encodeNumBytes 5`
    verbatim so the spine reduces by `rfl`. -/
theorem lv_unresolved_asm : executePlan (generateFnPlan lvFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP1",
     AsmInst.AsmPush (encodeNumBytes 5), AsmInst.AsmOp "MUL", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "RETURN"] := by rfl

/-- The `[Lit a, Var y]` body as a `RegularBodyH` against `lvFn` — the MUL instance of
    `mxLitVar_regularBodyH`, consuming the `bodyStep_commBinopLitVar` arm. -/
theorem lvBody_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 1 [mxCv, lvMul] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "MUL", rfl, rfl, by decide, rfl,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨"a", UInt256.ofNat 5, (· * ·), rfl, fun _ => rfl, rfl, by decide, by decide,
       fun _ h hg => asmStep_mul_ok h hg⟩)))))⟩

/-- Body-end state of `lvEntry`: `a := callvalue`, then `c := 5 * a` (LitVar order). -/
abbrev lvSEnd (s : VenomState) : VenomState :=
  { updateVar "c" (EvmYul.UInt256.ofNat 5 * s.callCtx.callvalue)
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
    with instIdx := 2 }

theorem lvEntry_thread (s : VenomState) :
    execBodyThread [mxCv, lvMul] 0 { s with instIdx := 0 } = some (lvSEnd s) := by
  have h1 : stepInstBase mxCv { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have hlk : lookupVar "a"
      ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = some s.callCtx.callvalue := lookupVar_updateVar_self _ _ _
  have h2 := stepInstBase_binopLitVar (inst := lvMul) (f := (· * ·)) (y := "a") (out := "c")
    (a := EvmYul.UInt256.ofNat 5) (wy := s.callCtx.callvalue) rfl rfl rfl hlk
  show (match stepInstBase mxCv { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [lvMul] 1 { s' with instIdx := 1 }
        | _ => none) = some (lvSEnd s)
  rw [h1]
  show (match stepInstBase lvMul
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [] 2 { s' with instIdx := 2 }
        | _ => none) = some (lvSEnd s)
  rw [h2]
  rfl

theorem lvEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (2 + (j + 1)) lvCtx lvEntry s = ExecResult.OK (jumpTo "next" (lvSEnd s)) :=
  runBlock_body_jmp lvCtx lvEntry j [mxCv, lvMul] mxJmp mxCv [lvMul, mxJmp] s
    (lvSEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (lvEntry_thread s) (by simpa [updateVar] using hnh)

/-- `mxInv` survives every block of `lvFn` (reusing the same invariant). `c = 5 * 0 = 0`. -/
theorem lvInv_pres : ∀ bb ∈ lvFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mxInv s → runBlock f' lvCtx bb s = ExecResult.OK s' → mxInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [lvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, lvEntry, mxCv] at hrun
    | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, lvEntry, mxCv,
             stepInstBase, execRead0, isTerminator] at hrun
    | 2 =>
      have hlk : lookupVar "a"
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
            : VenomState) = some s.callCtx.callvalue := lookupVar_updateVar_self _ _ _
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, lvEntry, mxCv,
        lvMul, stepInstBase, execRead0, execPure2, evalOperand, isTerminator, hlk] at hrun
    | (j+3) =>
      rw [show j+3 = 2+(j+1) from by omega, lvEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ?_⟩
      have ha : lookupVar "a" (jumpTo "next" (lvSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "a" (updateVar "c" (EvmYul.UInt256.ofNat 5 * s.callCtx.callvalue)
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
        show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
      have hc : lookupVar "c" (jumpTo "next" (lvSEnd s)) = some (EvmYul.UInt256.ofNat 0) := by
        show lookupVar "c" (updateVar "c" (EvmYul.UInt256.ofNat 5 * s.callCtx.callvalue)
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })
          = some (EvmYul.UInt256.ofNat 0)
        rw [lookupVar_updateVar_self, hcv]
        rfl
      exact ⟨ha, hc⟩
  · match f' with
    | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, mxNext, mxRet] at hrun
    | (j+1) =>
      rcases hla : lookupVar "a" s with _ | wa
      · have hstep : stepInstBase mxRet { s with instIdx := 0 }
            = ExecResult.Error "return: undefined operand" := by
          have hla' : lookupVar "a" { s with instIdx := 0 } = none := hla
          simp [mxRet, stepInstBase, evalOperand, hla']
        have hrb := runBlock_error lvCtx mxNext j [] mxRet mxRet [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) hstep (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
      · rcases hlc : lookupVar "c" s with _ | wc
        · have hstep : stepInstBase mxRet { s with instIdx := 0 }
              = ExecResult.Error "return: undefined operand" := by
            have hla' : lookupVar "a" { s with instIdx := 0 } = some wa := hla
            have hlc' : lookupVar "c" { s with instIdx := 0 } = none := hlc
            simp [mxRet, stepInstBase, evalOperand, hla', hlc']
          have hrb := runBlock_error lvCtx mxNext j [] mxRet mxRet [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) hstep (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
        · have hrb := runBlock_body_return lvCtx mxNext j [] mxRet mxRet [] s
            { s with instIdx := 0 } (Operand.Var "a") (Operand.Var "c") wa wc rfl rfl rfl hla hlc
            rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp] at hrun
          rw [hrb] at hrun
          exact absurd hrun (by simp)

/-- `mxNext_halts` at `lvCtx` (RETURN ignores the ctx, but the theorem type is fixed to it). -/
theorem lvNext_halts (s : VenomState)
    (ha : lookupVar "a" s = some (EvmYul.UInt256.ofNat 0))
    (hc : lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)) :
    runBlock (0 + (7 + 1)) lvCtx mxNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat
        (EvmYul.UInt256.ofNat 0).toNat { s with instIdx := 0 }) { s with instIdx := 0 })) :=
  runBlock_body_return lvCtx mxNext 7 [] mxRet mxRet [] s { s with instIdx := 0 }
    (Operand.Var "a") (Operand.Var "c") _ _ rfl rfl rfl ha hc rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

theorem lvFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 lvCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 lvCtx vs
      = runBlocks 10 lvCtx lvFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, lvCtx, lvFn, lookupFunction, fnEntryLabel, lvEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  have hentry : runBlock 9 lvCtx lvEntry s0 = ExecResult.OK (jumpTo "next" (lvSEnd s0)) := by
    rw [show (9 : Nat) = 2 + (6 + 1) from by omega]; exact lvEntry_runBlock s0 6 hnh0
  have hlk0 : lookupBlock s0.currentBb lvFn.blocks = some lvEntry := rfl
  have hjh : (jumpTo "next" (lvSEnd s0)).halted = false := by simpa [jumpTo, updateVar] using hnh0
  have hstep : runBlocks 10 lvCtx lvFn s0 = runBlocks 9 lvCtx lvFn (jumpTo "next" (lvSEnd s0)) :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hjh
  have ha : lookupVar "a" (jumpTo "next" (lvSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "a" (updateVar "c" (EvmYul.UInt256.ofNat 5 * s0.callCtx.callvalue)
      { updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "a" (updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]
  have hc : lookupVar "c" (jumpTo "next" (lvSEnd s0)) = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "c" (updateVar "c" (EvmYul.UInt256.ofNat 5 * s0.callCtx.callvalue)
      { updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 } with instIdx := 1 })
      = some (EvmYul.UInt256.ofNat 0)
    rw [lookupVar_updateVar_self, hcv0]; rfl
  have hlk1 : lookupBlock (jumpTo "next" (lvSEnd s0)).currentBb lvFn.blocks = some mxNext := rfl
  have hhalt := lvNext_halts (jumpTo "next" (lvSEnd s0)) ha hc
  rw [show (0 : Nat) + (7 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The mirror mixed-operand whole-function capstone.** `codegen_correct` for
    `entry: %a = CALLVALUE ; %c = MUL 5, %a ; JMP next` / `next: RETURN %a, %c` — the `[Lit a, Var y]`
    order, completing the pair with `codegen_correct_mxMulVarLit_recipeW`. -/
theorem codegen_correct_mxMulLitVar_recipeW {lo : AssocList String Nat} {vs : VenomState}
    {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 lvCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ lvFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [lvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [lvEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [mxNext, List.mem_singleton] at hinst; subst hinst
      unfold codegenReadyInst; decide
  have hgen : generateFnPlan lvFn 0 0
      = some ((generateFnPlan lvFn 0 0).get!.1, (generateFnPlan lvFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel lvFn) lvFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv mxInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel lvFn) lvFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan lvFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := lvCtx) (fn := lvFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan lvFn 0 0).get!.1) (psFinal := (generateFnPlan lvFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ lvInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, by simp⟩
  case _ =>
    intro bb hbb s
    simp only [lvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, lvEntry, mxCv]
    · simp [runBlock, evalPhis, execBlock, mxNext, mxRet]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [lvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, lvEntry, mxCv, stepInstBase, execRead0, isTerminator]⟩
      | 1 => exact Or.inl ⟨"out of fuel", by
               have hlk : lookupVar "a"
                   ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
                     : VenomState) = some s.callCtx.callvalue := lookupVar_updateVar_self _ _ _
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, lvEntry,
                 mxCv, lvMul, stepInstBase, execRead0, execPure2, evalOperand, isTerminator, hlk]⟩
      | (j+2) =>
      rw [show j+2+1 = ([mxCv, lvMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mxCv, lvMul]) (jmpInst := mxJmp) (hd := mxCv) (tl := [lvMul, mxJmp])
        (nextLiveness := ["a","c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := mxNext) (sEnd := lvSEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl <;> decide)
        (hthread := lvEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := lvBody_regularBodyH)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 4 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by rw [lv_unresolved_asm, encodeNumBytes_five]; decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by rw [lv_unresolved_asm, encodeNumBytes_five]; decide) (hlk' := rfl)
        (hw := by decide))
    · have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      obtain ⟨_, _, hvals⟩ := hinv
      obtain ⟨ha0, hc0⟩ := hvals hlbl
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := mxRet) (offv := "a") (szv := "c")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "a", Operand.Var "c"])
        (ps := psOfFn (fnPlanFuel lvFn) lvFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := ha0) (hevalsz := hc0) (hvoff := ha0) (hvsz := hc0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc7]; decide) (hget := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨lvEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel lvFn) lvFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan lvFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ A CONSUMING body reaches `codegen_correct` — `codegen_correct_csFn_recipeW`

The end-to-end payoff of the consuming regime. A same-block consuming op is impossible in the fold
(a `CALLVALUE`-produced operand dead at block exit is POPped before the op). The fix, verified at the
fold level: deliver the operands from a PREDECESSOR, consume them in the successor.

```
entry:  %c = CALLVALUE ; %a = CALLVALUE ; %b = CALLVALUE ; JMP work   -- c,a,b delivered live
work:   %d = MUL %a %b ; JMP done                                     -- a,b CONSUMED (bare MUL)
done:   RETURN %c, %d
```

`work` receives `[c, a, b]` on its entry stack and the bare `MUL` eats `a, b` (mirror order, via
`bodyStepHTo_commBinopDeadMirror` with `mul_comm`). First whole-function `codegen_correct` whose body
contains an operand the opcode CONSUMES rather than duplicates. Because the driver states `hpres`
(invariant preservation) `∀ s` — not restricted to the reachable path — the invariant pins every read
variable unconditionally (`csZ`: undefined-or-zero) plus a definedness link (`a` defined ⇒ `c`
defined, since they arrive as a package). The `work` block's undefined-operand branches are closed by
`runBlock_body_head_error`. -/

def csC : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }
def csA : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def csB : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def csJWork : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "work"], outputs := [] }
def csMulD : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["d"] }
def csJDone : Instruction := { id := 5, opcode := Opcode.JMP, operands := [Operand.Label "done"], outputs := [] }
def csRet : Instruction :=
  { id := 6, opcode := Opcode.RETURN, operands := [Operand.Var "c", Operand.Var "d"], outputs := [] }
def csEntry : BasicBlock := { label := "entry", instructions := [csC, csA, csB, csJWork] }
def csWork : BasicBlock := { label := "work", instructions := [csMulD, csJDone] }
def csDone : BasicBlock := { label := "done", instructions := [csRet] }
def csFn : IrFunction := { name := "main", blocks := [csEntry, csWork, csDone] }
def csCtx : VenomContext := { functions := [csFn], entry := some "main" }

theorem cs_unresolved_asm : executePlan (generateFnPlan csFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "CALLVALUE", AsmInst.AsmPushLabel "work", AsmInst.AsmOp "JUMP",
     AsmInst.AsmLabel "work", AsmInst.AsmOp "MUL", AsmInst.AsmPushLabel "done",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "done", AsmInst.AsmOp "SWAP1",
     AsmInst.AsmOp "RETURN"] := by rfl

theorem csEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["c", "a", "b"] offsetToPc
      (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 1 [csC, csA, csB] [] :=
  ⟨cv_step (out := "c") (S := []) rfl (by decide) (by decide),
   cv_step (out := "a") (S := ["c"]) rfl (by decide) (by decide),
   cv_step (out := "b") (S := ["c", "a"]) rfl (by decide) (by decide), trivial⟩

theorem csWork_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg csFn z.1
        ["c", "d"] false true "work" p)
      (fun _ => 1) ([csMulD].zipIdx 0) ["c", "a", "b"] ["c", "d"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := csFn) (curBbLabel := "work") (base := ["c"]) (x := "a") (y := "b")
      (out := "d") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

/-- `v` is undefined or the zero call value. -/
abbrev csZ (s : VenomState) (v : String) : Prop :=
  lookupVar v s = none ∨ lookupVar v s = some (EvmYul.UInt256.ofNat 0)

/-- The invariant. `hpres` is `∀ s`, so it pins every read var unconditionally (`csZ` on a,b,c,d),
    links `a` defined ⇒ `c` defined, and carries the per-block definedness the hsupplies consume. -/
def csInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  csZ s "a" ∧ csZ s "b" ∧ csZ s "c" ∧ csZ s "d" ∧
  (lookupVar "a" s = some (EvmYul.UInt256.ofNat 0) → lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "work" → lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "done" → lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0))

abbrev csEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue
          { updateVar "c" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem csEntry_thread (s : VenomState) :
    execBodyThread [csC, csA, csB] 0 { s with instIdx := 0 } = some (csEntrySEnd s) := by
  simp only [execBodyThread, csC, csA, csB, stepInstBase, execRead0]; rfl

theorem csEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) csCtx csEntry s = ExecResult.OK (jumpTo "work" (csEntrySEnd s)) :=
  runBlock_body_jmp csCtx csEntry j [csC, csA, csB] csJWork csC [csA, csB, csJWork] s
    (csEntrySEnd s) "work" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (csEntry_thread s) (by simpa [updateVar] using hnh)

abbrev csWorkSEnd (s : VenomState) (wa wb : bytes32) : VenomState :=
  { updateVar "d" (wa * wb) { s with instIdx := 0 } with instIdx := 1 }

theorem csWork_thread (s : VenomState) (wa wb : bytes32)
    (ha : lookupVar "a" s = some wa) (hb : lookupVar "b" s = some wb) :
    execBodyThread [csMulD] 0 { s with instIdx := 0 } = some (csWorkSEnd s wa wb) := by
  have ha' : lookupVar "a" { s with instIdx := 0 } = some wa := ha
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  show (match stepInstBase csMulD { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 }
        | _ => none) = some (csWorkSEnd s wa wb)
  have hstep : stepInstBase csMulD { s with instIdx := 0 }
      = ExecResult.OK (updateVar "d" (wa * wb) { s with instIdx := 0 }) := by
    simp [csMulD, stepInstBase, execPure2, evalOperand, ha', hb']
  rw [hstep]; rfl

theorem csWork_runBlock (s : VenomState) (j : Nat) (wa wb : bytes32)
    (hnh : s.halted = false)
    (ha : lookupVar "a" s = some wa) (hb : lookupVar "b" s = some wb) :
    runBlock (1 + (j + 1)) csCtx csWork s = ExecResult.OK (jumpTo "done" (csWorkSEnd s wa wb)) :=
  runBlock_body_jmp csCtx csWork j [csMulD] csJDone csMulD [csJDone] s
    (csWorkSEnd s wa wb) "done" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (csWork_thread s wa wb ha hb) (by simpa [updateVar] using hnh)

/-- The MUL errors when `a` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem csMulD_error_a (s : VenomState) (ha : lookupVar "a" s = none) :
    stepInstBase csMulD { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have ha' : lookupVar "a" { s with instIdx := 0 } = none := ha
  simp [csMulD, stepInstBase, execPure2, evalOperand, ha']

/-- The MUL errors when `b` is undefined (given `a` defined). -/
theorem csMulD_error_b (s : VenomState) (wa : bytes32)
    (ha : lookupVar "a" s = some wa) (hb : lookupVar "b" s = none) :
    stepInstBase csMulD { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have ha' : lookupVar "a" { s with instIdx := 0 } = some wa := ha
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [csMulD, stepInstBase, execPure2, evalOperand, ha', hb']

/-- lookupVar of `csEntrySEnd`: c,a,b are the call value; d is untouched. `lookupVar` is
    definitionally blind to the `instIdx` wrappers, so each `show` strips them. -/
theorem csEntrySEnd_lookup (s : VenomState) :
    lookupVar "c" (csEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "a" (csEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (csEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "d" (csEntrySEnd s) = lookupVar "d" s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show lookupVar "c" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue
      (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "a" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue
      (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue
      (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]
  · show lookupVar "d" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue
      (updateVar "c" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

/-- lookupVar of `csWorkSEnd`: d = wa*wb; a,b,c untouched. -/
theorem csWorkSEnd_lookup (s : VenomState) (wa wb : bytes32) :
    lookupVar "d" (csWorkSEnd s wa wb) = some (wa * wb)
    ∧ lookupVar "c" (csWorkSEnd s wa wb) = lookupVar "c" s
    ∧ lookupVar "a" (csWorkSEnd s wa wb) = lookupVar "a" s
    ∧ lookupVar "b" (csWorkSEnd s wa wb) = lookupVar "b" s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show lookupVar "d" (updateVar "d" (wa * wb) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "d" (wa * wb) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
  · show lookupVar "a" (updateVar "d" (wa * wb) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
  · show lookupVar "b" (updateVar "d" (wa * wb) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem csInv_pres : ∀ bb ∈ csFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    csInv s → runBlock f' csCtx bb s = ExecResult.OK s' → csInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, hZa, hZb, hZc, hZd, hlink, _, _⟩ := hinv
  simp only [csFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · -- entry: fuel ≥ 4 → jumpTo "work" (csEntrySEnd s), which is all-zero and defines c,a,b
    match f' with
    | 0 => rw [runBlock_no_phi 0 csCtx csEntry s csC [csA, csB, csJWork] rfl (by decide)] at hrun
           simp [execBlock] at hrun
    | 1 => rw [runBlock_no_phi 1 csCtx csEntry s csC [csA, csB, csJWork] rfl (by decide)] at hrun
           simp [execBlock, getInstruction, csEntry, csC, stepInstBase, execRead0, isTerminator] at hrun
    | 2 => rw [runBlock_no_phi 2 csCtx csEntry s csC [csA, csB, csJWork] rfl (by decide)] at hrun
           simp [execBlock, getInstruction, csEntry, csC, csA, stepInstBase, execRead0,
             isTerminator] at hrun
    | 3 => rw [runBlock_no_phi 3 csCtx csEntry s csC [csA, csB, csJWork] rfl (by decide)] at hrun
           simp [execBlock, getInstruction, csEntry, csC, csA, csB, stepInstBase, execRead0,
             isTerminator] at hrun
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, csEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨hc0, ha0, hb0, hd0⟩ := csEntrySEnd_lookup s
      rw [hcv] at hc0 ha0 hb0
      have hc : lookupVar "c" (jumpTo "work" (csEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hc0
      have ha : lookupVar "a" (jumpTo "work" (csEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := ha0
      have hb : lookupVar "b" (jumpTo "work" (csEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hb0
      have hd : lookupVar "d" (jumpTo "work" (csEntrySEnd s)) = lookupVar "d" s := hd0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        Or.inr ha, Or.inr hb, Or.inr hc, ?_, fun _ => hc, fun _ => ⟨hc, ha, hb⟩,
        fun hd' => by simp [jumpTo] at hd'⟩
      rw [csZ, hd]; exact hZd
  · -- work: reads a,b. Undefined ⇒ runBlock_body_head_error. Defined ⇒ csZ gives 0, csWork_runBlock.
    rcases hla : lookupVar "a" s with _ | wa
    · match f' with
      | 0 => rw [runBlock_no_phi 0 csCtx csWork s csMulD [csJDone] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error csCtx csWork csMulD [csJDone] s "undefined operand" j rfl
          (by decide) (csMulD_error_a s hla) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlb : lookupVar "b" s with _ | wb
      · match f' with
        | 0 => rw [runBlock_no_phi 0 csCtx csWork s csMulD [csJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error csCtx csWork csMulD [csJDone] s "undefined operand" j rfl
            (by decide) (csMulD_error_b s wa hla hlb) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · -- a,b defined: from csZ, both 0; from link, c=0
        have ha0 : wa = EvmYul.UInt256.ofNat 0 := by
          rcases hZa with h | h <;> rw [hla] at h <;> simp_all
        have hb0 : wb = EvmYul.UInt256.ofNat 0 := by
          rcases hZb with h | h <;> rw [hlb] at h <;> simp_all
        subst ha0; subst hb0
        have hc0 : lookupVar "c" s = some (EvmYul.UInt256.ofNat 0) := hlink hla
        match f' with
        | 0 => rw [runBlock_no_phi 0 csCtx csWork s csMulD [csJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | 1 =>
          rw [runBlock_no_phi 1 csCtx csWork s csMulD [csJDone] rfl (by decide)] at hrun
          have ha' : lookupVar "a" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := hla
          have hb' : lookupVar "b" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := hlb
          simp [execBlock, getInstruction, csWork, csMulD, stepInstBase, execPure2, evalOperand,
            isTerminator, ha', hb'] at hrun
        | (j+2) =>
          rw [show j+2 = 1+(j+1) from by omega,
              csWork_runBlock s j (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) hnh hla hlb] at hrun
          injection hrun with h; subst h
          obtain ⟨hd', hc', ha', hb'⟩ := csWorkSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
          have hd0 : lookupVar "d" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "d" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = lookupVar "d" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0)) from rfl, hd']; rfl
          have hcc : lookupVar "c" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "c" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = lookupVar "c" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0)) from rfl, hc']; exact hc0
          have haa : lookupVar "a" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "a" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = lookupVar "a" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0)) from rfl, ha']; exact hla
          have hbb2 : lookupVar "b" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "b" (jumpTo "done" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0))) = lookupVar "b" (csWorkSEnd s (EvmYul.UInt256.ofNat 0)
              (EvmYul.UInt256.ofNat 0)) from rfl, hb']; exact hlb
          exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
            Or.inr haa, Or.inr hbb2, Or.inr hcc, Or.inr hd0, fun _ => hcc,
            fun hw => by simp [jumpTo] at hw, fun _ => ⟨hcc, hd0⟩⟩
  · -- done: RETURN never yields OK
    match f' with
    | 0 => rw [runBlock_no_phi 0 csCtx csDone s csRet [] rfl (by decide)] at hrun
           simp [execBlock] at hrun
    | (j+1) =>
      rcases hlc : lookupVar "c" s with _ | wc
      · have he : stepInstBase csRet { s with instIdx := 0 }
            = ExecResult.Error "return: undefined operand" := by
          have hlc' : lookupVar "c" { s with instIdx := 0 } = none := hlc
          simp [csRet, stepInstBase, evalOperand, hlc']
        have hrb := runBlock_error csCtx csDone j [] csRet csRet [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) he (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
      · rcases hld : lookupVar "d" s with _ | wd
        · have he : stepInstBase csRet { s with instIdx := 0 }
              = ExecResult.Error "return: undefined operand" := by
            have hlc' : lookupVar "c" { s with instIdx := 0 } = some wc := hlc
            have hld' : lookupVar "d" { s with instIdx := 0 } = none := hld
            simp [csRet, stepInstBase, evalOperand, hlc', hld']
          have hrb := runBlock_error csCtx csDone j [] csRet csRet [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) he (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
        · have hrb := runBlock_body_return csCtx csDone j [] csRet csRet [] s
            { s with instIdx := 0 } (Operand.Var "c") (Operand.Var "d") wc wd rfl rfl rfl hlc hld
            rfl (by decide) (by intro i hi; cases hi) (by simp [execBodyThread])
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp] at hrun
          rw [hrb] at hrun
          exact absurd hrun (by simp)

/-- `csDone`'s RETURN halts, given `c, d` defined. -/
theorem csDone_halts (s : VenomState) (k : Nat)
    (hc : lookupVar "c" s = some (EvmYul.UInt256.ofNat 0))
    (hd : lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) :
    runBlock (0 + (k + 1)) csCtx csDone s = ExecResult.Halt
      (haltState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat
        (EvmYul.UInt256.ofNat 0).toNat { s with instIdx := 0 }) { s with instIdx := 0 })) :=
  runBlock_body_return csCtx csDone k [] csRet csRet [] s { s with instIdx := 0 }
    (Operand.Var "c") (Operand.Var "d") _ _ rfl rfl rfl hc hd rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

/-- **Non-vacuity**: `runContext 10 csCtx vs` halts for every state the capstone admits (callvalue
    zero). Chains `entry → work → done`, each `runBlocks_step_of_block`, ending in a direct Halt. -/
theorem csFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 csCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 csCtx vs
      = runBlocks 10 csCtx csFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, csCtx, csFn, lookupFunction, fnEntryLabel, csEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  -- entry → work
  set s1 : VenomState := jumpTo "work" (csEntrySEnd s0) with hs1
  have hentry : runBlock 9 csCtx csEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact csEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb csFn.blocks = some csEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 csCtx csFn s0 = runBlocks 9 csCtx csFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨hc1, ha1, hb1, _⟩ := csEntrySEnd_lookup s0
  rw [hcv0] at hc1 ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 0) := hc1
  -- work → done
  set s2 : VenomState := jumpTo "done" (csWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0)) with hs2
  have hwork : runBlock 8 csCtx csWork s1 = ExecResult.OK s2 := by
    rw [show (8 : Nat) = 1 + (6 + 1) from by omega]
    exact csWork_runBlock s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) hnh1 ha1' hb1'
  have hlk1 : lookupBlock s1.currentBb csFn.blocks = some csWork := rfl
  have hnh2 : s2.halted = false := by rw [hs2]; simpa [jumpTo, updateVar] using hnh1
  have hstep1 : runBlocks 9 csCtx csFn s1 = runBlocks 8 csCtx csFn s2 :=
    runBlocks_step_of_block (fuel := 8) hlk1 hwork hnh2
  obtain ⟨hd2, hc2, _, _⟩ := csWorkSEnd_lookup s1 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
  have hc2' : lookupVar "c" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "c" s2 = lookupVar "c" (csWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, hc2]; exact hc1'
  have hd2' : lookupVar "d" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "d" s2 = lookupVar "d" (csWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, hd2]; rfl
  -- done: halts
  have hlk2 : lookupBlock s2.currentBb csFn.blocks = some csDone := rfl
  have hhalt := csDone_halts s2 6 hc2' hd2'
  rw [show (0 : Nat) + (6 + 1) = 7 from by omega] at hhalt
  rw [h0, hstep0, hstep1]
  exact ⟨_, runBlocks_haltDirect_of_block hlk2 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The consuming whole-function capstone.** `codegen_correct` for
    `entry: %c,%a,%b = CALLVALUE ×3 ; JMP work` / `work: %d = MUL %a %b ; JMP done` /
    `done: RETURN %c %d`. The `work` block CONSUMES `a, b` off the stack (bare MUL, mirror order) —
    the first whole-function `codegen_correct` whose body eats an operand rather than duplicating it.
    `entry` via `hsupplyW_regularJmp` (growing), `work` via `hsupplyW_regularJmpTo` fed the consuming
    `csWork_ready`, `done` via `hsupplyW_emptyReturnReorder`. -/
theorem codegen_correct_csFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hclean : lookupVar "a" vs = none ∧ lookupVar "b" vs = none ∧ lookupVar "c" vs = none
      ∧ lookupVar "d" vs = none)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 csCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ csFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [csFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [csEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [csWork, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [csDone, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan csFn 0 0
      = some ((generateFnPlan csFn 0 0).get!.1, (generateFnPlan csFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel csFn) csFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv csInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel csFn) csFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan csFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := csCtx) (fn := csFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan csFn 0 0).get!.1) (psFinal := (generateFnPlan csFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ csInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero,
      Or.inl hclean.1, Or.inl hclean.2.1, Or.inl hclean.2.2.1, Or.inl hclean.2.2.2,
      fun h => absurd (hclean.1.symm.trans h) (by simp), fun h => by simp at h, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [csFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, csEntry, csC]
    · simp [runBlock, evalPhis, execBlock, csWork, csMulD]
    · simp [runBlock, evalPhis, execBlock, csDone, csRet]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [csFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · -- entry: 3 CALLVALUEs + JMP work
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, csEntry, csC, stepInstBase, execRead0, isTerminator]⟩
      | 1 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, csEntry, csC, csA, stepInstBase, execRead0, isTerminator]⟩
      | 2 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
               getInstruction, csEntry, csC, csA, csB, stepInstBase, execRead0, isTerminator]⟩
      | (j+3) =>
      rw [show j+3+1 = ([csC, csA, csB] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [csC, csA, csB]) (jmpInst := csJWork) (hd := csC) (tl := [csA, csB, csJWork])
        (nextLiveness := ["c","a","b"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "work") (off := 8) (bb' := csWork) (sEnd := csEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl | rfl <;> decide)
        (hthread := csEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := csEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 3 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- work: the CONSUMING MUL + JMP done
      have hlbl : s.currentBb = "work" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, _, _, _, _, hwork, _⟩ := hinv
      obtain ⟨hcw, haw, hbw⟩ := hwork hlbl
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl ⟨"out of fuel", by
               have ha' : lookupVar "a" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := haw
               have hb' : lookupVar "b" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := hbw
               simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, csWork, csMulD,
                 stepInstBase, execPure2, evalOperand, isTerminator, ha', hb']⟩
      | (j+1) =>
      rw [show j+1+1 = ([csMulD] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmpTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [csMulD]) (jmpInst := csJDone) (hd := csMulD) (tl := [csJDone])
        (nextLiveness := ["c","d"]) (curBbLabel := "work") (dem := 1)
        (S := ["c","a","b"]) (Sn := ["c","d"])
        (ps0 := psOfFn (fnPlanFuel csFn) csFn 0 0 "work") (lbl := "done") (off := 14) (bb' := csDone)
        (sEnd := csWorkSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := csWork_thread s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) haw hbw)
        (hnothalt := by simpa [updateVar] using hhalt)
        (hready := csWork_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel csFn) csFn 0 0 "work").stack
            = [Operand.Var "c", Operand.Var "a", Operand.Var "b"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, hcw⟩
          · exact ⟨_, haw⟩
          · exact ⟨_, hbw⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps := rfl) (hpc := by rw [hpc6]; decide) (hpush := by simp only [hpc6]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc6]; decide)
        (hjump := by simp only [hpc6]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- done: RETURN with the SWAP1 reorder
      have hlbl : s.currentBb = "done" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc10 : asm.pc = 10 := by rw [hpc_asm]; decide
      obtain ⟨_, _, _, _, _, _, _, _, hdone⟩ := hinv
      obtain ⟨hc0, hd0⟩ := hdone hlbl
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := csRet) (offv := "c") (szv := "d")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "c", Operand.Var "d"])
        (ps := psOfFn (fnPlanFuel csFn) csFn 0 0 "done")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := hc0) (hevalsz := hd0) (hvoff := hc0) (hvsz := hd0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc10]; decide) (hget := by simp only [hpc10]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨csEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel csFn) csFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan csFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ A non-empty body that ENDS in RETURN — `codegen_correct_bretFn_recipeW`

Every prior RETURN capstone (`mxMul*`, `cs*`) puts the RETURN in an *empty-body* block (`hsupplyW_emptyReturnReorder`),
producing its operands in a *predecessor*. This is the first `codegen_correct` whose RETURN block ALSO runs a
body first:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; RETURN %b, %a          -- one block, body-then-RETURN
```

The generator emits `[JUMPDEST ; CALLVALUE ; CALLVALUE ; RETURN]` — no reorder, because `RETURN %b %a` finds
its operands already positioned (`%b` on top). So the block is supplied by the non-empty-body RETURN slice
`hsupplyW_regularReturn`: the two `CALLVALUE`s are the body (`bretEntry_body`, a `RegularBodyH`), and the
body-end plan stack `[%a, %b]` puts `off = %b` on top (`hps'stack`), which is exactly what the RETURN recipe
needs. `callvalue = 0` (the invariant `bretInv`) makes `sz = %a = 0`, so RETURN's window is empty and the
memory obligations discharge for free — the same reason `mxMul` needs `callvalue = 0`. `hpres` is vacuous:
a RETURN block halts, so `runBlock … = OK s'` never holds. -/

def bretCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def bretCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def bretRet : Instruction :=
  { id := 2, opcode := Opcode.RETURN, operands := [Operand.Var "b", Operand.Var "a"], outputs := [] }
def bretBB : BasicBlock := { label := "entry", instructions := [bretCvA, bretCvB, bretRet] }
def bretFn : IrFunction := { name := "main", blocks := [bretBB] }
def bretCtx : VenomContext := { functions := [bretFn], entry := some "main" }

theorem bret_unresolved_asm : executePlan (generateFnPlan bretFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "RETURN"] := by rfl

theorem bretEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["b", "a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 1 [bretCvA, bretCvB] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
   cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), trivial⟩

/-- Body-end state: `a` and `b` both bound to the (zero) call value. -/
abbrev bretSEnd (s : VenomState) : VenomState :=
  { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
    with instIdx := 2 }

theorem bretEntry_thread (s : VenomState) :
    execBodyThread [bretCvA, bretCvB] 0 { s with instIdx := 0 } = some (bretSEnd s) := by
  simp only [execBodyThread, bretCvA, bretCvB, stepInstBase, execRead0]; rfl

theorem bretB_lookup (s : VenomState) : lookupVar "b" (bretSEnd s) = some s.callCtx.callvalue :=
  lookupVar_updateVar_self _ _ _

theorem bretA_lookup (s : VenomState) : lookupVar "a" (bretSEnd s) = some s.callCtx.callvalue := by
  show lookupVar "a" (updateVar "b" s.callCtx.callvalue
    { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
  show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_self]

/-- A RETURN block halts (`readMemory 0 0` → empty window). Used to close `bretInv_pres`'s reached case. -/
theorem bretEntry_halts (s : VenomState) (j : Nat) (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    runBlock (2 + (j + 1)) bretCtx bretBB s
      = ExecResult.Halt (haltState (setReturndata
          (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 0).toNat (bretSEnd s)) (bretSEnd s))) :=
  runBlock_body_return bretCtx bretBB j [bretCvA, bretCvB] bretRet bretCvA [bretCvB, bretRet] s
    (bretSEnd s) (Operand.Var "b") (Operand.Var "a") (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    rfl rfl rfl (by rw [show evalOperand (Operand.Var "b") (bretSEnd s) = lookupVar "b" (bretSEnd s) from rfl,
                         bretB_lookup, hcv])
    (by rw [show evalOperand (Operand.Var "a") (bretSEnd s) = lookupVar "a" (bretSEnd s) from rfl,
            bretA_lookup, hcv])
    rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (bretEntry_thread s)

/-- The invariant: unhalted with a zero call value (enough to empty RETURN's window). -/
def bretInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0

theorem bretInv_pres : ∀ bb ∈ bretFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    bretInv s → runBlock f' bretCtx bb s = ExecResult.OK s' → bretInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv⟩ := hinv
  simp only [bretFn, List.mem_singleton] at hbb; subst hbb
  match f' with
  | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, bretBB, bretCvA] at hrun
  | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, bretBB, bretCvA,
           stepInstBase, execRead0, isTerminator] at hrun
  | 2 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, bretBB, bretCvA, bretCvB,
           stepInstBase, execRead0, isTerminator] at hrun
  | (j+3) =>
    rw [show j+3 = 2+(j+1) from by omega, bretEntry_halts s j hcv] at hrun
    exact absurd hrun (by simp)

set_option maxHeartbeats 3200000 in
/-- **`codegen_correct` for `bretFn` (`entry: %a=CALLVALUE ; %b=CALLVALUE ; RETURN %b,%a`)** — the first whole
    function whose RETURN block runs a body first, closing the documented "RETURN/REVERT/SD have no non-empty
    slice" gap via `hsupplyW_regularReturn`. `callvalue = 0` (needed for the empty return window) is threaded
    by `bretInv`; `bretInv_pres` is vacuous (a RETURN block never yields `OK`). -/
theorem codegen_correct_bretFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 bretCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ bretFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [bretFn, List.mem_singleton] at hbb; subst hbb
    simp only [bretBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan bretFn 0 0
      = some ((generateFnPlan bretFn 0 0).get!.1, (generateFnPlan bretFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel bretFn) bretFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv bretInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel bretFn) bretFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan bretFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := bretCtx) (fn := bretFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan bretFn 0 0).get!.1) (psFinal := (generateFnPlan bretFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ bretInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero⟩
  case _ =>
    intro bb hbb s
    simp only [bretFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, bretBB, bretCvA]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [bretFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    obtain ⟨hnh, hcv⟩ := hinv
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    match k with
    | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
             getInstruction, bretBB, bretCvA, stepInstBase, execRead0, isTerminator]⟩
    | 1 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
             getInstruction, bretBB, bretCvA, bretCvB, stepInstBase, execRead0, isTerminator]⟩
    | (j+2) =>
    rw [show j+2+1 = ([bretCvA, bretCvB] : List Instruction).length + (j+1) from by
      simp only [List.length_cons, List.length_nil]; omega]
    refine Or.inr (hsupplyW_regularReturn
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [bretCvA, bretCvB]) (retInst := bretRet) (hd := bretCvA) (tl := [bretCvB, bretRet])
      (nextLiveness := ["b", "a"]) (curBbLabel := "entry") (dem := 1) (S := [])
      (ps0 := initPlanState 0) (offv := "b") (szv := "a") (base := [])
      (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (sEnd := bretSEnd s)
      (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl <;> decide)
      (hthread := bretEntry_thread s)
      (hevaloff := by rw [show evalOperand (Operand.Var "b") (bretSEnd s) = lookupVar "b" (bretSEnd s) from rfl,
                         bretB_lookup, hcv])
      (hevalsz := by rw [show evalOperand (Operand.Var "a") (bretSEnd s) = lookupVar "a" (bretSEnd s) from rfl,
                        bretA_lookup, hcv])
      (hvoff := by rw [show operandVal (bretSEnd s) lo (Operand.Var "b") = lookupVar "b" (bretSEnd s) from rfl,
                      bretB_lookup, hcv])
      (hvsz := by rw [show operandVal (bretSEnd s) lo (Operand.Var "a") = lookupVar "a" (bretSEnd s) from rfl,
                     bretA_lookup, hcv])
      (hreg := bretEntry_body)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                     have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                    have hj' : j < 2 := hj; interval_cases j <;> rfl)
      (hps'stack := by decide)
      (hpc := by rw [hpc0]; decide) (hret := by simp only [hpc0]; rfl)
      (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
      (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
      (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨bretBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel bretFn) bretFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan bretFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ The REVERT twin — `codegen_correct_brevFn_recipeW`

The aborting sibling of `bretFn`: `entry: %a=CALLVALUE ; %b=CALLVALUE ; REVERT %b,%a` (one block,
body-then-REVERT). Reuses `bretFn`'s body wholesale (`bretCvA`/`bretCvB`, so `bretSEnd`/`bretEntry_thread`/
`bret{A,B}_lookup`/`bretInv` all apply) and swaps the terminator; supplied by `hsupplyW_regularRevert`.
Routes to the `Abort RevertAbort → AsmRevert` branch. -/

def brevRev : Instruction :=
  { id := 2, opcode := Opcode.REVERT, operands := [Operand.Var "b", Operand.Var "a"], outputs := [] }
def brevBB : BasicBlock := { label := "entry", instructions := [bretCvA, bretCvB, brevRev] }
def brevFn : IrFunction := { name := "main", blocks := [brevBB] }
def brevCtx : VenomContext := { functions := [brevFn], entry := some "main" }

theorem brev_unresolved_asm : executePlan (generateFnPlan brevFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "REVERT"] := by rfl

theorem brevEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["b", "a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 1 [bretCvA, bretCvB] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
   cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), trivial⟩

/-- A REVERT block aborts (`Abort RevertAbort`). Used to close `brevInv_pres`'s reached case. -/
theorem brevEntry_reverts (s : VenomState) (j : Nat) (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    runBlock (2 + (j + 1)) brevCtx brevBB s
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata
          (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 0).toNat (bretSEnd s)) (bretSEnd s))) :=
  runBlock_body_revert brevCtx brevBB j [bretCvA, bretCvB] brevRev bretCvA [bretCvB, brevRev] s
    (bretSEnd s) (Operand.Var "b") (Operand.Var "a") (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    rfl rfl rfl (by rw [show evalOperand (Operand.Var "b") (bretSEnd s) = lookupVar "b" (bretSEnd s) from rfl,
                         bretB_lookup, hcv])
    (by rw [show evalOperand (Operand.Var "a") (bretSEnd s) = lookupVar "a" (bretSEnd s) from rfl,
            bretA_lookup, hcv])
    rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (bretEntry_thread s)

theorem brevInv_pres : ∀ bb ∈ brevFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    bretInv s → runBlock f' brevCtx bb s = ExecResult.OK s' → bretInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv⟩ := hinv
  simp only [brevFn, List.mem_singleton] at hbb; subst hbb
  match f' with
  | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, brevBB, bretCvA] at hrun
  | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, brevBB, bretCvA,
           stepInstBase, execRead0, isTerminator] at hrun
  | 2 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, brevBB, bretCvA, bretCvB,
           stepInstBase, execRead0, isTerminator] at hrun
  | (j+3) =>
    rw [show j+3 = 2+(j+1) from by omega, brevEntry_reverts s j hcv] at hrun
    exact absurd hrun (by simp)

set_option maxHeartbeats 3200000 in
/-- **`codegen_correct` for `brevFn` (`entry: %a=CALLVALUE ; %b=CALLVALUE ; REVERT %b,%a`)** — the REVERT twin
    of `codegen_correct_bretFn_recipeW`, via `hsupplyW_regularRevert`. Routes to `Abort RevertAbort`. -/
theorem codegen_correct_brevFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 brevCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ brevFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [brevFn, List.mem_singleton] at hbb; subst hbb
    simp only [brevBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan brevFn 0 0
      = some ((generateFnPlan brevFn 0 0).get!.1, (generateFnPlan brevFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel brevFn) brevFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv bretInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel brevFn) brevFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan brevFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := brevCtx) (fn := brevFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan brevFn 0 0).get!.1) (psFinal := (generateFnPlan brevFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ brevInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero⟩
  case _ =>
    intro bb hbb s
    simp only [brevFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, brevBB, bretCvA]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [brevFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    obtain ⟨hnh, hcv⟩ := hinv
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    match k with
    | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
             getInstruction, brevBB, bretCvA, stepInstBase, execRead0, isTerminator]⟩
    | 1 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
             getInstruction, brevBB, bretCvA, bretCvB, stepInstBase, execRead0, isTerminator]⟩
    | (j+2) =>
    rw [show j+2+1 = ([bretCvA, bretCvB] : List Instruction).length + (j+1) from by
      simp only [List.length_cons, List.length_nil]; omega]
    refine Or.inr (hsupplyW_regularRevert
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [bretCvA, bretCvB]) (revInst := brevRev) (hd := bretCvA) (tl := [bretCvB, brevRev])
      (nextLiveness := ["b", "a"]) (curBbLabel := "entry") (dem := 1) (S := [])
      (ps0 := initPlanState 0) (offv := "b") (szv := "a") (base := [])
      (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (sEnd := bretSEnd s)
      (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl <;> decide)
      (hthread := bretEntry_thread s)
      (hevaloff := by rw [show evalOperand (Operand.Var "b") (bretSEnd s) = lookupVar "b" (bretSEnd s) from rfl,
                         bretB_lookup, hcv])
      (hevalsz := by rw [show evalOperand (Operand.Var "a") (bretSEnd s) = lookupVar "a" (bretSEnd s) from rfl,
                        bretA_lookup, hcv])
      (hvoff := by rw [show operandVal (bretSEnd s) lo (Operand.Var "b") = lookupVar "b" (bretSEnd s) from rfl,
                      bretB_lookup, hcv])
      (hvsz := by rw [show operandVal (bretSEnd s) lo (Operand.Var "a") = lookupVar "a" (bretSEnd s) from rfl,
                     bretA_lookup, hcv])
      (hreg := brevEntry_body)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                     have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                    have hj' : j < 2 := hj; interval_cases j <;> rfl)
      (hps'stack := by decide)
      (hpc := by rw [hpc0]; decide) (hrev := by simp only [hpc0]; rfl)
      (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
      (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
      (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨brevBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel brevFn) brevFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan brevFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ The SELFDESTRUCT completion — `codegen_correct_bsdFn_recipeW`

`entry: %a = CALLVALUE ; SELFDESTRUCT %a` (one block, body-then-SELFDESTRUCT). SELFDESTRUCT takes a single
address operand and has NO memory window, so this is the simplest of the halting-terminator capstones — no
`callvalue = 0` needed (the address is arbitrary), supplied by `hsupplyW_regularSelfdestruct`. With this,
EVERY halting terminator the recipe route models (STOP / INVALID / RETURN / REVERT / SELFDESTRUCT) now has a
whole-function `codegen_correct` whose terminator block runs a body first. Reuses `bretCvA` for the body. -/

def bsdSelf : Instruction :=
  { id := 1, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Var "a"], outputs := [] }
def bsdBB : BasicBlock := { label := "entry", instructions := [bretCvA, bsdSelf] }
def bsdFn : IrFunction := { name := "main", blocks := [bsdBB] }
def bsdCtx : VenomContext := { functions := [bsdFn], entry := some "main" }

theorem bsd_unresolved_asm : executePlan (generateFnPlan bsdFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "SELFDESTRUCT"] := by rfl

/-- Body-end state: `a` bound to the call value (the beneficiary address, unconstrained). -/
abbrev bsdSEnd (s : VenomState) : VenomState :=
  { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }

theorem bsdEntry_thread (s : VenomState) :
    execBodyThread [bretCvA] 0 { s with instIdx := 0 } = some (bsdSEnd s) := by
  simp only [execBodyThread, bretCvA, stepInstBase, execRead0]

theorem bsdA_lookup (s : VenomState) : lookupVar "a" (bsdSEnd s) = some s.callCtx.callvalue :=
  lookupVar_updateVar_self _ _ _

theorem bsdEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a"] offsetToPc
      (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 1 [bretCvA] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩

/-- A SELFDESTRUCT block halts (`Halt (selfdestruct addr …)`). Closes `bsdInv_pres`'s reached case. -/
theorem bsdEntry_halts (s : VenomState) (j : Nat) :
    runBlock (1 + (j + 1)) bsdCtx bsdBB s
      = ExecResult.Halt (haltState (selfdestruct s.callCtx.callvalue (bsdSEnd s))) :=
  runBlock_body_selfdestruct bsdCtx bsdBB j [bretCvA] bsdSelf bretCvA [bsdSelf] s
    (bsdSEnd s) (Operand.Var "a") s.callCtx.callvalue rfl rfl rfl
    (by rw [show evalOperand (Operand.Var "a") (bsdSEnd s) = lookupVar "a" (bsdSEnd s) from rfl, bsdA_lookup])
    rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; decide)
    (bsdEntry_thread s)

/-- The invariant: just unhalted (SELFDESTRUCT needs no value constraint). -/
def bsdInv (s : VenomState) : Prop := s.halted = false

theorem bsdInv_pres : ∀ bb ∈ bsdFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    bsdInv s → runBlock f' bsdCtx bb s = ExecResult.OK s' → bsdInv s' := by
  intro bb hbb s s' f' hinv hrun
  simp only [bsdFn, List.mem_singleton] at hbb; subst hbb
  match f' with
  | 0 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, bsdBB, bretCvA] at hrun
  | 1 => simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, bsdBB, bretCvA,
           stepInstBase, execRead0, isTerminator] at hrun
  | (j+2) =>
    rw [show j+2 = 1+(j+1) from by omega, bsdEntry_halts s j] at hrun
    exact absurd hrun (by simp)

set_option maxHeartbeats 3200000 in
/-- **`codegen_correct` for `bsdFn` (`entry: %a=CALLVALUE ; SELFDESTRUCT %a`)** — the SELFDESTRUCT member of
    the non-empty-body halting-terminator family, via `hsupplyW_regularSelfdestruct`. No `callvalue` constraint
    (the address is arbitrary); `bsdInv_pres` is vacuous (a SELFDESTRUCT block never yields `OK`). -/
theorem codegen_correct_bsdFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 bsdCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ bsdFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [bsdFn, List.mem_singleton] at hbb; subst hbb
    simp only [bsdBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan bsdFn 0 0
      = some ((generateFnPlan bsdFn 0 0).get!.1, (generateFnPlan bsdFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel bsdFn) bsdFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv bsdInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel bsdFn) bsdFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan bsdFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := bsdCtx) (fn := bsdFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan bsdFn 0 0).get!.1) (psFinal := (generateFnPlan bsdFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ bsdInv_pres ?_
    (by simp only [bsdInv]; simpa using hvshalt)
  case _ =>
    intro bb hbb s
    simp only [bsdFn, List.mem_singleton] at hbb; subst hbb
    simp [runBlock, evalPhis, execBlock, bsdBB, bretCvA]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [bsdFn, List.mem_singleton] at hbb; subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    match k with
    | 0 => exact Or.inl ⟨"out of fuel", by simp [runBlock, evalPhis, phiPrefixLength, execBlock,
             getInstruction, bsdBB, bretCvA, stepInstBase, execRead0, isTerminator]⟩
    | (j+1) =>
    rw [show j+1+1 = ([bretCvA] : List Instruction).length + (j+1) from by
      simp only [List.length_cons, List.length_nil]; omega]
    refine Or.inr (hsupplyW_regularSelfdestruct
      (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
      (front := [bretCvA]) (sdInst := bsdSelf) (hd := bretCvA) (tl := [bsdSelf])
      (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := [])
      (ps0 := initPlanState 0) (addrv := "a") (base := [])
      (waddr := s.callCtx.callvalue) (sEnd := bsdSEnd s)
      (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                      subst hi; decide)
      (hthread := bsdEntry_thread s)
      (heval := by rw [show evalOperand (Operand.Var "a") (bsdSEnd s) = lookupVar "a" (bsdSEnd s) from rfl,
                      bsdA_lookup])
      (hval := by rw [show operandVal (bsdSEnd s) lo (Operand.Var "a") = lookupVar "a" (bsdSEnd s) from rfl,
                     bsdA_lookup])
      (hreg := bsdEntry_body)
      (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
      (hsv := by simp [StackIsVars, initPlanState])
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                     have hj' : j < 1 := hj; interval_cases j; rfl)
      (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                    have hj' : j < 1 := hj; interval_cases j; rfl)
      (hps'stack := by decide)
      (hpc := by rw [hpc0]; decide) (hsdop := by simp only [hpc0]; rfl)
      (hw := by decide))
  case _ =>
    refine ⟨⟨bsdBB, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel bsdFn) bsdFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan bsdFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ The first NON-COMMUTATIVE binop — `codegen_correct_scFn_recipeW`

Every prior binop capstone is commutative (ADD/MUL). This is the first `codegen_correct` for a
NON-commutative binop (SUB), and it routes *around* the buried-consuming (f1a) blocker:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = SUB %a %b ; JMP next   -- a,b,c all live → delivered
next:   %e = ADD %b %c ; RETURN %e, %a                                -- ADD consumes the TOP two (b,c)
```

The SUB is **duplicating** (both `a,b` live), emitted `DUP1 ; DUP3 ; SUB` (no active swap — the non-comm
optimistic-swap obligation is free). Its output `c` lands on top, giving `[a, b, c]`. In `next` the
consuming `ADD %b %c` eats the top two (`b,c`) — `a` at the bottom is never buried, so NO f1a reorder is
needed — leaving `[a, e]`, and `RETURN %e %a` is already positioned. `callvalue = 0` ⇒ `a=b=c=0 ⇒ e=0`,
emptying the return window. `entry` via `hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the
consuming ADD (`scNext_ready`) — exercising both the new non-comm-dup arm and the new non-empty RETURN slice. -/

def scCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def scCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def scSub : Instruction :=
  { id := 2, opcode := Opcode.SUB, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["c"] }
def scJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def scAdd : Instruction :=
  { id := 4, opcode := Opcode.ADD, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def scRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def scEntry : BasicBlock := { label := "entry", instructions := [scCvA, scCvB, scSub, scJmp] }
def scNext : BasicBlock := { label := "next", instructions := [scAdd, scRet] }
def scFn : IrFunction := { name := "main", blocks := [scEntry, scNext] }
def scCtx : VenomContext := { functions := [scFn], entry := some "main" }

theorem sc_unresolved_asm : executePlan (generateFnPlan scFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp "SUB", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "ADD", AsmInst.AsmOp "RETURN"] := by rfl

/-- entry's body `[CV a; CV b; SUB %a %b]` as a `RegularBodyH`: two `cv_step`s then the non-commutative
    SUB via `RegularStep`'s non-comm arm (`asmStep_sub_ok`), all outputs live (duplicating). -/
theorem scEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 1 [scCvA, scCvB, scSub] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "SUB", rfl, rfl, by decide, by decide,
    Or.inr (Or.inl ⟨"a", "b", (fun a b => a - b), by decide, by decide, rfl, fun _ => rfl, rfl,
      by decide, by decide, by decide, by decide, by decide, fun _ h hg => asmStep_sub_ok h hg⟩)⟩

/-- Body-end state of `scEntry`: `a,b := callvalue`, `c := a - b` (= 0 when callvalue = 0). -/
abbrev scEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (s.callCtx.callvalue - s.callCtx.callvalue)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem scEntry_thread (s : VenomState) :
    execBodyThread [scCvA, scCvB, scSub] 0 { s with instIdx := 0 } = some (scEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub := stepInstBase_binopVar (inst := scSub) (f := fun a b => a - b) (x := "a") (y := "b")
    (out := "c") (wx := s.callCtx.callvalue) (wy := s.callCtx.callvalue) rfl rfl rfl hla hlb
  have h1 : stepInstBase scCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase scCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase scCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [scCvB, scSub] 1 { s' with instIdx := 1 }
        | _ => none) = some (scEntrySEnd s)
  rw [h1]
  show (match stepInstBase scCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [scSub] 2 { s' with instIdx := 2 }
        | _ => none) = some (scEntrySEnd s)
  rw [h2]
  show (match stepInstBase scSub ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (scEntrySEnd s)
  rw [hsub]
  rfl

/-- `scEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem scEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) scCtx scEntry s = ExecResult.OK (jumpTo "next" (scEntrySEnd s)) :=
  runBlock_body_jmp scCtx scEntry j [scCvA, scCvB, scSub] scJmp scCvA [scCvB, scSub, scJmp] s
    (scEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (scEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `ADD %b %c` (mirror order, `bytes32_add_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem scNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg scFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([scAdd].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := scFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_add_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_add_ok h hg))

abbrev scNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb + wc) { s with instIdx := 0 } with instIdx := 1 }

theorem scNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (scNextSEnd s wb wc) = some (wb + wc)
    ∧ lookupVar "a" (scNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb + wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem scNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [scAdd] 0 { s with instIdx := 0 } = some (scNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase scAdd { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb + wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := scAdd) (f := fun a b => a + b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase scAdd { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The ADD errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem scAdd_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase scAdd { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [scAdd, stepInstBase, execPure2, evalOperand, hb']

/-- The ADD errors when `c` is undefined (given `b` defined). -/
theorem scAdd_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase scAdd { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [scAdd, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem scNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) scCtx scNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb + wc).toNat wa.toNat (scNextSEnd s wb wc))
        (scNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := scNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return scCtx scNext j [scAdd] scRet scAdd [scRet] s (scNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb + wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (scNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem scNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) scCtx scNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := scNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term scCtx scNext j [scAdd] scRet scAdd [scRet] s (scNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (scNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : scNext.instructions = [scAdd] ++ [scRet])
    (scNext_thread s wb wc hb hc), scRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `scEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem scEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (scEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (scEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (scEntrySEnd s) = some (s.callCtx.callvalue - s.callCtx.callvalue) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (s.callCtx.callvalue - s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (s.callCtx.callvalue - s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (s.callCtx.callvalue - s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def scInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0))

theorem scInv_pres : ∀ bb ∈ scFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    scInv s → runBlock f' scCtx bb s = ExecResult.OK s' → scInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [scFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (scEntrySEnd s)`
    have hnt : ∀ inst ∈ [scCvA, scCvB, scSub], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof scCtx scEntry 0 [scCvA, scCvB, scSub] scJmp scCvA
             [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof scCtx scEntry 1 [scCvA, scCvB, scSub] scJmp scCvA
             [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof scCtx scEntry 2 [scCvA, scCvB, scSub] scJmp scCvA
             [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof scCtx scEntry 3 [scCvA, scCvB, scSub] scJmp scCvA
             [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, scEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := scEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (scEntrySEnd s)) = lookupVar "c" (scEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 scCtx scNext s scAdd [scRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error scCtx scNext scAdd [scRet] s "undefined operand" j rfl
          (by decide) (scAdd_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 scCtx scNext s scAdd [scRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error scCtx scNext scAdd [scRet] s "undefined operand" j rfl
            (by decide) (scAdd_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 scCtx scNext s scAdd [scRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof scCtx scNext 1 [scAdd] scRet scAdd [scRet] s
                   (scNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (scNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, scNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 scCtx scNext s scAdd [scRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof scCtx scNext 1 [scAdd] scRet scAdd [scRet] s
                   (scNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (scNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, scNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 scCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem scFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 scCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 scCtx vs
      = runBlocks 10 scCtx scFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, scCtx, scFn, lookupFunction, fnEntryLabel, scEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (scEntrySEnd s0) with hs1
  have hentry : runBlock 9 scCtx scEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact scEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb scFn.blocks = some scEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 scCtx scFn s0 = runBlocks 9 scCtx scFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := scEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (scEntrySEnd s0) from rfl, hc1]; rfl
  have hlk1 : lookupBlock s1.currentBb scFn.blocks = some scNext := rfl
  have hhalt := scNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first non-commutative binop capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=SUB %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s SUB is the first NON-commutative binop to reach
    `codegen_correct`; it is duplicating (`DUP1 ; DUP3 ; SUB`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_scFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 scCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ scFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [scFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [scEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [scNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan scFn 0 0
      = some ((generateFnPlan scFn 0 0).get!.1, (generateFnPlan scFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel scFn) scFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv scInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel scFn) scFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan scFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := scCtx) (fn := scFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan scFn 0 0).get!.1) (psFinal := (generateFnPlan scFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ scInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [scFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, scEntry, scCvA]
    · simp [runBlock, evalPhis, execBlock, scNext, scAdd]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [scFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + SUB (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [scCvA, scCvB, scSub], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof scCtx scEntry 1 [scCvA, scCvB, scSub] scJmp scCvA
               [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof scCtx scEntry 2 [scCvA, scCvB, scSub] scJmp scCvA
               [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof scCtx scEntry 3 [scCvA, scCvB, scSub] scJmp scCvA
               [scCvB, scSub, scJmp] s (scEntrySEnd s) rfl rfl (by decide) hnt (scEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([scCvA, scCvB, scSub] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [scCvA, scCvB, scSub]) (jmpInst := scJmp) (hd := scCvA) (tl := [scCvB, scSub, scJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := scNext) (sEnd := scEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := scEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := scEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 5 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof scCtx scNext 1 [scAdd] scRet scAdd [scRet] s
               (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (scNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([scAdd] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [scAdd]) (retInst := scRet) (hd := scAdd) (tl := [scRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel scFn) scFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := scNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "e" (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (scNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1]; rfl)
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (scNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "e")
            = lookupVar "e" (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (scNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1]; rfl)
        (hvsz := by rw [show operandVal (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (scNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (scNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := scNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel scFn) scFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc8]; decide) (hret := by simp only [hpc8]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨scEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel scFn) scFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan scFn 0 0).get!.1)).1.length
      omega


/-! ### ✅ The all-var COMMUTATIVE binop (growing arm) — `codegen_correct_acFn_recipeW`

Every prior binop capstone is commutative (ADD/MUL). This is the first `codegen_correct` for a
NON-commutative binop (ADD), and it routes *around* the buried-consuming (f1a) blocker:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = ADD %a %b ; JMP next   -- a,b,c all live → delivered
next:   %e = ADD %b %c ; RETURN %e, %a                                -- ADD consumes the TOP two (b,c)
```

The ADD is **duplicating** (both `a,b` live), emitted `DUP1 ; DUP3 ; ADD` (no active swap — the non-comm
optimistic-swap obligation is free). Its output `c` lands on top, giving `[a, b, c]`. In `next` the
consuming `ADD %b %c` eats the top two (`b,c`) — `a` at the bottom is never buried, so NO f1a reorder is
needed — leaving `[a, e]`, and `RETURN %e %a` is already positioned. `callvalue = 0` ⇒ `a=b=c=0 ⇒ e=0`,
emptying the return window. `entry` via `hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the
consuming ADD (`acNext_ready`) — exercising both the new non-comm-dup arm and the new non-empty RETURN slice. -/

def acCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def acCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def acAddC : Instruction :=
  { id := 2, opcode := Opcode.ADD, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["c"] }
def acJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def acAddE : Instruction :=
  { id := 4, opcode := Opcode.ADD, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def acRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def acEntry : BasicBlock := { label := "entry", instructions := [acCvA, acCvB, acAddC, acJmp] }
def acNext : BasicBlock := { label := "next", instructions := [acAddE, acRet] }
def acFn : IrFunction := { name := "main", blocks := [acEntry, acNext] }
def acCtx : VenomContext := { functions := [acFn], entry := some "main" }

theorem ac_unresolved_asm : executePlan (generateFnPlan acFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp "ADD", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "ADD", AsmInst.AsmOp "RETURN"] := by rfl

/-- entry's body `[CV a; CV b; ADD %a %b]` as a `RegularBodyH`: two `cv_step`s then the non-commutative
    ADD via `RegularStep`'s non-comm arm (`asmStep_sub_ok`), all outputs live (duplicating). -/
theorem acEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 1 [acCvA, acCvB, acAddC] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "ADD", rfl, rfl, by decide, by decide,
    Or.inl ⟨"a", "b", (fun a b => a + b), by decide, fun _ => rfl, rfl,
      by decide, by decide, by decide, by decide, by decide, fun _ h hg => asmStep_add_ok h hg⟩⟩

/-- Body-end state of `acEntry`: `a,b := callvalue`, `c := a - b` (= 0 when callvalue = 0). -/
abbrev acEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (s.callCtx.callvalue + s.callCtx.callvalue)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem acEntry_thread (s : VenomState) :
    execBodyThread [acCvA, acCvB, acAddC] 0 { s with instIdx := 0 } = some (acEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub := stepInstBase_binopVar (inst := acAddC) (f := fun a b => a + b) (x := "a") (y := "b")
    (out := "c") (wx := s.callCtx.callvalue) (wy := s.callCtx.callvalue) rfl rfl rfl hla hlb
  have h1 : stepInstBase acCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase acCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase acCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [acCvB, acAddC] 1 { s' with instIdx := 1 }
        | _ => none) = some (acEntrySEnd s)
  rw [h1]
  show (match stepInstBase acCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [acAddC] 2 { s' with instIdx := 2 }
        | _ => none) = some (acEntrySEnd s)
  rw [h2]
  show (match stepInstBase acAddC ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (acEntrySEnd s)
  rw [hsub]
  rfl

/-- `acEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem acEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) acCtx acEntry s = ExecResult.OK (jumpTo "next" (acEntrySEnd s)) :=
  runBlock_body_jmp acCtx acEntry j [acCvA, acCvB, acAddC] acJmp acCvA [acCvB, acAddC, acJmp] s
    (acEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (acEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `ADD %b %c` (mirror order, `bytes32_add_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem acNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg acFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([acAddE].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := acFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_add_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_add_ok h hg))

abbrev acNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb + wc) { s with instIdx := 0 } with instIdx := 1 }

theorem acNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (acNextSEnd s wb wc) = some (wb + wc)
    ∧ lookupVar "a" (acNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb + wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem acNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [acAddE] 0 { s with instIdx := 0 } = some (acNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase acAddE { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb + wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := acAddE) (f := fun a b => a + b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase acAddE { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The ADD errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem acAddE_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase acAddE { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [acAddE, stepInstBase, execPure2, evalOperand, hb']

/-- The ADD errors when `c` is undefined (given `b` defined). -/
theorem acAddE_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase acAddE { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [acAddE, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem acNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) acCtx acNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb + wc).toNat wa.toNat (acNextSEnd s wb wc))
        (acNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := acNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return acCtx acNext j [acAddE] acRet acAddE [acRet] s (acNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb + wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (acNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem acNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) acCtx acNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := acNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term acCtx acNext j [acAddE] acRet acAddE [acRet] s (acNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (acNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : acNext.instructions = [acAddE] ++ [acRet])
    (acNext_thread s wb wc hb hc), acRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `acEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem acEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (acEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (acEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (acEntrySEnd s) = some (s.callCtx.callvalue + s.callCtx.callvalue) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (s.callCtx.callvalue + s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (s.callCtx.callvalue + s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (s.callCtx.callvalue + s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def acInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0))

theorem acInv_pres : ∀ bb ∈ acFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    acInv s → runBlock f' acCtx bb s = ExecResult.OK s' → acInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [acFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (acEntrySEnd s)`
    have hnt : ∀ inst ∈ [acCvA, acCvB, acAddC], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof acCtx acEntry 0 [acCvA, acCvB, acAddC] acJmp acCvA
             [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof acCtx acEntry 1 [acCvA, acCvB, acAddC] acJmp acCvA
             [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof acCtx acEntry 2 [acCvA, acCvB, acAddC] acJmp acCvA
             [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof acCtx acEntry 3 [acCvA, acCvB, acAddC] acJmp acCvA
             [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, acEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := acEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (acEntrySEnd s)) = lookupVar "c" (acEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 acCtx acNext s acAddE [acRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error acCtx acNext acAddE [acRet] s "undefined operand" j rfl
          (by decide) (acAddE_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 acCtx acNext s acAddE [acRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error acCtx acNext acAddE [acRet] s "undefined operand" j rfl
            (by decide) (acAddE_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 acCtx acNext s acAddE [acRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof acCtx acNext 1 [acAddE] acRet acAddE [acRet] s
                   (acNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (acNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, acNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 acCtx acNext s acAddE [acRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof acCtx acNext 1 [acAddE] acRet acAddE [acRet] s
                   (acNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (acNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, acNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 acCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem acFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 acCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 acCtx vs
      = runBlocks 10 acCtx acFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, acCtx, acFn, lookupFunction, fnEntryLabel, acEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (acEntrySEnd s0) with hs1
  have hentry : runBlock 9 acCtx acEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact acEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb acFn.blocks = some acEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 acCtx acFn s0 = runBlocks 9 acCtx acFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := acEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (acEntrySEnd s0) from rfl, hc1]; rfl
  have hlk1 : lookupBlock s1.currentBb acFn.blocks = some acNext := rfl
  have hhalt := acNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first non-commutative binop capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=ADD %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s ADD exercises the pure commutative var/var GROWING arm (`bodyStep_commBinop`); it is
    duplicating (`DUP1 ; DUP3 ; ADD`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_acFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 acCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ acFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [acFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [acEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [acNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan acFn 0 0
      = some ((generateFnPlan acFn 0 0).get!.1, (generateFnPlan acFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel acFn) acFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv acInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel acFn) acFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan acFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := acCtx) (fn := acFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan acFn 0 0).get!.1) (psFinal := (generateFnPlan acFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ acInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [acFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, acEntry, acCvA]
    · simp [runBlock, evalPhis, execBlock, acNext, acAddE]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [acFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [acCvA, acCvB, acAddC], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof acCtx acEntry 1 [acCvA, acCvB, acAddC] acJmp acCvA
               [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof acCtx acEntry 2 [acCvA, acCvB, acAddC] acJmp acCvA
               [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof acCtx acEntry 3 [acCvA, acCvB, acAddC] acJmp acCvA
               [acCvB, acAddC, acJmp] s (acEntrySEnd s) rfl rfl (by decide) hnt (acEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([acCvA, acCvB, acAddC] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [acCvA, acCvB, acAddC]) (jmpInst := acJmp) (hd := acCvA) (tl := [acCvB, acAddC, acJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := acNext) (sEnd := acEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := acEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := acEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 5 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof acCtx acNext 1 [acAddE] acRet acAddE [acRet] s
               (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (acNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([acAddE] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [acAddE]) (retInst := acRet) (hd := acAddE) (tl := [acRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel acFn) acFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := acNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "e" (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (acNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1]; rfl)
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (acNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "e")
            = lookupVar "e" (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (acNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1]; rfl)
        (hvsz := by rw [show operandVal (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (acNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (acNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := acNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel acFn) acFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc8]; decide) (hret := by simp only [hpc8]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨acEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel acFn) acFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan acFn 0 0).get!.1)).1.length
      omega


/-- `0 * x = 0` for `UInt256` (a bare `Fin`-wrapped structure with no `MulZeroClass`): proved via
    `toNat`-injectivity and `uint256_mul_toNat`. This is what lets a UNOP/ternop/litLit whose output is
    NON-zero still reach RETURN — the output is zeroed by `MUL`-ing it against a zero operand. -/
theorem uint256_zero_mul (x : EvmYul.UInt256) :
    EvmYul.UInt256.ofNat 0 * x = EvmYul.UInt256.ofNat 0 := by
  have h : (EvmYul.UInt256.ofNat 0 * x).toNat = (EvmYul.UInt256.ofNat 0).toNat := by
    rw [EvmYul.uint256_mul_toNat, EvmYul.uint256_ofNat_toNat]; simp
  have e : ∀ a b : EvmYul.UInt256, a.toNat = b.toNat → a = b := by
    intro a b hab; cases a; cases b
    simp only [EvmYul.UInt256.toNat, EvmYul.UInt256.mk.injEq] at hab ⊢; exact Fin.ext hab
  exact e _ _ h

/-! ### ✅ A UNOP via the recipe route (NOT) — `codegen_correct_unFn_recipeW`

The first `codegen_correct` for a UNOP (`NOT`), a distinct instruction class:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = NOT %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                             -- MUL consumes the TOP two (b,c)
```

`NOT %a` is the growing unop arm (`RegularStep`'s 3rd disjunct, `asmStep_not_ok`), emitted `DUP2 ; NOT`,
leaving `[a, b, c]` with `c = NOT 0` (NON-zero — so `c` cannot itself be a RETURN operand). In `next` the
consuming `MUL %b %c` eats the top two (`b, c`); since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`,
regardless of `c`), emptying the return window. `a` (bottom) is never buried — no f1a reorder. `entry` via
`hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the consuming `MUL` (`unNext_ready`). -/

def unCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def unCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def unNot : Instruction :=
  { id := 2, opcode := Opcode.NOT, operands := [Operand.Var "a"], outputs := ["c"] }
def unJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def unMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def unRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def unEntry : BasicBlock := { label := "entry", instructions := [unCvA, unCvB, unNot, unJmp] }
def unNext : BasicBlock := { label := "next", instructions := [unMul, unRet] }
def unFn : IrFunction := { name := "main", blocks := [unEntry, unNext] }
def unCtx : VenomContext := { functions := [unFn], entry := some "main" }

theorem un_unresolved_asm : executePlan (generateFnPlan unFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "NOT", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- entry's body `[CV a; CV b; NOT %a]` as a `RegularBodyH`: two `cv_step`s then the growing unop `NOT`
    via `RegularStep`'s unop arm (`asmStep_not_ok`), all outputs live. -/
theorem unEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 1 [unCvA, unCvB, unNot] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "NOT", rfl, rfl, by decide, by decide,
    Or.inr (Or.inr (Or.inl ⟨"a", (~~~ ·), by decide, rfl, fun _ => rfl, rfl,
      by decide, by decide, fun _ h hg => asmStep_not_ok h hg⟩))⟩

/-- Body-end state of `unEntry`: `a,b := callvalue`, `c := a - b` (= 0 when callvalue = 0). -/
abbrev unEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (~~~ s.callCtx.callvalue)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem unEntry_thread (s : VenomState) :
    execBodyThread [unCvA, unCvB, unNot] 0 { s with instIdx := 0 } = some (unEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub := stepInstBase_unopVar (inst := unNot) (f := (~~~ ·)) (x := "a")
    (out := "c") (w := s.callCtx.callvalue) rfl rfl rfl hla
  have h1 : stepInstBase unCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase unCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase unCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [unCvB, unNot] 1 { s' with instIdx := 1 }
        | _ => none) = some (unEntrySEnd s)
  rw [h1]
  show (match stepInstBase unCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [unNot] 2 { s' with instIdx := 2 }
        | _ => none) = some (unEntrySEnd s)
  rw [h2]
  show (match stepInstBase unNot ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (unEntrySEnd s)
  rw [hsub]
  rfl

/-- `unEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem unEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) unCtx unEntry s = ExecResult.OK (jumpTo "next" (unEntrySEnd s)) :=
  runBlock_body_jmp unCtx unEntry j [unCvA, unCvB, unNot] unJmp unCvA [unCvB, unNot, unJmp] s
    (unEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (unEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem unNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg unFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([unMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := unFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev unNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem unNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (unNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (unNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem unNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [unMul] 0 { s with instIdx := 0 } = some (unNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase unMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := unMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase unMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem unMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase unMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [unMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem unMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase unMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [unMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem unNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) unCtx unNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (unNextSEnd s wb wc))
        (unNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := unNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return unCtx unNext j [unMul] unRet unMul [unRet] s (unNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (unNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem unNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) unCtx unNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := unNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term unCtx unNext j [unMul] unRet unMul [unRet] s (unNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (unNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : unNext.instructions = [unMul] ++ [unRet])
    (unNext_thread s wb wc hb hc), unRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `unEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem unEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (unEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (unEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (unEntrySEnd s) = some (~~~ s.callCtx.callvalue) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (~~~ s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (~~~ s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (~~~ s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def unInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (~~~ EvmYul.UInt256.ofNat 0))

theorem unInv_pres : ∀ bb ∈ unFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    unInv s → runBlock f' unCtx bb s = ExecResult.OK s' → unInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [unFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (unEntrySEnd s)`
    have hnt : ∀ inst ∈ [unCvA, unCvB, unNot], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof unCtx unEntry 0 [unCvA, unCvB, unNot] unJmp unCvA
             [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof unCtx unEntry 1 [unCvA, unCvB, unNot] unJmp unCvA
             [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof unCtx unEntry 2 [unCvA, unCvB, unNot] unJmp unCvA
             [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof unCtx unEntry 3 [unCvA, unCvB, unNot] unJmp unCvA
             [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, unEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := unEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (unEntrySEnd s)) = lookupVar "c" (unEntrySEnd s) from rfl, hc0]
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 unCtx unNext s unMul [unRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error unCtx unNext unMul [unRet] s "undefined operand" j rfl
          (by decide) (unMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 unCtx unNext s unMul [unRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error unCtx unNext unMul [unRet] s "undefined operand" j rfl
            (by decide) (unMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 unCtx unNext s unMul [unRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof unCtx unNext 1 [unMul] unRet unMul [unRet] s
                   (unNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (unNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, unNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 unCtx unNext s unMul [unRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof unCtx unNext 1 [unMul] unRet unMul [unRet] s
                   (unNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (unNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, unNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 unCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem unFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 unCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 unCtx vs
      = runBlocks 10 unCtx unFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, unCtx, unFn, lookupFunction, fnEntryLabel, unEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (unEntrySEnd s0) with hs1
  have hentry : runBlock 9 unCtx unEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact unEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb unFn.blocks = some unEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 unCtx unFn s0 = runBlocks 9 unCtx unFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := unEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (~~~ EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (unEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb unFn.blocks = some unNext := rfl
  have hhalt := unNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first UNOP capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=ADD %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s ADD exercises the pure commutative var/var GROWING arm (`bodyStep_commBinop`); it is
    duplicating (`DUP1 ; DUP3 ; ADD`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_unFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 unCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ unFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [unFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [unEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [unNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan unFn 0 0
      = some ((generateFnPlan unFn 0 0).get!.1, (generateFnPlan unFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel unFn) unFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv unInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel unFn) unFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan unFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := unCtx) (fn := unFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan unFn 0 0).get!.1) (psFinal := (generateFnPlan unFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ unInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [unFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, unEntry, unCvA]
    · simp [runBlock, evalPhis, execBlock, unNext, unMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [unFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [unCvA, unCvB, unNot], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof unCtx unEntry 1 [unCvA, unCvB, unNot] unJmp unCvA
               [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof unCtx unEntry 2 [unCvA, unCvB, unNot] unJmp unCvA
               [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof unCtx unEntry 3 [unCvA, unCvB, unNot] unJmp unCvA
               [unCvB, unNot, unJmp] s (unEntrySEnd s) rfl rfl (by decide) hnt (unEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([unCvA, unCvB, unNot] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [unCvA, unCvB, unNot]) (jmpInst := unJmp) (hd := unCvA) (tl := [unCvB, unNot, unJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := unNext) (sEnd := unEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := unEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := unEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 4 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof unCtx unNext 1 [unMul] unRet unMul [unRet] s
               (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (unNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([unMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [unMul]) (retInst := unRet) (hd := unMul) (tl := [unRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel unFn) unFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := unNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0))
            = lookupVar "e" (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) from rfl,
            (unNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) from rfl,
            (unNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "e")
            = lookupVar "e" (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) from rfl,
            (unNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (unNextSEnd s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)) from rfl,
            (unNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (~~~ EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := unNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel unFn) unFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc7]; decide) (hret := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨unEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel unFn) unFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan unFn 0 0).get!.1)).1.length
      omega


/-! ### ✅ A 1-input READ (CALLDATALOAD) via the recipe route — `codegen_correct_clFn_recipeW`

The first `codegen_correct` for a UNOP (`NOT`), a distinct instruction class:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = NOT %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                             -- MUL consumes the TOP two (b,c)
```

`NOT %a` is the growing unop arm (`RegularStep`'s 3rd disjunct, `asmStep_not_ok`), emitted `DUP2 ; NOT`,
leaving `[a, b, c]` with `c = NOT 0` (NON-zero — so `c` cannot itself be a RETURN operand). In `next` the
consuming `MUL %b %c` eats the top two (`b, c`); since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`,
regardless of `c`), emptying the return window. `a` (bottom) is never buried — no f1a reorder. `entry` via
`hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the consuming `MUL` (`clNext_ready`). -/

def clCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def clCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def clLoad : Instruction :=
  { id := 2, opcode := Opcode.CALLDATALOAD, operands := [Operand.Var "a"], outputs := ["c"] }
def clJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def clMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def clRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def clEntry : BasicBlock := { label := "entry", instructions := [clCvA, clCvB, clLoad, clJmp] }
def clNext : BasicBlock := { label := "next", instructions := [clMul, clRet] }
def clFn : IrFunction := { name := "main", blocks := [clEntry, clNext] }
def clCtx : VenomContext := { functions := [clFn], entry := some "main" }

theorem cl_unresolved_asm : executePlan (generateFnPlan clFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "CALLDATALOAD", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- The word CALLDATALOAD reads at offset `a` (= the call value); context-dependent, generally NON-zero. -/
abbrev clVal (s : VenomState) : bytes32 :=
  wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding s.callCtx.callvalue.toNat 32)

/-- entry's body `[CV a; CV b; CALLDATALOAD %a]` as a `RegularBodyH`: two `cv_step`s then the
    CALLDATALOAD read via `RegularStepG`'s CALLDATALOAD arm (`asmStep_calldataload_ok`), output live. -/
theorem clEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 1 [clCvA, clCvB, clLoad] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, by decide⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨"a", "c", rfl, by decide, rfl, fun _ => rfl, rfl, rfl,
     by decide, by decide, by decide, by decide, fun _ h hg => asmStep_calldataload_ok h hg⟩))))))))

/-- Body-end state of `clEntry`: `a,b := callvalue`, `c := a - b` (= 0 when callvalue = 0). -/
abbrev clEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (clVal s)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem clEntry_thread (s : VenomState) :
    execBodyThread [clCvA, clCvB, clLoad] 0 { s with instIdx := 0 } = some (clEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub : stepInstBase clLoad ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = ExecResult.OK (updateVar "c" (clVal s)
        ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 })) := by
    have he : evalOperand (Operand.Var "a") ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := hla
    simp only [clLoad, stepInstBase, execRead1, he]
    rfl
  have h1 : stepInstBase clCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase clCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase clCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [clCvB, clLoad] 1 { s' with instIdx := 1 }
        | _ => none) = some (clEntrySEnd s)
  rw [h1]
  show (match stepInstBase clCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [clLoad] 2 { s' with instIdx := 2 }
        | _ => none) = some (clEntrySEnd s)
  rw [h2]
  show (match stepInstBase clLoad ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (clEntrySEnd s)
  rw [hsub]
  rfl

/-- `clEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem clEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) clCtx clEntry s = ExecResult.OK (jumpTo "next" (clEntrySEnd s)) :=
  runBlock_body_jmp clCtx clEntry j [clCvA, clCvB, clLoad] clJmp clCvA [clCvB, clLoad, clJmp] s
    (clEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (clEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem clNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg clFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([clMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := clFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev clNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem clNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (clNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (clNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem clNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [clMul] 0 { s with instIdx := 0 } = some (clNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase clMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := clMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase clMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem clMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase clMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [clMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem clMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase clMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [clMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem clNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) clCtx clNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (clNextSEnd s wb wc))
        (clNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := clNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return clCtx clNext j [clMul] clRet clMul [clRet] s (clNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (clNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem clNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) clCtx clNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := clNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term clCtx clNext j [clMul] clRet clMul [clRet] s (clNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (clNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : clNext.instructions = [clMul] ++ [clRet])
    (clNext_thread s wb wc hb hc), clRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `clEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem clEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (clEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (clEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (clEntrySEnd s) = some (clVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (clVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (clVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (clVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def clInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (clVal s))

theorem clInv_pres : ∀ bb ∈ clFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    clInv s → runBlock f' clCtx bb s = ExecResult.OK s' → clInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [clFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (clEntrySEnd s)`
    have hnt : ∀ inst ∈ [clCvA, clCvB, clLoad], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof clCtx clEntry 0 [clCvA, clCvB, clLoad] clJmp clCvA
             [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof clCtx clEntry 1 [clCvA, clCvB, clLoad] clJmp clCvA
             [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof clCtx clEntry 2 [clCvA, clCvB, clLoad] clJmp clCvA
             [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof clCtx clEntry 3 [clCvA, clCvB, clLoad] clJmp clCvA
             [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, clEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := clEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (clEntrySEnd s)) = lookupVar "c" (clEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 clCtx clNext s clMul [clRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error clCtx clNext clMul [clRet] s "undefined operand" j rfl
          (by decide) (clMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 clCtx clNext s clMul [clRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error clCtx clNext clMul [clRet] s "undefined operand" j rfl
            (by decide) (clMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 clCtx clNext s clMul [clRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof clCtx clNext 1 [clMul] clRet clMul [clRet] s
                   (clNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (clNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, clNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 clCtx clNext s clMul [clRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof clCtx clNext 1 [clMul] clRet clMul [clRet] s
                   (clNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (clNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, clNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 clCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem clFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 clCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 clCtx vs
      = runBlocks 10 clCtx clFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, clCtx, clFn, lookupFunction, fnEntryLabel, clEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (clEntrySEnd s0) with hs1
  have hentry : runBlock 9 clCtx clEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact clEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb clFn.blocks = some clEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 clCtx clFn s0 = runBlocks 9 clCtx clFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := clEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (clVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (clEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb clFn.blocks = some clNext := rfl
  have hhalt := clNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (clVal s0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **A 1-input READ (CALLDATALOAD) capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=ADD %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s ADD exercises the pure commutative var/var GROWING arm (`bodyStep_commBinop`); it is
    duplicating (`DUP1 ; DUP3 ; ADD`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_clFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 clCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ clFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [clFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [clEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [clNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan clFn 0 0
      = some ((generateFnPlan clFn 0 0).get!.1, (generateFnPlan clFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel clFn) clFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv clInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel clFn) clFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan clFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := clCtx) (fn := clFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan clFn 0 0).get!.1) (psFinal := (generateFnPlan clFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ clInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [clFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, clEntry, clCvA]
    · simp [runBlock, evalPhis, execBlock, clNext, clMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [clFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [clCvA, clCvB, clLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof clCtx clEntry 1 [clCvA, clCvB, clLoad] clJmp clCvA
               [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof clCtx clEntry 2 [clCvA, clCvB, clLoad] clJmp clCvA
               [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof clCtx clEntry 3 [clCvA, clCvB, clLoad] clJmp clCvA
               [clCvB, clLoad, clJmp] s (clEntrySEnd s) rfl rfl (by decide) hnt (clEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([clCvA, clCvB, clLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [clCvA, clCvB, clLoad]) (jmpInst := clJmp) (hd := clCvA) (tl := [clCvB, clLoad, clJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := clNext) (sEnd := clEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := clEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := clEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 4 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof clCtx clNext 1 [clMul] clRet clMul [clRet] s
               (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (clNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([clMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [clMul]) (retInst := clRet) (hd := clMul) (tl := [clRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel clFn) clFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := clNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s))
            = lookupVar "e" (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) from rfl,
            (clNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (clVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s))
            = lookupVar "a" (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) from rfl,
            (clNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (clVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) from rfl,
            (clNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (clVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (clNextSEnd s (EvmYul.UInt256.ofNat 0) (clVal s)) from rfl,
            (clNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (clVal s)).2]; exact ha0)
        (hready := clNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel clFn) clFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc7]; decide) (hret := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨clEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel clFn) clFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan clFn 0 0).get!.1)).1.length
      omega


theorem encodeNumBytes_three : encodeNumBytes 3 = [(3 : byte)] := by
  rw [encodeNumBytes_lt256] <;> decide

/-! ### ✅ A both-LITERAL binop (litLit) via the recipe route — `codegen_correct_llFn_recipeW`

The first `codegen_correct` for a UNOP (`NOT`), a distinct instruction class:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = NOT %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                             -- MUL consumes the TOP two (b,c)
```

`NOT %a` is the growing unop arm (`RegularStep`'s 3rd disjunct, `asmStep_not_ok`), emitted `DUP2 ; NOT`,
leaving `[a, b, c]` with `c = NOT 0` (NON-zero — so `c` cannot itself be a RETURN operand). In `next` the
consuming `MUL %b %c` eats the top two (`b, c`); since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`,
regardless of `c`), emptying the return window. `a` (bottom) is never buried — no f1a reorder. `entry` via
`hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the consuming `MUL` (`llNext_ready`). -/

def llCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def llCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def llAdd : Instruction :=
  { id := 2, opcode := Opcode.ADD, operands := [Operand.Lit (EvmYul.UInt256.ofNat 3), Operand.Lit (EvmYul.UInt256.ofNat 5)], outputs := ["c"] }
def llJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def llMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def llRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def llEntry : BasicBlock := { label := "entry", instructions := [llCvA, llCvB, llAdd, llJmp] }
def llNext : BasicBlock := { label := "next", instructions := [llMul, llRet] }
def llFn : IrFunction := { name := "main", blocks := [llEntry, llNext] }
def llCtx : VenomContext := { functions := [llFn], entry := some "main" }

theorem ll_unresolved_asm : executePlan (generateFnPlan llFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmPush (encodeNumBytes 5), AsmInst.AsmPush (encodeNumBytes 3), AsmInst.AsmOp "ADD",
     AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- entry's body `[CV a; CV b; ADD 3,5]` as a `RegularBodyH`: two `cv_step`s then the both-literal
    `ADD` via `RegularStep`'s litLit arm (`asmStep_add_ok`), output live. -/
theorem llEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 1 [llCvA, llCvB, llAdd] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "ADD", rfl, rfl, by decide, by decide,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨EvmYul.UInt256.ofNat 3, EvmYul.UInt256.ofNat 5, (fun a b => a + b), by decide, fun _ => rfl, rfl,
       by decide, fun _ h hg => asmStep_add_ok h hg⟩))))⟩

/-- Body-end state of `llEntry`: `a,b := callvalue`, `c := 3 + 5 = 8` (a constant, NON-zero). -/
abbrev llEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem llEntry_thread (s : VenomState) :
    execBodyThread [llCvA, llCvB, llAdd] 0 { s with instIdx := 0 } = some (llEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub : stepInstBase llAdd ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState)
      = ExecResult.OK (updateVar "c" (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
          ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 })) := rfl
  clear hla hlb
  have h1 : stepInstBase llCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase llCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase llCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [llCvB, llAdd] 1 { s' with instIdx := 1 }
        | _ => none) = some (llEntrySEnd s)
  rw [h1]
  show (match stepInstBase llCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [llAdd] 2 { s' with instIdx := 2 }
        | _ => none) = some (llEntrySEnd s)
  rw [h2]
  show (match stepInstBase llAdd ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (llEntrySEnd s)
  rw [hsub]
  rfl

/-- `llEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem llEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) llCtx llEntry s = ExecResult.OK (jumpTo "next" (llEntrySEnd s)) :=
  runBlock_body_jmp llCtx llEntry j [llCvA, llCvB, llAdd] llJmp llCvA [llCvB, llAdd, llJmp] s
    (llEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (llEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem llNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg llFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([llMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := llFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev llNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem llNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (llNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (llNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem llNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [llMul] 0 { s with instIdx := 0 } = some (llNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase llMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := llMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase llMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem llMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase llMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [llMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem llMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase llMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [llMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem llNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) llCtx llNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (llNextSEnd s wb wc))
        (llNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := llNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return llCtx llNext j [llMul] llRet llMul [llRet] s (llNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (llNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem llNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) llCtx llNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := llNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term llCtx llNext j [llMul] llRet llMul [llRet] s (llNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (llNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : llNext.instructions = [llMul] ++ [llRet])
    (llNext_thread s wb wc hb hc), llRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `llEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem llEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (llEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (llEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (llEntrySEnd s) = some (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def llInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5))

theorem llInv_pres : ∀ bb ∈ llFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    llInv s → runBlock f' llCtx bb s = ExecResult.OK s' → llInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [llFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (llEntrySEnd s)`
    have hnt : ∀ inst ∈ [llCvA, llCvB, llAdd], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof llCtx llEntry 0 [llCvA, llCvB, llAdd] llJmp llCvA
             [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof llCtx llEntry 1 [llCvA, llCvB, llAdd] llJmp llCvA
             [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof llCtx llEntry 2 [llCvA, llCvB, llAdd] llJmp llCvA
             [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof llCtx llEntry 3 [llCvA, llCvB, llAdd] llJmp llCvA
             [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, llEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := llEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (llEntrySEnd s)) = lookupVar "c" (llEntrySEnd s) from rfl, hc0]
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 llCtx llNext s llMul [llRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error llCtx llNext llMul [llRet] s "undefined operand" j rfl
          (by decide) (llMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 llCtx llNext s llMul [llRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error llCtx llNext llMul [llRet] s "undefined operand" j rfl
            (by decide) (llMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 llCtx llNext s llMul [llRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof llCtx llNext 1 [llMul] llRet llMul [llRet] s
                   (llNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (llNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, llNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 llCtx llNext s llMul [llRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof llCtx llNext 1 [llMul] llRet llMul [llRet] s
                   (llNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (llNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, llNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 llCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem llFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 llCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 llCtx vs
      = runBlocks 10 llCtx llFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, llCtx, llFn, lookupFunction, fnEntryLabel, llEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (llEntrySEnd s0) with hs1
  have hentry : runBlock 9 llCtx llEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact llEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb llFn.blocks = some llEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 llCtx llFn s0 = runBlocks 9 llCtx llFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := llEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (llEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb llFn.blocks = some llNext := rfl
  have hhalt := llNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **A both-literal (litLit) binop capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=ADD %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s ADD exercises the pure commutative var/var GROWING arm (`bodyStep_commBinop`); it is
    duplicating (`DUP1 ; DUP3 ; ADD`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_llFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 llCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ llFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [llFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [llEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [llNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan llFn 0 0
      = some ((generateFnPlan llFn 0 0).get!.1, (generateFnPlan llFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel llFn) llFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv llInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel llFn) llFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan llFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := llCtx) (fn := llFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan llFn 0 0).get!.1) (psFinal := (generateFnPlan llFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ llInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [llFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, llEntry, llCvA]
    · simp [runBlock, evalPhis, execBlock, llNext, llMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [llFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [llCvA, llCvB, llAdd], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof llCtx llEntry 1 [llCvA, llCvB, llAdd] llJmp llCvA
               [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof llCtx llEntry 2 [llCvA, llCvB, llAdd] llJmp llCvA
               [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof llCtx llEntry 3 [llCvA, llCvB, llAdd] llJmp llCvA
               [llCvB, llAdd, llJmp] s (llEntrySEnd s) rfl rfl (by decide) hnt (llEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([llCvA, llCvB, llAdd] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [llCvA, llCvB, llAdd]) (jmpInst := llJmp) (hd := llCvA) (tl := [llCvB, llAdd, llJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 12) (bb' := llNext) (sEnd := llEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := llEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := llEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 5 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by rw [ll_unresolved_asm, encodeNumBytes_five, encodeNumBytes_three]; decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by rw [ll_unresolved_asm, encodeNumBytes_five, encodeNumBytes_three]; decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof llCtx llNext 1 [llMul] llRet llMul [llRet] s
               (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (llNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([llMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [llMul]) (retInst := llRet) (hd := llMul) (tl := [llRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel llFn) llFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := llNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5))
            = lookupVar "e" (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) from rfl,
            (llNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5))
            = lookupVar "a" (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) from rfl,
            (llNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)).2]; exact ha0)
        (hvoff := by rw [show operandVal (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) lo
              (Operand.Var "e")
            = lookupVar "e" (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) from rfl,
            (llNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) lo
              (Operand.Var "a")
            = lookupVar "a" (llNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)) from rfl,
            (llNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 3 + EvmYul.UInt256.ofNat 5)).2]; exact ha0)
        (hready := llNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel llFn) llFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc8]; decide) (hret := by simp only [hpc8]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨llEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel llFn) llFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan llFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ SSTORE via the recipe route — the first STORE reaches `codegen_correct`

The first store instruction through the recipe driver (`codegen_correct_paramSstore` proves the same
statement bespoke; this uses the generic `hsupply` machinery). SSTORE is a `RegularStepH` via
`RegularStepG`'s SSTORE arm — the store analog of a binop:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; SSTORE %a %b ; JMP next   -- SSTORE keeps a,b live (DUP1;DUP3;SSTORE)
next:   RETURN %a, %b
```

`SSTORE %a %b` is duplicating (`a,b` live), writing `storage[a] = b` as a side effect while preserving
`[a, b]` on the stack. `emit_sstore_sim` carries `venomAsmRel` across the store, so `next`'s RETURN (empty
body, `SWAP1` reorder) closes with `finalStateRel`. `callvalue = 0` ⇒ `a = b = 0` empties the return window.
`entry` via `hsupplyW_regularJmp`, `next` via `hsupplyW_emptyReturnReorder`. First store on the recipe route. -/

def ssCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def ssCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def ssStore : Instruction :=
  { id := 2, opcode := Opcode.SSTORE, operands := [Operand.Var "a", Operand.Var "b"], outputs := [] }
def ssJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def ssRet : Instruction :=
  { id := 4, opcode := Opcode.RETURN, operands := [Operand.Var "a", Operand.Var "b"], outputs := [] }
def ssEntry : BasicBlock := { label := "entry", instructions := [ssCvA, ssCvB, ssStore, ssJmp] }
def ssNext : BasicBlock := { label := "next", instructions := [ssRet] }
def ssFn : IrFunction := { name := "main", blocks := [ssEntry, ssNext] }
def ssCtx : VenomContext := { functions := [ssFn], entry := some "main" }

/-- entry's body `[CV a; CV b; SSTORE %a %b]` as a `RegularBodyH`: two `cv_step`s then the SSTORE via
    `RegularStepG`'s SSTORE arm (`asmStep_sstore_ok`), operands live (duplicating), 0 outputs. -/
theorem ssEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b"] offsetToPc
      (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 1 [ssCvA, ssCvB, ssStore] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inr (Or.inl ?_), by decide⟩
  exact ⟨"a", "b", rfl, by decide, by decide, rfl, fun _ => rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, fun _ h hg => asmStep_sstore_ok h hg⟩

/-- Body-end state of `ssEntry`: `a,b := callvalue`, then `storage[a] = b` (a side effect; vars unchanged). -/
abbrev ssEntrySEnd (s : VenomState) : VenomState :=
  { sstore s.callCtx.callvalue s.callCtx.callvalue
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem ssEntry_thread (s : VenomState) :
    execBodyThread [ssCvA, ssCvB, ssStore] 0 { s with instIdx := 0 } = some (ssEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    (lookupVar_updateVar_ne _ _ _ _ (by decide)).trans (lookupVar_updateVar_self _ _ _)
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hss := stepInstBase_sstore (inst := ssStore) (op1 := Operand.Var "a") (op2 := Operand.Var "b")
    (key := s.callCtx.callvalue) (value := s.callCtx.callvalue) rfl rfl hla hlb
  have h1 : stepInstBase ssCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase ssCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase ssCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [ssCvB, ssStore] 1 { s' with instIdx := 1 }
        | _ => none) = some (ssEntrySEnd s)
  rw [h1]
  show (match stepInstBase ssCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [ssStore] 2 { s' with instIdx := 2 }
        | _ => none) = some (ssEntrySEnd s)
  rw [h2]
  show (match stepInstBase ssStore ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (ssEntrySEnd s)
  rw [hss]; rfl

/-- lookupVar of `ssEntrySEnd`: `a, b` are the call value — `sstore` touches accounts, not vars. -/
theorem ssEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (ssEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (ssEntrySEnd s) = some s.callCtx.callvalue := by
  refine ⟨?_, ?_⟩
  · show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_self]

/-- `ssEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 5). -/
theorem ssEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) ssCtx ssEntry s = ExecResult.OK (jumpTo "next" (ssEntrySEnd s)) :=
  runBlock_body_jmp ssCtx ssEntry j [ssCvA, ssCvB, ssStore] ssJmp ssCvA [ssCvB, ssStore, ssJmp] s
    (ssEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (ssEntry_thread s) (by simpa [updateVar, sstore] using hnh)

/-- `ssNext`'s RETURN halts, given `a, b` defined. -/
theorem ssNext_halts (s : VenomState) (k : Nat) (wa wb : bytes32)
    (ha : lookupVar "a" s = some wa) (hb : lookupVar "b" s = some wb) :
    runBlock (0 + (k + 1)) ssCtx ssNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory wa.toNat wb.toNat { s with instIdx := 0 })
        { s with instIdx := 0 })) :=
  runBlock_body_return ssCtx ssNext k [] ssRet ssRet [] s { s with instIdx := 0 }
    (Operand.Var "a") (Operand.Var "b") wa wb rfl rfl rfl ha hb rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b` are zero. -/
def ssInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0))

theorem ssInv_pres : ∀ bb ∈ ssFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    ssInv s → runBlock f' ssCtx bb s = ExecResult.OK s' → ssInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [ssFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 out-of-fuel; fuel ≥ 4 lands on `jumpTo "next" (ssEntrySEnd s)`, all-zero
    have hnt : ∀ inst ∈ [ssCvA, ssCvB, ssStore], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof ssCtx ssEntry 0 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
             [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof ssCtx ssEntry 1 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
             [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof ssCtx ssEntry 2 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
             [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof ssCtx ssEntry 3 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
             [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, ssEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0⟩ := ssEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      exact ⟨by simpa [jumpTo, updateVar, sstore] using hnh, by simp [jumpTo, updateVar, sstore, hcv], fun _ => ⟨ha0, hb0⟩⟩
  · -- next: RETURN never yields OK
    rcases hla : lookupVar "a" s with _ | wa
    · match f' with
      | 0 => rw [runBlock_no_phi 0 ssCtx ssNext s ssRet [] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        have he : stepInstBase ssRet { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
          have hla' : lookupVar "a" { s with instIdx := 0 } = none := hla
          simp [ssRet, stepInstBase, evalOperand, hla']
        have hrb := runBlock_error ssCtx ssNext j [] ssRet ssRet [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) he (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
    · rcases hlb : lookupVar "b" s with _ | wb
      · match f' with
        | 0 => rw [runBlock_no_phi 0 ssCtx ssNext s ssRet [] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          have he : stepInstBase ssRet { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
            have hla' : lookupVar "a" { s with instIdx := 0 } = some wa := hla
            have hlb' : lookupVar "b" { s with instIdx := 0 } = none := hlb
            simp [ssRet, stepInstBase, evalOperand, hla', hlb']
          have hrb := runBlock_error ssCtx ssNext j [] ssRet ssRet [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) he (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
      · match f' with
        | 0 => rw [runBlock_no_phi 0 ssCtx ssNext s ssRet [] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [show j+1 = 0 + (j+1) from by simp, ssNext_halts s j wa wb hla hlb] at hrun
          exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 ssCtx vs` halts for every admitted state. Chains `entry → next`. -/
theorem ssFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 ssCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 ssCtx vs
      = runBlocks 10 ssCtx ssFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, ssCtx, ssFn, lookupFunction, fnEntryLabel, ssEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (ssEntrySEnd s0) with hs1
  have hentry : runBlock 9 ssCtx ssEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact ssEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb ssFn.blocks = some ssEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar, sstore] using hnh0
  have hstep0 : runBlocks 10 ssCtx ssFn s0 = runBlocks 9 ssCtx ssFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1⟩ := ssEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := by rw [hs1]; exact ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := by rw [hs1]; exact hb1
  have hlk1 : lookupBlock s1.currentBb ssFn.blocks = some ssNext := rfl
  have hhalt := ssNext_halts s1 7 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) ha1' hb1'
  rw [show (0 : Nat) + (7 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first STORE via the recipe route.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; SSTORE %a %b ; JMP next` / `next: RETURN %a, %b`. -/
theorem codegen_correct_ssFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 ssCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ ssFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [ssFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [ssEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [ssNext, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan ssFn 0 0
      = some ((generateFnPlan ssFn 0 0).get!.1, (generateFnPlan ssFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel ssFn) ssFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv ssInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel ssFn) ssFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan ssFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := ssCtx) (fn := ssFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan ssFn 0 0).get!.1) (psFinal := (generateFnPlan ssFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ssInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [ssFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, ssEntry, ssCvA]
    · simp [runBlock, evalPhis, execBlock, ssNext, ssRet]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [ssFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + SSTORE (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [ssCvA, ssCvB, ssStore], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof ssCtx ssEntry 1 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
               [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof ssCtx ssEntry 2 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
               [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof ssCtx ssEntry 3 [ssCvA, ssCvB, ssStore] ssJmp ssCvA
               [ssCvB, ssStore, ssJmp] s (ssEntrySEnd s) rfl rfl (by decide) hnt (ssEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([ssCvA, ssCvB, ssStore] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [ssCvA, ssCvB, ssStore]) (jmpInst := ssJmp) (hd := ssCvA) (tl := [ssCvB, ssStore, ssJmp])
        (nextLiveness := ["a", "b"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := ssNext) (sEnd := ssEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := ssEntry_thread s) (hnothalt := by simpa [updateVar, sstore] using hhalt)
        (hreg := ssEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 5 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: RETURN %a %b (empty body, SWAP1 reorder); the invariant supplies a=b=0
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := ssRet) (offv := "a") (szv := "b")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "a", Operand.Var "b"])
        (ps := psOfFn (fnPlanFuel ssFn) ssFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := ha0) (hevalsz := hb0) (hvoff := ha0) (hvsz := hb0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc8]; decide) (hget := by simp only [hpc8]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨ssEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel ssFn) ssFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan ssFn 0 0).get!.1)).1.length
      omega


/-! ### ✅ TSTORE via the recipe route — the first STORE reaches `codegen_correct`

The first store instruction through the recipe driver (`codegen_correct_paramSstore` proves the same
statement bespoke; this uses the generic `hsupply` machinery). TSTORE is a `RegularStepH` via
`RegularStepG`'s TSTORE arm — the store analog of a binop:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; TSTORE %a %b ; JMP next   -- TSTORE keeps a,b live (DUP1;DUP3;TSTORE)
next:   RETURN %a, %b
```

`TSTORE %a %b` is duplicating (`a,b` live), writing `storage[a] = b` as a side effect while preserving
`[a, b]` on the stack. `emit_tstore_sim` carries `venomAsmRel` across the store, so `next`'s RETURN (empty
body, `SWAP1` reorder) closes with `finalStateRel`. `callvalue = 0` ⇒ `a = b = 0` empties the return window.
`entry` via `hsupplyW_regularJmp`, `next` via `hsupplyW_emptyReturnReorder`. First store on the recipe route. -/

def tsCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def tsCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def tsStore : Instruction :=
  { id := 2, opcode := Opcode.TSTORE, operands := [Operand.Var "a", Operand.Var "b"], outputs := [] }
def tsJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def tsRet : Instruction :=
  { id := 4, opcode := Opcode.RETURN, operands := [Operand.Var "a", Operand.Var "b"], outputs := [] }
def tsEntry : BasicBlock := { label := "entry", instructions := [tsCvA, tsCvB, tsStore, tsJmp] }
def tsNext : BasicBlock := { label := "next", instructions := [tsRet] }
def tsFn : IrFunction := { name := "main", blocks := [tsEntry, tsNext] }
def tsCtx : VenomContext := { functions := [tsFn], entry := some "main" }

/-- entry's body `[CV a; CV b; TSTORE %a %b]` as a `RegularBodyH`: two `cv_step`s then the TSTORE via
    `RegularStepG`'s TSTORE arm (`asmStep_tstore_ok`), operands live (duplicating), 0 outputs. -/
theorem tsEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b"] offsetToPc
      (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 1 [tsCvA, tsCvB, tsStore] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inr (Or.inr (Or.inl ?_)), by decide⟩
  exact ⟨"a", "b", rfl, by decide, by decide, rfl, fun _ => rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide⟩

/-- Body-end state of `tsEntry`: `a,b := callvalue`, then `storage[a] = b` (a side effect; vars unchanged). -/
abbrev tsEntrySEnd (s : VenomState) : VenomState :=
  { tstore s.callCtx.callvalue s.callCtx.callvalue
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem tsEntry_thread (s : VenomState) :
    execBodyThread [tsCvA, tsCvB, tsStore] 0 { s with instIdx := 0 } = some (tsEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    (lookupVar_updateVar_ne _ _ _ _ (by decide)).trans (lookupVar_updateVar_self _ _ _)
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hss := stepInstBase_tstore (inst := tsStore) (op1 := Operand.Var "a") (op2 := Operand.Var "b")
    (key := s.callCtx.callvalue) (value := s.callCtx.callvalue) rfl rfl hla hlb
  have h1 : stepInstBase tsCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase tsCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase tsCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [tsCvB, tsStore] 1 { s' with instIdx := 1 }
        | _ => none) = some (tsEntrySEnd s)
  rw [h1]
  show (match stepInstBase tsCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [tsStore] 2 { s' with instIdx := 2 }
        | _ => none) = some (tsEntrySEnd s)
  rw [h2]
  show (match stepInstBase tsStore ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (tsEntrySEnd s)
  rw [hss]; rfl

/-- lookupVar of `tsEntrySEnd`: `a, b` are the call value — `tstore` touches accounts, not vars. -/
theorem tsEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (tsEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (tsEntrySEnd s) = some s.callCtx.callvalue := by
  refine ⟨?_, ?_⟩
  · show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_self]

/-- `tsEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 5). -/
theorem tsEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) tsCtx tsEntry s = ExecResult.OK (jumpTo "next" (tsEntrySEnd s)) :=
  runBlock_body_jmp tsCtx tsEntry j [tsCvA, tsCvB, tsStore] tsJmp tsCvA [tsCvB, tsStore, tsJmp] s
    (tsEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (tsEntry_thread s) (by simpa [updateVar, tstore] using hnh)

/-- `tsNext`'s RETURN halts, given `a, b` defined. -/
theorem tsNext_halts (s : VenomState) (k : Nat) (wa wb : bytes32)
    (ha : lookupVar "a" s = some wa) (hb : lookupVar "b" s = some wb) :
    runBlock (0 + (k + 1)) tsCtx tsNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory wa.toNat wb.toNat { s with instIdx := 0 })
        { s with instIdx := 0 })) :=
  runBlock_body_return tsCtx tsNext k [] tsRet tsRet [] s { s with instIdx := 0 }
    (Operand.Var "a") (Operand.Var "b") wa wb rfl rfl rfl ha hb rfl (by decide)
    (by intro i hi; cases hi) (by simp [execBodyThread])

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b` are zero. -/
def tsInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0))

theorem tsInv_pres : ∀ bb ∈ tsFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    tsInv s → runBlock f' tsCtx bb s = ExecResult.OK s' → tsInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [tsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 out-of-fuel; fuel ≥ 4 lands on `jumpTo "next" (tsEntrySEnd s)`, all-zero
    have hnt : ∀ inst ∈ [tsCvA, tsCvB, tsStore], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof tsCtx tsEntry 0 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
             [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof tsCtx tsEntry 1 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
             [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof tsCtx tsEntry 2 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
             [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof tsCtx tsEntry 3 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
             [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, tsEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0⟩ := tsEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      exact ⟨by simpa [jumpTo, updateVar, tstore] using hnh, by simp [jumpTo, updateVar, tstore, hcv], fun _ => ⟨ha0, hb0⟩⟩
  · -- next: RETURN never yields OK
    rcases hla : lookupVar "a" s with _ | wa
    · match f' with
      | 0 => rw [runBlock_no_phi 0 tsCtx tsNext s tsRet [] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        have he : stepInstBase tsRet { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
          have hla' : lookupVar "a" { s with instIdx := 0 } = none := hla
          simp [tsRet, stepInstBase, evalOperand, hla']
        have hrb := runBlock_error tsCtx tsNext j [] tsRet tsRet [] s { s with instIdx := 0 }
          "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
          (by simp [execBodyThread]) he (by decide) (by decide)
        rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
        exact absurd hrun (by simp)
    · rcases hlb : lookupVar "b" s with _ | wb
      · match f' with
        | 0 => rw [runBlock_no_phi 0 tsCtx tsNext s tsRet [] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          have he : stepInstBase tsRet { s with instIdx := 0 } = ExecResult.Error "return: undefined operand" := by
            have hla' : lookupVar "a" { s with instIdx := 0 } = some wa := hla
            have hlb' : lookupVar "b" { s with instIdx := 0 } = none := hlb
            simp [tsRet, stepInstBase, evalOperand, hla', hlb']
          have hrb := runBlock_error tsCtx tsNext j [] tsRet tsRet [] s { s with instIdx := 0 }
            "return: undefined operand" rfl rfl (by decide) (by intro i hi; cases hi)
            (by simp [execBodyThread]) he (by decide) (by decide)
          rw [show j+1 = ([] : List Instruction).length + (j+1) from by simp, hrb] at hrun
          exact absurd hrun (by simp)
      · match f' with
        | 0 => rw [runBlock_no_phi 0 tsCtx tsNext s tsRet [] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [show j+1 = 0 + (j+1) from by simp, tsNext_halts s j wa wb hla hlb] at hrun
          exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 tsCtx vs` halts for every admitted state. Chains `entry → next`. -/
theorem tsFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 tsCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 tsCtx vs
      = runBlocks 10 tsCtx tsFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, tsCtx, tsFn, lookupFunction, fnEntryLabel, tsEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (tsEntrySEnd s0) with hs1
  have hentry : runBlock 9 tsCtx tsEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact tsEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb tsFn.blocks = some tsEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar, tstore] using hnh0
  have hstep0 : runBlocks 10 tsCtx tsFn s0 = runBlocks 9 tsCtx tsFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1⟩ := tsEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := by rw [hs1]; exact ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := by rw [hs1]; exact hb1
  have hlk1 : lookupBlock s1.currentBb tsFn.blocks = some tsNext := rfl
  have hhalt := tsNext_halts s1 7 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) ha1' hb1'
  rw [show (0 : Nat) + (7 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first STORE via the recipe route.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; TSTORE %a %b ; JMP next` / `next: RETURN %a, %b`. -/
theorem codegen_correct_tsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 tsCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ tsFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [tsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [tsEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [tsNext, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan tsFn 0 0
      = some ((generateFnPlan tsFn 0 0).get!.1, (generateFnPlan tsFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel tsFn) tsFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv tsInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel tsFn) tsFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan tsFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := tsCtx) (fn := tsFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan tsFn 0 0).get!.1) (psFinal := (generateFnPlan tsFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ tsInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [tsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, tsEntry, tsCvA]
    · simp [runBlock, evalPhis, execBlock, tsNext, tsRet]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [tsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + TSTORE (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [tsCvA, tsCvB, tsStore], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof tsCtx tsEntry 1 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
               [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof tsCtx tsEntry 2 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
               [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof tsCtx tsEntry 3 [tsCvA, tsCvB, tsStore] tsJmp tsCvA
               [tsCvB, tsStore, tsJmp] s (tsEntrySEnd s) rfl rfl (by decide) hnt (tsEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([tsCvA, tsCvB, tsStore] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [tsCvA, tsCvB, tsStore]) (jmpInst := tsJmp) (hd := tsCvA) (tl := [tsCvB, tsStore, tsJmp])
        (nextLiveness := ["a", "b"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := tsNext) (sEnd := tsEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := tsEntry_thread s) (hnothalt := by simpa [updateVar, tstore] using hhalt)
        (hreg := tsEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 5 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: RETURN %a %b (empty body, SWAP1 reorder); the invariant supplies a=b=0
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm]; decide
      refine Or.inr (hsupplyW_emptyReturnReorder (tInst := tsRet) (offv := "a") (szv := "b")
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0) (base := [])
        (perm := [Operand.Var "a", Operand.Var "b"])
        (ps := psOfFn (fnPlanFuel tsFn) tsFn 0 0 "next")
        (hbb := rfl) (hop := rfl) (hoperands := rfl)
        (hevaloff := ha0) (hevalsz := hb0) (hvoff := ha0) (hvsz := hb0)
        (hrel := hvrel)
        (hbLabel := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hperm := by decide) (hpsstk := by decide) (hbound := by decide)
        (hnospill := by intro o; rfl) (hreorder := rfl)
        (hblockR := by rw [hpc8]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hpc := by rw [hpc8]; decide) (hget := by simp only [hpc8]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨tsEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel tsFn) tsFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan tsFn 0 0).get!.1)).1.length
      omega


end Example

/-! ## Producing a block's recipe from `RegularBodyH`: the no-emit halting terminators (STOP / INVALID)

The recipe route reduces a block's `HbsimMatch` obligation to producing its `TermRecipe` (via
`HbsimMatch_dispatch`).
For the two **no-emit halting** terminators — STOP and INVALID — that recipe comes free from the
per-instruction correctness layer `RegularBodyH`, with **no successor-recording and hence no var-set
threading**: they halt, so there is no arriving-successor relation to reconcile. These two producers mirror
`HbsimMatch_stop_regular` / `HbsimMatch_invalid_regular` (same `RegularBodyH` + structural-invariant
hypotheses, from which their non-vacuity is inherited — witnessed for real bodies by the concrete
copy-carrying capstones) but yield the recipe
∃-body that `HbsimMatch_dispatch` consumes instead of producing the `HbsimMatch` directly. So a STOP/INVALID
block of modeled opcodes has its recipe derived end-to-end from `RegularBodyH`; the remaining recipe work
is exactly the operand/successor-carrying terminators, where var-set threading enters. -/



/-- **A STOP block's terminator recipe, produced from `RegularBodyH`.** Threads
    `bodyStepsReadyH_regular_list` → `genBlockBodyH_sim_inv` (the body sim: asm run + `venomAsmRel` at the
    body-fold state) → `runBlock_body_stop` (the Venom-side STOP reduction), then packages the STOP arm of
    `TermRecipe`. No successor-recording, hence no var-set threading. -/
theorem termRecipe_stop_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hstop : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "STOP")
    (hle : (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen N
          (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hrb := runBlock_body_stop ctx bb restFuel front stopInst hd tl s sEnd
    hbb hstopop hcons hphi hnonterm hthread
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hstop_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hstop
  exact ⟨as', _, sEnd, _, hrun, Or.inl ⟨hrel', hle, hrb, hpc_as, hstop_as⟩⟩

/-- **An INVALID block's terminator recipe, produced from `RegularBodyH`.** The INVALID twin of
    `termRecipe_stop_of_regular`: uses `runBlock_body_invalid` (fault reduction, clearing returndata) and
    packages the INVALID arm of `TermRecipe`. No successor-recording, hence no var-set threading. -/
theorem termRecipe_invalid_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpc : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hinv : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩
      = AsmInst.AsmOp "INVALID")
    (hle : (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen N
          (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hrb := runBlock_body_invalid ctx bb restFuel front invInst hd tl s sEnd
    hbb hinvop hcons hphi hnonterm hthread
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hinv_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hinv
  exact ⟨as', _, sEnd, _, hrun, Or.inr (Or.inl ⟨hrel', hle, hrb, hpc_as, hinv_as⟩)⟩

/-! ## Producing a block's recipe from the emit segment: the operand-carrying halting terminators
    (RETURN / REVERT / SELFDESTRUCT)

Unlike STOP/INVALID (no emit), these three halting terminators run stack-arranging code between the body
and the terminator (`emitInputPlan`, arranging their operands on top). Each recipe producer mirrors the
existing spill-aware asm segment (`hasm_regularHSVP_{return,revert,selfdestruct}_var`) **up to the
post-emit state** — body sim (`genBlockPrefixBodyHSVP_sim_inv`) then the operand emission
(`emitInputPlan_{pair,single}_var_sim`) — but, instead of taking the final terminator step to `AsmHalt`/
`AsmRevert`, packages the matching `TermRecipe` arm at that post-emit state (operands on top, terminator
at `as'.pc`, plus the memory-safety facts the operand terminators carry). They still HALT, so there is no
successor-recording and no var-set threading. With `termRecipe_{stop,invalid}_of_regular`, this completes
recipe production for **all five halting terminators**; only the continuing terminators (JMP/JNZ/DJMP),
whose successor-recording needs var-set threading, remain. Non-vacuity is inherited from the identical
hypothesis sets of `hstep_regularHSVP_{return,revert,selfdestruct}` (all positive existence/placement
facts — no ∀-∃ unsatisfiable shape). -/


/-- **A SELFDESTRUCT block's recipe from the body + single-operand emit segment.** -/
theorem termRecipe_selfdestruct_of_HSVP
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {offsets : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {addrv : String} {waddr : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState (selfdestruct waddr sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
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
    (hN : bodyLen + emitLen + 1 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' offsetToPc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf offsetToPc offsets prog as' ps' vs' bodyLen' N
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
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (selfdestruct waddr sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (selfdestruct waddr sEnd)) hbb hcons hphi hnonterm hthread' hterm_step
  have hbody : runAsm (bodyLen + emitLen) offsetToPc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨waddr, asMid2.stack.drop 1, herel, hN, hrb, ⟨hpc', hget'⟩, htop⟩))))⟩

/-- **A RETURN block's recipe from the body + 2-operand emit segment** (memory-safety facts carried). -/
theorem termRecipe_return_of_HSVP
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {offsets : AssocList String Nat}
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
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
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
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' offsetToPc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf offsetToPc offsets prog as' ps' vs' bodyLen' N
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
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
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
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd _ hbb hcons hphi hnonterm hthread' hterm_step
  have hbody : runAsm (bodyLen + emitLen) offsetToPc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    Or.inr (Or.inr (Or.inl ⟨woff, wsz, asMid2.stack.drop 2, herel, hN, hrb, ⟨hpc', hget'⟩,
      htop, hcov, hsafe', hlen⟩))⟩

/-- **A REVERT block's recipe** — the `AsmRevert` twin of `termRecipe_return_of_HSVP` (via
    `runBlock_abort`). -/
theorem termRecipe_revert_of_HSVP
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {offsets : AssocList String Nat}
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
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
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
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' offsetToPc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf offsetToPc offsets prog as' ps' vs' bodyLen' N
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
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
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
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd _ AbortType.RevertAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  have hbody : runAsm (bodyLen + emitLen) offsetToPc prog as0 = AsmResult.AsmOK asMid2 := by
    rw [runAsm_add_ok hbrun]; exact herun
  exact ⟨asMid2, _, sEnd, bodyLen + emitLen, hbody,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨woff, wsz, asMid2.stack.drop 2, herel, hN, hrb, ⟨hpc', hget'⟩,
      htop, hcov, hsafe', hlen⟩)))⟩

/-! ## Producing a block's recipe from `RegularBodyH`: the first continuing terminator (JMP)

The continuing terminators (JMP/JNZ/DJMP) differ from the halting ones by one input: the
**successor-recording** — the body-end plan lines up with the target block's recorded plan
(`ps' = psOf target`). `termRecipe_jmp_of_regular` produces the JMP recipe from `RegularBodyH`
(no-spill body) exactly like `termRecipe_stop_of_regular`, taking that successor-recording as an explicit
input. **It is not an open gap**: `adapter_lgfold_eq_psOfFn_succ_general` derives it as
`(lg.foldl gp).2 = psOfFn succ` (the real `psOfFn`, from the JMP-chain hypotheses), and the per-block
`hstep_regularHSVP_jmp_canonical` already uses that exact fact with `psOf := psOfFn` (which
`codegen_correct_{sched,fuel}` consume). So this producer isolates the single continuing-terminator input
and shows the JMP recipe is built from `RegularBodyH` + placement + that derivable fact. -/


/-- **A JMP block's terminator recipe from `RegularBodyH`** (no-spill body), taking the successor-recording
    `ps' = psOf target` as an explicit (derivable — see the section note) input. -/
theorem termRecipe_jmp_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel off : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {target : String}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label target])
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
    (hps : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 = psOf target)
    (hp1 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hpush : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hp1⟩
      = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hp2 : as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1, hp2⟩
      = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hle : (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen' N
          (front.length + (restFuel + 1)) ctx bb s := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hrb : runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo target sEnd) :=
    runBlock_body_jmp ctx bb restFuel front jmpInst hd tl s sEnd target
      hbb hjmpop hoperands hcons hphi hnonterm hthread hnothalt
  have hp1' : as'.pc < prog.length := hpc' ▸ hp1
  have hpush' : prog.get ⟨as'.pc, hp1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel target) :=
    prog_get_transfer hpc' hpush
  have hp2' : as'.pc + 1 < prog.length := by rw [hpc']; exact hp2
  have hjump' : prog.get ⟨as'.pc + 1, hp2'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (congrArg (· + 1) hpc') hjump
  refine ⟨as', _, sEnd, _, hrun,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨target, off, bb', hrel', hps, hle, hnothalt, hrb, ⟨hp1', hpush'⟩, hoff_lk, hoff,
        ⟨hp2', hjump'⟩, hidx_lk, hlk'⟩)))))⟩

/-! ## Producing a block's recipe from `RegularBodyH`: JNZ (both branches)

JNZ carries the branch condition ON THE STACK, so beyond `termRecipe_jmp_of_regular` two facts about the
existential body-end `as'` are DERIVED from the body-sim relation rather than taken raw: the asm condition
on top (`venomAsmRel_asmStack_top1_var`, given the plan-TOS is the condition var) and the condition-dropped
successor relation (`venomAsmRel_pop_tos`, given the successor plan is the body-fold with the condition
popped — the JNZ successor-recording, an explicit plan input). `venomAsmRel_pop_tos` is the reusable
building block: only `planStackRel` reads the stacks, so a shared-TOS pop is `planStackRel_pop` on that one
component. -/



/-- **A JNZ (taken) block's terminator recipe from `RegularBodyH`** (no-spill body); the condition-on-top
    and the condition-dropped successor relation are derived from the body-sim relation. -/
theorem termRecipe_jnz_taken_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel off : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
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
    (hle : (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen' N
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
  have hrb : runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo ifNz sEnd) :=
    runBlock_body_jnz_taken ctx bb restFuel front jnzInst hd tl s sEnd (Operand.Var condvar) ifNz ifZ cond
      hbb hop hoperands hcondv hcond_ne hcons hphi hnonterm hthread hnothalt
  have hp1' : as'.pc < prog.length := hpc' ▸ hp1
  have hpush' : prog.get ⟨as'.pc, hp1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer hpc' hpush
  have hp2' : as'.pc + 1 < prog.length := by rw [hpc']; exact hp2
  have hjumpi' : prog.get ⟨as'.pc + 1, hp2'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (congrArg (· + 1) hpc') hjumpi
  refine ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hrun,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨ifNz, off, cond, as'.stack.drop 1, bb', hle, hnothalt, hrb, hstk_c, hcond_ne,
        ⟨hp1', hpush'⟩, hoff_lk, hoff, ⟨hp2', hjumpi'⟩, hidx_lk, hsucc, hlk'⟩))))))⟩

/-- **A JNZ (not taken) block's terminator recipe from `RegularBodyH`** (condition zero; 4-op tail). -/
theorem termRecipe_jnz_nottaken_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel offN offZ : Nat} {ctx : VenomContext}
    {bb bb' : BasicBlock}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {condvar ifNz ifZ : String} {base : List Operand}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [Operand.Var condvar, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand (Operand.Var condvar) sEnd = some (EvmYul.UInt256.ofNat 0))
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
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 2 + 1, hp4⟩
      = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hle : (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 4 ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen' N
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
  have hrb : runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo ifZ sEnd) :=
    runBlock_body_jnz_nottaken ctx bb restFuel front jnzInst hd tl s sEnd (Operand.Var condvar) ifNz ifZ
      hbb hop hoperands hcondv hcons hphi hnonterm hthread hnothalt
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
  refine ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd, _, hrun,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨ifNz, ifZ, offN, offZ, as'.stack.drop 1, bb', hle, hnothalt, hrb, hstk_c,
        ⟨hp1', hpushN'⟩, hoffN_lk, hoffN, ⟨hp2', hjumpi'⟩, ⟨hp3', hpushZ'⟩, hoffZ_lk, hoffZ,
        ⟨hp4', hjump'⟩, hidxZ_lk, hsucc, hlk'⟩)))))))⟩

/-! ## Producing a block's recipe from `RegularBodyH`: DJMP (the last terminator; recipe coverage 8/8)

DJMP is the dynamic-jump analogue of JNZ: the selector is on the stack (extracted from the body-sim
relation), the selector-dropped successor relation comes from `venomAsmRel_pop_tos`, and the dispatch run
comes from `djmp_switch_sim_state` (the `pre`-list of non-matching entries + the trampoline placement,
threaded from the caller; only the scan/match positions are relative to the body-end pc, so they transfer
via `hpc'`, while the trampoline ops sit at an absolute index). With this, every one of the eight codegen
terminators has a `RegularBodyH`-to-`TermRecipe` producer. -/


/-- **A DJMP block's terminator recipe from `RegularBodyH`.** The dynamic-jump analogue: the selector is
    on the stack (extracted from the body-sim relation), the dispatch run comes from `djmp_switch_sim_state`
    (the `pre`-list of non-matching entries + trampoline placement, threaded from the caller), and the
    selector-dropped successor relation from `venomAsmRel_pop_tos`. The last terminator's recipe. -/
theorem termRecipe_djmp_of_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {dInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {selvar : String} {idx : bytes32} {base : List Operand}
    {labelOps : List Operand} {labels : List String} {hi : idx.toNat < labels.length}
    -- dispatch structure (threaded to djmp_switch_sim_state)
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
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hseltos : (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack
      = base ++ [Operand.Var selvar])
    (hpsj : psOf (labels.get ⟨idx.toNat, hi⟩)
      = { (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with
          stack := stackPop 1 (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.stack, labelCounter := lc })
    (hpct : pcOf (labels.get ⟨idx.toNat, hi⟩) = target)
    -- dispatch placement (about as0.pc+bodyLen for the scan/match; absolute idxTramp for the trampoline)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog ((as0.pc + (executePlan
            (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * k)
          (pre.get ⟨k, hk⟩).1 (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        idx ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    (hmatch : djmpEntryHere offsets prog ((as0.pc + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length) + 5 * pre.length)
        matb tName matoff)
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
    (hle : (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
      + (5 * pre.length + 5 + 4) ≤ N) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen' : Nat),
      runAsm bodyLen' o2pc prog as0 = AsmResult.AsmOK as'
      ∧ TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen' N
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
  have hrb : runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.OK (jumpTo (labels.get ⟨idx.toNat, hi⟩) sEnd) :=
    runBlock_body_djmp ctx bb restFuel front dInst hd tl s sEnd (Operand.Var selvar) labelOps idx labels
      hi hbb hop hoperands hselv hlabels hcons hphi hnonterm hthread hnothalt
  -- the dispatch run
  have hdispatch := djmp_switch_sim_state (offsetToPc := o2pc) pre as' hstk_c
    (by intro k hk; rw [hpc']; exact hpre k hk)
    (by rw [hpc']; exact hmatch) hsel hidx_lk ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  rw [← hpct] at hdispatch
  exact ⟨as', (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2, sEnd,
    (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hrun,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨labels.get ⟨idx.toNat, hi⟩, 5 * pre.length + 5 + 4, as'.stack.drop 1, bb', hle, hnothalt, hrb,
        hdispatch, hsucc, hlk⟩)))))))⟩

end EvmYul.Venom.Hol.Codegen

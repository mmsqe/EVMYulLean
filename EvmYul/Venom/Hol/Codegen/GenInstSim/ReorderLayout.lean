import EvmYul.Venom.Hol.Codegen.GenInstSim.ComputeAtoms

/-!
# GenInstSim — ReorderLayout

Reorder + output handling + stack-swap algebra; the positioned-nodup-var-list / JMP terminator
plan decomposition and the SOLabel- and push-label-freeness of the plan machinery.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

variable {offsetToPc : AssocList Nat Nat}

/-! ## Reorder

`reorderPlan` arranges an instruction's operands to their target positions before the
emit; `reorderPlan_sim` reduces it (via the fold harness) to a per-`reorderOne` residual.
The common case — an operand already on the stack at its final position — is a no-op,
discharged here. (The genuine 2-swap case composes two `doSwap_sim`s; the spilled-restore
case adds `doRestore`.) -/

/-- `reorderOne` is a no-op when the operand is already on the stack at its final position
    (`finalDist = targetOps.length - 1 - idx`): no restore, no swaps. -/
theorem reorderOne_nil_of_positioned {targetOps : List Operand} {idx : Nat} {op : Operand}
    {ps : PlanState}
    (hpos : stackGetDepth op ps.stack = some (targetOps.length - 1 - idx)) :
    reorderOne () targetOps idx op ps = ([], ps) := by
  unfold reorderOne
  simp only [hpos, if_pos]

/-- `reorderOne` simulation, the already-positioned case: the step emits no ops, so it
    trivially preserves `venomAsmRel`. Discharges `reorderPlan_sim`'s `hstep` when an
    operand needs no reordering (the common case after input emission). -/
theorem reorderOne_sim_positioned {targetOps idx op ps lo vs as prog}
    (hpos : stackGetDepth op ps.stack = some (targetOps.length - 1 - idx))
    (hrel : venomAsmRel lo ps vs as) :
    ∃ as', runAsm (executePlan (reorderOne () targetOps idx op ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (reorderOne () targetOps idx op ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (reorderOne () targetOps idx op ps).1).length := by
  rw [reorderOne_nil_of_positioned hpos]
  exact ⟨as, rfl, hrel, rfl⟩

/-- Small `doSwap` (dist ≤ 16, the non-spilling case) preserves stack length. Needed to
    carry the second swap's length bound `finalDist < ps₂.stack.length` across the first. -/
theorem doSwap_small_stack_length {dist : Nat} {ps : PlanState} (h : dist ≤ 16) :
    (doSwap dist ps).2.stack.length = ps.stack.length := by
  unfold doSwap
  by_cases h0 : dist = 0
  · simp [h0]
  · rw [if_neg h0, if_pos h]
    show (stackSwap dist ps.stack).length = ps.stack.length
    rw [stackSwap]; simp only [List.length_set]

/-- `reorderOne` simulation, the genuine 2-swap case: the operand is on the stack at
    `dist`, but `dist ≠ finalDist`, so the plan emits `doSwap dist ; doSwap finalDist`.
    Both distances are small (≤ 16, no big-swap spilling); we compose the two
    `doSwap_sim`s with `runAsm_compose`. This is the real reorder content beyond the
    already-positioned no-op of `reorderOne_sim_positioned`.

    Caveat (allocator generalization): restricted to the no-spill, small-distance case
    (`op` live on the stack, `dist, finalDist ≤ 16`). The spilled-restore case (`op` only
    in `ps.spilled`, prefixed by `doRestore`) and big-swap distances are deferred. -/
theorem reorderOne_sim_swap {targetOps idx op ps lo vs as prog dist}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hne : dist ≠ targetOps.length - 1 - idx)
    (hdsmall : dist ≤ 16)
    (hfsmall : targetOps.length - 1 - idx ≤ 16)
    (hrel : venomAsmRel lo ps vs as)
    (hlen : dist < ps.stack.length)
    (hflen : targetOps.length - 1 - idx < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan (reorderOne () targetOps idx op ps).1)) :
    ∃ as', runAsm (executePlan (reorderOne () targetOps idx op ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (reorderOne () targetOps idx op ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (reorderOne () targetOps idx op ps).1).length := by
  -- decompose `reorderOne` into its two `doSwap`s (no-spill, dist ≠ finalDist branch)
  rcases hsw1 : doSwap dist ps with ⟨swapOps1, ps2⟩
  rcases hsw2 : doSwap (targetOps.length - 1 - idx) ps2 with ⟨swapOps2, ps3⟩
  have hdecomp : reorderOne () targetOps idx op ps = (swapOps1 ++ swapOps2, ps3) := by
    unfold reorderOne
    simp only [hdepth, if_neg hne, hsw1, hsw2, List.nil_append]
  rw [hdecomp]
  rw [hdecomp] at hblock
  rw [executePlan_append] at hblock
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  -- first swap
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ := doSwap_sim hsw1 hrel hlen hb1 (fun h => absurd h (by omega))
  -- second swap: `finalDist < ps₂.stack.length` since the small first swap preserves length
  have hps2len : ps2.stack.length = ps.stack.length := by
    have := doSwap_small_stack_length (dist := dist) (ps := ps) hdsmall
    rw [hsw1] at this; exact this
  have hflen2 : targetOps.length - 1 - idx < ps2.stack.length := by rw [hps2len]; exact hflen
  have hb2' : asmBlockAt prog as1.pc (executePlan swapOps2) := by rw [hpc1]; exact hb2
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doSwap_sim hsw2 hrel1 hflen2 hb2' (fun h => absurd h (by omega))
  refine ⟨as2, ?_, hrel2, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrun1 hrun2
  · rw [executePlan_append, List.length_append, hpc2, hpc1]; omega

/-! ### General reorder plan-stack effect (`perm_reaches` building blocks)

The no-op reorder (already-positioned body) is fully handled (`reorderPlan_vars_nil` &c.). The general
permutation reorder synthesises the target layout from any arrangement — a selection-sort over
`reorderOne`. These lemmas give the per-step *plan-stack* transition (the asm-side per-step sims are
`reorderOne_sim_positioned`/`reorderOne_sim_swap`); the remaining `perm_reaches` content is that this
transition positions `op` at `finalDist` and that the fold reaches `base ++ targetOps`. -/

/-- **`doSwap` plan-stack effect (small, non-zero case).** For `0 < dist ≤ 16` (the no-spill case),
    `doSwap` swaps TOS with the element at distance `dist`, leaving `stackSwap dist ps.stack`. -/
theorem doSwap_stack_small {dist : Nat} {ps : PlanState} (h0 : dist ≠ 0) (h : dist ≤ 16) :
    (doSwap dist ps).2.stack = stackSwap dist ps.stack := by
  unfold doSwap; rw [if_neg h0, if_pos h]

/-- `doSwap 0` is a plan-stack no-op. -/
theorem doSwap_stack_zero {ps : PlanState} : (doSwap 0 ps).2.stack = ps.stack := by
  unfold doSwap; rw [if_pos rfl]

/-- **`doSwap` plan-stack effect, the big-swap case (`dist > 16`).** The spill/restore bulk swap nets
    to `stackSwap dist ps.stack` — offset-independent (`bigSwap_stack_spec`), so no `freeSlots`
    precondition is needed for the *stack* (unlike `doSwap_big_eq`, which fixes the offsets). -/
theorem doSwap_stack_big {dist : Nat} {ps : PlanState} (hd : 16 < dist)
    (hlen : dist < ps.stack.length) :
    (doSwap dist ps).2.stack = stackSwap dist ps.stack := by
  unfold doSwap
  rw [if_neg (by omega), if_neg (by omega)]
  show ps.stack.take (ps.stack.length - (dist + 1)) ++
      ([dist + 1 - 1] ++ (List.range (dist + 1 - 2)).map (· + 1) ++ [0]).map
        (fun idx => (topN (dist + 1) ps.stack)[idx]!) = stackSwap dist ps.stack
  rw [show dist + 1 - 1 = dist from by omega, show dist + 1 - 2 = dist - 1 from by omega]
  exact bigSwap_stack_spec ps.stack dist (by omega) hlen

/-- **`doSwap` plan-stack effect, any non-zero distance in range.** Unifies the small-swap
    (`doSwap_stack_small`) and big-swap (`doSwap_stack_big`) cases: `(doSwap dist ps).2.stack =
    stackSwap dist ps.stack` for any `0 < dist < ps.stack.length`. This is what lets the reorder
    lemmas drop the `≤ 16` / `≤ 17` bounds and apply at arbitrary stack depth. -/
theorem doSwap_stack_ne0 {dist : Nat} {ps : PlanState} (h0 : dist ≠ 0)
    (hlen : dist < ps.stack.length) :
    (doSwap dist ps).2.stack = stackSwap dist ps.stack := by
  by_cases h16 : dist ≤ 16
  · exact doSwap_stack_small h0 h16
  · exact doSwap_stack_big (by omega) hlen

/-- `doSwap` preserves the stack length (for `dist < length`). -/
theorem doSwap_length {dist : Nat} {ps : PlanState} (hlen : dist < ps.stack.length) :
    (doSwap dist ps).2.stack.length = ps.stack.length := by
  by_cases h0 : dist = 0
  · subst h0; rw [doSwap_stack_zero]
  · rw [doSwap_stack_ne0 h0 hlen]; unfold stackSwap; simp [List.length_set]

/-- **`reorderOne` plan-stack effect, the 2-swap case.** When `op` is on the stack at depth
    `dist ≠ finalDist`, both non-zero and in range, `reorderOne` composes the two swaps: it first
    brings `op` to TOS (`stackSwap dist`), then swaps TOS to its final depth `finalDist =
    targetOps.length - 1 - idx` (`stackSwap finalDist`). This is the per-step plan-stack transition the
    general reorder's selection-sort fold (`perm_reaches`) iterates. Uses `doSwap_stack_ne0`, so it
    holds at arbitrary stack depth (big swaps included). -/
theorem reorderOne_stack_swap {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {dist : Nat}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hne : dist ≠ targetOps.length - 1 - idx)
    (hd0 : dist ≠ 0) (hdlt : dist < ps.stack.length)
    (hf0 : targetOps.length - 1 - idx ≠ 0) (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    (reorderOne () targetOps idx op ps).2.stack
      = stackSwap (targetOps.length - 1 - idx) (stackSwap dist ps.stack) := by
  unfold reorderOne
  simp only [hdepth, if_neg hne]
  rw [doSwap_stack_ne0 hf0 (by rw [doSwap_length hdlt]; exact hflt), doSwap_stack_ne0 hd0 hdlt]

/-! ## Output handling: optimistic swap

The live-output branch of `generateRegularInstPlan` ends with `optimisticSwapPlan`, which
brings the next-scheduled var to the top (a single swap) unless that is unnecessary. -/

/-- `optimisticSwapPlan` is structurally either a no-op (`([], ps)`) — every short-circuit
    branch: next-is-terminator, no outputs, no next-liveness, output already next-scheduled,
    or next-scheduled not on the stack — or a single `doSwap dist ps` at the depth of the
    next-scheduled var. -/
theorem optimisticSwapPlan_cases (dfg : DfgAnalysis) (inst : Instruction)
    (nextLiveness : List String) (nIT : Bool) (ps : PlanState) :
    optimisticSwapPlan dfg inst nextLiveness nIT ps = ([], ps) ∨
    ∃ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist ∧
            optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps := by
  simp only [optimisticSwapPlan]
  split_ifs with h1 h2 h3 h4
  · left; rfl
  · left; rfl
  · left; rfl
  · left; rfl
  · cases hd : stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack with
    | none => left; rfl
    | some dist => right; exact ⟨dist, rfl, rfl⟩

/-- `optimisticSwapPlan` simulation. The no-op branches preserve `venomAsmRel` trivially;
    the single-swap branch composes `doSwap_sim`, with the small-distance bound supplied as
    the residual `hswap` (discharged at the call site, as for `reorderPlan_sim`). vs-preserving
    (a pure stack reshuffle), so it composes with `plan_seq_sim` after the compute step. -/
theorem optimisticSwapPlan_sim {dfg inst nextLiveness nIT ps lo vs as prog}
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
        (executePlan (optimisticSwapPlan dfg inst nextLiveness nIT ps).1))
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist →
              optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps →
              dist ≤ 16 ∧ dist < ps.stack.length) :
    ∃ as', runAsm (executePlan (optimisticSwapPlan dfg inst nextLiveness nIT ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (optimisticSwapPlan dfg inst nextLiveness nIT ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (optimisticSwapPlan dfg inst nextLiveness nIT ps).1).length := by
  rcases optimisticSwapPlan_cases dfg inst nextLiveness nIT ps with hnoop | ⟨dist, hd, heq⟩
  · rw [hnoop]; exact ⟨as, rfl, hrel, rfl⟩
  · rw [heq] at hblock ⊢
    obtain ⟨_, hlen⟩ := hswap dist hd heq
    exact doSwap_sim rfl hrel hlen hblock (fun h => absurd h (by omega))

/-! ## Output handling: release dead spills

Both branches of `generateRegularInstPlan` end with `releaseDeadSpills`, which emits no asm
and only frees the spill slots of vars dead after this instruction (shrinking `spilled`,
extending `alloc.freeSlots`). It therefore preserves `venomAsmRel`. -/

/-- The fold body of `releaseDeadSpills`: keep the accumulator if the spilled var is still
    live, else drop its entry and free its slot. -/
def releaseDeadSpillStep (nextLiveness : List String) (ps' : PlanState)
    (p : Operand × Nat) : PlanState :=
  match p.1 with
  | Operand.Var v =>
    if nextLiveness.contains v then ps'
    else { ps' with spilled := aremove ps'.spilled p.1, alloc := freeSpillSlot p.2 ps'.alloc }
  | _ => { ps' with spilled := aremove ps'.spilled p.1, alloc := freeSpillSlot p.2 ps'.alloc }

theorem releaseDeadSpills_eq_foldl (nextLiveness : List String) (ps : PlanState) :
    releaseDeadSpills nextLiveness ps
      = ps.spilled.foldl (releaseDeadSpillStep nextLiveness) ps := rfl

/-- One fold step leaves `stack`/`fnEom`/`nextOffset` untouched and only shrinks `spilled`. -/
theorem releaseDeadSpillStep_props (nextLiveness : List String) (acc : PlanState)
    (p : Operand × Nat) :
    (releaseDeadSpillStep nextLiveness acc p).stack = acc.stack ∧
    (releaseDeadSpillStep nextLiveness acc p).alloc.fnEom = acc.alloc.fnEom ∧
    (releaseDeadSpillStep nextLiveness acc p).alloc.nextOffset = acc.alloc.nextOffset ∧
    (∀ op off, AssocList.lookup Operand Nat (releaseDeadSpillStep nextLiveness acc p).spilled op
                 = some off →
               AssocList.lookup Operand Nat acc.spilled op = some off) := by
  rcases p with ⟨op, off⟩
  cases op with
  | Var v =>
    dsimp only [releaseDeadSpillStep]
    split_ifs with hv
    · exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
    · exact ⟨rfl, rfl, rfl, fun o f h => aremove_lookup_some acc.spilled _ o f h⟩
  | Lit l =>
    dsimp only [releaseDeadSpillStep]
    exact ⟨rfl, rfl, rfl, fun o f h => aremove_lookup_some acc.spilled _ o f h⟩
  | Label l =>
    dsimp only [releaseDeadSpillStep]
    exact ⟨rfl, rfl, rfl, fun o f h => aremove_lookup_some acc.spilled _ o f h⟩

/-- The fold invariant: over any list/accumulator, `stack`/`fnEom`/`nextOffset` are
    preserved and the final `spilled` is a sub-map of the initial one. -/
theorem releaseDeadSpills_foldl_inv (nextLiveness : List String) (l : List (Operand × Nat)) :
    ∀ acc : PlanState,
      (l.foldl (releaseDeadSpillStep nextLiveness) acc).stack = acc.stack ∧
      (l.foldl (releaseDeadSpillStep nextLiveness) acc).alloc.fnEom = acc.alloc.fnEom ∧
      (l.foldl (releaseDeadSpillStep nextLiveness) acc).alloc.nextOffset = acc.alloc.nextOffset ∧
      (∀ op off, AssocList.lookup Operand Nat
                   (l.foldl (releaseDeadSpillStep nextLiveness) acc).spilled op = some off →
                 AssocList.lookup Operand Nat acc.spilled op = some off) := by
  induction l with
  | nil => intro acc; exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
  | cons hd tl ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨hs, hf, hn, hsub⟩ := releaseDeadSpillStep_props nextLiveness acc hd
    obtain ⟨hs', hf', hn', hsub'⟩ := ih (releaseDeadSpillStep nextLiveness acc hd)
    exact ⟨hs'.trans hs, hf'.trans hf, hn'.trans hn,
           fun o f h => hsub o f (hsub' o f h)⟩

/-- `releaseDeadSpills` never changes the plan stack (the fold only edits `spilled`/`alloc`). -/
theorem releaseDeadSpills_stack (nextLiveness : List String) (ps : PlanState) :
    (releaseDeadSpills nextLiveness ps).stack = ps.stack := by
  rw [releaseDeadSpills_eq_foldl]
  exact (releaseDeadSpills_foldl_inv nextLiveness ps.spilled ps).1

/-- `releaseDeadSpills` preserves spill-freedom: if no operand was spilled, none is afterwards
    (the fold only *removes* spill entries). -/
theorem releaseDeadSpills_noSpill (nextLiveness : List String) (ps : PlanState)
    (h : ∀ op, alookup' ps.spilled op = none) :
    ∀ op, alookup' (releaseDeadSpills nextLiveness ps).spilled op = none := by
  intro op
  rcases hlk : alookup' (releaseDeadSpills nextLiveness ps).spilled op with _ | off
  · rfl
  · exfalso
    rw [releaseDeadSpills_eq_foldl] at hlk
    have hsub := (releaseDeadSpills_foldl_inv nextLiveness ps.spilled ps).2.2.2 op off hlk
    have hnone : alookup' ps.spilled op = none := h op
    unfold alookup' at hnone
    rw [hnone] at hsub
    nomatch hsub

/-- `releaseDeadSpills` is the identity when there are no spills (`ps.spilled = []`): the fold over
    the spill map is a fold over `[]`. Used by `generateRegularInstPlan_jmp_id`. -/
theorem releaseDeadSpills_empty (nl : List String) (ps : PlanState)
    (h : ps.spilled = ([] : AssocList Operand Nat)) :
    releaseDeadSpills nl ps = ps := by
  unfold releaseDeadSpills; rw [h]; rfl

/-- `releaseDeadSpills` simulation: it emits no asm and touches only the spill bookkeeping
    (`spilled`/`alloc.freeSlots`), so `venomAsmRel` is preserved.

    * `planStackRel`: `ps.stack` is untouched.
    * `planSpillRel`: `spilled` only shrinks (`hsub`), so each surviving entry's value
      obligation still comes from the original relation.
    * `memoryRel`: `freeSpillSlot` preserves `fnEom`/`nextOffset`, the only `alloc` fields
      `memoryRel` reads.
    * shared state: untouched. -/
theorem releaseDeadSpills_sim {nextLiveness lo ps vs as}
    (hrel : venomAsmRel lo ps vs as) :
    venomAsmRel lo (releaseDeadSpills nextLiveness ps) vs as := by
  rw [releaseDeadSpills_eq_foldl]
  obtain ⟨hstk, hfn, hno, hsub⟩ := releaseDeadSpills_foldl_inv nextLiveness ps.spilled ps
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · rw [hstk]; exact hStk
  · intro op off hlook; exact hSpill op off (hsub op off hlook)
  · intro i hi; rw [hfn, hno] at hi; exact hMem i hi

/-! ## Regular-instruction connectors

Small structural lemmas wiring the generated segments into the standard sim shapes for the
full `generateRegularInstPlan` composition. -/

/-- `popmanyPlan` with nothing to pop is a no-op — the live-output case of
    `generateRegularInstPlan` (every output stays live, so `dead = []`). -/
theorem popmanyPlan_nil (ps : PlanState) : popmanyPlan [] ps = ([], ps) := by
  unfold popmanyPlan; simp

/-- `popmanyPlan []` simulation: emits no asm, preserves `venomAsmRel`. -/
theorem popmanyPlan_nil_sim {ps lo vs as prog} (hrel : venomAsmRel lo ps vs as) :
    ∃ as', runAsm (executePlan (popmanyPlan [] ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (popmanyPlan [] ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (popmanyPlan [] ps).1).length := by
  rw [popmanyPlan_nil]; exact ⟨as, rfl, hrel, rfl⟩

/-! ## Dead-operand discard (the single-`POP` step)

A regular instruction whose output is *dead* in `nextLiveness` has its just-pushed result
discarded: the asm side emits `POP`, the plan side `stackPop 1`. The Venom step still writes
the output to `vars` (Venom keeps every var) — it is simply absent from the operand stack
afterwards, which is exactly what `planStackRel` allows. `SOPop 1` lowers to a single
`AsmOp "POP"`, so every `popmanyPlan` dead-output lowering bottoms out in this atomic step. -/

/-- **A single TOS pop preserves `venomAsmRel`.** With `a` on top of the asm stack, popping
    one element on each side (asm `POP`, plan `stackPop 1`) keeps the loop invariant: only
    `planStackRel` changes (`planStackRel_pop`), and every other component reads `vars` /
    `spilled` / `alloc` / `memory` / shared fields, all untouched. The discard analog of
    `venomAsmRel_sstore` (no Venom-state change at all). -/
theorem venomAsmRel_pop {lo ps vs as} {a rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = a :: rest) :
    venomAsmRel lo { ps with stack := stackPop 1 ps.stack } vs
      { asmNext as with stack := rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  refine ⟨?_, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  rw [hstack] at hStk
  exact planStackRel_pop hStk

/-- The runnable discard step for a dead output: running the emitted `[SOPop 1]` from a state
    with the dead value `a` on top pops it, advances the pc by 1, and preserves `venomAsmRel`.
    The `POP`-step companion of `emit_sstore_sim`; consumed by the dead-output branch of
    `generateRegularInstPlan` (`popmanyPlan`). -/
theorem emit_pop1_sim {ps lo vs as prog a rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = a :: rest)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOPop 1])) :
    ∃ as', runAsm (executePlan [StackOp.SOPop 1]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 1 ps.stack } vs as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOPop 1]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK { asmNext as with stack := rest } := by
    have hd : asmStep offsetToPc prog as = asmPop as := by unfold asmStep; rw [dif_pos hpc, hget]; rfl
    rw [hd]; simp only [asmPop, hstack]
  refine ⟨{ asmNext as with stack := rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_pop hrel hstack
  · rfl



/-- `generateEmitOps` for an opcode with a direct EVM name emits exactly `[SOEmit name]` and
    leaves the plan state unchanged — the shape `emit_binop_sim` consumes for the arithmetic
    opcodes (`opcodeToEvmName` = `some "ADD"`, etc.). -/
theorem generateEmitOps_evmName {inst : Instruction} {logTopicCount : Nat} {ps : PlanState}
    {name : String} (h : opcodeToEvmName inst.opcode = some name) :
    generateEmitOps inst logTopicCount ps = ([StackOp.SOEmit name], ps) := by
  simp only [generateEmitOps, h]

/-! ## Input-emission positioning invariant

The compute step (`emit_binop_sim`) needs the input operands on top of the asm stack. That
fact comes from `emitInputPlan`'s effect on the *plan* stack (transferred by `planStackRel`).
Here is the all-literal case: emitting literal inputs appends them to the plan stack in
order (last operand = TOS), so they end up positioned with no reorder needed. -/

/-- Emitting a literal input pushes it onto the (TOS = last) plan stack. -/
theorem emitOneInput_stack_lit (opc : Opcode) (nl : List String) (v : bytes32)
    (ps : PlanState) :
    (emitOneInput opc nl (Operand.Lit v) ps).2.stack = ps.stack ++ [Operand.Lit v] := by
  unfold emitOneInput
  simp [isVarOperand, stackPush]

/-- Positioning invariant (all-literal case), generalized over the fold accumulator. -/
theorem emitInputPlan_foldl_stack_allLit (opc : Opcode) (nl : List String) :
    ∀ (ops : List Operand), (∀ op ∈ ops, ∃ v, op = Operand.Lit v) →
    ∀ (acc : List StackOp × PlanState),
      (ops.foldl (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1,
                                 (emitOneInput opc nl op acc.2).2)) acc).2.stack
        = acc.2.stack ++ ops := by
  intro ops
  induction ops with
  | nil => intro _ acc; simp
  | cons hd tl ih =>
    intro h acc
    obtain ⟨v, rfl⟩ := h hd (List.mem_cons_self)
    rw [List.foldl_cons,
        ih (fun op hop => h op (List.mem_cons_of_mem _ hop)),
        show (emitOneInput opc nl (Operand.Lit v) acc.2).2.stack = acc.2.stack ++ [Operand.Lit v]
          from emitOneInput_stack_lit opc nl v acc.2]
    simp

/-- `emitInputPlan` (all literals) leaves the operands as the top of the plan stack, in order
    (last operand = TOS). This is the postcondition feeding the compute step's "inputs on
    top" precondition (via `planStackRel`) when no reorder is needed. -/
theorem emitInputPlan_stack_allLit (opc : Opcode) (ops : List Operand) (nl : List String)
    (ps : PlanState) (h : ∀ op ∈ ops, ∃ v, op = Operand.Lit v) :
    (emitInputPlan opc ops nl ps).2.stack = ps.stack ++ ops := by
  have := emitInputPlan_foldl_stack_allLit opc nl ops h ([], ps)
  simpa [emitInputPlan] using this

/-! ## Reorder no-op when positioned

The complement of the positioning invariant: once the operands are at their target depths
(which input emission establishes), `reorderPlan` emits nothing. -/

/-- Fold form: if every operand is already at its target depth in (the fixed) `ps.stack`,
    each `reorderOne` is a no-op, so the whole reorder fold leaves `(acc, ps)` unchanged. -/
theorem reorderPlan_foldl_nil (targetOps : List Operand) (ps : PlanState) :
    ∀ (l : List (Nat × Operand)) (acc : List StackOp),
      (∀ p ∈ l, stackGetDepth p.2 ps.stack = some (targetOps.length - 1 - p.1)) →
      l.foldl (fun (a : List StackOp × PlanState) (q : Nat × Operand) =>
        (a.1 ++ (reorderOne () targetOps q.1 q.2 a.2).1, (reorderOne () targetOps q.1 q.2 a.2).2))
        (acc, ps) = (acc, ps) := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons hd tl ih =>
    intro acc h
    rw [List.foldl_cons]
    have hno : reorderOne () targetOps hd.1 hd.2 ps = ([], ps) :=
      reorderOne_nil_of_positioned (h hd (List.mem_cons_self))
    simp only [hno, List.append_nil]
    exact ih acc (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- `reorderPlan` is a no-op when every target operand is already at its final position
    (`stackGetDepth = targetOps.length - 1 - idx`). The positioning hypothesis is what
    input-emission establishes; discharging it (e.g. via distinctness for literals) is left
    to the caller. -/
theorem reorderPlan_nil_of_allPositioned (targetOps : List Operand) (ps : PlanState)
    (h : ∀ p ∈ targetOps.enum,
           stackGetDepth p.2 ps.stack = some (targetOps.length - 1 - p.1)) :
    reorderPlan targetOps ps = ([], ps) := by
  unfold reorderPlan
  exact reorderPlan_foldl_nil targetOps ps targetOps.enum [] h

/-- **Discharge of the positioning hypothesis for any distinct operand pair already on top:**
    `reorderPlan [p, q]` is a no-op when `ps.stack = base ++ [p, q]` and `q ≠ p`. Nothing here
    reads the operands' *class* — only that the top one differs from the one below it, so the
    reverse search for `p` skips the TOS. The literal, var, and **mixed Var/Lit** pairs are all
    instances (for a mixed pair the distinctness is free: the constructors differ). -/
theorem reorderPlan_pair_nil (base : List Operand) (p q : Operand) (ps : PlanState)
    (hstack : ps.stack = base ++ [p, q]) (hqp : q ≠ p) :
    reorderPlan [p, q] ps = ([], ps) := by
  have hqp' : (q == p) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hqp
  apply reorderPlan_nil_of_allPositioned
  intro r hr
  have henum : ([p, q]).enum = [(0, p), (1, q)] := rfl
  rw [henum] at hr
  rw [hstack]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · show stackGetDepth p (base ++ [p, q]) = some 1
    simp [stackGetDepth, stackFind, List.reverse_append, hqp']
  · show stackGetDepth q (base ++ [p, q]) = some 0
    simp [stackGetDepth, stackFind, List.reverse_append]

/-- Discharge of the positioning hypothesis for a distinct literal pair already on top:
    `reorderPlan [Lit a, Lit b]` is a no-op when `ps.stack = base ++ [Lit a, Lit b]` and
    `a ≠ b`. This is the concrete reorder-no-op for a 2-input binop after input emission
    (`emitInputPlan_stack_allLit` supplies the `base ++ [Lit a, Lit b]` shape). -/
theorem reorderPlan_pair_lit_nil (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) (hab : a ≠ b) :
    reorderPlan [Operand.Lit a, Operand.Lit b] ps = ([], ps) :=
  reorderPlan_pair_nil base _ _ ps hstack (fun h => hab (Operand.Lit.inj h).symm)

/-- `reorderPlan [Var x, Var y]` is a no-op when that pair is already positioned (`Var x` at depth 1,
    `Var y` at depth 0). The var counterpart of `reorderPlan_pair_lit_nil` (the commutative `opsA`
    side). -/
theorem reorderPlan_pair_var_nil (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) (hxy : x ≠ y) :
    reorderPlan [Operand.Var x, Operand.Var y] ps = ([], ps) :=
  reorderPlan_pair_nil base _ _ ps hstack (fun h => hxy (Operand.Var.inj h).symm)

/-- **The mixed `[Var x, Lit b]` reorder is a no-op** — the `ADD %x, b` operand shape after input
    emission (`PUSH b ; DUP`, so the var is TOS). Unlike the literal and var pairs this needs *no*
    distinctness side condition: `Lit b` and `Var x` are different constructors. -/
theorem reorderPlan_pair_litVar_nil (base : List Operand) (b : bytes32) (x : String)
    (ps : PlanState) (hstack : ps.stack = base ++ [Operand.Lit b, Operand.Var x]) :
    reorderPlan [Operand.Lit b, Operand.Var x] ps = ([], ps) :=
  reorderPlan_pair_nil base _ _ ps hstack (by simp)

/-- **The mixed `[Lit a, Var y]` reorder is a no-op** — the `ADD a, %y` operand shape after input
    emission (`DUP ; PUSH a`, so the literal is TOS). The mirror of `reorderPlan_pair_litVar_nil`. -/
theorem reorderPlan_pair_varLit_nil (base : List Operand) (y : String) (a : bytes32)
    (ps : PlanState) (hstack : ps.stack = base ++ [Operand.Var y, Operand.Lit a]) :
    reorderPlan [Operand.Var y, Operand.Lit a] ps = ([], ps) :=
  reorderPlan_pair_nil base _ _ ps hstack (by simp)

/-- `reorderCost` of a positioned reorder is zero — the `opsA` side of the commutative
    optimization's cheaper-order comparison in `generateRegularInstPlan`. -/
theorem reorderCost_eq_zero_of_positioned (targetOps : List Operand) (ps : PlanState)
    (h : ∀ p ∈ targetOps.enum,
           stackGetDepth p.2 ps.stack = some (targetOps.length - 1 - p.1)) :
    reorderCost (reorderPlan targetOps ps).1 = 0 := by
  rw [reorderPlan_nil_of_allPositioned targetOps ps h]; rfl

/-! ## Stack-swap algebra

`stackSwap 1` exchanges the top two elements; on a stack whose top two are `[x, y]` this is
the explicit `base ++ [y, x]`. Needed to evaluate the swapped-order reorder in the
commutative branch (`reorderCost opsB`). -/

theorem getbang_append_pair_fst (base : List Operand) (x y : Operand) :
    (base ++ [x, y])[base.length]! = x := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

theorem getbang_append_pair_snd (base : List Operand) (x y : Operand) :
    (base ++ [x, y])[base.length + 1]! = y := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

/-- `stackSwap 1` on a stack whose top two are `[x, y]` (y = TOS) swaps them. -/
theorem stackSwap_1_append_pair (base : List Operand) (x y : Operand) :
    stackSwap 1 (base ++ [x, y]) = base ++ [y, x] := by
  have hlen : (base ++ [x, y]).length = base.length + 2 := by simp
  have htop : (base ++ [x, y])[base.length + 1]! = y := getbang_append_pair_snd base x y
  have htgt : (base ++ [x, y])[base.length]! = x := getbang_append_pair_fst base x y
  have hset1 : (base ++ [x, y]).set (base.length + 1) x = base ++ [x, x] := by
    rw [List.set_append_right (base.length + 1) x (Nat.le_succ _)]; simp
  have hset2 : (base ++ [x, x]).set base.length y = base ++ [y, x] := by
    rw [List.set_append_right base.length y (Nat.le_refl _)]; simp
  unfold stackSwap
  simp only [hlen]
  rw [show base.length + 2 - 1 = base.length + 1 from by omega,
      show base.length + 1 - 1 = base.length from by omega,
      htop, htgt, hset1, hset2]

/-- `reorderOne` when the operand is already on top (`dist = 0`) but its target depth `f` is nonzero
    (`≤ 16`): `doSwap 0` is a no-op, so it emits one `SWAP f`. -/
theorem reorderOne_dist0 {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {f : Nat} (hf : targetOps.length - 1 - idx = f)
    (hd : stackGetDepth op ps.stack = some 0) (hf0 : f ≠ 0) (hf16 : f ≤ 16) :
    reorderOne () targetOps idx op ps
      = ([StackOp.SOSwap f], { ps with stack := stackSwap f ps.stack }) := by
  simp only [reorderOne, hf, hd, if_neg (Ne.symm hf0)]
  rw [show doSwap 0 ps = ([], ps) from by rw [doSwap, if_pos rfl]]
  simp only [List.nil_append]
  rw [show doSwap f ps = ([StackOp.SOSwap f], { ps with stack := stackSwap f ps.stack })
      from by rw [doSwap, if_neg hf0, if_pos hf16]]

/-- **The reorder for a *repeated* operand pair `[Var x, Var x]` is one `SWAP1` — a semantic no-op**
    (the two identical operands are already at the store's target depths; the swap exchanges equal
    values, leaving the plan state unchanged). Same-var analogue of `reorderPlan_pair_var_nil` (which
    needs `x ≠ y` and yields `[]`). Together with `emitInputPlan_pair_var_same_sim` this pins the
    same-var 2-input plan to `emit [x,x] ++ [SWAP1] ++ [op]` with the swap a no-op — the reorder half
    of the `x = y` coverage gap. -/
theorem reorderPlan_pair_var_same (base : List Operand) (x : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var x, Operand.Var x] ps = ([StackOp.SOSwap 1], ps) := by
  have hd0 : stackGetDepth (Operand.Var x) ps.stack = some 0 := by
    rw [hstack]; simp [stackGetDepth, stackFind, List.reverse_append]
  have hswap : stackSwap 1 ps.stack = ps.stack := by rw [hstack, stackSwap_1_append_pair]
  unfold reorderPlan
  rw [show [Operand.Var x, Operand.Var x].enum = [(0, Operand.Var x), (1, Operand.Var x)] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
  rw [reorderOne_dist0 (targetOps := [Operand.Var x, Operand.Var x]) (idx := 0) (f := 1) rfl hd0
      (by decide) (by decide)]
  have hps0 : ({ ps with stack := stackSwap 1 ps.stack } : PlanState) = ps := by rw [hswap]
  rw [hps0, reorderOne_nil_of_positioned (targetOps := [Operand.Var x, Operand.Var x]) (idx := 1)
    (by simpa using hd0)]
  rfl

/-! ## Swapped-order reorder (commutative branch `opsB`)

The commutative optimization compares `reorderPlan operands` (cost 0 when positioned) with
`reorderPlan swapped`. For a positioned literal pair the swapped order costs one `SWAP1`, so
the comparison `0 < 1` pins the cheaper choice to the un-swapped `operands`. -/

/-- The TOS of `base ++ [x, y]` is `y` at depth 0. -/
theorem stackGetDepth_tos (base : List Operand) (x y : Operand) :
    stackGetDepth y (base ++ [x, y]) = some 0 := by
  simp [stackGetDepth, stackFind, List.reverse_append]

/-- `stackFind` returning `some d` witnesses that the `d`-th element (from the head) satisfies the
    predicate, and that `d` is in range. Proved by induction on the list. -/
theorem stackFind_some {p : Operand → Bool} :
    ∀ {l : List Operand} {d : Nat}, stackFind p l = some d → d < l.length ∧ p (l[d]!) = true := by
  intro l
  induction l with
  | nil => intro d h; simp [stackFind] at h
  | cons a as ih =>
    intro d h
    rw [stackFind] at h
    split at h
    · rename_i hpa
      have hd : d = 0 := by simpa using h.symm
      subst hd
      exact ⟨Nat.succ_pos _, by simpa using hpa⟩
    · rename_i hpa
      cases hf : stackFind p as with
      | none => rw [hf] at h; simp at h
      | some d' =>
        rw [hf] at h
        have hd : d = d' + 1 := by simpa using h.symm
        subst hd
        obtain ⟨hlt, hp⟩ := ih hf
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        simpa using hp

/-- Bridge: if `stackGetDepth op stk = some d` then peeking at depth `d` returns `op`. The depth
    search scans `stk.reverse` from the head (TOS first); `stackPeek d` reads `stk` at
    `length-1-d`, which is exactly `stk.reverse[d]`. -/
theorem stackGetDepth_peek {op : Operand} {stk : List Operand} {d : Nat}
    (h : stackGetDepth op stk = some d) : stackPeek d stk = op := by
  unfold stackGetDepth at h
  obtain ⟨hlt, hp⟩ := stackFind_some h
  rw [List.length_reverse] at hlt
  have hbeq : stk.reverse[d]! = op := by simpa using hp
  unfold stackPeek
  rw [← hbeq]
  rw [
      List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_reverse hlt]

/-- A found depth is a valid index into the stack (`stackGetDepth = stackFind ∘ reverse`, and
    `stackFind_some` bounds the returned index). Lets N-input emission derive its per-DUP length
    side-conditions from the depth chain alone. -/
theorem stackGetDepth_lt_length {op : Operand} {stk : List Operand} {d : Nat}
    (h : stackGetDepth op stk = some d) : d < stk.length := by
  unfold stackGetDepth at h
  have := (stackFind_some h).1
  rwa [List.length_reverse] at this

/-- **Per-`reorderOne` asm discharge, small-swap case — base-independent.** The only requirement is that
    the operand's depth `dist` and its final depth are both `≤ 16` (small swaps, no spilling); the *total*
    stack depth is irrelevant. So a reorder region sitting atop an arbitrarily deep base still runs, as
    long as the region itself is `≤ 16` deep (which a JMP-join's live-var layout always is). Generalises
    `reorderOne_asm_bounded` (which conservatively bounded the whole stack by 17). -/
theorem reorderOne_asm_smallswap {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {dist : Nat}
    (hdist : stackGetDepth op ps.stack = some dist)
    (hd16 : dist ≤ 16) (hf16 : targetOps.length - 1 - idx ≤ 16)
    (hflen : targetOps.length - 1 - idx < ps.stack.length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (reorderOne () targetOps idx op ps).1)) :
    ∃ as', runAsm (executePlan (reorderOne () targetOps idx op ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (reorderOne () targetOps idx op ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (reorderOne () targetOps idx op ps).1).length := by
  by_cases hpos : dist = targetOps.length - 1 - idx
  · rw [hpos] at hdist; exact reorderOne_sim_positioned hdist hrel
  · exact reorderOne_sim_swap hdist hpos hd16 hf16 hrel (stackGetDepth_lt_length hdist) hflen hblock

/-- **Per-`reorderOne` asm discharge, bounded case** (`ps.stack.length ≤ 17` ⇒ `dist ≤ 16`). The
    conservative corollary of `reorderOne_asm_smallswap` used by the JMP-join fold: bounding the whole
    stack by 17 is enough for the join case (the reorder region *is* the whole live-var stack), and gives
    `dist ≤ 16` from `dist < ps.stack.length`. -/
theorem reorderOne_asm_bounded {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {dist : Nat}
    (hdist : stackGetDepth op ps.stack = some dist)
    (hfbound : targetOps.length - 1 - idx ≤ 16)
    (hflen : targetOps.length - 1 - idx < ps.stack.length)
    (hsbound : ps.stack.length ≤ 17)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (reorderOne () targetOps idx op ps).1)) :
    ∃ as', runAsm (executePlan (reorderOne () targetOps idx op ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (reorderOne () targetOps idx op ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (reorderOne () targetOps idx op ps).1).length :=
  reorderOne_asm_smallswap hdist (by have := stackGetDepth_lt_length hdist; omega) hfbound hflen hrel hblock

/-- **Depth-shift when the stack grows by one *different* operand:** appending `q ≠ p` pushes `p`'s
    depth up by one. Class-agnostic — the appended operand may be a DUP'd var (`stackDup d s =
    s ++ [peek]`, the var-pair case) or a **`PUSH`ed literal** (the mixed Var/Lit case, where the var
    is DUP'd from the already-pushed stack). This is the depth-tracking step a per-block
    stack-discipline invariant maintains across instructions. -/
theorem stackGetDepth_append_ne_op {p q : Operand} (stk : List Operand) (h : q ≠ p) :
    stackGetDepth p (stk ++ [q]) = (stackGetDepth p stk).map (· + 1) := by
  unfold stackGetDepth
  rw [List.reverse_append]
  have hne : (q == p) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, stackFind, hne,
    Bool.false_eq_true, if_false]
  cases stackFind (fun z => z == p) stk.reverse <;> simp

/-- Depth-shift under a DUP: appending a *different* var to the bottom-to-top stack pushes every
    other var's depth up by one. `stackDup d s = s ++ [peek]`, so the second operand of a var pair
    sits one deeper after the first DUP — this is the `hdepth_x'` relation the var-binop input needs.
    The all-var instance of `stackGetDepth_append_ne_op`. -/
theorem stackGetDepth_append_ne {x y : String} (stk : List Operand) (h : x ≠ y) :
    stackGetDepth (Operand.Var x) (stk ++ [Operand.Var y])
      = (stackGetDepth (Operand.Var x) stk).map (· + 1) :=
  stackGetDepth_append_ne_op stk (fun hc => h (Operand.Var.inj hc).symm)

/-- **Depth-shift under a `PUSH`:** appending a literal pushes every var's depth up by one — the
    mixed Var/Lit instance of `stackGetDepth_append_ne_op`, needing no side condition (a `Lit` is
    never a `Var`). This is what turns a var's depth in `ps.stack` into its depth in
    `ps.stack ++ [Lit b]`, where `emitInputPlan_pair_litVar_eq` reads it. -/
theorem stackGetDepth_append_lit {x : String} (stk : List Operand) (b : bytes32) :
    stackGetDepth (Operand.Var x) (stk ++ [Operand.Lit b])
      = (stackGetDepth (Operand.Var x) stk).map (· + 1) :=
  stackGetDepth_append_ne_op stk (by simp)

/-! ## Positioned nodup var list (join reconciliation, well-scheduled case)

For the inter-block JMP join, the well-scheduled case is when the body already produces the target
block's expected entry layout `S.map Var`, so the join `reorderPlan (S.map Var)` is a no-op. The
foundation is that a **nodup** operand list is positioned as itself: `stackFind` on a nodup list finds
exactly the queried index, so `stackGetDepth L[i] L = some (length-1-i)` — every element is at its own
target depth. -/


/-- First hit after a miss-prefix: scanning `xs ++ y :: ys` with every `xs` element failing and
    `y` matching finds index `xs.length`. -/
theorem stackFind_prefix_hit {p : Operand → Bool} :
    ∀ {xs : List Operand} {y : Operand} {ys : List Operand},
      (∀ x ∈ xs, p x = false) → p y = true →
      stackFind p (xs ++ y :: ys) = some xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro y ys _ hy
    show stackFind p (y :: ys) = some 0
    unfold stackFind
    simp [hy]
  | cons x xs ih =>
    intro y ys hmiss hy
    show stackFind p (x :: (xs ++ y :: ys)) = some (xs.length + 1)
    unfold stackFind
    rw [show p x = false from hmiss x List.mem_cons_self]
    simp only [Bool.false_eq_true, if_false]
    rw [ih (fun w hw => hmiss w (List.mem_cons_of_mem x hw)) hy]

/-- **Middle-position depth**: an operand whose every occurrence above it is absent sits at depth
    `B.length` in `A ++ op :: B` (the scan from the TOS crosses `B` first). The segment-general
    form of the pair/triple/quad depth computations — the workhorse for the N-ary doubles-reorder
    fold invariant. -/
theorem stackGetDepth_middle {A : List Operand} {op : Operand} {B : List Operand}
    (hnotB : op ∉ B) : stackGetDepth op (A ++ op :: B) = some B.length := by
  unfold stackGetDepth
  rw [show (A ++ op :: B).reverse = B.reverse ++ op :: A.reverse from by simp]
  rw [show B.length = B.reverse.length from by simp]
  apply stackFind_prefix_hit
  · intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc
    exact hnotB (by rw [← hc]; exact List.mem_reverse.mp hx)
  · exact beq_self_eq_true op

/-- getElem! at the seam of `C ++ a :: D`. -/
theorem getbang_append_middle (C : List Operand) (a : Operand) (D : List Operand) :
    (C ++ a :: D)[C.length]! = a := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- getElem! at the top of `C ++ a :: (D ++ [t])`. -/
theorem getbang_middle_top (C : List Operand) (a : Operand) (D : List Operand) (t : Operand) :
    (C ++ a :: (D ++ [t]))[C.length + D.length + 1]! = t := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  rw [show C.length + D.length + 1 - C.length = D.length + 1 from by omega]
  rw [show (a :: (D ++ [t]))[D.length + 1]? = (D ++ [t])[D.length]? from rfl]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- set at the seam of `C ++ a :: D`. -/
theorem set_append_middle (C : List Operand) (a b : Operand) (D : List Operand) :
    (C ++ a :: D).set C.length b = C ++ b :: D := by
  rw [List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-- set at the top of `C ++ a :: (D ++ [t])`. -/
theorem set_middle_top (C : List Operand) (a : Operand) (D : List Operand) (t b : Operand) :
    (C ++ a :: (D ++ [t])).set (C.length + D.length + 1) b = C ++ a :: (D ++ [b]) := by
  rw [List.set_append_right _ _ (by omega)]
  rw [show C.length + D.length + 1 - C.length = D.length + 1 from by omega]
  rw [show (a :: (D ++ [t])).set (D.length + 1) b = a :: ((D ++ [t]).set D.length b) from rfl]
  rw [List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-- **Middle-position swap**: swapping the TOS with the element at depth `D.length + 1` in
    `C ++ a :: (D ++ [t])` exchanges `a` and `t` across the untouched middle segment `D`. The
    segment-general form of the `stackSwap_{1,2,3}_append_*` family. -/
theorem stackSwap_middle (C : List Operand) (a : Operand) (D : List Operand) (t : Operand) :
    stackSwap (D.length + 1) (C ++ a :: (D ++ [t])) = C ++ t :: (D ++ [a]) := by
  have hlen : (C ++ a :: (D ++ [t])).length = C.length + D.length + 2 := by
    simp; omega
  have htop : (C ++ a :: (D ++ [t]))[C.length + D.length + 1]! = t :=
    getbang_middle_top C a D t
  have htgt : (C ++ a :: (D ++ [t]))[C.length]! = a := getbang_append_middle C a (D ++ [t])
  have hset1 : (C ++ a :: (D ++ [t])).set (C.length + D.length + 1) a
      = C ++ a :: (D ++ [a]) := set_middle_top C a D t a
  have hset2 : (C ++ a :: (D ++ [a])).set C.length t = C ++ t :: (D ++ [a]) :=
    set_append_middle C a t (D ++ [a])
  unfold stackSwap
  simp only [hlen,
    show C.length + D.length + 2 - 1 = C.length + D.length + 1 from by omega,
    show C.length + D.length + 1 - (D.length + 1) = C.length from by omega,
    htop, htgt, hset1, hset2]

/-- **The seat-and-hoist step**: the fold's current operand sits at the TOS (hoisted by the
    previous step); one `SWAP (D.length + 1)` seats it at its final slot and hoists the seam
    element `next`. The generic per-step reduction of the doubles-reorder pre-phase. -/
theorem reorderOne_seat_hoist {tgt : List Operand} {i : Nat} {cur next : Operand} {ps : PlanState}
    {C D : List Operand}
    (htos : ps.stack = C ++ next :: (D ++ [cur]))
    (hdist : D.length + 1 = tgt.length - 1 - i)
    (hd16 : D.length + 1 ≤ 16) :
    reorderOne () tgt i cur ps
      = ([StackOp.SOSwap (D.length + 1)], { ps with stack := C ++ cur :: (D ++ [next]) }) := by
  have hdepth : stackGetDepth cur ps.stack = some 0 := by
    rw [htos, show C ++ next :: (D ++ [cur]) = (C ++ next :: D) ++ cur :: [] from by simp]
    simpa using stackGetDepth_middle (A := C ++ next :: D) (op := cur) (B := []) (by simp)
  have hds0 : doSwap 0 ps = ([], ps) := by rw [doSwap, if_pos rfl]
  have hswapfin : doSwap (tgt.length - 1 - i) ps
      = ([StackOp.SOSwap (D.length + 1)], { ps with stack := C ++ cur :: (D ++ [next]) }) := by
    rw [← hdist]
    unfold doSwap
    rw [if_neg (by omega), if_pos hd16]
    rw [htos, stackSwap_middle]
  have h0ne : ¬ ((0 : Nat) = tgt.length - 1 - i) := by omega
  unfold reorderOne
  simp only [hdepth, hds0, hswapfin, if_neg h0ne, List.nil_append]

/-- **The park-and-seat step** (the doubles-reorder phase opener): the current operand sits at
    full depth; the first swap brings it to the TOS (parking the old TOS at the bottom slot),
    the second seats it one below, hoisting the seam element `next`. Two `stackSwap_middle`
    applications at shifted segmentations. -/
theorem reorderOne_park_seat {tgt : List Operand} {i : Nat} {cur next t : Operand}
    {ps : PlanState} {C D : List Operand}
    (htos : ps.stack = C ++ cur :: next :: (D ++ [t]))
    (habsent : cur ∉ next :: (D ++ [t]))
    (hdist : D.length + 2 = tgt.length - 1 - i + 1)
    (hd16 : D.length + 2 ≤ 16) :
    reorderOne () tgt i cur ps
      = ([StackOp.SOSwap (D.length + 2), StackOp.SOSwap (D.length + 1)],
         { ps with stack := C ++ t :: cur :: (D ++ [next]) }) := by
  have hdepth : stackGetDepth cur ps.stack = some (D.length + 2) := by
    rw [htos]
    have h := stackGetDepth_middle (A := C) (op := cur) (B := next :: (D ++ [t])) habsent
    simpa using h
  have hswap1 : doSwap (D.length + 2) ps
      = ([StackOp.SOSwap (D.length + 2)],
         { ps with stack := C ++ t :: next :: (D ++ [cur]) }) := by
    unfold doSwap
    rw [if_neg (by omega), if_pos hd16]
    rw [htos,
        show C ++ cur :: next :: (D ++ [t]) = C ++ cur :: ((next :: D) ++ [t]) from by simp,
        show (D.length + 2 : Nat) = (next :: D).length + 1 from by simp,
        stackSwap_middle C cur (next :: D) t]
    simp
  have hswap2 : doSwap (tgt.length - 1 - i)
        ({ ps with stack := C ++ t :: next :: (D ++ [cur]) } : PlanState)
      = ([StackOp.SOSwap (D.length + 1)],
         { ps with stack := C ++ t :: cur :: (D ++ [next]) }) := by
    rw [show tgt.length - 1 - i = D.length + 1 from by omega]
    unfold doSwap
    rw [if_neg (by omega), if_pos (by omega)]
    rw [show ({ ps with stack := C ++ t :: next :: (D ++ [cur]) } : PlanState).stack
          = (C ++ [t]) ++ next :: (D ++ [cur]) from by simp,
        stackSwap_middle (C ++ [t]) next D cur]
    simp
  have hne : ¬ (D.length + 2 = tgt.length - 1 - i) := by omega
  unfold reorderOne
  simp only [hdepth, if_neg hne, hswap1, hswap2, List.nil_append]
  rfl

/-- **The seated no-op**: the operand already sits at its target depth — `reorderOne` emits
    nothing. (Covers the trailing post-operands and the `q = 0` v-step.) -/
theorem reorderOne_seated {tgt : List Operand} {i : Nat} {cur : Operand} {ps : PlanState}
    {d : Nat}
    (hdepth : stackGetDepth cur ps.stack = some d)
    (hfin : d = tgt.length - 1 - i) :
    reorderOne () tgt i cur ps = ([], ps) := by
  unfold reorderOne
  simp only [hdepth, if_pos hfin]

/-- Descending swap run: `descSwaps n = [SWAP n, SWAP n-1, …, SWAP 1]`. -/
def descSwaps : Nat → List StackOp
  | 0 => []
  | n + 1 => StackOp.SOSwap (n + 1) :: descSwaps n

/-- **The seat-and-hoist chain** (fold form, accumulator-generalized): from the invariant stack,
    folding the remaining enum entries seats each hoisted element in one descending swap and ends
    with the seated `w`-step — emitting exactly `descSwaps hs.length` and landing at
    `B ++ placed ++ hs ++ [w]`. -/
theorem reorderFold_chain (tgt : List Operand) (B : List Operand) (w : Operand) :
    ∀ (hs : List Operand) (placed : List Operand) (i : Nat) (ps : PlanState)
      (ops0 : List StackOp),
      (match hs with
       | [] => ps.stack = B ++ placed ++ [w]
       | c :: cs => ps.stack = B ++ placed ++ ((cs ++ [w]) ++ [c])) →
      i + hs.length + 1 = tgt.length →
      hs.length ≤ 15 →
      ((hs ++ [w]).zipIdx i).foldl
          (fun acc x => (acc.1 ++ (reorderOne () tgt x.2 x.1 acc.2).1,
            (reorderOne () tgt x.2 x.1 acc.2).2)) (ops0, ps)
        = (ops0 ++ descSwaps hs.length, { ps with stack := B ++ (placed ++ hs) ++ [w] }) := by
  intro hs
  induction hs with
  | nil =>
    intro placed i ps ops0 hstk hidx _
    simp only at hstk
    simp only [List.length_nil] at hidx
    have hdepth : stackGetDepth w ps.stack = some 0 := by
      rw [hstk, show B ++ placed ++ [w] = (B ++ placed) ++ w :: [] from by simp]
      simpa using stackGetDepth_middle (A := B ++ placed) (op := w) (B := []) (by simp)
    have hseated : reorderOne () tgt i w ps = ([], ps) := by
      refine reorderOne_seated hdepth ?_
      omega
    show ([(w, i)]).foldl _ (ops0, ps) = _
    simp only [List.foldl_cons, List.foldl_nil, hseated, List.append_nil, descSwaps,
      Prod.mk.injEq]
    refine ⟨by simp [descSwaps], ?_⟩
    rw [← hstk]
  | cons c cs ih =>
    intro placed i ps ops0 hstk hidx h16
    simp only at hstk
    simp only [List.length_cons] at hidx h16
    show (((c :: (cs ++ [w]))).zipIdx i).foldl _ (ops0, ps) = _
    rw [List.zipIdx_cons, List.foldl_cons]
    cases cs with
    | nil =>
      have hstep := reorderOne_seat_hoist (tgt := tgt) (i := i) (cur := c) (next := w)
          (ps := ps) (C := B ++ placed) (D := ([] : List Operand))
          (by rw [hstk]; simp)
          (by simp only [List.length_nil] at hidx ⊢; omega)
          (by simp)
      simp only [List.length_nil, Nat.zero_add, List.nil_append] at hstep
      simp only [hstep]
      have hih := ih (placed ++ [c]) (i + 1)
        ({ ps with stack := (B ++ placed) ++ c :: [w] } : PlanState)
        (ops0 ++ [StackOp.SOSwap 1])
        (by simp)
        (by simp only [List.length_nil] at hidx ⊢; omega)
        (by simp)
      rw [hih]
      simp only [Prod.mk.injEq]
      refine ⟨by simp [descSwaps], by simp⟩
    | cons c2 cs' =>
      have hstep : reorderOne () tgt i c ps
          = ([StackOp.SOSwap ((cs' ++ [w]).length + 1)],
             { ps with stack := (B ++ placed) ++ c :: ((cs' ++ [w]) ++ [c2]) }) := by
        exact reorderOne_seat_hoist (tgt := tgt) (i := i) (cur := c) (next := c2)
          (ps := ps) (C := B ++ placed) (D := cs' ++ [w])
          (by rw [hstk]; simp)
          (by simp only [List.length_cons, List.length_append, List.length_nil] at hidx ⊢; omega)
          (by simp only [List.length_cons, List.length_append, List.length_nil] at h16 ⊢; omega)
      simp only [hstep]
      have hih := ih (placed ++ [c]) (i + 1)
        ({ ps with stack := (B ++ placed) ++ c :: ((cs' ++ [w]) ++ [c2]) } : PlanState)
        (ops0 ++ [StackOp.SOSwap ((cs' ++ [w]).length + 1)])
        (by simp)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hidx ⊢; omega)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at h16 ⊢; omega)
      rw [hih]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by simp⟩
      show (ops0 ++ [StackOp.SOSwap ((cs' ++ [w]).length + 1)]) ++ descSwaps (c2 :: cs').length
          = ops0 ++ descSwaps (c :: c2 :: cs').length
      rw [List.append_assoc]
      congr 1
      show StackOp.SOSwap ((cs' ++ [w]).length + 1) :: descSwaps (c2 :: cs').length
          = descSwaps (c :: c2 :: cs').length
      simp only [List.length_append, List.length_cons, List.length_nil, descSwaps]

/-- **The last-operand-spilled N-ary reorder** (`q = 0`): on the one-double emission layout
    `base ++ pre ++ [v, v]` with target `pre ++ [v]`, `reorderPlan` synthesises exactly the
    descending run `SWAP N; …; SWAP 1` and lands at the uniformly positioned
    `base ++ [v] ++ target` — the arbitrary-arity generalization of the proven ternop x-spilled
    atom (park-and-seat opener + seat-and-hoist chain). -/
theorem reorderPlan_lastspilled (base : List Operand) (pre : List Operand) (v : Operand)
    (ps : PlanState)
    (hstack : ps.stack = base ++ pre ++ [v, v])
    (hne : pre ≠ [])
    (h16 : pre.length + 1 ≤ 16)
    (habs : v ∉ pre) (hnd : pre.Nodup) :
    reorderPlan (pre ++ [v]) ps
      = (descSwaps (pre.length + 1), { ps with stack := base ++ v :: (pre ++ [v]) }) := by
  obtain ⟨p0, pre', rfl⟩ : ∃ p0 pre', pre = p0 :: pre' := by
    cases pre with
    | nil => exact absurd rfl hne
    | cons a l => exact ⟨a, l, rfl⟩
  simp only [List.length_cons] at h16
  obtain ⟨hvp0, hvpre'⟩ : v ≠ p0 ∧ v ∉ pre' := by
    simp only [List.mem_cons] at habs
    push Not at habs
    exact habs
  obtain ⟨hp0pre', hndpre'⟩ := List.nodup_cons.mp hnd
  unfold reorderPlan
  show (List.map (fun p => (p.2, p.1)) (((p0 :: pre') ++ [v]).zipIdx 0)).foldl _ ([], ps) = _
  rw [List.foldl_map]
  show (((p0 :: pre') ++ [v]).zipIdx 0).foldl
      (fun acc x => (acc.1 ++ (reorderOne () ((p0 :: pre') ++ [v]) x.2 x.1 acc.2).1,
        (reorderOne () ((p0 :: pre') ++ [v]) x.2 x.1 acc.2).2)) ([], ps) = _
  rw [show ((p0 :: pre') ++ [v]) = p0 :: (pre' ++ [v]) from rfl, List.zipIdx_cons,
      List.foldl_cons]
  cases pre' with
  | nil =>
    have hopener : reorderOne () (p0 :: ([] ++ [v])) 0 p0 ps
        = ([StackOp.SOSwap 2, StackOp.SOSwap 1],
           { ps with stack := (base ++ [v]) ++ p0 :: ([] ++ [v]) }) := by
      have h := reorderOne_park_seat (tgt := p0 :: ([] ++ [v])) (i := 0)
        (cur := p0) (next := v) (t := v) (ps := ps) (C := base) (D := [])
        (by rw [hstack]; simp)
        (by intro hmem
            simp only [List.mem_cons, List.nil_append, List.not_mem_nil, or_false] at hmem
            rcases hmem with h | h <;> exact hvp0 h.symm)
        (by simp)
        (by simp)
      rw [h]
      simp
    simp only [List.nil_append] at hopener ⊢
    simp only [hopener, Nat.zero_add]
    have hchain := reorderFold_chain (p0 :: [v]) (base ++ [v]) v [] [p0] 1
      ({ ps with stack := (base ++ [v]) ++ p0 :: [v] } : PlanState)
      [StackOp.SOSwap 2, StackOp.SOSwap 1]
      (by simp)
      (by simp)
      (by simp)
    simp only [List.nil_append] at hchain
    rw [hchain]
    simp only [Prod.mk.injEq]
    refine ⟨by simp [descSwaps], by simp⟩
  | cons r pre'' =>
    have habsent : p0 ∉ r :: ((pre'' ++ [v]) ++ [v]) := by
      intro hmem
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · exact hp0pre' (h ▸ List.mem_cons_self)
      · rcases h with h | h
        · exact hp0pre' (List.mem_cons_of_mem r h)
        · exact hvp0 h.symm
      · exact hvp0 h.symm
    have hopener : reorderOne () (p0 :: ((r :: pre'') ++ [v])) 0 p0 ps
        = ([StackOp.SOSwap (pre''.length + 3), StackOp.SOSwap (pre''.length + 2)],
           { ps with stack := (base ++ [v]) ++ p0 :: ((pre'' ++ [v]) ++ [r]) }) := by
      have h := reorderOne_park_seat (tgt := p0 :: ((r :: pre'') ++ [v])) (i := 0)
        (cur := p0) (next := r) (t := v) (ps := ps) (C := base) (D := pre'' ++ [v])
        (by rw [hstack]; simp)
        habsent
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at h16 ⊢; omega)
      rw [h]
      simp only [Prod.mk.injEq]
      constructor
      · simp only [List.length_append, List.length_cons, List.length_nil]
      · simp
    simp only [hopener]
    have hchain := reorderFold_chain (p0 :: ((r :: pre'') ++ [v])) (base ++ [v]) v
      (r :: pre'') [p0] 1
      ({ ps with stack := (base ++ [v]) ++ p0 :: ((pre'' ++ [v]) ++ [r]) } : PlanState)
      [StackOp.SOSwap (pre''.length + 3), StackOp.SOSwap (pre''.length + 2)]
      (by simp)
      (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
      (by simp only [List.length_cons, List.length_append, List.length_nil] at h16 ⊢; omega)
    simp only [Nat.zero_add, List.nil_append]
    rw [hchain]
    simp only [Prod.mk.injEq]
    constructor
    · show ([StackOp.SOSwap (pre''.length + 3), StackOp.SOSwap (pre''.length + 2)]
          ++ descSwaps (r :: pre'').length)
        = descSwaps ((p0 :: r :: pre'').length + 1)
      simp only [List.length_cons]
      show [StackOp.SOSwap (pre''.length + 3), StackOp.SOSwap (pre''.length + 2)]
          ++ descSwaps (pre''.length + 1) = descSwaps (pre''.length + 1 + 1 + 1)
      rfl
    · simp

/-- Descending swap run from `lo + len - 1` down to `lo`. -/
def descRun (lo : Nat) : Nat → List StackOp
  | 0 => []
  | len + 1 => StackOp.SOSwap (lo + len) :: descRun lo len

/-- **The seat-and-hoist chain over a fixed tail** `t0 :: T'`: each hoisted element seats in one
    swap against the head of the shrinking arrangement; when `hs` is exhausted, `t0` sits at the
    TOS. Emits `descRun (T'.length + 1) hs.length`. The mid-spilled pre-phase; the `q = 0` chain
    is the `T' = []` shape (plus its seated terminal). -/
theorem reorderFold_chain_pre (tgt : List Operand) (B : List Operand) (t0 : Operand)
    (T' : List Operand) :
    ∀ (hs : List Operand) (placed : List Operand) (i : Nat) (ps : PlanState)
      (ops0 : List StackOp),
      (match hs with
       | [] => ps.stack = B ++ placed ++ (T' ++ [t0])
       | c :: cs => ps.stack = B ++ placed ++ ((cs ++ (t0 :: T')) ++ [c])) →
      i + hs.length + T'.length + 1 = tgt.length →
      hs.length + T'.length + 1 ≤ 16 →
      (hs.zipIdx i).foldl
          (fun acc x => (acc.1 ++ (reorderOne () tgt x.2 x.1 acc.2).1,
            (reorderOne () tgt x.2 x.1 acc.2).2)) (ops0, ps)
        = (ops0 ++ descRun (T'.length + 1) hs.length,
           { ps with stack := B ++ (placed ++ hs) ++ (T' ++ [t0]) }) := by
  intro hs
  induction hs with
  | nil =>
    intro placed i ps ops0 hstk _ _
    simp only at hstk
    show ([] : List (Operand × Nat)).foldl _ (ops0, ps) = _
    simp only [List.foldl_nil, Prod.mk.injEq]
    refine ⟨by simp [descRun], ?_⟩
    rw [show B ++ (placed ++ []) ++ (T' ++ [t0]) = B ++ placed ++ (T' ++ [t0]) from by simp,
        ← hstk]
  | cons c cs ih =>
    intro placed i ps ops0 hstk hidx h16
    simp only at hstk
    simp only [List.length_cons] at hidx h16
    show ((c :: cs).zipIdx i).foldl _ (ops0, ps) = _
    rw [List.zipIdx_cons, List.foldl_cons]
    cases cs with
    | nil =>
      have hstep := reorderOne_seat_hoist (tgt := tgt) (i := i) (cur := c) (next := t0)
        (ps := ps) (C := B ++ placed) (D := T')
        (by rw [hstk]; simp)
        (by simp only [List.length_nil, Nat.zero_add] at hidx ⊢; omega)
        (by simp only [List.length_nil, Nat.zero_add] at h16 ⊢; omega)
      simp only [hstep]
      have hih := ih (placed ++ [c]) (i + 1)
        ({ ps with stack := (B ++ placed) ++ c :: (T' ++ [t0]) } : PlanState)
        (ops0 ++ [StackOp.SOSwap (T'.length + 1)])
        (by simp)
        (by simp only [List.length_nil, Nat.zero_add] at hidx ⊢; omega)
        (by simp only [List.length_nil, Nat.zero_add] at h16 ⊢; omega)
      rw [hih]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by simp⟩
      show (ops0 ++ [StackOp.SOSwap (T'.length + 1)]) ++ descRun (T'.length + 1) [].length
          = ops0 ++ descRun (T'.length + 1) ([].length + 1)
      simp only [List.length_nil, descRun, List.append_assoc]
      rfl
    | cons c2 cs' =>
      have hstep := reorderOne_seat_hoist (tgt := tgt) (i := i) (cur := c) (next := c2)
        (ps := ps) (C := B ++ placed) (D := cs' ++ (t0 :: T'))
        (by rw [hstk]; simp)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hidx ⊢; omega)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at h16 ⊢; omega)
      simp only [hstep]
      have hih := ih (placed ++ [c]) (i + 1)
        ({ ps with stack := (B ++ placed) ++ c :: ((cs' ++ (t0 :: T')) ++ [c2]) } : PlanState)
        (ops0 ++ [StackOp.SOSwap ((cs' ++ (t0 :: T')).length + 1)])
        (by simp)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hidx ⊢; omega)
        (by simp only [List.length_cons, List.length_append, List.length_nil] at h16 ⊢; omega)
      rw [hih]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by simp⟩
      show (ops0 ++ [StackOp.SOSwap ((cs' ++ (t0 :: T')).length + 1)])
            ++ descRun (T'.length + 1) (c2 :: cs').length
          = ops0 ++ descRun (T'.length + 1) ((c2 :: cs').length + 1)
      have hops : StackOp.SOSwap ((cs' ++ (t0 :: T')).length + 1)
          = StackOp.SOSwap ((T'.length + 1) + (c2 :: cs').length) := by
        congr 1
        simp only [List.length_cons, List.length_append]
        omega
      rw [List.append_assoc, hops]
      rfl

/-- **The return step**: the operand parked at the bottom of the group returns to the TOS in one
    swap (its final distance is 0), sinking the current TOS to the bottom slot. -/
theorem reorderOne_return {tgt : List Operand} {i : Nat} {cur t : Operand} {ps : PlanState}
    {C M : List Operand}
    (htos : ps.stack = C ++ cur :: (M ++ [t]))
    (habsent : cur ∉ M ++ [t])
    (hfin : tgt.length - 1 - i = 0)
    (h16 : M.length + 1 ≤ 16) (hne : M.length + 1 ≠ 0) :
    reorderOne () tgt i cur ps
      = ([StackOp.SOSwap (M.length + 1)], { ps with stack := C ++ t :: (M ++ [cur]) }) := by
  have hdepth : stackGetDepth cur ps.stack = some (M.length + 1) := by
    rw [htos]
    simpa using stackGetDepth_middle (A := C) (op := cur) (B := M ++ [t]) habsent
  have hswap : doSwap (M.length + 1) ps
      = ([StackOp.SOSwap (M.length + 1)], { ps with stack := C ++ t :: (M ++ [cur]) }) := by
    unfold doSwap
    rw [if_neg hne, if_pos h16, htos, stackSwap_middle]
  have hds0 : doSwap (tgt.length - 1 - i)
        ({ ps with stack := C ++ t :: (M ++ [cur]) } : PlanState)
      = ([], { ps with stack := C ++ t :: (M ++ [cur]) }) := by
    rw [hfin, doSwap, if_pos rfl]
  have hne2 : ¬ (M.length + 1 = tgt.length - 1 - i) := by omega
  unfold reorderOne
  simp only [hdepth, if_neg hne2, hswap, hds0, List.nil_append, List.append_nil]

/-- **The seated run**: a segment of operands each already at its final depth folds to no ops.
    (The inner post-operands of the mid-spilled reorder.) -/
theorem reorderFold_seated_run (tgt : List Operand) (t : Operand) :
    ∀ (qs : List Operand) (P : List Operand) (i : Nat) (ps : PlanState) (ops0 : List StackOp),
      ps.stack = P ++ (qs ++ [t]) →
      (∀ x ∈ qs, x ∉ [t]) →
      qs.Nodup →
      i + qs.length + 1 = tgt.length →
      (qs.zipIdx i).foldl
          (fun acc x => (acc.1 ++ (reorderOne () tgt x.2 x.1 acc.2).1,
            (reorderOne () tgt x.2 x.1 acc.2).2)) (ops0, ps)
        = (ops0, ps) := by
  intro qs
  induction qs with
  | nil => intro P i ps ops0 _ _ _ _; simp
  | cons a qs' ih =>
    intro P i ps ops0 hstk habs hnd hidx
    simp only [List.length_cons] at hidx
    obtain ⟨hanotqs, hnd'⟩ := List.nodup_cons.mp hnd
    have hdepth : stackGetDepth a ps.stack = some (qs'.length + 1) := by
      rw [hstk, show P ++ ((a :: qs') ++ [t]) = (P) ++ a :: (qs' ++ [t]) from by simp]
      have hnot : a ∉ qs' ++ [t] := by
        intro h
        rcases List.mem_append.mp h with h | h
        · exact hanotqs h
        · exact habs a List.mem_cons_self h
      simpa using stackGetDepth_middle (A := P) (op := a) (B := qs' ++ [t]) hnot
    have hseated : reorderOne () tgt i a ps = ([], ps) := by
      refine reorderOne_seated hdepth ?_
      omega
    rw [List.zipIdx_cons, List.foldl_cons]
    simp only [hseated, List.append_nil]
    exact ih (P ++ [a]) (i + 1) ps ops0
      (by rw [hstk]; simp)
      (fun x hx => habs x (List.mem_cons_of_mem a hx))
      hnd'
      (by omega)

/-- **The mid-operand-spilled N-ary reorder** (`p, q ≥ 1`): on the one-double emission layout
    `base ++ pre ++ [v, v] ++ post`, `reorderPlan` synthesises exactly
    `SWAP N; …; SWAP q; SWAP N` and lands at the uniformly positioned `base ++ [v] ++ target` —
    the arbitrary-arity generalization of the proven ternop mid-spilled atom: park-and-seat
    opener, seat-and-hoist chain over the fixed `[v] ++ post'` tail, the equal-`v` swap, the
    seated post-run, and the parked operand's return. -/
theorem reorderPlan_midspilled (base : List Operand) (pre post : List Operand) (v : Operand)
    (ps : PlanState)
    (hstack : ps.stack = base ++ pre ++ [v, v] ++ post)
    (hpre : pre ≠ []) (hpost : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post) :
    reorderPlan (pre ++ [v] ++ post) ps
      = ((StackOp.SOSwap (pre.length + post.length + 1)
            :: StackOp.SOSwap (pre.length + post.length)
            :: descRun (post.length + 1) (pre.length - 1))
          ++ [StackOp.SOSwap post.length]
          ++ [StackOp.SOSwap (pre.length + post.length + 1)],
         { ps with stack := base ++ v :: (pre ++ [v] ++ post) }) := by
  obtain ⟨p0, pre', rfl⟩ : ∃ p0 pre', pre = p0 :: pre' := by
    cases pre with
    | nil => exact absurd rfl hpre
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨post', plast, rfl⟩ : ∃ post' plast, post = post' ++ [plast] := by
    rcases List.eq_nil_or_concat post with h | ⟨l, a, h⟩
    · exact absurd h hpost
    · exact ⟨l, a, by rw [h, List.concat_eq_append]⟩
  simp only [List.length_cons, List.length_append, List.length_nil] at h16
  obtain ⟨hvp0, hvpre'⟩ : v ≠ p0 ∧ v ∉ pre' := by
    simp only [List.mem_cons] at hvpre; push Not at hvpre; exact hvpre
  obtain ⟨hp0pre', hndpre'⟩ := List.nodup_cons.mp hndpre
  have hvpost' : v ∉ post' := fun h => hvpost (List.mem_append.mpr (Or.inl h))
  have hvplast : v ≠ plast := fun h => hvpost (by rw [h]; exact List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hp0post' : p0 ∉ post' := fun h =>
    hdisj p0 List.mem_cons_self (List.mem_append.mpr (Or.inl h))
  have hp0plast : p0 ≠ plast := fun h =>
    hdisj p0 List.mem_cons_self (by rw [h]; exact List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hplastpost' : plast ∉ post' := by
    intro h
    have h2 := hndpost
    rw [List.nodup_append] at h2
    exact h2.2.2 plast h plast (by simp) rfl
  unfold reorderPlan
  show (List.map (fun p => (p.2, p.1)) (((p0 :: pre') ++ [v] ++ (post' ++ [plast])).zipIdx 0)).foldl
      _ ([], ps) = _
  rw [List.foldl_map]
  show (((p0 :: pre') ++ [v] ++ (post' ++ [plast])).zipIdx 0).foldl
      (fun acc x => (acc.1 ++ (reorderOne () ((p0 :: pre') ++ [v] ++ (post' ++ [plast])) x.2 x.1 acc.2).1,
        (reorderOne () ((p0 :: pre') ++ [v] ++ (post' ++ [plast])) x.2 x.1 acc.2).2)) ([], ps) = _
  set tgt := (p0 :: pre') ++ [v] ++ (post' ++ [plast]) with htgt
  have htgtlen : tgt.length = pre'.length + post'.length + 3 := by
    rw [htgt]; simp; omega
  -- split the enum walk: p0 ; pre' ; v ; post' ; plast (keeping `tgt` abstract in the fold)
  have hz0 : tgt.zipIdx 0
      = (p0, 0) :: (pre'.zipIdx 1
          ++ ([v] ++ (post' ++ [plast])).zipIdx (1 + pre'.length)) := by
    rw [htgt]
    rw [show (p0 :: pre') ++ [v] ++ (post' ++ [plast])
          = p0 :: (pre' ++ ([v] ++ (post' ++ [plast]))) from by simp,
        List.zipIdx_cons, List.zipIdx_append]
  rw [hz0, List.foldl_cons, List.foldl_append]
  -- the opener: park plast, seat p0, hoist the seam element
  have hopener : reorderOne () tgt 0 p0 ps
      = ([StackOp.SOSwap (pre'.length + post'.length + 3),
          StackOp.SOSwap (pre'.length + post'.length + 2)],
         { ps with stack := (base ++ [plast]) ++ p0 ::
             ((pre' ++ (v :: v :: post')).tail ++ [(pre' ++ (v :: v :: post')).head (by cases pre' <;> simp)]) }) := by
    cases pre' with
    | nil =>
      have h := reorderOne_park_seat (tgt := tgt) (i := 0)
        (cur := p0) (next := v) (t := plast) (ps := ps) (C := base) (D := v :: post')
        (by rw [hstack]; simp)
        (by intro hmem
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
            have l1 : ¬ p0 = v := fun h => hvp0 h.symm
            have l2 : ¬ p0 = plast := hp0plast
            have l3 : ¬ p0 ∈ post' := hp0post'
            tauto)
        (by rw [htgtlen]; simp only [List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_cons, List.length_nil] at h16 ⊢; omega)
      rw [h]
      simp only [Prod.mk.injEq]
      constructor
      · simp only [List.length_cons, List.length_nil]
        have h1 : post'.length + 1 + 2 = 0 + post'.length + 3 := by omega
        have h2 : post'.length + 1 + 1 = 0 + post'.length + 2 := by omega
        rw [h1, h2]
      · simp
    | cons r pre'' =>
      have h := reorderOne_park_seat (tgt := tgt) (i := 0)
        (cur := p0) (next := r) (t := plast) (ps := ps)
        (C := base) (D := pre'' ++ (v :: v :: post'))
        (by rw [hstack]; simp)
        (by intro hmem
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
            have l1 : ¬ p0 = v := fun h => hvp0 h.symm
            have l2 : ¬ p0 = plast := hp0plast
            have l3 : ¬ p0 ∈ post' := hp0post'
            have l4 : ¬ p0 = r := fun h => hp0pre' (h ▸ List.mem_cons_self)
            have l5 : ¬ p0 ∈ pre'' := fun h => hp0pre' (List.mem_cons_of_mem r h)
            tauto)
        (by rw [htgtlen]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at h16 ⊢; omega)
      rw [h]
      simp only [Prod.mk.injEq]
      constructor
      · simp only [List.length_cons, List.length_append, List.length_nil]
        have h1 : pre''.length + (post'.length + 1 + 1) + 2
            = pre''.length + 1 + post'.length + 3 := by omega
        have h2 : pre''.length + (post'.length + 1 + 1) + 1
            = pre''.length + 1 + post'.length + 2 := by omega
        rw [h1, h2]
      · simp
  simp only [hopener, List.nil_append]
  have hchain := reorderFold_chain_pre tgt (base ++ [plast]) v (v :: post') pre' [p0] 1
    ({ ps with stack := (base ++ [plast]) ++ p0 ::
        ((pre' ++ (v :: v :: post')).tail ++ [(pre' ++ (v :: v :: post')).head (by cases pre' <;> simp)]) } : PlanState)
    [StackOp.SOSwap (pre'.length + post'.length + 3),
     StackOp.SOSwap (pre'.length + post'.length + 2)]
    (by cases pre' <;> simp)
    (by rw [htgtlen]; simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil] at h16 ⊢; omega)
  rw [hchain]
  -- the v-step (equal-v swap, stack unchanged)
  have hz1 : ([v] ++ (post' ++ [plast])).zipIdx (1 + pre'.length)
      = (v, 1 + pre'.length) :: (post'.zipIdx (1 + pre'.length + 1)
          ++ [(plast, 1 + pre'.length + 1 + post'.length)]) := by
    rw [show ([v] ++ (post' ++ [plast])) = v :: (post' ++ [plast]) from by simp,
        List.zipIdx_cons, List.zipIdx_append]
    simp [Nat.add_comm]
  rw [hz1, List.foldl_cons]
  have hvstep : reorderOne () tgt (1 + pre'.length) v
      ({ ps with stack := (base ++ [plast]) ++ ([p0] ++ pre') ++ ((v :: post') ++ [v]) } : PlanState)
      = ([StackOp.SOSwap (post'.length + 1)],
         { ps with stack := ((base ++ [plast]) ++ ([p0] ++ pre')) ++ v :: (post' ++ [v]) }) := by
    exact reorderOne_seat_hoist (tgt := tgt) (i := 1 + pre'.length) (cur := v) (next := v)
      (C := (base ++ [plast]) ++ ([p0] ++ pre')) (D := post')
      (by simp)
      (by rw [htgtlen]; omega)
      (by omega)
  simp only [hvstep]
  -- the seated post-run
  rw [List.foldl_append]
  have hrun := reorderFold_seated_run tgt v post'
    (((base ++ [plast]) ++ ([p0] ++ pre')) ++ [v]) (1 + pre'.length + 1)
    ({ ps with stack := ((base ++ [plast]) ++ ([p0] ++ pre')) ++ v :: (post' ++ [v]) } : PlanState)
    (([StackOp.SOSwap (pre'.length + post'.length + 3),
        StackOp.SOSwap (pre'.length + post'.length + 2)]
      ++ descRun ((v :: post').length + 1) pre'.length)
      ++ [StackOp.SOSwap (post'.length + 1)])
    (by simp)
    (by intro x hx hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact hvpost' (hmem ▸ hx))
    ((List.nodup_append.mp hndpost).1)
    (by rw [htgtlen]; omega)
  rw [hrun]
  -- the return: the parked plast comes home, v sinks to the bottom slot
  rw [List.foldl_cons, List.foldl_nil]
  have hplastpre : plast ∉ p0 :: pre' := fun h =>
    hdisj plast h (List.mem_append.mpr (Or.inr List.mem_cons_self))
  have hreturn : reorderOne () tgt (1 + pre'.length + 1 + post'.length) plast
      ({ ps with stack := ((base ++ [plast]) ++ ([p0] ++ pre')) ++ v :: (post' ++ [v]) } : PlanState)
      = ([StackOp.SOSwap (((p0 :: pre') ++ [v] ++ post').length + 1)],
         { ps with stack := base ++ v :: (((p0 :: pre') ++ [v] ++ post') ++ [plast]) }) := by
    exact reorderOne_return (tgt := tgt) (i := 1 + pre'.length + 1 + post'.length)
      (cur := plast) (t := v) (C := base) (M := (p0 :: pre') ++ [v] ++ post')
      (by show ((base ++ [plast]) ++ ([p0] ++ pre')) ++ v :: (post' ++ [v])
            = base ++ plast :: (((p0 :: pre') ++ [v] ++ post') ++ [v])
          simp)
      (by intro hmem
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
          have l1 : ¬ plast = p0 := fun h => hplastpre (h ▸ List.mem_cons_self)
          have l2 : ¬ plast ∈ pre' := fun h => hplastpre (List.mem_cons_of_mem p0 h)
          have l3 : ¬ plast = v := fun h => hvplast h.symm
          have l4 : ¬ plast ∈ post' := hplastpost'
          tauto)
      (by rw [htgtlen]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at h16 ⊢; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  simp only [hreturn]
  -- assemble
  simp only [Prod.mk.injEq]
  constructor
  · show ((([StackOp.SOSwap (pre'.length + post'.length + 3),
        StackOp.SOSwap (pre'.length + post'.length + 2)]
        ++ descRun ((v :: post').length + 1) pre'.length)
        ++ [StackOp.SOSwap (post'.length + 1)]))
        ++ [StackOp.SOSwap (((p0 :: pre') ++ [v] ++ post').length + 1)]
      = _
    simp only [List.append_nil, List.append_assoc, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add]
    rw [show pre'.length + 1 + (post'.length + 1) + 1 = pre'.length + post'.length + 3 from by
          omega,
        show pre'.length + 1 + (post'.length + 1) = pre'.length + post'.length + 2 from by
          omega,
        show pre'.length + 1 - 1 = pre'.length from by omega,
        show pre'.length + 1 + (1 + post'.length) + 1 = pre'.length + post'.length + 3 from by
          omega]
    rfl
  · rw [htgt]
    simp
/-- On a `Nodup` list, `stackFind (· == x)` returns exactly the index where `x` sits (no earlier
    match, since nodup forbids duplicates). -/
theorem stackFind_eq_some_of_nodup : ∀ {L : List Operand} {j : Nat} {x : Operand},
    L.Nodup → L[j]? = some x → stackFind (· == x) L = some j := by
  intro L
  induction L with
  | nil => intro j x _ hj; simp at hj
  | cons a as ih =>
    intro j x hnd hj
    rw [stackFind]
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hj
      have hax : a = x := Option.some.inj hj
      subst hax
      simp
    | succ j' =>
      rw [List.getElem?_cons_succ] at hj
      have hmem : x ∈ as := List.mem_of_getElem? hj
      have hne : a ≠ x := by rintro rfl; exact (List.nodup_cons.mp hnd).1 hmem
      have hax : (a == x) = false := by simpa using hne
      simp only [hax, Bool.false_eq_true, if_false]
      rw [ih (List.nodup_cons.mp hnd).2 hj]

/-- A `Nodup` list is positioned as itself: its `i`-th element sits at depth `length-1-i`. -/
theorem stackGetDepth_self_nodup {L : List Operand} (hnd : L.Nodup) {i : Nat} (hi : i < L.length) :
    stackGetDepth (L[i]'hi) L = some (L.length - 1 - i) := by
  unfold stackGetDepth
  have hlt : L.length - 1 - i < L.length := by omega
  have hidx : L.reverse[L.length - 1 - i]? = some (L[i]'hi) := by
    rw [List.getElem?_reverse hlt, show L.length - 1 - (L.length - 1 - i) = i from by omega]
    exact List.getElem?_eq_getElem hi
  exact stackFind_eq_some_of_nodup (List.nodup_reverse.mpr hnd) hidx

/-- **`reorderPlan` is a no-op on an already-positioned `Nodup` stack** (`ps.stack = L`, `L` nodup):
    every operand is at its own target depth, so no swap is emitted. The general well-scheduled-join
    no-op; generalises `reorderPlan_pair_var_nil` / `reorderPlan_triple_var_nil` from fixed arity. -/
theorem reorderPlan_self_nil (L : List Operand) (ps : PlanState)
    (hstack : ps.stack = L) (hnd : L.Nodup) :
    reorderPlan L ps = ([], ps) := by
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  rw [hstack]
  obtain ⟨hlt0, hget⟩ := List.mem_enum hp
  rw [hget]
  exact stackGetDepth_self_nodup hnd hlt0

/-- `stackFind` stops at the first match, so a hit in the left part is unaffected by the right. -/
theorem stackFind_append_left {p : Operand → Bool} {l1 l2 : List Operand} {j : Nat}
    (h : stackFind p l1 = some j) : stackFind p (l1 ++ l2) = some j := by
  induction l1 generalizing j with
  | nil => simp [stackFind] at h
  | cons a as ih =>
    rw [List.cons_append, stackFind]
    rw [stackFind] at h
    by_cases hpa : p a
    · rw [if_pos hpa] at h ⊢; exact h
    · rw [if_neg hpa] at h ⊢
      cases hf : stackFind p as with
      | none => rw [hf] at h; simp at h
      | some d => rw [hf] at h; rw [ih hf]; exact h

/-- A `Nodup` operand list sitting on top of any `base` is positioned as itself: its `i`-th element is
    at depth `L.length - 1 - i`, independent of `base` (the fresh top occurrence is found first). The
    base-aware generalisation of `stackGetDepth_self_nodup`. -/
theorem stackGetDepth_append_top_self {base L : List Operand} (hnd : L.Nodup) {i : Nat} (hi : i < L.length) :
    stackGetDepth (L[i]'hi) (base ++ L) = some (L.length - 1 - i) := by
  unfold stackGetDepth
  rw [List.reverse_append]
  apply stackFind_append_left
  have hlt : L.length - 1 - i < L.length := by omega
  have hidx : L.reverse[L.length - 1 - i]? = some (L[i]'hi) := by
    rw [List.getElem?_reverse hlt, show L.length - 1 - (L.length - 1 - i) = i from by omega]
    exact List.getElem?_eq_getElem hi
  exact stackFind_eq_some_of_nodup (List.nodup_reverse.mpr hnd) hidx

/-- **`reorderPlan` is a no-op on freshly-emitted distinct vars over any `base`.** The base-aware
    N-input generalisation of `reorderPlan_pair_var_nil`/`reorderPlan_triple_var_nil`: after emitting
    the distinct `ws` onto `base`, each is already at its target depth. Discharges the reorder step for
    an arbitrary-arity all-variable op (e.g. LOG). -/
theorem reorderPlan_allVars_nil (base : List Operand) (ws : List String) (ps : PlanState)
    (hstack : ps.stack = base ++ ws.map Operand.Var) (hnd : ws.Nodup) :
    reorderPlan (ws.map Operand.Var) ps = ([], ps) := by
  have hndm : (ws.map Operand.Var).Nodup := hnd.map (fun _ _ h => Operand.Var.inj h)
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  rw [hstack]
  obtain ⟨hlt0, hget⟩ := List.mem_enum hp
  rw [hget]
  exact stackGetDepth_append_top_self hndm hlt0

/-- The well-scheduled JMP join: `reorderPlan (S.map Var)` is a no-op when the body already laid the
    stack out as the target's entry layout `S.map Var` (`S` nodup — distinct SSA vars). This is the
    post-body plan stack = target entry layout reconciliation for the no-reorder case; the general case
    needs `reorderPlan` to *synthesise* the layout from any permutation (the `perm_reaches` work). -/
theorem reorderPlan_vars_nil (S : List String) (ps : PlanState)
    (hstack : ps.stack = S.map Operand.Var) (hnd : S.Nodup) :
    reorderPlan (S.map Operand.Var) ps = ([], ps) :=
  reorderPlan_self_nil (S.map Operand.Var) ps hstack
    (List.Nodup.map (fun _ _ h => Operand.Var.inj h) hnd)

/-! ## JMP terminator codegen decomposition (well-scheduled join)

Wiring `reorderPlan_vars_nil` into `generateRegularInstPlan`'s JMP path. For a JMP, the input
operands are empty (`computeOperands` filters the label out), the join reorders the stack to the
target's entry layout (a no-op when the body already produced it), the emit is `[push-label ; JUMP]`,
and there are no outputs — so the plan collapses to `[SOPushLabel target, SOEmit "JUMP"]` over the
dead-spill release, leaving the plan stack at the target layout. -/

/-- `computeOperands` of a JMP is empty (the `Label` is filtered out by `getNonLabelOperands`). -/
theorem computeOperands_jmp {inst : Instruction} {target : String}
    (hjmp : inst.opcode = Opcode.JMP) (hops : inst.operands = [Operand.Label target]) :
    computeOperands inst = [] := by
  simp [computeOperands, getNonLabelOperands, hjmp, hops, isLabelOperand]

/-- Emitting one input over an empty operand list is a no-op. -/
theorem emitInputPlan_nil (opc : Opcode) (nl : List String) (ps : PlanState) :
    emitInputPlan opc [] nl ps = ([], ps) := by unfold emitInputPlan; rfl

/-- `reorderPlan` of an empty target list is a no-op. -/
theorem reorderPlan_empty (ps : PlanState) : reorderPlan [] ps = ([], ps) := by
  unfold reorderPlan; rfl

/-- `stackPop 0` is the identity. -/
theorem stackPop_zero (stk : List Operand) : stackPop 0 stk = stk := by
  unfold stackPop; simp

/-- `generateEmitOps` of a JMP is `[push-label target ; JUMP]` (its `opcodeToEvmName` is `none`). -/
theorem generateEmitOps_jmp {inst : Instruction} {target : String} {ps : PlanState} {n : Nat}
    (hjmp : inst.opcode = Opcode.JMP) (hops : inst.operands = [Operand.Label target]) :
    generateEmitOps inst n ps
      = ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], ps) := by
  unfold generateEmitOps
  rw [hjmp, hops]; rfl

/-- **JMP terminator-step is PlanState-identity** when the successor consumes no stack inputs
    (`inputVarsFrom = []`, so the join-reorder `reorderPlan targetStack` is empty) and there are no
    live spills (`ps.spilled = []`, so `releaseDeadSpills` is the identity). Every intermediate stage
    threads `ps` unchanged: `emitInputPlan [] = id` (JMP has no Var operands, `computeOperands_jmp`),
    the join-reorder is `reorderPlan [] = id`, the commutative branch's plan state is `ps` regardless,
    `reorderPlan [] = id`, `stackPop 0 = id`, no outputs, `generateEmitOps` leaves `ps`, and
    `releaseDeadSpills` is the identity.

    With the plan-representation spine (`generateBlockPlan_split_term`, giving
    `ps' = term-step ps_body`) and `psOfFn_entry_succ` (`psOf successor = ps'`), this discharges the
    per-block `hstep` residual (`hstk/hsp/hfe/hno`) for such JMP blocks: `psOf successor = ps_body`,
    the body-fold output — reducing the residual to the body-fold representation reconciliation. -/
theorem generateRegularInstPlan_jmp_id
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {target : String} {nextLive : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom curBb targetBb.instructions (liveVarsAt L target 0) = [])
    (hsp : ps.spilled = ([] : AssocList Operand Nat)) :
    (generateRegularInstPlan L D C fn inst nextLive isH nextT curBb ps).2 = ps := by
  have hc : (isCommutative Opcode.JMP && decide ((0:Nat) ≥ 2)) = false := by decide
  unfold generateRegularInstPlan
  rw [computeOperands_jmp hjmp hops]
  rcases hf : fn.blocks.find? (fun x => x.label == target) with _ | targetBb
  · simp only [hjmp, hops, houts, emitInputPlan_nil, hf, reorderPlan_empty, hc,
      List.length_nil, if_true, Bool.false_eq_true, if_false, stackPop_zero,
      List.foldl_nil, List.isEmpty_nil, generateEmitOps_jmp hjmp hops,
      releaseDeadSpills_empty nextLive ps hsp]
  · simp only [hjmp, hops, houts, emitInputPlan_nil, hf, hjoin targetBb hf, List.map_nil,
      reorderPlan_empty, hc, List.length_nil, if_true, Bool.false_eq_true, if_false,
      stackPop_zero, List.foldl_nil, List.isEmpty_nil, generateEmitOps_jmp hjmp hops,
      releaseDeadSpills_empty nextLive ps hsp]

/-- **Full aligned-JMP terminator-step characterization.** For an aligned JMP (successor with no stack
    inputs, no live spills), the plan step is exactly `([SOPushLabel target, SOEmit "JUMP"], ps)` — the
    ops-side (foundation for the asm-layout `hpush`/`hjump`) strengthening `generateRegularInstPlan_jmp_id`
    (which gave only the `ps`-identity). -/
theorem generateRegularInstPlan_jmp_full
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {target : String} {nextLive : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom curBb targetBb.instructions (liveVarsAt L target 0) = [])
    (hsp : ps.spilled = ([] : AssocList Operand Nat)) :
    generateRegularInstPlan L D C fn inst nextLive isH nextT curBb ps
      = ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], ps) := by
  have hc : (isCommutative Opcode.JMP && decide ((0:Nat) ≥ 2)) = false := by decide
  unfold generateRegularInstPlan
  rw [computeOperands_jmp hjmp hops]
  rcases hf : fn.blocks.find? (fun x => x.label == target) with _ | targetBb
  · simp only [hjmp, hops, houts, emitInputPlan_nil, hf, reorderPlan_empty, hc,
      List.length_nil, if_true, Bool.false_eq_true, if_false, stackPop_zero,
      List.foldl_nil, List.isEmpty_nil, generateEmitOps_jmp hjmp hops,
      releaseDeadSpills_empty nextLive ps hsp, List.nil_append, List.append_nil]
  · simp only [hjmp, hops, houts, emitInputPlan_nil, hf, hjoin targetBb hf, List.map_nil,
      reorderPlan_empty, hc, List.length_nil, if_true, Bool.false_eq_true, if_false,
      stackPop_zero, List.foldl_nil, List.isEmpty_nil, generateEmitOps_jmp hjmp hops,
      releaseDeadSpills_empty nextLive ps hsp, List.nil_append, List.append_nil]

/-- `computeOperands` of an operand-free instruction is `[]` (all three branches — `getNonLabelOperands`,
    `.tail.reverse`, `.reverse` — collapse on the empty operand list). -/
theorem computeOperands_nil {inst : Instruction} (hops : inst.operands = []) :
    computeOperands inst = [] := by
  unfold computeOperands getNonLabelOperands
  rw [hops]; simp

/-- **Full bare-halting-terminator plan characterization.** For a terminal op with no operands, no
    outputs, and a single EVM name (`STOP`/`INVALID` — `opcodeToEvmName = some name`), and no live spills,
    the plan step is exactly `([SOEmit name], ps)`: every stage threads `ps` unchanged (`emitInputPlan [] = id`,
    no join since not JMP, the commutative branch is skipped on the empty operand list, `reorderPlan [] = id`,
    `stackPop 0 = id`, no outputs, `generateEmitOps` leaves `ps`, `releaseDeadSpills` identity). The bare-op
    analogue of `generateRegularInstPlan_jmp_full` — foundation for the aligned STOP/INVALID asm layout. -/
theorem generateRegularInstPlan_bareHalt_full
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {name : String} {nextLive : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hops : inst.operands = [])
    (houts : inst.outputs = [])
    (hsp : ps.spilled = ([] : AssocList Operand Nat)) :
    generateRegularInstPlan L D C fn inst nextLive isH nextT curBb ps
      = ([StackOp.SOEmit name], ps) := by
  unfold generateRegularInstPlan
  rw [computeOperands_nil hops]
  simp [hops, houts, emitInputPlan_nil, reorderPlan_empty,
    stackPop_zero, generateEmitOps_evmName hname, releaseDeadSpills_empty nextLive ps hsp]

/-- **Aligned two-operand-terminal plan ops = emit ++ `[SOEmit name]`** (RETURN/REVERT). The operand-
    terminal analogue of `generateRegularInstPlan_bareHalt_full`: for a terminator with a single EVM name
    (`opcodeToEvmName = some name`), two operands `[off, sz]` (computed as `[sz, off]` = `computeOperands`,
    given `hco`), no outputs, non-commutative, and the join-reorder already positioned after emission
    (`hreorderNil` — the alignment condition, discharged separately as `generateBlockPlan_aligned_jmp` took
    `hjoin`), the plan *ops* are exactly the operand emission followed by `[SOEmit name]` (no reorder). We
    characterize only `.1` (the ops) — enough for the layout `hblock`/`hget`; the terminal `ps'` is
    irrelevant since RETURN/REVERT halt (the OK-not-halted branch is vacuous). -/
theorem generateRegularInstPlan_return_full
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {name : String} {offv szv : String} {nextLive : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hco : computeOperands inst = [Operand.Var szv, Operand.Var offv])
    (houts : inst.outputs = [])
    (hreorderNil : (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan inst.opcode [Operand.Var szv, Operand.Var offv] nextLive ps).2).1 = []) :
    (generateRegularInstPlan L D C fn inst nextLive isH nextT curBb ps).1
      = (emitInputPlan inst.opcode [Operand.Var szv, Operand.Var offv] nextLive ps).1
        ++ [StackOp.SOEmit name] := by
  unfold generateRegularInstPlan
  rw [hco]
  simp [if_neg hnjmp, hncomm, houts, generateEmitOps_evmName hname, hreorderNil]

/-- `generateEmitOps` for a JNZ emits `[push ifNz; JUMPI; push ifZ; JUMP]` (`opcodeToEvmName JNZ = none`,
    then the JNZ branch with the two label operands). -/
theorem generateEmitOps_jnz {inst : Instruction} {c ifNz ifZ : String} {ps : PlanState} {n : Nat}
    (hjnz : inst.opcode = Opcode.JNZ)
    (hops : inst.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ]) :
    generateEmitOps inst n ps
      = ([StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
          StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"], ps) := by
  unfold generateEmitOps
  rw [hjnz, hops]; rfl

/-- **Full aligned-JNZ plan characterization.** For a JNZ `[cond, ifNz, ifZ]` whose condition is emitted
    as a single `DUP1` (`hemit` — the live condition sits at the plan-stack top) with the join-reorder then
    positioned (`hreorder`), the plan *ops* are `[DUP1, push ifNz, JUMPI, push ifZ, JUMP]` — the 5-op tail
    the `hstep_regularHSVP_jnz_{taken,nottaken}` layout reads. Alignment (`hemit`/`hreorder`) is discharged
    separately, as `generateBlockPlan_aligned_jmp` took `hjoin`. Only `.1` (ops); terminal `ps'` unused
    (JNZ continues, but the successor `psOf` comes from the DFS, not this plan). -/
theorem generateRegularInstPlan_jnz_full
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {c ifNz ifZ : String} {nl : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hjnz : inst.opcode = Opcode.JNZ)
    (hops : inst.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (houts : inst.outputs = [])
    (hemit : (emitInputPlan Opcode.JNZ [Operand.Var c] nl ps).1 = [StackOp.SODup 1])
    (hreorder : (reorderPlan [Operand.Var c]
        (emitInputPlan Opcode.JNZ [Operand.Var c] nl ps).2).1 = []) :
    (generateRegularInstPlan L D C fn inst nl isH nextT curBb ps).1
      = [StackOp.SODup 1, StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
         StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"] := by
  have hco : computeOperands inst = [Operand.Var c] := by
    unfold computeOperands getNonLabelOperands; rw [hjnz, hops]; simp [isLabelOperand]
  unfold generateRegularInstPlan
  rw [hco]
  simp [houts, hjnz, hemit, hreorder, generateEmitOps_jnz hjnz hops]

/-- **`stackPop 1 (stackDup 0 s) = s`.** Duplicating the TOS then popping one recovers the original stack —
    the net stack effect of a JNZ terminator's condition-DUP followed by the `JUMPI` operand pop. -/
theorem stackPop_stackDup_zero (s : List Operand) : stackPop 1 (stackDup 0 s) = s := by
  unfold stackPop stackDup
  simp [List.length_append]

/-- **JNZ terminator-step is PlanState-identity for an aligned block.** When the live condition sits at
    the plan-stack top so its emission is a single `DUP1` (`hemit` — leaving `ps` with the TOS duplicated),
    the join-reorder is positioned (`hreorder`, no state change), and there are no live spills
    (`hsp`, so `releaseDeadSpills` is the identity), every stage threads `ps` unchanged: the DUP+`stackPop 1`
    cancel (`stackPop_stackDup_zero`), no outputs, `generateEmitOps` leaves `ps`. The JNZ analogue of
    `generateRegularInstPlan_jmp_id` — the plan-effect fact a JNZ scheduling-residual discharge needs
    (`(lg.foldl gp).2 = psOf successor`), alongside a JNZ two-successor DFS recording. -/
theorem generateRegularInstPlan_jnz_id
    {L : DfState (List String)} {D : DfgAnalysis} {C : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {c ifNz ifZ : String} {nl : List String}
    {isH nextT : Bool} {curBb : String} {ps : PlanState}
    (hjnz : inst.opcode = Opcode.JNZ)
    (hops : inst.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (houts : inst.outputs = [])
    (hemit : emitInputPlan Opcode.JNZ [Operand.Var c] nl ps
        = ([StackOp.SODup 1], { ps with stack := stackDup 0 ps.stack }))
    (hreorder : reorderPlan [Operand.Var c] { ps with stack := stackDup 0 ps.stack }
        = ([], { ps with stack := stackDup 0 ps.stack }))
    (hsp : ps.spilled = ([] : AssocList Operand Nat)) :
    (generateRegularInstPlan L D C fn inst nl isH nextT curBb ps).2 = ps := by
  have hco : computeOperands inst = [Operand.Var c] := by
    unfold computeOperands getNonLabelOperands; rw [hjnz, hops]; simp [isLabelOperand]
  unfold generateRegularInstPlan
  rw [hco]
  simp only [hjnz, hemit, hreorder, houts, generateEmitOps_jnz hjnz hops, List.length_singleton,
    stackPop_stackDup_zero, show isCommutative Opcode.JNZ = false from rfl, Bool.false_and,
    List.foldl_nil, List.isEmpty_nil, reduceCtorEq, reduceIte, if_false, if_true,
    List.append_nil, List.nil_append]
  exact releaseDeadSpills_empty nl _ hsp

/-- **`executePlan` is label-free when no stack-op is a label push.** `execStackOp` produces an
    `AsmPushLabel`/`AsmPushOfst` only from `SOPushLabel`/`SOPushOfst`/`SOPush (Operand.Label _)`; every
    other stack op yields `AsmPush`/`AsmOp`/`AsmLabel`/`POP`. So a plan free of those three label-push ops
    compiles to asm with no label pushes — the hypothesis `asmBlockAt_resolved_of_middle_no_label` needs
    for the operand-emission segment of a RETURN/REVERT block. -/
theorem executePlan_no_label (ops : List StackOp)
    (h : ∀ so ∈ ops, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l))) :
    ∀ a ∈ executePlan ops, (∀ l, a ≠ AsmInst.AsmPushLabel l) ∧ (∀ l d, a ≠ AsmInst.AsmPushOfst l d) := by
  intro a ha
  have ha' : a ∈ ops.flatMap execStackOp := ha
  rw [List.mem_flatMap] at ha'
  obtain ⟨so, hso, hain⟩ := ha'
  obtain ⟨hnpl, hnpo, hnplit⟩ := h so hso
  cases so with
  | SOPush op =>
    cases op with
    | Lit v => simp [execStackOp] at hain; subst hain; exact ⟨by simp, by simp⟩
    | Var v => simp [execStackOp] at hain
    | Label l => exact absurd rfl (hnplit l)
  | SOPushLabel l => exact absurd rfl (hnpl l)
  | SOPushOfst l d => exact absurd rfl (hnpo l d)
  | SOPop n =>
    simp only [execStackOp, List.mem_replicate] at hain
    rw [hain.2]; exact ⟨by simp, by simp⟩
  | SOSwap n => simp [execStackOp] at hain; subst hain; exact ⟨by simp, by simp⟩
  | SODup n => simp [execStackOp] at hain; subst hain; exact ⟨by simp, by simp⟩
  | SOPoke a b => simp [execStackOp] at hain
  | SOSpill off => simp [execStackOp] at hain; rcases hain with h | h <;> subst h <;> exact ⟨by simp, by simp⟩
  | SORestore off => simp [execStackOp] at hain; rcases hain with h | h <;> subst h <;> exact ⟨by simp, by simp⟩
  | SOEmit opc => simp [execStackOp] at hain; subst hain; exact ⟨by simp, by simp⟩
  | SOLabel lbl => simp [execStackOp] at hain; subst hain; exact ⟨by simp, by simp⟩

/-- The spill fold of `doDup`/`doSwap`'s bulk branch appends only `SOSpill` ops, so every produced op is
    label-push-free (helper for `doDup_no_label`). -/
theorem spillFold_no_label :
    ∀ (items : List Operand) (acc : List StackOp × List Nat × SpillAlloc),
    (∀ so ∈ acc.1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l))) →
    ∀ so ∈ (items.foldl (fun (x : List StackOp × List Nat × SpillAlloc) (item : Operand) =>
        let (off, al') := allocSpillSlot x.2.2
        (x.1 ++ [StackOp.SOSpill off], x.2.1 ++ [off], al')) acc).1,
      (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
        ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro items
  induction items with
  | nil => intro acc hacc so hso; exact hacc so hso
  | cons hd tl ih =>
    intro acc hacc so hso
    rw [List.foldl_cons] at hso
    refine ih _ ?_ so hso
    intro so' hso'
    rw [List.mem_append] at hso'
    rcases hso' with h | h
    · exact hacc so' h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨by simp, by simp, by simp⟩

/-- **`doDup` produces no label-push stack-op.** Both branches emit only `SODup`/`SOSpill`/`SORestore`. -/
theorem doDup_no_label (dist : Nat) (ps : PlanState) :
    ∀ so ∈ (doDup dist ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  unfold doDup at hso
  split at hso
  · simp only [List.mem_singleton] at hso; subst hso; exact ⟨by simp, by simp, by simp⟩
  · simp only [List.mem_append] at hso
    rcases hso with h | h
    · exact spillFold_no_label _ ([], [], ps.alloc) (by simp) so h
    · rw [List.mem_map] at h; obtain ⟨idx, _, rfl⟩ := h; exact ⟨by simp, by simp, by simp⟩

/-- **`doRestore` produces no label-push stack-op** (`[]` or `[SORestore off]`). -/
theorem doRestore_no_label (op : Operand) (ps : PlanState) :
    ∀ so ∈ (doRestore op ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  unfold doRestore at hso
  split at hso
  · simp at hso
  · simp only [List.mem_singleton] at hso; subst hso; exact ⟨by simp, by simp, by simp⟩

/-- **`emitOneInput` of a non-label operand produces no label-push stack-op.** For a `Var`/`Lit` operand,
    the emission is `restoreOps ++ (SOPush(Lit) | doDup)` — all `SORestore`/`SODup`/`SOSpill`/`SOPush(Lit)`,
    never a label push (only `Operand.Label` emits `SOPushLabel`). -/
theorem emitOneInput_no_label (opc : Opcode) (nl : List String) (op : Operand)
    (hop : ∀ l, op ≠ Operand.Label l) (ps : PlanState) :
    ∀ so ∈ (emitOneInput opc nl op ps).1, (∀ l, so ≠ StackOp.SOPushLabel l)
      ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d) ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  have hrestore : ∀ so' ∈ (if isVarOperand op && (alookup' ps.spilled op).isSome
      then doRestore op ps else ([], ps)).1, (∀ l, so' ≠ StackOp.SOPushLabel l)
      ∧ (∀ l d, so' ≠ StackOp.SOPushOfst l d) ∧ (∀ l, so' ≠ StackOp.SOPush (Operand.Label l)) := by
    intro so' hso'; split at hso'
    · exact doRestore_no_label op ps so' hso'
    · simp at hso'
  unfold emitOneInput at hso
  cases op with
  | Label l => exact absurd rfl (hop l)
  | Lit v =>
    simp only [List.mem_append] at hso
    rcases hso with h | h
    · exact hrestore so h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨by simp, by simp, by simp⟩
  | Var v =>
    simp only at hso
    split at hso
    · split at hso
      · rw [List.mem_append] at hso
        rcases hso with h | h
        · exact hrestore so h
        · exact doDup_no_label _ _ so h
      · exact hrestore so hso
    · exact hrestore so hso

/-- **`emitInputPlan` of non-label operands produces no label-push stack-op** (fold of
    `emitOneInput_no_label`), so its compiled asm is label-free — the emit segment of a RETURN/REVERT block
    resolves pointwise. -/
theorem emitInputPlan_no_label (opc : Opcode) (nl : List String) :
    ∀ (ops : List Operand), (∀ op ∈ ops, ∀ l, op ≠ Operand.Label l) → ∀ (ps : PlanState),
    ∀ so ∈ (emitInputPlan opc ops nl ps).1, (∀ l, so ≠ StackOp.SOPushLabel l)
      ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d) ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  have hfold : ∀ (ops : List Operand), (∀ op ∈ ops, ∀ l, op ≠ Operand.Label l) →
      ∀ (acc : List StackOp × PlanState),
      (∀ so ∈ acc.1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
        ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l))) →
      ∀ so ∈ (ops.foldl (fun (acc : List StackOp × PlanState) op =>
          (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) acc).1,
        (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
          ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
    intro ops
    induction ops with
    | nil => intro _ acc hacc so hso; exact hacc so hso
    | cons hd tl ih =>
      intro hlbl acc hacc so hso
      rw [List.foldl_cons] at hso
      refine ih (fun op hop => hlbl op (List.mem_cons_of_mem _ hop)) _ ?_ so hso
      intro so' hso'
      rw [List.mem_append] at hso'
      rcases hso' with h | h
      · exact hacc so' h
      · exact emitOneInput_no_label opc nl hd (hlbl hd (List.mem_cons_self ..)) acc.2 so' h
  intro ops hlbl ps so hso
  exact hfold ops hlbl ([], ps) (by simp) so hso

/-! ### No `SOLabel` in the plan ops — the other half of `hpreuniq`

`hpreuniq` reduces (via `asmLabelCount_executePlan`) to counting `SOLabel` in the plan. `SOLabel` is
emitted ONLY by `generateBlockPlan`'s own leading label and by `generateEmitOps` for INVOKE /
ASSERT_UNREACHABLE / DJMP (which mint fresh labels). Everything else — the whole spill/reorder/emit
machinery — emits none. These mirror the `SOPushLabel` chain above. Note NO non-label-operand side
condition is needed: even an `Operand.Label` emits `SOPushLabel`, never `SOLabel`. -/

theorem spillFold_no_soLabel :
    ∀ (items : List Operand) (acc : List StackOp × List Nat × SpillAlloc),
    (∀ so ∈ acc.1, ∀ l, so ≠ StackOp.SOLabel l) →
    ∀ so ∈ (items.foldl (fun (x : List StackOp × List Nat × SpillAlloc) (item : Operand) =>
        let (off, al') := allocSpillSlot x.2.2
        (x.1 ++ [StackOp.SOSpill off], x.2.1 ++ [off], al')) acc).1,
      ∀ l, so ≠ StackOp.SOLabel l := by
  intro items
  induction items with
  | nil => intro acc hacc so hso; exact hacc so hso
  | cons hd tl ih =>
    intro acc hacc so hso
    rw [List.foldl_cons] at hso
    refine ih _ ?_ so hso
    intro so' hso'
    rw [List.mem_append] at hso'
    rcases hso' with h | h
    · exact hacc so' h
    · simp only [List.mem_singleton] at h; subst h; simp

theorem doDup_no_soLabel (dist : Nat) (ps : PlanState) :
    ∀ so ∈ (doDup dist ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso
  unfold doDup at hso
  split at hso
  · simp only [List.mem_singleton] at hso; subst hso; simp
  · simp only [List.mem_append] at hso
    rcases hso with h | h
    · exact spillFold_no_soLabel _ ([], [], ps.alloc) (by simp) so h
    · rw [List.mem_map] at h; obtain ⟨idx, _, rfl⟩ := h; simp

theorem doSwap_no_soLabel (dist : Nat) (ps : PlanState) :
    ∀ so ∈ (doSwap dist ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso
  unfold doSwap at hso
  split at hso
  · simp at hso
  · split at hso
    · simp only [List.mem_singleton] at hso; subst hso; simp
    · simp only [List.mem_append] at hso
      rcases hso with h | h
      · exact spillFold_no_soLabel _ ([], [], ps.alloc) (by simp) so h
      · rw [List.mem_map] at h; obtain ⟨idx, _, rfl⟩ := h; simp

theorem doRestore_no_soLabel (op : Operand) (ps : PlanState) :
    ∀ so ∈ (doRestore op ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso
  unfold doRestore at hso
  split at hso
  · simp at hso
  · simp only [List.mem_singleton] at hso; subst hso; simp

theorem emitOneInput_no_soLabel (opc : Opcode) (nl : List String) (op : Operand) (ps : PlanState) :
    ∀ so ∈ (emitOneInput opc nl op ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso
  have hrestore : ∀ so' ∈ (if isVarOperand op && (alookup' ps.spilled op).isSome
      then doRestore op ps else ([], ps)).1, ∀ l, so' ≠ StackOp.SOLabel l := by
    intro so' hso'; split at hso'
    · exact doRestore_no_soLabel op ps so' hso'
    · simp at hso'
  unfold emitOneInput at hso
  cases op with
  | Label l =>
    simp only at hso
    split at hso
    · exact hrestore so hso
    · simp only [List.mem_append] at hso
      rcases hso with h | h
      · exact hrestore so h
      · simp only [List.mem_singleton] at h; subst h; simp
  | Lit v =>
    simp only [List.mem_append] at hso
    rcases hso with h | h
    · exact hrestore so h
    · simp only [List.mem_singleton] at h; subst h; simp
  | Var v =>
    simp only at hso
    split at hso
    · split at hso
      · rw [List.mem_append] at hso
        rcases hso with h | h
        · exact hrestore so h
        · exact doDup_no_soLabel _ _ so h
      · exact hrestore so hso
    · exact hrestore so hso

theorem emitInputPlan_no_soLabel (opc : Opcode) (nl : List String) :
    ∀ (ops : List Operand) (ps : PlanState),
    ∀ so ∈ (emitInputPlan opc ops nl ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  have hfold : ∀ (ops : List Operand) (acc : List StackOp × PlanState),
      (∀ so ∈ acc.1, ∀ l, so ≠ StackOp.SOLabel l) →
      ∀ so ∈ (ops.foldl (fun (acc : List StackOp × PlanState) op =>
          (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) acc).1,
        ∀ l, so ≠ StackOp.SOLabel l := by
    intro ops
    induction ops with
    | nil => intro acc hacc so hso; exact hacc so hso
    | cons hd tl ih =>
      intro acc hacc so hso
      rw [List.foldl_cons] at hso
      refine ih _ ?_ so hso
      intro so' hso'
      rw [List.mem_append] at hso'
      rcases hso' with h | h
      · exact hacc so' h
      · exact emitOneInput_no_soLabel opc nl hd acc.2 so' h
  intro ops ps
  exact hfold ops ([], ps) (by simp)
theorem reorderOne_no_soLabel (dfg : Unit) (targetOps : List Operand) (targetIdx : Nat)
    (op : Operand) (ps : PlanState) :
    ∀ so ∈ (reorderOne dfg targetOps targetIdx op ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  have hrest : ∀ so' ∈ ((match stackGetDepth op ps.stack with
      | some _ => ([], ps)
      | none =>
        match alookup' ps.spilled op with
        | some _ => doRestore op ps
        | none => ([], ps)) : List StackOp × PlanState).1,
      ∀ l, so' ≠ StackOp.SOLabel l := by
    intro so' hso'
    split at hso'
    · simp at hso'
    · split at hso'
      · exact doRestore_no_soLabel op ps so' hso'
      · simp at hso'
  intro so hso
  unfold reorderOne at hso
  simp only [] at hso
  split at hso
  · exact hrest so hso
  · split at hso
    · exact hrest so hso
    · simp only [List.mem_append] at hso
      rcases hso with (h | h) | h
      · exact hrest so h
      · exact doSwap_no_soLabel _ _ so h
      · exact doSwap_no_soLabel _ _ so h

theorem reorderPlan_no_soLabel (targetOps : List Operand) (ps : PlanState) :
    ∀ so ∈ (reorderPlan targetOps ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  have hfold : ∀ (xs : List (Nat × Operand)) (acc : List StackOp × PlanState),
      (∀ so ∈ acc.1, ∀ l, so ≠ StackOp.SOLabel l) →
      ∀ so ∈ (xs.foldl (fun (acc : List StackOp × PlanState) (x : Nat × Operand) =>
          (acc.1 ++ (reorderOne () targetOps x.1 x.2 acc.2).1,
           (reorderOne () targetOps x.1 x.2 acc.2).2)) acc).1,
        ∀ l, so ≠ StackOp.SOLabel l := by
    intro xs
    induction xs with
    | nil => intro acc hacc so hso; exact hacc so hso
    | cons hd tl ih =>
      intro acc hacc so hso
      rw [List.foldl_cons] at hso
      refine ih _ ?_ so hso
      intro so' hso'
      rw [List.mem_append] at hso'
      rcases hso' with h | h
      · exact hacc so' h
      · exact reorderOne_no_soLabel () targetOps hd.1 hd.2 acc.2 so' h
  intro so hso
  exact hfold _ ([], ps) (by simp) so hso

/-- Generic fold lift: if each step only ever adds ops that are not `SOLabel`, the whole fold is
    `SOLabel`-free. Stated so `refine` can infer the fold function from the goal (writing the fold out
    longhand is what fights the unifier). -/
theorem foldl_pair_no_soLabel {α : Type} (l : List α)
    (f : List StackOp × PlanState → α → List StackOp × PlanState)
    (hf : ∀ acc x, ∀ so ∈ (f acc x).1, so ∈ acc.1 ∨ ∀ m, so ≠ StackOp.SOLabel m) :
    ∀ (acc : List StackOp × PlanState), (∀ so ∈ acc.1, ∀ m, so ≠ StackOp.SOLabel m) →
      ∀ so ∈ (l.foldl f acc).1, ∀ m, so ≠ StackOp.SOLabel m := by
  induction l with
  | nil => intro acc hacc so hso; exact hacc so hso
  | cons hd tl ih =>
    intro acc hacc so hso
    rw [List.foldl_cons] at hso
    refine ih _ ?_ so hso
    intro so' hso'
    rcases hf acc hd so' hso' with h | h
    · exact hacc so' h
    · exact h

theorem popmanyPlan_no_soLabel (toPop : List Operand) (ps : PlanState) :
    ∀ so ∈ (popmanyPlan toPop ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  unfold popmanyPlan
  simp only []
  split
  · intro so hso; exact absurd hso (by simp)
  · split
    · split
      · -- contiguous top: doSwap ++ [SOPop n]
        intro so hso
        simp only [List.mem_append, List.mem_singleton] at hso
        rcases hso with h | h
        · exact doSwap_no_soLabel _ _ so h
        · subst h; simp
      · -- individual swap+pop fold
        refine foldl_pair_no_soLabel _ _ ?_ ([], ps) (by simp)
        intro acc v so hso
        split at hso
        · exact Or.inl hso
        · simp only [List.mem_append, List.mem_singleton] at hso
          rcases hso with (h | h) | h
          · exact Or.inl h
          · refine Or.inr ?_
            split at h
            · exact absurd h (by simp)
            · exact doSwap_no_soLabel _ _ so h
          · refine Or.inr ?_
            subst h
            simp
    · -- fallback individual fold
        refine foldl_pair_no_soLabel _ _ ?_ ([], ps) (by simp)
        intro acc v so hso
        split at hso
        · exact Or.inl hso
        · simp only [List.mem_append, List.mem_singleton] at hso
          rcases hso with (h | h) | h
          · exact Or.inl h
          · refine Or.inr ?_
            split at h
            · exact absurd h (by simp)
            · exact doSwap_no_soLabel _ _ so h
          · refine Or.inr ?_
            subst h
            simp

theorem optimisticSwapPlan_no_soLabel (dfg : DfgAnalysis) (inst : Instruction)
    (nextLiveness : List String) (nextIsTerminator : Bool) (ps : PlanState) :
    ∀ so ∈ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator ps).1,
      ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso
  unfold optimisticSwapPlan at hso
  simp only [] at hso
  (repeat' split at hso) <;>
    first
    | simp at hso
    | exact doSwap_no_soLabel _ _ so hso

theorem generatePhiPlan_no_soLabel (inst : Instruction) (nextLiveness : List String)
    (ps : PlanState) :
    ∀ so ∈ (generatePhiPlan inst nextLiveness ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold generatePhiPlan at hso
  simp only [] at hso
  split at hso
  · simp at hso
  · split at hso
    · simp only [List.mem_append, List.mem_singleton] at hso
      rcases hso with h | h
      · exact doDup_no_soLabel _ _ _ h l rfl
      · simp at h
    · simp at hso

theorem generateOffsetPlan_no_soLabel (inst : Instruction) (ps : PlanState) :
    ∀ so ∈ (generateOffsetPlan inst ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold generateOffsetPlan at hso
  simp only [] at hso
  (repeat' split at hso) <;> simp_all

/-- **`generateEmitOps` emits no `SOLabel`** — unless the opcode is one of the three that MINT a fresh
    label (`INVOKE` / `ASSERT_UNREACHABLE` / `DJMP`). So in a function free of those three, the only
    `SOLabel`s in the whole plan are the blocks' own leading labels. -/
theorem generateEmitOps_no_soLabel (inst : Instruction) (n : Nat) (ps : PlanState)
    (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (hdjmp : inst.opcode ≠ Opcode.DJMP) :
    ∀ so ∈ (generateEmitOps inst n ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold generateEmitOps at hso
  simp only [] at hso
  (repeat' split at hso) <;> simp_all

/-- The whole per-instruction plan emits no `SOLabel`, provided the opcode isn't one of the three
    fresh-label minters. Its ops are `emitInput ++ join-reorder ++ reorder ++ emit (++ popmany ++ optswap)`,
    every piece of which is `SOLabel`-free. -/
theorem generateRegularInstPlan_no_soLabel (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (hdjmp : inst.opcode ≠ Opcode.DJMP) :
    ∀ so ∈ (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
      nextIsTerminator curBbLabel ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold generateRegularInstPlan at hso
  simp only [] at hso
  have hjoin : ∀ h : StackOp.SOLabel l ∈ (if inst.opcode = Opcode.JMP then
      (match inst.operands with
       | [Operand.Label target] =>
         match fn.blocks.find? (·.label == target) with
         | none => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)
         | some targetBb =>
           reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
             (liveVarsAt liveness target 0)).map Operand.Var)
             (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2
       | _ => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2))
    else ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)).1, False := by
    intro h
    (repeat' split at h) <;>
      first
      | exact absurd h List.not_mem_nil
      | exact reorderPlan_no_soLabel _ _ _ h l rfl
  split at hso
  · simp only [List.mem_append] at hso
    rcases hso with ((h | h) | h) | h
    · exact emitInputPlan_no_soLabel _ _ _ _ _ h l rfl
    · exact hjoin h
    · exact reorderPlan_no_soLabel _ _ _ h l rfl
    · exact generateEmitOps_no_soLabel _ _ _ hinv hau hdjmp _ h l rfl
  · simp only [List.mem_append] at hso
    rcases hso with (((( h | h) | h) | h) | h) | h
    · exact emitInputPlan_no_soLabel _ _ _ _ _ h l rfl
    · exact hjoin h
    · exact reorderPlan_no_soLabel _ _ _ h l rfl
    · exact generateEmitOps_no_soLabel _ _ _ hinv hau hdjmp _ h l rfl
    · (repeat' split at h) <;>
        first
        | exact absurd h List.not_mem_nil
        | exact popmanyPlan_no_soLabel _ _ _ h l rfl
    · (repeat' split at h) <;>
        first
        | exact absurd h List.not_mem_nil
        | exact optimisticSwapPlan_no_soLabel _ _ _ _ _ _ h l rfl

theorem generateInstPlan_no_soLabel (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    {ops : List StackOp} {ps' : PlanState}
    (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (hdjmp : inst.opcode ≠ Opcode.DJMP)
    (h : generateInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
      curBbLabel ps = some (ops, ps')) :
    ∀ so ∈ ops, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold generateInstPlan at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq, Prod.ext_iff] at h
      obtain ⟨rfl, -⟩ := h
      exact generatePhiPlan_no_soLabel _ _ _ _ hso l rfl
    · split at h
      · simp only [Option.some.injEq, Prod.ext_iff] at h
        obtain ⟨rfl, -⟩ := h
        exact generateOffsetPlan_no_soLabel _ _ _ hso l rfl
      · split at h
        · simp only [Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, -⟩ := h
          exact absurd hso (by simp)
        · split at h
          · simp only [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, -⟩ := h
            exact absurd hso (by simp)
          · simp only [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, -⟩ := h
            exact generateRegularInstPlan_no_soLabel _ _ _ _ _ _ _ _ _ _ hinv hau hdjmp
              _ hso l rfl

theorem prepareParamsPlan_no_soLabel (liveness : DfState (List String)) (fn : IrFunction)
    (ps : PlanState) :
    ∀ so ∈ (prepareParamsPlan liveness fn ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold prepareParamsPlan at hso
  split at hso
  · exact absurd hso (by simp)
  · simp only [] at hso
    split at hso
    · exact absurd hso (by simp)
    · simp only [List.mem_append] at hso
      rcases hso with h | h
      · exact popmanyPlan_no_soLabel _ _ _ h l rfl
      · exact optimisticSwapPlan_no_soLabel _ _ _ _ _ _ h l rfl

theorem cleanStackPlan_no_soLabel (liveness : DfState (List String)) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) :
    ∀ so ∈ (cleanStackPlan liveness cfg fn bb ps).1, ∀ l, so ≠ StackOp.SOLabel l := by
  intro so hso l hcontra
  subst hcontra
  unfold cleanStackPlan at hso
  simp only [] at hso
  (repeat' split at hso) <;>
    first
    | exact absurd hso List.not_mem_nil
    | exact popmanyPlan_no_soLabel _ _ _ hso l rfl

/-! ### Push-label-freeness of the plan machinery — the other undischarged hstep input (`hlblfree`)

Every canonical `hstep` also takes `hlblfree` (the block's body asm emits no `AsmPushLabel`/`AsmPushOfst`)
as an INPUT, and it was never discharged either. `AsmPushLabel`/`AsmPushOfst` come only from
`SOPushLabel` / `SOPushOfst` / `SOPush (Operand.Label _)` (see `executePlan_no_label`), and among the
plan-producing operations only `generateEmitOps` ever emits those — for JMP / JNZ / DJMP / INVOKE /
ASSERT / ASSERT_UNREACHABLE. A *body* instruction is a non-terminator, which already rules out
JMP / JNZ / DJMP; the remaining three are an explicit side condition. -/

/-- Predicate-generic fold lift over the ops component. -/
theorem foldl_pair_ops_pred {α : Type} (P : StackOp → Prop) (l : List α)
    (f : List StackOp × PlanState → α → List StackOp × PlanState)
    (hf : ∀ acc x, ∀ so ∈ (f acc x).1, so ∈ acc.1 ∨ P so) :
    ∀ (acc : List StackOp × PlanState), (∀ so ∈ acc.1, P so) →
      ∀ so ∈ (l.foldl f acc).1, P so := by
  induction l with
  | nil => intro acc hacc so hso; exact hacc so hso
  | cons hd tl ih =>
    intro acc hacc so hso
    rw [List.foldl_cons] at hso
    refine ih _ ?_ so hso
    intro so' hso'
    rcases hf acc hd so' hso' with h | h
    · exact hacc so' h
    · exact h

theorem doSwap_no_label (dist : Nat) (ps : PlanState) :
    ∀ so ∈ (doSwap dist ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  unfold doSwap at hso
  split at hso
  · simp at hso
  · split at hso
    · simp only [List.mem_singleton] at hso; subst hso; exact ⟨by simp, by simp, by simp⟩
    · simp only [List.mem_append] at hso
      rcases hso with h | h
      · exact spillFold_no_label _ ([], [], ps.alloc) (by simp) so h
      · rw [List.mem_map] at h; obtain ⟨idx, _, rfl⟩ := h; exact ⟨by simp, by simp, by simp⟩

theorem reorderOne_no_label (dfg : Unit) (targetOps : List Operand) (targetIdx : Nat)
    (op : Operand) (ps : PlanState) :
    ∀ so ∈ (reorderOne dfg targetOps targetIdx op ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  have hrest : ∀ so' ∈ ((match stackGetDepth op ps.stack with
      | some _ => ([], ps)
      | none =>
        match alookup' ps.spilled op with
        | some _ => doRestore op ps
        | none => ([], ps)) : List StackOp × PlanState).1,
      (∀ l, so' ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so' ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so' ≠ StackOp.SOPush (Operand.Label l)) := by
    intro so' hso'
    split at hso'
    · simp at hso'
    · split at hso'
      · exact doRestore_no_label op ps so' hso'
      · simp at hso'
  intro so hso
  unfold reorderOne at hso
  simp only [] at hso
  split at hso
  · exact hrest so hso
  · split at hso
    · exact hrest so hso
    · simp only [List.mem_append] at hso
      rcases hso with (h | h) | h
      · exact hrest so h
      · exact doSwap_no_label _ _ so h
      · exact doSwap_no_label _ _ so h

theorem reorderPlan_no_label (targetOps : List Operand) (ps : PlanState) :
    ∀ so ∈ (reorderPlan targetOps ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  unfold reorderPlan
  refine foldl_pair_ops_pred _ _ _ ?_ ([], ps) (by simp)
  intro acc x so hso
  rw [List.mem_append] at hso
  rcases hso with h | h
  · exact Or.inl h
  · exact Or.inr (reorderOne_no_label () targetOps x.1 x.2 acc.2 so h)

theorem popmanyPlan_no_label (toPop : List Operand) (ps : PlanState) :
    ∀ so ∈ (popmanyPlan toPop ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  unfold popmanyPlan
  simp only []
  split
  · intro so hso; exact absurd hso List.not_mem_nil
  · split
    · split
      · intro so hso
        simp only [List.mem_append, List.mem_singleton] at hso
        rcases hso with h | h
        · exact doSwap_no_label _ _ so h
        · subst h; exact ⟨by simp, by simp, by simp⟩
      · refine foldl_pair_ops_pred _ _ _ ?_ ([], ps) (by simp)
        intro acc v so hso
        split at hso
        · exact Or.inl hso
        · simp only [List.mem_append, List.mem_singleton] at hso
          rcases hso with (h | h) | h
          · exact Or.inl h
          · refine Or.inr ?_
            split at h
            · exact absurd h List.not_mem_nil
            · exact doSwap_no_label _ _ so h
          · exact Or.inr (by subst h; exact ⟨by simp, by simp, by simp⟩)
    · refine foldl_pair_ops_pred _ _ _ ?_ ([], ps) (by simp)
      intro acc v so hso
      split at hso
      · exact Or.inl hso
      · simp only [List.mem_append, List.mem_singleton] at hso
        rcases hso with (h | h) | h
        · exact Or.inl h
        · refine Or.inr ?_
          split at h
          · exact absurd h List.not_mem_nil
          · exact doSwap_no_label _ _ so h
        · exact Or.inr (by subst h; exact ⟨by simp, by simp, by simp⟩)

theorem optimisticSwapPlan_no_label (dfg : DfgAnalysis) (inst : Instruction)
    (nextLiveness : List String) (nextIsTerminator : Bool) (ps : PlanState) :
    ∀ so ∈ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  unfold optimisticSwapPlan at hso
  simp only [] at hso
  (repeat' split at hso) <;>
    first
    | exact absurd hso List.not_mem_nil
    | exact doSwap_no_label _ _ so hso

/-- **`generateEmitOps` emits no label-push** unless the opcode is one of the six that reference a label:
    JMP / JNZ / DJMP / INVOKE / ASSERT / ASSERT_UNREACHABLE. -/
theorem generateEmitOps_no_label (inst : Instruction) (n : Nat) (ps : PlanState)
    (hjmp : inst.opcode ≠ Opcode.JMP) (hjnz : inst.opcode ≠ Opcode.JNZ)
    (hdjmp : inst.opcode ≠ Opcode.DJMP) (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hassert : inst.opcode ≠ Opcode.ASSERT) (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE) :
    ∀ so ∈ (generateEmitOps inst n ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  refine ⟨fun l hc => ?_, fun l d hc => ?_, fun l hc => ?_⟩ <;>
    subst hc <;>
    (unfold generateEmitOps at hso
     simp only [] at hso
     (repeat' split at hso) <;> simp_all)

/-- **The whole per-instruction plan is label-push-free** for a body instruction: the opcode references
    no label (six exclusions) and its operands carry none. -/
theorem generateRegularInstPlan_no_label (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    (hops : ∀ op ∈ computeOperands inst, ∀ l, op ≠ Operand.Label l)
    (hjmp : inst.opcode ≠ Opcode.JMP) (hjnz : inst.opcode ≠ Opcode.JNZ)
    (hdjmp : inst.opcode ≠ Opcode.DJMP) (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hassert : inst.opcode ≠ Opcode.ASSERT) (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE) :
    ∀ so ∈ (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
      nextIsTerminator curBbLabel ps).1, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  intro so hso
  unfold generateRegularInstPlan at hso
  simp only [] at hso
  -- the JMP join-reorder branch is dead (opcode ≠ JMP)
  have hjoin : ∀ so' ∈ (if inst.opcode = Opcode.JMP then
      (match inst.operands with
       | [Operand.Label target] =>
         match fn.blocks.find? (·.label == target) with
         | none => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)
         | some targetBb =>
           reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
             (liveVarsAt liveness target 0)).map Operand.Var)
             (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2
       | _ => ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2))
    else ([], (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2)).1,
      (∀ l, so' ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so' ≠ StackOp.SOPushOfst l d)
        ∧ (∀ l, so' ≠ StackOp.SOPush (Operand.Label l)) := by
    intro so' hso'
    (repeat' split at hso') <;>
      first
      | exact absurd hso' List.not_mem_nil
      | exact reorderPlan_no_label _ _ so' hso'
  have handle : ∀ h : so ∈ ([] : List StackOp), (∀ l, so ≠ StackOp.SOPushLabel l) ∧
      (∀ l d, so ≠ StackOp.SOPushOfst l d) ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) :=
    fun h => absurd h List.not_mem_nil
  split at hso <;>
    (simp only [List.mem_append] at hso
     (repeat' rcases hso with hso | hso) <;>
       first
       | exact handle hso
       | exact emitInputPlan_no_label _ _ _ hops _ so hso
       | exact hjoin so hso
       | exact reorderPlan_no_label _ _ so hso
       | exact generateEmitOps_no_label _ _ _ hjmp hjnz hdjmp hinv hassert hau so hso
       | ((repeat' split at hso) <;>
           first
           | exact handle hso
           | exact popmanyPlan_no_label _ _ so hso
           | exact optimisticSwapPlan_no_label _ _ _ _ _ so hso))

theorem generateInstPlan_no_label (liveness : DfState (List String)) (dfg : DfgAnalysis)
    (cfg : CfgAnalysis) (fn : IrFunction) (inst : Instruction) (nextLiveness : List String)
    (isHalting nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    {ops : List StackOp} {ps' : PlanState}
    (hops : ∀ op ∈ computeOperands inst, ∀ l, op ≠ Operand.Label l)
    (hreg : ¬ isPreCodegenOpcode inst.opcode ∧ inst.opcode ≠ Opcode.PHI ∧
      inst.opcode ≠ Opcode.OFFSET ∧ inst.opcode ≠ Opcode.PARAM ∧ inst.opcode ≠ Opcode.NOP)
    (hjmp : inst.opcode ≠ Opcode.JMP) (hjnz : inst.opcode ≠ Opcode.JNZ)
    (hdjmp : inst.opcode ≠ Opcode.DJMP) (hinv : inst.opcode ≠ Opcode.INVOKE)
    (hassert : inst.opcode ≠ Opcode.ASSERT) (hau : inst.opcode ≠ Opcode.ASSERT_UNREACHABLE)
    (h : generateInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
      curBbLabel ps = some (ops, ps')) :
    ∀ so ∈ ops, (∀ l, so ≠ StackOp.SOPushLabel l) ∧ (∀ l d, so ≠ StackOp.SOPushOfst l d)
      ∧ (∀ l, so ≠ StackOp.SOPush (Operand.Label l)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hreg
  intro so hso
  unfold generateInstPlan at h
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4] at h
  simp only [Option.some.injEq, Prod.ext_iff] at h
  obtain ⟨rfl, -⟩ := h
  exact generateRegularInstPlan_no_label _ _ _ _ _ _ _ _ _ _ hops hjmp hjnz hdjmp hinv hassert hau
    so hso

/-- `generateEmitOps` for a LOG op emits the single `LOGn` opcode (`opcodeToEvmName LOG = none`, then
    the if-chain reaches the LOG branch). -/
theorem generateEmitOps_log {inst : Instruction} {n : Nat} {ps : PlanState}
    (hopc : inst.opcode = Opcode.LOG) :
    generateEmitOps inst n ps = ([StackOp.SOEmit ("LOG" ++ toString n)], ps) := by
  unfold generateEmitOps
  rw [hopc]; rfl

/-- Popping the whole freshly-emitted top group leaves the base (`stackPop os.length (base ++ os)`). -/
theorem stackPop_append_top (base os : List Operand) :
    stackPop os.length (base ++ os) = base := by
  unfold stackPop
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left

/-- **Structural decomposition of `generateRegularInstPlan` for a JMP terminator** in the
    well-scheduled case: the body already laid the plan stack out as the target block's entry layout
    `inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)` (mapped to vars,
    nodup), so the join reorder is a no-op. The plan is exactly `[SOPushLabel target, SOEmit "JUMP"]`
    over the dead-spill release, and the output plan stack stays the target layout
    (`releaseDeadSpills` doesn't touch the stack) — the post-body plan stack = target entry layout
    reconciliation, wired through the real generator. -/
theorem generateRegularInstPlan_jmp_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hstack : ps.stack = (inputVarsFrom curBbLabel targetBb.instructions
                (liveVarsAt liveness target 0)).map Operand.Var)
    (hnodup : (inputVarsFrom curBbLabel targetBb.instructions
                (liveVarsAt liveness target 0)).Nodup) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], releaseDeadSpills nextLiveness ps) := by
  have hjoin : reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
      (liveVarsAt liveness target 0)).map Operand.Var) ps = ([], ps) :=
    reorderPlan_vars_nil _ ps hstack hnodup
  unfold generateRegularInstPlan
  simp only [computeOperands_jmp hjmp hops, emitInputPlan_nil, hjmp, hops, htgt, hjoin,
    generateEmitOps_jmp hjmp hops, houts, reorderPlan_empty, stackPop_zero,
    isCommutative, List.length_nil, List.foldl_nil, List.isEmpty_nil, List.append_nil,
    List.nil_append, if_true, if_false, Bool.false_eq_true, Bool.false_and]

/-- **The JMP terminator compiles to `[AsmPushLabel target ; AsmOp "JUMP"]`** (well-scheduled): the
    asm form of `generateRegularInstPlan_jmp_eq`'s plan. This is the bridge that discharges
    `block_jmp_asm_compose`'s "the resolved `[push-label ; JUMP]` sits at `asmPreJmp.pc`" hypotheses
    from the block-plan structure — combined with the body run (`runAsm bodyLen` to `asmPreJmp`) and
    the resolved JUMP (`resolved_jump_sim`), the JMP block runs to the successor's entry index. -/
theorem genJmp_executePlan_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hstack : ps.stack = (inputVarsFrom curBbLabel targetBb.instructions
                (liveVarsAt liveness target 0)).map Operand.Var)
    (hnodup : (inputVarsFrom curBbLabel targetBb.instructions
                (liveVarsAt liveness target 0)).Nodup) :
    executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps).1
      = [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] := by
  rw [generateRegularInstPlan_jmp_eq hjmp hops houts htgt hstack hnodup]; rfl

/-- **JMP-terminator plan decomposition, genuine-reorder case.** Unlike `generateRegularInstPlan_jmp_eq`
    (which assumes the body already produced the target layout, so the join reorder is a no-op), this
    keeps the join reorder explicit: for a JMP to `target`, the plan is
    `(reorderPlan targetStack ps).1 ++ [SOPushLabel target, SOEmit "JUMP"]` — the join reorder that aligns
    the predecessor's stack to the target block's entry layout, then the label push + JUMP. This is the
    plan whose asm side `reorderPlan_join_sim` + `resolved_jump_sim` (packaged as `hasm_jmp_reorder`)
    discharge for a genuine (non-identity) join. -/
theorem generateRegularInstPlan_jmp_reorder_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1
      = (reorderPlan ((inputVarsFrom curBbLabel targetBb.instructions
          (liveVarsAt liveness target 0)).map Operand.Var) ps).1
        ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"] := by
  unfold generateRegularInstPlan
  simp only [computeOperands_jmp hjmp hops, emitInputPlan_nil, hjmp, hops, htgt,
    generateEmitOps_jmp hjmp hops, houts, reorderPlan_empty, stackPop_zero,
    isCommutative, List.length_nil, List.foldl_nil, List.isEmpty_nil, List.append_nil,
    List.nil_append, if_true, if_false, Bool.false_eq_true, Bool.false_and]

/-- `stackFind` succeeds (with an in-range index) whenever some element satisfies the predicate.
    The membership counterpart of `stackFind_some`. -/
theorem stackFind_isSome {p : Operand → Bool} :
    ∀ {l : List Operand}, (∃ a, a ∈ l ∧ p a = true) → ∃ d, stackFind p l = some d ∧ d < l.length := by
  intro l
  induction l with
  | nil => intro h; obtain ⟨a, ha, _⟩ := h; simp at ha
  | cons b bs ih =>
    intro h
    rw [stackFind]
    split
    · exact ⟨0, rfl, by simp⟩
    · rename_i hpb
      have hbs : ∃ a, a ∈ bs ∧ p a = true := by
        obtain ⟨a, ha, hpa⟩ := h
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact absurd hpa hpb
        · exact ⟨a, ha', hpa⟩
      obtain ⟨d, hd, hlt⟩ := ih hbs
      rw [hd]
      exact ⟨d + 1, rfl, by simp only [List.length_cons]; omega⟩

/-- A var present on the stack has a concrete depth, in range. The membership→depth direction
    (`stackGetDepth_peek` is the depth→value direction) — this is how a stack-discipline invariant
    (vars-on-stack) discharges the per-instruction `hdepth`/`hlen` side conditions. -/
theorem stackGetDepth_of_mem {x : String} {stk : List Operand} (h : Operand.Var x ∈ stk) :
    ∃ d, stackGetDepth (Operand.Var x) stk = some d ∧ d < stk.length := by
  unfold stackGetDepth
  have hex : ∃ a, a ∈ stk.reverse ∧ (a == Operand.Var x) = true := by
    refine ⟨Operand.Var x, ?_, by simp⟩
    rwa [List.mem_reverse]
  obtain ⟨d, hd, hlt⟩ := stackFind_isSome hex
  rw [List.length_reverse] at hlt
  exact ⟨d, hd, hlt⟩

theorem doSwap_zero (ps : PlanState) : doSwap 0 ps = ([], ps) := by
  unfold doSwap; simp

theorem doSwap_one (ps : PlanState) :
    doSwap 1 ps = ([StackOp.SOSwap 1], { ps with stack := stackSwap 1 ps.stack }) := by
  unfold doSwap; simp

/-- **Step 0 of the swapped reorder for any operand pair:** the TOS `q` is at depth 0 and its
    target depth is 1, so `reorderOne` emits a single `SWAP1`. Class-agnostic — literal, var, and
    mixed pairs are all instances. -/
theorem reorderOne_swap0_pair (base : List Operand) (p q : Operand) (ps : PlanState)
    (hstack : ps.stack = base ++ [p, q]) :
    reorderOne () [q, p] 0 q ps = ([StackOp.SOSwap 1], { ps with stack := base ++ [q, p] }) := by
  have hdb : stackGetDepth q ps.stack = some 0 := by
    rw [hstack]; exact stackGetDepth_tos base p q
  have hsw : stackSwap 1 ps.stack = base ++ [q, p] := by
    rw [hstack]; exact stackSwap_1_append_pair base p q
  unfold reorderOne
  simp [hdb, doSwap_zero, doSwap_one, hsw]

/-- **The swapped reorder of any positioned pair costs one `SWAP1`** — the commutative `opsB` side,
    class-agnostic and needing no distinctness (`q` is on top and gets swapped down; `p` then sits
    at its target depth 0). Paired with `reorderPlan_pair_nil` (cost 0) this pins the commutative
    cheaper-order comparison `0 < 1` for *every* operand-class combination, mixed included. -/
theorem reorderPlan_swapped_pair (base : List Operand) (p q : Operand) (ps : PlanState)
    (hstack : ps.stack = base ++ [p, q]) :
    reorderPlan [q, p] ps = ([StackOp.SOSwap 1], { ps with stack := base ++ [q, p] }) := by
  have hstep0 := reorderOne_swap0_pair base p q ps hstack
  have hstep1 : reorderOne () [q, p] 1 p { ps with stack := base ++ [q, p] }
      = ([], { ps with stack := base ++ [q, p] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth p (base ++ [q, p]) = some 0
    exact stackGetDepth_tos base q p
  unfold reorderPlan
  have henum : ([q, p]).enum = [(0, q), (1, p)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.append_nil, List.nil_append]

/-- Step 0 of the swapped-pair reorder: bring `Lit b` (at depth 0) to its target depth 1
    via a single `SWAP1`. -/
theorem reorderOne_swap0 (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderOne () [Operand.Lit b, Operand.Lit a] 0 (Operand.Lit b) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }) :=
  reorderOne_swap0_pair base _ _ ps hstack

/-- The swapped-pair reorder on a positioned stack costs one `SWAP1` (independent of
    distinctness: `Lit b` is on top, gets swapped down; `Lit a` then sits at its target). -/
theorem reorderPlan_swapped_pair_lit (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderPlan [Operand.Lit b, Operand.Lit a] ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }) :=
  reorderPlan_swapped_pair base _ _ ps hstack

/-- The first `reorderOne` of the swapped var pair does a `SWAP1` (var counterpart of
    `reorderOne_swap0`). -/
theorem reorderOne_swap0_var (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) :
    reorderOne () [Operand.Var y, Operand.Var x] 0 (Operand.Var y) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var x] }) :=
  reorderOne_swap0_pair base _ _ ps hstack

/-- The swapped var-pair reorder costs one `SWAP1` (var counterpart of
    `reorderPlan_swapped_pair_lit` — the commutative `opsB` side). -/
theorem reorderPlan_swapped_pair_var (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) :
    reorderPlan [Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var x] }) :=
  reorderPlan_swapped_pair base _ _ ps hstack

/-- `reorderCost` of the swapped-pair reorder is 1 — the `opsB` side, completing the
    commutative-branch comparison (`reorderCost opsA = 0 < 1 = reorderCost opsB`). -/
theorem reorderCost_swapped_pair_lit (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderCost (reorderPlan [Operand.Lit b, Operand.Lit a] ps).1 = 1 := by
  rw [reorderPlan_swapped_pair_lit base a b ps hstack]; rfl

end EvmYul.Venom.Hol.Codegen

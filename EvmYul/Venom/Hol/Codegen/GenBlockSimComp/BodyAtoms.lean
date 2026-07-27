/-
GenBlockSimComp / Phase 2 — body atoms & reorder

Split part of `GenBlockSimComp`; see that module's header for the full roadmap.
This part continues the single `EvmYul.Venom.Hol.Codegen` namespace and imports
the previous part, so the whole was cut horizontally with no change in meaning.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.StackDiscipline

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ## Invariant-threading body fold

The body-fold counterpart of `genBlockBody_sim` that THREADS the `StackDiscH` invariant. Given a
per-instruction step that, from `StackDiscH (j+1)`, both simulates the asm AND re-establishes
`StackDiscH j` (exactly `stackDisc_commBinopVar_step`'s shape), folding over a body of length `n`
with initial headroom `n` runs the whole body's asm and lands at `StackDiscH 0`. Unlike
`genBlockBody_sim`'s *uniform* `hstep` (which only sees `venomAsmRel`), here the per-instruction side
conditions are carried by the invariant, whose headroom drops one unit per (stack-growing)
instruction — so a depth bound that a single instruction would break stays true across the body. -/
theorem genBlockBody_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length)
        ∧ StackDiscH j (gp x p).2 (gvBodyStep x v))
    (l : List (Instruction × Nat)) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState)
    (hsd0 : StackDiscH l.length ps0 vs0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (l.foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (l.foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
             (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (l.foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0
             (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
             (l.foldl (fun v x => gvBodyStep x v) vs0) := by
  induction l generalizing ps0 vs0 as0 with
  | nil =>
    refine ⟨as0, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
  | cons x xs ih =>
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1⟩ := hstep x ps0 vs0 as0 xs.length hsd0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd'⟩ :=
      ih (gp x ps0).2 (gvBodyStep x vs0) as1 hsd1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd'⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega

/-! ## S-threading body fold (no-swap regime)

`genBlockBody_sim_inv`'s `hstep` is `∀ x p`, so it can't supply each instruction's operand membership
(`x, y ∈ stack`). This version threads the stack-var list `S` too, via a per-instruction readiness
predicate `BodyStepsReady` that *pins* `S` at each position — so the SSA fact "operands ∈ S_i" is a
fixed fact the caller discharges (via `stackDisc_commBinopVar_step_S`). The pinned-`S` entry is still
`∀ p` (any plan state with `StackIsVars S p`), which is exactly what `step_S` proves given the static
binop facts + the no-op optimistic swap (the no-swap regime, where the schedule needs no reorder). -/

/-- The output var an instruction appends to the stack-var list. -/
def outOf (x : Instruction × Nat) : String := x.1.outputs.headD ""

/-- Per-instruction readiness threading the stack-var list `S`: each instruction's body step holds
    for any state with `StackIsVars S` (S pinned to its position), and the tail is ready relative to
    `S ++ [outOf x]`. Proven per-block by `stackDisc_commBinopVar_step_S` (its `x,y ∈ S`/`out ∉ S`
    obligations become fixed SSA facts once `S` is pinned). -/
def BodyStepsReady (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S =>
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → StackIsVars S p → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
        StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
        StackIsVars (S ++ [outOf x]) (gp x p).2)
      ∧ BodyStepsReady lo offsetToPc prog gp xs (S ++ [outOf x])

/-- **S-threading body fold.** Given `BodyStepsReady` (per-instruction steps with `S` pinned) and the
    initial headroom (`StackDiscH l.length`) + stack shape (`StackIsVars S0`), folding the body runs
    its whole asm and ends at `StackDiscH 0` with the stack now `S0 ++ l.map outOf`. The fold consumes
    the readiness predicate one entry per instruction, threading both invariants. -/
theorem genBlockBody_sim_inv_S {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReady lo offsetToPc prog gp l S0 →
      StackDiscH l.length ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
             StackDiscH 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) ∧
             StackIsVars (S0 ++ l.map outOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨hstepx, hready_xs⟩ := hready
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv, List.map_cons] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ := hstepx ps0 vs0 as0 xs.length hsd0 hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ [outOf x]) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'

/-- **Single-binop `BodyStepsReady` constructor.** Packages one commutative var-binop body
    instruction (immediately preceding the block terminator) into a one-element `BodyStepsReady`,
    ready to feed `genBlockBody_sim_inv_S` / `genBlockPrefixBody_sim_inv`. The key simplification is
    `nextIsTerminator = true`: the optimistic-swap obligation of `stackDisc_commBinopVar_step_S`
    collapses to `([], ps)` (the first branch of `optimisticSwapPlan`), so it holds for *every* plan
    state with no per-state reasoning — exactly the no-swap regime the body fold needs. The remaining
    obligations are static SSA facts about `inst`/`S` (operands `∈ S`, output fresh, both live) and the
    program's opcode dispatch. This is the missing adapter between the per-instruction body atom and the
    body-fold engine. -/
theorem bodyStepsReady_single_commBinop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s) :
    BodyStepsReady lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      [(inst, idx)] S := by
  refine ⟨?_, trivial⟩
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopVar_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ## Permutation-aware invariant (handling an active optimistic swap)

The optimistic swap reorders the stack to match the next instruction's operand order, breaking the
exact-order `StackIsVars`. But everything the per-instruction step actually needs — operand
membership, stack length, output freshness — is order-INDEPENDENT. So the right generalization tracks
the stack *up to permutation*: `StackPerm S p` says the plan stack is a permutation of `S.map Var`. It
generalizes `StackIsVars` (equality ⇒ permutation) and supports the same membership/length/freshness
derivations, now stable under the swap's reordering. (The exact-order `StackIsVars` is the no-swap
special case; `StackPerm` is what an active-swap fold threads.) -/
def StackPerm (S : List String) (p : PlanState) : Prop :=
  List.Perm p.stack (S.map Operand.Var)

/-- The exact-order invariant implies the permutation invariant. -/
theorem stackIsVars_perm {S : List String} {p : PlanState} (h : StackIsVars S p) : StackPerm S p := by
  have hp : p.stack = S.map Operand.Var := h
  rw [StackPerm, hp]

/-- Operand membership from the permutation invariant (order-independent). -/
theorem stackPerm_mem {S : List String} {p : PlanState} {z : String}
    (h : StackPerm S p) (hz : z ∈ S) : Operand.Var z ∈ p.stack :=
  h.mem_iff.mpr (List.mem_map_of_mem hz)

/-- A var not in `S` is absent from the stack (freshness), order-independent. -/
theorem stackPerm_not_mem {S : List String} {p : PlanState} {z : String}
    (h : StackPerm S p) (hz : z ∉ S) : ¬ Operand.Var z ∈ p.stack := by
  intro hc
  rw [h.mem_iff, List.mem_map] at hc
  obtain ⟨a, ha, hav⟩ := hc
  injection hav with hav'
  exact hz (hav' ▸ ha)

/-- The stack depth equals `S.length` (for the `shallow` bound), order-independent. -/
theorem stackPerm_length {S : List String} {p : PlanState} (h : StackPerm S p) :
    p.stack.length = S.length := by rw [h.length_eq, List.length_map]

/-- `StackPerm` is preserved by appending the output (the no-swap output stack `ps.stack ++ [Var out]`
    permutes `(S ++ [out]).map Var`); under an active swap, a stack *permutation* of this still
    satisfies `StackPerm (S ++ [out])` by transitivity — which is exactly why the permutation form is
    the right invariant for the swap. -/
theorem stackPerm_append_out {S : List String} {p : PlanState} {out : String}
    (h : StackPerm S p) :
    StackPerm (S ++ [out]) { p with stack := p.stack ++ [Operand.Var out] } := by
  show List.Perm (p.stack ++ [Operand.Var out]) ((S ++ [out]).map Operand.Var)
  rw [List.map_append]
  exact h.append_right _

open List in
/-- **`stackSwap` is a permutation of its input.** The optimistic swap reorders the stack via a
    single `stackSwap` (a transposition of the top with an earlier element), so its output is a
    *permutation* of the input. Proved structurally (BEq-free): decompose `s = mid ++ [last]`, reduce
    the two `set`s to `(mid.set k last) ++ [mid[k]]`, then chain `set_perm_cons_eraseIdx` +
    `getElem_cons_eraseIdx_perm` + `perm_append_comm`. (`dist < s.length` holds at every call site
    via `doSwap`'s bound; `dist = 0` is the identity case.) -/
theorem stackSwap_perm (dist : Nat) (s : List Operand) (hd : dist < s.length) :
    List.Perm (stackSwap dist s) s := by
  rcases Nat.eq_zero_or_pos dist with h0 | hpos
  · subst h0
    have ht : s.length - 1 < s.length := by omega
    simp only [stackSwap, Nat.sub_zero, List.set_set]
    rw [getElem!_pos s _ ht, List.set_getElem_self]
  · obtain ⟨mid, last, hs⟩ : ∃ mid last, s = mid ++ [last] := by
      rcases List.eq_nil_or_concat s with h | ⟨mid, last, h⟩
      · subst h; simp at hd
      · exact ⟨mid, last, by rw [h, List.concat_eq_append]⟩
    subst hs
    have hkmid : mid.length - dist < mid.length := by simp at hd; omega
    have hlenq : (mid ++ [last]).length = mid.length + 1 := by simp
    have hidx_t : (mid ++ [last]).length - 1 = mid.length := by simp
    have hv : (mid ++ [last])[mid.length - dist]! = mid[mid.length - dist]'hkmid := by
      rw [getElem!_pos _ _ (by rw [hlenq]; omega),
          List.getElem_append_left hkmid]
    have hw : (mid ++ [last])[mid.length]! = last := by
      rw [getElem!_pos _ _ (by rw [hlenq]; omega),
          List.getElem_append_right (by omega)]; simp
    have hstk : stackSwap dist (mid ++ [last])
        = (mid.set (mid.length - dist) last) ++ [mid[mid.length - dist]'hkmid] := by
      simp only [stackSwap, hidx_t, hv, hw]
      rw [List.set_append, if_neg (by omega)]
      simp only [Nat.sub_self, List.set_cons_zero]
      rw [List.set_append, if_pos (by omega)]
    rw [hstk]
    have hperm1 : (mid.set (mid.length - dist) last) ~ last :: mid.eraseIdx (mid.length - dist) :=
      List.set_perm_cons_eraseIdx hkmid last
    calc (mid.set (mid.length - dist) last) ++ [mid[mid.length - dist]'hkmid]
        ~ (last :: mid.eraseIdx (mid.length - dist)) ++ [mid[mid.length - dist]'hkmid] :=
          hperm1.append_right _
      _ = last :: (mid.eraseIdx (mid.length - dist) ++ [mid[mid.length - dist]'hkmid]) := by simp
      _ ~ last :: (mid[mid.length - dist]'hkmid :: mid.eraseIdx (mid.length - dist)) :=
          List.Perm.cons _ (List.perm_append_comm.trans (by simp))
      _ ~ last :: mid := List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hkmid)
      _ ~ mid ++ [last] := by
          have := List.perm_append_comm (l₁ := [last]) (l₂ := mid); simpa using this

/-! ### General reorder positioning (`perm_reaches` per-step correctness)

The per-step plan-stack transition (`reorderOne_stack_swap`) leaves `op` at its final depth. These
`stackSwap`/`stackPeek` element-tracking lemmas + the nodup first-occurrence converse establish that
positioning fact (`reorderOne_positions`) — the induction step of the general reorder's selection sort.
The remaining `perm_reaches` content is the fold invariant: positioning `op[i]` (each step shallower)
leaves the already-positioned deeper `op[0..i-1]` untouched, so `reorderPlan` reaches `base ++ targetOps`. -/

theorem stackSwap_length (dist : Nat) (stk : List Operand) :
    (stackSwap dist stk).length = stk.length := by
  unfold stackSwap; simp [List.length_set]

/-- `stackSwap dist` brings the depth-`dist` element to TOS (depth 0). -/
theorem stackPeek_zero_stackSwap {dist : Nat} {stk : List Operand} (hpos : 0 < dist)
    (hlt : dist < stk.length) : stackPeek 0 (stackSwap dist stk) = stackPeek dist stk := by
  have hne : stk.length - 1 - dist ≠ stk.length - 1 := by omega
  have hjt : stk.length - 1 < (stk.set (stk.length - 1) (stk[stk.length - 1 - dist]!)).length := by
    rw [List.length_set]; omega
  have hit : stk.length - 1 < stk.length := by omega
  unfold stackPeek
  rw [stackSwap_length]
  simp only [Nat.sub_zero]
  rw [getElem!_eq_getD]
  unfold stackSwap
  rw [getD_set_at_otherpos _ _ _ _ hne hjt, getD_set_at_setpos _ _ _ hit]

/-- `stackSwap dist` sends the old TOS to depth `dist`. -/
theorem stackPeek_dist_stackSwap {dist : Nat} {stk : List Operand} (hpos : 0 < dist)
    (hlt : dist < stk.length) : stackPeek dist (stackSwap dist stk) = stackPeek 0 stk := by
  have hit : stk.length - 1 - dist < (stk.set (stk.length - 1) (stk[stk.length - 1 - dist]!)).length := by
    rw [List.length_set]; omega
  unfold stackPeek
  rw [stackSwap_length]
  simp only [Nat.sub_zero]
  rw [getElem!_eq_getD]
  unfold stackSwap
  rw [getD_set_at_setpos _ _ _ hit]

/-- A nodup list positions any element at its peeked depth: if `stackPeek fd stk = op` then
    `op` has depth `fd` (converse of `stackGetDepth_peek` for nodup lists). -/
theorem stackGetDepth_of_peek_nodup {stk : List Operand} (hnd : stk.Nodup) {fd : Nat}
    (hfd : fd < stk.length) {op : Operand} (hpeek : stackPeek fd stk = op) :
    stackGetDepth op stk = some fd := by
  have hi : stk.length - 1 - fd < stk.length := by omega
  have hsd := stackGetDepth_self_nodup hnd hi
  rw [show stk.length - 1 - (stk.length - 1 - fd) = fd from by omega] at hsd
  have hpeekeq : stk[stk.length - 1 - fd]'hi = op := by
    rw [← hpeek]; unfold stackPeek; rw [getElem!_pos stk _ hi]
  rwa [hpeekeq] at hsd

/-- **`reorderOne` positions `op` at its final depth.** In the 2-swap non-spill case, after
    `reorderOne`, `op` sits at depth `finalDist = targetOps.length - 1 - idx`. -/
theorem reorderOne_positions {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {dist : Nat}
    (hnd : ps.stack.Nodup)
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hne : dist ≠ targetOps.length - 1 - idx)
    (hd0 : dist ≠ 0)
    (hf0 : targetOps.length - 1 - idx ≠ 0)
    (hdlt : dist < ps.stack.length)
    (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    stackGetDepth op (reorderOne () targetOps idx op ps).2.stack = some (targetOps.length - 1 - idx) := by
  set fd := targetOps.length - 1 - idx with hfd
  rw [reorderOne_stack_swap hdepth hne hd0 hdlt hf0 hflt]
  have hop_tos : stackPeek 0 (stackSwap dist ps.stack) = op := by
    rw [stackPeek_zero_stackSwap (by omega) hdlt]; exact stackGetDepth_peek hdepth
  have hnd1 : (stackSwap dist ps.stack).Nodup := (stackSwap_perm dist ps.stack hdlt).nodup_iff.mpr hnd
  have hlen1 : (stackSwap dist ps.stack).length = ps.stack.length := stackSwap_length dist ps.stack
  have hnd2 : (stackSwap fd (stackSwap dist ps.stack)).Nodup :=
    (stackSwap_perm fd (stackSwap dist ps.stack) (by rw [hlen1]; exact hflt)).nodup_iff.mpr hnd1
  have hlen2 : (stackSwap fd (stackSwap dist ps.stack)).length = ps.stack.length := by
    rw [stackSwap_length, hlen1]
  have hpeek_fd : stackPeek fd (stackSwap fd (stackSwap dist ps.stack)) = op := by
    rw [stackPeek_dist_stackSwap (by omega) (by rw [hlen1]; exact hflt), hop_tos]
  exact stackGetDepth_of_peek_nodup hnd2 (by rw [hlen2]; exact hflt) hpeek_fd

/-- `stackSwap s` only touches depths `0` and `s`; any other depth `d` is preserved. -/
theorem stackPeek_stackSwap_ne {s d : Nat} {stk : List Operand}
    (hd0 : d ≠ 0) (hds : d ≠ s) (hdl : d < stk.length) (hsl : s < stk.length) :
    stackPeek d (stackSwap s stk) = stackPeek d stk := by
  have hne1 : stk.length - 1 - s ≠ stk.length - 1 - d := by omega
  have hne2 : stk.length - 1 ≠ stk.length - 1 - d := by omega
  have hj1 : stk.length - 1 - d < (stk.set (stk.length - 1) (stk[stk.length - 1 - s]!)).length := by
    rw [List.length_set]; omega
  unfold stackPeek
  rw [stackSwap_length]
  rw [getElem!_eq_getD, getElem!_eq_getD]
  unfold stackSwap
  rw [getD_set_at_otherpos _ _ _ _ hne1 hj1, getD_set_at_otherpos _ _ _ _ hne2 (by omega)]

/-- **`reorderOne` leaves deeper slots untouched (non-disturbance).** In the 2-swap non-spill case,
    `reorderOne` positions `op` at `finalDist` via two swaps that only touch depths `0`, `dist`, and
    `finalDist`; so any depth `d` deeper than `finalDist` and distinct from `dist` is preserved. This is
    the second half of the general reorder's inductive step: positioning `op[i]` (at the shallower
    `finalDist`) does not disturb the already-positioned deeper `op[0..i-1]` (distinct by nodup). -/
theorem reorderOne_preserves_deep {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {dist d : Nat}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hne : dist ≠ targetOps.length - 1 - idx)
    (hd0 : dist ≠ 0)
    (hf0 : targetOps.length - 1 - idx ≠ 0)
    (hdlt : dist < ps.stack.length)
    (hflt : targetOps.length - 1 - idx < ps.stack.length)
    (hdeep : targetOps.length - 1 - idx < d) (hd_ne_dist : d ≠ dist) (hd_lt : d < ps.stack.length) :
    stackPeek d (reorderOne () targetOps idx op ps).2.stack = stackPeek d ps.stack := by
  set fd := targetOps.length - 1 - idx with hfd
  rw [reorderOne_stack_swap hdepth hne hd0 hdlt hf0 hflt]
  have hlen1 : (stackSwap dist ps.stack).length = ps.stack.length := stackSwap_length dist ps.stack
  rw [stackPeek_stackSwap_ne (by omega) (by omega) (by rw [hlen1]; exact hd_lt) (by rw [hlen1]; exact hflt),
      stackPeek_stackSwap_ne (by omega) hd_ne_dist hd_lt hdlt]

/-- **`reorderOne` plan-stack effect, the `finalDist = 0` (last-op) case.** When the target depth is
    TOS and `op` is elsewhere (`dist ≠ 0 ≤ 16`), `reorderOne` swaps `op` to TOS (the second swap,
    `doSwap 0`, is a no-op): the plan stack becomes `stackSwap dist ps.stack`. The last step of the
    general reorder's fold (target index `numOps-1`, `finalDist = 0`), not covered by
    `reorderOne_stack_swap` (which assumed `finalDist ≠ 0`). -/
theorem reorderOne_stack_tos {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {dist : Nat}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hfd0 : targetOps.length - 1 - idx = 0)
    (hd0 : dist ≠ 0) (hdlt : dist < ps.stack.length) :
    (reorderOne () targetOps idx op ps).2.stack = stackSwap dist ps.stack := by
  unfold reorderOne
  simp only [hdepth, hfd0, if_neg hd0]
  rw [doSwap_stack_zero, doSwap_stack_ne0 hd0 hdlt]

/-- **`reorderOne` positions `op` at TOS in the last-op case (`finalDist = 0`).** Completes the
    per-step positioning coverage for the fold's final step. -/
theorem reorderOne_positions_tos {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    {dist : Nat}
    (hnd : ps.stack.Nodup)
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hfd0 : targetOps.length - 1 - idx = 0)
    (hd0 : dist ≠ 0)
    (hdlt : dist < ps.stack.length) :
    stackGetDepth op (reorderOne () targetOps idx op ps).2.stack = some 0 := by
  rw [reorderOne_stack_tos hdepth hfd0 hd0 hdlt]
  have hnd1 : (stackSwap dist ps.stack).Nodup := (stackSwap_perm dist ps.stack hdlt).nodup_iff.mpr hnd
  have hlen1 : (stackSwap dist ps.stack).length = ps.stack.length := stackSwap_length dist ps.stack
  have hpeek0 : stackPeek 0 (stackSwap dist ps.stack) = op := by
    rw [stackPeek_zero_stackSwap (by omega) hdlt]; exact stackGetDepth_peek hdepth
  exact stackGetDepth_of_peek_nodup hnd1 (by rw [hlen1]; omega) hpeek0

/-- `reorderOne` plan-stack effect when `op` is already at TOS (`dist = 0`, `finalDist ≠ 0`): the first
    swap `doSwap 0` is a no-op, the second sends the TOS to `finalDist`. -/
theorem reorderOne_stack_fromTos {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    (hdepth : stackGetDepth op ps.stack = some 0)
    (hfne : targetOps.length - 1 - idx ≠ 0)
    (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    (reorderOne () targetOps idx op ps).2.stack = stackSwap (targetOps.length - 1 - idx) ps.stack := by
  unfold reorderOne
  simp only [hdepth, if_neg (Ne.symm hfne)]
  rw [doSwap_stack_ne0 (ps := (doSwap 0 ps).2) hfne hflt, doSwap_stack_zero]

/-- `reorderOne` positions `op` at `finalDist` when it starts at TOS (`dist = 0`). -/
theorem reorderOne_positions_fromTos {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    (hnd : ps.stack.Nodup)
    (hdepth : stackGetDepth op ps.stack = some 0)
    (hfne : targetOps.length - 1 - idx ≠ 0)
    (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    stackGetDepth op (reorderOne () targetOps idx op ps).2.stack = some (targetOps.length - 1 - idx) := by
  set fd := targetOps.length - 1 - idx with hfd
  rw [reorderOne_stack_fromTos hdepth hfne hflt]
  have hnd1 : (stackSwap fd ps.stack).Nodup := (stackSwap_perm fd ps.stack hflt).nodup_iff.mpr hnd
  have hlen1 : (stackSwap fd ps.stack).length = ps.stack.length := stackSwap_length fd ps.stack
  have hpeek : stackPeek fd (stackSwap fd ps.stack) = op := by
    rw [stackPeek_dist_stackSwap (by omega) hflt]; exact stackGetDepth_peek hdepth
  exact stackGetDepth_of_peek_nodup hnd1 (by rw [hlen1]; exact hflt) hpeek

/-- **Unified per-step positioning.** For any target index and any `op` present in range
    (`dist < length`, `finalDist < length` — big swaps included), `reorderOne` positions `op` at
    `finalDist`. Cases on the four sub-cases (no-op `dist = finalDist`, last-op `finalDist = 0`,
    already-TOS `dist = 0`, and the general two-swap), dispatching to the specific lemmas. This is the
    clean per-step interface the general reorder's fold consumes. -/
theorem reorderOne_positions_small {targetOps : List Operand} {idx : Nat} {op : Operand}
    {ps : PlanState} {dist : Nat}
    (hnd : ps.stack.Nodup)
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hdlt : dist < ps.stack.length) (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    stackGetDepth op (reorderOne () targetOps idx op ps).2.stack = some (targetOps.length - 1 - idx) := by
  by_cases hdf : dist = targetOps.length - 1 - idx
  · rw [reorderOne_nil_of_positioned (hdf ▸ hdepth)]
    rw [hdf] at hdepth; exact hdepth
  · by_cases hf0 : targetOps.length - 1 - idx = 0
    · rw [hf0]
      exact reorderOne_positions_tos hnd hdepth hf0 (by rw [hf0] at hdf; exact hdf) hdlt
    · by_cases hd0 : dist = 0
      · subst hd0
        exact reorderOne_positions_fromTos hnd hdepth hf0 hflt
      · exact reorderOne_positions hnd hdepth hdf hd0 hf0 hdlt hflt

/-- **Unified per-step non-disturbance (small-swap cases).** `reorderOne` preserves any depth `d`
    deeper than `finalDist` and distinct from `op`'s current depth `dist` — across all four small-swap
    sub-cases. Together with `reorderOne_positions_small`, the full per-step correctness the general
    reorder's fold iterates: position `op[k]` at `finalDist` without disturbing the deeper positioned
    `op[0..k-1]` (distinct from `op[k]` by nodup, hence `d ≠ dist`). -/
theorem reorderOne_preserves_deep_small {targetOps : List Operand} {idx : Nat} {op : Operand}
    {ps : PlanState} {dist d : Nat}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hdlt : dist < ps.stack.length) (hflt : targetOps.length - 1 - idx < ps.stack.length)
    (hdeep : targetOps.length - 1 - idx < d) (hd_ne_dist : d ≠ dist) (hd_lt : d < ps.stack.length) :
    stackPeek d (reorderOne () targetOps idx op ps).2.stack = stackPeek d ps.stack := by
  by_cases hdf : dist = targetOps.length - 1 - idx
  · rw [reorderOne_nil_of_positioned (hdf ▸ hdepth)]
  · by_cases hf0 : targetOps.length - 1 - idx = 0
    · rw [reorderOne_stack_tos hdepth hf0 (by rw [hf0] at hdf; exact hdf) hdlt]
      exact stackPeek_stackSwap_ne (by omega) hd_ne_dist hd_lt hdlt
    · by_cases hd0 : dist = 0
      · subst hd0
        rw [reorderOne_stack_fromTos hdepth hf0 hflt]
        exact stackPeek_stackSwap_ne (by omega) (by omega) hd_lt hflt
      · exact reorderOne_preserves_deep hdepth hdf hd0 hf0 hdlt hflt hdeep hd_ne_dist hd_lt

/-- **`reorderOne` permutes the plan stack (small-swap, on-stack cases).** Since each small `doSwap` is
    a permutation (`stackSwap_perm`) and the no-op leaves the stack, `reorderOne`'s plan stack is a
    permutation of the input — so it preserves `Nodup` and membership (target presence) across the
    fold. -/
theorem reorderOne_perm_small {targetOps : List Operand} {idx : Nat} {op : Operand}
    {ps : PlanState} {dist : Nat}
    (hdepth : stackGetDepth op ps.stack = some dist)
    (hdlt : dist < ps.stack.length) (hflt : targetOps.length - 1 - idx < ps.stack.length) :
    List.Perm (reorderOne () targetOps idx op ps).2.stack ps.stack := by
  by_cases hdf : dist = targetOps.length - 1 - idx
  · rw [reorderOne_nil_of_positioned (hdf ▸ hdepth)]
  · by_cases hf0 : targetOps.length - 1 - idx = 0
    · rw [reorderOne_stack_tos hdepth hf0 (by rw [hf0] at hdf; exact hdf) hdlt]
      exact stackSwap_perm dist ps.stack hdlt
    · by_cases hd0 : dist = 0
      · subst hd0
        rw [reorderOne_stack_fromTos hdepth hf0 hflt]
        exact stackSwap_perm _ ps.stack hflt
      · rw [reorderOne_stack_swap hdepth hdf hd0 hdlt hf0 hflt]
        have hlen1 : (stackSwap dist ps.stack).length = ps.stack.length := stackSwap_length dist ps.stack
        exact (stackSwap_perm _ (stackSwap dist ps.stack) (by rw [hlen1]; exact hflt)).trans
          (stackSwap_perm dist ps.stack hdlt)

/-- **Fold step: one `reorderOne` extends the positioned prefix.** Processing target index `k`
    (op = `targetOps[k]`) where `targetOps[0..k-1]` are
    already positioned at depths `numOps-1-i`, positions `targetOps[k]` at `numOps-1-k`
    (reorderOne_positions_small) without disturbing `targetOps[0..k-1]` (they sit deeper than
    `finalDist` and are distinct from `targetOps[k]` by nodup, so reorderOne_preserves_deep_small
    applies) — the positioned prefix grows to `k+1`. The inductive step of the general reorder (any
    stack depth). -/
theorem reorderPlan_step {targetOps : List Operand} {ps : PlanState} {k dist : Nat}
    (hndT : targetOps.Nodup) (hnd : ps.stack.Nodup)
    (hk : k < targetOps.length)
    (hlen : targetOps.length ≤ ps.stack.length)
    (hdepth : stackGetDepth (targetOps[k]'hk) ps.stack = some dist)
    (hinv : ∀ i (hi : i < targetOps.length), i < k →
      stackGetDepth (targetOps[i]'hi) ps.stack = some (targetOps.length - 1 - i)) :
    ∀ i (hi : i < targetOps.length), i < k + 1 →
      stackGetDepth (targetOps[i]'hi) (reorderOne () targetOps k (targetOps[k]'hk) ps).2.stack
        = some (targetOps.length - 1 - i) := by
  have hdlt : dist < ps.stack.length := stackGetDepth_lt_length hdepth
  have hflt : targetOps.length - 1 - k < ps.stack.length := by omega
  have hperm := reorderOne_perm_small hdepth hdlt hflt
  have hnd' : (reorderOne () targetOps k (targetOps[k]'hk) ps).2.stack.Nodup := hperm.nodup_iff.mpr hnd
  have hlenEq : (reorderOne () targetOps k (targetOps[k]'hk) ps).2.stack.length = ps.stack.length :=
    hperm.length_eq
  intro i hi hik
  by_cases hik' : i = k
  · subst hik'
    exact reorderOne_positions_small hnd hdepth hdlt hflt
  · have hik2 : i < k := by omega
    have hposi := hinv i hi hik2
    have hpeeki : stackPeek (targetOps.length - 1 - i) ps.stack = targetOps[i]'hi :=
      stackGetDepth_peek hposi
    have hilen : targetOps.length - 1 - i < ps.stack.length := stackGetDepth_lt_length hposi
    have hnedist : targetOps.length - 1 - i ≠ dist := by
      intro heq
      have h1 := stackGetDepth_peek hdepth
      rw [← heq, hpeeki] at h1
      exact hik' ((List.Nodup.getElem_inj_iff hndT).mp h1)
    have hpres := reorderOne_preserves_deep_small hdepth hdlt hflt (by omega) hnedist hilen
    rw [hpeeki] at hpres
    exact stackGetDepth_of_peek_nodup hnd' (by rw [hlenEq]; exact hilen) hpres

/-- Any operand present on the stack has a depth (the general `stackGetDepth_of_mem`, for any
    `Operand`, not just `Var`). Supplies `reorderPlan_step`'s `hdepth` in the fold: each target is
    present (membership preserved by `reorderOne_perm_small`), so it has a current depth. -/
theorem stackGetDepth_of_mem_op {op : Operand} {stk : List Operand} (h : op ∈ stk) :
    ∃ d, stackGetDepth op stk = some d ∧ d < stk.length := by
  unfold stackGetDepth
  have hex : ∃ a, a ∈ stk.reverse ∧ (a == op) = true := ⟨op, by rwa [List.mem_reverse], by simp⟩
  obtain ⟨d, hd, hlt⟩ := stackFind_isSome hex
  rw [List.length_reverse] at hlt
  exact ⟨d, hd, hlt⟩

/-! ### General reorder fold: `reorderPlan` synthesises the target layout (`perm_reaches`)

Threading the per-step positioning + non-disturbance (`reorderPlan_step`) over `reorderPlan`'s
`targetOps.enum.foldl` with the structural invariant (nodup / length / target presence preserved by
`reorderOne_perm_small`), at **arbitrary** stack depth — big swaps (`doSwap_stack_big`) included. -/

/-- The `reorderPlan` fold body (over `(idx, op)` pairs), abstracted for the induction. -/
def roStep (targetOps : List Operand) (a : List StackOp × PlanState) (p : Nat × Operand) :
    List StackOp × PlanState :=
  (a.1 ++ (reorderOne () targetOps p.1 p.2 a.2).1, (reorderOne () targetOps p.1 p.2 a.2).2)

theorem reorderPlan_fold_aux (targetOps : List Operand) (hndT : targetOps.Nodup) :
    ∀ (L : List (Nat × Operand)) (start : Nat) (acc : List StackOp × PlanState),
    (∀ j (hj : j < L.length), L[j]'hj = (start + j, targetOps[start + j]!)) →
    start + L.length = targetOps.length →
    acc.2.stack.Nodup → targetOps.length ≤ acc.2.stack.length →
    (∀ t ∈ targetOps, t ∈ acc.2.stack) →
    (∀ i (hi : i < targetOps.length), i < start →
      stackGetDepth (targetOps[i]'hi) acc.2.stack = some (targetOps.length - 1 - i)) →
    ∀ i (hi : i < targetOps.length),
      stackGetDepth (targetOps[i]'hi) (L.foldl (roStep targetOps) acc).2.stack
        = some (targetOps.length - 1 - i) := by
  intro L
  induction L with
  | nil =>
    intro start acc _ hsum _ _ _ hinv i hi
    simp only [List.foldl_nil]
    exact hinv i hi (by simp only [List.length_nil, Nat.add_zero] at hsum; omega)
  | cons hd rest ih =>
    intro start acc hchar hsum hnd hlen hpres hinv i hi
    have hhd : hd = (start, targetOps[start]!) := by
      have := hchar 0 (by simp); simpa using this
    have hstartlt : start < targetOps.length := by simp only [List.length_cons] at hsum; omega
    have hidx : targetOps[start]'hstartlt = targetOps[start]! := (getElem!_pos targetOps start hstartlt).symm
    have hmem_t : targetOps[start]! ∈ targetOps := by rw [← hidx]; exact List.getElem_mem hstartlt
    have hopmem : targetOps[start]! ∈ acc.2.stack := hpres _ hmem_t
    obtain ⟨dist, hdepth, hdlt⟩ := stackGetDepth_of_mem_op hopmem
    have hdepth' : stackGetDepth (targetOps[start]'hstartlt) acc.2.stack = some dist := by
      rw [hidx]; exact hdepth
    have hgrow := reorderPlan_step hndT hnd hstartlt hlen hdepth' hinv
    rw [hidx] at hgrow
    have hperm := reorderOne_perm_small (targetOps := targetOps) (idx := start)
      (op := targetOps[start]!) hdepth hdlt (by omega)
    have hnd1 := hperm.nodup_iff.mpr hnd
    have hlenEq := hperm.length_eq
    have hpres1 : ∀ t ∈ targetOps, t ∈ (reorderOne () targetOps start (targetOps[start]!) acc.2).2.stack :=
      fun t ht => (hperm.mem_iff).mpr (hpres t ht)
    have hchar' : ∀ j (hj : j < rest.length),
        rest[j]'hj = (start + 1 + j, targetOps[start + 1 + j]!) := by
      intro j hj
      have := hchar (j + 1) (by simp only [List.length_cons]; omega)
      simpa [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using this
    rw [List.foldl_cons, hhd]
    exact ih (start + 1) (roStep targetOps acc (start, targetOps[start]!)) hchar'
      (by simp only [List.length_cons] at hsum; omega)
      hnd1 (by simp only [roStep]; rw [hlenEq]; exact hlen) hpres1 hgrow i hi

theorem enum_length_op (l : List Operand) : l.enum.length = l.length := by
  simp only [List.enum, List.length_map, List.length_zipIdx]

theorem enum_getElem_op (l : List Operand) (j : Nat) (hj : j < l.length) :
    l.enum[j]'(by rw [enum_length_op]; exact hj) = (j, l[j]'hj) := by
  simp only [List.enum]
  rw [List.getElem_map, List.getElem_zipIdx]
  simp

/-- **`reorderPlan` positions every target (`perm_reaches`).** On any stack (big swaps included)
    holding all of the nodup `targetOps`, `reorderPlan targetOps ps` leaves each
    `targetOps[i]` at depth `numOps-1-i` — i.e. the top `numOps` of the stack are exactly `targetOps`.
    The general reorder synthesises the target layout from any permutation. Instantiates the fold aux
    (`reorderPlan_fold_aux`) with the full `enum` (`start = 0`, prefix vacuous). -/
theorem reorderPlan_positions (targetOps : List Operand) (ps : PlanState)
    (hndT : targetOps.Nodup)
    (hnd : ps.stack.Nodup)
    (hlen : targetOps.length ≤ ps.stack.length)
    (hpres : ∀ t ∈ targetOps, t ∈ ps.stack) :
    ∀ i (hi : i < targetOps.length),
      stackGetDepth (targetOps[i]'hi) (reorderPlan targetOps ps).2.stack
        = some (targetOps.length - 1 - i) := by
  have hfold : reorderPlan targetOps ps = targetOps.enum.foldl (roStep targetOps) ([], ps) := rfl
  rw [hfold]
  refine reorderPlan_fold_aux targetOps hndT targetOps.enum 0 ([], ps) ?_ ?_ hnd hlen hpres ?_
  · intro j hj
    rw [enum_length_op] at hj
    rw [enum_getElem_op targetOps j hj, Nat.zero_add]
    congr 1
    exact (getElem!_pos targetOps j hj).symm
  · rw [Nat.zero_add, enum_length_op]
  · intro i hi hi0; omega

/-- **Join reorder synthesises the target entry layout.** The completed general reorder
    (`reorderPlan_positions`) as a *stack-shape* fact: after `reorderPlan targetOps ps`, the top
    `targetOps.length` slots of the plan stack (its length-`T` suffix, LAST=TOS) are exactly `targetOps`
    in order. This is the join-point `psOf` fact — at a multi-pred join, the predecessor's JMP runs
    `joinOps = reorderPlan (targetStack.map Var)`, and this shows the resulting exit stack's top region
    equals the join target's fixed entry stack `targetStack.map Var = psOf target`. Combined with the
    tree-edge fact (`generateSuccsPlan_first_succ_prefix`, exit = entry directly) it discharges
    `psPostBody = psOf bb'` for both edge kinds. -/
theorem reorderPlan_stack_suffix_eq_target (targetOps : List Operand) (ps : PlanState)
    (hndT : targetOps.Nodup) (hnd : ps.stack.Nodup)
    (hlen : targetOps.length ≤ ps.stack.length)
    (hpres : ∀ t ∈ targetOps, t ∈ ps.stack) :
    (reorderPlan targetOps ps).2.stack.drop
      ((reorderPlan targetOps ps).2.stack.length - targetOps.length) = targetOps := by
  have hpos := reorderPlan_positions targetOps ps hndT hnd hlen hpres
  set stk := (reorderPlan targetOps ps).2.stack with hstk
  have hMT : targetOps.length ≤ stk.length := by
    rcases Nat.eq_zero_or_pos targetOps.length with h0 | hp
    · omega
    · have := stackGetDepth_lt_length (hpos 0 hp); omega
  apply List.ext_getElem
  · rw [List.length_drop]; omega
  · intro i h1 h2
    rw [List.length_drop] at h1
    have hi : i < targetOps.length := by omega
    have hpeek : stackPeek (targetOps.length - 1 - i) stk = targetOps[i]'hi :=
      stackGetDepth_peek (hpos i hi)
    rw [List.getElem_drop]
    have hidx : stk.length - targetOps.length + i = stk.length - 1 - (targetOps.length - 1 - i) := by omega
    have hval : stk[stk.length - targetOps.length + i] = stk[stk.length - targetOps.length + i]! :=
      (getElem!_pos _ _ (by omega)).symm
    rw [hval, hidx]
    exact hpeek

/-! ### Nodup-free, base-preserving `perm_reaches` (`List.Perm` route)

`reorderPlan_stack_suffix_eq_target` gives the *suffix* (top `targetOps.length` slots) under **nodup**
hypotheses. The lemmas below give the complementary **full-stack, base-preserving** form
`reorderPlan T (base ++ perm) = base ++ T` for a stack that is exactly `base ++ perm` with `perm` any
permutation of `T` — with **no nodup**, by running the whole argument at the `List.Perm` level: each
`reorderOne` moves the located operand to the deepest active slot (the boundary with `base`), only
permuting the active segment (`reorderOne_perm_step`), and the fold shrinks the segment by one via
`List.Perm.cons_inv`. This is the form a JMP-join predecessor's exact live-var config feeds. -/

/-- The element at depth `d` comes to the TOS after `stackSwap d`. -/
theorem stackSwap_tos_getElem (l : List Operand) (d : Nat) (hd : d < l.length) :
    (stackSwap d l)[l.length - 1]! = l[l.length - 1 - d]! := by
  show ((l.set (l.length - 1) l[l.length - 1 - d]!).set (l.length - 1 - d) l[l.length - 1]!)[l.length - 1]! = _
  by_cases hd0 : d = 0
  · subst hd0; simp only [Nat.sub_zero, List.set_set]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]; rfl

/-- The TOS (`l[len-1]`) lands at index 0 after `stackSwap (len-1)`. -/
theorem stackSwap_index0_getElem (l : List Operand) (hl : 0 < l.length) :
    (stackSwap (l.length - 1) l)[0]! = l[l.length - 1]! := by
  show ((l.set (l.length - 1) l[l.length - 1 - (l.length - 1)]!).set
        (l.length - 1 - (l.length - 1)) l[l.length - 1]!)[0]! = _
  simp only [show l.length - 1 - (l.length - 1) = 0 from by omega]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by simp only [List.length_set]; exact hl)]; rfl

/-- The element at depth `d` lands at index 0 (the deepest slot) after the two swaps `stackSwap (len-1)
    ∘ stackSwap d` — the reorder rotation-to-final-slot. -/
theorem stackSwap_double_index0 (l : List Operand) (d : Nat) (hd : d < l.length) :
    (stackSwap (l.length - 1) (stackSwap d l))[0]! = l[l.length - 1 - d]! := by
  have hsl : (stackSwap d l).length = l.length := stackSwap_length d l
  have h1 : (stackSwap ((stackSwap d l).length - 1) (stackSwap d l))[0]!
      = (stackSwap d l)[(stackSwap d l).length - 1]! :=
    stackSwap_index0_getElem (stackSwap d l) (by rw [hsl]; omega)
  rw [hsl] at h1
  rw [h1, stackSwap_tos_getElem l d hd]

/-- `stackGetDepth` found in the top segment `rem` carries over to `low ++ rem` (rem is searched from
    the TOS first). -/
theorem stackGetDepth_append_right {op : Operand} {low rem : List Operand} {d : Nat}
    (h : stackGetDepth op rem = some d) : stackGetDepth op (low ++ rem) = some d := by
  unfold stackGetDepth at h ⊢
  rw [List.reverse_append]
  exact stackFind_append_left h

theorem stackFind_isSome_of_mem {op : Operand} :
    ∀ {L : List Operand}, op ∈ L → ∃ d, stackFind (·== op) L = some d := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons x xs ih =>
    intro h
    simp only [stackFind]
    by_cases hx : x == op
    · exact ⟨0, by rw [if_pos hx]⟩
    · rw [if_neg hx]
      simp only [List.mem_cons] at h
      rcases h with rfl | hm
      · simp at hx
      · obtain ⟨d, hd⟩ := ih hm; exact ⟨d + 1, by rw [hd]⟩

/-- Any `op ∈ rem` has a `stackGetDepth` (found at some depth from the TOS). -/
theorem stackGetDepth_isSome_of_mem {op : Operand} {rem : List Operand} (h : op ∈ rem) :
    ∃ d, stackGetDepth op rem = some d := by
  unfold stackGetDepth
  exact stackFind_isSome_of_mem (by simpa using h)

/-- **One arbitrary-permutation reorder step.** For a stack `low ++ rem` with `op` located in the active
    segment `rem` (at depth `d`) and the final depth pinned to the deepest slot (`finalDist =
    rem.length - 1`), `reorderOne` moves `op` to the boundary (top of `low`): the result is
    `low ++ (op :: rem')` where `op :: rem'` is a permutation of `rem`. The reorder only permutes `rem`
    (all cases: positioned / TOS / two-swap), so the base `low` is untouched. No nodup needed. -/
theorem reorderOne_perm_step {T low rem : List Operand} {op : Operand} {ps : PlanState} {idx d : Nat}
    (hstk : ps.stack = low ++ rem)
    (hdep : stackGetDepth op rem = some d)
    (hfd : T.length - 1 - idx = rem.length - 1) :
    ∃ rem', (reorderOne () T idx op ps).2.stack = low ++ (op :: rem') ∧ List.Perm (op :: rem') rem := by
  have hdlt : d < rem.length := stackGetDepth_lt_length hdep
  have hm1 : 1 ≤ rem.length := by omega
  have hdep_full : stackGetDepth op ps.stack = some d := by
    rw [hstk]; exact stackGetDepth_append_right hdep
  have hopeek : rem[rem.length - 1 - d]! = op := stackGetDepth_peek hdep
  have hstklen : ps.stack.length = low.length + rem.length := by rw [hstk]; simp
  have hfd_lt : T.length - 1 - idx < ps.stack.length := by rw [hfd, hstklen]; omega
  have hR : ∃ R, (reorderOne () T idx op ps).2.stack = low ++ R ∧ List.Perm R rem ∧ R[0]! = op ∧ 1 ≤ R.length := by
    by_cases hcase : d = rem.length - 1
    · refine ⟨rem, ?_, List.Perm.refl _, ?_, hm1⟩
      · have hro : (reorderOne () T idx op ps) = ([], ps) := by
          unfold reorderOne; simp only [hdep_full]
          rw [if_pos (show d = T.length - 1 - idx from by rw [hfd]; exact hcase)]
        rw [hro]; exact hstk
      · rw [show (0:Nat) = rem.length - 1 - d from by omega]; exact hopeek
    · by_cases hd0 : d = 0
      · refine ⟨stackSwap (rem.length - 1) rem, ?_, stackSwap_perm (rem.length - 1) rem (by omega), ?_,
            by simp only [stackSwap_length]; exact hm1⟩
        · rw [reorderOne_tos_stack (by rw [← hd0]; exact hdep_full) hfd_lt, hfd, hstk,
              stackSwap_append_right low rem (rem.length - 1) (by omega)]
        · rw [stackSwap_index0_getElem rem (by omega), show rem.length - 1 = rem.length - 1 - d from by omega]
          exact hopeek
      · have hf0 : T.length - 1 - idx ≠ 0 := by rw [hfd]; omega
        refine ⟨stackSwap (rem.length - 1) (stackSwap d rem), ?_, ?_, ?_,
            by simp only [stackSwap_length]; exact hm1⟩
        · rw [reorderOne_stack_swap hdep_full (show d ≠ T.length - 1 - idx from by rw [hfd]; exact hcase)
                hd0 (by rw [hstklen]; omega) hf0 hfd_lt, hfd, hstk,
              stackSwap_append_right low rem d (by omega),
              stackSwap_append_right low (stackSwap d rem) (rem.length - 1) (by rw [stackSwap_length]; omega)]
        · exact (stackSwap_perm (rem.length - 1) (stackSwap d rem) (by rw [stackSwap_length]; omega)).trans
            (stackSwap_perm d rem (by omega))
        · rw [stackSwap_double_index0 rem d hdlt]; exact hopeek
  obtain ⟨R, hRstk, hRperm, hRhead, hRlen⟩ := hR
  cases R with
  | nil => simp at hRlen
  | cons r0 rs =>
    have hr0 : r0 = op := by simpa using hRhead
    subst hr0
    exact ⟨rs, hRstk, hRperm⟩

/-- **The fold invariant for an arbitrary permutation.** From a stack `base ++ pre ++ rem` where `rem`
    is any permutation of the remaining target `suf`, processing the tail of the `reorderPlan` fold
    yields `base ++ pre ++ suf = base ++ T`. Each step moves the next target var from `rem` to the
    boundary (`reorderOne_perm_step`), shrinking `rem` to a permutation of the shorter tail
    (`List.Perm.cons_inv`). No nodup needed. -/
theorem reorderPlan_perm_aux (T base : List Operand) :
    ∀ (suf pre rem : List Operand) (acc : List StackOp) (ps : PlanState),
    T = pre ++ suf →
    List.Perm rem suf →
    ps.stack = base ++ pre ++ rem →
    (List.foldl (fun (a : List StackOp × PlanState) (p : Operand × Nat) =>
       (a.1 ++ (reorderOne () T p.2 p.1 a.2).1, (reorderOne () T p.2 p.1 a.2).2))
       (acc, ps) (suf.zipIdx pre.length)).2.stack = base ++ T := by
  intro suf
  induction suf with
  | nil =>
    intro pre rem acc ps hT hperm hstk
    simp only [List.zipIdx_nil, List.foldl_nil]
    have hrnil : rem = [] := List.perm_nil.mp hperm
    rw [hstk, hrnil, hT]; simp
  | cons op rest ih =>
    intro pre rem acc ps hT hperm hstk
    rw [show (op :: rest).zipIdx pre.length = (op, pre.length) :: rest.zipIdx (pre.length + 1) from rfl,
        List.foldl_cons]
    have hopmem : op ∈ rem := hperm.mem_iff.mpr (List.mem_cons_self)
    obtain ⟨d, hdep⟩ := stackGetDepth_isSome_of_mem hopmem
    have hfd : T.length - 1 - pre.length = rem.length - 1 := by
      have h1 : T.length = pre.length + rem.length := by
        rw [hT]; simp only [List.length_append]; rw [hperm.length_eq]
      omega
    obtain ⟨rem', hrstk, hrperm⟩ :=
      reorderOne_perm_step (T := T) (low := base ++ pre) (idx := pre.length)
        (by rw [hstk]) hdep hfd
    have hrem'rest : List.Perm rem' rest := (hrperm.trans hperm).cons_inv
    have hps'stk : (reorderOne () T pre.length op ps).2.stack = base ++ (pre ++ [op]) ++ rem' := by
      rw [hrstk]; simp [List.append_assoc]
    have hrec := ih (pre ++ [op]) rem' (acc ++ (reorderOne () T pre.length op ps).1)
      (reorderOne () T pre.length op ps).2 (by rw [hT]; simp) hrem'rest hps'stk
    rw [show pre.length + 1 = (pre ++ [op]).length from by simp]
    exact hrec

/-- **General join reconciliation for an arbitrary permutation (`perm_reaches`).** For any target entry
    layout `T` and a predecessor leaving **any permutation** `perm` of `T` on the stack
    (`base ++ perm`), `reorderPlan T` synthesises the target layout `base ++ T`. The nodup-free,
    base-preserving companion of `reorderPlan_stack_suffix_eq_target`; unlike `reorderPlan_rotate`
    (rotations only), the operand to place need not be at the TOS, so `reorderOne` locates it at its
    depth (`stackGetDepth_isSome_of_mem`) and swaps it to the boundary. The whole argument runs at the
    `List.Perm` level, so **no distinctness / nodup** is needed. -/
theorem reorderPlan_perm (T base perm : List Operand) (ps : PlanState)
    (hperm : List.Perm perm T)
    (hstk : ps.stack = base ++ perm) :
    (reorderPlan T ps).2.stack = base ++ T := by
  unfold reorderPlan
  rw [show T.enum = (T.zipIdx 0).map (fun p => (p.2, p.1)) from rfl, List.foldl_map]
  exact reorderPlan_perm_aux T base T [] perm [] ps (by simp) hperm (by simpa using hstk)

/-- **venomAsmRel-level join reconciliation.** Combines the plan-stack result `reorderPlan_perm` (the
    reorder synthesises the successor's entry layout `base ++ targetOps` from any permutation `perm`) with
    the asm-side sim `reorderPlan_sim` (the emitted SWAP/restore ops run to `AsmOK`, preserving
    `venomAsmRel`). For a JMP-join whose predecessor leaves `base ++ perm` on the stack, the join reorder
    lands the plan stack at `base ++ targetOps` AND advances the asm state in lock-step — exactly the
    reconciliation a genuine (non-identity) join needs. The per-`reorderOne` asm step `hstep` is carried
    (discharged per reorder via `reorderOne_sim_positioned` / `reorderOne_sim_swap`). -/
theorem reorderPlan_join_sim {targetOps base perm : List Operand} {ps ps' : PlanState}
    {ops : List StackOp} {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hperm : List.Perm perm targetOps)
    (hpsstk : ps.stack = base ++ perm)
    (hreorder : reorderPlan targetOps ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hstep : ∀ (i : Nat × Operand) (p : PlanState) (s : AsmState),
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (reorderOne () targetOps i.1 i.2 p).1) →
        ∃ s', runAsm (executePlan (reorderOne () targetOps i.1 i.2 p).1).length
                offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (reorderOne () targetOps i.1 i.2 p).2 vs s' ∧
              s'.pc = s.pc + (executePlan (reorderOne () targetOps i.1 i.2 p).1).length) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧ ps'.stack = base ++ targetOps ∧
           as'.pc = as.pc + (executePlan ops).length := by
  obtain ⟨as', hrun, hrel', hpc⟩ := reorderPlan_sim hreorder hrel hblock hstep
  have hstk : ps'.stack = base ++ targetOps := by
    have h := reorderPlan_perm targetOps base perm ps hperm hpsstk
    rw [hreorder] at h; exact h
  exact ⟨as', hrun, hrel', hstk, hpc⟩

/-- **Residual asm run for a genuine JMP-join: reorder + push-label + JUMP.** From a predecessor whose
    stack is `base ++ perm` (perm any permutation of the target block's entry layout `targetOps`), the
    join `reorderPlan targetOps` runs its SWAP/restore ops (`reorderPlan_join_sim` — landing the plan
    stack at `base ++ targetOps` and preserving `venomAsmRel`), then the resolved `push-label ; JUMP`
    runs two more steps to the successor's pc `idx` (`resolved_jump_sim`, `venomAsmRel_setPc`). This is
    the genuine-reorder counterpart of `hasm_regularHN_jmp` (which handles only the no-reorder join). The
    per-`reorderOne` asm step `hstep` is carried (swap case needs the no-spill invariant, gap C). -/
theorem hasm_jmp_reorder {targetOps base perm : List Operand} {ps ps' : PlanState}
    {jOps : List StackOp} {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {target : String} {off idx : Nat}
    (hperm : List.Perm perm targetOps)
    (hpsstk : ps.stack = base ++ perm)
    (hreorder : reorderPlan targetOps ps = (jOps, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblockJ : asmBlockAt prog as.pc (executePlan jOps))
    (hstep : ∀ (i : Nat × Operand) (p : PlanState) (s : AsmState),
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (reorderOne () targetOps i.1 i.2 p).1) →
        ∃ s', runAsm (executePlan (reorderOne () targetOps i.1 i.2 p).1).length
                offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (reorderOne () targetOps i.1 i.2 p).2 vs s' ∧
              s'.pc = s.pc + (executePlan (reorderOne () targetOps i.1 i.2 p).1).length)
    (hpc1 : as.pc + (executePlan jOps).length < prog.length)
    (hpush : prog.get ⟨as.pc + (executePlan jOps).length, hpc1⟩
        = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + (executePlan jOps).length + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + (executePlan jOps).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ as', runAsm ((executePlan jOps).length + 2) offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧ ps'.stack = base ++ targetOps ∧ as'.pc = idx := by
  obtain ⟨asReord, hrunJ, hrelJ, hstk, hpcJ⟩ :=
    reorderPlan_join_sim hperm hpsstk hreorder hrel hblockJ hstep
  have hpc1' : asReord.pc < prog.length := by rw [hpcJ]; exact hpc1
  have hpush' : prog.get ⟨asReord.pc, hpc1'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target) := by
    rw [show (⟨asReord.pc, hpc1'⟩ : Fin _) = ⟨as.pc + (executePlan jOps).length, hpc1⟩ from Fin.ext hpcJ]
    exact hpush
  have hpc2' : asReord.pc + 1 < prog.length := by rw [hpcJ]; exact hpc2
  have hjump' : prog.get ⟨asReord.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" := by
    have e : asReord.pc + 1 = as.pc + (executePlan jOps).length + 1 := by rw [hpcJ]
    conv_lhs => rw [show (⟨asReord.pc + 1, hpc2'⟩ : Fin prog.length)
      = ⟨as.pc + (executePlan jOps).length + 1, hpc2⟩ from Fin.ext e]
    exact hjump
  have hjrun : runAsm 2 offsetToPc prog asReord = AsmResult.AsmOK { asReord with pc := idx } :=
    resolved_jump_sim hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk
  refine ⟨{ asReord with pc := idx }, ?_, venomAsmRel_setPc hrelJ, hstk, rfl⟩
  rw [runAsm_add_ok hrunJ]; exact hjrun

/-- Small `doSwap` (`dist ≤ 16`) leaves the spill map untouched (only the stack is swapped). -/
theorem doSwap_bounded_spilled {dist : Nat} {ps : PlanState} (h : dist ≤ 16) :
    (doSwap dist ps).2.spilled = ps.spilled := by
  unfold doSwap
  by_cases h0 : dist = 0
  · simp [h0]
  · rw [if_neg h0, if_pos h]

/-- `reorderOne` on a bounded on-stack operand leaves the spill map untouched (its two `doSwap`s are
    small). -/
theorem reorderOne_onstack_spilled {targetOps : List Operand} {idx : Nat} {op : Operand}
    {ps : PlanState} {dist : Nat}
    (hdist : stackGetDepth op ps.stack = some dist)
    (hd16 : dist ≤ 16) (hf16 : targetOps.length - 1 - idx ≤ 16) :
    (reorderOne () targetOps idx op ps).2.spilled = ps.spilled := by
  unfold reorderOne
  simp only [hdist]
  by_cases hpos : dist = targetOps.length - 1 - idx
  · rw [if_pos hpos]
  · rw [if_neg hpos, doSwap_bounded_spilled hf16, doSwap_bounded_spilled hd16]

/-- `reorderOne` is a no-op when the operand is neither on the stack nor spilled. -/
theorem reorderOne_offstack_noop {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    (hnone : stackGetDepth op ps.stack = none)
    (hnospill : alookup' ps.spilled op = none) :
    reorderOne () targetOps idx op ps = ([], ps) := by
  unfold reorderOne
  simp only [hnone, hnospill]

/-- **Bounded genuine-reorder join asm sim.** For a predecessor stack `base ++ perm` (perm any
    permutation of the target layout `targetOps`) bounded by 17 with no spills, `reorderPlan targetOps`
    runs on the asm side to `AsmOK`, landing the plan stack at `base ++ targetOps` with `venomAsmRel`
    preserved — **discharging** the per-`reorderOne` step *internally* (no carried `hstep`, unlike
    `reorderPlan_join_sim`). Combines the invariant harness `foldl_ops_sim_inv` (invariant: stack length
    fixed + no spills ⇒ every swap distance `≤ 16`) fed the per-step `reorderOne_asm_bounded` — whose
    `hInvStep` is `reorderOne_perm_small` (length) + `reorderOne_onstack_spilled` (no-spill preserved),
    and whose off-stack case is `reorderOne_offstack_noop` — with `reorderPlan_perm` for the plan-stack
    result. This is the full genuine (non-identity) JMP-join reorder for the realistic bounded-stack
    case (the reorder region being the target's `≤ 16` live vars): `reorderPlan_sim`'s `∀ p` `hstep`,
    undischargeable for genuine swaps, is replaced by the reachable-state invariant. -/
theorem reorderPlan_join_bounded {targetOps base perm : List Operand} {ps ps' : PlanState}
    {ops : List StackOp} {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hperm : List.Perm perm targetOps)
    (hpsstk : ps.stack = base ++ perm)
    (hbound : (base ++ perm).length ≤ 17)
    (hnospill : ∀ o, alookup' ps.spilled o = none)
    (hreorder : reorderPlan targetOps ps = (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧ ps'.stack = base ++ targetOps ∧
           as'.pc = as.pc + (executePlan ops).length := by
  set N := (base ++ perm).length with hN
  set Inv : PlanState → Prop := fun p =>
    p.stack.length = N ∧ (∀ o, alookup' p.spilled o = none) with hInvDef
  have htgtN : targetOps.length ≤ N := by rw [hN, ← hperm.length_eq]; simp
  have hpslen : ps.stack.length = N := by rw [hpsstk]
  have hstep : ∀ (a : Nat × Operand) (p : PlanState) (s : AsmState),
      Inv p → venomAsmRel lo p vs s →
      asmBlockAt prog s.pc (executePlan (reorderOne () targetOps a.1 a.2 p).1) →
      ∃ s', runAsm (executePlan (reorderOne () targetOps a.1 a.2 p).1).length offsetToPc prog s
              = AsmResult.AsmOK s' ∧
            venomAsmRel lo (reorderOne () targetOps a.1 a.2 p).2 vs s' ∧
            s'.pc = s.pc + (executePlan (reorderOne () targetOps a.1 a.2 p).1).length := by
    intro a p s hInv hrelp hblockp
    obtain ⟨hlenp, hspp⟩ := hInv
    by_cases hmem : ∃ d, stackGetDepth a.2 p.stack = some d
    · obtain ⟨d, hd⟩ := hmem
      have hdlt : d < p.stack.length := stackGetDepth_lt_length hd
      exact reorderOne_asm_bounded hd (by omega) (by omega) (by omega) hrelp hblockp
    · have hnone : stackGetDepth a.2 p.stack = none := by
        cases h : stackGetDepth a.2 p.stack with
        | none => rfl
        | some d => exact absurd ⟨d, h⟩ hmem
      rw [reorderOne_offstack_noop hnone (hspp a.2)]
      exact ⟨s, by simp [executePlan, runAsm], by simpa using hrelp, by simp [executePlan]⟩
  have hInvStep : ∀ (a : Nat × Operand) (p : PlanState), Inv p → Inv (reorderOne () targetOps a.1 a.2 p).2 := by
    intro a p hInv
    obtain ⟨hlenp, hspp⟩ := hInv
    by_cases hmem : ∃ d, stackGetDepth a.2 p.stack = some d
    · obtain ⟨d, hd⟩ := hmem
      have hdlt : d < p.stack.length := stackGetDepth_lt_length hd
      have hflt : targetOps.length - 1 - a.1 < p.stack.length := by omega
      have hperm2 := reorderOne_perm_small hd hdlt hflt
      exact ⟨by rw [hperm2.length_eq]; exact hlenp,
             by rw [reorderOne_onstack_spilled hd (by omega) (by omega)]; exact hspp⟩
    · have hnone : stackGetDepth a.2 p.stack = none := by
        cases h : stackGetDepth a.2 p.stack with
        | none => rfl
        | some d => exact absurd ⟨d, h⟩ hmem
      rw [reorderOne_offstack_noop hnone (hspp a.2)]
      exact ⟨hlenp, hspp⟩
  have hrp : reorderPlan targetOps ps = targetOps.enum.foldl
      (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                     (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps) := by
    unfold reorderPlan; congr 1
  have hfold : targetOps.enum.foldl
      (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                     (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps) = (ops, ps') := by
    rw [← hrp]; exact hreorder
  have he1 : (targetOps.enum.foldl (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps)).1 = ops := congrArg Prod.fst hfold
  have he2 : (targetOps.enum.foldl (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps)).2 = ps' := congrArg Prod.snd hfold
  obtain ⟨as', hrun, hrel', hpc⟩ :=
    foldl_ops_sim_inv lo vs prog offsetToPc
      (fun (p : PlanState) (a : Nat × Operand) => reorderOne () targetOps a.1 a.2 p)
      Inv hInvStep hstep targetOps.enum ps as ⟨hpslen, hnospill⟩ hrel (by rw [he1]; exact hblock)
  rw [he1] at hrun hpc
  rw [he2] at hrel'
  have hstk : ps'.stack = base ++ targetOps := by
    have h := reorderPlan_perm targetOps base perm ps hperm hpsstk
    rw [hreorder] at h; exact h
  exact ⟨as', hrun, hrel', hstk, hpc⟩

/-- **Fully-discharged reorder runner for a KNOWN plan equation** (bounded stack, no spills):
    given `reorderPlan targetOps ps = (ops, ps')` — e.g. from the general one-double atoms
    `reorderPlan_{lastspilled,midspilled}` — the emitted swaps run on the asm side preserving
    `venomAsmRel`, with the per-`reorderOne` discharge threaded internally. The permutation-free
    sibling of `reorderPlan_join_bounded`; makes every arity's doubles-reorder executable. -/
theorem reorderPlan_run_bounded {targetOps : List Operand} {ps ps' : PlanState}
    {ops : List StackOp} {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hbound : ps.stack.length ≤ 17)
    (htgtle : targetOps.length ≤ ps.stack.length)
    (hnospill : ∀ o, alookup' ps.spilled o = none)
    (hreorder : reorderPlan targetOps ps = (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  set N := ps.stack.length with hN
  set Inv : PlanState → Prop := fun p =>
    p.stack.length = N ∧ (∀ o, alookup' p.spilled o = none) with hInvDef
  have htgtN : targetOps.length ≤ N := htgtle
  have hstep : ∀ (a : Nat × Operand) (p : PlanState) (s : AsmState),
      Inv p → venomAsmRel lo p vs s →
      asmBlockAt prog s.pc (executePlan (reorderOne () targetOps a.1 a.2 p).1) →
      ∃ s', runAsm (executePlan (reorderOne () targetOps a.1 a.2 p).1).length offsetToPc prog s
              = AsmResult.AsmOK s' ∧
            venomAsmRel lo (reorderOne () targetOps a.1 a.2 p).2 vs s' ∧
            s'.pc = s.pc + (executePlan (reorderOne () targetOps a.1 a.2 p).1).length := by
    intro a p s hInv hrelp hblockp
    obtain ⟨hlenp, hspp⟩ := hInv
    by_cases hmem : ∃ d, stackGetDepth a.2 p.stack = some d
    · obtain ⟨d, hd⟩ := hmem
      have hdlt : d < p.stack.length := stackGetDepth_lt_length hd
      exact reorderOne_asm_bounded hd (by omega) (by omega) (by omega) hrelp hblockp
    · have hnone : stackGetDepth a.2 p.stack = none := by
        cases h : stackGetDepth a.2 p.stack with
        | none => rfl
        | some d => exact absurd ⟨d, h⟩ hmem
      rw [reorderOne_offstack_noop hnone (hspp a.2)]
      exact ⟨s, by simp [executePlan, runAsm], by simpa using hrelp, by simp [executePlan]⟩
  have hInvStep : ∀ (a : Nat × Operand) (p : PlanState), Inv p → Inv (reorderOne () targetOps a.1 a.2 p).2 := by
    intro a p hInv
    obtain ⟨hlenp, hspp⟩ := hInv
    by_cases hmem : ∃ d, stackGetDepth a.2 p.stack = some d
    · obtain ⟨d, hd⟩ := hmem
      have hdlt : d < p.stack.length := stackGetDepth_lt_length hd
      have hflt : targetOps.length - 1 - a.1 < p.stack.length := by omega
      have hperm2 := reorderOne_perm_small hd hdlt hflt
      exact ⟨by rw [hperm2.length_eq]; exact hlenp,
             by rw [reorderOne_onstack_spilled hd (by omega) (by omega)]; exact hspp⟩
    · have hnone : stackGetDepth a.2 p.stack = none := by
        cases h : stackGetDepth a.2 p.stack with
        | none => rfl
        | some d => exact absurd ⟨d, h⟩ hmem
      rw [reorderOne_offstack_noop hnone (hspp a.2)]
      exact ⟨hlenp, hspp⟩
  have hrp : reorderPlan targetOps ps = targetOps.enum.foldl
      (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                     (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps) := by
    unfold reorderPlan; congr 1
  have hfold : targetOps.enum.foldl
      (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                     (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps) = (ops, ps') := by
    rw [← hrp]; exact hreorder
  have he1 : (targetOps.enum.foldl (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps)).1 = ops := congrArg Prod.fst hfold
  have he2 : (targetOps.enum.foldl (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps)).2 = ps' := congrArg Prod.snd hfold
  obtain ⟨as', hrun, hrel', hpc⟩ :=
    foldl_ops_sim_inv lo vs prog offsetToPc
      (fun (p : PlanState) (a : Nat × Operand) => reorderOne () targetOps a.1 a.2 p)
      Inv hInvStep hstep targetOps.enum ps as ⟨rfl, hnospill⟩ hrel (by rw [he1]; exact hblock)
  rw [he1] at hrun hpc
  rw [he2] at hrel'
  exact ⟨as', hrun, hrel', hpc⟩

/-- **Fully-discharged genuine JMP-join residual asm run** (bounded-stack case). The `hstep`-free
    counterpart of `hasm_jmp_reorder`: for a predecessor leaving `base ++ perm` (perm a permutation of
    the target's entry layout, `≤ 17`, no spills), the join reorder runs on asm (`reorderPlan_join_bounded`
    — per-step discharged internally) then the resolved `push-label ; JUMP` lands at the successor pc.
    The genuine-reorder counterpart of `hasm_regularHN_jmp` with **no** carried per-step obligation —
    the completed genuine (non-identity) JMP-join for the realistic bounded-stack case. -/
theorem hasm_jmp_reorder_bounded {targetOps base perm : List Operand} {ps ps' : PlanState}
    {jOps : List StackOp} {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {target : String} {off idx : Nat}
    (hperm : List.Perm perm targetOps)
    (hpsstk : ps.stack = base ++ perm)
    (hbound : (base ++ perm).length ≤ 17)
    (hnospill : ∀ o, alookup' ps.spilled o = none)
    (hreorder : reorderPlan targetOps ps = (jOps, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblockJ : asmBlockAt prog as.pc (executePlan jOps))
    (hpc1 : as.pc + (executePlan jOps).length < prog.length)
    (hpush : prog.get ⟨as.pc + (executePlan jOps).length, hpc1⟩
        = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + (executePlan jOps).length + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + (executePlan jOps).length + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ as', runAsm ((executePlan jOps).length + 2) offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧ ps'.stack = base ++ targetOps ∧ as'.pc = idx := by
  obtain ⟨asReord, hrunJ, hrelJ, hstk, hpcJ⟩ :=
    reorderPlan_join_bounded hperm hpsstk hbound hnospill hreorder hrel hblockJ
  have hpc1' : asReord.pc < prog.length := by rw [hpcJ]; exact hpc1
  have hpush' : prog.get ⟨asReord.pc, hpc1'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target) := by
    rw [show (⟨asReord.pc, hpc1'⟩ : Fin _) = ⟨as.pc + (executePlan jOps).length, hpc1⟩ from Fin.ext hpcJ]
    exact hpush
  have hpc2' : asReord.pc + 1 < prog.length := by rw [hpcJ]; exact hpc2
  have hjump' : prog.get ⟨asReord.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" := by
    have e : asReord.pc + 1 = as.pc + (executePlan jOps).length + 1 := by rw [hpcJ]
    conv_lhs => rw [show (⟨asReord.pc + 1, hpc2'⟩ : Fin prog.length)
      = ⟨as.pc + (executePlan jOps).length + 1, hpc2⟩ from Fin.ext e]
    exact hjump
  have hjrun : runAsm 2 offsetToPc prog asReord = AsmResult.AsmOK { asReord with pc := idx } :=
    resolved_jump_sim hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk
  refine ⟨{ asReord with pc := idx }, ?_, venomAsmRel_setPc hrelJ, hstk, rfl⟩
  rw [runAsm_add_ok hrunJ]; exact hjrun

/-- **DJMP pop-trampoline correspondence** (the OK-case core of the new DJMP jump-table lowering,
    `generateDjmpPlan`). The resolved trampoline `[JUMPDEST t ; POP ; PUSH lᵢ ; JUMP]` — entered from the
    switch's `JUMPI` with the selector still on the stack — pops that selector and jumps to `lᵢ`'s pc
    `idx`, leaving the successor's stack `rest`. This is what makes the DJMP switch match the
    interpreter's `jumpTo labels[idx]` (which consumes the selector var and does not touch the successor
    stack). Four steps: `asmStep_label_ok` (JUMPDEST), the `POP` step (`asmPop` on `sel :: rest`), then
    `resolved_jump_sim` (`push-label ; JUMP`). -/
theorem djmp_trampoline_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {t l : String} {off idx : Nat} {sel : bytes32} {rest : List bytes32}
    (hstack : s.stack = sel :: rest)
    (hpc0 : s.pc < prog.length) (hg0 : prog.get ⟨s.pc, hpc0⟩ = AsmInst.AsmLabel t)
    (hpc1 : s.pc + 1 < prog.length) (hg1 : prog.get ⟨s.pc + 1, hpc1⟩ = AsmInst.AsmOp "POP")
    (hpc2 : s.pc + 2 < prog.length)
    (hpush : prog.get ⟨s.pc + 2, hpc2⟩ = resolveInst offsets (AsmInst.AsmPushLabel l))
    (hoff_lk : AssocList.lookup String Nat offsets l = some off) (hoff : off < 2 ^ 256)
    (hpc3 : s.pc + 3 < prog.length) (hg3 : prog.get ⟨s.pc + 3, hpc3⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ s', runAsm 4 offsetToPc prog s = AsmResult.AsmOK s' ∧ s'.pc = idx ∧ s'.stack = rest := by
  have e0 : asmStep offsetToPc prog s = AsmResult.AsmOK (asmNext s) := asmStep_label_ok hpc0 hg0
  set s1 := asmNext s with hs1
  have hs1pc : s1.pc = s.pc + 1 := rfl
  have hpc1' : s1.pc < prog.length := by rw [hs1pc]; exact hpc1
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK ({ asmNext s1 with stack := rest }) := by
    have hg1' : prog.get ⟨s1.pc, hpc1'⟩ = AsmInst.AsmOp "POP" := by
      rw [show (⟨s1.pc, hpc1'⟩ : Fin _) = ⟨s.pc + 1, hpc1⟩ from Fin.ext hs1pc]; exact hg1
    have hs1stack : s1.stack = sel :: rest := by rw [hs1]; exact hstack
    rw [asmStep]
    split
    · next h =>
      rw [show prog.get ⟨s1.pc, h⟩ = AsmInst.AsmOp "POP" from hg1']
      simp only [asmPop, hs1stack]
    · next hc => exact absurd hpc1' hc
  set s2 := ({ asmNext s1 with stack := rest } : AsmState) with hs2
  have hs2pc : s2.pc = s.pc + 2 := by rw [hs2]; show (asmNext s1).pc = _; rw [hs1]; rfl
  have hpc2' : s2.pc < prog.length := by rw [hs2pc]; exact hpc2
  have hpush' : prog.get ⟨s2.pc, hpc2'⟩ = resolveInst offsets (AsmInst.AsmPushLabel l) := by
    rw [show (⟨s2.pc, hpc2'⟩ : Fin _) = ⟨s.pc + 2, hpc2⟩ from Fin.ext hs2pc]; exact hpush
  have hpc3' : s2.pc + 1 < prog.length := by rw [hs2pc]; exact hpc3
  have hg3' : prog.get ⟨s2.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMP" := by
    have e : s2.pc + 1 = s.pc + 3 := by rw [hs2pc]
    conv_lhs => rw [show (⟨s2.pc + 1, hpc3'⟩ : Fin prog.length) = ⟨s.pc + 3, hpc3⟩ from Fin.ext e]
    exact hg3
  have ejump : runAsm 2 offsetToPc prog s2 = AsmResult.AsmOK { s2 with pc := idx } :=
    resolved_jump_sim hpc2' hpush' hoff_lk hoff hpc3' hg3' hidx_lk
  refine ⟨{ s2 with pc := idx }, ?_, rfl, rfl⟩
  rw [runAsm_succ_ok hpc0 e0, runAsm_succ_ok hpc1' e1]
  exact ejump

/-- **DJMP matching switch-entry correspondence.** For the switch entry `[DUP1 ; PUSH pbytes ; EQ ;
    PUSH t ; JUMPI]` where the selector `sel` equals the pushed comparison value, the `EQ` yields `1`,
    the `JUMPI` is **taken**, and control jumps to the trampoline `t` (pc `idx`) with the selector still
    on the stack (`sel :: rest`) — where `djmp_trampoline_sim` then pops it and jumps to the target. The
    5-step entry: `DUP1` + `PUSH` + `EQ` + `resolved_jumpi_taken_sim`. Together with `djmp_trampoline_sim`
    this is the single-target OK case of the `generateDjmpPlan` switch. -/
theorem djmp_entry_taken_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {t : String} {off idx : Nat} {sel : bytes32}
    {rest : List bytes32} {pbytes : List byte}
    (hstack : s.stack = sel :: rest)
    (hsel : sel = wordOfBytes (List.toByteArray (List.replicate (32 - pbytes.length) (0 : byte) ++ pbytes)))
    (hpc0 : s.pc < prog.length) (hg0 : prog.get ⟨s.pc, hpc0⟩ = AsmInst.AsmOp "DUP1")
    (hpc1 : s.pc + 1 < prog.length) (hg1 : prog.get ⟨s.pc + 1, hpc1⟩ = AsmInst.AsmPush pbytes)
    (hpc2 : s.pc + 2 < prog.length) (hg2 : prog.get ⟨s.pc + 2, hpc2⟩ = AsmInst.AsmOp "EQ")
    (hpc3 : s.pc + 3 < prog.length)
    (hpush : prog.get ⟨s.pc + 3, hpc3⟩ = resolveInst offsets (AsmInst.AsmPushLabel t))
    (hoff_lk : AssocList.lookup String Nat offsets t = some off) (hoff : off < 2 ^ 256)
    (hpc4 : s.pc + 4 < prog.length) (hjumpi : prog.get ⟨s.pc + 4, hpc4⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runAsm 5 offsetToPc prog s = AsmResult.AsmOK { s with stack := sel :: rest, pc := idx } := by
  set val := wordOfBytes (List.toByteArray (List.replicate (32 - pbytes.length) (0 : byte) ++ pbytes)) with hval
  have hlen0 : 0 < s.stack.length := by rw [hstack]; simp
  have hget0 : s.stack.get ⟨0, hlen0⟩ = sel := by simp [hstack]
  have e0 : asmStep offsetToPc prog s = AsmResult.AsmOK ({ asmNext s with stack := sel :: sel :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc0 (by rw [hg0]; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 s = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hstack]
  set s1 := ({ asmNext s with stack := sel :: sel :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = s.pc + 1 := rfl
  have hpc1' : s1.pc < prog.length := by rw [hs1pc]; exact hpc1
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK ({ asmNext s1 with stack := val :: sel :: sel :: rest }) := by
    have hg1' : prog.get ⟨s1.pc, hpc1'⟩ = AsmInst.AsmPush pbytes := by
      rw [show (⟨s1.pc, hpc1'⟩ : Fin _) = ⟨s.pc + 1, hpc1⟩ from Fin.ext hs1pc]; exact hg1
    rw [asmStep_push_ok hpc1' hg1']
    show asmPushVal val s1 = _
    unfold asmPushVal; rw [hs1]
  set s2 := ({ asmNext s1 with stack := val :: sel :: sel :: rest } : AsmState) with hs2
  have hs2pc : s2.pc = s.pc + 2 := by rw [hs2]; show (asmNext s1).pc = _; rw [hs1]; rfl
  have hpc2' : s2.pc < prog.length := by rw [hs2pc]; exact hpc2
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK ({ asmNext s2 with stack := (⟨1⟩ : bytes32) :: sel :: rest }) := by
    have hg2' : prog.get ⟨s2.pc, hpc2'⟩ = AsmInst.AsmOp "EQ" := by
      rw [show (⟨s2.pc, hpc2'⟩ : Fin _) = ⟨s.pc + 2, hpc2⟩ from Fin.ext hs2pc]; exact hg2
    rw [asmStep]
    split
    · next h =>
      rw [show prog.get ⟨s2.pc, h⟩ = AsmInst.AsmOp "EQ" from hg2']
      show asmBinop (fun x y => boolToWord (x = y)) s2 = _
      have hcond : boolToWord (val = sel) = (⟨1⟩ : bytes32) := by rw [hsel]; simp [boolToWord]
      simp only [asmBinop, show s2.stack = val :: sel :: sel :: rest from rfl, hcond]
    · next hc => exact absurd hpc2' hc
  set s3 := ({ asmNext s2 with stack := (⟨1⟩ : bytes32) :: sel :: rest } : AsmState) with hs3
  have hs3pc : s3.pc = s.pc + 3 := by rw [hs3]; show (asmNext s2).pc = _; rw [hs2]; show (asmNext s1).pc + 1 = _; rw [hs1]; rfl
  have hpc3' : s3.pc < prog.length := by rw [hs3pc]; exact hpc3
  have hpush' : prog.get ⟨s3.pc, hpc3'⟩ = resolveInst offsets (AsmInst.AsmPushLabel t) := by
    rw [show (⟨s3.pc, hpc3'⟩ : Fin _) = ⟨s.pc + 3, hpc3⟩ from Fin.ext hs3pc]; exact hpush
  have hpc4' : s3.pc + 1 < prog.length := by rw [hs3pc]; exact hpc4
  have hjumpi' : prog.get ⟨s3.pc + 1, hpc4'⟩ = AsmInst.AsmOp "JUMPI" := by
    have e : s3.pc + 1 = s.pc + 4 := by rw [hs3pc]
    conv_lhs => rw [show (⟨s3.pc + 1, hpc4'⟩ : Fin prog.length) = ⟨s.pc + 4, hpc4⟩ from Fin.ext e]
    exact hjumpi
  have ejumpi : runAsm 2 offsetToPc prog s3
      = AsmResult.AsmOK { s3 with stack := sel :: rest, pc := idx } :=
    resolved_jumpi_taken_sim (by rw [hs3]) (by decide) hpc3' hpush' hoff_lk hoff hpc4' hjumpi' hidx_lk
  rw [show (5:Nat) = 1 + (1 + (1 + 2)) from rfl,
      runAsm_succ_ok hpc0 e0, runAsm_succ_ok hpc1' e1, runAsm_succ_ok hpc2' e2]
  rw [ejumpi]
  congr 1

/-- **DJMP non-matching switch-entry correspondence** (fall-through). When the selector `sel` does *not*
    equal the pushed comparison value, `EQ` yields `0`, the `JUMPI` is **not taken**, and the entry falls
    through to the next entry (`pc + 5`) with the stack restored to `sel :: rest` — so the switch scans
    on to the matching entry. The fall-through counterpart of `djmp_entry_taken_sim`; the two together
    (with `djmp_trampoline_sim`) leave only the n-way chain induction for the full DJMP OK-case. -/
theorem djmp_entry_nottaken_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {t : String} {off : Nat} {sel : bytes32}
    {rest : List bytes32} {pbytes : List byte}
    (hstack : s.stack = sel :: rest)
    (hsel : sel ≠ wordOfBytes (List.toByteArray (List.replicate (32 - pbytes.length) (0 : byte) ++ pbytes)))
    (hpc0 : s.pc < prog.length) (hg0 : prog.get ⟨s.pc, hpc0⟩ = AsmInst.AsmOp "DUP1")
    (hpc1 : s.pc + 1 < prog.length) (hg1 : prog.get ⟨s.pc + 1, hpc1⟩ = AsmInst.AsmPush pbytes)
    (hpc2 : s.pc + 2 < prog.length) (hg2 : prog.get ⟨s.pc + 2, hpc2⟩ = AsmInst.AsmOp "EQ")
    (hpc3 : s.pc + 3 < prog.length)
    (hpush : prog.get ⟨s.pc + 3, hpc3⟩ = resolveInst offsets (AsmInst.AsmPushLabel t))
    (hoff_lk : AssocList.lookup String Nat offsets t = some off) (hoff : off < 2 ^ 256)
    (hpc4 : s.pc + 4 < prog.length) (hjumpi : prog.get ⟨s.pc + 4, hpc4⟩ = AsmInst.AsmOp "JUMPI") :
    runAsm 5 offsetToPc prog s = AsmResult.AsmOK { s with stack := sel :: rest, pc := s.pc + 5 } := by
  set val := wordOfBytes (List.toByteArray (List.replicate (32 - pbytes.length) (0 : byte) ++ pbytes)) with hval
  have hlen0 : 0 < s.stack.length := by rw [hstack]; simp
  have hget0 : s.stack.get ⟨0, hlen0⟩ = sel := by simp [hstack]
  have e0 : asmStep offsetToPc prog s = AsmResult.AsmOK ({ asmNext s with stack := sel :: sel :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc0 (by rw [hg0]; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 s = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hstack]
  set s1 := ({ asmNext s with stack := sel :: sel :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = s.pc + 1 := rfl
  have hpc1' : s1.pc < prog.length := by rw [hs1pc]; exact hpc1
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK ({ asmNext s1 with stack := val :: sel :: sel :: rest }) := by
    have hg1' : prog.get ⟨s1.pc, hpc1'⟩ = AsmInst.AsmPush pbytes := by
      rw [show (⟨s1.pc, hpc1'⟩ : Fin _) = ⟨s.pc + 1, hpc1⟩ from Fin.ext hs1pc]; exact hg1
    rw [asmStep_push_ok hpc1' hg1']
    show asmPushVal val s1 = _
    unfold asmPushVal; rw [hs1]
  set s2 := ({ asmNext s1 with stack := val :: sel :: sel :: rest } : AsmState) with hs2
  have hs2pc : s2.pc = s.pc + 2 := by rw [hs2]; show (asmNext s1).pc = _; rw [hs1]; rfl
  have hpc2' : s2.pc < prog.length := by rw [hs2pc]; exact hpc2
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK ({ asmNext s2 with stack := EvmYul.UInt256.ofNat 0 :: sel :: rest }) := by
    have hg2' : prog.get ⟨s2.pc, hpc2'⟩ = AsmInst.AsmOp "EQ" := by
      rw [show (⟨s2.pc, hpc2'⟩ : Fin _) = ⟨s.pc + 2, hpc2⟩ from Fin.ext hs2pc]; exact hg2
    rw [asmStep]
    split
    · next h =>
      rw [show prog.get ⟨s2.pc, h⟩ = AsmInst.AsmOp "EQ" from hg2']
      show asmBinop (fun x y => boolToWord (x = y)) s2 = _
      have hne : val ≠ sel := fun heq => hsel heq.symm
      have hcond : boolToWord (val = sel) = EvmYul.UInt256.ofNat 0 := by
        simp only [boolToWord, decide_eq_false hne]; rfl
      simp only [asmBinop, show s2.stack = val :: sel :: sel :: rest from rfl, hcond]
    · next hc => exact absurd hpc2' hc
  set s3 := ({ asmNext s2 with stack := EvmYul.UInt256.ofNat 0 :: sel :: rest } : AsmState) with hs3
  have hs3pc : s3.pc = s.pc + 3 := by rw [hs3]; show (asmNext s2).pc = _; rw [hs2]; show (asmNext s1).pc + 1 = _; rw [hs1]; rfl
  have hpc3' : s3.pc < prog.length := by rw [hs3pc]; exact hpc3
  have hpush' : prog.get ⟨s3.pc, hpc3'⟩ = resolveInst offsets (AsmInst.AsmPushLabel t) := by
    rw [show (⟨s3.pc, hpc3'⟩ : Fin _) = ⟨s.pc + 3, hpc3⟩ from Fin.ext hs3pc]; exact hpush
  have hpc4' : s3.pc + 1 < prog.length := by rw [hs3pc]; exact hpc4
  have hjumpi' : prog.get ⟨s3.pc + 1, hpc4'⟩ = AsmInst.AsmOp "JUMPI" := by
    have e : s3.pc + 1 = s.pc + 4 := by rw [hs3pc]
    conv_lhs => rw [show (⟨s3.pc + 1, hpc4'⟩ : Fin prog.length) = ⟨s.pc + 4, hpc4⟩ from Fin.ext e]
    exact hjumpi
  have ejumpi : runAsm 2 offsetToPc prog s3
      = AsmResult.AsmOK { s3 with stack := sel :: rest, pc := s3.pc + 2 } :=
    resolved_jumpi_nottaken_sim (by rw [hs3]) hpc3' hpush' hoff_lk hoff hpc4' hjumpi'
  rw [show (5:Nat) = 1 + (1 + (1 + 2)) from rfl,
      runAsm_succ_ok hpc0 e0, runAsm_succ_ok hpc1' e1, runAsm_succ_ok hpc2' e2, ejumpi]
  rw [hs3pc]; congr 1

/-- The comparison word a DJMP switch entry pushes: the zero-padded 32-byte encoding of the entry's
    literal, read back as a `bytes32` (matches the `pbytes` handling in the entry bricks). -/
def djmpVal (pbytes : List byte) : bytes32 :=
  wordOfBytes (List.toByteArray (List.replicate (32 - pbytes.length) (0 : byte) ++ pbytes))

/-- A DJMP switch entry `[DUP1 ; PUSH pbytes ; EQ ; PUSHLabel t ; JUMPI]` laid out at program pc `p`,
    with its trampoline label `t` resolving to offset `off < 2^256`. Bundles the positional facts the
    entry bricks consume. -/
def djmpEntryHere (offsets : AssocList String Nat) (prog : List AsmInst) (p : Nat)
    (pbytes : List byte) (t : String) (off : Nat) : Prop :=
  (∃ h : p < prog.length, prog.get ⟨p, h⟩ = AsmInst.AsmOp "DUP1") ∧
  (∃ h : p + 1 < prog.length, prog.get ⟨p + 1, h⟩ = AsmInst.AsmPush pbytes) ∧
  (∃ h : p + 2 < prog.length, prog.get ⟨p + 2, h⟩ = AsmInst.AsmOp "EQ") ∧
  (∃ h : p + 3 < prog.length, prog.get ⟨p + 3, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel t)) ∧
  AssocList.lookup String Nat offsets t = some off ∧ off < 2 ^ 256 ∧
  (∃ h : p + 4 < prog.length, prog.get ⟨p + 4, h⟩ = AsmInst.AsmOp "JUMPI")

/-- **DJMP switch scan (non-matching prefix).** The switch scans past a run of non-matching entries
    `pre`, each laid out at `s.pc + 5*k` and failing the selector comparison, advancing `5` pc per
    entry with the selector `sel :: rest` preserved on the stack — reaching `s.pc + 5*|pre|`, the
    start of the matching entry. Induction over `pre`, folding `djmp_entry_nottaken_sim`. -/
theorem djmp_scan_nottaken {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {sel : bytes32} {rest : List bytes32}
    (pre : List (List byte × String × Nat)) (s : AsmState) (hstack : s.stack = sel :: rest)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog (s.pc + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        sel ≠ djmpVal (pre.get ⟨k, hk⟩).1) :
    runAsm (5 * pre.length) offsetToPc prog s
      = AsmResult.AsmOK { s with stack := sel :: rest, pc := s.pc + 5 * pre.length } := by
  induction pre generalizing s with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, runAsm]
    rw [← hstack]
  | cons e restpre ih =>
    -- head entry, at s.pc (k = 0), is non-matching
    obtain ⟨hhere, hne⟩ := hpre 0 (Nat.zero_lt_succ _)
    simp only [Nat.mul_zero, Nat.add_zero] at hhere hne
    obtain ⟨⟨h0, hg0⟩, ⟨h1, hg1⟩, ⟨h2, hg2⟩, ⟨h3, hg3⟩, hlk, hoff, ⟨h4, hg4⟩⟩ := hhere
    have hstep : runAsm 5 offsetToPc prog s
        = AsmResult.AsmOK { s with stack := sel :: rest, pc := s.pc + 5 } :=
      djmp_entry_nottaken_sim hstack hne h0 hg0 h1 hg1 h2 hg2 h3 hg3 hlk hoff h4 hg4
    set s' := ({ s with stack := sel :: rest, pc := s.pc + 5 } : AsmState) with hs'
    -- tail entries, shifted by 5, feed the induction hypothesis
    have hpre' : ∀ (k : Nat) (hk : k < restpre.length),
        djmpEntryHere offsets prog (s'.pc + 5 * k) (restpre.get ⟨k, hk⟩).1
          (restpre.get ⟨k, hk⟩).2.1 (restpre.get ⟨k, hk⟩).2.2 ∧
        sel ≠ djmpVal (restpre.get ⟨k, hk⟩).1 := by
      intro k hk
      have := hpre (k + 1) (by simpa using Nat.succ_lt_succ hk)
      simp only [List.get_cons_succ] at this
      have hpceq : s'.pc + 5 * k = s.pc + 5 * (k + 1) := by rw [hs']; simp; ring
      rw [hpceq]; exact this
    have hIH := ih s' rfl hpre'
    -- compose: 5 (head) + 5*|restpre| (tail) = 5*|pre|
    have hlen : 5 * (restpre.length + 1) = 5 + 5 * restpre.length := by ring
    rw [List.length_cons, hlen, runAsm_add_ok hstep, hIH]
    congr 1
    simp only [hs', Nat.add_assoc]

/-- **DJMP n-way switch OK-case.** The full comparison-switch lowering of `DJMP`: for a selector `sel`
    that matches the `|pre|`-th entry (scanning past `pre` earlier non-matching entries), control runs
    the `5*|pre|` scan steps, takes the matching entry (`5` steps → its trampoline at `idxTramp`), then
    the trampoline (`4` steps: `JUMPDEST ; POP ; PUSH target ; JUMP`) → arriving at the selected block
    `target` with the selector popped (stack `rest`). Composes `djmp_scan_nottaken` +
    `djmp_entry_taken_sim` + `djmp_trampoline_sim` via `runAsm_add_ok`. This is the whole DJMP OK-case
    n-way, reducing it to the per-entry/per-trampoline layout facts (supplied by the resolved plan). -/
theorem djmp_switch_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {sel : bytes32} {rest : List bytes32}
    (pre : List (List byte × String × Nat)) (s : AsmState) (hstack : s.stack = sel :: rest)
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere offsets prog (s.pc + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        sel ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere offsets prog (s.pc + 5 * pre.length) matb tName matoff)
    (hsel : sel = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst offsets (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat offsets lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target) :
    ∃ s', runAsm (5 * pre.length + 5 + 4) offsetToPc prog s = AsmResult.AsmOK s'
      ∧ s'.pc = target ∧ s'.stack = rest := by
  -- (1) scan the non-matching prefix
  have hscan := djmp_scan_nottaken (offsetToPc := offsetToPc) pre s hstack hpre
  set sI := ({ s with stack := sel :: rest, pc := s.pc + 5 * pre.length } : AsmState) with hsI
  -- (2) take the matching entry → trampoline
  obtain ⟨⟨m0, mg0⟩, ⟨m1, mg1⟩, ⟨m2, mg2⟩, ⟨m3, mg3⟩, mlk, moff, ⟨m4, mg4⟩⟩ := hmatch
  -- `sI.pc` is defeq `s.pc + 5*pre.length`, so the positional hyps feed the brick directly
  have htaken : runAsm 5 offsetToPc prog sI
      = AsmResult.AsmOK { sI with stack := sel :: rest, pc := idxTramp } := by
    refine djmp_entry_taken_sim (s := sI) (rfl) ?_ m0 mg0 m1 mg1 m2 mg2 m3 mg3 mlk moff m4 mg4 hidx_lk
    rw [djmpVal] at hsel; exact hsel
  set sT := ({ sI with stack := sel :: rest, pc := idxTramp } : AsmState) with hsT
  -- (3) run the trampoline → target (`sT.pc` is defeq `idxTramp`)
  obtain ⟨t0, tg0⟩ := ht0; obtain ⟨t1, tg1⟩ := ht1; obtain ⟨t2, tg2⟩ := ht2; obtain ⟨t3, tg3⟩ := ht3
  obtain ⟨s', htramp, hpc', hstk'⟩ :=
    djmp_trampoline_sim (s := sT) (rfl) t0 tg0 t1 tg1 t2 tg2 hl_lk hloff t3 tg3 htarget_lk
  -- compose 5*|pre| + 5 + 4
  refine ⟨s', ?_, hpc', hstk'⟩
  rw [show 5 * pre.length + 5 + 4 = 5 * pre.length + (5 + 4) from by ring, runAsm_add_ok hscan,
      runAsm_add_ok htaken]
  exact htramp


/-- **`generatePhiPlan` renames the source slot to the phi output (dead-source case).** When the phi's
    live source var sits at depth `dist` and is dead afterwards, the asm plan pokes the phi output
    `Var (inst.outputs.head!)` into that slot: the plan stack becomes `stackPoke dist ret ps.stack`.
    The asm-side rename atom for the join-point PHI alignment (the Venom side is `evalPhis`, which binds
    the same output to `resolvePhi`'s prevBb-selected source value); the full alignment additionally
    needs `venomAsmRel` preservation across the rename and the `evalPhis` ↔ poke value match. -/
theorem generatePhiPlan_stack_pokeCase (inst : Instruction) (nextLiveness : List String)
    (ps : PlanState) (dist : Nat)
    (hdepth : stackGetPhiDepth (inst.operands.filter isVarOperand) ps.stack = some dist)
    (hdead : nextLiveness.contains (operandToString (stackPeek dist ps.stack)) = false) :
    (generatePhiPlan inst nextLiveness ps).2.stack
      = stackPoke dist (Operand.Var (inst.outputs.head!)) ps.stack := by
  unfold generatePhiPlan
  simp only [hdepth]
  rw [if_neg (by rw [hdead]; simp)]

/-- **Venom phi step selects the prevBb source var's value.** For a PHI with output `[out]`, incoming
    `prevBb = some prev`, whose `resolvePhi prev` picks source `Var src` bound to `v`, `evalOnePhi`
    yields `(out, v)` — the phi output takes the source var's value. The Venom counterpart of the asm
    rename `generatePhiPlan_stack_pokeCase` (which relabels `src`'s stack slot to `out`). -/
theorem evalOnePhi_var {s : VenomState} {inst : Instruction} {prev out src : String} {v : bytes32}
    (houts : inst.outputs = [out])
    (hprev : s.prevBb = some prev)
    (hresolve : resolvePhi prev inst.operands = some (Operand.Var src))
    (hval : lookupVar src s = some v) :
    evalOnePhi s inst = some (out, v) := by
  simp only [evalOnePhi, houts, hprev, hresolve, evalOperand, hval, Option.map_some]

/-- **Single-phi block prefix (Venom).** `evalPhis` over a one-element PHI prefix binds `out` to the
    selected source value: `evalPhis s [phi] = OK (updateVar out v s)`. Combines with the asm-side
    rename to align the join entry. -/
theorem evalPhis_single {s : VenomState} {inst : Instruction} {prev out src : String} {v : bytes32}
    (hphi : inst.opcode = Opcode.PHI)
    (houts : inst.outputs = [out])
    (hprev : s.prevBb = some prev)
    (hresolve : resolvePhi prev inst.operands = some (Operand.Var src))
    (hval : lookupVar src s = some v) :
    evalPhis s [inst] = ExecResult.OK (updateVar out v s) := by
  unfold evalPhis
  rw [if_neg (by rw [hphi]; simp), evalOnePhi_var houts hprev hresolve hval]
  rfl

/-- **The phi step of a genuine join, on *any* incoming edge.**

This is the piece an `hstep` for a real (≥ 2-predecessor) join needs, and the point is which relation it
takes as input. `planStackRel_phi_poke` above assumes the relation already holds against the *recorded*
plan stack — the layout of the predecessor the DFS happened to compile the block against. On any other
edge that is false (`phiFn_rel_fails_before_phi`): the recorded slot names a variable this path never
assigned.

What *is* true on every edge is the relation against the **arriving** predecessor's exit layout — which is
exactly what that predecessor's own block simulation hands you. This lemma starts from that, and produces
the relation against the recorded plan stack, which is what the rest of the block is compiled for.

Both sides move consistently and neither touches the asm stack: `evalPhis` binds `out` to the value
arriving on this edge, `SOPoke` renames the slot, and no EVM code is emitted. -/
theorem phi_join_step {lo : AssocList String Nat} {vs : VenomState}
    {psArr psRec : List Operand} {asmStack : List bytes32} {d : Nat}
    {inst : Instruction} {prev src out : String} {v : bytes32}
    -- Venom side: this is a phi, and it resolves to *this* edge's source
    (hphi : inst.opcode = Opcode.PHI)
    (houts : inst.outputs = [out])
    (hprev : vs.prevBb = some prev)
    (hresolve : resolvePhi prev inst.operands = some (Operand.Var src))
    (hval : lookupVar src vs = some v)
    -- asm side: the relation that actually holds on arrival — against the *arriving* layout
    (hrel : planStackRel lo vs psArr asmStack)
    (hlen : psRec.length = psArr.length)
    (hd : d < psRec.length)
    (hoff : ∀ i, i < psRec.length → i ≠ d → psRec.reverse[i]! = psArr.reverse[i]!)
    (hsrc : psArr.reverse[d]! = Operand.Var src)
    (hfresh : ∀ i, i < psRec.length → i ≠ d → psRec.reverse[i]! ≠ Operand.Var out) :
    evalPhis vs [inst] = ExecResult.OK (updateVar out v vs)
    ∧ planStackRel lo (updateVar out v vs) (stackPoke d (Operand.Var out) psRec) asmStack :=
  ⟨evalPhis_single hphi houts hprev hresolve hval,
   planStackRel_phi_join_bridge hrel hlen hd hoff hsrc hval hfresh⟩

/-- **`planStackRel` bridges the phi rename (the join-point PHI `venomAsmRel` core).** When the plan
    slot at depth `dist` holds `Var src` (value `v`) and `out` is fresh (not on the plan stack),
    relabelling that slot to `Var out` (`stackPoke`, the asm side `generatePhiPlan_stack_pokeCase`)
    while binding `out := v` in the vars (`updateVar`, the Venom side `evalPhis_single`) preserves
    `planStackRel` against the *unchanged* asm stack: the renamed slot now reads `out` (value `v`),
    matching the asm value there (`= v`, since it read `src`); every other slot is untouched and `out`
    isn't among them (`operandVal_updateVar_ne`). The other `venomAsmRel` fields (memory, accounts, …)
    are untouched by the phi, so this is the whole `venomAsmRel`-preservation content of a join-entry
    phi. -/
theorem planStackRel_phi_poke {lo : AssocList String Nat} {vs : VenomState}
    {psStack : List Operand} {asmStack : List bytes32} {out src : String} {dist : Nat} {v : bytes32}
    (hrel : planStackRel lo vs psStack asmStack)
    (hdist : dist < psStack.length)
    (hsrc : stackPeek dist psStack = Operand.Var src)
    (hval : lookupVar src vs = some v)
    (hfresh : Operand.Var out ∉ psStack) :
    planStackRel lo (updateVar out v vs) (stackPoke dist (Operand.Var out) psStack) asmStack := by
  obtain ⟨hlen, hcorr⟩ := hrel
  refine ⟨by rw [stackPoke, List.length_set]; exact hlen, ?_⟩
  intro i hi
  rw [stackPoke, List.length_set] at hi
  have hrev : (stackPoke dist (Operand.Var out) psStack).reverse[i]!
      = if i = dist then Operand.Var out else psStack.reverse[i]! := by
    unfold stackPoke
    rw [getElem!_eq_getElem?_getD, List.getElem?_reverse (by rw [List.length_set]; exact hi),
        List.length_set, List.getElem?_set]
    by_cases hid : i = dist
    · rw [if_pos (show psStack.length - 1 - dist = psStack.length - 1 - i by rw [hid]),
          if_pos (by omega : psStack.length - 1 - dist < psStack.length), if_pos hid]
      simp
    · rw [if_neg (show ¬ psStack.length - 1 - dist = psStack.length - 1 - i by omega), if_neg hid,
          getElem!_eq_getElem?_getD, List.getElem?_reverse hi]
  rw [hrev]
  by_cases hid : i = dist
  · rw [if_pos hid]
    have hpeek : psStack.reverse[i]! = Operand.Var src := by
      rw [hid]
      have hh : psStack.reverse[dist]! = stackPeek dist psStack := by
        unfold stackPeek
        rw [getElem!_pos _ dist (by rw [List.length_reverse]; exact hdist), List.getElem_reverse,
            getElem!_pos _ _ (by omega)]
      rw [hh, hsrc]
    have hasm : asmStack[i]! = v := by
      have hc := hcorr i hi
      rw [hpeek] at hc
      simp only [operandVal, hval] at hc
      exact (Option.some.inj hc).symm
    rw [hasm]
    rw [operandVal_var_eq_lookupVar, lookupVar_updateVar_self]
  · rw [if_neg hid]
    have hmem : psStack.reverse[i]! ∈ psStack := by
      rw [getElem!_pos _ i (by rw [List.length_reverse]; exact hi), ← List.mem_reverse]
      exact List.getElem_mem _
    have hne : psStack.reverse[i]! ≠ Operand.Var out := fun hc => hfresh (hc ▸ hmem)
    rw [operandVal_updateVar_ne vs lo out v _ hne]
    exact hcorr i hi

/-- `doDup` plan-stack effect, the small (non-spill) case (`dist ≤ 15`): copies the depth-`dist`
    element to TOS (`stackDup dist ps.stack`). -/
theorem doDup_stack_small {dist : Nat} {ps : PlanState} (h : dist ≤ 15) :
    (doDup dist ps).2.stack = stackDup dist ps.stack := by
  unfold doDup; rw [if_pos h]

/-- **`generatePhiPlan` (live-source dup case).** When the phi's source var (at depth `dist ≤ 15`)
    stays live afterwards, the asm plan DUPs it to TOS then relabels the copy to the phi output:
    the plan stack becomes `stackPoke 0 (Var out) (stackDup dist ps.stack)` — i.e. `src` is kept and a
    fresh `Var out` copy sits on top. The live-source companion of `generatePhiPlan_stack_pokeCase`. -/
theorem generatePhiPlan_stack_dupCase (inst : Instruction) (nextLiveness : List String)
    (ps : PlanState) (dist : Nat)
    (hdepth : stackGetPhiDepth (inst.operands.filter isVarOperand) ps.stack = some dist)
    (hlive : nextLiveness.contains (operandToString (stackPeek dist ps.stack)) = true)
    (hsmall : dist ≤ 15) :
    (generatePhiPlan inst nextLiveness ps).2.stack
      = stackPoke 0 (Operand.Var (inst.outputs.head!)) (stackDup dist ps.stack) := by
  unfold generatePhiPlan
  simp only [hdepth]
  rw [if_pos (by rw [hlive]), doDup_stack_small hsmall]

/-- **`planStackRel` bridges the phi DUP (live-source case).** When the plan slot at depth `dist`
    holds `Var src` (value `v`) and `out` is fresh, DUPing that slot to a fresh TOS and relabelling it
    to `Var out` (the asm side pushes `src`'s value `= v` on top) while binding `out := v` (Venom)
    preserves `planStackRel`: the new top plan slot `Var out` reads `v`, matching the dup'd asm value
    `= v`; `src` and all other slots are untouched. The live-source companion of `planStackRel_phi_poke`. -/
theorem planStackRel_phi_dup {lo : AssocList String Nat} {vs : VenomState}
    {psStack : List Operand} {asmStack : List bytes32} {out : String} {v : bytes32}
    (hrel : planStackRel lo vs psStack asmStack)
    (hfresh : Operand.Var out ∉ psStack) :
    planStackRel lo (updateVar out v vs) (psStack ++ [Operand.Var out]) (v :: asmStack) := by
  obtain ⟨hlen, hcorr⟩ := hrel
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  match i, hi with
  | 0, _ =>
    simp only [List.getElem!_cons_zero]
    rw [operandVal_var_eq_lookupVar, lookupVar_updateVar_self]
  | i' + 1, hi =>
    have hi' : i' < psStack.length := by omega
    rw [List.getElem!_cons_succ, List.getElem!_cons_succ]
    have hmem : psStack.reverse[i']! ∈ psStack := by
      rw [getElem!_pos _ i' (by rw [List.length_reverse]; exact hi'), ← List.mem_reverse]
      exact List.getElem_mem _
    have hne : psStack.reverse[i']! ≠ Operand.Var out := fun hc => hfresh (hc ▸ hmem)
    rw [operandVal_updateVar_ne vs lo out v _ hne]
    exact hcorr i' hi'

/-- `stackPoke d1` only relabels depth `d1`; any other depth `d2` is unaffected (source preservation
    across a phi poke). -/
theorem stackPeek_stackPoke_ne {d1 d2 : Nat} {op : Operand} {stk : List Operand}
    (hne : d1 ≠ d2) (hd1 : d1 < stk.length) (hd2 : d2 < stk.length) :
    stackPeek d2 (stackPoke d1 op stk) = stackPeek d2 stk := by
  have hne1 : stk.length - 1 - d1 ≠ stk.length - 1 - d2 := by omega
  unfold stackPeek stackPoke
  dsimp only []
  rw [List.length_set, getElem!_eq_getD, getElem!_eq_getD]
  exact getD_set_at_otherpos _ _ _ _ hne1 (by omega)

/-- A fresh var stays fresh after poking a *different* var into a slot. -/
theorem notMem_stackPoke {stk : List Operand} {op : Operand} {w : String} {d : Nat}
    (hop : op ≠ Operand.Var w) (hw : Operand.Var w ∉ stk) :
    Operand.Var w ∉ stackPoke d op stk := by
  unfold stackPoke
  intro hc
  rcases List.mem_or_eq_of_mem_set hc with h | h
  · exact hw h
  · exact hop h.symm

/-- **General multi-phi fold.** A block's whole phi prefix, encoded as records `(out, src, dist, v)`,
    aligns in one shot: folding the asm pokes (each `stackPoke dist (Var out)`) over the plan stack and
    the Venom binds (each `updateVar out v`) over the varstate preserves `planStackRel`, provided each
    phi is a dead-source rename whose source sits at its depth with value `v`, outputs are fresh and
    pairwise-distinct, depths are pairwise-distinct, and no output coincides with any source (SSA). Proof
    threads `planStackRel_phi_poke` down the list, re-establishing each tail precondition from the head's
    poke via `stackPeek_stackPoke_ne` (depths distinct), `lookupVar_updateVar_ne` (source ≠ output), and
    `notMem_stackPoke` (outputs distinct + fresh). -/
theorem planStackRel_phi_fold (lo : AssocList String Nat) :
    ∀ (phis : List (String × String × Nat × bytes32)) (vs : VenomState)
      (psStack : List Operand) (asmStack : List bytes32),
      planStackRel lo vs psStack asmStack →
      (∀ p ∈ phis, stackPeek p.2.2.1 psStack = Operand.Var p.2.1) →
      (∀ p ∈ phis, lookupVar p.2.1 vs = some p.2.2.2) →
      (∀ p ∈ phis, Operand.Var p.1 ∉ psStack) →
      (∀ p ∈ phis, p.2.2.1 < psStack.length) →
      (phis.map (·.2.2.1)).Nodup →
      (∀ p ∈ phis, ∀ q ∈ phis, p.1 ≠ q.2.1) →
      (phis.map (·.1)).Nodup →
      planStackRel lo (phis.foldl (fun s p => updateVar p.1 p.2.2.2 s) vs)
        (phis.foldl (fun stk p => stackPoke p.2.2.1 (Operand.Var p.1) stk) psStack) asmStack := by
  intro phis
  induction phis with
  | nil => intro vs psStack asmStack hrel _ _ _ _ _ _ _; simpa using hrel
  | cons p0 rest ih =>
    intro vs psStack asmStack hrel hsrc hval hfresh hd hnddist hnoout hndout
    simp only [List.foldl_cons]
    -- head-vs-tail distinctness facts
    rw [List.map_cons, List.nodup_cons] at hnddist hndout
    have hdist_ne : ∀ pi ∈ rest, pi.2.2.1 ≠ p0.2.2.1 := fun pi hpi hc =>
      hnddist.1 (hc ▸ List.mem_map_of_mem hpi)
    have hout_ne : ∀ pi ∈ rest, p0.1 ≠ pi.1 := fun pi hpi hc =>
      hndout.1 (hc ▸ List.mem_map_of_mem hpi)
    apply ih (updateVar p0.1 p0.2.2.2 vs) (stackPoke p0.2.2.1 (Operand.Var p0.1) psStack) asmStack
    · exact planStackRel_phi_poke hrel (hd p0 (by simp)) (hsrc p0 (by simp))
        (hval p0 (by simp)) (hfresh p0 (by simp))
    · intro pi hpi
      rw [stackPeek_stackPoke_ne (fun h => (hdist_ne pi hpi) h.symm) (hd p0 (by simp))
        (hd pi (by simp [hpi]))]
      exact hsrc pi (by simp [hpi])
    · intro pi hpi
      rw [lookupVar_updateVar_ne vs p0.1 pi.2.1 p0.2.2.2
        (fun h => hnoout p0 (by simp) pi (by simp [hpi]) h.symm)]
      exact hval pi (by simp [hpi])
    · intro pi hpi
      exact notMem_stackPoke (fun h => hout_ne pi hpi (Operand.Var.inj h)) (hfresh pi (by simp [hpi]))
    · intro pi hpi; rw [stackPoke, List.length_set]; exact hd pi (by simp [hpi])
    · exact hnddist.2
    · exact fun a ha b hb => hnoout a (by simp [ha]) b (by simp [hb])
    · exact hndout.2





/-- **Join-entry phi `venomAsmRel` bridge.** The full-relation lift of `planStackRel_phi_poke`: at a
    join point where the plan slot at depth `dist` holds `Var src` (value `v`) and `out` is fresh
    (not on the plan stack, not spilled), relabelling that slot to `Var out` (the asm-side
    `generatePhiPlan` poke) while binding `out := v` (the Venom-side `evalPhis`) preserves the whole
    `venomAsmRel` against the *unchanged* asm state -- every non-stack field is untouched by the phi
    (`updateVar` keeps memory/accounts/…; the poke keeps spilled/alloc). This is the join-point PHI's
    entire `venomAsmRel` content. -/
theorem venomAsmRel_phi_poke {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {psStack : List Operand} {spl : SpilledMap} {al : SpillAlloc} {lc : Nat}
    {out src : String} {dist : Nat} {v : bytes32}
    (hrel : venomAsmRel lo ⟨psStack, spl, al, lc⟩ vs as)
    (hdist : dist < psStack.length)
    (hsrc : stackPeek dist psStack = Operand.Var src)
    (hval : lookupVar src vs = some v)
    (hfresh : Operand.Var out ∉ psStack)
    (hfreshsp : AssocList.lookup Operand Nat spl (Operand.Var out) = none) :
    venomAsmRel lo ⟨stackPoke dist (Operand.Var out) psStack, spl, al, lc⟩ (updateVar out v vs) as := by
  obtain ⟨hStk, hSp, hMem, hAcc, hTr, hRd, hLg, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hSp' : planSpillRel lo (updateVar out v vs) spl as.memory := by
    intro op off hlk
    obtain ⟨w, hval', hmem'⟩ := hSp op off hlk
    have hne : op ≠ Operand.Var out := by
      intro he; rw [he, hfreshsp] at hlk; contradiction
    exact ⟨w, by rw [operandVal_updateVar_ne _ _ _ _ _ hne]; exact hval', hmem'⟩
  exact ⟨planStackRel_phi_poke hStk hdist hsrc hval hfresh, hSp', hMem, hAcc, hTr, hRd, hLg,
         hCall, hTx, hBlk, hCode, hPrev⟩

/-- **Join-entry phi step (Venom + relation, composed).** For a block whose entry is a single PHI
    `out := φ(… prev ↦ src …)`, at a state that came from predecessor `prev` (via `jumpTo`, so
    `prevBb = some prev`) and is `venomAsmRel`-related with `Var src` at plan depth `dist`: the Venom
    `evalPhis` binds `out := v` (the selected source value) *and* the codegen poke keeps the whole
    `venomAsmRel` (against the unchanged asm state). Packages `evalPhis_single` with
    `venomAsmRel_phi_poke` -- the complete per-phi content of a multi-predecessor join entry. -/
theorem phi_entry_step {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {psStack : List Operand} {spl : SpilledMap} {al : SpillAlloc} {lc : Nat}
    {inst : Instruction} {out src prev : String} {dist : Nat} {v : bytes32}
    (hphi : inst.opcode = Opcode.PHI) (houts : inst.outputs = [out])
    (hprev : vs.prevBb = some prev)
    (hresolve : resolvePhi prev inst.operands = some (Operand.Var src))
    (hval : lookupVar src vs = some v)
    (hrel : venomAsmRel lo ⟨psStack, spl, al, lc⟩ vs as)
    (hdist : dist < psStack.length)
    (hsrc : stackPeek dist psStack = Operand.Var src)
    (hfresh : Operand.Var out ∉ psStack)
    (hfreshsp : AssocList.lookup Operand Nat spl (Operand.Var out) = none) :
    evalPhis vs [inst] = ExecResult.OK (updateVar out v vs) ∧
    venomAsmRel lo ⟨stackPoke dist (Operand.Var out) psStack, spl, al, lc⟩ (updateVar out v vs) as :=
  ⟨evalPhis_single hphi houts hprev hresolve hval,
   venomAsmRel_phi_poke hrel hdist hsrc hval hfresh hfreshsp⟩

/-- **The active swap preserves `StackPerm`.** Since `stackSwap` permutes the stack and `StackPerm`
    tracks the stack only up to permutation, applying the optimistic swap keeps `StackPerm S` — the
    payoff of choosing the permutation form: an active swap (which would break exact-order
    `StackIsVars`) leaves the invariant intact. -/
theorem stackPerm_swap {S : List String} {p : PlanState} {dist : Nat}
    (h : StackPerm S p) (hd : dist < p.stack.length) :
    StackPerm S { p with stack := stackSwap dist p.stack } :=
  (stackSwap_perm dist p.stack hd).trans h

/-- **The whole optimistic swap preserves `StackPerm`** — the invariant-side companion of
    `optimisticSwapPlan_sim` (the asm side). `optimisticSwapPlan` is either a no-op or a single
    `doSwap`; under the same in-range bound `optimisticSwapPlan_sim` assumes (`dist ≤ 16 ∧ dist <
    length`), `doSwap`'s stack effect is exactly `stackSwap` (or identity for `dist = 0`), so
    `StackPerm S` survives. This is the invariant-threading fact an active-swap binop step needs. -/
theorem optimisticSwapPlan_stackPerm {dfg : DfgAnalysis} {inst : Instruction}
    {nextLiveness : List String} {nIT : Bool} {ps : PlanState} {S : List String}
    (h : StackPerm S ps)
    (hbound : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist →
              optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps →
              dist ≤ 16 ∧ dist < ps.stack.length) :
    StackPerm S (optimisticSwapPlan dfg inst nextLiveness nIT ps).2 := by
  rcases optimisticSwapPlan_cases dfg inst nextLiveness nIT ps with hnoop | ⟨dist, hd, heq⟩
  · rw [hnoop]; exact h
  · rw [heq]
    obtain ⟨hle, hlt⟩ := hbound dist hd heq
    rcases Nat.eq_zero_or_pos dist with h0 | hpos
    · subst h0; rw [doSwap_zero]; exact h
    · unfold doSwap
      rw [if_neg (by omega), if_pos hle]
      exact stackPerm_swap h hlt

/-- The active swap preserves `StackDiscH` too: it permutes the stack, so length and the var set are
    unchanged (`shallow`/`defined` survive via `stackSwap_perm`), and `spilled` is untouched. -/
theorem stackDiscH_swap {k : Nat} {p : PlanState} {v : VenomState} {dist : Nat}
    (h : StackDiscH k p v) (hd : dist < p.stack.length) :
    StackDiscH k { p with stack := stackSwap dist p.stack } v where
  noSpill := h.noSpill
  shallow := by
    show (stackSwap dist p.stack).length + k ≤ 15
    rw [(stackSwap_perm dist p.stack hd).length_eq]; exact h.shallow
  defined := fun z hz =>
    h.defined z ((stackSwap_perm dist p.stack hd).mem_iff.mp hz)

/-- `optimisticSwapPlan` preserves `StackDiscH` (the `StackDiscH` companion of
    `optimisticSwapPlan_stackPerm`): no-op or a single in-range `doSwap`, both `StackDiscH`-preserving. -/
theorem optimisticSwapPlan_stackDiscH {dfg : DfgAnalysis} {inst : Instruction}
    {nextLiveness : List String} {nIT : Bool} {ps : PlanState} {vs : VenomState} {k : Nat}
    (h : StackDiscH k ps vs)
    (hbound : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist →
              optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps →
              dist ≤ 16 ∧ dist < ps.stack.length) :
    StackDiscH k (optimisticSwapPlan dfg inst nextLiveness nIT ps).2 vs := by
  rcases optimisticSwapPlan_cases dfg inst nextLiveness nIT ps with hnoop | ⟨dist, hd, heq⟩
  · rw [hnoop]; exact h
  · rw [heq]
    obtain ⟨hle, hlt⟩ := hbound dist hd heq
    rcases Nat.eq_zero_or_pos dist with h0 | hpos
    · subst h0; rw [doSwap_zero]; exact h
    · unfold doSwap
      rw [if_neg (by omega), if_pos hle]
      exact stackDiscH_swap h hlt

/-- `releaseDeadSpills` preserves `StackDiscH`: it never touches the stack
    (`releaseDeadSpills_stack`, so `shallow`/`defined` survive) and only removes spills
    (`releaseDeadSpills_noSpill`). -/
theorem releaseDeadSpills_stackDiscH {nextLiveness : List String} {k : Nat} {ps : PlanState}
    {vs : VenomState} (h : StackDiscH k ps vs) :
    StackDiscH k (releaseDeadSpills nextLiveness ps) vs where
  noSpill := releaseDeadSpills_noSpill nextLiveness ps h.noSpill
  shallow := by rw [releaseDeadSpills_stack]; exact h.shallow
  defined := fun z hz => h.defined z (by rw [releaseDeadSpills_stack] at hz; exact hz)

/-- `releaseDeadSpills` preserves the spill-aware invariant `StackDiscHS`. The fold only *removes*
    spill entries and never touches the stack, so each surviving spill's well-formedness still holds
    (`spillWf`) and the headroom/valuedness fields carry over unchanged. The `StackDiscHS` twin of
    `releaseDeadSpills_stackDiscH`; needed to re-establish the invariant after a spilled body step. -/
theorem releaseDeadSpills_stackDiscHS {nextLiveness : List String} {k : Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} (h : StackDiscHS k ps vs as) :
    StackDiscHS k (releaseDeadSpills nextLiveness ps) vs as where
  spillWf o off hlook := by
    apply h.spillWf o off
    have hlook' : AssocList.lookup Operand Nat (releaseDeadSpills nextLiveness ps).spilled o = some off := hlook
    rw [releaseDeadSpills_eq_foldl] at hlook'
    exact (releaseDeadSpills_foldl_inv nextLiveness ps.spilled ps).2.2.2 o off hlook'
  shallow := by rw [releaseDeadSpills_stack]; exact h.shallow
  defined := fun z hz => h.defined z (by rw [releaseDeadSpills_stack] at hz; exact hz)

/-- `releaseDeadSpills` preserves `StackPerm` (it never touches the stack). -/
theorem releaseDeadSpills_stackPerm {nextLiveness : List String} {S : List String} {ps : PlanState}
    (h : StackPerm S ps) : StackPerm S (releaseDeadSpills nextLiveness ps) := by
  show List.Perm (releaseDeadSpills nextLiveness ps).stack (S.map Operand.Var)
  rw [releaseDeadSpills_stack]; exact h

/-- `StackPerm` for a state whose stack is `ps.stack ++ [Var out]` and `StackPerm S ps`: it permutes
    `(S ++ [out]).map Var`. (Generalises `stackPerm_append_out` to any state with that stack — used
    for the post-emit state, whose non-stack fields come from the input-emission output, not `ps`.) -/
theorem stackPerm_of_stack_append {S : List String} {ps q : PlanState} {out : String}
    (h : StackPerm S ps) (hq : q.stack = ps.stack ++ [Operand.Var out]) :
    StackPerm (S ++ [out]) q := by
  show List.Perm q.stack ((S ++ [out]).map Operand.Var)
  rw [hq, List.map_append]
  exact h.append_right _

/-- **Active-swap body step under the invariant** — discharges a `BodyStepsReadyP` entry for a
    commutative var binop. From `StackDiscH (k+1)` + `StackPerm S` it derives the binop sim's side
    conditions (membership/depths/values; freshness from `out ∉ S`), runs the active-swap sim
    (`genRegularInstPlan_commBinopVar_sim_swap`), and re-establishes both invariants on the output:
    `StackDiscH k` (post-emit `StackDiscH` + `optimisticSwapPlan_stackDiscH` + `releaseDeadSpills_stackDiscH`)
    and `StackPerm (S ++ [out])` (post-emit `StackPerm` via `stackPerm_of_stack_append` +
    `optimisticSwapPlan_stackPerm` + `releaseDeadSpills_stackPerm`). The active-swap counterpart of
    `stackDisc_commBinopVar_step_S`; this is what `genBlockBody_sim_inv_P` folds. -/
theorem stackDisc_commBinopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  -- the asm step (active swap)
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopVar_sim_swap hname hcomm hops houts
    hxy hox hoy rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivey hdepth_y hsmall_y hleny
    (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx' hwx hwy hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  -- the output state is `releaseDeadSpills (optimisticSwapPlan … psE).2`, psE the post-emit state
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy rfl hlive (hsd.noSpill _)
      hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x', hrev]
  -- post-emit StackDiscH on psE
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_pair_var_eq (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex
      hdepth_x' hsmall_x']
  -- `lookupVar` is invisible to `gvBodyStep`'s `instIdx` (it only sets that field)
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs)
      = lookupVar z (updateVar out (f wx wy) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w, hw⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w, by rw [hlv z, lookupVar_updateVar_ne vs out z (f wx wy) hzout]; exact hw⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f wx wy, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · -- StackDiscH k (output) (gvBodyStep …)
    rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · -- StackPerm (S ++ [out]) (output)
    rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Active-swap body step under the invariant — non-commutative var binop.** Discharges a
    `BodyStepsReadyP` entry for SUB/DIV/MOD/LT/GT/SHL/…; the non-comm counterpart of
    `stackDisc_commBinopVar_step_swap_P` (uses `genRegularInstPlan_nonCommBinopVar_sim_swap`). -/
theorem stackDisc_nonCommBinopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_nonCommBinopVar_sim_swap hname hncomm hnjmp
    hcompute hops houts hxy hox hoy rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivey hdepth_y
    hsmall_y hleny (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx' hwx hwy hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x', hrev]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_pair_var_eq (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex
      hdepth_x' hsmall_x']
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs)
      = lookupVar z (updateVar out (f wx wy) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w, hw⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w, by rw [hlv z, lookupVar_updateVar_ne vs out z (f wx wy) hzout]; exact hw⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f wx wy, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Active-swap body step under the invariant — ternary var opcode.** Discharges a
    `BodyStepsReadyP` entry for ADDMOD/MULMOD: derives the sim's side conditions from
    `StackDiscH (k+1)` + `StackPerm S` (depths via `stackDisc_ternopVar_depths`), runs the active-swap
    sim (`genRegularInstPlan_ternopVar_sim_swap`), and re-establishes `StackDiscH k` + `StackPerm
    (S ++ [out])`. The 3-input counterpart of `stackDisc_commBinopVar_step_swap_P`. -/
theorem stackDisc_ternopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y z out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                   nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } : PlanState).stack
                 = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hzmem : Operand.Var z ∈ ps.stack := stackPerm_mem hsv hzS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  have hsd1 : StackDiscH 1 ps vs := ⟨hsd.noSpill, by have := hsd.shallow; omega, hsd.defined⟩
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'',
    hsmall_x, hlenx''⟩ := stackDisc_ternopVar_depths hsd1 hxy hyz hxz hxmem hymem hzmem
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  obtain ⟨wz, hwz⟩ := hsd.toStackDisc.defined z hzmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_ternopVar_sim_swap hname hncomm hnjmp hcompute
    hops houts hxy hyz hxz hox hoy hoz rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivez
    hdepth_z hsmall_z hlenz (hsd.noSpill _) hlivey hdepth_y' hsmall_y hleny' (hsd.noSpill _) hlivex
    hdepth_x'' hsmall_x hlenx'' hwx hwy hwz hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) :=
    stepInstBase_3opVar hdispatch hops houts hwx hwy hwz
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy wz) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz rfl hlive
      (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey hdepth_y' hsmall_y
      (hsd.noSpill _) hlivex hdepth_x'' hsmall_x, hrev]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
        nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled
      = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled
      = ps.spilled
    rw [emitInputPlan_triple_var_eq (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey
      hdepth_y' hsmall_y (hsd.noSpill _) hlivex hdepth_x'' hsmall_x]
  have hlv : ∀ w, lookupVar w (gvBodyStep (inst, idx) vs)
      = lookupVar w (updateVar out (f wx wy wz) vs) :=
    fun w => (congrArg (lookupVar w) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro w hw
      have hw' : Operand.Var w ∈ ps.stack ++ [Operand.Var out] := hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with hw' | hw'
      · have hwout : w ≠ out := by rintro rfl; exact hfresh hw'
        obtain ⟨ww, hww⟩ := hsd.toStackDisc.defined w hw'
        exact ⟨ww, by rw [hlv w, lookupVar_updateVar_ne vs out w (f wx wy wz) hwout]; exact hww⟩
      · injection hw' with hw''; rw [hw'']
        exact ⟨f wx wy wz, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy wz)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Body step from the invariant — unary var op (no-swap).** The unary counterpart of
    `stackDisc_commBinopVar_step_S`: a single-operand op (ISZERO/NOT/…) discharges a `BodyStepsReady`
    entry. Membership/depth/value/freshness are derived from `StackDiscH`+`StackIsVars`; the asm runs
    via `genRegularInstPlan_unopVar_sim`; `StackDiscH k` (post-emit `StackDiscH` +
    `releaseDeadSpills_stackDiscH`, the `optimisticSwap` is a no-op via `hoptnoop`) and
    `StackIsVars (S ++ [out])` are re-established. -/
theorem stackDisc_unopVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure1 f inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by have := hsd.toStackDisc.shallow; omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_unopVar_sim hname hnjmp hcompute hops houts
    rfl hlive (hsd.noSpill _) hlivex hdepth hsmall hpeek hlen hxmem hw hfresh (hsd.noSpill _) hdisp
    hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) :=
    stepInstBase_unopVar hdispatch hops houts hw
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f w) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs) = lookupVar z (updateVar out (f w) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive (hsd.noSpill _)
      hlivex hdepth hsmall hpeek]
    simp only [hoptnoop]
  have hpsE_spill : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled = ps.spilled
    rw [hrev, emitInputPlan_single_var_eq (hsd.noSpill _) hlivex hdepth hsmall hpeek]
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w', hw'⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w', by rw [hlv z, lookupVar_updateVar_ne vs out z (f w) hzout]; exact hw'⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f w, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f w)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]; exact releaseDeadSpills_stackDiscH hsdE
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [hstateEq, releaseDeadSpills_stack, hsv, List.map_append]; rfl

/-- **Active-swap body step under the invariant — unary var op.** The unary counterpart of
    `stackDisc_commBinopVar_step_swap_P`: discharges a `BodyStepsReadyP` entry for a unary var op,
    running the active-swap unary sim and re-establishing `StackDiscH k` + `StackPerm (S ++ [out])`. -/
theorem stackDisc_unopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure1 f inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
    (hswap : ∀ d, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some d →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap d
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            d ≤ 16 ∧ d < (ps.stack ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall : dist ≤ 15 := by omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_unopVar_sim_swap hname hnjmp hcompute hops
    houts rfl hlive (hsd.noSpill _) hlivex hdepth hsmall hpeek hlen hxmem hw hfresh (hsd.noSpill _)
    hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) :=
    stepInstBase_unopVar hdispatch hops houts hw
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f w) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs) = lookupVar z (updateVar out (f w) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive (hsd.noSpill _)
      hlivex hdepth hsmall hpeek,
      show inst.operands.reverse = [Operand.Var x] from by rw [hops]; rfl]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_single_var_eq (hsd.noSpill _) hlivex hdepth hsmall hpeek]
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w', hw'⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w', by rw [hlv z, lookupVar_updateVar_ne vs out z (f w) hzout]; exact hw'⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f w, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f w)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

end EvmYul.Venom.Hol.Codegen

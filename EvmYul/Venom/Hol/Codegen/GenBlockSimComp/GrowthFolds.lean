/-
GenBlockSimComp / Phase 4 — growth-aware folds & terminator

Split part of `GenBlockSimComp`; see that module's header for the full roadmap.
This part continues the single `EvmYul.Venom.Hol.Codegen` namespace and imports
the previous part, so the whole was cut horizontally with no change in meaning.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.Producers

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ### Varying-growth spill-aware fold (HSV)

The uniform HS/HSD folds thread `StackDiscHS (l.length → 0)` and `S → S ++ [outOf x]` — a net-+1
regime that only both-live configs fit. Spilled configs *restore* operands onto the stack
(net +2/+3), so the fold must thread a **per-step gain** (the exact list of stack entries a step
appends: restored operands ++ output) and, to let a step *know* its operands' spill status, the
**exact spilled map** `M → M'`. Fuel = the total gain. This is the fuel/`S` model for feeding
spilled ops into a whole-body fold; the entry bound `StackDiscHS (totalGain l)` (the spilling
allocator's stack-bound obligation) is the caller's hypothesis, exactly as `l.length` is for HS. -/

/-- N-ary `stackPerm_of_stack_append`: appending `gain.map Var` extends the permutation invariant
    by `gain`. -/
theorem stackPerm_of_stack_append_many {S gain : List String} {ps q : PlanState}
    (h : StackPerm S ps) (hq : q.stack = ps.stack ++ gain.map Operand.Var) :
    StackPerm (S ++ gain) q := by
  show List.Perm q.stack ((S ++ gain).map Operand.Var)
  rw [hq, List.map_append]
  exact h.append_right _


/-- The `StackPerm`/spilled-map pair every HSV/HSVP packager concludes with: the final plan state is
    `releaseDeadSpills` of a state `q` whose stack grew by exactly `gain` and whose spilled map is
    `N`; the shape extends by `gain` and the map transitions by `hM'`. -/
theorem stackPerm_spilled_of_final {S gain nl : List String}
    {p q r : PlanState} {N M' : AssocList Operand Nat}
    (hsv : StackPerm S p)
    (hfinal : r = releaseDeadSpills nl q)
    (hqstack : q.stack = p.stack ++ gain.map Operand.Var)
    (hqspill : q.spilled = N)
    (hM' : ∀ q₀ : PlanState, q₀.spilled = N → (releaseDeadSpills nl q₀).spilled = M') :
    StackPerm (S ++ gain) r ∧ r.spilled = M' := by
  constructor
  · rw [hfinal]
    exact stackPerm_of_stack_append_many hsv (by rw [releaseDeadSpills_stack]; exact hqstack)
  · rw [hfinal]; exact hM' q hqspill

/-- Total stack gain of a varying-growth body: the sum of each step's gained-entry count. -/
def totalGain (l : List ((Instruction × Nat) × List String)) : Nat :=
  (l.map (fun e => e.2.length)).sum

/-- **Varying-growth spill-aware single body step.** As `BodyStepHS` but with a per-step `gain`
    (the exact stack entries the step appends — restored operands ++ output; the both-live 1-output
    case is `gain = [out]`) and the exact spilled map threaded `M → M'` (so a spilled-operand step
    can *read* its operand's slot from `M`, which `SpillFree`-style disjointness cannot supply). -/
def BodyStepHSV (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) (M : AssocList Operand Nat)
    (gain : List String) (M' : AssocList Operand Nat) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscHS (j + gain.length) p v s → StackPerm S p → p.spilled = M → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length ∧
           StackDiscHS j (gp x p).2 (gvBodyStep x v) s') ∧
    StackPerm (S ++ gain) (gp x p).2 ∧ (gp x p).2.spilled = M'

/-- Readiness for the varying-growth fold: each entry carries its gain; the stack shape and the
    exact spilled map thread through (`S ++ gain`, `M → M'` existential per step). -/
def BodyStepsReadyHSV (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List ((Instruction × Nat) × List String) → List String → AssocList Operand Nat → Prop
  | [], _, _ => True
  | x :: xs, S, M =>
      ∃ M', BodyStepHSV lo offsetToPc prog gp x.1 S M x.2 M' ∧
            BodyStepsReadyHSV lo offsetToPc prog gp xs (S ++ x.2) M'

/-- Empty varying-growth body is trivially ready. -/
theorem bodyStepsReadyHSV_nil {lo offsetToPc prog gp S M} :
    BodyStepsReadyHSV lo offsetToPc prog gp [] S M := trivial

/-- Cons a ready head (with its gain and map transition) onto a ready tail. -/
theorem bodyStepsReadyHSV_cons {lo offsetToPc prog gp x gain xs S M M'}
    (hhead : BodyStepHSV lo offsetToPc prog gp x S M gain M')
    (htail : BodyStepsReadyHSV lo offsetToPc prog gp xs (S ++ gain) M') :
    BodyStepsReadyHSV lo offsetToPc prog gp ((x, gain) :: xs) S M :=
  ⟨M', hhead, htail⟩

/-- **Varying-growth spill-aware body fold.** The `BodyStepHSV` analogue of
    `genBlockBody_sim_inv_HS`: threads `StackDiscHS (totalGain l → 0)` (fuel = total gain, not
    instruction count), `StackPerm (S0 → S0 ++ all gains)`, and the exact spilled map. Any block
    mixing both-live steps (`gain = [out]`) and *spilled* steps (`gain` = restored operands ++
    output) folds to a whole-body sim — the varying-growth regime the uniform fuel cannot fit. -/
theorem genBlockBody_sim_inv_HSV {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List ((Instruction × Nat) × List String)) :
    ∀ (S0 : List String) (M0 : AssocList Operand Nat) (ps0 : PlanState) (vs0 : VenomState)
      (as0 : AsmState),
      BodyStepsReadyHSV lo offsetToPc prog gp l S0 M0 →
      StackDiscHS (totalGain l) ps0 vs0 as0 → StackPerm S0 ps0 → ps0.spilled = M0 →
      venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x.1 v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1).length ∧
             StackDiscHS 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x.1 v) vs0) as' ∧
             StackPerm (S0 ++ l.flatMap (fun e => e.2))
               (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 M0 ps0 vs0 as0 _ hsd0 hsv0 _ hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa [totalGain] using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 M0 ps0 vs0 as0 hready hsd0 hsv0 hspM hrel0 hblock
    obtain ⟨M', hstepx, hready_xs⟩ := hready
    have key : ((x :: xs).foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2)) ([], ps0))
        = ((gp x.1 ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
              ([], (gp x.1 ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
              ([], (gp x.1 ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y.1 p) xs (gp x.1 ps0).1 (gp x.1 ps0).2
    have keyv : ((x :: xs).foldl (fun v y => gvBodyStep y.1 v) vs0)
        = xs.foldl (fun v y => gvBodyStep y.1 v) (gvBodyStep x.1 vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv, List.flatMap_cons] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscHS (totalGain xs + x.2.length) ps0 vs0 as0 := by
      have heq : totalGain (x :: xs) = totalGain xs + x.2.length := by
        simp [totalGain, Nat.add_comm]
      rw [← heq]; exact hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1, hsd1⟩, hsv1, hM1⟩ :=
      hstepx ps0 vs0 as0 (totalGain xs) hsd0' hsv0 hspM hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
          ([], (gp x.1 ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ x.2) M' (gp x.1 ps0).2 (gvBodyStep x.1 vs0) as1 hready_xs hsd1 hsv1 hM1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'

/-- An empty spilled map stays empty across `releaseDeadSpills` (the fold has nothing to release).
    Discharges the `M'`-transition hypothesis of the HSV packagers at concrete empty maps. -/
theorem releaseDeadSpills_spilled_of_nil {nl : List String} {q : PlanState}
    (h : q.spilled = ([] : AssocList Operand Nat)) :
    (releaseDeadSpills nl q).spilled = ([] : AssocList Operand Nat) := by
  unfold releaseDeadSpills
  rw [h]
  exact h


/-- Self-lookup in a single-entry map. -/
theorem alookup'_single_self {β : Type} (k : Operand) (v : β) :
    alookup' ([(k, v)] : AssocList Operand β) k = some v := by
  show AssocList.lookup _ _ [(k, v)] k = some v
  simp [AssocList.lookup]

/-- Other-key lookup in a single-entry map misses. -/
theorem alookup'_single_ne {β : Type} {w x : String} (h : w ≠ x) (off : β) :
    alookup' ([(Operand.Var w, off)] : AssocList Operand β) (Operand.Var x) = none := by
  show AssocList.lookup _ _ _ _ = none
  have hne : (Operand.Var w == Operand.Var x) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc; injection hc with hc'; exact h hc'
  simp [AssocList.lookup, hne]

/-- Removing the sole key of a single-entry map empties it. -/
theorem aremove_single_self {β : Type} (k : Operand) (v : β) :
    aremove ([(k, v)] : AssocList Operand β) k = ([] : AssocList Operand β) := by
  unfold aremove
  simp [List.filter]

/-- A single-entry spilled map whose variable is still live survives `releaseDeadSpills`
    unchanged — the `M → M` transition for a step that does not touch the spill. -/
theorem releaseDeadSpills_spilled_of_live_single {nl : List String} {q : PlanState}
    {w : String} {off : Nat}
    (h : q.spilled = ([(Operand.Var w, off)] : AssocList Operand Nat))
    (hlive : nl.contains w = true) :
    (releaseDeadSpills nl q).spilled = ([(Operand.Var w, off)] : AssocList Operand Nat) := by
  unfold releaseDeadSpills
  rw [h]
  simp only [List.foldl_cons, List.foldl_nil, hlive, if_true]
  exact h

/-- **Spilled TLOAD as a `BodyStepHSV`** — the first *spilled-operand* fold feed. The operand `x`
    sits in a spill slot, read off the threaded exact map `M` (`hxM`); the step restores it
    (gain `[x, out]`, net +2) and shrinks the map (`aremove` then `releaseDeadSpills`, transition
    supplied by `hM'` — dischargeable concretely, e.g. via `releaseDeadSpills_spilled_of_nil` when
    `x` was the last spill). Packages `stackDiscHS_tload_spilled_step_S`. -/
theorem bodyStepHSV_tload_spilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x out : String} {off idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => tload key s) inst v)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true) (hlivex : nextLiveness.contains x = true)
    (houtx : out ≠ x) (houtS : out ∉ S)
    (hxM : alookup' M (Operand.Var x) = some off)
    (houtM : alookup' M (Operand.Var out) = none)
    (hM' : ∀ q : PlanState, q.spilled = aremove M (Operand.Var x) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x, Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [x, out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hspill := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_tload_spilled_step_S (idx := idx)
    hsd hname hnjmp hcompute (hdispatch v) hops houts rfl hlive hspill hlivex hfresh houtx hspill_out
    hdisp (hoptnoop p) hrel hblock
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hemiteq : emitInputPlan inst.opcode inst.operands.reverse nextLiveness p
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { p with stack := p.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove p.spilled (Operand.Var x),
                   alloc := freeSpillSlot off p.alloc }) := by
    rw [hrev]; unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append,
      emitOneInput_var_spilled_eq hspill hlivex]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var x, Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_spilled_eq hname hnjmp hcompute hops houts rfl hlive hspill hlivex]
    show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
    rw [hoptnoop p]
  refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
    stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
  show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
      = aremove M (Operand.Var x)
  rw [hemiteq, hspM]

/-- **Spilled-operand unary op as a `BodyStepHSV`** (gain `[x, out]`, since the restore brings `x` back
    onto the stack). The op-generic twin of `bodyStepHSV_tload_spilled`; completes the unary-op matrix,
    which previously had only the both-live case. Covers ISZERO / NOT / SLOAD / EXTCODESIZE / … with a
    spilled input. -/
theorem bodyStepHSV_unopVar_spilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x out name : String} {off idx : Nat}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true) (hlivex : nextLiveness.contains x = true)
    (houtx : out ≠ x) (houtS : out ∉ S)
    (hxM : alookup' M (Operand.Var x) = some off)
    (houtM : alookup' M (Operand.Var out) = none)
    (hstepF : ∀ (v : VenomState) ww, operandVal v lo (Operand.Var x) = some ww →
        stepInstBase inst v = ExecResult.OK (updateVar out (f ww) v))
    (hM' : ∀ q : PlanState, q.spilled = aremove M (Operand.Var x) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x, Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [x, out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hspill := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_unopVar_spilled_step_S (idx := idx)
    hsd hname hnjmp hcompute hops houts rfl hlive hspill hlivex hfresh houtx hspill_out (hstepF v)
    hdisp (hoptnoop p) hrel hblock
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hemiteq : emitInputPlan inst.opcode inst.operands.reverse nextLiveness p
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { p with stack := p.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove p.spilled (Operand.Var x),
                   alloc := freeSpillSlot off p.alloc }) := by
    rw [hrev]; unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append,
      emitOneInput_var_spilled_eq hspill hlivex]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var x, Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_spilled_eq hname hnjmp hcompute hops houts rfl hlive hspill hlivex]
    show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
    rw [hoptnoop p]
  refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
    stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
  show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
      = aremove M (Operand.Var x)
  rw [hemiteq, hspM]


/-- **Both-live non-commutative binop as a `BodyStepHSV`** (gain `[out]`, map unchanged modulo
    `releaseDeadSpills`). The operands' not-spilled facts read off the threaded exact map `M` —
    the HSV counterpart of `bodyStepHSD_nonCommBinop_bothlive` (whose `SpillFree D` cannot coexist
    with a spilled-operand step in the same body). -/
theorem bodyStepHSV_nonCommBinop_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x y out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hxM : alookup' M (Operand.Var x) = none) (hyM : alookup' M (Operand.Var y) = none)
    (houtM : alookup' M (Operand.Var out) = none)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hymem := stackPerm_mem hsv hyS
  have hnospill_x := alookup_of_spilled_eq hspM hxM
  have hnospill_y := alookup_of_spilled_eq hspM hyM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_nonCommBinop_bothlive_step_S hsd hname hncomm
    hnjmp hcompute (hdispatch v) hops houts hxy rfl hxmem hymem hlive hfresh hspill_out hnospill_y
    hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y p.stack = p.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y p.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne p.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by have := hsd.shallow; omega
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy rfl hlive
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hoptnoop p]
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩



/-- **Non-vacuous varying-growth feed: spilled TLOAD then both-live binop.** The first whole-body
    readiness containing a *spilled-operand* step: entry map `M` holds exactly the spilled `x1`
    (`haremove` says removing it empties the map); step 1 restores it (gain `[x1, o1]`, map → `[]`),
    step 2 is a both-live binop over the grown shape `S ++ [x1, o1]` (gain `[o2]`, map stays `[]`).
    Feeds `genBlockBody_sim_inv_HSV` with `totalGain = 3`. -/
theorem bodyStepsReadyHSV_tload_binop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M : AssocList Operand Nat} {x1 o1 x2 y2 o2 name2 : String}
    {off idx1 idx2 : Nat} {f : bytes32 → bytes32 → bytes32}
    -- instruction 1: TLOAD with spilled operand x1
    (hname1 : opcodeToEvmName i1.opcode = some "TLOAD")
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execRead1 (fun key s => tload key s) i1 v)
    (hops1 : i1.operands = [Operand.Var x1]) (houts1 : i1.outputs = [o1])
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (ho1x1 : o1 ≠ x1) (ho1S : o1 ∉ S)
    (hxM : alookup' M (Operand.Var x1) = some off)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (haremove : aremove M (Operand.Var x1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }))
    -- instruction 2: both-live non-commutative binop over the grown shape
    (hname2 : opcodeToEvmName i2.opcode = some name2)
    (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execPure2 f i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2)
    (hx2S : x2 ∈ S ++ [x1, o1]) (hy2S : y2 ∈ S ++ [x1, o1]) (ho2S : o2 ∉ S ++ [x1, o1])
    (hlive2 : nextLiveness.contains o2 = true)
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name2 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop2 : ∀ (p : PlanState), optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o2] })) :
    BodyStepsReadyHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [x1, o1]), ((i2, idx2), [o2])] S M := by
  refine bodyStepsReadyHSV_cons (M' := ([] : AssocList Operand Nat)) ?_
    (bodyStepsReadyHSV_cons (M' := ([] : AssocList Operand Nat)) ?_ bodyStepsReadyHSV_nil)
  · exact bodyStepHSV_tload_spilled hname1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hlive1 hlivex1
      ho1x1 ho1S hxM ho1M
      (fun q hq => releaseDeadSpills_spilled_of_nil (by rw [hq, haremove]))
      hdisp1 hoptnoop1
  · exact bodyStepHSV_nonCommBinop_bothlive hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2
      hxy2 hx2S hy2S ho2S rfl rfl rfl
      (fun q hq => releaseDeadSpills_spilled_of_nil hq)
      hlive2 hlivex2 hlivey2 hdisp2 hoptnoop2


/-- **Whole-body sim with a spilled op — the varying-growth capstone.** A 2-instruction body
    `[TLOAD (x1 spilled) ; binop]` folds end-to-end under `StackDiscHS 3` (the total gain:
    +2 restore, +1 output): the asm run of the concatenated generated plans simulates the composed
    Venom body steps, re-establishing the invariant at 0 headroom and the grown stack shape
    `S ++ [x1, o1] ++ [o2]`. Instantiates `genBlockBody_sim_inv_HSV` with
    `bodyStepsReadyHSV_tload_binop` — the first whole-body simulation through a spill slot. -/
theorem genBlockBodyHSV_tload_binop_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M : AssocList Operand Nat} {x1 o1 x2 y2 o2 name2 : String}
    {off idx1 idx2 : Nat} {f : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some "TLOAD")
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execRead1 (fun key s => tload key s) i1 v)
    (hops1 : i1.operands = [Operand.Var x1]) (houts1 : i1.outputs = [o1])
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (ho1x1 : o1 ≠ x1) (ho1S : o1 ∉ S)
    (hxM : alookup' M (Operand.Var x1) = some off)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (haremove : aremove M (Operand.Var x1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }))
    (hname2 : opcodeToEvmName i2.opcode = some name2)
    (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execPure2 f i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2)
    (hx2S : x2 ∈ S ++ [x1, o1]) (hy2S : y2 ∈ S ++ [x1, o1]) (ho2S : o2 ∉ S ++ [x1, o1])
    (hlive2 : nextLiveness.contains o2 = true)
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name2 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop2 : ∀ (p : PlanState), optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o2] }))
    -- entry state: invariant at the total gain, shape S, exactly M spilled
    (hsd0 : StackDiscHS 3 ps0 vs0 as0) (hsv0 : StackPerm S ps0) (hspM : ps0.spilled = M)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([((i1, idx1), [x1, o1]), ((i2, idx2), [o2])].foldl
        (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
          false nextIsTerminator curBbLabel acc.2)).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
            curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan ([((i1, idx1), [x1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).1).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ([((i1, idx1), [x1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackDiscHS 0 ([((i1, idx1), [x1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackPerm ((S ++ [x1, o1]) ++ [o2]) ([((i1, idx1), [x1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyHSV_tload_binop (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (curBbLabel := curBbLabel)
    (idx1 := idx1) (idx2 := idx2)
    hname1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hlive1 hlivex1 ho1x1 ho1S hxM ho1M haremove
    hdisp1 hoptnoop1 hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S ho2S
    hlive2 hlivex2 hlivey2 hdisp2 hoptnoop2
  obtain ⟨as', hrun, hrel', hpc, hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSV
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [x1, o1]), ((i2, idx2), [o2])] S M ps0 vs0 as0 hready hsd0 hsv0 hspM hrel0 hblock
  refine ⟨as', hrun, ?_, ?_, ?_⟩
  · simpa using hrel'
  · simpa using hsd'
  · simpa [List.append_assoc] using hsv'















/-- **Both-live 1-input read as a `BodyStepHSV`** (gain `[out]`; generic over the read `f` —
    TLOAD/SLOAD/CALLDATALOAD/account queries), for mixed spilled blocks. -/
theorem bodyStepHSV_unopVar_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x out name : String} {idx : Nat}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hxM : alookup' M (Operand.Var x) = none) (houtM : alookup' M (Operand.Var out) = none)
    (hlivex : nextLiveness.contains x = true)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hstepF : ∀ (v : VenomState) (ww : bytes32), operandVal v lo (Operand.Var x) = some ww →
        stepInstBase inst v = ExecResult.OK (updateVar out (f ww) v))
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hnospill := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_unopVar_bothlive_step_S (idx := idx)
    hsd hname hnjmp hcompute hops houts rfl hxmem hlive hfresh hspill_out hnospill hlivex
    (hstepF v) hdisp (hoptnoop p) hrel hblock
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by
    have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
  have hpeek : stackPeek dist p.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
        hdepth hsmall hpeek, hoptnoop p]
    rw [hrev, emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek]
  exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩

/-- **Both-live TLOAD as a `BodyStepHSV`** (gain `[out]`). Completes the state-read row of the matrix. -/
theorem bodyStepHSV_tload_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hxM : alookup' M (Operand.Var x) = none) (houtM : alookup' M (Operand.Var out) = none)
    (hlivex : nextLiveness.contains x = true)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => tload key s) inst v)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hnospill := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_tload_bothlive_step_S (idx := idx)
    hsd hname hnjmp hcompute hops houts rfl hxmem hlive hfresh hspill_out hnospill hlivex
    (hdispatch v) hdisp (hoptnoop p) hrel hblock
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by
    have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
  have hpeek : stackPeek dist p.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
        hdepth hsmall hpeek, hoptnoop p]
    rw [hrev, emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek]
  exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩


/-- **Both-live SLOAD as a `BodyStepHSV`** (gain `[out]`). Completes the state-read row of the matrix. -/
theorem bodyStepHSV_sload_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hxM : alookup' M (Operand.Var x) = none) (houtM : alookup' M (Operand.Var out) = none)
    (hlivex : nextLiveness.contains x = true)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => sload key s) inst v)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hnospill := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_sload_bothlive_step_S (idx := idx)
    hsd hname hnjmp hcompute hops houts rfl hxmem hlive hfresh hspill_out hnospill hlivex
    (hdispatch v) hdisp (hoptnoop p) hrel hblock
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by
    have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
  have hpeek : stackPeek dist p.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
        hdepth hsmall hpeek, hoptnoop p]
    rw [hrev, emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek]
  exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩


/-- **0-input context-push read as a `BodyStepHSV`** (gain `[out]`; ADDRESS/CALLER/…). The pushed
    value is supplied per-state by `hpushFn` (its Venom step and the matching asm push under the
    relation), for mixed spilled blocks. -/
theorem bodyStepHSV_read0
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {out name : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (houtM : alookup' M (Operand.Var out) = none)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hpushFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ val, stepInstBase inst v = ExecResult.OK (updateVar out val v) ∧
          (∀ (h : s.pc < prog.length), prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
            asmStep offsetToPc prog s = asmPushVal val s))
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { p with stack := p.stack ++ [Operand.Var out] }
      = ([], { p with stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hspill_out := alookup_of_spilled_eq hspM houtM
  obtain ⟨val, hstepEq, hdisp⟩ := hpushFn p v s hrel
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_read0_step_S (idx := idx)
    hsd hname hnjmp hcompute hops houts rfl hlive hfresh hspill_out hstepEq hdisp (hoptnoop p)
    hrel hblock
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive, hoptnoop p]
  exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩



/-! ### Peak-aware refinement (HSVP): padded varying-growth fold

`BodyStepHSV`'s fuel is the *net* gain, which under-serves net-0 ops with a transient DUP peak
(copy runs at `k+1`, LOG at `k+n`). The refinement threads a uniform padding `P` (≥ the maximum
peak excess over the block) on top of the net-gain fuel: each step receives
`StackDiscHS (j + gain.length + P)` and returns `StackDiscHS (j + P)`. Existing `BodyStepHSV`
feeds lift verbatim (`bodyStepHSVP_of_bodyStepHSV`); the peaked ops consume padding transiently
and *restore* it via `StackDiscHS.rebuild` — sound because their stack length is unchanged, so the
pre-state's shallow bound re-establishes the full padded headroom on the post state. -/

/-- Padded varying-growth single body step: as `BodyStepHSV` with `P` extra headroom threaded
    through unchanged (available for a step's transient DUP peak). -/
def BodyStepHSVP (P : Nat) (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) (M : AssocList Operand Nat)
    (gain : List String) (M' : AssocList Operand Nat) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscHS (j + gain.length + P) p v s → StackPerm S p → p.spilled = M →
    venomAsmRel lo p v s → asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length ∧
           StackDiscHS (j + P) (gp x p).2 (gvBodyStep x v) s') ∧
    StackPerm (S ++ gain) (gp x p).2 ∧ (gp x p).2.spilled = M'

/-- Every net-gain feed is a padded feed (instantiate at `j + P`). -/
theorem bodyStepHSVP_of_bodyStepHSV {P lo offsetToPc prog gp x S M gain M'}
    (h : BodyStepHSV lo offsetToPc prog gp x S M gain M') :
    BodyStepHSVP P lo offsetToPc prog gp x S M gain M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have heq : j + gain.length + P = (j + P) + gain.length := by omega
  exact h p v s (j + P) (by rw [← heq]; exact hsd) hsv hspM hrel hblock

/-- Readiness for the padded fold (same threading as `BodyStepsReadyHSV`). -/
def BodyStepsReadyHSVP (P : Nat) (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List ((Instruction × Nat) × List String) → List String → AssocList Operand Nat → Prop
  | [], _, _ => True
  | x :: xs, S, M =>
      ∃ M', BodyStepHSVP P lo offsetToPc prog gp x.1 S M x.2 M' ∧
            BodyStepsReadyHSVP P lo offsetToPc prog gp xs (S ++ x.2) M'

theorem bodyStepsReadyHSVP_nil {P lo offsetToPc prog gp S M} :
    BodyStepsReadyHSVP P lo offsetToPc prog gp [] S M := trivial

theorem bodyStepsReadyHSVP_cons {P lo offsetToPc prog gp x gain xs S M M'}
    (hhead : BodyStepHSVP P lo offsetToPc prog gp x S M gain M')
    (htail : BodyStepsReadyHSVP P lo offsetToPc prog gp xs (S ++ gain) M') :
    BodyStepsReadyHSVP P lo offsetToPc prog gp ((x, gain) :: xs) S M :=
  ⟨M', hhead, htail⟩

/-- **Padded varying-growth body fold**: entry fuel `totalGain l + P`, exit `StackDiscHS P`. Admits
    blocks mixing spilled steps, both-live steps, and transiently-peaked net-0 steps (copy/LOG with
    peak excess ≤ `P`). -/
theorem genBlockBody_sim_inv_HSVP {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List ((Instruction × Nat) × List String)) :
    ∀ (S0 : List String) (M0 : AssocList Operand Nat) (ps0 : PlanState) (vs0 : VenomState)
      (as0 : AsmState),
      BodyStepsReadyHSVP P lo offsetToPc prog gp l S0 M0 →
      StackDiscHS (totalGain l + P) ps0 vs0 as0 → StackPerm S0 ps0 → ps0.spilled = M0 →
      venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x.1 v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1).length ∧
             StackDiscHS P
               (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x.1 v) vs0) as' ∧
             StackPerm (S0 ++ l.flatMap (fun e => e.2))
               (l.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 M0 ps0 vs0 as0 _ hsd0 hsv0 _ hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa [totalGain] using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 M0 ps0 vs0 as0 hready hsd0 hsv0 hspM hrel0 hblock
    obtain ⟨M', hstepx, hready_xs⟩ := hready
    have key : ((x :: xs).foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2)) ([], ps0))
        = ((gp x.1 ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
              ([], (gp x.1 ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
              ([], (gp x.1 ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y.1 p) xs (gp x.1 ps0).1 (gp x.1 ps0).2
    have keyv : ((x :: xs).foldl (fun v y => gvBodyStep y.1 v) vs0)
        = xs.foldl (fun v y => gvBodyStep y.1 v) (gvBodyStep x.1 vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv, List.flatMap_cons] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscHS (totalGain xs + x.2.length + P) ps0 vs0 as0 := by
      have heq : totalGain (x :: xs) + P = totalGain xs + x.2.length + P := by
        simp [totalGain]; omega
      rw [← heq]; exact hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1, hsd1⟩, hsv1, hM1⟩ :=
      hstepx ps0 vs0 as0 (totalGain xs) hsd0' hsv0 hspM hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y.1 acc.2).1, (gp y.1 acc.2).2))
          ([], (gp x.1 ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ x.2) M' (gp x.1 ps0).2 (gvBodyStep x.1 vs0) as1 hready_xs hsd1 hsv1 hM1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'


/-- **Both-live LOG as a padded feed** (gain `[]`, peak `n ≤ P`): consumes `n` padding transiently
    for the DUP chain and restores it via `StackDiscHS.rebuild` — sound because LOG is net 0, so the
    pre-state's shallow bound re-establishes the full padded headroom. Per-state facts via `hlogFn`
    (as `bodyStepH_log`). -/
theorem bodyStepHSVP_log_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S es : List String} {M M' : AssocList Operand Nat} {tc : bytes32} {n idx : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S) (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4) (hnP : n ≤ P)
    (hnospillM : ∀ v ∈ es, alookup' M (Operand.Var v) = none)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hlogFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = ((offset :: size :: topics).map some) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase inst v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hmemes : ∀ w ∈ es, Operand.Var w ∈ p.stack := fun w hw => stackPerm_mem hsv (hesS w hw)
  have hnospill : ∀ w ∈ es, alookup' p.spilled (Operand.Var w) = none := by
    intro w hw; rw [hspM]; exact hnospillM w hw
  have hshallow0 := hsd.shallow
  simp only [List.length_nil] at hshallow0
  have hbound : p.stack.length + es.length ≤ 17 := by omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds es p.stack hbound hnd hmemes hlive
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hstepEq⟩ := hlogFn p v s hrel
  have hsd2 : StackDiscHS ((j + P - n) + n) p v s := by
    have heq : (j + P - n) + n = j + ([] : List String).length + P := by
      simp only [List.length_nil]; omega
    rw [heq]; exact hsd
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_log_bothlive_step_S (idx := idx)
    hsd2 hopc hhead hcompute houts hnd hmemes hnospill hlive hlenes htc hn htlen hvals hcov
    hbelow hsize hstepEq hrel hblock
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness p).2 with
        stack := p.stack } : PlanState) = { p with stack := p.stack } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness es dists p hnospill hdepths]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness { p with stack := p.stack } := by
    rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths, hstateEq]
  have hlen : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2.stack.length = p.stack.length := by
    rw [hfinal, releaseDeadSpills_stack]
  refine ⟨⟨as', hrun, hrel', hpc, ?_⟩,
    stackPerm_spilled_of_final hsv hfinal (by simp) hspM hM'⟩
  refine hsd'.rebuild (Nat.le_refl _) (fun _ _ h => h) ?_ hsd'.defined
  rw [hlen]; omega

/-- **Both-live CALLDATACOPY as a padded feed** (gain `[]`, peak `1 ≤ P`): the 3-deep DUP chain
    consumes one padding unit transiently, restored after the copy (net 0). Per-state semantics /
    memory-safety / spill-region facts via `hcopyFn`. -/
theorem bodyStepHSVP_calldatacopy_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S : List String} {M M' : AssocList Operand Nat} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hP : 1 ≤ P)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (haM : alookup' M (Operand.Var a) = none) (hbM : alookup' M (Operand.Var b) = none)
    (hcM : alookup' M (Operand.Var c) = none)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true)
    (hlivec : nextLiveness.contains c = true)
    (hM' : ∀ q : PlanState, q.spilled = M → (releaseDeadSpills nextLiveness q).spilled = M')
    (hcopyFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        p.spilled = M →
        (∀ wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
          stepInstBase inst v = ExecResult.OK
            (writeMemoryWithExpansion wa.toNat
              ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v)) ∧
        (∀ wa wc, operandVal v lo (Operand.Var a) = some wa → operandVal v lo (Operand.Var c) = some wc →
          wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) ∧
        (∀ op off', AssocList.lookup Operand Nat p.spilled op = some off' → p.alloc.fnEom ≤ off')) :
    BodyStepHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hamem := stackPerm_mem hsv haS
  have hbmem := stackPerm_mem hsv hbS
  have hcmem := stackPerm_mem hsv hcS
  have hnospill_a := alookup_of_spilled_eq hspM haM
  have hnospill_b := alookup_of_spilled_eq hspM hbM
  have hnospill_c := alookup_of_spilled_eq hspM hcM
  obtain ⟨hstepEqF, hmemsafe, hspillReg⟩ := hcopyFn p v s hrel hspM
  have hshallow0 := hsd.shallow
  simp only [List.length_nil] at hshallow0
  have hsd2 : StackDiscHS ((j + P - 1) + 1) p v s := by
    have heq : (j + P - 1) + 1 = j + ([] : List String).length + P := by
      simp only [List.length_nil]; omega
    rw [heq]; exact hsd
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_calldatacopy_bothlive_step_S (idx := idx)
    hsd2 hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hamem hbmem hcmem
    hnospill_c hlivec hnospill_b hliveb hnospill_a hlivea hstepEqF hmemsafe hspillReg hrel hblock
  have hshallow : p.stack.length ≤ 14 := by omega
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    ternopVar_depths_of_shallow (x := a) (y := b) (z := c) hshallow hab hbc hac hamem hbmem hcmem
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack } : PlanState) = { p with stack := p.stack } := by
    rw [hrev, emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb
      hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness { p with stack := p.stack } := by
    rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac rfl
        hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea
        hdepth_a hsmall_a, hstateEq]
  have hlen : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2.stack.length = p.stack.length := by
    rw [hfinal, releaseDeadSpills_stack]
  refine ⟨⟨as', hrun, hrel', hpc, ?_⟩,
    stackPerm_spilled_of_final hsv hfinal (by simp) hspM hM'⟩
  refine hsd'.rebuild (Nat.le_refl _) (fun _ _ h => h) ?_ hsd'.defined
  rw [hlen]; omega


/-- **Padded-fold readiness: spilled TLOAD then both-live LOG.** The first readiness mixing a
    *spilled* step (gain `[x1, o1]`, map emptied) with a *transiently peaked* net-0 step (LOG,
    gain `[]`, peak `n ≤ P`): the TLOAD feed lifts from the net-gain world
    (`bodyStepHSVP_of_bodyStepHSV`), the LOG feed borrows and restores padding. -/
theorem bodyStepsReadyHSVP_tload_log
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S es : List String} {M : AssocList Operand Nat} {x1 o1 : String} {tc : bytes32}
    {off n idx1 idx2 : Nat}
    -- instruction 1: TLOAD with spilled operand x1 (the only spill in M)
    (hname1 : opcodeToEvmName i1.opcode = some "TLOAD")
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execRead1 (fun key s => tload key s) i1 v)
    (hops1 : i1.operands = [Operand.Var x1]) (houts1 : i1.outputs = [o1])
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (ho1x1 : o1 ≠ x1) (ho1S : o1 ∉ S)
    (hxM : alookup' M (Operand.Var x1) = some off)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (haremove : aremove M (Operand.Var x1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }))
    -- instruction 2: both-live LOG over the grown shape (peak n ≤ P)
    (hopc2 : i2.opcode = Opcode.LOG) (hhead2 : i2.operands.head! = Operand.Lit tc)
    (hcompute2 : computeOperands i2 = es.map Operand.Var) (houts2 : i2.outputs = [])
    (hnd2 : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S ++ [x1, o1])
    (hlive2 : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4) (hnP : n ≤ P)
    (hlogFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = ((offset :: size :: topics).map some) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase i2 v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepsReadyHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [x1, o1]), ((i2, idx2), [])] S M := by
  refine bodyStepsReadyHSVP_cons (M' := ([] : AssocList Operand Nat)) ?_
    (bodyStepsReadyHSVP_cons (M' := ([] : AssocList Operand Nat)) ?_ bodyStepsReadyHSVP_nil)
  · exact bodyStepHSVP_of_bodyStepHSV
      (bodyStepHSV_tload_spilled hname1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hlive1 hlivex1
        ho1x1 ho1S hxM ho1M
        (fun q hq => releaseDeadSpills_spilled_of_nil (by rw [hq, haremove]))
        hdisp1 hoptnoop1)
  · exact bodyStepHSVP_log_bothlive hopc2 hhead2 hcompute2 houts2 hnd2 hesS hlive2 hlenes htc hn hnP
      (fun v _ => rfl)
      (fun q hq => releaseDeadSpills_spilled_of_nil hq)
      hlogFn

/-- **Whole-body sim through a spill slot AND a transient peak — the padded-fold capstone.** The
    body `[TLOAD (x1 spilled) ; LOG]` folds end-to-end under `StackDiscHS (2 + P)` (net gain 2 for
    the restore+output, padding `P ≥ n` for LOG's DUP chain, restored after): the asm run of the
    concatenated generated plans simulates the composed Venom steps, exiting at `StackDiscHS P` with
    stack shape grown exactly by `[x1, o1]`. Instantiates `genBlockBody_sim_inv_HSVP` with
    `bodyStepsReadyHSVP_tload_log`. -/
theorem genBlockBodyHSVP_tload_log_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S es : List String} {M : AssocList Operand Nat} {x1 o1 : String} {tc : bytes32}
    {off n idx1 idx2 : Nat} {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some "TLOAD")
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execRead1 (fun key s => tload key s) i1 v)
    (hops1 : i1.operands = [Operand.Var x1]) (houts1 : i1.outputs = [o1])
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (ho1x1 : o1 ≠ x1) (ho1S : o1 ∉ S)
    (hxM : alookup' M (Operand.Var x1) = some off)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (haremove : aremove M (Operand.Var x1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x1, Operand.Var o1] }))
    (hopc2 : i2.opcode = Opcode.LOG) (hhead2 : i2.operands.head! = Operand.Lit tc)
    (hcompute2 : computeOperands i2 = es.map Operand.Var) (houts2 : i2.outputs = [])
    (hnd2 : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S ++ [x1, o1])
    (hlive2 : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4) (hnP : n ≤ P)
    (hlogFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = ((offset :: size :: topics).map some) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase i2 v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hsd0 : StackDiscHS (2 + P) ps0 vs0 as0) (hsv0 : StackPerm S ps0) (hspM : ps0.spilled = M)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([((i1, idx1), [x1, o1]), ((i2, idx2), ([] : List String))].foldl
        (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
          false nextIsTerminator curBbLabel acc.2)).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
            curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan ([((i1, idx1), [x1, o1]), ((i2, idx2), ([] : List String))].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).1).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ([((i1, idx1), [x1, o1]), ((i2, idx2), ([] : List String))].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackDiscHS P ([((i1, idx1), [x1, o1]), ((i2, idx2), ([] : List String))].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackPerm (S ++ [x1, o1]) ([((i1, idx1), [x1, o1]), ((i2, idx2), ([] : List String))].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyHSVP_tload_log (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (curBbLabel := curBbLabel)
    (nextIsTerminator := nextIsTerminator) (idx1 := idx1) (idx2 := idx2)
    hname1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hlive1 hlivex1 ho1x1 ho1S hxM ho1M haremove
    hdisp1 hoptnoop1 hopc2 hhead2 hcompute2 houts2 hnd2 hesS hlive2 hlenes htc hn hnP hlogFn
  obtain ⟨as', hrun, hrel', hpc, hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSVP P
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [x1, o1]), ((i2, idx2), [])] S M ps0 vs0 as0 hready
      (by simpa [totalGain] using hsd0) hsv0 hspM hrel0 hblock
  refine ⟨as', hrun, ?_, ?_, ?_⟩
  · simpa using hrel'
  · simpa using hsd'
  · simpa using hsv'

/-- **`StackDiscHS` preservation across a z-spilled ternop** (net +2: kept restored `z` + `out`;
    `StackDiscHS (k+2) → k`). The 3-ary analogue of `stackDiscHS_binop_valspilled_preserve`. -/
theorem stackDiscHS_ternop_zspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y z out name : String} {base : List Operand} {offz d_y d_x idx k : Nat} {w : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hspill_z : alookup' ps.spilled (Operand.Var z) = some offz)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 2 ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15)
    (hdef_z : ∃ wz, lookupVar z vs = some wz)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out w vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var z, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var z, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_zspilled_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz
      hstack0 hlive hspill_z hlivez hnospill_y hlivey hnospill_x hlivex hdepth_y hsmall_y
      hdepth_x hsmall_x, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var z, Operand.Var out] } : PlanState)
      = { ps with stack := base ++ [Operand.Var z, Operand.Var out],
                  spilled := aremove ps.spilled (Operand.Var z),
                  alloc := freeSpillSlot offz ps.alloc } := by
    rw [hrev, emit3_zspilled hstack0 hspill_z hlivez hnospill_y hlivey hnospill_x hlivex
      hyz hxz hxy hdepth_y hsmall_y hdepth_x hsmall_x]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out w vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var z) o off' hlook
  · show (base ++ [Operand.Var z, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro v hv
    show ∃ ww, lookupVar v { updateVar out w vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar v { updateVar out w vs with instIdx := idx + 1 }
        = lookupVar v (updateVar out w vs) := rfl
    rw [hlk]
    change Operand.Var v ∈ base ++ [Operand.Var z, Operand.Var out] at hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · have hvout : v ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined v (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out v w hvout]; exact hww⟩
    · injection h with h'
      obtain ⟨wz, hwz⟩ := hdef_z
      exact ⟨wz, by rw [h', lookupVar_updateVar_ne vs out z w (Ne.symm hoz)]; exact hwz⟩
    · injection h with h'
      exact ⟨w, by rw [h']; exact lookupVar_updateVar_self vs out w⟩

/-- **Spill-aware body step for a z-spilled ternop** — the first spilled ternary fold producer:
    `StackDiscHS (k+2)` drives the restore+dups, the ternop over the positioned top three, and the
    output push; re-established at `k` with `StackDiscHS` bundled inside the existential. -/
theorem stackDiscHS_ternopVar_zspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y z out : String} {base : List Operand} {name : String}
    {offz idx k : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_z : alookup' ps.spilled (Operand.Var z) = some offz)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var z, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var z, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y + 2 ≤ 15 := by have := hsd.shallow; omega
  have hsmall_x : d_x + 3 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wz, hwz⟩ := venomAsmRel_spilled_defined hrel hspill_z
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hvz : operandVal vs lo (Operand.Var z) = some wz := by
    rw [operandVal_var_eq_lookupVar]; exact hwz
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) := by
    rw [hdispatch]; unfold execPure3; rw [hops, houts]
    simp only [evalOperand, hwx, hwy, hwz]
  have hsim := genRegularInstPlan_ternopVar_zspilled_sim hname hncomm hnjmp hcompute hops houts
    hxy hyz hxz hox hoy hstack0 hlive hfresh hspill_out hspill_z hlivez hnospill_y hlivey
    hnospill_x hlivex hdepth_y hsmall_y hdepth_x hsmall_x hvx hvy hvz hsd.spillWf hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_ternop_zspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hyz hxz hoz hstack0 hlive hfresh hspill_z hlivez hnospill_y hlivey hnospill_x
    hlivex hdepth_y hsmall_y hdepth_x hsmall_x ⟨wz, hwz⟩ hstepEq hoptnoop


/-- **`StackDiscHS` preservation across a first-spilled ternop** (net +2: kept restored `x` + `out`;
    `StackDiscHS (k+2) → k`). The x-spilled (non-positioned, reordered) twin of the z-spilled preservation. -/
theorem stackDiscHS_ternop_xspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y z out name : String} {base : List Operand} {offx d_z d_y idx k : Nat} {w : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y + 1 ≤ 15)
    (hdef_x : ∃ wx, lookupVar x vs = some wx)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out w vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_xspilled_eq hname hncomm hnjmp hcompute hops houts hyz hxz
      hstack0 hlive hnospill_z hlivez hnospill_y hlivey hspill_x hlivex hdepth_z hsmall_z
      hdepth_y hsmall_y, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var x, Operand.Var out] } : PlanState)
      = { ps with stack := base ++ [Operand.Var x, Operand.Var out],
                  spilled := aremove ps.spilled (Operand.Var x),
                  alloc := freeSpillSlot offx ps.alloc } := by
    rw [hrev, emit3_xspilled hstack0 hnospill_z hlivez hnospill_y hlivey hspill_x hlivex
      hyz hdepth_z hsmall_z hdepth_y hsmall_y]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out w vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var x) o off' hlook
  · show (base ++ [Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro v hv
    show ∃ ww, lookupVar v { updateVar out w vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar v { updateVar out w vs with instIdx := idx + 1 }
        = lookupVar v (updateVar out w vs) := rfl
    rw [hlk]
    change Operand.Var v ∈ base ++ [Operand.Var x, Operand.Var out] at hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · have hvout : v ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined v (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out v w hvout]; exact hww⟩
    · injection h with h'
      obtain ⟨wx, hwx⟩ := hdef_x
      exact ⟨wx, by rw [h', lookupVar_updateVar_ne vs out x w (Ne.symm hox)]; exact hwx⟩
    · injection h with h'
      exact ⟨w, by rw [h']; exact lookupVar_updateVar_self vs out w⟩

/-- **Spill-aware body step for a first-spilled ternop** — the non-positioned spilled ternary
    producer: `StackDiscHS (k+2)` drives the emission, the proven `SWAP3;SWAP2;SWAP1` reorder, the
    ternop, and the output push; re-established at `k`. -/
theorem stackDiscHS_ternopVar_xspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y z out : String} {base : List Operand} {name : String}
    {offx idx k : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hzmem : Operand.Var z ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_z : d_z ≤ 15 := by have := hsd.shallow; omega
  have hsmall_y : d_y + 1 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wz, hwz⟩ := hsd.defined z hzmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  have hvz : operandVal vs lo (Operand.Var z) = some wz := hwz
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by
    rw [operandVal_var_eq_lookupVar]; exact hwx
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) := by
    rw [hdispatch]; unfold execPure3; rw [hops, houts]
    simp only [evalOperand, hwx, hwy, hwz]
  have hsim := genRegularInstPlan_ternopVar_xspilled_sim hname hncomm hnjmp hcompute hops houts
    hyz hxz hox hoy hoz hstack0 hlive hfresh hspill_out hnospill_z hlivez hnospill_y hlivey
    hspill_x hlivex hdepth_z hsmall_z hdepth_y hsmall_y hvx hvy hvz hsd.spillWf hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_ternop_xspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hyz hxz hox hstack0 hlive hfresh hnospill_z hlivez hnospill_y hlivey hspill_x
    hlivex hdepth_z hsmall_z hdepth_y hsmall_y ⟨wx, hwx⟩ hstepEq hoptnoop


/-- **`StackDiscHS` preservation across a mid-spilled ternop** (net +2: kept restored `y` + `out`;
    `StackDiscHS (k+2) → k`). The y-spilled (4-swap reorder) twin of the x-spilled preservation. -/
theorem stackDiscHS_ternop_yspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y z out name : String} {base : List Operand} {offy d_z d_x idx k : Nat} {w : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 3 ≤ 15)
    (hdef_y : ∃ wy, lookupVar y vs = some wy)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out w vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_yspilled_eq hname hncomm hnjmp hcompute hops houts hxy hxz
      hyz hstack0 hlive hnospill_z hlivez hspill_y hlivey hnospill_x hlivex hdepth_z hsmall_z
      hdepth_x hsmall_x, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var y, Operand.Var out] } : PlanState)
      = { ps with stack := base ++ [Operand.Var y, Operand.Var out],
                  spilled := aremove ps.spilled (Operand.Var y),
                  alloc := freeSpillSlot offy ps.alloc } := by
    rw [hrev, emit3_yspilled hstack0 hnospill_z hlivez hspill_y hlivey hnospill_x hlivex
      hxy hxz hdepth_z hsmall_z hdepth_x hsmall_x]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out w vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off' hlook
  · show (base ++ [Operand.Var y, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro v hv
    show ∃ ww, lookupVar v { updateVar out w vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar v { updateVar out w vs with instIdx := idx + 1 }
        = lookupVar v (updateVar out w vs) := rfl
    rw [hlk]
    change Operand.Var v ∈ base ++ [Operand.Var y, Operand.Var out] at hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · have hvout : v ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined v (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out v w hvout]; exact hww⟩
    · injection h with h'
      obtain ⟨wy, hwy⟩ := hdef_y
      exact ⟨wy, by rw [h', lookupVar_updateVar_ne vs out y w (Ne.symm hoy)]; exact hwy⟩
    · injection h with h'
      exact ⟨w, by rw [h']; exact lookupVar_updateVar_self vs out w⟩

/-- **Spill-aware body step for a mid-spilled ternop**: `StackDiscHS (k+2)` drives the emission,
    the proven `SWAP3;SWAP2;SWAP1;SWAP3` reorder (equal-`y` SWAP1 no-op included), the ternop, and
    the output push; re-established at `k`. -/
theorem stackDiscHS_ternopVar_yspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y z out : String} {base : List Operand} {name : String}
    {offy idx k : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hzmem : Operand.Var z ∈ ps.stack) (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_z : d_z ≤ 15 := by have := hsd.shallow; omega
  have hsmall_x : d_x + 3 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wz, hwz⟩ := hsd.defined z hzmem
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvz : operandVal vs lo (Operand.Var z) = some wz := hwz
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by
    rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) := by
    rw [hdispatch]; unfold execPure3; rw [hops, houts]
    simp only [evalOperand, hwx, hwy, hwz]
  have hsim := genRegularInstPlan_ternopVar_yspilled_sim hname hncomm hnjmp hcompute hops houts
    hxy hxz hyz hox hoy hoz hstack0 hlive hfresh hspill_out hnospill_z hlivez hspill_y hlivey
    hnospill_x hlivex hdepth_z hsmall_z hdepth_x hsmall_x hvx hvy hvz hsd.spillWf hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_ternop_yspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hxz hyz hoy hstack0 hlive hfresh hnospill_z hlivez hspill_y hlivey hnospill_x
    hlivex hdepth_z hsmall_z hdepth_x hsmall_x ⟨wy, hwy⟩ hstepEq hoptnoop


/-- **Mid-spilled ternop as a `BodyStepHSV`** (gain `[y, out]`, the map loses `y`): restore +
    4-swap reorder + ternop under the varying-growth fold — the spilled ternary matrix is now
    closed (z/x/y positions all fed). -/
theorem bodyStepHSV_ternopVar_yspilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x y z out name : String} {offy idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hzS : z ∈ S) (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (houtM : alookup' M (Operand.Var out) = none)
    (hzM : alookup' M (Operand.Var z) = none) (hlivez : nextLiveness.contains z = true)
    (hyM : alookup' M (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hxM : alookup' M (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hM' : ∀ q : PlanState, q.spilled = aremove M (Operand.Var y) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var y, Operand.Var out] })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [y, out] M' := by
  intro p v s j hsd hsv hspM hrel hblock
  have hzmem := stackPerm_mem hsv hzS
  have hxmem := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hnospill_z := alookup_of_spilled_eq hspM hzM
  have hspill_y := alookup_of_spilled_eq hspM hyM
  have hnospill_x := alookup_of_spilled_eq hspM hxM
  have hspill_out := alookup_of_spilled_eq hspM houtM
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_ternopVar_yspilled_step_S (idx := idx)
    hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy hxz hyz hox hoy hoz rfl
    hzmem hxmem hlive hfresh hspill_out hnospill_z hlivez hspill_y hlivey hnospill_x hlivex
    hdisp (hoptnoop p) hrel hblock
  obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_z : d_z ≤ 15 := by
    have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
  have hsmall_x : d_x + 3 ≤ 15 := by
    have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var y, Operand.Var out] } := by
    rw [genRegularInstPlan_ternopVar_yspilled_eq hname hncomm hnjmp hcompute hops houts hxy hxz
        hyz rfl hlive hnospill_z hlivez hspill_y hlivey hnospill_x hlivex hdepth_z hsmall_z
        hdepth_x hsmall_x]
    show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
    rw [hoptnoop p]
  refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
    stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
  show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
      = aremove M (Operand.Var y)
  rw [hrev, emit3_yspilled rfl hnospill_z hlivez hspill_y hlivey hnospill_x hlivex hxy hxz
    hdepth_z hsmall_z hdepth_x hsmall_x, hspM]


/-- **Non-vacuous varying-growth feed through a reordered spill: mid-spilled ternop then both-live
    binop.** The first whole-body readiness containing a *non-positioned* spilled step: step 1
    restores the mid operand `y1` and runs the proven `SWAP3;SWAP2;SWAP1;SWAP3` reorder
    (gain `[y1, o1]`, map → `[]`), step 2 is a both-live binop over the grown shape `S ++ [y1, o1]`
    (gain `[o2]`). Feeds `genBlockBody_sim_inv_HSV` with `totalGain = 3`. -/
theorem bodyStepsReadyHSV_ternopYspilled_binop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M : AssocList Operand Nat} {x1 y1 z1 o1 x2 y2 o2 name1 name2 : String}
    {off idx1 idx2 : Nat} {f3 : bytes32 → bytes32 → bytes32 → bytes32} {f : bytes32 → bytes32 → bytes32}
    -- instruction 1: non-commutative ternop with the MID operand y1 spilled
    (hname1 : opcodeToEvmName i1.opcode = some name1)
    (hncomm1 : isCommutative i1.opcode = false)
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execPure3 f3 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1, Operand.Var z1])
    (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hxz1 : x1 ≠ z1) (hyz1 : y1 ≠ z1)
    (ho1x : o1 ≠ x1) (ho1y : o1 ≠ y1) (ho1z : o1 ≠ z1)
    (hz1S : z1 ∈ S) (hx1S : x1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (hz1M : alookup' M (Operand.Var z1) = none) (hlivez1 : nextLiveness.contains z1 = true)
    (hy1M : alookup' M (Operand.Var y1) = some off) (hlivey1 : nextLiveness.contains y1 = true)
    (hx1M : alookup' M (Operand.Var x1) = none) (hlivex1 : nextLiveness.contains x1 = true)
    (haremove : aremove M (Operand.Var y1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name1 → asmStep offsetToPc prog s = asmTernop f3 s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var y1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var y1, Operand.Var o1] }))
    -- instruction 2: both-live non-commutative binop over the grown shape
    (hname2 : opcodeToEvmName i2.opcode = some name2)
    (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execPure2 f i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2)
    (hx2S : x2 ∈ S ++ [y1, o1]) (hy2S : y2 ∈ S ++ [y1, o1]) (ho2S : o2 ∉ S ++ [y1, o1])
    (hlive2 : nextLiveness.contains o2 = true)
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name2 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop2 : ∀ (p : PlanState), optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o2] })) :
    BodyStepsReadyHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [y1, o1]), ((i2, idx2), [o2])] S M := by
  refine bodyStepsReadyHSV_cons (M' := ([] : AssocList Operand Nat)) ?_
    (bodyStepsReadyHSV_cons (M' := ([] : AssocList Operand Nat)) ?_ bodyStepsReadyHSV_nil)
  · exact bodyStepHSV_ternopVar_yspilled hname1 hncomm1 hnjmp1 hcompute1 hdispatch1 hops1 houts1
      hxy1 hxz1 hyz1 ho1x ho1y ho1z hz1S hx1S ho1S hlive1 ho1M hz1M hlivez1 hy1M hlivey1
      hx1M hlivex1
      (fun q hq => releaseDeadSpills_spilled_of_nil (by rw [hq, haremove]))
      hdisp1 hoptnoop1
  · exact bodyStepHSV_nonCommBinop_bothlive hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2
      hxy2 hx2S hy2S ho2S rfl rfl rfl
      (fun q hq => releaseDeadSpills_spilled_of_nil hq)
      hlive2 hlivex2 hlivey2 hdisp2 hoptnoop2

/-- **Whole-body sim through a REORDERED spill — the spilled-ternary capstone.** A 2-instruction
    body `[ternop (y1 mid-spilled) ; binop]` folds end-to-end under `StackDiscHS 3` (total gain:
    +2 restore-and-keep, +1 output): the asm run of the concatenated generated plans — including
    the synthesised `SWAP3;SWAP2;SWAP1;SWAP3` reorder — simulates the composed Venom body steps,
    re-establishing the invariant at 0 headroom and the grown shape `S ++ [y1, o1] ++ [o2]`.
    Instantiates `genBlockBody_sim_inv_HSV` with `bodyStepsReadyHSV_ternopYspilled_binop` — the
    first whole-body simulation through a non-positioned spill restore. -/
theorem genBlockBodyHSV_ternop_yspilled_binop_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M : AssocList Operand Nat} {x1 y1 z1 o1 x2 y2 o2 name1 name2 : String}
    {off idx1 idx2 : Nat} {f3 : bytes32 → bytes32 → bytes32 → bytes32} {f : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some name1)
    (hncomm1 : isCommutative i1.opcode = false)
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execPure3 f3 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1, Operand.Var z1])
    (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hxz1 : x1 ≠ z1) (hyz1 : y1 ≠ z1)
    (ho1x : o1 ≠ x1) (ho1y : o1 ≠ y1) (ho1z : o1 ≠ z1)
    (hz1S : z1 ∈ S) (hx1S : x1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true)
    (ho1M : alookup' M (Operand.Var o1) = none)
    (hz1M : alookup' M (Operand.Var z1) = none) (hlivez1 : nextLiveness.contains z1 = true)
    (hy1M : alookup' M (Operand.Var y1) = some off) (hlivey1 : nextLiveness.contains y1 = true)
    (hx1M : alookup' M (Operand.Var x1) = none) (hlivex1 : nextLiveness.contains x1 = true)
    (haremove : aremove M (Operand.Var y1) = ([] : AssocList Operand Nat))
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name1 → asmStep offsetToPc prog s = asmTernop f3 s)
    (hoptnoop1 : ∀ p : PlanState, optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var y1, Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var y1, Operand.Var o1] }))
    -- instruction 2: both-live non-commutative binop over the grown shape
    (hname2 : opcodeToEvmName i2.opcode = some name2)
    (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execPure2 f i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2)
    (hx2S : x2 ∈ S ++ [y1, o1]) (hy2S : y2 ∈ S ++ [y1, o1]) (ho2S : o2 ∉ S ++ [y1, o1])
    (hlive2 : nextLiveness.contains o2 = true)
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name2 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop2 : ∀ (p : PlanState), optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o2] }))
    -- entry state: invariant at the total gain, shape S, exactly M spilled
    (hsd0 : StackDiscHS 3 ps0 vs0 as0) (hsv0 : StackPerm S ps0) (hspM : ps0.spilled = M)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([((i1, idx1), [y1, o1]), ((i2, idx2), [o2])].foldl
        (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
          false nextIsTerminator curBbLabel acc.2)).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
            curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan ([((i1, idx1), [y1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).1).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ([((i1, idx1), [y1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackDiscHS 0 ([((i1, idx1), [y1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackPerm ((S ++ [y1, o1]) ++ [o2]) ([((i1, idx1), [y1, o1]), ((i2, idx2), [o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyHSV_ternopYspilled_binop (liveness := liveness) (dfg := dfg)
    (cfg := cfg) (fn := fn) (lo := lo) (offsetToPc := offsetToPc) (prog := prog)
    (curBbLabel := curBbLabel) (idx1 := idx1) (idx2 := idx2)
    hname1 hncomm1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hxy1 hxz1 hyz1 ho1x ho1y ho1z
    hz1S hx1S ho1S hlive1 ho1M hz1M hlivez1 hy1M hlivey1 hx1M hlivex1 haremove hdisp1 hoptnoop1
    hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S ho2S
    hlive2 hlivex2 hlivey2 hdisp2 hoptnoop2
  obtain ⟨as', hrun, hrel', hpc, hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSV
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [y1, o1]), ((i2, idx2), [o2])] S M ps0 vs0 as0 hready hsd0 hsv0 hspM hrel0 hblock
  refine ⟨as', hrun, ?_, ?_, ?_⟩
  · simpa using hrel'
  · simpa using hsd'
  · simpa [List.append_assoc] using hsv'

/-- **A live spill survives an unrelated step before consumption.** Readiness for
    `[binop (all operands live) ; TLOAD (w spilled)]` where the single-entry spilled map
    `[(w, off)]` passes UNCHANGED over step 1 (`w` live, untouched — the `M → M` transition via
    `releaseDeadSpills_spilled_of_live_single`) and is consumed by step 2 (restore, map → `[]`).
    The intra-block core of a spill crossing a block boundary. `totalGain = 3`. -/
theorem bodyStepsReadyHSV_spill_passover
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x1 y1 o1 w o2 name1 : String}
    {off idx1 idx2 : Nat} {f : bytes32 → bytes32 → bytes32}
    -- instruction 1: both-live binop; the spilled w is NOT among its variables
    (hname1 : opcodeToEvmName i1.opcode = some name1)
    (hncomm1 : isCommutative i1.opcode = false)
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execPure2 f i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1)
    (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hwx1 : w ≠ x1) (hwy1 : w ≠ y1) (hwo1 : w ≠ o1)
    (hlive1 : nextLiveness.contains o1 = true)
    (hlivex1 : nextLiveness.contains x1 = true) (hlivey1 : nextLiveness.contains y1 = true)
    (hlivew : nextLiveness.contains w = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name1 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop1 : ∀ (p : PlanState), optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o1] }))
    -- instruction 2: TLOAD consuming the spilled w over the grown shape
    (hname2 : opcodeToEvmName i2.opcode = some "TLOAD")
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execRead1 (fun key s => tload key s) i2 v)
    (hops2 : i2.operands = [Operand.Var w]) (houts2 : i2.outputs = [o2])
    (hlive2 : nextLiveness.contains o2 = true)
    (ho2w : o2 ≠ w) (hwo2 : w ≠ o2) (ho2S : o2 ∉ S ++ [o1])
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop2 : ∀ p : PlanState, optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var w, Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var w, Operand.Var o2] })) :
    BodyStepsReadyHSV lo offsetToPc prog
      (fun w' p => generateRegularInstPlan liveness dfg cfg fn w'.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [o1]), ((i2, idx2), [w, o2])] S
      ([(Operand.Var w, off)] : AssocList Operand Nat) := by
  refine bodyStepsReadyHSV_cons
      (M' := ([(Operand.Var w, off)] : AssocList Operand Nat)) ?_
    (bodyStepsReadyHSV_cons (M' := ([] : AssocList Operand Nat)) ?_ bodyStepsReadyHSV_nil)
  · exact bodyStepHSV_nonCommBinop_bothlive hname1 hncomm1 hnjmp1 hcompute1 hdispatch1 hops1
      houts1 hxy1 hx1S hy1S ho1S
      (alookup'_single_ne hwx1 off) (alookup'_single_ne hwy1 off) (alookup'_single_ne hwo1 off)
      (fun q hq => releaseDeadSpills_spilled_of_live_single hq hlivew)
      hlive1 hlivex1 hlivey1 hdisp1 hoptnoop1
  · exact bodyStepHSV_tload_spilled hname2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hlive2 hlivew
      ho2w ho2S (alookup'_single_self (Operand.Var w) off) (alookup'_single_ne hwo2 off)
      (fun q hq => releaseDeadSpills_spilled_of_nil
        (by rw [hq, aremove_single_self]))
      hdisp2 hoptnoop2

/-- **Whole-body sim where a live spill passes over an unrelated step — the cross-block-spill
    core, intra-block.** A 2-instruction body `[binop (all live) ; TLOAD (w spilled)]` folds
    end-to-end under `StackDiscHS 3` with the single-entry spilled map `[(w, off)]` held INTACT
    across step 1 and consumed by step 2: the exact-map thread of `genBlockBody_sim_inv_HSV`
    carries a non-empty map through a step that does not touch it. Exit at 0 headroom, shape
    `S ++ [o1] ++ [w, o2]`, empty map. -/
theorem genBlockBodyHSV_spill_passover_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x1 y1 o1 w o2 name1 : String}
    {off idx1 idx2 : Nat} {f : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some name1)
    (hncomm1 : isCommutative i1.opcode = false)
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execPure2 f i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1)
    (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hwx1 : w ≠ x1) (hwy1 : w ≠ y1) (hwo1 : w ≠ o1)
    (hlive1 : nextLiveness.contains o1 = true)
    (hlivex1 : nextLiveness.contains x1 = true) (hlivey1 : nextLiveness.contains y1 = true)
    (hlivew : nextLiveness.contains w = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name1 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop1 : ∀ (p : PlanState), optimisticSwapPlan dfg i1 nextLiveness nextIsTerminator
        { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var o1] }))
    -- instruction 2: TLOAD consuming the spilled w over the grown shape
    (hname2 : opcodeToEvmName i2.opcode = some "TLOAD")
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execRead1 (fun key s => tload key s) i2 v)
    (hops2 : i2.operands = [Operand.Var w]) (houts2 : i2.outputs = [o2])
    (hlive2 : nextLiveness.contains o2 = true)
    (ho2w : o2 ≠ w) (hwo2 : w ≠ o2) (ho2S : o2 ∉ S ++ [o1])
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop2 : ∀ p : PlanState, optimisticSwapPlan dfg i2 nextLiveness nextIsTerminator
        { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var w, Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var w, Operand.Var o2] }))
    -- entry state: invariant at the total gain, shape S, exactly the single spill
    (hsd0 : StackDiscHS 3 ps0 vs0 as0) (hsv0 : StackPerm S ps0)
    (hspM : ps0.spilled = ([(Operand.Var w, off)] : AssocList Operand Nat))
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([((i1, idx1), [o1]), ((i2, idx2), [w, o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan ([((i1, idx1), [o1]), ((i2, idx2), [w, o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).1).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ([((i1, idx1), [o1]), ((i2, idx2), [w, o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackDiscHS 0 ([((i1, idx1), [o1]), ((i2, idx2), [w, o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2
             (gvBodyStep (i2, idx2) (gvBodyStep (i1, idx1) vs0)) as' ∧
           StackPerm ((S ++ [o1]) ++ [w, o2]) ([((i1, idx1), [o1]), ((i2, idx2), [w, o2])].foldl
             (fun acc x => (acc.1 ++ ((generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness
               false nextIsTerminator curBbLabel acc.2)).1,
               (generateRegularInstPlan liveness dfg cfg fn x.1.1 nextLiveness false nextIsTerminator
                 curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyHSV_spill_passover (liveness := liveness) (dfg := dfg)
    (cfg := cfg) (fn := fn) (lo := lo) (offsetToPc := offsetToPc) (prog := prog)
    (curBbLabel := curBbLabel) (idx1 := idx1) (idx2 := idx2) (off := off)
    hname1 hncomm1 hnjmp1 hcompute1 hdispatch1 hops1 houts1 hxy1 hx1S hy1S ho1S
    hwx1 hwy1 hwo1 hlive1 hlivex1 hlivey1 hlivew hdisp1 hoptnoop1
    hname2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hlive2 ho2w hwo2 ho2S hdisp2 hoptnoop2
  obtain ⟨as', hrun, hrel', hpc, hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSV
      (fun w' p => generateRegularInstPlan liveness dfg cfg fn w'.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      [((i1, idx1), [o1]), ((i2, idx2), [w, o2])] S
      ([(Operand.Var w, off)] : AssocList Operand Nat) ps0 vs0 as0
      hready hsd0 hsv0 hspM hrel0 hblock
  refine ⟨as', hrun, ?_, ?_, ?_⟩
  · simpa using hrel'
  · simpa using hsd'
  · simpa [List.append_assoc] using hsv'

/-- **`StackDiscHS` preservation across a head-spilled LOG** (net +1: the kept restored copy).
    The spilled first-emitted operand is restored and stays; LOG consumes the emitted run and
    appends an event; the map loses `v`, its slot is freed, memory only grows —
    `StackDiscHS (k+1) → k`. The spilled twin of `stackDiscHS_log_bothlive_preserve`. -/
theorem stackDiscHS_log_headspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {v : String} {rest : List String} {dists : List Nat} {tc : bytes32} {k idx off : Nat}
    {L : List Event}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var) (houts : inst.outputs = [])
    (hnd : (v :: rest).Nodup)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists (ps.stack ++ [Operand.Var v, Operand.Var v]))
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_log_headspilled_eq hopc hhead hcompute houts rfl hnd hspill hlive hns hd]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var v] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var v],
                  spilled := aremove ps.spilled (Operand.Var v),
                  alloc := freeSpillSlot off ps.alloc } := by
    rw [hcompute, emitInputPlan_headSpilled_eq inst.opcode nextLiveness hspill hlive hns hd]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var v) o off' hlook
  · show (ps.stack ++ [Operand.Var v]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var v] at hz
    show ∃ w, lookupVar z vs = some w
    rcases List.mem_append.mp hz with h | h
    · exact hsd.defined z h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      rw [h']
      exact hdef_v

/-- **Spill-aware body step for a head-spilled LOG**: `StackDiscHS (k + n + 2)` covers the
    transient peak (restore + keep-alive + `n+1` DUPs), re-established at `k` over the grown
    stack (net +1, the kept restore). Composes `genRegularInstPlan_log_headspilled_sim` with
    the preservation. -/
theorem stackDiscHS_log_headspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {v : String} {rest : List String} {tc : bytes32}
    {n k idx off : Nat} {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscHS (k + n + 2) ps vs as)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var) (houts : inst.outputs = [])
    (hnd : (v :: rest).Nodup)
    (hmemrest : ∀ w ∈ rest, Operand.Var w ∈ ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hliverest : ∀ w ∈ rest, nextLiveness.contains w = true)
    (hlenes : (v :: rest).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : ((v :: rest).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
  have hlenrest : rest.length = n + 1 := by
    simp only [List.length_cons] at hlenes; omega
  have hbound : (ps.stack ++ [Operand.Var v, Operand.Var v]).length + rest.length ≤ 17 := by
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hmemrest2 : ∀ w ∈ rest, Operand.Var w ∈ ps.stack ++ [Operand.Var v, Operand.Var v] :=
    fun w hw => List.mem_append.mpr (Or.inl (hmemrest w hw))
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds rest
    (ps.stack ++ [Operand.Var v, Operand.Var v]) hbound hndrest hmemrest2 hliverest
  have hsim := genRegularInstPlan_log_headspilled_sim (offsetToPc := offsetToPc) hopc hhead
    hcompute houts rfl hnd hspill hlivev hns hdepths hlenes htc htlen hvals hcov hbelow hsize hn
    hsd.spillWf hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_log_headspilled_preserve (idx := idx) (hsd.mono (by omega)) hmemmono hopc
    hhead hcompute houts hnd hspill hlivev hns hdepths hdef_v hstepEq

/-- **Head-spilled LOG as a padded feed** (gain `[v]`: the kept restore; the map loses `v`;
    transient peak `n + 1 ≤ P` borrowed from the padding and restored). The first spilled
    VARIABLE-ARITY fold feed — LOG joins the varying-growth regime in its spilled config. -/
theorem bodyStepHSVP_log_headspilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S : List String} {M M' : AssocList Operand Nat} {v : String} {rest : List String}
    {tc : bytes32} {n idx off : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (v :: rest).map Operand.Var) (houts : inst.outputs = [])
    (hnd : (v :: rest).Nodup) (hrestS : ∀ w ∈ rest, w ∈ S)
    (hlivev : nextLiveness.contains v = true)
    (hliverest : ∀ w ∈ rest, nextLiveness.contains w = true)
    (hlenes : (v :: rest).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4) (hnP : n + 1 ≤ P)
    (hvM : alookup' M (Operand.Var v) = some off)
    (hnsM : ∀ w ∈ rest, alookup' M (Operand.Var w) = none)
    (hM' : ∀ q : PlanState, q.spilled = aremove M (Operand.Var v) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hlogFn : ∀ (p : PlanState) (vst : VenomState) (s : AsmState), venomAsmRel lo p vst s →
        ∃ offset size topics,
          topics.length = n ∧
          (((v :: rest).map Operand.Var).reverse.map (fun o => operandVal vst lo o)
            = ((offset :: size :: topics).map some)) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase inst vst = ExecResult.OK { vst with logs := vst.logs ++ [({ logger := vst.callCtx.contract, topics := topics, data := (vst.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M [v] M' := by
  intro p vst s j hsd hsv hspM hrel hblock
  have hmemrest : ∀ w ∈ rest, Operand.Var w ∈ p.stack :=
    fun w hw => stackPerm_mem hsv (hrestS w hw)
  have hspill_v : alookup' p.spilled (Operand.Var v) = some off := by
    rw [hspM]; exact hvM
  have hns : ∀ w ∈ rest, alookup' p.spilled (Operand.Var w) = none := by
    intro w hw; rw [hspM]; exact hnsM w hw
  have hdef_v := venomAsmRel_spilled_defined hrel hspill_v
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hstepEq⟩ := hlogFn p vst s hrel
  have hshallow0 := hsd.shallow
  simp only [List.length_cons, List.length_nil] at hshallow0
  have hsd2 : StackDiscHS ((j + P - (n + 1)) + n + 2) p vst s := by
    have heq : (j + P - (n + 1)) + n + 2 = j + (1 + 0) + P := by omega
    rw [heq]
    exact hsd
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_log_headspilled_step_S (idx := idx)
    hsd2 hopc hhead hcompute houts hnd hmemrest hspill_v hlivev hns hliverest hlenes htc hn
    htlen hvals hcov hbelow hsize hdef_v hstepEq hrel hblock
  -- closed-form final state (for the StackPerm / exact-map thread)
  have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
  have hbound : (p.stack ++ [Operand.Var v, Operand.Var v]).length + rest.length ≤ 17 := by
    have hlenrest : rest.length = n + 1 := by
      simp only [List.length_cons] at hlenes; omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hmemrest2 : ∀ w ∈ rest, Operand.Var w ∈ p.stack ++ [Operand.Var v, Operand.Var v] :=
    fun w hw => List.mem_append.mpr (Or.inl (hmemrest w hw))
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds rest
    (p.stack ++ [Operand.Var v, Operand.Var v]) hbound hndrest hmemrest2 hliverest
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var v] } : PlanState)
      = { p with stack := p.stack ++ [Operand.Var v],
                  spilled := aremove p.spilled (Operand.Var v),
                  alloc := freeSpillSlot off p.alloc } := by
    rw [hcompute, emitInputPlan_headSpilled_eq inst.opcode nextLiveness hspill_v hlivev hns hdepths]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { p with stack := p.stack ++ [Operand.Var v],
                   spilled := aremove p.spilled (Operand.Var v),
                   alloc := freeSpillSlot off p.alloc } := by
    rw [genRegularInstPlan_log_headspilled_eq hopc hhead hcompute houts rfl hnd hspill_v hlivev
        hns hdepths, hstateEq]
  have hlen : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2.stack.length = p.stack.length + 1 := by
    rw [hfinal, releaseDeadSpills_stack]
    simp
  refine ⟨⟨as', hrun, hrel', hpc, ?_⟩,
    stackPerm_spilled_of_final hsv hfinal (by simp) ?_ hM'⟩
  · refine hsd'.rebuild (Nat.le_refl _) (fun _ _ h => h) ?_ hsd'.defined
    rw [hlen]
    omega
  · show aremove p.spilled (Operand.Var v) = aremove M (Operand.Var v)
    rw [hspM]

/-- `callWriteback` binds `out` and otherwise preserves every variable. -/
theorem callWriteback_lookupVar {out : String} {rOff rSz : Nat} {success : bytes32}
    {newAccs : Accounts} {ret : List byte} {vs : VenomState} {z : String} :
    lookupVar z (callWriteback out rOff rSz success newAccs ret vs)
      = if z = out then some success else lookupVar z vs := by
  by_cases hz : z = out
  · subst hz
    simp only [callWriteback]
    simp only [updateVar, lookupVar, alookup, ainsert, AssocList.insert, AssocList.lookup,
      beq_self_eq_true, if_true]
  · rw [if_neg hz]
    simp only [callWriteback]
    rw [lookupVar_updateVar_ne _ _ _ _ (fun h => hz h)]
    rfl

/-- **`StackDiscHS` preservation across a full CALL plan** (net +1: the success output; unrelated
    spills untouched — the writeback lands below the spill region; memory only grows).
    `StackDiscHS (k+1) → k` at the `callWriteback` state. -/
theorem stackDiscHS_call_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {ovars : List String} {dists : List Nat} {out : String}
    {rOff rSz : Nat} {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      (callWriteback out rOff rSz success newAccs ret vs) as' := by
  rw [genRegularInstPlan_call_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
  rw [hstateEq]
  refine hsd.rebuild hmemmono (fun _ _ h => h) ?_ ?_
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var out] at hz
    by_cases hzo : z = out
    · exact ⟨success, by rw [callWriteback_lookupVar, if_pos hzo]⟩
    · rcases List.mem_append.mp hz with h | h
      · obtain ⟨w, hw⟩ := hsd.defined z h
        exact ⟨w, by rw [callWriteback_lookupVar, if_neg hzo]; exact hw⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        injection h with h'
        exact absurd h' hzo

/-- **Spill-aware CALL step**: `StackDiscHS (k + 7)` covers the 7-DUP transient peak; the full
    generated CALL plan runs, `venomAsmRel` lands at the `callWriteback` state, and the invariant
    is re-established at `k` over the grown stack (net +1, the success output). The block-level
    bridging atom for a mid-block external call (CALL is dispatched at the `execBlock` driver, not
    `stepInstBase`, so this concludes on the writeback state directly — the future body-split
    composition consumes it alongside `execBlock_step_extcall_ok`). -/
theorem stackDiscHS_call_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 7) ps vs as)
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ps.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' := by
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 7 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 7 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  obtain ⟨as', hrun, hstepV, hrelF, hpcF⟩ :=
    genRegularInstPlan_call_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospill
      hdepths hlive heval hvals hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov
      hspill_out hspillReg hcall hoptnoop hrel hblock
  have hmemmono := runAsm_memory_size_mono hrun
  exact ⟨as', hrun, hstepV, hrelF, hpcF,
    stackDiscHS_call_preserve (hsd.mono (by omega)) hmemmono hopc hcompute houts hnd hnospill
      hdepths hlive hoptnoop⟩

/-- **`StackDiscHS` preservation across a full STATICCALL plan** (net +1; writeback below the
    spill region; memory only grows). `StackDiscHS (k+1) → k` at the `callWriteback` state. -/
theorem stackDiscHS_staticcall_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {ovars : List String} {dists : List Nat} {out : String}
    {rOff rSz : Nat} {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.STATICCALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      (callWriteback out rOff rSz success newAccs ret vs) as' := by
  rw [genRegularInstPlan_staticcall_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
  rw [hstateEq]
  refine hsd.rebuild hmemmono (fun _ _ h => h) ?_ ?_
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var out] at hz
    by_cases hzo : z = out
    · exact ⟨success, by rw [callWriteback_lookupVar, if_pos hzo]⟩
    · rcases List.mem_append.mp hz with h | h
      · obtain ⟨w, hw⟩ := hsd.defined z h
        exact ⟨w, by rw [callWriteback_lookupVar, if_neg hzo]; exact hw⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        injection h with h'
        exact absurd h' hzo

/-- **Spill-aware CALL step**: `StackDiscHS (k + 6)` covers the 7-DUP transient peak; the full
    generated CALL plan runs, `venomAsmRel` lands at the `callWriteback` state, and the invariant
    is re-established at `k` over the grown stack (net +1, the success output). The block-level
    bridging atom for a mid-block external call (CALL is dispatched at the `execBlock` driver, not
    `stepInstBase`, so this concludes on the writeback state directly — the future body-split
    composition consumes it alongside `execBlock_step_extcall_ok`). -/
theorem stackDiscHS_staticcall_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 6) ps vs as)
    (hopc : inst.opcode = Opcode.STATICCALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ps.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 false
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' := by
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 6 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 6 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  obtain ⟨as', hrun, hstepV, hrelF, hpcF⟩ :=
    genRegularInstPlan_staticcall_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospill
      hdepths hlive heval hvals hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov
      hspill_out hspillReg hcall hoptnoop hrel hblock
  have hmemmono := runAsm_memory_size_mono hrun
  exact ⟨as', hrun, hstepV, hrelF, hpcF,
    stackDiscHS_staticcall_preserve (hsd.mono (by omega)) hmemmono hopc hcompute houts hnd hnospill
      hdepths hlive hoptnoop⟩

/-- **`StackDiscHS` preservation across a full DELEGATECALL plan** (net +1; writeback below the
    spill region; memory only grows). `StackDiscHS (k+1) → k` at the `callWriteback` state. -/
theorem stackDiscHS_delegatecall_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {ovars : List String} {dists : List Nat} {out : String}
    {rOff rSz : Nat} {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      (callWriteback out rOff rSz success newAccs ret vs) as' := by
  rw [genRegularInstPlan_delegatecall_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
  rw [hstateEq]
  refine hsd.rebuild hmemmono (fun _ _ h => h) ?_ ?_
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var out] at hz
    by_cases hzo : z = out
    · exact ⟨success, by rw [callWriteback_lookupVar, if_pos hzo]⟩
    · rcases List.mem_append.mp hz with h | h
      · obtain ⟨w, hw⟩ := hsd.defined z h
        exact ⟨w, by rw [callWriteback_lookupVar, if_neg hzo]; exact hw⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        injection h with h'
        exact absurd h' hzo

/-- **Spill-aware CALL step**: `StackDiscHS (k + 6)` covers the 7-DUP transient peak; the full
    generated CALL plan runs, `venomAsmRel` lands at the `callWriteback` state, and the invariant
    is re-established at `k` over the grown stack (net +1, the success output). The block-level
    bridging atom for a mid-block external call (CALL is dispatched at the `execBlock` driver, not
    `stepInstBase`, so this concludes on the writeback state directly — the future body-split
    composition consumes it alongside `execBlock_step_extcall_ok`). -/
theorem stackDiscHS_delegatecall_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 6) ps vs as)
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ps.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.caller vs.txCtx.origin
      vs.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ vs.callCtx.callvalue
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' := by
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 6 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 6 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  obtain ⟨as', hrun, hstepV, hrelF, hpcF⟩ :=
    genRegularInstPlan_delegatecall_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospill
      hdepths hlive heval hvals hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov
      hspill_out hspillReg hcall hoptnoop hrel hblock
  have hmemmono := runAsm_memory_size_mono hrun
  exact ⟨as', hrun, hstepV, hrelF, hpcF,
    stackDiscHS_delegatecall_preserve (hsd.mono (by omega)) hmemmono hopc hcompute houts hnd hnospill
      hdepths hlive hoptnoop⟩

/-- **`StackDiscHS` preservation across a full CREATE plan** (net +1: the created address binds
    to `out`; memory untouched on both sides). `StackDiscHS (k+1) → k` at the creation
    writeback. -/
theorem stackDiscHS_create_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {ovars : List String} {dists : List Nat} {out : String}
    {addrOrZero : bytes32} {newAccs : Accounts} {k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.CREATE)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      (updateVar out addrOrZero { vs with accounts := newAccs }) as' := by
  rw [genRegularInstPlan_create_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
  rw [hstateEq]
  refine hsd.rebuild hmemmono (fun _ _ h => h) ?_ ?_
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var out] at hz
    by_cases hzo : z = out
    · exact ⟨addrOrZero, by rw [hzo]; exact lookupVar_updateVar_self _ _ _⟩
    · rcases List.mem_append.mp hz with h | h
      · obtain ⟨w, hw⟩ := hsd.defined z h
        exact ⟨w, by rw [lookupVar_updateVar_ne _ _ _ _ hzo]; exact hw⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        injection h with h'
        exact absurd h' hzo

/-- **Spill-aware CREATE step**: `StackDiscHS (k + 3)` covers the 3-DUP transient peak; the full
    generated CREATE plan runs, `venomAsmRel` lands at the creation writeback, and the invariant
    is re-established at `k` over the grown stack (net +1, the address output). -/
theorem stackDiscHS_create_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {value off size : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hopc : inst.opcode = Opcode.CREATE)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [value, off, size])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (updateVar out addrOrZero { vs with accounts := newAccs }) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out addrOrZero { vs with accounts := newAccs }) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out addrOrZero { vs with accounts := newAccs }) as' := by
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 3 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 3 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  obtain ⟨as', hrun, hstepV, hrelF, hpcF⟩ :=
    genRegularInstPlan_create_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospill
      hdepths hlive heval hvals hvalrev hargs hszlt hfreshS houtov
      hspill_out hspillReg hcreate hoptnoop hrel hblock
  have hmemmono := runAsm_memory_size_mono hrun
  exact ⟨as', hrun, hstepV, hrelF, hpcF,
    stackDiscHS_create_preserve (hsd.mono (by omega)) hmemmono hopc hcompute houts hnd hnospill
      hdepths hlive hoptnoop⟩

/-- **`StackDiscHS` preservation across a full CREATE2 plan** (net +1: the created address binds
    to `out`; memory untouched on both sides). `StackDiscHS (k+1) → k` at the creation
    writeback. -/
theorem stackDiscHS_create2_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {ovars : List String} {dists : List Nat} {out : String}
    {addrOrZero : bytes32} {newAccs : Accounts} {k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.CREATE2)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      (updateVar out addrOrZero { vs with accounts := newAccs }) as' := by
  rw [genRegularInstPlan_create2_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
  rw [hstateEq]
  refine hsd.rebuild hmemmono (fun _ _ h => h) ?_ ?_
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var out] at hz
    by_cases hzo : z = out
    · exact ⟨addrOrZero, by rw [hzo]; exact lookupVar_updateVar_self _ _ _⟩
    · rcases List.mem_append.mp hz with h | h
      · obtain ⟨w, hw⟩ := hsd.defined z h
        exact ⟨w, by rw [lookupVar_updateVar_ne _ _ _ _ hzo]; exact hw⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        injection h with h'
        exact absurd h' hzo

/-- **Spill-aware CREATE step**: `StackDiscHS (k + 4)` covers the 3-DUP transient peak; the full
    generated CREATE2 plan runs, `venomAsmRel` lands at the creation writeback, and the invariant
    is re-established at `k` over the grown stack (net +1, the address output). -/
theorem stackDiscHS_create2_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {value off size salt : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte} {k : Nat}
    (hsd : StackDiscHS (k + 4) ps vs as)
    (hopc : inst.opcode = Opcode.CREATE2)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [value, off, size, salt])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size, salt])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (updateVar out addrOrZero { vs with accounts := newAccs }) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out addrOrZero { vs with accounts := newAccs }) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out addrOrZero { vs with accounts := newAccs }) as' := by
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 4 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 4 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  obtain ⟨as', hrun, hstepV, hrelF, hpcF⟩ :=
    genRegularInstPlan_create2_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospill
      hdepths hlive heval hvals hvalrev hargs hszlt hfreshS houtov
      hspill_out hspillReg hcreate hoptnoop hrel hblock
  have hmemmono := runAsm_memory_size_mono hrun
  exact ⟨as', hrun, hstepV, hrelF, hpcF,
    stackDiscHS_create2_preserve (hsd.mono (by omega)) hmemmono hopc hcompute houts hnd hnospill
      hdepths hlive hoptnoop⟩

/-- **Body continues after a CALL** — the mid-block split composition, asm side. From a state
    satisfying the spill-aware invariant at the CALL's transient budget, run the full generated
    CALL plan (`stackDiscHS_call_step`) and then a varying-growth suffix body fold
    (`genBlockBody_sim_inv_HSV`) from the writeback state: the composed run re-establishes
    `venomAsmRel`/`StackDiscHS`/`StackPerm` at the suffix fold's exit. The prefix body composes
    in front via the same fold; the Venom side threads through `execBlock_step_extcall_ok`
    (CALL is `execBlock`-dispatched, so the suffix's Venom states fold from `callWriteback`). -/
theorem genBlockBodyHSV_after_call_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    {S : List String} {M1 M2 : AssocList Operand Nat}
    {lgPost : List ((Instruction × Nat) × List String)}
    (hsd : StackDiscHS (totalGain lgPost + 7) ps vs as)
    (hsv : StackPerm S ps) (hspM1 : ps.spilled = M1)
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hmemes : ∀ v ∈ ovars, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off, AssocList.lookup Operand Nat ps.spilled op = some off →
        ps.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hM' : ∀ q : PlanState, q.spilled = M1 → (releaseDeadSpills nextLiveness q).spilled = M2)
    (hreadyPost : BodyStepsReadyHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      lgPost (S ++ [out]) M2)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel ps).1
        ++ (lgPost.foldl (fun acc x =>
              (acc.1 ++ ((fun (w : Instruction × Nat) (p : PlanState) =>
                generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                  nextIsTerminator curBbLabel p) x.1 acc.2).1,
               ((fun (w : Instruction × Nat) (p : PlanState) =>
                generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                  nextIsTerminator curBbLabel p) x.1 acc.2).2))
            ([], (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2)).1))) :
    ∃ as', runAsm ((executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length
           + (executePlan (lgPost.foldl (fun acc x =>
                (acc.1 ++ ((fun (w : Instruction × Nat) (p : PlanState) =>
                  generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                    nextIsTerminator curBbLabel p) x.1 acc.2).1,
                 ((fun (w : Instruction × Nat) (p : PlanState) =>
                  generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                    nextIsTerminator curBbLabel p) x.1 acc.2).2))
              ([], (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
                nextIsTerminator curBbLabel ps).2)).1).length) offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (lgPost.foldl (fun acc x =>
               (acc.1 ++ ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).1,
                ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).2))
             ([], (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
               nextIsTerminator curBbLabel ps).2)).2
             (lgPost.foldl (fun v x => gvBodyStep x.1 v)
               (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)) as' ∧
           StackDiscHS 0 (lgPost.foldl (fun acc x =>
               (acc.1 ++ ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).1,
                ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).2))
             ([], (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
               nextIsTerminator curBbLabel ps).2)).2
             (lgPost.foldl (fun v x => gvBodyStep x.1 v)
               (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)) as' ∧
           StackPerm ((S ++ [out]) ++ lgPost.flatMap (fun e => e.2))
             (lgPost.foldl (fun acc x =>
               (acc.1 ++ ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).1,
                ((fun (w : Instruction × Nat) (p : PlanState) =>
                 generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
                   nextIsTerminator curBbLabel p) x.1 acc.2).2))
             ([], (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
               nextIsTerminator curBbLabel ps).2)).2 := by
  set gp : Instruction × Nat → PlanState → List StackOp × PlanState :=
    fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
      nextIsTerminator curBbLabel p with hgp
  set cplan := generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
    nextIsTerminator curBbLabel ps with hcplan
  rw [executePlan_append] at hblock
  obtain ⟨hbCall, hbPost⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hrun1, hstepV, hrelMid, hpcMid, hsdMid⟩ :=
    stackDiscHS_call_step (k := totalGain lgPost) (offsetToPc := offsetToPc) hsd hopc hcompute
      houts hnd hmemes hnospill hliveall hlive heval hvals hvalrev hargs haszlt hro1 hretbelow
      hfnEom hfreshS houtov hspill_out hspillReg hcall hoptnoop hrel hbCall
  have hbound : ps.stack.length + ovars.length ≤ 17 := by
    have h1 := hsd.shallow
    have h2 : ovars.length = 7 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 7 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars ps.stack hbound hnd hmemes hliveall
  have hfinal : cplan.2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [hcplan,
        genRegularInstPlan_call_eq hopc hcompute houts rfl hnd hnospill hdepths hlive, hoptnoop]
  have hqstack : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).stack
      = ps.stack ++ [out].map Operand.Var := rfl
  have hqspill : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = M1 := by
    show (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2.spilled = M1
    rw [hcompute,
        emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths]
    exact hspM1
  obtain ⟨hsvMid, hspM2⟩ := stackPerm_spilled_of_final hsv hfinal hqstack hqspill hM'
  have hbPost' : asmBlockAt prog asMid.pc
      (executePlan (lgPost.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], cplan.2)).1) := by
    rw [hpcMid]; exact hbPost
  obtain ⟨as', hrun2, hrel', hpc', hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSV gp lgPost (S ++ [out]) M2 cplan.2
      (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) asMid
      hreadyPost hsdMid hsvMid hspM2 hrelMid hbPost'
  refine ⟨as', ?_, hstepV, hrel', hsd', hsv'⟩
  rw [runAsm_add_ok hrun1]
  exact hrun2

/-- **Body continues after ANY external call** — the GENERIC mid-block split composition,
    parameterized over the opcode's step atom (its conclusion, conditioned on the segment's
    block fact) and the plan-reduction facts feeding the exact-map thread
    (`stackPerm_spilled_of_final`). All five external-call opcodes integrate mid-block through
    this one lemma: instantiate `hatom` with
    `stackDiscHS_{call,staticcall,delegatecall,create,create2}_step` (partially applied up to
    the block fact), `hfinal`/`hqstack`/`hqspill` from the respective plan reduction, and the
    suffix fold runs from the writeback state `wb`. Generalizes
    `genBlockBodyHSV_after_call_sim` (the CALL instance). -/
theorem genBlockBodyHSV_after_extcall_sim
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {cops : List StackOp} {cps : PlanState} {nl : List String}
    {inst : Instruction} {ps q : PlanState} {vs wb : VenomState} {as : AsmState}
    {out : String} {S : List String} {M1 M2 : AssocList Operand Nat}
    {lgPost : List ((Instruction × Nat) × List String)}
    (hsv : StackPerm S ps)
    (hatom : asmBlockAt prog as.pc (executePlan cops) →
      ∃ asMid, runAsm (executePlan cops).length offsetToPc prog as = AsmResult.AsmOK asMid ∧
        stepExternalCall subEvmFuel inst vs = some wb ∧
        venomAsmRel lo cps wb asMid ∧
        asMid.pc = as.pc + (executePlan cops).length ∧
        StackDiscHS (totalGain lgPost) cps wb asMid)
    (hfinal : cps = releaseDeadSpills nl q)
    (hqstack : q.stack = ps.stack ++ [out].map Operand.Var)
    (hqspill : q.spilled = M1)
    (hM' : ∀ q₀ : PlanState, q₀.spilled = M1 → (releaseDeadSpills nl q₀).spilled = M2)
    (hreadyPost : BodyStepsReadyHSV lo offsetToPc prog gp lgPost (S ++ [out]) M2)
    (hblock : asmBlockAt prog as.pc (executePlan (cops
      ++ (lgPost.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], cps)).1))) :
    ∃ as', runAsm ((executePlan cops).length
             + (executePlan (lgPost.foldl
                 (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
                 ([], cps)).1).length) offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs = some wb ∧
           venomAsmRel lo (lgPost.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], cps)).2
             (lgPost.foldl (fun v x => gvBodyStep x.1 v) wb) as' ∧
           StackDiscHS 0 (lgPost.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], cps)).2
             (lgPost.foldl (fun v x => gvBodyStep x.1 v) wb) as' ∧
           StackPerm ((S ++ [out]) ++ lgPost.flatMap (fun e => e.2))
             (lgPost.foldl
               (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], cps)).2 := by
  rw [executePlan_append] at hblock
  obtain ⟨hbCall, hbPost⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hrun1, hstepV, hrelMid, hpcMid, hsdMid⟩ := hatom hbCall
  obtain ⟨hsvMid, hspM2⟩ := stackPerm_spilled_of_final hsv hfinal hqstack hqspill hM'
  have hbPost' : asmBlockAt prog asMid.pc
      (executePlan (lgPost.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], cps)).1) := by
    rw [hpcMid]; exact hbPost
  obtain ⟨as', hrun2, hrel', hpc', hsd', hsv'⟩ :=
    genBlockBody_sim_inv_HSV gp lgPost (S ++ [out]) M2 cps wb asMid
      hreadyPost hsdMid hsvMid hspM2 hrelMid hbPost'
  refine ⟨as', ?_, hstepV, hrel', hsd', hsv'⟩
  rw [runAsm_add_ok hrun1]
  exact hrun2

/-- **Runnable last-spilled LOG sim** — the first end-to-end consumer of the general reorder
    atoms: live-prefix DUPs + spilled restore (`emitInputPlan_mixed_sim`), the arbitrary-arity
    `SWAP N; …; SWAP 1` doubles-reorder executed by `reorderPlan_run_bounded` over
    `reorderPlan_lastspilled`, then `LOGn` — `venomAsmRel` preserved across the event append,
    net `+1`. -/
theorem genRegularInstPlan_log_lastspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {rest : List String} {v : String} {dists : List Nat} {tc : bytes32} {base : List Operand}
    {off : Nat} {n : Nat} {offset size : bytes32} {topics : List bytes32}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hrestne : rest ≠ [])
    (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : base.length + rest.length + 2 ≤ 17)
    (hlenes : (rest ++ [v]).length = n + 2)
    (htc : tc.toNat = n)
    (htlen : topics.length = n)
    (hvals : ((rest ++ [v]).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) (hn : n ≤ 4)
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] } as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_log_lastspilled_eq hopc hhead hcompute houts hstack0 hrestne h16 hvrest
      hnd hns hd hspill hlivev, hcompute] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode ((rest ++ [v]).map Operand.Var) nextLiveness ps).2
    with hps1def
  have hpvar := emitInputPlan_lastSpilled_eq inst.opcode nextLiveness hns hd hspill hlivev
  have hps1stack : ps1.stack = base ++ rest.map Operand.Var ++ [Operand.Var v, Operand.Var v] := by
    rw [hps1def, hpvar, hstack0]
  have hps1spilled : ps1.spilled = aremove ps.spilled (Operand.Var v) := by
    rw [hps1def, hpvar]
  have hps1nospill : ∀ o, alookup' ps1.spilled o = none := by
    intro o
    rw [hps1spilled, hspM, aremove_single_self]
    rfl
  have hps1fnEom : ps1.alloc.fnEom = ps.alloc.fnEom := by
    rw [hps1def, hpvar]
    rfl
  rw [show ((emitInputPlan inst.opcode ((rest ++ [v]).map Operand.Var) nextLiveness ps).1
        ++ descSwaps (rest.length + 1) ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)])
      = (emitInputPlan inst.opcode ((rest ++ [v]).map Operand.Var) nextLiveness ps).1
        ++ (descSwaps (rest.length + 1) ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)]) from by
      simp] at hblock ⊢
  rw [executePlan_append, executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwaps, hbEmit⟩ := asmBlockAt_append hbRest
  -- the mixed emission
  have hok : emitMixedOk nextLiveness (rest ++ [v]) ps.spilled ps.stack :=
    emitMixedOk_snoc_spilled hns hd hspill hlivev
  obtain ⟨as1, hrunI, hrelI, hpcI, hmono1⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness (rest ++ [v]) ps hok hspillWf hrel hbI
  -- the general doubles-reorder, executed by the bounded runner
  have hndm : (rest.map Operand.Var).Nodup := hnd.map (fun _ _ h => Operand.Var.inj h)
  have hvm : Operand.Var v ∉ rest.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvrest (hwe' ▸ hw)
  have hreo := reorderPlan_lastspilled base (rest.map Operand.Var) (Operand.Var v) ps1
    (by rw [hps1stack]) (by simpa using hrestne) (by simpa using h16) hvm hndm
  have hreo' : reorderPlan ((rest ++ [v]).map Operand.Var) ps1
      = (descSwaps (rest.length + 1),
         { ps1 with stack := base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]) }) := by
    rw [show ((rest ++ [v]).map Operand.Var) = rest.map Operand.Var ++ [Operand.Var v] from by simp,
        hreo]
    simp
  have hbSwaps' : asmBlockAt prog as1.pc (executePlan (descSwaps (rest.length + 1))) := by
    rw [hpcI]; exact hbSwaps
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    reorderPlan_run_bounded (offsetToPc := offsetToPc)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      hps1nospill hreo' hrelI hbSwaps'
  have hmono2 : as1.memory.size ≤ as2.memory.size := runAsm_memory_size_mono hrun2
  -- the LOGn over the positioned inputs
  have hps2stack : ({ ps1 with
        stack := base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]) } : PlanState).stack
      = (base ++ [Operand.Var v]) ++ (rest ++ [v]).map Operand.Var := by
    simp
  have hstacktop : as2.stack
      = offset :: size :: topics ++ as2.stack.drop ((rest ++ [v]).map Operand.Var).length :=
    venomAsmRel_asmStack_topVals hrel2 hps2stack hvals
  have hbEmit' : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]) := by
    rw [hpc2, hpcI, ← htc]; exact hbEmit
  obtain ⟨as3, hrunE, hrelE, hpcE⟩ :=
    emit_log_sim hrel2 hstacktop htlen (le_trans hcov (le_trans hmono1 hmono2))
      (by show offset.toNat + size.toNat ≤ ps1.alloc.fnEom
          rw [hps1fnEom]; exact hbelow)
      hsize hn hbEmit'
  have hps5 : ({ { ps1 with
        stack := base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v]) } with
        stack := stackPop (n + 2)
          (base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v])) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var v] } := by
    rw [show base ++ Operand.Var v :: (rest.map Operand.Var ++ [Operand.Var v])
          = (base ++ [Operand.Var v]) ++ (rest ++ [v]).map Operand.Var from by simp, ← hlenes]
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((rest ++ [v]).map Operand.Var)
    rw [List.length_map] at h
    rw [h]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [List.length_append, List.length_append, htc]
    exact runAsm_compose hrunI (runAsm_compose hrun2 hrunE)
  · rw [List.length_append, List.length_append, htc, hpcE, hpc2, hpcI]
    omega

/-- **`StackDiscHS` preservation across a last-spilled LOG** (net +1: the kept restore; the map
    loses `v`, its slot is freed, memory only grows) — `StackDiscHS (k+1) → k`. -/
theorem stackDiscHS_log_lastspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {rest : List String} {v : String} {dists : List Nat} {tc : bytes32} {k idx off : Nat}
    {L : List Event}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var) (houts : inst.outputs = [])
    (hrestne : rest ≠ []) (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_log_lastspilled_eq hopc hhead hcompute houts rfl hrestne h16 hvrest hnd
      hns hd hspill hlivev]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var v] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var v],
                  spilled := aremove ps.spilled (Operand.Var v),
                  alloc := freeSpillSlot off ps.alloc } := by
    rw [hcompute, emitInputPlan_lastSpilled_eq inst.opcode nextLiveness hns hd hspill hlivev]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var v) o off' hlook
  · show (ps.stack ++ [Operand.Var v]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var v] at hz
    show ∃ w, lookupVar z vs = some w
    rcases List.mem_append.mp hz with h | h
    · exact hsd.defined z h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      rw [h']
      exact hdef_v

/-- **Spill-aware body step for a last-spilled LOG**: `StackDiscHS (k + n + 2)` covers the
    transient peak (live DUPs + restore + keep-alive), re-established at `k` over the grown
    stack (net +1). Composes the runner-backed `genRegularInstPlan_log_lastspilled_sim`. -/
theorem stackDiscHS_log_lastspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {rest : List String} {v : String} {tc : bytes32}
    {n k idx off : Nat} {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscHS (k + n + 2) ps vs as)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var) (houts : inst.outputs = [])
    (hrestne : rest ≠ [])
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hmemrest : ∀ w ∈ rest, Operand.Var w ∈ ps.stack)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hliverest : ∀ w ∈ rest, nextLiveness.contains w = true)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hlenes : (rest ++ [v]).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : ((rest ++ [v]).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
    have hlenrest : rest.length = n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlenes; omega
    have h16 : rest.length + 1 ≤ 16 := by omega
    have hbound : ps.stack.length + rest.length ≤ 17 := by
      have := hsd.shallow; omega
    obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds rest ps.stack hbound hnd hmemrest hliverest
    have hbound17 : ps.stack.length + rest.length + 2 ≤ 17 := by
      have := hsd.shallow; omega
    have hsim := genRegularInstPlan_log_lastspilled_sim (offsetToPc := offsetToPc) hopc hhead
      hcompute houts rfl hrestne h16 hvrest hnd hns hdepths hspill hlivev hspM hbound17 hlenes
      htc htlen hvals hcov hbelow hsize hn hsd.spillWf hrel hblock
    refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
    exact stackDiscHS_log_lastspilled_preserve (idx := idx) (hsd.mono (by omega)) hmemmono hopc
      hhead hcompute houts hrestne h16 hvrest hnd hns hdepths hspill hlivev hdef_v hstepEq

/-- **Last-spilled LOG as a padded feed** (gain `[v]`; the singleton map loses `v`; transient
    peak `n + 1 ≤ P` borrowed and restored). Together with `bodyStepHSVP_log_headspilled`, both
    spilled positions of a variable-arity op now feed the padded whole-body fold — through the
    GENERAL reorder atoms. -/
theorem bodyStepHSVP_log_lastspilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S : List String} {M' : AssocList Operand Nat} {rest : List String} {v : String}
    {tc : bytes32} {n idx off : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var) (houts : inst.outputs = [])
    (hrestne : rest ≠ []) (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hrestS : ∀ w ∈ rest, w ∈ S)
    (hliverest : ∀ w ∈ rest, nextLiveness.contains w = true)
    (hlivev : nextLiveness.contains v = true)
    (hlenes : (rest ++ [v]).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4) (hnP : n + 1 ≤ P)
    (hM' : ∀ q : PlanState, q.spilled = ([] : AssocList Operand Nat) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hlogFn : ∀ (p : PlanState) (vst : VenomState) (s : AsmState), venomAsmRel lo p vst s →
        ∃ offset size topics,
          topics.length = n ∧
          (((rest ++ [v]).map Operand.Var).reverse.map (fun o => operandVal vst lo o)
            = ((offset :: size :: topics).map some)) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          (∃ w, lookupVar v vst = some w) ∧
          stepInstBase inst vst = ExecResult.OK { vst with logs := vst.logs ++ [({ logger := vst.callCtx.contract, topics := topics, data := (vst.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S ([(Operand.Var v, off)] : AssocList Operand Nat) [v] M' := by
  intro p vst s j hsd hsv hspM hrel hblock
  have hmemrest : ∀ w ∈ rest, Operand.Var w ∈ p.stack :=
    fun w hw => stackPerm_mem hsv (hrestS w hw)
  have hspill_v : alookup' p.spilled (Operand.Var v) = some off := by
    rw [hspM]
    exact alookup'_single_self (Operand.Var v) off
  have hns : ∀ w ∈ rest, alookup' p.spilled (Operand.Var w) = none := by
    intro w hw
    rw [hspM]
    exact alookup'_single_ne (fun h => hvrest (by rw [h]; exact hw)) off
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hdefv, hstepEq⟩ :=
    hlogFn p vst s hrel
  have hshallow0 := hsd.shallow
  simp only [List.length_cons, List.length_nil] at hshallow0
  have hsd2 : StackDiscHS ((j + P - (n + 1)) + n + 2) p vst s := by
    have heq : (j + P - (n + 1)) + n + 2 = j + (1 + 0) + P := by omega
    rw [heq]
    exact hsd
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_log_lastspilled_step_S (idx := idx)
    hsd2 hopc hhead hcompute houts hrestne hvrest hnd hmemrest hns hliverest hspill_v hlivev
    hspM hlenes htc hn htlen hvals hcov hbelow hsize hdefv hstepEq hrel hblock
  -- closed-form final state (StackPerm / exact-map thread)
  have hlenrest : rest.length = n + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlenes; omega
  have h16 : rest.length + 1 ≤ 16 := by omega
  have hbound : p.stack.length + rest.length ≤ 17 := by omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds rest p.stack hbound hnd hmemrest hliverest
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var v] } : PlanState)
      = { p with stack := p.stack ++ [Operand.Var v],
                 spilled := aremove p.spilled (Operand.Var v),
                 alloc := freeSpillSlot off p.alloc } := by
    rw [hcompute, emitInputPlan_lastSpilled_eq inst.opcode nextLiveness hns hdepths hspill_v hlivev]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { p with stack := p.stack ++ [Operand.Var v],
                   spilled := aremove p.spilled (Operand.Var v),
                   alloc := freeSpillSlot off p.alloc } := by
    rw [genRegularInstPlan_log_lastspilled_eq hopc hhead hcompute houts rfl hrestne h16 hvrest
        hnd hns hdepths hspill_v hlivev, hstateEq]
  have hlen : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2.stack.length = p.stack.length + 1 := by
    rw [hfinal, releaseDeadSpills_stack]
    simp
  refine ⟨⟨as', hrun, hrel', hpc, ?_⟩,
    stackPerm_spilled_of_final (N := ([] : AssocList Operand Nat)) hsv hfinal (by simp) ?_ ?_⟩
  · refine hsd'.rebuild (Nat.le_refl _) (fun _ _ h => h) ?_ hsd'.defined
    rw [hlen]
    omega
  · show aremove p.spilled (Operand.Var v) = ([] : AssocList Operand Nat)
    rw [hspM, aremove_single_self]
  · exact hM'

/-- **Runnable mid-spilled LOG sim** — the mid atom's end-to-end consumer, completing the spilled
    variable-arity trilogy: mixed emission, the general `SWAP N; …; SWAP q; SWAP N` reorder
    executed by `reorderPlan_run_bounded` over `reorderPlan_midspilled`, then `LOGn` — net `+1`. -/
theorem genRegularInstPlan_log_midspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {pre post : List String} {v : String} {dists dists' : List Nat} {tc : bytes32}
    {base : List Operand} {off : Nat} {n : Nat} {offset size : bytes32} {topics : List bytes32}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nextLiveness pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nextLiveness post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]))
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : base.length + pre.length + post.length + 2 ≤ 17)
    (hlenes : (pre ++ [v] ++ post).length = n + 2)
    (htc : tc.toNat = n)
    (htlen : topics.length = n)
    (hvals : ((pre ++ [v] ++ post).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) (hn : n ≤ 4)
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] } as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_log_midspilled_eq hopc hhead hcompute houts hstack0 hprene hpostne h16
      hvpre hvpost hndpre hndpost hdisj hnspre hdpre hspill hlivev hnspost hdpost, hcompute] at hblock ⊢
  set swapsOps := (StackOp.SOSwap (pre.length + post.length + 1)
      :: StackOp.SOSwap (pre.length + post.length)
      :: descRun (post.length + 1) (pre.length - 1))
      ++ [StackOp.SOSwap post.length]
      ++ [StackOp.SOSwap (pre.length + post.length + 1)] with hswapsdef
  set ps1 := (emitInputPlan inst.opcode ((pre ++ [v] ++ post).map Operand.Var) nextLiveness ps).2
    with hps1def
  have hpvar := emitInputPlan_midSpilled_eq inst.opcode nextLiveness hnspre hdpre hspill hlivev
    hnspost hdpost
  have hps1stack : ps1.stack
      = base ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v] ++ post.map Operand.Var := by
    rw [hps1def, hpvar, hstack0]
  have hps1spilled : ps1.spilled = aremove ps.spilled (Operand.Var v) := by
    rw [hps1def, hpvar]
  have hps1nospill : ∀ o, alookup' ps1.spilled o = none := by
    intro o
    rw [hps1spilled, hspM, aremove_single_self]
    rfl
  have hps1fnEom : ps1.alloc.fnEom = ps.alloc.fnEom := by
    rw [hps1def, hpvar]
    rfl
  rw [show ((emitInputPlan inst.opcode ((pre ++ [v] ++ post).map Operand.Var) nextLiveness ps).1
        ++ swapsOps ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)])
      = (emitInputPlan inst.opcode ((pre ++ [v] ++ post).map Operand.Var) nextLiveness ps).1
        ++ (swapsOps ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)]) from by
      simp] at hblock ⊢
  rw [executePlan_append, executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwaps, hbEmit⟩ := asmBlockAt_append hbRest
  -- the mixed emission: live prefix + spilled + live suffix
  have hok : emitMixedOk nextLiveness (pre ++ [v] ++ post) ps.spilled ps.stack := by
    rw [show pre ++ [v] ++ post = pre ++ (v :: post) from by simp]
    refine emitMixedOk_append_live hnspre hdpre ⟨hlivev, ?_⟩
    simp only [hspill]
    exact emitMixedOk_of_depthsOk
      (by intro w hw
          exact hnspost w hw)
      (by rw [show ps.stack ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v]
              = (ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v] from by simp]
            at hdpost ⊢
          exact hdpost)
  obtain ⟨as1, hrunI, hrelI, hpcI, hmono1⟩ :=
    emitInputPlan_mixed_sim inst.opcode nextLiveness (pre ++ [v] ++ post) ps hok hspillWf hrel hbI
  -- the general doubles-reorder via the bounded runner
  have hndmpre : (pre.map Operand.Var).Nodup := hndpre.map (fun _ _ h => Operand.Var.inj h)
  have hndmpost : (post.map Operand.Var).Nodup := hndpost.map (fun _ _ h => Operand.Var.inj h)
  have hvmpre : Operand.Var v ∉ pre.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpre (hwe' ▸ hw)
  have hvmpost : Operand.Var v ∉ post.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpost (hwe' ▸ hw)
  have hdisjm : ∀ x ∈ pre.map Operand.Var, x ∉ post.map Operand.Var := by
    intro x hx hx2
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hx2
    rw [← hwe] at hue
    injection hue with hue'
    exact hdisj w hw (hue' ▸ hu)
  have hreo := reorderPlan_midspilled base (pre.map Operand.Var) (post.map Operand.Var)
    (Operand.Var v) ps1
    (by rw [hps1stack]) (by simpa using hprene) (by simpa using hpostne)
    (by simpa using h16) hvmpre hvmpost hndmpre hndmpost hdisjm
  have hreo' : reorderPlan ((pre ++ [v] ++ post).map Operand.Var) ps1
      = (swapsOps,
         { ps1 with stack := base ++ Operand.Var v
             :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var) }) := by
    rw [show ((pre ++ [v] ++ post).map Operand.Var)
          = pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var from by simp,
        hreo, hswapsdef]
    simp
  have hbSwaps' : asmBlockAt prog as1.pc (executePlan swapsOps) := by
    rw [hpcI]; exact hbSwaps
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    reorderPlan_run_bounded (offsetToPc := offsetToPc)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      hps1nospill hreo' hrelI hbSwaps'
  have hmono2 : as1.memory.size ≤ as2.memory.size := runAsm_memory_size_mono hrun2
  -- the LOGn over the positioned inputs
  have hps2stack : ({ ps1 with stack := base ++ Operand.Var v
        :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var) } : PlanState).stack
      = (base ++ [Operand.Var v]) ++ (pre ++ [v] ++ post).map Operand.Var := by
    simp
  have hstacktop : as2.stack
      = offset :: size :: topics ++ as2.stack.drop ((pre ++ [v] ++ post).map Operand.Var).length :=
    venomAsmRel_asmStack_topVals hrel2 hps2stack hvals
  have hbEmit' : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]) := by
    rw [hpc2, hpcI, ← htc]; exact hbEmit
  obtain ⟨as3, hrunE, hrelE, hpcE⟩ :=
    emit_log_sim hrel2 hstacktop htlen (le_trans hcov (le_trans hmono1 hmono2))
      (by show offset.toNat + size.toNat ≤ ps1.alloc.fnEom
          rw [hps1fnEom]; exact hbelow)
      hsize hn hbEmit'
  have hps5 : ({ { ps1 with stack := base ++ Operand.Var v
        :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var) } with
        stack := stackPop (n + 2) (base ++ Operand.Var v
          :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var)) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var v] } := by
    rw [show base ++ Operand.Var v
          :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var)
          = (base ++ [Operand.Var v]) ++ (pre ++ [v] ++ post).map Operand.Var from by simp,
        ← hlenes]
    have h := stackPop_append_top (base ++ [Operand.Var v]) ((pre ++ [v] ++ post).map Operand.Var)
    rw [List.length_map] at h
    rw [h]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [List.length_append, List.length_append, htc]
    exact runAsm_compose hrunI (runAsm_compose hrun2 hrunE)
  · rw [List.length_append, List.length_append, htc, hpcE, hpc2, hpcI]
    omega

/-- **`StackDiscHS` preservation across a mid-spilled LOG** (net +1: the kept restore; the map
    loses `v`, its slot is freed, memory only grows) — `StackDiscHS (k+1) → k`. -/
theorem stackDiscHS_log_midspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {pre post : List String} {v : String} {dists dists' : List Nat} {tc : bytes32} {k idx off : Nat}
    {L : List Event}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [])
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nextLiveness pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nextLiveness post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]))
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_log_midspilled_eq hopc hhead hcompute houts rfl hprene hpostne h16
      hvpre hvpost hndpre hndpost hdisj hnspre hdpre hspill hlivev hnspost hdpost]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var v] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var v],
                  spilled := aremove ps.spilled (Operand.Var v),
                  alloc := freeSpillSlot off ps.alloc } := by
    rw [hcompute, emitInputPlan_midSpilled_eq inst.opcode nextLiveness hnspre hdpre hspill hlivev
        hnspost hdpost]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var v) o off' hlook
  · show (ps.stack ++ [Operand.Var v]).length + k ≤ 15
    have := hsd.shallow
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro z hz
    change Operand.Var z ∈ ps.stack ++ [Operand.Var v] at hz
    show ∃ w, lookupVar z vs = some w
    rcases List.mem_append.mp hz with h | h
    · exact hsd.defined z h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      rw [h']
      exact hdef_v

/-- **Spill-aware body step for a mid-spilled LOG**: `StackDiscHS (k + n + 2)` covers the
    transient peak (prefix DUPs + restore + keep-alive + suffix DUPs), re-established at `k` over
    the grown stack (net +1). Composes the runner-backed `genRegularInstPlan_log_midspilled_sim`. -/
theorem stackDiscHS_log_midspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {pre post : List String} {v : String} {tc : bytes32}
    {n k idx off : Nat} {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscHS (k + n + 2) ps vs as)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [])
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hmempre : ∀ w ∈ pre, Operand.Var w ∈ ps.stack)
    (hmempost : ∀ w ∈ post, Operand.Var w ∈ ps.stack)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hlivepre : ∀ w ∈ pre, nextLiveness.contains w = true)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hlivepost : ∀ w ∈ post, nextLiveness.contains w = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hlenes : (pre ++ [v] ++ post).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : ((pre ++ [v] ++ post).map Operand.Var).reverse.map (fun o => operandVal vs lo o)
      = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
    (hdef_v : ∃ w, lookupVar v vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length ∧
           StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
    have hlensum : pre.length + post.length = n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlenes; omega
    have h16 : pre.length + post.length + 1 ≤ 16 := by omega
    have hshallow := hsd.shallow
    have hboundpre : ps.stack.length + pre.length ≤ 17 := by omega
    obtain ⟨dists, hdpre⟩ := emitDepthsOk_of_bounds pre ps.stack hboundpre hndpre hmempre hlivepre
    have hboundpost : ((ps.stack ++ pre.map Operand.Var)
        ++ [Operand.Var v, Operand.Var v]).length + post.length ≤ 17 := by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    obtain ⟨dists', hdpost⟩ := emitDepthsOk_of_bounds post
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]) hboundpost hndpost
      (fun w hw => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (hmempost w hw)))))
      hlivepost
    have hbound17 : ps.stack.length + pre.length + post.length + 2 ≤ 17 := by omega
    have hsim := genRegularInstPlan_log_midspilled_sim (offsetToPc := offsetToPc) hopc hhead
      hcompute houts rfl hprene hpostne h16 hvpre hvpost hndpre hndpost hdisj hnspre hdpre
      hspill hlivev hnspost hdpost hspM hbound17 hlenes htc htlen hvals hcov hbelow hsize hn
      hsd.spillWf hrel hblock
    refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
    exact stackDiscHS_log_midspilled_preserve (idx := idx) (hsd.mono (by omega)) hmemmono hopc
      hhead hcompute houts hprene hpostne h16 hvpre hvpost hndpre hndpost hdisj hnspre hdpre
      hspill hlivev hnspost hdpost hdef_v hstepEq

/-- **Mid-spilled LOG as a padded feed** (gain `[v]`; the singleton map loses `v`; transient
    peak `n + 1 ≤ P` borrowed and restored). All three spilled positions of a variable-arity op
    (head / last / mid) now feed the padded whole-body fold — through the GENERAL reorder atoms. -/
theorem bodyStepHSVP_log_midspilled
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {P : Nat} {S : List String} {M' : AssocList Operand Nat} {pre post : List String} {v : String}
    {tc : bytes32} {n idx off : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [])
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hpreS : ∀ w ∈ pre, w ∈ S) (hpostS : ∀ w ∈ post, w ∈ S)
    (hlivepre : ∀ w ∈ pre, nextLiveness.contains w = true)
    (hlivepost : ∀ w ∈ post, nextLiveness.contains w = true)
    (hlivev : nextLiveness.contains v = true)
    (hlenes : (pre ++ [v] ++ post).length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (hnP : n + 1 ≤ P)
    (hM' : ∀ q : PlanState, q.spilled = ([] : AssocList Operand Nat) →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hlogFn : ∀ (p : PlanState) (vst : VenomState) (s : AsmState), venomAsmRel lo p vst s →
        ∃ offset size topics,
          topics.length = n ∧
          (((pre ++ [v] ++ post).map Operand.Var).reverse.map (fun o => operandVal vst lo o)
            = ((offset :: size :: topics).map some)) ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          (∃ w, lookupVar v vst = some w) ∧
          stepInstBase inst vst = ExecResult.OK { vst with logs := vst.logs ++ [({ logger := vst.callCtx.contract, topics := topics, data := (vst.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepHSVP P lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S ([(Operand.Var v, off)] : AssocList Operand Nat) [v] M' := by
  intro p vst s j hsd hsv hspM hrel hblock
  have hmempre : ∀ w ∈ pre, Operand.Var w ∈ p.stack :=
    fun w hw => stackPerm_mem hsv (hpreS w hw)
  have hmempost : ∀ w ∈ post, Operand.Var w ∈ p.stack :=
    fun w hw => stackPerm_mem hsv (hpostS w hw)
  have hspill_v : alookup' p.spilled (Operand.Var v) = some off := by
    rw [hspM]
    exact alookup'_single_self (Operand.Var v) off
  have hnspre : ∀ w ∈ pre, alookup' p.spilled (Operand.Var w) = none := by
    intro w hw
    rw [hspM]
    exact alookup'_single_ne (fun h => hvpre (by rw [h]; exact hw)) off
  have hnspost : ∀ w ∈ post, alookup' (aremove p.spilled (Operand.Var v)) (Operand.Var w) = none := by
    intro w hw
    rw [hspM, aremove_single_self]
    rfl
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hdefv, hstepEq⟩ :=
    hlogFn p vst s hrel
  have hshallow0 := hsd.shallow
  simp only [List.length_cons, List.length_nil] at hshallow0
  have hsd2 : StackDiscHS ((j + P - (n + 1)) + n + 2) p vst s := by
    have heq : (j + P - (n + 1)) + n + 2 = j + (1 + 0) + P := by omega
    rw [heq]
    exact hsd
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_log_midspilled_step_S (idx := idx)
    hsd2 hopc hhead hcompute houts hprene hpostne hvpre hvpost hndpre hndpost hdisj
    hmempre hmempost hnspre hlivepre hspill_v hlivev hnspost hlivepost hspM hlenes htc hn
    htlen hvals hcov hbelow hsize hdefv hstepEq hrel hblock
  -- closed-form final state (StackPerm / exact-map thread)
  have hlensum : pre.length + post.length = n + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlenes; omega
  have h16 : pre.length + post.length + 1 ≤ 16 := by omega
  have hboundpre : p.stack.length + pre.length ≤ 17 := by omega
  obtain ⟨dists, hdpre⟩ := emitDepthsOk_of_bounds pre p.stack hboundpre hndpre hmempre hlivepre
  have hboundpost : ((p.stack ++ pre.map Operand.Var)
      ++ [Operand.Var v, Operand.Var v]).length + post.length ≤ 17 := by
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  obtain ⟨dists', hdpost⟩ := emitDepthsOk_of_bounds post
    ((p.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]) hboundpost hndpost
    (fun w hw => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (hmempost w hw)))))
    hlivepost
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var v] } : PlanState)
      = { p with stack := p.stack ++ [Operand.Var v],
                 spilled := aremove p.spilled (Operand.Var v),
                 alloc := freeSpillSlot off p.alloc } := by
    rw [hcompute, emitInputPlan_midSpilled_eq inst.opcode nextLiveness hnspre hdpre hspill_v hlivev
        hnspost hdpost]
  have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2
      = releaseDeadSpills nextLiveness
          { p with stack := p.stack ++ [Operand.Var v],
                   spilled := aremove p.spilled (Operand.Var v),
                   alloc := freeSpillSlot off p.alloc } := by
    rw [genRegularInstPlan_log_midspilled_eq hopc hhead hcompute houts rfl hprene hpostne h16
        hvpre hvpost hndpre hndpost hdisj hnspre hdpre hspill_v hlivev hnspost hdpost, hstateEq]
  have hlen : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel p).2.stack.length = p.stack.length + 1 := by
    rw [hfinal, releaseDeadSpills_stack]
    simp
  refine ⟨⟨as', hrun, hrel', hpc, ?_⟩,
    stackPerm_spilled_of_final (N := ([] : AssocList Operand Nat)) hsv hfinal (by simp) ?_ ?_⟩
  · refine hsd'.rebuild (Nat.le_refl _) (fun _ _ h => h) ?_ hsd'.defined
    rw [hlen]
    omega
  · show aremove p.spilled (Operand.Var v) = ([] : AssocList Operand Nat)
    rw [hspM, aremove_single_self]
  · exact hM'

set_option maxHeartbeats 1600000 in
/-- **Full-relation mid-spilled CALL block core**: mixed emission (live prefix, spilled middle
    restore + keep-alive, live suffix), the general doubles-reorder run by the bounded runner,
    then CALL — concluding the COMPLETE `venomAsmRel` at net +2 and the writeback state. The
    non-positioned sibling of `call_block_emit_rel_full_headspilled`. -/
theorem call_block_emit_rel_full_midspilled {lo : AssocList String Nat} {vs : VenomState}
    {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out v : String} {pre post : List String} {dists dists' : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nl pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nl.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nl post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]))
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : ps.stack.length + pre.length + post.length + 2 ≤ 17)
    (hvals : List.map (operandVal vs lo) ((pre ++ [v] ++ post).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v)
    (houtpre : out ∉ pre) (houtpost : out ∉ post)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).1
        ++ ((StackOp.SOSwap (pre.length + post.length + 1)
              :: StackOp.SOSwap (pre.length + post.length)
              :: descRun (post.length + 1) (pre.length - 1))
            ++ [StackOp.SOSwap post.length]
            ++ [StackOp.SOSwap (pre.length + post.length + 1)])
        ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).1
             ++ ((StackOp.SOSwap (pre.length + post.length + 1)
                   :: StackOp.SOSwap (pre.length + post.length)
                   :: descRun (post.length + 1) (pre.length - 1))
                 ++ [StackOp.SOSwap post.length]
                 ++ [StackOp.SOSwap (pre.length + post.length + 1)])
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var v, Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).1
          ++ ((StackOp.SOSwap (pre.length + post.length + 1)
                :: StackOp.SOSwap (pre.length + post.length)
                :: descRun (post.length + 1) (pre.length - 1))
              ++ [StackOp.SOSwap post.length]
              ++ [StackOp.SOSwap (pre.length + post.length + 1)])
          ++ [StackOp.SOEmit "CALL"])).length := by
  set swapsOps := (StackOp.SOSwap (pre.length + post.length + 1)
      :: StackOp.SOSwap (pre.length + post.length)
      :: descRun (post.length + 1) (pre.length - 1))
      ++ [StackOp.SOSwap post.length]
      ++ [StackOp.SOSwap (pre.length + post.length + 1)] with hswapsdef
  set ps1 := (emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).2
    with hps1def
  have hpvar := emitInputPlan_midSpilled_eq Opcode.CALL nl hnspre hdpre hspill hlivev
    hnspost hdpost
  have hps1stack : ps1.stack
      = ps.stack ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v] ++ post.map Operand.Var := by
    rw [hps1def, hpvar]
  have hps1spilled : ps1.spilled = aremove ps.spilled (Operand.Var v) := by
    rw [hps1def, hpvar]
  have hps1nospill : ∀ o, alookup' ps1.spilled o = none := by
    intro o
    rw [hps1spilled, hspM, aremove_single_self]
    rfl
  have hps1alloc : ps1.alloc = freeSpillSlot off ps.alloc := by
    rw [hps1def, hpvar]
  rw [show ((emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).1
        ++ swapsOps ++ [StackOp.SOEmit "CALL"])
      = (emitInputPlan Opcode.CALL ((pre ++ [v] ++ post).map Operand.Var) nl ps).1
        ++ (swapsOps ++ [StackOp.SOEmit "CALL"]) from by
      simp] at hblock ⊢
  rw [executePlan_append, executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwaps, hbCall⟩ := asmBlockAt_append hbRest
  -- the mixed emission: live prefix + spilled + live suffix
  have hok : emitMixedOk nl (pre ++ [v] ++ post) ps.spilled ps.stack := by
    rw [show pre ++ [v] ++ post = pre ++ (v :: post) from by simp]
    refine emitMixedOk_append_live hnspre hdpre ⟨hlivev, ?_⟩
    simp only [hspill]
    exact emitMixedOk_of_depthsOk
      (by intro w hw
          exact hnspost w hw)
      (by rw [show ps.stack ++ pre.map Operand.Var ++ [Operand.Var v, Operand.Var v]
              = (ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v] from by simp]
            at hdpost ⊢
          exact hdpost)
  obtain ⟨as1, hrunI, hrelI, hpcI, hmono1⟩ :=
    emitInputPlan_mixed_sim Opcode.CALL nl (pre ++ [v] ++ post) ps hok hspillWf hrel hbI
  -- the general doubles-reorder via the bounded runner
  have hndmpre : (pre.map Operand.Var).Nodup := hndpre.map (fun _ _ h => Operand.Var.inj h)
  have hndmpost : (post.map Operand.Var).Nodup := hndpost.map (fun _ _ h => Operand.Var.inj h)
  have hvmpre : Operand.Var v ∉ pre.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpre (hwe' ▸ hw)
  have hvmpost : Operand.Var v ∉ post.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvpost (hwe' ▸ hw)
  have hdisjm : ∀ x ∈ pre.map Operand.Var, x ∉ post.map Operand.Var := by
    intro x hx hx2
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hx2
    rw [← hwe] at hue
    injection hue with hue'
    exact hdisj w hw (hue' ▸ hu)
  have hreo := reorderPlan_midspilled ps.stack (pre.map Operand.Var) (post.map Operand.Var)
    (Operand.Var v) ps1
    (by rw [hps1stack]) (by simpa using hprene) (by simpa using hpostne)
    (by simpa using h16) hvmpre hvmpost hndmpre hndmpost hdisjm
  have hreo' : reorderPlan ((pre ++ [v] ++ post).map Operand.Var) ps1
      = (swapsOps,
         { ps1 with stack := ps.stack ++ Operand.Var v
             :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var) }) := by
    rw [show ((pre ++ [v] ++ post).map Operand.Var)
          = pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var from by simp,
        hreo, hswapsdef]
    simp
  have hbSwaps' : asmBlockAt prog as1.pc (executePlan swapsOps) := by
    rw [hpcI]; exact hbSwaps
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    reorderPlan_run_bounded (offsetToPc := offsetToPc)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      hps1nospill hreo' hrelI hbSwaps'
  have hmono2 : as1.memory.size ≤ as2.memory.size := runAsm_memory_size_mono hrun2
  -- the CALL over the positioned operands
  set ps2 := ({ ps1 with stack := ps.stack ++ Operand.Var v
      :: (pre.map Operand.Var ++ [Operand.Var v] ++ post.map Operand.Var) } : PlanState)
    with hps2def
  have hps2stack : ps2.stack
      = (ps.stack ++ [Operand.Var v]) ++ (pre ++ [v] ++ post).map Operand.Var := by
    rw [hps2def]
    simp
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack ++ [Operand.Var v])
    (ops := (pre ++ [v] ++ post).map Operand.Var) (vals := vals) hrel2 hps2stack hvals
  rw [hvalrev] at htop
  have hlenops : ((pre ++ [v] ++ post).map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : (pre ++ [v] ++ post).length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrel2
  have hmemrel1' : memoryRel ps.alloc vs.memory as2.memory := by
    have halloc2 : ps2.alloc = freeSpillSlot off ps.alloc := by
      rw [hps2def]; exact hps1alloc
    rw [halloc2] at hmemrel1
    exact hmemrel1
  have hro2 : rOff.toNat ≤ as2.memory.size := by omega
  have hcall1 : evmCall subEvmFuel as2.accounts as2.callCtx.contract as2.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as2.memory.readWithPadding aOff.toNat aSz.toNat).toList as2.txCtx.gasprice 0 (!as2.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1' hargs haszlt]
    exact hcall
  have hbCall' : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "CALL"]) := by
    rw [hpc2, hpcI]; exact hbCall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one hbCall'
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    call_step_stateAgree_rel (alloc := ps.alloc) (as := as2) hopc heval hout htop
      hacc1.symm hmemrel1' hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  have hpcadv : s''.pc = as2.pc + 1 := by
    have hcalleq : asmCall as2 = AsmResult.AsmOK s'' := hasmOK
    unfold asmCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as2 = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as2
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as2 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  have hcongrStack : ∀ o ∈ ps2.stack, operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps2stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h2 | h2
      · intro hc; rw [hc] at h2; exact hfreshS h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        intro hc; rw [hc] at h2
        injection h2 with h2'
        exact houtv h2'
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      subst hwe'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (h3 | h3) | h3
      · exact houtpre h3
      · exact houtv h3
      · exact houtpost h3
  have hStkCb : planStackRel lo cb ps2.stack as2.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 7 ≤ ps2.stack.length := by
    rw [hps2stack, List.length_append]
    have := hlenops
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 7 ps2.stack = ps.stack ++ [Operand.Var v] := by
    rw [hps2stack, ← hlenops]
    exact stackPop_append_top (ps.stack ++ [Operand.Var v]) ((pre ++ [v] ++ post).map Operand.Var)
  rw [hpop7] at hStkFinal
  have hSpillFinal : planSpillRel lo cb ps2.spilled s''.memory := by
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off' hlook
      rw [show ps2.spilled = ps1.spilled from rfl, hps1spilled] at hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc] at hlook
      rw [aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var out) hspill_out] at hlook
      simp at hlook
    · intro op off' hlook
      rw [show ps2.spilled = ps1.spilled from rfl, hps1spilled] at hlook
      have hge : ps.alloc.fnEom ≤ off' :=
        hspillReg op off' (aremove_lookup_some ps.spilled (Operand.Var v) op off' hlook)
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off' 32 h32
      intro k hk
      have := hframe' (off' + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [List.length_append, List.length_append]
    exact runAsm_compose hrunI (runAsm_compose hrun2 hrunC)
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var v, Operand.Var out]) s''.stack
      rw [hstk']
      have hassoc : ps.stack ++ [Operand.Var v, Operand.Var out]
          = (ps.stack ++ [Operand.Var v]) ++ [Operand.Var out] := by simp
      rw [hassoc]
      exact hStkFinal
    · show memoryRel ps1.alloc cb.memory s''.memory
      rw [hps1alloc]
      exact hmemrel'
  · rw [List.length_append, List.length_append, hpcadv, hpc2, hpcI]
    have hc1 : (executePlan [StackOp.SOEmit "CALL"]).length = 1 := rfl
    rw [hc1]
    omega

/-- **The mid-spilled CALL producer sim** — the non-positioned spilled external-call config
    end-to-end: the spilled middle operand restores mid-emission, the general doubles-reorder
    (run generically by the bounded runner) positions the seven inputs, CALL writes back — the
    whole generated plan preserves the complete `venomAsmRel` (net +2). -/
theorem genRegularInstPlan_call_midspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {pre post : List String} {v : String} {dists dists' : List Nat}
    {out : String} {base : List Operand} {off : Nat}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (pre ++ [v] ++ post).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hprene : pre ≠ []) (hpostne : post ≠ [])
    (h16 : pre.length + post.length + 1 ≤ 16)
    (hvpre : v ∉ pre) (hvpost : v ∉ post)
    (hndpre : pre.Nodup) (hndpost : post.Nodup)
    (hdisj : ∀ x ∈ pre, x ∉ post)
    (hnspre : ∀ w ∈ pre, alookup' ps.spilled (Operand.Var w) = none)
    (hdpre : emitDepthsOk nextLiveness pre dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hnspost : ∀ w ∈ post, alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = none)
    (hdpost : emitDepthsOk nextLiveness post dists'
      ((ps.stack ++ pre.map Operand.Var) ++ [Operand.Var v, Operand.Var v]))
    (hlive : nextLiveness.contains out = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : ps.stack.length + pre.length + post.length + 2 ≤ 17)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) ((pre ++ [v] ++ post).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v)
    (houtpre : out ∉ pre) (houtpost : out ∉ post)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := base ++ [Operand.Var v, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var v, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_call_midspilled_eq hopc hcompute houts hstack0 hprene hpostne h16
      hvpre hvpost hndpre hndpost hdisj hnspre hdpre hspill hlivev hnspost hdpost hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    call_block_emit_rel_full_midspilled (offsetToPc := offsetToPc) hopc heval houts hprene
      hpostne h16 hvpre hvpost hndpre hndpost hdisj hnspre hdpre hspill hlivev hnspost hdpost
      hspM hbound17 hvals hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtv houtpre
      houtpost hspill_out hspillReg hspillWf hcall hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

set_option maxHeartbeats 1600000 in
/-- **Full-relation last-spilled CALL block core**: live-prefix emission, the spilled
    last-emitted operand restored, the `SWAP N; …; SWAP 1` reorder run by the bounded runner,
    then CALL — concluding the COMPLETE `venomAsmRel` at net +2 and the writeback state. The
    `q = 0` sibling of `call_block_emit_rel_full_midspilled`. -/
theorem call_block_emit_rel_full_lastspilled {lo : AssocList String Nat} {vs : VenomState}
    {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out v : String} {rest : List String} {dists : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState} {off : Nat}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hrestne : rest ≠ [])
    (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nl rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nl.contains v = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : ps.stack.length + rest.length + 2 ≤ 17)
    (hvals : List.map (operandVal vs lo) ((rest ++ [v]).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v) (houtrest : out ∉ rest)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).1
        ++ descSwaps (rest.length + 1)
        ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).1
             ++ descSwaps (rest.length + 1)
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var v, Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).1
          ++ descSwaps (rest.length + 1)
          ++ [StackOp.SOEmit "CALL"])).length := by
  set ps1 := (emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).2
    with hps1def
  have hpvar := emitInputPlan_lastSpilled_eq Opcode.CALL nl hns hd hspill hlivev
  have hps1stack : ps1.stack
      = (ps.stack ++ rest.map Operand.Var) ++ [Operand.Var v, Operand.Var v] := by
    rw [hps1def, hpvar]
  have hps1spilled : ps1.spilled = aremove ps.spilled (Operand.Var v) := by
    rw [hps1def, hpvar]
  have hps1nospill : ∀ o, alookup' ps1.spilled o = none := by
    intro o
    rw [hps1spilled, hspM, aremove_single_self]
    rfl
  have hps1alloc : ps1.alloc = freeSpillSlot off ps.alloc := by
    rw [hps1def, hpvar]
  rw [show ((emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).1
        ++ descSwaps (rest.length + 1) ++ [StackOp.SOEmit "CALL"])
      = (emitInputPlan Opcode.CALL ((rest ++ [v]).map Operand.Var) nl ps).1
        ++ (descSwaps (rest.length + 1) ++ [StackOp.SOEmit "CALL"]) from by
      simp] at hblock ⊢
  rw [executePlan_append, executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  obtain ⟨hbSwaps, hbCall⟩ := asmBlockAt_append hbRest
  -- the mixed emission: live prefix + trailing spilled
  have hok : emitMixedOk nl (rest ++ [v]) ps.spilled ps.stack :=
    emitMixedOk_snoc_spilled hns hd hspill hlivev
  obtain ⟨as1, hrunI, hrelI, hpcI, hmono1⟩ :=
    emitInputPlan_mixed_sim Opcode.CALL nl (rest ++ [v]) ps hok hspillWf hrel hbI
  -- the q = 0 doubles-reorder via the bounded runner
  have hndm : (rest.map Operand.Var).Nodup := hnd.map (fun _ _ h => Operand.Var.inj h)
  have hvm : Operand.Var v ∉ rest.map Operand.Var := by
    intro h
    obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
    injection hwe with hwe'
    exact hvrest (hwe' ▸ hw)
  have hreo := reorderPlan_lastspilled ps.stack (rest.map Operand.Var) (Operand.Var v) ps1
    (by rw [hps1stack]) (by simpa using hrestne) (by simpa using h16) hvm hndm
  have hreo' : reorderPlan ((rest ++ [v]).map Operand.Var) ps1
      = (descSwaps (rest.length + 1),
         { ps1 with stack := ps.stack ++ Operand.Var v
             :: (rest.map Operand.Var ++ [Operand.Var v]) }) := by
    rw [show ((rest ++ [v]).map Operand.Var)
          = rest.map Operand.Var ++ [Operand.Var v] from by simp,
        hreo]
    simp
  have hbSwaps' : asmBlockAt prog as1.pc (executePlan (descSwaps (rest.length + 1))) := by
    rw [hpcI]; exact hbSwaps
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    reorderPlan_run_bounded (offsetToPc := offsetToPc)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      (by rw [hps1stack]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega)
      hps1nospill hreo' hrelI hbSwaps'
  have hmono2 : as1.memory.size ≤ as2.memory.size := runAsm_memory_size_mono hrun2
  -- the CALL over the positioned operands
  set ps2 := ({ ps1 with stack := ps.stack ++ Operand.Var v
      :: (rest.map Operand.Var ++ [Operand.Var v]) } : PlanState)
    with hps2def
  have hps2stack : ps2.stack
      = (ps.stack ++ [Operand.Var v]) ++ (rest ++ [v]).map Operand.Var := by
    rw [hps2def]
    simp
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack ++ [Operand.Var v])
    (ops := (rest ++ [v]).map Operand.Var) (vals := vals) hrel2 hps2stack hvals
  rw [hvalrev] at htop
  have hlenops : ((rest ++ [v]).map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : (rest ++ [v]).length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrel2
  have hmemrel1' : memoryRel ps.alloc vs.memory as2.memory := by
    have halloc2 : ps2.alloc = freeSpillSlot off ps.alloc := by
      rw [hps2def]; exact hps1alloc
    rw [halloc2] at hmemrel1
    exact hmemrel1
  have hro2 : rOff.toNat ≤ as2.memory.size := by omega
  have hcall1 : evmCall subEvmFuel as2.accounts as2.callCtx.contract as2.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as2.memory.readWithPadding aOff.toNat aSz.toNat).toList as2.txCtx.gasprice 0 (!as2.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1' hargs haszlt]
    exact hcall
  have hbCall' : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "CALL"]) := by
    rw [hpc2, hpcI]; exact hbCall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one hbCall'
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    call_step_stateAgree_rel (alloc := ps.alloc) (as := as2) hopc heval hout htop
      hacc1.symm hmemrel1' hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  have hpcadv : s''.pc = as2.pc + 1 := by
    have hcalleq : asmCall as2 = AsmResult.AsmOK s'' := hasmOK
    unfold asmCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as2 = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as2
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as2 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  have hcongrStack : ∀ o ∈ ps2.stack, operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps2stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h2 | h2
      · intro hc; rw [hc] at h2; exact hfreshS h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        intro hc; rw [hc] at h2
        injection h2 with h2'
        exact houtv h2'
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      subst hwe'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h3 | h3
      · exact houtrest h3
      · exact houtv h3
  have hStkCb : planStackRel lo cb ps2.stack as2.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 7 ≤ ps2.stack.length := by
    rw [hps2stack, List.length_append]
    have := hlenops
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 7 ps2.stack = ps.stack ++ [Operand.Var v] := by
    rw [hps2stack, ← hlenops]
    exact stackPop_append_top (ps.stack ++ [Operand.Var v]) ((rest ++ [v]).map Operand.Var)
  rw [hpop7] at hStkFinal
  have hSpillFinal : planSpillRel lo cb ps2.spilled s''.memory := by
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off' hlook
      rw [show ps2.spilled = ps1.spilled from rfl, hps1spilled] at hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc] at hlook
      rw [aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var out) hspill_out] at hlook
      simp at hlook
    · intro op off' hlook
      rw [show ps2.spilled = ps1.spilled from rfl, hps1spilled] at hlook
      have hge : ps.alloc.fnEom ≤ off' :=
        hspillReg op off' (aremove_lookup_some ps.spilled (Operand.Var v) op off' hlook)
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off' 32 h32
      intro k hk
      have := hframe' (off' + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [List.length_append, List.length_append]
    exact runAsm_compose hrunI (runAsm_compose hrun2 hrunC)
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var v, Operand.Var out]) s''.stack
      rw [hstk']
      have hassoc : ps.stack ++ [Operand.Var v, Operand.Var out]
          = (ps.stack ++ [Operand.Var v]) ++ [Operand.Var out] := by simp
      rw [hassoc]
      exact hStkFinal
    · show memoryRel ps1.alloc cb.memory s''.memory
      rw [hps1alloc]
      exact hmemrel'
  · rw [List.length_append, List.length_append, hpcadv, hpc2, hpcI]
    have hc1 : (executePlan [StackOp.SOEmit "CALL"]).length = 1 := rfl
    rw [hc1]
    omega

/-- **The last-spilled CALL producer sim** — the `q = 0` spilled external-call config
    end-to-end: the spilled last-emitted operand restores, the `SWAP N; …; SWAP 1` reorder
    (run generically by the bounded runner) positions the seven inputs, CALL writes back — the
    whole generated plan preserves the complete `venomAsmRel` (net +2). Completes the spilled
    CALL position trilogy (head / last / mid). -/
theorem genRegularInstPlan_call_lastspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {rest : List String} {v : String} {dists : List Nat}
    {out : String} {base : List Operand} {off : Nat}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = (rest ++ [v]).map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hrestne : rest ≠ [])
    (h16 : rest.length + 1 ≤ 16)
    (hvrest : v ∉ rest) (hnd : rest.Nodup)
    (hns : ∀ w ∈ rest, alookup' ps.spilled (Operand.Var w) = none)
    (hd : emitDepthsOk nextLiveness rest dists ps.stack)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (hspM : ps.spilled = ([(Operand.Var v, off)] : AssocList Operand Nat))
    (hbound17 : ps.stack.length + rest.length + 2 ≤ 17)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal vs lo) ((rest ++ [v]).map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtv : out ≠ v) (houtrest : out ∉ rest)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hspillWf : ∀ o off', alookup' ps.spilled o = some off' →
        32 ∣ off' ∧ off' + 32 ≤ as.memory.size ∧ off' < 2 ^ 256)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := base ++ [Operand.Var v, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var v, Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           stepExternalCall subEvmFuel inst vs
             = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_call_lastspilled_eq hopc hcompute houts hstack0 hrestne h16
      hvrest hnd hns hd hspill hlivev hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    call_block_emit_rel_full_lastspilled (offsetToPc := offsetToPc) hopc heval houts hrestne
      h16 hvrest hnd hns hd hspill hlivev hspM hbound17 hvals hvalrev hargs haszlt hro1
      hretbelow hfnEom hfreshS houtv houtrest hspill_out hspillReg hspillWf hcall hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-! ## Terminator split of the plan body fold

`generateBlockPlan`'s `instOps` runs over `nonParamInsts bb = front ++ [term]`. The fold splits into
the front (non-terminator) fold followed by one terminator step at index `front.length` — the asm
runs the body via `genBlockBody_sim` and the terminator separately (`resolved_jump_sim` etc.), and
`execBlock` peels the front (`execBlock_body_prefix`) then steps the terminator
(`execBlock_step_term`). This is the plan-side split feeding that dispatch. -/

theorem instOps_fold_split (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (term : Instruction) (ps2 : PlanState) :
    (front ++ [term]).zipIdx.foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)
      = (((front.zipIdx).foldl
            (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).1
          ++ (gp (term, front.length)
                ((front.zipIdx).foldl
                  (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).2).1,
         (gp (term, front.length)
                ((front.zipIdx).foldl
                  (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).2).2) := by
  rw [List.zipIdx_append]
  simp only [Nat.zero_add, List.foldl_append, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil]

/-! ## Generic-`offsetToPc` plan sequencing

`plan_seq_sim` (PlanSim) is stated for the empty `offsetToPc`; the assembly threads the whole-
function `offsetToPc` (so cross-block `JUMP`/`JUMPI` resolve), and every body lemma here is already
`offsetToPc`-generic. `plan_seq_sim'` is the same sequencing under a generic `offsetToPc` — chains
two consecutive `AsmOK` plan segments (prefix→body, body→terminator) via the generic
`runAsm_compose`. -/

theorem plan_seq_sim' {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} {vs : VenomState} {ps2 : PlanState} {as as1 as2 : AsmState}
    {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h1pc : as1.pc = as.pc + (executePlan ops1).length)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmOK as2)
    (h2rel : venomAsmRel lo ps2 vs as2)
    (h2pc : as2.pc = as1.pc + (executePlan ops2).length) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmOK as2 ∧
    venomAsmRel lo ps2 vs as2 ∧
    as2.pc = as.pc + (executePlan (ops1 ++ ops2)).length := by
  rw [executePlan_append, List.length_append]
  exact ⟨runAsm_compose h1run h2run, h2rel, by rw [h2pc, h1pc]; omega⟩

/-- Sequencing into a halting terminator: the body plan `ops1` runs to `AsmOK as1`, then the
    terminator plan `ops2` halts. The whole `ops1 ++ ops2` halts at the same state. The arm-carrying
    counterpart of `plan_seq_sim'` for the `Halt` branch (`genInstPlan_sim_stop`), via the generic
    `runAsm_add_ok`. -/
theorem asm_seq_halt {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as1 as2 : AsmState}
    {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmHalt as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmHalt as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a reverting terminator (`Abort RevertAbort` ↦ `AsmRevert`). -/
theorem asm_seq_revert {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmRevert as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmRevert as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a faulting terminator (`Abort ExHaltAbort` / INVALID ↦ `AsmFault`). -/
theorem asm_seq_fault {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmFault as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmFault as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a non-halting (`OK`) terminator (e.g. `JUMP`). Unlike `plan_seq_sim'` this
    needs no `pc` constraint — a jumping terminator's `pc` is not sequential — so it is the right
    glue for the *final* segment. -/
theorem asm_seq_ok {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmOK as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmOK as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-! ## Prefix + body composition (`[SOLabel] ++ body`)

The first two segments of a block's plan: the `JUMPDEST` prefix (`soLabel_sim`) sequenced with the
non-terminator body (`genBlockBody_sim`) via `plan_seq_sim'`, splitting the program coverage with
`asmBlockAt_append`. Running `[SOLabel l] ++ body` from `as0` simulates the plan after the body,
with the Venom side at `execBodyThread`'s end state `sEnd`. The remaining segment is the
terminator (handled by `instOps_fold_split` + the terminator's own sim). -/

theorem genBlockPrefixBody_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1))) :
    ∃ as', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ((front.zipIdx 0).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd as' ∧
           as'.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length := by
  rw [executePlan_append] at hblock
  obtain ⟨hpre, hbody⟩ := asmBlockAt_append hblock
  obtain ⟨as1, h1run, h1rel, h1pc⟩ := soLabel_sim lo ps0 vs0 as0 prog l hrel0 hpre
  have hbody' : asmBlockAt prog as1.pc
      (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) := by
    rw [h1pc]; exact hbody
  obtain ⟨as', h2run, h2rel, h2pc⟩ :=
    genBlockBody_sim gp front 0 ps0 vs0 sEnd as1 hstep h1rel hthread hbody'
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Invariant-threading prefix-body sim** — the body half of the per-block `hsim` builder. As
    `genBlockPrefixBody_sim` but driven by `BodyStepsReady` (the per-instruction steps discharged
    from `StackDiscH`+`StackIsVars`, e.g. via `stackDisc_commBinopVar_step_S`/`stackDisc_unopVar_step_S`)
    instead of a uniform `venomAsmRel`-only `hstep`. Runs the block's `SOLabel` prefix then the body
    via `genBlockBody_sim_inv_S`, landing the asm at `sEnd` (the `gvBodyStep` fold is `sEnd` by
    `execBodyThread_eq_gvFold`). The terminator is composed on top by the caller via the
    `genBlockAsm_*_sim` lemmas to produce the full `hsim`. -/
theorem genBlockPrefixBody_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hready : BodyStepsReady lo offsetToPc prog gp (front.zipIdx 0) S0)
    (hsd0 : StackDiscH (front.zipIdx 0).length ps0 vs0)
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1))) :
    ∃ as', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ((front.zipIdx 0).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd as' ∧
           as'.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length := by
  rw [executePlan_append] at hblock
  obtain ⟨hpre, hbody⟩ := asmBlockAt_append hblock
  obtain ⟨as1, h1run, h1rel, h1pc⟩ := soLabel_sim lo ps0 vs0 as0 prog l hrel0 hpre
  have hbody' : asmBlockAt prog as1.pc
      (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) := by
    rw [h1pc]; exact hbody
  obtain ⟨as', h2run, h2rel, h2pc, _, _⟩ :=
    genBlockBody_sim_inv_S gp (front.zipIdx 0) S0 ps0 vs0 as1 hready hsd0 hsv0 h1rel hbody'
  rw [execBodyThread_eq_gvFold front 0 vs0 sEnd hthread] at h2rel
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Body block ending in a JMP** — the OK-terminator (non-halting) counterpart of the
    `genBlockSimulation_body_{halt,revert,fault}` family. Runs the block's `SOLabel` prefix + body
    (via `genBlockPrefixBody_sim_inv`) then the resolved `[push-label target ; JUMP]` (via
    `block_jmp_sim`), landing at the successor block's entry index `idx` (`AsmOK`, pc = `idx`) still
    related to the post-body Venom/plan state. This is exactly `hfsim_jmp_then_*`'s `hentryAsm`
    (the entry-block arm) for an entry block that *does work before jumping* — `block_jmp_sim` already
    accepts a prefix run of any length, so the body fold composes onto it directly. The Venom JMP
    step (`OK (jumpTo target …)`) is supplied by the caller via `hfsim_jmp_then_*`'s `heterm_step`;
    `venomAsmRel` is currentBb-independent so it carries through the jump. -/
theorem genBlockPrefixBody_then_jmp_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} {offsets : AssocList String Nat}
    (l target : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState) (off idx : Nat)
    (hready : BodyStepsReady lo offsetToPc prog gp (front.zipIdx 0) S0)
    (hsd0 : StackDiscH (front.zipIdx 0).length ps0 vs0)
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asm', runAsm (bodyLen + 2) offsetToPc prog as0 = AsmResult.AsmOK asm' ∧
            venomAsmRel lo ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd asm' ∧
            asm'.pc = idx := by
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBody_sim_inv l gp front S0 ps0 vs0 sEnd as0 hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hpush' : prog.get ⟨asMid.pc, hpc1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel target) := by
    have he : (⟨asMid.pc, hpc1'⟩ : Fin prog.length) = ⟨as0.pc + bodyLen, hpc1⟩ := Fin.ext hbpc
    rw [he]; exact hpush
  have hpc2' : asMid.pc + 1 < prog.length := by rw [hbpc]; exact hpc2
  have hjump' : prog.get ⟨asMid.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" := by
    have he : (⟨asMid.pc + 1, hpc2'⟩ : Fin prog.length) = ⟨as0.pc + bodyLen + 1, hpc2⟩ :=
      Fin.ext (congrArg (· + 1) hbpc)
    rw [he]; exact hjump
  exact block_jmp_sim hbrun hbrel hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk

/-! ## Venom side: runBlock reduces to execBlock at the terminator

The Venom counterpart of `genBlockPrefixBody_sim`. For a phi-free block whose instructions are the
non-terminator body `front` followed by the terminator `term`, `runBlock` (no phi prefix, so just
`execBlock` from `instIdx 0` — `runBlock_no_phi`) peels `front` (`execBlock_body_prefix`) and lands
on `execBlock` of the terminator at the threaded end state `sEnd`. The caller then applies
`execBlock_step_term_*` to dispatch the terminator into its `Halt`/`OK`/`Abort` arm. -/

/-- `execBodyThread` leaves `instIdx` at `start + body.length` (each step sets it to the next
    index), so after the body the terminator sits at `getInstruction bb (start + body.length)`. -/
theorem execBodyThread_instIdx (body : List Instruction) :
    ∀ (start : Nat) (s sEnd : VenomState), s.instIdx = start →
    execBodyThread body start s = some sEnd → sEnd.instIdx = start + body.length := by
  induction body with
  | nil =>
    intro start s sEnd hidx hthread
    simp only [execBodyThread] at hthread
    obtain rfl := Option.some.inj hthread
    simpa using hidx
  | cons inst rest ih =>
    intro start s sEnd _ hthread
    simp only [execBodyThread] at hthread
    cases hstep : stepInstBase inst s with
    | OK s' =>
      rw [hstep] at hthread
      have := ih (start + 1) { s' with instIdx := start + 1 } sEnd rfl hthread
      rw [this, List.length_cons]; omega
    | IntRet _ _ => rw [hstep] at hthread; simp at hthread
    | Halt _ => rw [hstep] at hthread; simp at hthread
    | Abort _ _ => rw [hstep] at hthread; simp at hthread
    | Error _ => rw [hstep] at hthread; simp at hthread

/-- One `execBlock` step on an instruction whose Venom step *directly* halts (STOP/RETURN/SINK —
    `stepInstBase = Halt`, not `OK`-then-`halted`). The existing `execBlock_step_term_*` lemmas only
    cover the `OK` branch; this is the `Halt` match arm. -/
theorem execBlock_step_halt (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Halt s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Halt s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step on an instruction whose Venom step *directly* aborts (REVERT ↦
    `RevertAbort`, faulting opcodes ↦ `ExHaltAbort` — `stepInstBase = Abort`). The `Abort` match
    arm. -/
theorem execBlock_step_abort (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction) (a : AbortType)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Abort a s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Abort a s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step whose Venom step internally returns (`stepInstBase = IntRet` — RET). -/
theorem execBlock_step_intret (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction) (vals : List bytes32)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.IntRet vals s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.IntRet vals s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step whose Venom step errors (`stepInstBase = Error`). Requires `inst` is not
    `INVOKE` — `execBlock` intercepts `INVOKE` in its `Error` arm to run the callee rather than error. -/
theorem execBlock_step_error (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s : VenomState) (inst : Instruction) (e : String)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Error e)
    (hninv : inst.opcode ≠ Opcode.INVOKE) (hncall : isExternalCall inst.opcode = false) :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Error e := by
  simp only [execBlock, hget, hstep, if_neg hninv, hncall, Bool.false_eq_true, if_false]

/-- **`execBlock` runs `INVOKE` via `stepInvoke` (wiring correctness).** When the current instruction
    is `INVOKE` and the mutual `stepInvoke` returns `OK s''`, `execBlock` binds the call's result and
    continues past the call (`instIdx + 1`). Confirms the `INVOKE` call is actually wired through the
    `Error` arm (`stepInstBase` defers `INVOKE` to `Error`; `execBlock` intercepts it there). -/
theorem execBlock_step_invoke_ok (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s'' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hinv : inst.opcode = Opcode.INVOKE)
    (hstep : stepInvoke fuel' ctx inst s = ExecResult.OK s'') :
    execBlock (fuel' + 1) ctx bb s
      = execBlock fuel' ctx bb { s'' with instIdx := s.instIdx + 1 } := by
  have he : ∃ m, stepInstBase inst s = ExecResult.Error m := by
    simp only [stepInstBase, hinv]; exact ⟨_, rfl⟩
  obtain ⟨m, he⟩ := he
  simp only [execBlock, hget, he, if_pos hinv, hstep]

/-- **`execBlock` propagates an `INVOKE` callee halt.** A callee that halts (`RETURN`/`STOP`) surfaces
    the halt through `execBlock` unchanged. -/
theorem execBlock_step_invoke_halt (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s'' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hinv : inst.opcode = Opcode.INVOKE)
    (hstep : stepInvoke fuel' ctx inst s = ExecResult.Halt s'') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Halt s'' := by
  have he : ∃ m, stepInstBase inst s = ExecResult.Error m := by
    simp only [stepInstBase, hinv]; exact ⟨_, rfl⟩
  obtain ⟨m, he⟩ := he
  simp only [execBlock, hget, he, if_pos hinv, hstep]

/-- **`execBlock` runs an external call via `stepExternalCall` (wiring correctness).** For an external
    call opcode whose sub-EVM step succeeds (`some s''`), `execBlock` continues past the call at the
    resulting state. Confirms CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 are wired through the
    `Error` arm (`stepInstBase` defers them to `Error`; `execBlock` runs the sub-EVM there). -/
theorem execBlock_step_extcall_ok (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s'' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hcall : isExternalCall inst.opcode = true)
    (hstep : stepExternalCall subEvmFuel inst s = some s'') :
    execBlock (fuel' + 1) ctx bb s = execBlock fuel' ctx bb { s'' with instIdx := s.instIdx + 1 } := by
  obtain ⟨m, he⟩ := stepInstBase_extcall_error (inst := inst) (s := s) hcall
  simp only [execBlock, hget, he, if_neg (isExternalCall_ne_invoke hcall), hcall, if_pos, hstep]

theorem runBlock_to_term (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + restFuel) ctx bb s = execBlock restFuel ctx bb sEnd := by
  rw [runBlock_no_phi (front.length + restFuel) ctx bb s hd tl (hbb.trans hcons) hphi]
  refine execBlock_body_prefix ctx bb restFuel front 0 { s with instIdx := 0 } sEnd rfl ?_ hnonterm
    hthread
  intro j hj
  rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]

/-- `getInstruction` of the terminator: `bb.instructions = front ++ [term]` puts `term` at index
    `front.length`, which is exactly where `execBodyThread` leaves `instIdx`. -/
theorem getInstruction_term (bb : BasicBlock) (front : List Instruction) (term : Instruction)
    (hbb : bb.instructions = front ++ [term]) :
    getInstruction bb front.length = some term := by
  rw [getInstruction_eq, hbb, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Venom-side `Halt` arm: a phi-free block `front ++ [term]` whose terminator halts directly
    (`stepInstBase term sEnd = Halt sEnd'` — STOP/RETURN/SINK) returns `Halt sEnd'`, given enough
    fuel. Combines `runBlock_to_term` (peel the body) with `execBlock_step_halt` (step the
    terminator), locating it via `execBodyThread_instIdx`. -/
theorem runBlock_halt (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Halt sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_halt extraFuel ctx bb sEnd sEnd' term hget hterm_step

/-- **Venom-side threading through a mid-body external call**: a phi-free block whose body is
    `front1 ++ [callInst] ++ front2` peels the prefix (`execBlock_body_prefix`), dispatches the
    external call at the driver (`execBlock_step_extcall_ok` — CALL-family opcodes fall through
    `stepInstBase`'s Error arm), and peels the suffix from the writeback — landing `execBlock` at
    the terminator with `restFuel`. The Venom counterpart of the asm-side generic split
    composition (`genBlockBodyHSV_after_extcall_sim`). -/
theorem runBlock_to_term_extcall (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd) :
    runBlock (front1.length + 1 + front2.length + restFuel) ctx bb s
      = execBlock restFuel ctx bb sEnd := by
  rw [runBlock_no_phi (front1.length + 1 + front2.length + restFuel) ctx bb s hd tl
      (hbb.trans hcons) hphi]
  rw [show front1.length + 1 + front2.length + restFuel
        = front1.length + ((front2.length + restFuel) + 1) from by omega]
  have hpre : execBlock (front1.length + ((front2.length + restFuel) + 1)) ctx bb
      { s with instIdx := 0 }
      = execBlock ((front2.length + restFuel) + 1) ctx bb sMid := by
    refine execBlock_body_prefix ctx bb ((front2.length + restFuel) + 1) front1 0
      { s with instIdx := 0 } sMid rfl ?_ hnt1 hthread1
    intro j hj
    have hb1 : j < ((front1 ++ [callInst]) ++ front2).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hb2 : j < (front1 ++ [callInst]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hb1,
        List.getElem?_append_left hb2, List.getElem?_append_left hj,
        List.getElem?_eq_getElem hj]
  have hmid_idx : sMid.instIdx = front1.length := by
    simpa using execBodyThread_instIdx front1 0 { s with instIdx := 0 } sMid rfl hthread1
  have hgetc : getInstruction bb sMid.instIdx = some callInst := by
    have hb1 : front1.length < ((front1 ++ [callInst]) ++ front2).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hb1b : front1.length < (front1 ++ [callInst]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hmid_idx, getInstruction_eq, hbb, List.getElem?_append_left hb1,
        List.getElem?_append_left hb1b, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hcallstep : execBlock ((front2.length + restFuel) + 1) ctx bb sMid
      = execBlock (front2.length + restFuel) ctx bb { wb with instIdx := sMid.instIdx + 1 } :=
    execBlock_step_extcall_ok (front2.length + restFuel) ctx bb sMid wb callInst
      hgetc hcall hstep
  have hpost : execBlock (front2.length + restFuel) ctx bb
      { wb with instIdx := sMid.instIdx + 1 }
      = execBlock restFuel ctx bb sEnd := by
    rw [hmid_idx]
    refine execBlock_body_prefix ctx bb restFuel front2 (front1.length + 1)
      { wb with instIdx := front1.length + 1 } sEnd rfl ?_ hnt2 hthread2
    intro j hj
    have hb1 : front1.length + 1 + j < ((front1 ++ [callInst]) ++ front2).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hb2 : (front1 ++ [callInst]).length ≤ front1.length + 1 + j := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hix : front1.length + 1 + j - (front1 ++ [callInst]).length = j := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [getInstruction_eq, hbb, List.getElem?_append_left hb1,
        List.getElem?_append_right hb2, hix, List.getElem?_eq_getElem hj]
  rw [hpre, hcallstep, hpost]

/-- **Venom-side `Halt` arm through a mid-body external call**: the extcall-threaded sibling of
    `runBlock_halt` — the block runs prefix / external call / suffix, then its halting terminator
    (STOP/RETURN/SINK) fires from the threaded end state. -/
theorem runBlock_halt_extcall (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd sEnd' : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd') :
    runBlock (front1.length + 1 + front2.length + (extraFuel + 1)) ctx bb s
      = ExecResult.Halt sEnd' := by
  rw [runBlock_to_term_extcall ctx bb (extraFuel + 1) front1 front2 callInst term hd tl
      s sMid wb sEnd hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2]
  have hidx : sEnd.instIdx = front1.length + 1 + front2.length := by
    have h := execBodyThread_instIdx front2 (front1.length + 1)
      { wb with instIdx := front1.length + 1 } sEnd rfl hthread2
    omega
  have hget : getInstruction bb sEnd.instIdx = some term := by
    have hb1 : ((front1 ++ [callInst]) ++ front2).length ≤ front1.length + 1 + front2.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hix : front1.length + 1 + front2.length - ((front1 ++ [callInst]) ++ front2).length
        = 0 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hidx, getInstruction_eq, hbb, List.getElem?_append_right hb1, hix]
    rfl
  exact execBlock_step_halt extraFuel ctx bb sEnd sEnd' term hget hterm_step

/-- **Venom-side `Abort` arm through a mid-body external call** (REVERT ↦ `RevertAbort`, faulting
    opcodes ↦ `ExHaltAbort`): the extcall-threaded sibling of `runBlock_abort`. -/
theorem runBlock_abort_extcall (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd sEnd' : VenomState) (a : AbortType)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort a sEnd') :
    runBlock (front1.length + 1 + front2.length + (extraFuel + 1)) ctx bb s
      = ExecResult.Abort a sEnd' := by
  rw [runBlock_to_term_extcall ctx bb (extraFuel + 1) front1 front2 callInst term hd tl
      s sMid wb sEnd hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2]
  have hidx : sEnd.instIdx = front1.length + 1 + front2.length := by
    have h := execBodyThread_instIdx front2 (front1.length + 1)
      { wb with instIdx := front1.length + 1 } sEnd rfl hthread2
    omega
  have hget : getInstruction bb sEnd.instIdx = some term := by
    have hb1 : ((front1 ++ [callInst]) ++ front2).length ≤ front1.length + 1 + front2.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hix : front1.length + 1 + front2.length - ((front1 ++ [callInst]) ++ front2).length
        = 0 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hidx, getInstruction_eq, hbb, List.getElem?_append_right hb1, hix]
    rfl
  exact execBlock_step_abort extraFuel ctx bb sEnd sEnd' term a hget hterm_step

/-- Venom-side `Abort` arm (REVERT ↦ `RevertAbort`, faulting opcodes ↦ `ExHaltAbort`): same as
    `runBlock_halt` with `execBlock_step_abort`. -/
theorem runBlock_abort (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState) (a : AbortType)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort a sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Abort a sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_abort extraFuel ctx bb sEnd sEnd' term a hget hterm_step

/-- Venom-side `OK` arm: a non-halting terminator (`stepInstBase = OK`, not halted — e.g. JMP, which
    sets `currentBb`) leaves `runBlock = OK sEnd'`, given enough fuel. Combines `runBlock_to_term`
    with `execBlock_step_term_ok`. -/
theorem runBlock_ok (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false) :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.OK sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_term_ok extraFuel ctx bb sEnd sEnd' term hget hterm_step hterm_isterm hnohalt

/-- Venom-side `IntRet` arm: a terminator that internally returns (`stepInstBase = IntRet` — RET)
    leaves `runBlock = IntRet`, given enough fuel. -/
theorem runBlock_intret (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState) (vals : List bytes32)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.IntRet vals sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.IntRet vals sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_intret extraFuel ctx bb sEnd sEnd' term vals hget hterm_step

/-- Venom-side `Error` arm: a terminator that errors leaves `runBlock = Error`, given enough fuel. -/
theorem runBlock_error (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (e : String)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Error e)
    (hninv : term.opcode ≠ Opcode.INVOKE) (hncall : isExternalCall term.opcode = false) :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Error e := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_error extraFuel ctx bb sEnd term e hget hterm_step hninv hncall

/-- **A BODY instruction (not the terminator) erroring aborts the block.** `runBlock_error` handles
    the terminator erroring; this handles the block's FIRST instruction erroring — the shape a
    consuming-operand block hits when an operand is undefined (`MUL %a %b` with `a` undefined). Any
    fuel `≥ 1` suffices: the error surfaces at the first step, before fuel matters. Non-INVOKE,
    non-external-call (those have their own continuation arms). -/
theorem runBlock_body_head_error (ctx : VenomContext) (bb : BasicBlock)
    (inst : Instruction) (rest : List Instruction) (s : VenomState) (e : String) (fuel' : Nat)
    (hbb : bb.instructions = inst :: rest)
    (hphi : inst.opcode ≠ Opcode.PHI)
    (hstep : stepInstBase inst { s with instIdx := 0 } = ExecResult.Error e)
    (hninv : inst.opcode ≠ Opcode.INVOKE)
    (hncall : isExternalCall inst.opcode = false) :
    runBlock (fuel' + 1) ctx bb s = ExecResult.Error e := by
  rw [runBlock_no_phi (fuel' + 1) ctx bb s inst rest hbb hphi]
  show execBlock (fuel' + 1) ctx bb { s with instIdx := 0 } = ExecResult.Error e
  have hget : getInstruction bb ({ s with instIdx := 0 } : VenomState).instIdx = some inst := by
    show getInstruction bb 0 = some inst
    rw [getInstruction, hbb]; simp
  conv_lhs => rw [execBlock]
  rw [hget]
  simp only [hstep, hninv, hncall, if_false, Bool.false_eq_true]

/-- Venom-side insufficient-fuel arm: `fuel ≤ front.length` means `runBlock` runs out before the
    terminator, returning `Error`. Lands the discharge in `genBlockSimulation`'s vacuous `_ => True`
    branch. Completes the `runBlock` fuel characterization (`runBlock_halt`/`abort` for sufficient
    fuel, this for insufficient). -/
theorem runBlock_oof (ctx : VenomContext) (bb : BasicBlock) (fuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hfuel : fuel ≤ front.length) :
    ∃ e, runBlock fuel ctx bb s = ExecResult.Error e := by
  rw [runBlock_no_phi fuel ctx bb s hd tl (hbb.trans hcons) hphi]
  refine execBlock_oof ctx bb front 0 fuel { s with instIdx := 0 } sEnd rfl ?_ hnonterm hthread hfuel
  intro j hj
  rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]

/-! ## Venom-side block-arm packaging (the `∀ f'` outcome for the CFG walk)

`hfsim_jmp_then_terminal` (and the CFG walk's `hbsim`) want the per-block `runBlock` outcome quantified
over *all* fuel `f'`: the real outcome when fuel suffices, and the vacuous `Error` (insufficient fuel)
arm otherwise. These package the `runBlock_*` decomposition + `runBlock_oof` into that `∀ f'` form. -/

/-- **The `∀ f'` outcome of a JMP (non-halting terminator) block** — exactly
    `hfsim_jmp_then_terminal`'s `hentry`. For sufficient fuel the block runs to `sEnd'` (`runBlock_ok`,
    `halted = false`); for insufficient fuel it runs out (`runBlock_oof` ⇒ `Error` ⇒ the vacuous arm).
    Pure Venom semantics — no codegen. -/
theorem runBlock_jmp_arm (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false) :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' => s' = sEnd' ∧ s'.halted = false
      | ExecResult.Halt _ => False
      | ExecResult.Abort _ _ => False
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_ok ctx bb extra front term hd tl s sEnd sEnd' hbb hcons hphi hnonterm hthread
      hterm_step hterm_isterm hnohalt]
    exact ⟨rfl, hnohalt⟩

/-- **The `∀ f'` outcome of a halting terminal block** (`stepInstBase term sEnd = Halt sEnd'` —
    STOP/RETURN/SINK) — `hfsim_jmp_then_terminal`'s `hterm` for the `Halt` case. Factors `hterm` into
    the Venom-side `runBlock_halt` (sufficient fuel ⇒ `Halt sEnd'`; insufficient ⇒ `Error` ⇒ vacuous)
    and the asm correspondence `hasm` (the terminal block's asm running from `asMid` to `AsmHalt`, at
    the residual budget). The `OK`/`Abort` match arms are never reached (a Halt-terminator block's
    `runBlock` is only `Halt` or `Error`), so they need no proof. The remaining input is `hasm` — the
    terminal block's whole-program asm sim. -/
theorem hterm_halt {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_halt ctx bb extra front term hd tl s sEnd sEnd' hbb hcons hphi hnonterm hthread
      hterm_step]
    exact hasm

/-- Insufficient fuel through a body containing a mid-body external call errors out: the run
    dies in the prefix, at the call itself (fuel 0 after the prefix), or in the suffix. -/
theorem runBlock_oof_extcall (ctx : VenomContext) (bb : BasicBlock) (fuel : Nat)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hfuel : fuel ≤ front1.length + 1 + front2.length) :
    ∃ e, runBlock fuel ctx bb s = ExecResult.Error e := by
  rw [runBlock_no_phi fuel ctx bb s hd tl (hbb.trans hcons) hphi]
  have hsplit1 : ∀ (j : Nat) (hj : j < front1.length),
      getInstruction bb (0 + j) = some front1[j] := by
    intro j hj
    have hb1 : j < ((front1 ++ [callInst]) ++ front2).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hb2 : j < (front1 ++ [callInst]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hb1,
        List.getElem?_append_left hb2, List.getElem?_append_left hj,
        List.getElem?_eq_getElem hj]
  by_cases h1 : fuel ≤ front1.length
  · exact execBlock_oof ctx bb front1 0 fuel { s with instIdx := 0 } sMid rfl hsplit1
      hnt1 hthread1 h1
  · obtain ⟨k, rfl⟩ : ∃ k, fuel = front1.length + (k + 1) :=
      ⟨fuel - front1.length - 1, by omega⟩
    have hk : k ≤ front2.length := by omega
    rw [execBlock_body_prefix ctx bb (k + 1) front1 0 { s with instIdx := 0 } sMid rfl hsplit1
        hnt1 hthread1]
    have hmid_idx : sMid.instIdx = front1.length := by
      simpa using execBodyThread_instIdx front1 0 { s with instIdx := 0 } sMid rfl hthread1
    have hgetc : getInstruction bb sMid.instIdx = some callInst := by
      have hb1 : front1.length < ((front1 ++ [callInst]) ++ front2).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hb1b : front1.length < (front1 ++ [callInst]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hmid_idx, getInstruction_eq, hbb, List.getElem?_append_left hb1,
          List.getElem?_append_left hb1b, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [execBlock_step_extcall_ok k ctx bb sMid wb callInst hgetc hcall hstep, hmid_idx]
    refine execBlock_oof ctx bb front2 (front1.length + 1) k
      { wb with instIdx := front1.length + 1 } sEnd rfl ?_ hnt2 hthread2 hk
    intro j hj
    have hb1 : front1.length + 1 + j < ((front1 ++ [callInst]) ++ front2).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hb2 : (front1 ++ [callInst]).length ≤ front1.length + 1 + j := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hix : front1.length + 1 + j - (front1 ++ [callInst]).length = j := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [getInstruction_eq, hbb, List.getElem?_append_left hb1,
        List.getElem?_append_right hb2, hix, List.getElem?_eq_getElem hj]

/-- **The `∀ f'` outcome of a halting terminal block containing a mid-body external call** —
    the extcall sibling of `hterm_halt`, feeding the CFG walk / chain scaffold: for sufficient
    fuel the block threads prefix / call / suffix and its halting terminator fires
    (`runBlock_halt_extcall`); for insufficient fuel it errors (`runBlock_oof_extcall`, the
    vacuous arm). With this, blocks containing any external call enter the whole-function
    correspondence. -/
theorem hterm_halt_extcall {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd sEnd' : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front1.length + 1 + front2.length
  · obtain ⟨e, he⟩ := runBlock_oof_extcall ctx bb f' front1 front2 callInst term hd tl
      s sMid wb sEnd hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front1.length + 1 + front2.length + (e + 1) :=
      ⟨f' - (front1.length + 1 + front2.length) - 1, by omega⟩
    rw [runBlock_halt_extcall ctx bb extra front1 front2 callInst term hd tl
        s sMid wb sEnd sEnd' hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a revert terminal block containing a mid-body external call** —
    the extcall sibling of `hterm_revert`. -/
theorem hterm_revert_extcall {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd sEnd' : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front1.length + 1 + front2.length
  · obtain ⟨e, he⟩ := runBlock_oof_extcall ctx bb f' front1 front2 callInst term hd tl
      s sMid wb sEnd hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front1.length + 1 + front2.length + (e + 1) :=
      ⟨f' - (front1.length + 1 + front2.length) - 1, by omega⟩
    rw [runBlock_abort_extcall ctx bb extra front1 front2 callInst term hd tl
        s sMid wb sEnd sEnd' AbortType.RevertAbort hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a fault terminal block containing a mid-body external call** —
    the extcall sibling of `hterm_fault`. -/
theorem hterm_fault_extcall {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front1 front2 : List Instruction) (callInst term hd : Instruction) (tl : List Instruction)
    (s sMid wb sEnd sEnd' : VenomState)
    (hbb : bb.instructions = (front1 ++ [callInst] ++ front2) ++ [term])
    (hcons : (front1 ++ [callInst] ++ front2) ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnt1 : ∀ inst ∈ front1, isTerminator inst.opcode = false)
    (hnt2 : ∀ inst ∈ front2, isTerminator inst.opcode = false)
    (hthread1 : execBodyThread front1 0 { s with instIdx := 0 } = some sMid)
    (hcall : isExternalCall callInst.opcode = true)
    (hstep : stepExternalCall subEvmFuel callInst sMid = some wb)
    (hthread2 : execBodyThread front2 (front1.length + 1)
        { wb with instIdx := front1.length + 1 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front1.length + 1 + front2.length
  · obtain ⟨e, he⟩ := runBlock_oof_extcall ctx bb f' front1 front2 callInst term hd tl
      s sMid wb sEnd hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front1.length + 1 + front2.length + (e + 1) :=
      ⟨f' - (front1.length + 1 + front2.length) - 1, by omega⟩
    rw [runBlock_abort_extcall ctx bb extra front1 front2 callInst term hd tl
        s sMid wb sEnd sEnd' AbortType.ExHaltAbort hbb hcons hphi hnt1 hnt2 hthread1 hcall hstep hthread2 hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a reverting terminal block** (`stepInstBase term sEnd = Abort RevertAbort
    sEnd'` — REVERT) — `hfsim_jmp_then_terminal`'s `hterm` for the `Revert` case. The Revert-case
    companion of `hterm_halt` (via `runBlock_abort`); only the `Abort RevertAbort` arm is reached. -/
theorem hterm_revert {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb extra front term hd tl s sEnd sEnd' AbortType.RevertAbort hbb hcons
      hphi hnonterm hthread hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a faulting terminal block** (`stepInstBase term sEnd = Abort ExHaltAbort
    sEnd'` — INVALID) — `hfsim_jmp_then_terminal`'s `hterm` for the `Fault` case. The Fault-case
    companion of `hterm_halt`; only the `Abort ExHaltAbort` arm is reached. -/
theorem hterm_fault {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb extra front term hd tl s sEnd sEnd' AbortType.ExHaltAbort hbb hcons
      hphi hnonterm hthread hterm_step]
    exact hasm

/-! ## Asm-side full-block sim (halting terminator)

The asm side of a block's `Halt` arm: prefix + body (`genBlockPrefixBody_sim`) sequenced with a
terminator whose sim halts (`asm_seq_halt`). The terminator is abstracted as `htermsim` — the caller
plugs `genInstPlan_sim_stop` (STOP) or any `[term-ops] → AsmHalt` sim. Running
`[SOLabel l] ++ body ++ termOps` from `as0` halts at `as''`, with observable effects agreeing
(`venomAsmTerminalRel`) at the terminator's Venom result `vsTerm`. The `Revert`/`Fault`/`OK` arms
are the same shape with `asm_seq_revert`/`asm_seq_fault`/`plan_seq_sim'`. -/

theorem genBlockAsm_halt_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmHalt s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmHalt as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_halt h1run h2run, h2rel⟩

/-- Asm side of a block's `Revert` arm (terminator `Abort RevertAbort`). -/
theorem genBlockAsm_revert_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmRevert s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmRevert as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_revert h1run h2run, h2rel⟩

/-- Asm side of a block's `Fault` arm (terminator `Abort ExHaltAbort` / INVALID). -/
theorem genBlockAsm_fault_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmFault s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmFault as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_fault h1run h2run, h2rel⟩

/-- Asm side of a block's `OK` arm (non-halting terminator, e.g. `JUMP`): the terminator's
    `venomAsmRel` (not terminal) carries forward to the next block. -/
theorem genBlockAsm_ok_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp) (psTerm : PlanState)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo psTerm vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmOK as'' ∧
           venomAsmRel lo psTerm vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_ok h1run h2run, h2rel⟩

/-! ## Discharge logic — the halting arm

The core `genBlockSimulation` discharge for a halting block (terminator `stepInstBase = Halt` —
STOP/RETURN/SINK), in the exact `match runBlock`-shape `genBlockSimulation` uses. Cases on fuel:
with enough fuel `runBlock = Halt (haltState sEnd)` (`runBlock_halt`), so the match reduces to the
`Halt` arm, discharged by the asm result `hasm` (which `genBlockAsm_halt_sim` supplies); with too
little fuel `runBlock = Error` (`runBlock_oof`), landing in the vacuous `_ => True` arm. The OK /
Abort arms are unreachable for a halting block (their hypotheses are never selected). This isolates
the fuel case-split + match handling — the asm side is the `hasm` hypothesis. -/

theorem genBlockSim_match_halt {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_halt : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_halt ctx bb e front term hd tl vs sEnd sEnd' hbb hcons hphi hnonterm
        hthread hterm_halt]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-- Discharge logic for the `Revert` arm (terminator `stepInstBase = Abort RevertAbort` — REVERT).
    Same shape as `genBlockSim_match_halt` with `runBlock_abort`. -/
theorem genBlockSim_match_revert {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb e front term hd tl vs sEnd sEnd' AbortType.RevertAbort hbb hcons hphi
        hnonterm hthread hterm_abort]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-- Discharge logic for the `Fault` arm (terminator `stepInstBase = Abort ExHaltAbort` — INVALID and
    the faulting opcodes). Same shape with `runBlock_abort`. -/
theorem genBlockSim_match_fault {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb e front term hd tl vs sEnd sEnd' AbortType.ExHaltAbort hbb hcons hphi
        hnonterm hthread hterm_abort]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-! ## Plan-structure connection

For a non-single-predecessor block (so `generateBlockPlan_decompose`'s `cleanOps` is empty) with an
entry that has no params and a body of regular instructions, the generated plan is exactly
`SOLabel :: (the plain generateRegularInstPlan fold over nonParamInsts)`. Chains
`generateBlockPlan_decompose` (peel the `SOLabel` / `cleanOps`) with `genInstOps_eq_plain` (the
`Option` instOps fold collapses to the plain regular fold). The body fold can then be split at the
terminator by `instOps_fold_split` to match the `genBlockAsm_*_sim` shape. -/

theorem genBlockPlan_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ inst ∈ nonParamInsts bb, ¬ isPreCodegenOpcode inst.opcode ∧
      inst.opcode ≠ Opcode.PHI ∧ inst.opcode ≠ Opcode.OFFSET ∧
      inst.opcode ≠ Opcode.PARAM ∧ inst.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = StackOp.SOLabel bb.label :: ((nonParamInsts bb).zipIdx.foldl
        (fun (acc : List StackOp × PlanState) (instI : Instruction × Nat) =>
          let (inst, i) := instI
          let nextLive :=
            if i + 1 < (nonParamInsts bb).length then
              liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
            else liveVarsAt liveness bb.label bb.instructions.length
          let nextIsTerm :=
            if i + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
          (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).1,
           (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).2))
        ([], ps)).1 := by
  obtain ⟨cleanOps, ps2, instOps, hclean, hf, hblk⟩ :=
    generateBlockPlan_decompose liveness dfg cfg fn bb ps blockOps ps' hentry hplan
  obtain ⟨hco, hps2⟩ : cleanOps = [] ∧ ps2 = ps := by
    rcases hclean with ⟨hc, _⟩ | ⟨_, hco, hps2⟩
    · exact absurd hc hnotsingle
    · exact ⟨hco, hps2⟩
  subst hco; subst ps2
  have hio : instOps = _ := congrArg Prod.fst (genInstOps_eq_plain bb ps instOps ps' hreg hf)
  rw [hblk, hio]; simp

/-- A program contains itself at pc 0 — `asmBlockAt prog 0 prog`. Used to feed `genBlockAsm_*_sim`
    when the block's compiled program *is* `prog` and execution starts at the top (`as.pc = 0`). -/
theorem asmBlockAt_self (prog : List AsmInst) : asmBlockAt prog 0 prog := by
  refine ⟨by omega, ?_⟩
  intro j hj; simp

/-! ## asmResolve identity on a label-free plan

For a block whose plan emits no label/offset pushes (no `SOPushLabel`/`SOPushOfst`/`SOPush (Label)` —
i.e. a non-control-flow block: arithmetic body + STOP/RETURN/REVERT/INVALID terminator),
`executePlan ops` contains no `AsmPushLabel`/`AsmPushOfst`, so `asmResolve` is the identity on it and
the capstone's `prog = (asmResolve (executePlan ops)).1` *is* `executePlan ops`. This reduces the
whole-plan no-label condition to a per-`StackOp` one via `executePlan = ops >>= execStackOp`. -/

theorem asmResolve_executePlan_id (ops : List StackOp)
    (hL : ∀ op ∈ ops, ∀ a ∈ execStackOp op, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (hO : ∀ op ∈ ops, ∀ a ∈ execStackOp op, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    (asmResolve (executePlan ops)).1 = executePlan ops := by
  apply asmResolve_fst_eq_of_no_label
  · intro a ha lbl
    have ha2 : a ∈ ops.flatMap execStackOp := ha
    rw [List.mem_flatMap] at ha2
    obtain ⟨op, hop, ha'⟩ := ha2
    exact hL op hop a ha' lbl
  · intro a ha lbl d
    have ha2 : a ∈ ops.flatMap execStackOp := ha
    rw [List.mem_flatMap] at ha2
    obtain ⟨op, hop, ha'⟩ := ha2
    exact hO op hop a ha' lbl d

/-- Discharge logic for the `OK` arm (non-halting terminator, e.g. JMP): the match reduces (via
    `runBlock_ok`) to the `OK` arm, carrying `venomAsmRel` forward to the next block. The asm side
    `hasm` is supplied by `genBlockAsm_ok_sim` (whose control-flow terminator resolves through
    `offsetToPc`). -/
theorem genBlockSim_match_ok {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
                   venomAsmRel labelOffsets ps' sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_ok ctx bb e front term hd tl vs sEnd sEnd' hbb hcons hphi hnonterm hthread
        hterm_step hterm_isterm hnohalt]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-! ## Full halting-block discharge

The `genBlockSimulation`-shaped conclusion (with the *resolved* program
`prog = (asmResolve (executePlan blockOps)).1`) for a halting block. Bridges the `asmResolve`
identity (`hresolve`, from `asmResolve_executePlan_id` on a label-free plan) to
`genBlockSim_match_halt`: rewriting `prog` to `executePlan blockOps` reduces the goal to the latter,
whose `hasm` is supplied by `genBlockAsm_halt_sim` (run from `as.pc = 0` via `asmBlockAt_self`, with
`blockOps = SOLabel :: front-fold ++ termOps` from `genBlockPlan_regular` + `instOps_fold_split`).
The first end-to-end assembly of the discharge components into the capstone shape. -/

theorem genBlockSimulation_halting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_halt : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel (haltState sEnd) as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_halt front term hd tl sEnd (haltState sEnd) fuel hbb hcons hphi hnonterm
    hthread hterm_halt hasm

/-- Full reverting-block discharge (terminator `Abort RevertAbort` — REVERT). Variant of
    `genBlockSimulation_halting` via `genBlockSim_match_revert`. -/
theorem genBlockSimulation_reverting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_revert front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
    hterm_abort hasm

/-- Full faulting-block discharge (terminator `Abort ExHaltAbort` — INVALID / faulting opcodes).
    Variant of `genBlockSimulation_halting` via `genBlockSim_match_fault`. -/
theorem genBlockSimulation_faulting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmFault as' ∧ venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_fault front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
    hterm_abort hasm

/-! ## General block-simulation discharge (all terminator arms)

The unified `genBlockSimulation`-shaped discharge for an arbitrary phi-free block
`front ++ [term]`, given the asm-side result `hsim` keyed by the terminator's effect
`stepInstBase term sEnd`. Cases on that effect and dispatches to the matching per-arm lemma
(`genBlockSim_match_{ok,halt,revert,fault}`); for an internally-returning (RET) or erroring
terminator, `runBlock` is `IntRet`/`Error` (via `runBlock_intret`/`runBlock_error`, or `runBlock_oof`
on low fuel), landing in the vacuous `_ => True` arm. The whole asm side is the `hsim` hypothesis
(supplied by the body per-inst sims + the terminator's own sim through `genBlockAsm_*_sim`); this
lemma is purely the terminator case-split + `runBlock` reduction. -/

theorem genBlockSim_match {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hsim : match stepInstBase term sEnd with
      | ExecResult.OK sEnd' =>
        sEnd'.halted = false ∧ ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' sEnd' as'
      | ExecResult.Halt sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel sEnd' as'
      | ExecResult.Abort AbortType.RevertAbort sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel sEnd' as'
      | ExecResult.Abort AbortType.ExHaltAbort sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel sEnd' as'
      | _ => True) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  cases hstep_term : stepInstBase term sEnd with
  | OK sEnd' =>
    simp only [hstep_term] at hsim
    obtain ⟨hnohalt, hasm⟩ := hsim
    exact genBlockSim_match_ok front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
      hstep_term histerm hnohalt hasm
  | Halt sEnd' =>
    simp only [hstep_term] at hsim
    exact genBlockSim_match_halt front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
      hstep_term hsim
  | Abort a sEnd' =>
    cases a with
    | RevertAbort =>
      simp only [hstep_term] at hsim
      exact genBlockSim_match_revert front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm
        hthread hstep_term hsim
    | ExHaltAbort =>
      simp only [hstep_term] at hsim
      exact genBlockSim_match_fault front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm
        hthread hstep_term hsim
  | IntRet vals sEnd' =>
    by_cases hf : front.length < fuel
    · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) := ⟨fuel - front.length - 1, by omega⟩
      rw [runBlock_intret ctx bb e front term hd tl vs sEnd sEnd' vals hbb hcons hphi hnonterm
        hthread hstep_term]; trivial
    · obtain ⟨err, herr⟩ :=
        runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
      rw [herr]; trivial
  | Error e =>
    have hninv : term.opcode ≠ Opcode.INVOKE := by
      intro h; rw [h] at histerm; simp [isTerminator] at histerm
    have hncall : isExternalCall term.opcode = false := by
      cases h : isExternalCall term.opcode with
      | false => rfl
      | true => rw [isExternalCall_not_terminator h] at histerm; simp at histerm
    by_cases hf : front.length < fuel
    · obtain ⟨e2, rfl⟩ : ∃ e2, fuel = front.length + (e2 + 1) := ⟨fuel - front.length - 1, by omega⟩
      rw [runBlock_error ctx bb e2 front term hd tl vs sEnd e hbb hcons hphi hnonterm
        hthread hstep_term hninv hncall]; trivial
    · obtain ⟨err, herr⟩ :=
        runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
      rw [herr]; trivial

/-! ## Empty-body terminal blocks: reusable `genBlockSimulation` discharge

For a block `[term]` (no body) whose terminator halts/reverts/faults, there is no body fold (hence no
well-scheduling obligation), and `genBlockSimulation`'s `hsim` collapses to the terminator's own sim.
These wrappers feed `genBlockSim_match` the empty-body structure, leaving only the Venom terminator
step (`hstep`) and the runnable asm sim (`hasm`) — supplied by the per-instruction terminal sims
(`emit_{return,revert,selfdestruct}_sim`, `asmStep_{stop,invalid}_ok`, …) over the resolved program
(`asmResolve` is the identity on a label-push-free terminal block). The first *general*
(non-example) `genBlockSimulation` discharge for the terminal-terminator class. -/

/-- Empty-body **Halt**-terminated block (STOP / RETURN / SELFDESTRUCT). -/
theorem genBlockSimulation_empty_body_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Halt vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-- Empty-body **Revert**-terminated block (REVERT). -/
theorem genBlockSimulation_empty_body_revert
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Abort AbortType.RevertAbort vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-- Empty-body **Fault**-terminated block (INVALID). -/
theorem genBlockSimulation_empty_body_fault
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Abort AbortType.ExHaltAbort vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-! ## Non-empty-body terminal blocks: body fold ∘ terminator

The reusable discharge for a block with a *non-empty* straight-line body `front` followed by a
terminal terminator.  The body's asm runs `bodyLen` steps to `AsmOK as_mid` (supplied by
`genBlockPrefixBody_sim_inv` over a `BodyStepsReady` — the well-scheduled body fold), and the
terminator's asm then runs the remaining `prog.length - bodyLen` steps from `as_mid` to its terminal
result (supplied by the per-instruction terminal sims).  `runAsm_append_ok` glues the two into the
single whole-program `runAsm prog.length` that `genBlockSim_match`'s `hsim` demands.  This is what
lets a block with body instructions — not just a bare terminator — be discharged. -/

/-- Non-empty-body **Halt**-terminated block: body OK to `as_mid`, terminator Halt from `as_mid`. -/
theorem genBlockSimulation_body_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmHalt asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- Non-empty-body **Revert**-terminated block (REVERT terminator). -/
theorem genBlockSimulation_body_revert
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmRevert asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmRevert asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- Non-empty-body **Fault**-terminated block (INVALID terminator). -/
theorem genBlockSimulation_body_fault
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmFault asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmFault asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- **Fully-wired single-binop-body block sim (Halt terminator).** End-to-end composition of the
    non-empty-body fold for a block `[c := <comm var binop> x y ; <Halt terminator>]`: the single
    binop atom is packaged into a `BodyStepsReady` (`bodyStepsReady_single_commBinop`, free
    optimistic-swap since `nextIsTerminator`), folded to its post-body asm state by
    `genBlockPrefixBody_sim_inv`, and glued to the terminator by `genBlockSimulation_body_halt`. The
    only example-specific inputs are the resolved program's layout/dispatch (`hblock`, `hdisp`) and
    the terminator's own asm sim (`htermrun`) — the body fold itself is fully discharged here. The
    first per-block simulation with a non-empty instruction body. -/
theorem genBlockSimulation_single_commBinop_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst term : Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd sEndTerm : VenomState} {asFin : AsmState}
    {x y out name : String} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxS : x ∈ S0) (hyS : y ∈ S0) (houtS : out ∉ S0)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hbb : bb.instructions = [inst] ++ [term])
    (hinstphi : inst.opcode ≠ Opcode.PHI)
    (hinstnonterm : isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ([inst].zipIdx 0).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread [inst] 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ (([inst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (([inst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlen : bodyLen ≤ prog.length)
    (htermrun : ∀ asMid : AsmState, asMid.pc = asm.pc + bodyLen →
        runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt asFin)
    (htermrel : venomAsmTerminalRel sEndTerm asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog asm = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog asm
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hready := bodyStepsReady_single_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (curBbLabel := curBbLabel) (idx := 0) (lo := labelOffsets) (offsetToPc := offsetToPc)
    (prog := prog) hname hcomm hdispatch hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBody_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      [inst] S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  exact genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    [inst] term inst [term] sEnd sEndTerm asMid asFin bodyLen
    hbb rfl hinstphi (by intro i hi; simp at hi; subst hi; exact hinstnonterm) hthread histerm
    hstepterm hbrun (htermrun asMid hbpc) hlen htermrel

end EvmYul.Venom.Hol.Codegen

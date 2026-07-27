/-
The spill-mode indices for regular-instruction body steps — the Ty-indexed collapse

`GenBlockSimComp` proved the `BodyStepHSV` coverage of each regular-instruction
shape as a hand-enumerated spill matrix — near-identical theorems restating ~20
hypotheses whose *shapes* (which operand sits on the live stack `S` vs in the
spill map `M`, the stack gain, the map after consumption) are functions of the
matrix point. This file states each matrix ONCE, in the style of abi-lean's
`Val : Ty → Type`: an index type with mode-computed statement pieces, and a single
quantified theorem covering every point.

Three shapes, three collapses:

* **binop** (2-in-1-out) — `bodyStepHSV_binop (m : Spill2) (comm : Bool)`. Was
  {comm, non-comm} × {bothlive, valspilled, keyspilled, bothspilled} = 8 theorems.
  Pieces: `gain` / `consumed` / `Placement` / `OutFresh` / `CommDispatch` / `CommOk`.
* **SSTORE** (2-in-0-out, non-commutative) — `bodyStepHSV_sstore (m : Spill2)`.
  Was the same four spill modes, minus output and commutativity. Reuses
  `Spill2.Placement`/`consumed`; only the gain drops the output (`gainNoOut`).
* **ternop** (3-in-1-out) — `bodyStepHSV_ternop (m : Spill3)`. Was
  {bothlive, xspilled, yspilled, zspilled} = 4 theorems (one operand restored per
  step). Pieces: `Spill3.gain` / `consumed` / `Placement`.

The hand-written originals are definitional instances. Each family's one member
with in-`GenBlockSimComp` consumers (`bodyStepHSV_nonCommBinop_bothlive` for binop,
`bodyStepHSV_ternopVar_yspilled` for ternop) survives there — since this module
imports `GenBlockSimComp`, the consumer cannot reach the indexed theorem — and the
corresponding indexed case DELEGATES to it; the rest are inlined. So each collapse
is exactly as strong as the enumeration it replaces, and states the coverage the
enumeration only implied: *every* spill mode feeds the varying-growth fold.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-- Which of a two-operand instruction's inputs currently live in the spill map
rather than on the live stack shape (`x` = first operand / key, `y` = second /
value, matching the family's naming). -/
inductive Spill2 where
  | bothlive
  | valspilled
  | keyspilled
  | bothspilled
  deriving Repr, DecidableEq

namespace Spill2

/-- Stack gain of the step: restored spilled operands stay on the stack, the
output joins on top. -/
def gain (m : Spill2) (x y out : String) : List String :=
  match m with
  | .bothlive    => [out]
  | .valspilled  => [y, out]
  | .keyspilled  => [x, out]
  | .bothspilled => [y, x, out]

/-- The spill map after the step consumes its operands: every restored entry
leaves the map. -/
def consumed (m : Spill2) (M : AssocList Operand Nat) (x y : String) :
    AssocList Operand Nat :=
  match m with
  | .bothlive    => M
  | .valspilled  => aremove M (Operand.Var y)
  | .keyspilled  => aremove M (Operand.Var x)
  | .bothspilled => aremove (aremove M (Operand.Var y)) (Operand.Var x)

/-- Mode-dependent operand placement: live operands are on the shape `S` and
absent from the map; spilled operands have a map entry. -/
def Placement (m : Spill2) (S : List String) (M : AssocList Operand Nat)
    (x y : String) : Prop :=
  match m with
  | .bothlive    => x ∈ S ∧ y ∈ S ∧
      alookup' M (Operand.Var x) = none ∧ alookup' M (Operand.Var y) = none
  | .valspilled  => x ∈ S ∧ alookup' M (Operand.Var x) = none ∧
      (∃ off, alookup' M (Operand.Var y) = some off)
  | .keyspilled  => y ∈ S ∧ alookup' M (Operand.Var y) = none ∧
      (∃ off, alookup' M (Operand.Var x) = some off)
  | .bothspilled => (∃ off, alookup' M (Operand.Var y) = some off) ∧
      (∃ off, alookup' M (Operand.Var x) = some off)

/-- The spilled modes additionally need the output name distinct from both
operand names (the restore sequence must not capture it). -/
def OutFresh (m : Spill2) (x y out : String) : Prop :=
  match m with
  | .bothlive => True
  | _         => out ≠ x ∧ out ≠ y

/-- Stack gain for a **0-output** two-operand step (SSTORE): only the restored
spilled operands stay; there is no output to join. -/
def gainNoOut (m : Spill2) (x y : String) : List String :=
  match m with
  | .bothlive    => []
  | .valspilled  => [y]
  | .keyspilled  => [x]
  | .bothspilled => [y, x]

end Spill2

/-- Which single operand of a three-operand instruction is currently in the
spill map (or none). Ternops restore at most one operand per step. -/
inductive Spill3 where
  | none
  | xsp
  | ysp
  | zsp
  deriving Repr, DecidableEq

namespace Spill3

/-- Stack gain: the restored operand (if any) stays, the output joins on top. -/
def gain (m : Spill3) (x y z out : String) : List String :=
  match m with
  | .none => [out]
  | .xsp  => [x, out]
  | .ysp  => [y, out]
  | .zsp  => [z, out]

/-- The spill map after the step: the restored operand leaves it. -/
def consumed (m : Spill3) (M : AssocList Operand Nat) (x y z : String) :
    AssocList Operand Nat :=
  match m with
  | .none => M
  | .xsp  => aremove M (Operand.Var x)
  | .ysp  => aremove M (Operand.Var y)
  | .zsp  => aremove M (Operand.Var z)

/-- Mode-dependent operand placement: the two live operands are on the shape `S`
and absent from the map; the spilled one has a map entry. -/
def Placement (m : Spill3) (S : List String) (M : AssocList Operand Nat)
    (x y z : String) : Prop :=
  match m with
  | .none => x ∈ S ∧ y ∈ S ∧ z ∈ S ∧
      alookup' M (Operand.Var x) = Option.none ∧ alookup' M (Operand.Var y) = Option.none ∧
      alookup' M (Operand.Var z) = Option.none
  | .xsp  => y ∈ S ∧ z ∈ S ∧
      alookup' M (Operand.Var y) = Option.none ∧ alookup' M (Operand.Var z) = Option.none ∧
      (∃ off, alookup' M (Operand.Var x) = some off)
  | .ysp  => x ∈ S ∧ z ∈ S ∧
      alookup' M (Operand.Var x) = Option.none ∧ alookup' M (Operand.Var z) = Option.none ∧
      (∃ off, alookup' M (Operand.Var y) = some off)
  | .zsp  => x ∈ S ∧ y ∈ S ∧
      alookup' M (Operand.Var x) = Option.none ∧ alookup' M (Operand.Var y) = Option.none ∧
      (∃ off, alookup' M (Operand.Var z) = some off)

end Spill3

/-- The commutativity side of the dispatch: a commutative opcode needs only its
flag; a non-commutative one needs the flag off, the JMP exclusion, and the
positioned operand order. -/
def CommDispatch : Bool → Instruction → Prop
  | true,  inst => isCommutative inst.opcode = true
  | false, inst => isCommutative inst.opcode = false ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse

/-- Where the plan picks the swapped operand order (a commutative opcode with a
spilled key), the semantic function must actually commute. -/
def CommOk : Bool → Spill2 → (bytes32 → bytes32 → bytes32) → Prop
  | true, .keyspilled,  f => ∀ (a b : bytes32), f a b = f b a
  | true, .bothspilled, f => ∀ (a b : bytes32), f a b = f b a
  | _,    _,            _ => True

/-- **The binop spill matrix, as one indexed theorem.** For every spill mode
`m` and either commutativity, a two-variable-operand pure binop is a
`BodyStepHSV` with gain `m.gain x y out` and spill map `m.consumed M x y`.

Instantiating `m`/`comm` recovers each of the eight hand-enumerated theorems
this replaces (`bodyStepHSV_{comm,nonComm}Binop_{bothlive,valspilled,
keyspilled,bothspilled}`); the statement pieces reduce definitionally at any
concrete mode. -/
theorem bodyStepHSV_binop (m : Spill2) (comm : Bool)
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x y out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcm : CommDispatch comm inst)
    (hfc : CommOk comm m f)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hplace : m.Placement S M x y)
    (hout : m.OutFresh x y out)
    (houtS : out ∉ S)
    (houtM : alookup' M (Operand.Var out) = none)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hM' : ∀ q : PlanState, q.spilled = m.consumed M x y →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ (m.gain x y out).map Operand.Var }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ (m.gain x y out).map Operand.Var })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M (m.gain x y out) M' := by
  cases m with
  | bothlive =>
    obtain ⟨hxS, hyS, hxM, hyM⟩ := hplace
    cases comm with
    | false =>
      obtain ⟨hncomm, hnjmp, hcompute⟩ := hcm
      exact bodyStepHSV_nonCommBinop_bothlive hname hncomm hnjmp hcompute hdispatch hops houts
        hxy hxS hyS houtS hxM hyM houtM hM' hlive hlivex hlivey hdisp hoptnoop
    | true =>
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hxmem := stackPerm_mem hsv hxS
      have hymem := stackPerm_mem hsv hyS
      have hnospill_x := alookup_of_spilled_eq hspM hxM
      have hnospill_y := alookup_of_spilled_eq hspM hyM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_commBinop_bothlive_step_S hsd hname hcm
        (hdispatch v) hops houts hxy rfl hxmem hymem hlive hfresh hspill_out hnospill_y
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
        rw [genRegularInstPlan_commBinopVar_eq hname hcm hops houts hxy rfl hlive
            hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hoptnoop p]
        rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
      exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩
  | valspilled =>
    obtain ⟨hxS, hxM, offy, hyM⟩ := hplace
    obtain ⟨hox, hoy⟩ := hout
    cases comm with
    | false =>
      obtain ⟨hncomm, hnjmp, hcompute⟩ := hcm
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hxmem := stackPerm_mem hsv hxS
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hspill_y := alookup_of_spilled_eq hspM hyM
      have hnospill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_nonCommBinop_valspilled_step_S (idx := idx)
        hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy hox hoy rfl hxmem hlive hfresh
        hspill_out hspill_y hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
      obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
      have hsmall_x : d_x + 2 ≤ 15 := by
        have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var y, Operand.Var out] } := by
        rw [genRegularInstPlan_nonCommBinopVar_spilled_eq hname hncomm hnjmp hcompute hops houts hxy rfl
            hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove M (Operand.Var y)
      rw [hrev, emit2_valspilled rfl hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x, hspM]
    | true =>
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hxmem := stackPerm_mem hsv hxS
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hspill_y := alookup_of_spilled_eq hspM hyM
      have hnospill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_commBinop_valspilled_step_S (idx := idx)
        hsd hname hcm (hdispatch v) hops houts hxy hox hoy rfl hxmem hlive hfresh hspill_out
        hspill_y hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
      obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
      have hsmall_x : d_x + 2 ≤ 15 := by
        have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var y, Operand.Var out] } := by
        rw [genRegularInstPlan_commBinopVar_valspilled_eq hname hcm hops houts hxy rfl hlive
            hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove M (Operand.Var y)
      rw [hrev, emit2_valspilled rfl hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x, hspM]
  | keyspilled =>
    obtain ⟨hyS, hyM, offx, hxM⟩ := hplace
    obtain ⟨hox, hoy⟩ := hout
    cases comm with
    | false =>
      obtain ⟨hncomm, hnjmp, hcompute⟩ := hcm
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [x, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hymem := stackPerm_mem hsv hyS
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hnospill_y := alookup_of_spilled_eq hspM hyM
      have hspill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_nonCommBinop_keyspilled_step_S (idx := idx)
        hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy hox hoy rfl hymem hlive hfresh
        hspill_out hnospill_y hlivey hspill_x hlivex hdisp (hoptnoop p) hrel hblock
      obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
      have hsmall_y : d_y ≤ 15 := by
        have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var x, Operand.Var out] } := by
        rw [genRegularInstPlan_nonCommBinopVar_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy
            rfl hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove M (Operand.Var x)
      rw [hrev, emit2_keyspilled rfl hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hspM]
    | true =>
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [x, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hymem := stackPerm_mem hsv hyS
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hnospill_y := alookup_of_spilled_eq hspM hyM
      have hspill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_commBinop_keyspilled_step_S (idx := idx)
        hsd hname hcm hfc (hdispatch v) hops houts hxy hox hoy rfl hymem hlive hfresh hspill_out
        hnospill_y hlivey hspill_x hlivex hdisp (hoptnoop p) hrel hblock
      obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
      have hsmall_y : d_y ≤ 15 := by
        have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var x, Operand.Var out] } := by
        rw [genRegularInstPlan_commBinopVar_keyspilled_eq hname hcm hops houts hxy rfl hlive
            hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove M (Operand.Var x)
      rw [hrev, emit2_keyspilled rfl hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hspM]
  | bothspilled =>
    obtain ⟨⟨offy, hyM⟩, offx, hxM⟩ := hplace
    obtain ⟨hox, hoy⟩ := hout
    cases comm with
    | false =>
      obtain ⟨hncomm, hnjmp, hcompute⟩ := hcm
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, x, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hspill_y := alookup_of_spilled_eq hspM hyM
      have hspill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_nonCommBinop_bothspilled_step_S (idx := idx)
        hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy hox hoy rfl hlive hfresh
        hspill_out hspill_y hlivey hspill_x hlivex hdisp (hoptnoop p) hrel hblock
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var y, Operand.Var x, Operand.Var out] } := by
        rw [genRegularInstPlan_nonCommBinopVar_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy
            rfl hlive hspill_y hlivey hspill_x hlivex]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove (aremove M (Operand.Var y)) (Operand.Var x)
      rw [hrev, emit2_bothspilled rfl hspill_y hlivey hspill_x hlivex hxy, hspM]
    | true =>
      show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, x, out] M'
      try simp only [Spill2.gain, List.map] at hoptnoop
      intro p v s j hsd hsv hspM hrel hblock
      have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
      have hspill_y := alookup_of_spilled_eq hspM hyM
      have hspill_x := alookup_of_spilled_eq hspM hxM
      have hspill_out := alookup_of_spilled_eq hspM houtM
      obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_commBinop_bothspilled_step_S (idx := idx)
        hsd hname hcm hfc (hdispatch v) hops houts hxy hox hoy rfl hlive hfresh hspill_out
        hspill_y hlivey hspill_x hlivex hdisp (hoptnoop p) hrel hblock
      have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
      have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
            nextIsTerminator curBbLabel p).2
          = releaseDeadSpills nextLiveness
              { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
                stack := p.stack ++ [Operand.Var y, Operand.Var x, Operand.Var out] } := by
        rw [genRegularInstPlan_commBinopVar_bothspilled_eq hname hcm hops houts hxy rfl hlive
            hspill_y hlivey hspill_x hlivex]
        show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
        rw [hoptnoop p]
      refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
        stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
      show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
          = aremove (aremove M (Operand.Var y)) (Operand.Var x)
      rw [hrev, emit2_bothspilled rfl hspill_y hlivey hspill_x hlivex hxy, hspM]

/-- **The SSTORE spill matrix, as one indexed theorem.** A two-variable-operand
`SSTORE` (2-in-0-out) is a `BodyStepHSV` with gain `m.gainNoOut x y` and spill
map `m.consumed M x y`, for every spill mode `m`. Reuses `Spill2.Placement` and
`Spill2.consumed` unchanged — only the gain drops the (absent) output. The four
originals (`bodyStepHSV_sstore_{bothlive,valspilled,keyspilled,bothspilled}`) are
its definitional instances. -/
theorem bodyStepHSV_sstore (m : Spill2)
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun key val s => sstore key val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hplace : m.Placement S M x y)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hM' : ∀ q : PlanState, q.spilled = m.consumed M x y →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M (m.gainNoOut x y) M' := by
  cases m with
  | bothlive =>
    obtain ⟨hxS, hyS, hxM, hyM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [] M'
    intro p v s j hsd hsv hspM hrel hblock
    have hxmem := stackPerm_mem hsv hxS
    have hymem := stackPerm_mem hsv hyS
    have hnospill_y := alookup_of_spilled_eq hspM hyM
    have hnospill_x := alookup_of_spilled_eq hspM hxM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_sstore_bothlive_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy rfl hxmem hymem hnospill_y hlivey
      hnospill_x hlivex hdisp hrel hblock
    have hshallow : p.stack.length ≤ 15 := by
      have := hsd.shallow; simp only [List.length_nil] at this; omega
    obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
      binopVar_depths_of_shallow hshallow hxmem hymem
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack } := by
      rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
          hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
      rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
        hdepth_x' hsmall_x']
    exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal (by simp) hspM hM'⟩
  | valspilled =>
    obtain ⟨hxS, hxM, offy, hyM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y] M'
    intro p v s j hsd hsv hspM hrel hblock
    have hxmem := stackPerm_mem hsv hxS
    have hspill_y := alookup_of_spilled_eq hspM hyM
    have hnospill_x := alookup_of_spilled_eq hspM hxM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_sstore_valspilled_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy rfl hxmem hspill_y hlivey
      hnospill_x hlivex hdisp hrel hblock
    obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
    have hsmall_x : d_x + 2 ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel p).2
        = releaseDeadSpills nextLiveness
            { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var y] } := by
      rw [genRegularInstPlan_sstore_spilled_eq hname hncomm hnjmp hcompute hops houts hxy rfl
          hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x]
    refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
    show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
        = aremove M (Operand.Var y)
    rw [hrev, emit2_valspilled rfl hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x, hspM]
  | keyspilled =>
    obtain ⟨hyS, hyM, offx, hxM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [x] M'
    intro p v s j hsd hsv hspM hrel hblock
    have hymem := stackPerm_mem hsv hyS
    have hnospill_y := alookup_of_spilled_eq hspM hyM
    have hspill_x := alookup_of_spilled_eq hspM hxM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_sstore_keyspilled_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy rfl hymem hnospill_y hlivey
      hspill_x hlivex hdisp hrel hblock
    obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
    have hsmall_y : d_y ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel p).2
        = releaseDeadSpills nextLiveness
            { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x] } := by
      rw [genRegularInstPlan_sstore_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy rfl
          hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
    refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
    show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
        = aremove M (Operand.Var x)
    rw [hrev, emit2_keyspilled rfl hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hspM]
  | bothspilled =>
    obtain ⟨⟨offy, hyM⟩, offx, hxM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, x] M'
    intro p v s j hsd hsv hspM hrel hblock
    have hspill_y := alookup_of_spilled_eq hspM hyM
    have hspill_x := alookup_of_spilled_eq hspM hxM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_sstore_bothspilled_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy rfl hspill_y hlivey
      hspill_x hlivex hdisp hrel hblock
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel p).2
        = releaseDeadSpills nextLiveness
            { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var y, Operand.Var x] } := by
      rw [genRegularInstPlan_sstore_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy rfl
          hspill_y hlivey hspill_x hlivex]
    refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
    show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
        = aremove (aremove M (Operand.Var y)) (Operand.Var x)
    rw [hrev, emit2_bothspilled rfl hspill_y hlivey hspill_x hlivex hxy, hspM]

/-- **The ternop spill matrix, as one indexed theorem.** A three-variable-operand
pure ternop (`execPure3`) is a `BodyStepHSV` with gain `m.gain x y z out` and
spill map `m.consumed M x y z`, for every single-operand spill mode `m : Spill3`.
Placement is mode-dependent (`Spill3.Placement`); operand distinctness is carried
uniformly (all of `x≠y`, `y≠z`, `x≠z`, and `out` distinct from each) — a vacuous
strengthening in any real instance, four distinct names, that lets one statement
cover cases whose hand-written forms each dropped the locally-unused inequalities.
The four originals (`bodyStepHSV_ternopVar_{bothlive,xspilled,yspilled,zspilled}`)
are recovered by instantiating `m`. -/
theorem bodyStepHSV_ternop (m : Spill3)
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {M M' : AssocList Operand Nat} {x y z out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hplace : m.Placement S M x y z)
    (houtS : out ∉ S)
    (houtM : alookup' M (Operand.Var out) = none)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hM' : ∀ q : PlanState, q.spilled = m.consumed M x y z →
        (releaseDeadSpills nextLiveness q).spilled = M')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ (m.gain x y z out).map Operand.Var }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ (m.gain x y z out).map Operand.Var })) :
    BodyStepHSV lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false
        nextIsTerminator curBbLabel p)
      (inst, idx) S M (m.gain x y z out) M' := by
  cases m with
  | none =>
    obtain ⟨hxS, hyS, hzS, hxM, hyM, hzM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [out] M'
    try simp only [Spill3.gain, List.map] at hoptnoop
    intro p v s j hsd hsv hspM hrel hblock
    have hxmem := stackPerm_mem hsv hxS
    have hymem := stackPerm_mem hsv hyS
    have hzmem := stackPerm_mem hsv hzS
    have hnospill_x := alookup_of_spilled_eq hspM hxM
    have hnospill_y := alookup_of_spilled_eq hspM hyM
    have hnospill_z := alookup_of_spilled_eq hspM hzM
    have hspill_out := alookup_of_spilled_eq hspM houtM
    have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_ternopVar_bothlive_step_S hsd hname hncomm
      hnjmp hcompute (hdispatch v) hops houts hxy hyz hxz hox hoy hoz rfl hxmem hymem hzmem hlive hfresh
      hspill_out hnospill_z hlivez hnospill_y hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
    have hshallow : p.stack.length ≤ 14 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'', hsmall_x, hlenx''⟩ :=
      ternopVar_depths_of_shallow hshallow hxy hyz hxz hxmem hymem hzmem
    have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel p).2 = releaseDeadSpills nextLiveness { p with stack := p.stack ++ [Operand.Var out] } := by
      rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz rfl hlive
          hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y hnospill_x hlivex
          hdepth_x'' hsmall_x, hoptnoop p]
      rw [hrev, emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey
        hdepth_y' hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x]
    exact ⟨⟨as', hrun, hrel', hpc, hsd'⟩, stackPerm_spilled_of_final hsv hfinal rfl hspM hM'⟩
  | xsp =>
    obtain ⟨hyS, hzS, hyM, hzM, offx, hxM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [x, out] M'
    try simp only [Spill3.gain, List.map] at hoptnoop
    intro p v s j hsd hsv hspM hrel hblock
    have hzmem := stackPerm_mem hsv hzS
    have hymem := stackPerm_mem hsv hyS
    have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
    have hnospill_z := alookup_of_spilled_eq hspM hzM
    have hnospill_y := alookup_of_spilled_eq hspM hyM
    have hspill_x := alookup_of_spilled_eq hspM hxM
    have hspill_out := alookup_of_spilled_eq hspM houtM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_ternopVar_xspilled_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hyz hxz hox hoy hoz rfl
      hzmem hymem hlive hfresh hspill_out hnospill_z hlivez hnospill_y hlivey hspill_x hlivex
      hdisp (hoptnoop p) hrel hblock
    obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
    obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
    have hsmall_z : d_z ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hsmall_y : d_y + 1 ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
      rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel p).2
        = releaseDeadSpills nextLiveness
            { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var x, Operand.Var out] } := by
      rw [genRegularInstPlan_ternopVar_xspilled_eq hname hncomm hnjmp hcompute hops houts hyz hxz
          rfl hlive hnospill_z hlivez hnospill_y hlivey hspill_x hlivex hdepth_z hsmall_z
          hdepth_y hsmall_y]
      show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
      rw [hoptnoop p]
    refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
    show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
        = aremove M (Operand.Var x)
    rw [hrev, emit3_xspilled rfl hnospill_z hlivez hnospill_y hlivey hspill_x hlivex hyz
      hdepth_z hsmall_z hdepth_y hsmall_y, hspM]
  | ysp =>
    -- the one ternop mode with an in-file consumer, so its full proof stays in
    -- `GenBlockSimComp` (below this module in the import graph) and this case
    -- delegates to it — the same arrangement as the binop `nonComm/bothlive` case.
    obtain ⟨hxS, hzS, hxM, hzM, offy, hyM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [y, out] M'
    try simp only [Spill3.gain, List.map] at hoptnoop
    exact bodyStepHSV_ternopVar_yspilled hname hncomm hnjmp hcompute hdispatch hops houts
      hxy hxz hyz hox hoy hoz hzS hxS houtS hlive houtM hzM hlivez hyM hlivey hxM hlivex
      hM' hdisp hoptnoop
  | zsp =>
    obtain ⟨hxS, hyS, hxM, hyM, offz, hzM⟩ := hplace
    show BodyStepHSV lo offsetToPc prog _ (inst, idx) S M [z, out] M'
    try simp only [Spill3.gain, List.map] at hoptnoop
    intro p v s j hsd hsv hspM hrel hblock
    have hxmem := stackPerm_mem hsv hxS
    have hymem := stackPerm_mem hsv hyS
    have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
    have hspill_z := alookup_of_spilled_eq hspM hzM
    have hnospill_y := alookup_of_spilled_eq hspM hyM
    have hnospill_x := alookup_of_spilled_eq hspM hxM
    have hspill_out := alookup_of_spilled_eq hspM houtM
    obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_ternopVar_zspilled_step_S (idx := idx)
      hsd hname hncomm hnjmp hcompute (hdispatch v) hops houts hxy hyz hxz hox hoy hoz rfl
      hxmem hymem hlive hfresh hspill_out hspill_z hlivez hnospill_y hlivey hnospill_x hlivex
      hdisp (hoptnoop p) hrel hblock
    obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
    obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
    have hsmall_y : d_y + 2 ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hsmall_x : d_x + 3 ≤ 15 := by
      have := hsd.shallow; simp only [List.length_cons, List.length_nil] at this; omega
    have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
      rw [hops]; rfl
    have hfinal : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
          nextIsTerminator curBbLabel p).2
        = releaseDeadSpills nextLiveness
            { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var z, Operand.Var out] } := by
      rw [genRegularInstPlan_ternopVar_zspilled_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz
          rfl hlive hspill_z hlivez hnospill_y hlivey hnospill_x hlivex hdepth_y hsmall_y
          hdepth_x hsmall_x]
      show releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator _).2 = _
      rw [hoptnoop p]
    refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩,
      stackPerm_spilled_of_final hsv hfinal rfl ?_ hM'⟩
    show ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2).spilled
        = aremove M (Operand.Var z)
    rw [hrev, emit3_zspilled rfl hspill_z hlivez hnospill_y hlivey hnospill_x hlivex hyz hxz hxy
      hdepth_y hsmall_y hdepth_x hsmall_x, hspM]

end EvmYul.Venom.Hol.Codegen

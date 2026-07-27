/-
GenBlockSimComp / Phase 3 — body-fold composition & per-opcode producers

Split part of `GenBlockSimComp`; see that module's header for the full roadmap.
This part continues the single `EvmYul.Venom.Hol.Codegen` namespace and imports
the previous part, so the whole was cut horizontally with no change in meaning.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.BodyAtoms

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ## Body-fold composition kit (chain per-instruction `BodyStep`s into `BodyStepsReady`)

`BodyStepsReady` is cons-structured (`x :: xs` = head-step ∧ ready-tail), and `genBlockBody_sim_inv_S`
folds it into a whole-body sim. What was missing was the *builder* side: a way to assemble
`BodyStepsReady` for an N-instruction body from per-instruction facts. This kit supplies it:

  - `BodyStep` names the head-step (the first conjunct of the cons case) so it can be produced once
    per instruction shape;
  - `bodyStepsReady_nil` / `bodyStepsReady_cons` are the list combinators (`cons` threads `S` by
    `outOf x`, exactly matching the fold's induction);
  - `bodyStep_commBinop` / `bodyStep_unopVar` / `bodyStep_nonCommBinopVar` factor the existing
    `stackDisc_*_step_S` per-instruction steps into `BodyStep` producers.

Chaining `bodyStepsReady_cons` over these producers, then feeding `genBlockBody_sim_inv_S`, gives a
multi-instruction body sim (see `bodyStepsReady_two_commBinop`). The remaining generality gap: the
`gp` is one function for the whole body, so heterogeneous *per-instruction* liveness/`nextIsTerminator`
must be encoded through `gp`'s instruction argument — the producers already take those as parameters,
so a `gp` that dispatches on the index composes; a concrete real-liveness N-instruction block is the
next step. -/

/-- The per-instruction **head-step** — exactly the first conjunct of `BodyStepsReady`'s cons case,
    named so it can be produced once per instruction shape and chained by `bodyStepsReady_cons`. -/
def BodyStep (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + 1) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ [outOf x]) (gp x p).2

/-- Empty body is trivially ready. -/
theorem bodyStepsReady_nil {lo offsetToPc prog gp S} :
    BodyStepsReady lo offsetToPc prog gp ([] : List (Instruction × Nat)) S := trivial

/-- **The body-fold composition step.** Prepend one ready instruction (`BodyStep` at `S`) to a ready
    tail (starting at `S ++ [outOf x]`) to get a ready `x :: xs`. Turns per-instruction `BodyStep`s
    into an N-instruction `BodyStepsReady`, which `genBlockBody_sim_inv_S` then folds. -/
theorem bodyStepsReady_cons {lo offsetToPc prog gp x xs S}
    (hhead : BodyStep lo offsetToPc prog gp x S)
    (htail : BodyStepsReady lo offsetToPc prog gp xs (S ++ [outOf x])) :
    BodyStepsReady lo offsetToPc prog gp (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **`BodyStep` for a commutative var-binop** (immediately before the terminator, `nextIsTerminator =
    true`, so the optimistic swap collapses to a no-op), factored from `bodyStepsReady_single_commBinop`. -/
theorem bodyStep_commBinop
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
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, idx) S := by
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

/-- The commutative both-literal binop as a `BodyStep` — the Lit sibling of
    `bodyStep_commBinop`, dispatching to `stackDisc_commBinopLit_step_S`. First literal-operand
    member of the `bodyStep_*` family. -/
theorem bodyStep_commBinopLit
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {a b : bytes32} {out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hab : a ≠ b)
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopLit_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hab houtS hlive hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The commutative binop with MIXED `[Var x, Lit b]` operands as a `BodyStep`, dispatching to
    `stackDisc_commBinopVarLit_step_S`. With `bodyStep_commBinop` (both vars) and
    `bodyStep_commBinopLit` (both literals) this completes the commutative binop's operand-class
    coverage in the body fold. -/
theorem bodyStep_commBinopVarLit
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x : String} {b : bytes32} {out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopVarLit_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The commutative binop with MIXED `[Lit a, Var y]` operands as a `BodyStep` — the mirror of
    `bodyStep_commBinopVarLit`, dispatching to `stackDisc_commBinopLitVar_step_S`. -/
theorem bodyStep_commBinopLitVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {y : String} {a : bytes32} {out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [out])
    (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopLitVar_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hyS houtS hlive hlivey hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩


/-- **`BodyStep` for a var-unop** (ISZERO/NOT), factored from `stackDisc_unopVar_step_S`. The
    optimistic-swap no-op is hypothesised per plan state (`hoptnoop : ∀ p, …`). -/
theorem bodyStep_unopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out name : String} {idx : Nat} {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure1 f inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_unopVar_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **`BodyStep` for a non-commutative var-binop** (SUB/DIV/SHL/…), factored from
    `stackDisc_nonCommBinopVar_step_S`. -/
theorem bodyStep_nonCommBinopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_nonCommBinopVar_step_S (idx := idx) hsd hsv hname hncomm hnjmp
    hcompute (hdispatch v) hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- SHA3 body-step sim: derive operand values + memory coverage (`hmemsafe`), run
    `genRegularInstPlan_sha3_sim`, and package the venom step (`keccak` of the slice). -/
theorem stackDisc_sha3_bodyStep
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y out : String} {idx : Nat}
    (hsd : StackDisc ps vs)
    (hop : inst.opcode = Opcode.SHA3)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ wx wy, lookupVar x vs = some wx → lookupVar y vs = some wy →
        ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wx.toNat + wy.toNat ≤ ps.alloc.fnEom ∧ wy.toNat < USize.size)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SHA3" → asmStep offsetToPc prog s = asmSha3 s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by have := hsd.shallow; omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  obtain ⟨hcov, hbelow, hsize⟩ := hmemsafe wx wy hwx hwy
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hname : opcodeToEvmName inst.opcode = some "SHA3" := by rw [hop]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hop]; rfl
  have hnjmp : inst.opcode ≠ Opcode.JMP := by rw [hop]; decide
  have hcompute : computeOperands inst = inst.operands.reverse := by simp [computeOperands, hop]
  have hsim := genRegularInstPlan_sha3_sim (d_x' := d_x + 1)
    hname hncomm hnjmp hcompute hops houts hxy hox hoy rfl hlive hfresh (hsd.noSpill _)
    (hsd.noSpill _) hlivey hdepth_y hsmall_y hleny (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hcov hbelow hsize hdisp hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs
      = ExecResult.OK (updateVar out (keccak256 (readMemory wx.toNat wy.toNat vs)) vs) := by
    unfold stepInstBase; rw [hop]; simp only [hops, houts, evalOperand, hwx, hwy]
  exact gvBodyStep_of_updateVar (idx := idx) hstepEq hsim

/-- The `StackIsVars`-aware body step for SHA3, combining `stackDisc_sha3_bodyStep`,
    `stackDisc_binop2_preserve`, and the (value-agnostic) `genRegularInstPlan_nonCommBinopVar_outStack`.
    The memory-hashing counterpart of `stackDisc_nonCommBinopVar_step_S`. -/
theorem stackDisc_sha3_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hop : inst.opcode = Opcode.SHA3)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ wx wy, lookupVar x vs = some wx → lookupVar y vs = some wy →
        ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wx.toNat + wy.toNat ≤ ps.alloc.fnEom ∧ wy.toNat < USize.size)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SHA3" → asmStep offsetToPc prog s = asmSha3 s)
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
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hname : opcodeToEvmName inst.opcode = some "SHA3" := by rw [hop]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hop]; rfl
  have hnjmp : inst.opcode ≠ Opcode.JMP := by rw [hop]; decide
  have hcompute : computeOperands inst = inst.operands.reverse := by simp [computeOperands, hop]
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  have hstepEq : stepInstBase inst vs
      = ExecResult.OK (updateVar out (keccak256 (readMemory wx.toNat wy.toNat vs)) vs) := by
    unfold stepInstBase; rw [hop]; simp only [hops, houts, evalOperand, hwx, hwy]
  refine ⟨stackDisc_sha3_bodyStep hsd.toStackDisc hop hops houts hxy hxmem hymem hfresh hlive hlivex
            hlivey hmemsafe hdisp hoptnoop hrel hblock,
          stackDisc_binop2_preserve hsd hname hncomm hnjmp hcompute hops houts hxy hxmem hymem hfresh
            hlive hlivex hlivey hstepEq hoptnoop, ?_⟩
  have hout := genRegularInstPlan_nonCommBinopVar_outStack (liveness := liveness) (dfg := dfg)
    (cfg := cfg) (fn := fn) (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
    hsd.toStackDisc hname hncomm hnjmp hcompute hops houts hxy hxmem hymem hlive hlivex hlivey hoptnoop
  show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
    curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
  rw [hout, hsv, List.map_append]; rfl

/-- **`BodyStep` for SHA3.** The 2-input memory-hash body-fold producer — the previously-hardest opcode
    wired into the body fold. `hmemsafe` is the runtime memory-in-bounds precondition (a program
    well-formedness side condition), exactly as `bodyStepH_calldatacopy` uses for the copy family. -/
theorem bodyStep_sha3
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.SHA3)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wx wy,
        venomAsmRel lo p v s → lookupVar x v = some wx → lookupVar y v = some wy →
        ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wx.toNat + wy.toNat ≤ p.alloc.fnEom ∧ wy.toNat < USize.size)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SHA3" → asmStep offsetToPc prog s = asmSha3 s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_sha3_step_S (idx := idx) hsd hsv hop hops houts hxy hxS hyS
    houtS hlive hlivex hlivey (fun wx wy hwx hwy => hmemsafe p v s wx wy hrel hwx hwy) hdisp
    (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **A 2-instruction body composes.** Two commutative var-binops (both in the collapsed-swap regime)
    chain via `bodyStepsReady_cons`: the first ready at `S`, the second at `S ++ [out₁]` (the
    S-thread), giving `BodyStepsReady [i₁, i₂]` — feedable to `genBlockBody_sim_inv_S` for a whole
    2-instruction-body sim. Validates that the kit scales past one instruction. -/
theorem bodyStepsReady_two_commBinop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 o2 n1 n2 : String} {idx1 idx2 : Nat}
    {f1 f2 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some n2) (hcomm2 : isCommutative i2.opcode = true)
    (hdisp2' : ∀ v, stepInstBase i2 v = execPure2 f2 i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1]) (ho2S : o2 ∉ S ++ [o1])
    (hlive2 : nextLiveness.contains o2 = true) (hlivex2 : nextLiveness.contains x2 = true)
    (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n2 → asmStep offsetToPc prog s = asmBinop f2 s) :
    BodyStepsReady lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      [(i1, idx1), (i2, idx2)] S := by
  have hstep1 := bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
    (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
  have hstep2 := bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
    (curBbLabel := curBbLabel) (S := S ++ [o1]) hname2 hcomm2 hdisp2' hops2 houts2 hxy2 hx2S hy2S ho2S hlive2 hlivex2 hlivey2 hdisp2
  have hout1 : outOf (i1, idx1) = o1 := by simp [outOf, houts1]
  refine bodyStepsReady_cons hstep1 ?_
  rw [hout1]
  exact bodyStepsReady_cons hstep2 bodyStepsReady_nil

/-- **`BodyStep` for a var-ternop** (ADDMOD/MULMOD), factored from `stackDisc_ternopVar_step_S`. -/
theorem bodyStep_ternopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y z out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_ternopVar_step_S (idx := idx) hsd hsv hname hncomm hnjmp
    hcompute (hdispatch v) hops houts hxy hyz hxz hxS hyS hzS houtS hlive hlivex hlivey hlivez hdisp
    (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ### `BodyStep` producer for 0-input context pushes (wiring a non-arithmetic atom into the fold)

The first body-fold producer for an op that is *not* an arithmetic var-op: a 0-input context push
(`CALLVALUE`, `CALLER`, `CODESIZE`, …), built on `genRegularInstPlan_read0_eq`/`_sim`. The output
stack (`genRegularInstPlan_read0_outStack`) and headroom (`stackDisc_read0_preserve`) mirror the
arithmetic producers; the wrinkle is that the pushed value is a *state field* (`fV v` on the Venom
side, `fA s` on the asm side, equal under the relation), threaded through `hfield`. -/

/-- Output stack of a 0-input push: `ps.stack ++ [Var out]` (the 0-operand analog of
    `genRegularInstPlan_commBinopVar_outStack`). -/
theorem genRegularInstPlan_read0_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {out name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive]
  simp only [hoptnoop]
  rw [releaseDeadSpills_stack]

/-- Headroom preservation for a 0-input push: `StackDiscH (k+1)` before ⇒ `StackDiscH k` after (one
    output pushed). The 0-operand analog of `stackDisc_commBinopVar_preserve`. -/
theorem stackDisc_read0_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {out name : String} {idx k : Nat} {v : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out v vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive]
  simp only [hoptnoop]
  apply releaseDeadSpills_stackDiscH
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out v vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    show ∃ w, lookupVar z (updateVar out v vs) = some w
    rw [List.mem_append] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨w, hw⟩ := hsd.defined z h
      exact ⟨w, by rw [lookupVar_updateVar_ne vs out z v hzout]; exact hw⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      exact ⟨v, by rw [h']; exact lookupVar_updateVar_self vs out v⟩

/-- The `StackIsVars`-aware body step for a 0-input push: the sim (via `gvBodyStep_of_updateVar`), the
    headroom drop, and the output shape `StackIsVars (S ++ [out])`. The 0-operand analog of
    `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_read0_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {out name : String} {k idx : Nat} {v : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out v vs))
    (hdisp : ∀ (h : as.pc < prog.length),
        prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog as = asmPushVal v as)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  have hsim := genRegularInstPlan_read0_sim hname hnjmp hcompute hops houts hlive
    hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read0_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read0_outStack hname hnjmp hcompute hops houts hlive hoptnoop, hsv,
      List.map_append]; rfl

/-- **`BodyStep` for a 0-input context-push op** (CALLVALUE / CALLER / CODESIZE / …). The pushed value
    is a state field: `fV v` on the Venom side (`hstepEq`), `fA s` on the asm side (`hdispAsm`), equal
    under the relation (`hfield`, from the equated `venomAsmRel` conjunct for that field). The first
    non-arithmetic body-fold producer — lets context pushes chain via `bodyStepsReady_cons` alongside
    the arithmetic ops. -/
theorem bodyStep_read0
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {out name : String} {idx : Nat}
    {fV : VenomState → bytes32} {fA : AsmState → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hstepEq : ∀ v, stepInstBase inst v = ExecResult.OK (updateVar out (fV v) v))
    (hdispAsm : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fA s) s)
    (hfield : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { p with stack := p.stack ++ [Operand.Var out] }
      = ([], { p with stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hdisp : ∀ (h : s.pc < prog.length),
      prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fV v) s := by
    intro h hg; rw [hdispAsm s h hg, hfield p v s hrel]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_read0_step_S (idx := idx) (v := fV v) hsd hsv hname hnjmp
    hcompute hops houts houtS hlive (hstepEq v) hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ### First concrete `bodyStep_read0` instances: the 0-input environment pushes

`bodyStep_read0` is the generic 0-input/1-output push producer; `bodyStep_ctxPush0` specialises it to
the terminator-adjacent env-push shape (fixing `nextIsTerminator := true`, which collapses the optimistic
swap to a no-op, and packaging the boilerplate), and CALLER/CALLVALUE/ADDRESS/GAS are its one-liner
instances — the `execRead0` opcodes whose pushed field lives in the preserved `callCtx` (so the field
bridge is a single `venomAsmRel` projection, exactly as in `emit_caller_sim`). This is the body-fold
counterpart of `emit_ctx_push_sim`. -/

/-- **Generic terminator-adjacent env-push `BodyStep`.** `bodyStep_read0` with `nextIsTerminator := true`
    and the optimistic-swap no-op discharged; each concrete env opcode supplies only `hname` / `hstepEq`
    (its `execRead0` reduction) / `hdispAsm` (its `asmStep_*_ok`) / `hfield` (its `callCtx` bridge). -/
theorem bodyStep_ctxPush0
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out name : String} {idx : Nat}
    {fV : VenomState → bytes32} {fA : AsmState → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hstepEq : ∀ v, stepInstBase inst v = ExecResult.OK (updateVar out (fV v) v))
    (hdispAsm : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fA s) s)
    (hfield : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_read0 hname hnjmp hcompute hops houts houtS hlive hstepEq hdispAsm hfield
    (fun p => by simp [optimisticSwapPlan])

/-- **`BodyStep` for CALLER** — `out := caller`. First concrete env-push instance. -/
theorem bodyStep_caller
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.CALLER)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "CALLER") (fV := fun v => addressToWord v.callCtx.caller)
    (fA := fun s => addressToWord s.callCtx.caller)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => addressToWord s.callCtx.caller) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_caller_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for CALLVALUE** — `out := callvalue`. -/
theorem bodyStep_callvalue
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.CALLVALUE)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "CALLVALUE") (fV := fun v => v.callCtx.callvalue)
    (fA := fun s => s.callCtx.callvalue)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.callCtx.callvalue) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_callvalue_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for ADDRESS** — `out := address` (executing contract). -/
theorem bodyStep_address
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.ADDRESS)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "ADDRESS") (fV := fun v => addressToWord v.callCtx.contract)
    (fA := fun s => addressToWord s.callCtx.contract)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => addressToWord s.callCtx.contract) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_address_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for GAS** — `out := gas`. -/
theorem bodyStep_gas
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.GAS)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "GAS") (fV := fun v => EvmYul.UInt256.ofNat v.callCtx.gas)
    (fA := fun s => EvmYul.UInt256.ofNat s.callCtx.gas)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => EvmYul.UInt256.ofNat s.callCtx.gas) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_gas_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for ORIGIN** — `out := origin` (the *tx-context* field; `venomAsmRel` projection
    `…2.2.1` rather than the `callCtx` one, showing `bodyStep_ctxPush0` is not tied to `callCtx`). -/
theorem bodyStep_origin
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.ORIGIN)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "ORIGIN") (fV := fun v => addressToWord v.txCtx.origin)
    (fA := fun s => addressToWord s.txCtx.origin)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => addressToWord s.txCtx.origin) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_origin_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for NUMBER** — `out := block.number` (the *block-context* projection `…2.2.2.1`). -/
theorem bodyStep_number
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.NUMBER)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "NUMBER") (fV := fun v => v.blockCtx.number)
    (fA := fun s => s.blockCtx.number)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.blockCtx.number) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_number_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for CALLDATASIZE** — `out := |calldata|` (`callCtx` projection, non-address field). -/
theorem bodyStep_calldatasize
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.CALLDATASIZE)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "CALLDATASIZE")
    (fV := fun v => EvmYul.UInt256.ofNat v.callCtx.calldata.length)
    (fA := fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v
          = execRead0 (fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_calldatasize_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for CODESIZE** — `out := |code|` (the top-level `code` projection `…2.2.2.2.1`). -/
theorem bodyStep_codesize
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.CODESIZE)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "CODESIZE") (fV := fun v => EvmYul.UInt256.ofNat v.code.length)
    (fA := fun s => EvmYul.UInt256.ofNat s.code.length)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => EvmYul.UInt256.ofNat s.code.length) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_codesize_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for RETURNDATASIZE** — `out := returndata.size` (the `returndata` projection `…2.2.1`). -/
theorem bodyStep_returndatasize
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.RETURNDATASIZE)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "RETURNDATASIZE")
    (fV := fun v => EvmYul.UInt256.ofNat v.returndata.size)
    (fA := fun s => EvmYul.UInt256.ofNat s.returndata.size)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v
          = execRead0 (fun s => EvmYul.UInt256.ofNat s.returndata.size) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_returndatasize_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.1])

/-- **`BodyStep` for SELFBALANCE** — `out := balance(self)`. A 0-input env-push (so `bodyStep_ctxPush0`,
    like the other pushes) whose read touches *two* state components: `callCtx.contract` and `accounts`
    — so the field bridge uses both the `callCtx` and `accounts` conjuncts of `venomAsmRel`. -/
theorem bodyStep_selfbalance
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.SELFBALANCE)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "SELFBALANCE")
    (fV := fun v => EvmYul.UInt256.ofNat (lookupAccount v.callCtx.contract v.accounts).balance)
    (fA := fun s => EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s =>
          EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_selfbalance_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.1, hrel.2.2.2.1])

/-! ### Remaining env-push siblings (tx-context / block-context reads)

`bodyStep_ctxPush0` instances for the env pushes whose emit sims (`emit_gasprice_sim`, …) and
`asmStep_*_ok` were already in place — completing the 0-input environment-read family. Each is a
one-liner differing only in the `txCtx` / `blockCtx` field read and its `venomAsmRel` projection. -/

/-- **`BodyStep` for GASPRICE** — `out := txCtx.gasprice`. -/
theorem bodyStep_gasprice
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.GASPRICE) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "GASPRICE") (fV := fun v => v.txCtx.gasprice) (fA := fun s => s.txCtx.gasprice)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.txCtx.gasprice) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_gasprice_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for CHAINID** — `out := txCtx.chainid`. -/
theorem bodyStep_chainid
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.CHAINID) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "CHAINID") (fV := fun v => v.txCtx.chainid) (fA := fun s => s.txCtx.chainid)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.txCtx.chainid) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_chainid_ok h hg) (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for COINBASE** — `out := block.coinbase`. -/
theorem bodyStep_coinbase
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.COINBASE) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "COINBASE") (fV := fun v => addressToWord v.blockCtx.coinbase)
    (fA := fun s => addressToWord s.blockCtx.coinbase)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => addressToWord s.blockCtx.coinbase) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_coinbase_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for TIMESTAMP** — `out := block.timestamp`. -/
theorem bodyStep_timestamp
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.TIMESTAMP) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "TIMESTAMP") (fV := fun v => v.blockCtx.timestamp)
    (fA := fun s => s.blockCtx.timestamp)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.blockCtx.timestamp) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_timestamp_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for BASEFEE** — `out := block.basefee`. -/
theorem bodyStep_basefee
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.BASEFEE) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "BASEFEE") (fV := fun v => v.blockCtx.basefee)
    (fA := fun s => s.blockCtx.basefee)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.blockCtx.basefee) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_basefee_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.1])

/-- **`BodyStep` for GASLIMIT** — `out := block.gaslimit`. -/
theorem bodyStep_gaslimit
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx : Nat}
    (hop : inst.opcode = Opcode.GASLIMIT) (hops : inst.operands = []) (houts : inst.outputs = [out])
    (houtS : out ∉ S) (hlive : nextLiveness.contains out = true) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (inst, idx) S :=
  bodyStep_ctxPush0 (name := "GASLIMIT") (fV := fun v => v.blockCtx.gaslimit)
    (fA := fun s => s.blockCtx.gaslimit)
    (by rw [hop]; rfl) (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts houtS hlive
    (fun v => by
      have h0 : stepInstBase inst v = execRead0 (fun s => s.blockCtx.gaslimit) inst v := by
        unfold stepInstBase; rw [hop]
      rw [h0]; simp only [execRead0, houts])
    (fun s h hg => asmStep_gaslimit_ok h hg)
    (fun p v s hrel => by simp only [hrel.2.2.2.2.2.2.2.2.2.1])

/-! ### `BodyStep` producer for SLOAD (a 1-input storage load)

The load counterpart of the read0 producer. It has a stack *input* (the key), so — unlike read0 — the
input's stack depth is derived from `StackIsVars S` inside `stackDisc_sload_step_S` (as the arithmetic
producers do), and the plan state carries the input-emission bridge (`sload_emit2_eq`). No field bridge
is needed: `emit_sload_sim` reconciles `sload key as.toVenomState` with `sload key vs` internally. -/

/-- Reduce `(emitInputPlan opc (reverse = [Var x]) nl ps).2` to `{ps with stack := stackDup dist ps.stack}`
    — the single-var input emission is a `doDup`. -/
private theorem sload_emit2_eq {inst : Instruction} {nextLiveness : List String} {ps : PlanState}
    {x : String} {dist : Nat}
    (hops : inst.operands = [Operand.Var x])
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) :
    (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2
      = { ps with stack := stackDup dist ps.stack } := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepth, hdd, List.nil_append]
  rw [hrev, hemiteq, hdo]

/-- Output stack of an SLOAD: `ps.stack ++ [Var out]` (unopVar shape). -/
theorem genRegularInstPlan_read1_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x out name : String} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
      hdepth hsmall hpeek]
  simp only [hoptnoop]
  rw [releaseDeadSpills_stack]

/-- Headroom preservation for a 1-input/1-output read (SLOAD/TLOAD): `StackDiscH (k+1)` before ⇒
    `StackDiscH k` after. Read-generic — the pushed value `val` is abstract (from `hstepEq`). -/
theorem stackDisc_read1_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x out name : String} {idx k dist : Nat} {val : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
      hdepth hsmall hpeek]
  simp only [hoptnoop]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [sload_emit2_eq hops hnospill hlivex hdepth hsmall]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    show ∃ ww, lookupVar z (updateVar out val vs) = some ww
    rw [List.mem_append] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z h
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **`StackDiscHS` preservation across a spilled 1-input read.** The spill-aware analogue of
    `stackDisc_read1_preserve`: the input `x` is *spilled* (not on the stack), so the emit restores
    and DUPs it (`base ++ [x, x]`, grows by 2), the read consumes one copy and pushes `out`
    (`base ++ [x, out]`), the spill slot is freed, and dead spills are released — re-establishing
    `StackDiscHS` at headroom `k` (from `k+2`) against the post-run asm state `as'` (whose memory
    only grew, discharging `spillWf` for the surviving slots). -/
theorem stackDiscHS_read1_spilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x out name : String} {idx k off : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base) (houtx : out ≠ x)
    (hdef_x : ∃ w, lookupVar x vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_unopVar_spilled_eq hname hnjmp hcompute hops houts hstack0 hlive hspill hlivex,
      hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hemitshape : emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps.spilled (Operand.Var x), alloc := freeSpillSlot off ps.alloc }) := by
    have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
    rw [hrev]; unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append, emitOneInput_var_spilled_eq hspill hlivex]
  rw [hemitshape]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var x) o off' hlook
  · show (base ++ [Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var x, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_x
      refine ⟨ww, ?_⟩
      rw [h', lookupVar_updateVar_ne vs out x val houtx.symm]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- The `StackIsVars`-aware body step for SLOAD: derives the input depth from `StackIsVars S`, runs the
    sim (`genRegularInstPlan_sload_sim` via `gvBodyStep_of_updateVar`), and threads the headroom /
    output shape. The storage-load analog of `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_sload_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => sload key s) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (sload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_sload_sim hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for SLOAD.** The storage-load body-fold producer. Unlike `bodyStep_read0`, no field
    bridge is needed (`emit_sload_sim` reconciles the asm/Venom reads internally via the
    `accounts`/`callCtx` conjuncts); the input depth is derived from `StackIsVars S` inside
    `stackDisc_sload_step_S`. -/
theorem bodyStep_sload
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => sload key s) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_sload_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for TLOAD (transient-storage load): the twin of
    `stackDisc_sload_step_S`, using `genRegularInstPlan_tload_sim` and the read-generic
    `stackDisc_read1_preserve` / `genRegularInstPlan_read1_outStack`. -/
theorem stackDisc_tload_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => tload key s) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (tload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_tload_sim hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for TLOAD.** The transient-storage-load body-fold producer; the twin of `bodyStep_sload`
    via `stackDisc_tload_step_S`. -/
theorem bodyStep_tload
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => tload key s) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_tload_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **Spill-aware body step for a spilled TLOAD.** The reroute of `stackDisc_tload_step_S` off
    `StackDiscH.noSpill`: when the operand `x` is *spilled*, `StackDiscHS (k+2)` drives the restore+dup
    emit, the transient-load, and the invariant re-establishment — bundling `StackDiscHS k` inside the
    existential (tied to the post-run asm state `as'`, since `spillWf` reads its memory size). Composes
    `genRegularInstPlan_tload_spilled_sim` with `stackDiscHS_read1_spilled_preserve`; the first body
    producer that consumes the spill-aware invariant rather than assuming `noSpill`. -/
theorem stackDiscHS_tload_spilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x out : String} {base : List Operand} {off idx k : Nat}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => tload key s) inst vs)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base) (houtx : out ≠ x)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
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
  obtain ⟨w, hw⟩ := venomAsmRel_spilled_defined hrel hspill
  have hval : operandVal vs lo (Operand.Var x) = some w := by
    rw [operandVal_var_eq_lookupVar]; exact hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (tload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_tload_spilled_sim hname hnjmp hcompute hops houts hstack0 hlive
    hspill hlivex hval hfresh houtx hspill_out hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read1_spilled_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts
    hstack0 hlive hspill hlivex hfresh houtx ⟨w, hw⟩ hstepEq hoptnoop

/-- **Spilled-operand unary-op step** (generic pure `f`): the op-generic twin of
    `stackDiscHS_tload_spilled_step_S` and the spilled twin of `stackDiscHS_unopVar_bothlive_step_S`.
    Restores the spilled input, DUPs it, applies the opcode. -/
theorem stackDiscHS_unopVar_spilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x out name : String} {base : List Operand}
    {off idx k : Nat} {f : bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base) (houtx : out ≠ x)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hstepF : ∀ ww, operandVal vs lo (Operand.Var x) = some ww →
        stepInstBase inst vs = ExecResult.OK (updateVar out (f ww) vs))
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmUnop f s)
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
  obtain ⟨w, hw⟩ := venomAsmRel_spilled_defined hrel hspill
  have hval : operandVal vs lo (Operand.Var x) = some w := by
    rw [operandVal_var_eq_lookupVar]; exact hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) := hstepF w hval
  have hsim := genRegularInstPlan_unopVar_spilled_sim hname hnjmp hcompute hops houts hstack0 hlive
    hspill hlivex hval hfresh houtx hspill_out hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read1_spilled_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts
    hstack0 hlive hspill hlivex hfresh houtx ⟨w, hw⟩ hstepEq hoptnoop


/-- The `StackIsVars`-aware body step for CALLDATALOAD (calldata-word read): `bodyStep_tload`'s twin
    using `genRegularInstPlan_calldataload_sim` and the read-generic preserve/outStack. -/
theorem stackDisc_calldataload_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "CALLDATALOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun offset s =>
        wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "CALLDATALOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun offset s =>
            wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out
      (wordOfBytes ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding w.toNat 32)) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_calldataload_sim hname hnjmp hcompute hops houts rfl hlive hnospill
    hlivex hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for CALLDATALOAD** — the calldata-word read, via `stackDisc_calldataload_step_S`. -/
theorem bodyStep_calldataload
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATALOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun offset s =>
        wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "CALLDATALOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun offset s =>
            wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_calldataload_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for BALANCE (account-balance query): the account-read twin of
    `stackDisc_tload_step_S`, using `genRegularInstPlan_accountRead_sim` and the read-generic
    `stackDisc_read1_preserve` / `genRegularInstPlan_read1_outStack`. -/
theorem stackDisc_balance_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "BALANCE")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun addr s =>
        EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).balance) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "BALANCE" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            EvmYul.UInt256.ofNat
              (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).balance) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out
      (EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 w) vs.accounts).balance) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_accountRead_sim
    (fRead := fun addr accts =>
      EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) accts).balance)
    hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for BALANCE.** The account-balance-query body-fold producer; the account-read twin of
    `bodyStep_sload`/`bodyStep_tload` via `stackDisc_balance_step_S`. The first *previously-unmodeled*
    opcode wired into the body-fold layer (needed extending the asm machine with a `BALANCE` case). -/
theorem bodyStep_balance
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "BALANCE")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun addr s =>
        EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).balance) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "BALANCE" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            EvmYul.UInt256.ofNat
              (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).balance) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_balance_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **Generic account-read step** — abstracts `stackDisc_balance_step_S`/`_extcodesize_step_S`/
    `_extcodehash_step_S` over the read `fRead : bytes32 → Accounts → bytes32` (the asm side reads the
    shared `.accounts`, `venomAsmRel`-equal to the Venom side). The account-query family collapses to
    one lemma via `genRegularInstPlan_accountRead_sim`. -/
theorem stackDisc_accountRead_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out name : String} {k idx : Nat} {fRead : bytes32 → Accounts → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun addr s => fRead addr s.accounts) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (fRead w vs.accounts) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_accountRead_sim (fRead := fRead)
    hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **Generic account-read `BodyStep`** (BALANCE/EXTCODESIZE/EXTCODEHASH), over the read `fRead`. -/
theorem bodyStep_accountRead
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out name : String} {idx : Nat} {fRead : bytes32 → Accounts → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun addr s => fRead addr s.accounts) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_accountRead_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for EXTCODESIZE (account code length): `bodyStep_balance`'s twin
    with `fRead` reading `.code.length`. -/
theorem stackDisc_extcodesize_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "EXTCODESIZE")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun addr s =>
        EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code.length) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "EXTCODESIZE" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            EvmYul.UInt256.ofNat
              (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).code.length) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out
      (EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 w) vs.accounts).code.length) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_accountRead_sim
    (fRead := fun addr accts =>
      EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) accts).code.length)
    hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for EXTCODESIZE** — the account-code-length query, via `stackDisc_extcodesize_step_S`. -/
theorem bodyStep_extcodesize
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "EXTCODESIZE")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun addr s =>
        EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code.length) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "EXTCODESIZE" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            EvmYul.UInt256.ofNat
              (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).code.length) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_extcodesize_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for EXTCODEHASH (account code hash): `bodyStep_balance`'s twin
    with `fRead` reading the keccak of the account code (`⟨0⟩` for empty code). -/
theorem stackDisc_extcodehash_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "EXTCODEHASH")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun addr s =>
        let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.accounts
        if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "EXTCODEHASH" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts
            if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out
      (let acct := lookupAccount (AccountAddress.ofUInt256 w) vs.accounts
       if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_accountRead_sim
    (fRead := fun addr accts =>
      let acct := lookupAccount (AccountAddress.ofUInt256 addr) accts
      if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray))
    hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read1_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read1_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for EXTCODEHASH** — the account-code-hash query, via `stackDisc_extcodehash_step_S`. -/
theorem bodyStep_extcodehash
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "EXTCODEHASH")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun addr s =>
        let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.accounts
        if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "EXTCODEHASH" →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s =>
            let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts
            if acct.code.isEmpty then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_extcodehash_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **End-to-end 2-instruction body sim.** Chains two commutative var-binops via the composition kit
    (`bodyStepsReady_two_commBinop`) and folds them through `genBlockBody_sim_inv_S`: running the whole
    2-instruction body's asm from a disciplined, `S`-shaped, related state ends OK, still related, with
    the discipline at 0 and the stack now `S ++ [o₁, o₂]`. The concrete payoff of the body-fold kit —
    it composes the builder (kit) with the fold into a genuine multi-instruction body simulation. -/
theorem genBlockBody_two_commBinop_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 o2 n1 n2 : String} {idx1 idx2 : Nat}
    {f1 f2 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some n2) (hcomm2 : isCommutative i2.opcode = true)
    (hdisp2' : ∀ v, stepInstBase i2 v = execPure2 f2 i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1]) (ho2S : o2 ∉ S ++ [o1])
    (hlive2 : nextLiveness.contains o2 = true) (hlivex2 : nextLiveness.contains x2 = true)
    (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n2 → asmStep offsetToPc prog s = asmBinop f2 s)
    (hsd0 : StackDiscH 2 ps0 vs0) (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].map outOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReady_two_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (curBbLabel := curBbLabel) (idx1 := idx1) (idx2 := idx2)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S
    hlive1 hlivex1 hlivey1 hdisp1 hname2 hcomm2 hdisp2' hops2 houts2 hxy2 hx2S hy2S ho2S hlive2 hlivex2 hlivey2 hdisp2
  exact genBlockBody_sim_inv_S
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ## General body fold — 0- and 1-output ops (`outsOf`/`BodyStepG`/`genBlockBodyG_sim_inv`)

`BodyStep`/`BodyStepsReady`/`genBlockBody_sim_inv_S` assume exactly one output per instruction (they
thread `S ++ [outOf x]` and count `l.length` units of headroom). That excludes no-output observable-
effect ops (stores, LOG). This generalisation replaces the single output `outOf x : String` with the
full list `outsOf x = x.1.outputs : List String`: a 0-output op contributes `[]` (stack and headroom
unchanged), a 1-output op contributes `[out]` (the old behaviour). `bodyStepG_of_bodyStep` bridges
every existing 1-output producer into the general fold, so 0- and 1-output ops mix freely in one body. -/

/-- The full output list of a body instruction (0 or 1 element in practice). Generalises `outOf`
    (a single `String`) so a *0-output* op contributes `[]` — the stack stays `S`. -/
def outsOf (x : Instruction × Nat) : List String := x.1.outputs

/-- The per-instruction head-step, generalised to an arbitrary output list: an op with
    `(outsOf x).length` outputs consumes that many units of headroom (`StackDiscH (j+n) → StackDiscH j`)
    and grows the stack by `outsOf x` (`S → S ++ outsOf x`). For a 1-output op this is `BodyStep`; for
    a 0-output op (store/LOG) it keeps `S` and the headroom. -/
def BodyStepG (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + (outsOf x).length) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ outsOf x) (gp x p).2

/-- Readiness for a general body (mixing 0- and 1-output ops). -/
def BodyStepsReadyG (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepG lo offsetToPc prog gp x S ∧ BodyStepsReadyG lo offsetToPc prog gp xs (S ++ outsOf x)

theorem bodyStepsReadyG_nil {lo offsetToPc prog gp S} :
    BodyStepsReadyG lo offsetToPc prog gp ([] : List (Instruction × Nat)) S := trivial

theorem bodyStepsReadyG_cons {lo offsetToPc prog gp x xs S}
    (hhead : BodyStepG lo offsetToPc prog gp x S)
    (htail : BodyStepsReadyG lo offsetToPc prog gp xs (S ++ outsOf x)) :
    BodyStepsReadyG lo offsetToPc prog gp (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Bridge: a 1-output `BodyStep` is a `BodyStepG`.** So every existing producer (`bodyStep_commBinop`,
    `bodyStep_read0`, `bodyStep_sload`, …) feeds the general fold unchanged: for a 1-output op
    `outsOf x = [out]`, so the headroom delta is `1` and `S ++ outsOf x = S ++ [outOf x]`. -/
theorem bodyStepG_of_bodyStep {lo offsetToPc prog gp x S out}
    (houts : x.1.outputs = [out]) (h : BodyStep lo offsetToPc prog gp x S) :
    BodyStepG lo offsetToPc prog gp x S := by
  intro p v s j hsd hsv hrel hblock
  have hlen : (outsOf x).length = 1 := by rw [outsOf, houts]; rfl
  rw [hlen] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := h p v s j hsd hsv hrel hblock
  have houtOf : outsOf x = [outOf x] := by rw [outsOf, outOf, houts]; rfl
  exact ⟨hsim, hsd', by rw [houtOf]; exact hsv'⟩

/-- **The general S-threading body fold** (0- and 1-output). Same shape as `genBlockBody_sim_inv_S`, but
    the headroom is `(l.flatMap outsOf).length` (Σ outputs, not #instructions) and the stack grows by
    `l.flatMap outsOf` — so a 0-output op consumes 0 headroom and leaves the stack unchanged. -/
theorem genBlockBodyG_sim_inv {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyG lo offsetToPc prog gp l S0 →
      StackDiscH (l.flatMap outsOf).length ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
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
             StackIsVars (S0 ++ l.flatMap outsOf)
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
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscH ((xs.flatMap outsOf).length + (outsOf x).length) ps0 vs0 := by
      have he : ((x :: xs).flatMap outsOf).length = (xs.flatMap outsOf).length + (outsOf x).length := by
        rw [List.flatMap_cons, List.length_append]; omega
      rwa [he] at hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ :=
      hstepx ps0 vs0 as0 (xs.flatMap outsOf).length hsd0' hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ outsOf x) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · rw [List.flatMap_cons, ← List.append_assoc]; exact hsv'

/-! ### Demand-decoupled body fold (headroom demand ≠ output count, for N-input 0-output ops)

The copies (3-input, 0-output) don't fit the output-count headroom of `genBlockBodyG_sim_inv`: the 3rd
DUP reaches `original_depth + 2`, needing `StackDiscH 1` even though `outsOf = []`. This generalisation
threads a per-instruction *demand* `dem` (≥ the output count) for the headroom, decoupled from the
stack delta `outsOf`. `genBlockBodyG_sim_inv` is the `dem = outsOf.length` special case; the copies use
`dem = inputs.length - 2`. `bodyStepH_of_bodyStepG` feeds every existing producer in via monotonicity. -/

/-- `StackDiscH` is antitone in the headroom index: more reserved headroom is a stronger claim. -/
theorem StackDiscH.mono {a b : Nat} {p : PlanState} {v : VenomState}
    (h : StackDiscH a p v) (hab : b ≤ a) : StackDiscH b p v where
  noSpill := h.noSpill
  shallow := by have := h.shallow; omega
  defined := h.defined

/-- The per-instruction head-step with an explicit *headroom demand* `dem` — decoupled from the output
    count `outsOf`. An op reserves `dem` units of headroom (`StackDiscH (j + dem) → StackDiscH j`) — for
    an N-input op `dem ≥ N - 2` covers the deepest DUP's reach even when the output count is smaller
    (e.g. a 3-input 0-output copy needs `dem = 1` though `outsOf = []`). The stack still grows by
    `outsOf x` only. -/
def BodyStepH (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Nat) (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + dem) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ outsOf x) (gp x p).2

/-- Readiness with a per-instruction demand function `dem`. -/
def BodyStepsReadyH (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepH lo offsetToPc prog gp (dem x) x S ∧ BodyStepsReadyH lo offsetToPc prog gp dem xs (S ++ outsOf x)

theorem bodyStepsReadyH_nil {lo offsetToPc prog gp dem S} :
    BodyStepsReadyH lo offsetToPc prog gp dem ([] : List (Instruction × Nat)) S := trivial

theorem bodyStepsReadyH_cons {lo offsetToPc prog gp dem x xs S}
    (hhead : BodyStepH lo offsetToPc prog gp (dem x) x S)
    (htail : BodyStepsReadyH lo offsetToPc prog gp dem xs (S ++ outsOf x)) :
    BodyStepsReadyH lo offsetToPc prog gp dem (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Bridge: `BodyStepG` (output-count demand) is a `BodyStepH` at any demand `≥ outsOf.length`.** So
    every 0- and 1-output producer feeds the demand-threading fold; ops whose reach demand exceeds
    their output count (the copies) use a larger `dem`. -/
theorem bodyStepH_of_bodyStepG {lo offsetToPc prog gp dem x S}
    (hdem : (outsOf x).length ≤ dem) (h : BodyStepG lo offsetToPc prog gp x S) :
    BodyStepH lo offsetToPc prog gp dem x S := by
  intro p v s j hsd hsv hrel hblock
  exact h p v s j (StackDiscH.mono hsd (by omega)) hsv hrel hblock

/-- **`BodyStepH` for CALLER** at any demand `≥ 1` — the env-push counterpart of the copy-family
    `bodyStepH_*` producers. Lifts `bodyStep_caller` through `bodyStepG_of_bodyStep` (1 output) and
    `bodyStepH_of_bodyStepG`, so CALLER now composes in the general demand-threaded body fold. -/
theorem bodyStepH_caller
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {out : String} {idx dem : Nat}
    (hdem : 1 ≤ dem)
    (hop : inst.opcode = Opcode.CALLER)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      dem (inst, idx) S := by
  exact bodyStepH_of_bodyStepG (by rw [outsOf, houts]; simpa using hdem)
    (bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_caller hop hops houts houtS hlive))

/-- **The demand-threading body fold.** Generalises `genBlockBodyG_sim_inv`: headroom is `Σ dem`
    (a per-instruction reach demand) instead of `Σ outsOf.length`, so N-input 0-output ops (copies) —
    whose reach demand exceeds their output count — compose too. Stack still grows by `l.flatMap outsOf`. -/
theorem genBlockBodyH_sim_inv {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyH lo offsetToPc prog gp dem l S0 →
      StackDiscH (l.map dem).sum ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
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
             StackIsVars (S0 ++ l.flatMap outsOf)
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
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscH ((xs.map dem).sum + dem x) ps0 vs0 := by
      have he : ((x :: xs).map dem).sum = (xs.map dem).sum + dem x := by
        rw [List.map_cons, List.sum_cons]; omega
      rwa [he] at hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ :=
      hstepx ps0 vs0 as0 (xs.map dem).sum hsd0' hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ outsOf x) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · rw [List.flatMap_cons, ← List.append_assoc]; exact hsv'

/-! ## Threading an explicit output layout — admitting CONSUMING steps

`BodyStepH` hardcodes `StackIsVars (S ++ outsOf x)`: the stack only ever grows. That is the
**duplicating** regime, where an operand stays live and the generator DUPs it. An instruction whose
operands are dead consumes them off the stack, so its output layout is *shorter* — it cannot be a
`BodyStepH` at all, whatever its proof looks like.

`BodyStepHTo` takes the output layout as a parameter. `BodyStepH` is exactly its
`S' = S ++ outsOf x` instance — definitionally, so `bodyStepHTo_of_bodyStepH` is the identity and
every existing producer lifts for free with nothing above it changing. -/

/-- Per-instruction step with an **explicit output layout** `S'`. -/
def BodyStepHTo (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Nat) (x : Instruction × Nat) (S S' : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + dem) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars S' (gp x p).2

/-- Every growing step is a `BodyStepHTo` at its own output layout — definitionally. -/
theorem bodyStepHTo_of_bodyStepH {lo offsetToPc prog gp dem x S}
    (h : BodyStepH lo offsetToPc prog gp dem x S) :
    BodyStepHTo lo offsetToPc prog gp dem x S (S ++ outsOf x) := h

/-- Readiness threading an explicit layout through the body: each step names the layout it hands to
    the next, so growing and consuming steps compose in one list. -/
def BodyStepsReadyHTo (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat) :
    List (Instruction × Nat) → List String → List String → Prop
  | [], S, S' => S' = S
  | x :: xs, S, S' => ∃ Smid, BodyStepHTo lo offsetToPc prog gp (dem x) x S Smid ∧
                              BodyStepsReadyHTo lo offsetToPc prog gp dem xs Smid S'

/-- An all-growing body is ready at the layout the old fold computes, so every existing
    `BodyStepsReadyH` feeds the generalised fold unchanged. -/
theorem bodyStepsReadyHTo_of_bodyStepsReadyH {lo offsetToPc prog gp dem} :
    ∀ (l : List (Instruction × Nat)) (S : List String),
      BodyStepsReadyH lo offsetToPc prog gp dem l S →
      BodyStepsReadyHTo lo offsetToPc prog gp dem l S (S ++ l.flatMap outsOf) := by
  intro l
  induction l with
  | nil => intro S _; show S ++ [] = S; simp
  | cons x xs ih =>
    intro S h
    obtain ⟨hhead, htail⟩ := h
    refine ⟨S ++ outsOf x, bodyStepHTo_of_bodyStepH hhead, ?_⟩
    have := ih (S ++ outsOf x) htail
    rwa [List.flatMap_cons, ← List.append_assoc]

/-- A single step is a one-element ready body. -/
theorem bodyStepsReadyHTo_singleton {lo offsetToPc prog gp dem x S S'}
    (h : BodyStepHTo lo offsetToPc prog gp (dem x) x S S') :
    BodyStepsReadyHTo lo offsetToPc prog gp dem [x] S S' :=
  ⟨S', h, rfl⟩

/-- Ready bodies compose at a shared intermediate layout — so a growing prefix and a consuming
    step live in ONE body. -/
theorem bodyStepsReadyHTo_append {lo offsetToPc prog gp dem} :
    ∀ (l1 l2 : List (Instruction × Nat)) (S0 Smid Sn : List String),
      BodyStepsReadyHTo lo offsetToPc prog gp dem l1 S0 Smid →
      BodyStepsReadyHTo lo offsetToPc prog gp dem l2 Smid Sn →
      BodyStepsReadyHTo lo offsetToPc prog gp dem (l1 ++ l2) S0 Sn := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 S0 Smid Sn h1 h2
    have : Smid = S0 := h1
    subst this; exact h2
  | cons x xs ih =>
    intro l2 S0 Smid Sn h1 h2
    obtain ⟨Sx, hhead, htail⟩ := h1
    exact ⟨Sx, hhead, ih l2 Sx Smid Sn htail h2⟩

/-- **Growing prefix, then one consuming step — the shape the fold could not express before.**
    Every existing (growing) producer supplies `front` via `BodyStepsReadyH`; the consuming step is
    appended at the layout the prefix reached. The result feeds `genBlockBodyHTo_sim_inv`. -/
theorem bodyStepsReadyHTo_growing_then_consuming {lo offsetToPc prog gp dem}
    {front : List (Instruction × Nat)} {x : Instruction × Nat} {S0 Sout : List String}
    (hfront : BodyStepsReadyH lo offsetToPc prog gp dem front S0)
    (hlast : BodyStepHTo lo offsetToPc prog gp (dem x) x (S0 ++ front.flatMap outsOf) Sout) :
    BodyStepsReadyHTo lo offsetToPc prog gp dem (front ++ [x]) S0 Sout :=
  bodyStepsReadyHTo_append front [x] S0 (S0 ++ front.flatMap outsOf) Sout
    (bodyStepsReadyHTo_of_bodyStepsReadyH front S0 hfront)
    (bodyStepsReadyHTo_singleton hlast)

/-- **The body fold, threading an explicit output layout.** The `BodyStepsReadyHTo` twin of
    `genBlockBodyH_sim_inv`: same induction, but the final `StackIsVars` is whatever the steps
    threaded rather than `S0 ++ flatMap outsOf` — so a body containing a consuming instruction is
    admissible. With `bodyStepsReadyHTo_of_bodyStepsReadyH` this subsumes the original. -/
theorem genBlockBodyHTo_sim_inv {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat)
    (l : List (Instruction × Nat)) :
    ∀ (S0 Sn : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyHTo lo offsetToPc prog gp dem l S0 Sn →
      StackDiscH (l.map dem).sum ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
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
             StackIsVars Sn
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 Sn ps0 vs0 as0 hready hsd0 hsv0 hrel0 _
    have hSn : Sn = S0 := hready
    subst hSn
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 Sn ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨Smid, hstepx, hready_xs⟩ := hready
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
    have hsd0' : StackDiscH ((xs.map dem).sum + dem x) ps0 vs0 := by
      have he : ((x :: xs).map dem).sum = (xs.map dem).sum + dem x := by
        rw [List.map_cons, List.sum_cons]; omega
      rwa [he] at hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ :=
      hstepx ps0 vs0 as0 (xs.map dem).sum hsd0' hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih Smid Sn (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', hsv'⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega

/-- **`BodyStepHTo` for a commutative binop whose operands are both DEAD** — the first consuming
    producer, and the reason `BodyStepHTo` exists: its output layout `base ++ [out]` is SHORTER than
    its input `base ++ [y, x]`, so no `BodyStepH` can state it.

    Verified against the generator at exactly this configuration: with `a`,`b` dead and the stack
    `[%c, %b, %a]`, `generateRegularInstPlan` returns `(["ADD"], [%c, %d])` — a bare `ADD` that
    shrinks the stack, which is precisely what this producer claims. -/
theorem bodyStepHTo_commBinopDead
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {base : List String} {x y out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (houtS : out ∉ base ++ [y, x])
    (hlive : nextLiveness.contains out = true)
    (hdead_x : nextLiveness.contains x = false)
    (hdead_y : nextLiveness.contains y = false)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s) :
    BodyStepHTo lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      1 (inst, idx) (base ++ [y, x]) (base ++ [out]) := by
  intro p v s j hsd hsv hrel hblock
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := base.map Operand.Var ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := base.map Operand.Var ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  exact stackDisc_commBinopDead_step_S (idx := idx) hsd hsv hname hcomm (hdispatch v) hops houts
    hxy houtS hlive hdead_x hdead_y hdisp hopt hrel hblock

/-- **`BodyStepHTo` for a dead commutative binop in the MIRROR order** (`base ++ [x, y]`) — the
    config the generator emits bare, so THIS is the producer a consuming whole-function capstone
    feeds. `hfcomm` is commutativity of `f` as a function (the asm computes `f wy wx`, Venom
    `f wx wy`). The output layout `base ++ [out]` is again shorter than the input `base ++ [x, y]`. -/
theorem bodyStepHTo_commBinopDeadMirror
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {base : List String} {x y out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (houtS : out ∉ base ++ [x, y])
    (hlive : nextLiveness.contains out = true)
    (hdead_x : nextLiveness.contains x = false)
    (hdead_y : nextLiveness.contains y = false)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s) :
    BodyStepHTo lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      1 (inst, idx) (base ++ [x, y]) (base ++ [out]) := by
  intro p v s j hsd hsv hrel hblock
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := base.map Operand.Var ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := base.map Operand.Var ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  exact stackDisc_commBinopDeadMirror_step_S (idx := idx) hsd hsv hname hcomm hfcomm (hdispatch v)
    hops houts hxy houtS hlive hdead_x hdead_y hdisp hopt hrel hblock

/-! ### `BodyStepG` producer for SSTORE (the first 0-output producer)

Exercises the general fold: SSTORE has no output, so `outsOf = []` — the headroom delta is 0 and the
stack is unchanged. Built on `genRegularInstPlan_sstore_eq`/`_sim`, with the general `gvBodyStep_of_ok`
bridge (the venom step is `sstore wx wy`, not an `updateVar`). -/

/-- `{(emitInputPlan (reverse=[Var y,Var x]) nl ps).2 with stack := base} = {ps with stack := base}`. -/
private theorem sstore_state_eq {inst : Instruction} {nextLiveness : List String} {ps : PlanState}
    {x y : String} {base : List Operand} {d_y d_x' : Nat}
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) :
    ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']

/-- Output stack of an SSTORE: `ps.stack` (unchanged — no output). -/
theorem genRegularInstPlan_sstore_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y : String} {base : List Operand} {name : String} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [releaseDeadSpills_stack]
  show base = ps.stack
  exact hstack0.symm

/-- Headroom preservation for an SSTORE: `StackDiscH j` unchanged (no output, stack back to `base`). -/
theorem stackDisc_sstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for SSTORE: derives the two input depths from `StackIsVars S`,
    runs the sim (`gvBodyStep_of_ok`), and threads the (unchanged) headroom / stack. The no-output
    (delta-0) analog of `stackDisc_nonCommBinopVar_step_S`. -/
theorem stackDisc_sstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_sim hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
    hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hvx hvy hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_sstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`StackDiscHS` preservation across a value-spilled store.** The spill-aware analogue of
    `stackDisc_sstore_preserve` for the config where the *value* operand `y` is spilled (the key `x`
    live). Emit restores+DUPs `y` and DUPs `x` (`base ++ [y, y, x]`), the store consumes key+value,
    leaving the kept restored value (`base ++ [y]`, net +1), and the freed slot settles; dead spills
    are released — re-establishing `StackDiscHS` at headroom `k` (from `k+1`). `sstore` never touches
    the var map, so `defined` reduces to `lookupVar _ vs`. -/
theorem stackDiscHS_store_valspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y name : String} {idx k offy d_x : Nat} {base : List Operand} {wx wy : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 2 ≤ 15)
    (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_sstore_spilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hspill_y
      hlivey hnospill_x hlivex hdepth_x hsmall_x]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_valspilled hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x]
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off' hlook
  · show (base ++ [Operand.Var y]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    change Operand.Var z ∈ base ++ [Operand.Var y] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · exact hsd.defined z (by rw [hstack0]; exact h)
    · injection h with h'; rw [h']; exact hdef_y

/-- **Spill-aware body step for a value-spilled store.** The reroute of `stackDisc_sstore_step_S` off
    `StackDiscH.noSpill` for the value-spilled config: `StackDiscHS (k+1)` drives the restore+dup of
    the spilled value `y` and the DUP of the live key `x`, the store, and the invariant
    re-establishment — bundling `StackDiscHS k` inside the existential. Composes
    `genRegularInstPlan_sstore_spilled_sim` with `stackDiscHS_store_valspilled_preserve`. The
    0-output store analogue of `stackDiscHS_tload_spilled_step_S`. -/
theorem stackDiscHS_sstore_valspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {base : List Operand} {offy idx k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
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
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_x : d_x + 2 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_spilled_sim hname hncomm hnjmp hcompute hops houts hxy hstack0
    hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x hvx hvy hsd.spillWf hdisp hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_store_valspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hstack0 hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x ⟨wy, hwy⟩ hstepEq

/-- **`StackDiscHS` preservation across a key-spilled store.** The spill-aware analogue of
    `stackDisc_sstore_preserve` for the *non-positioned* config where the *key* operand `x` is spilled
    (the value `y` live). Emit DUPs `y` and restores+DUPs `x` (`base ++ [y, x, x]`), the reorder swaps
    the deep value into place (`base ++ [x, y, x]`), the store consumes value+key leaving the kept
    restored key (`base ++ [x]`, net +1), the freed slot settles, dead spills released —
    re-establishing `StackDiscHS` at headroom `k` (from `k+1`). -/
theorem stackDiscHS_store_keyspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y name : String} {idx k offx d_y : Nat} {base : List Operand} {wx wy : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdef_x : ∃ w, lookupVar x vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_sstore_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_keyspilled hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var x) o off' hlook
  · show (base ++ [Operand.Var x]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    change Operand.Var z ∈ base ++ [Operand.Var x] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · exact hsd.defined z (by rw [hstack0]; exact h)
    · injection h with h'; rw [h']; exact hdef_x

/-- **Spill-aware body step for a key-spilled store.** The reroute of `stackDisc_sstore_step_S` off
    `StackDiscH.noSpill` for the *non-positioned* key-spilled config: `StackDiscHS (k+1)` drives the
    DUP of the live value `y`, the restore+dup of the spilled key `x`, the `SWAP2 ; SWAP1` reorder, the
    store, and the invariant re-establishment — bundling `StackDiscHS k` inside the existential.
    Composes `genRegularInstPlan_sstore_keyspilled_sim` with `stackDiscHS_store_keyspilled_preserve`.
    The first StackDiscHS body producer whose plan carries a genuine (non-empty) reorder. -/
theorem stackDiscHS_sstore_keyspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {base : List Operand} {offx idx k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hymem : Operand.Var y ∈ ps.stack)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
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
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_keyspilled_sim hname hncomm hnjmp hcompute hops houts hxy
    hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex hvx hvy hsd.spillWf hdisp hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_store_keyspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex ⟨wx, hwx⟩ hstepEq

/-- **`StackDiscHS` preservation across a both-spilled store.** The spill-aware analogue of
    `stackDisc_sstore_preserve` for the config where *both* operands are spilled. Emit restores+DUPs
    each (`base ++ [y, y, x, x]`), the `SWAP2 ; SWAP1` reorder gives `base ++ [y, x, y, x]`, the store
    consumes value+key leaving the two kept restored operands (`base ++ [y, x]`, net +2), both slots
    settle, dead spills released — re-establishing `StackDiscHS` at headroom `k` (from `k+2`). -/
theorem stackDiscHS_store_bothspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y name : String} {idx k offx offy : Nat} {base : List Operand} {wx wy : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdef_x : ∃ w, lookupVar x vs = some w) (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_sstore_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hspill_y hlivey hspill_x hlivex]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_bothspilled hstack0 hspill_y hlivey hspill_x hlivex hxy]
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off'
          (aremove_lookup_some _ (Operand.Var x) o off' hlook)
  · show (base ++ [Operand.Var y, Operand.Var x]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    change Operand.Var z ∈ base ++ [Operand.Var y, Operand.Var x] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · exact hsd.defined z (by rw [hstack0]; exact h)
    · injection h with h'; rw [h']; exact hdef_y
    · injection h with h'; rw [h']; exact hdef_x

/-- **Spill-aware body step for a both-spilled store.** The reroute of `stackDisc_sstore_step_S` off
    `StackDiscH.noSpill` for the both-spilled config: `StackDiscHS (k+2)` drives the restore+dup of
    both operands, the `SWAP2 ; SWAP1` reorder, the store, and the invariant re-establishment —
    bundling `StackDiscHS k` inside the existential. Composes
    `genRegularInstPlan_sstore_bothspilled_sim` with `stackDiscHS_store_bothspilled_preserve`. Both
    operands come off spill slots, so no live-stack membership hypothesis is needed. -/
theorem stackDiscHS_sstore_bothspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {base : List Operand} {offx offy idx k : Nat}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
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
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_bothspilled_sim hname hncomm hnjmp hcompute hops houts hxy
    hstack0 hspill_y hlivey hspill_x hlivex hvx hvy hsd.spillWf hdisp hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_store_bothspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hstack0 hspill_y hlivey hspill_x hlivex ⟨wx, hwx⟩ ⟨wy, hwy⟩ hstepEq

/-- **`StackDiscHS` preservation across a value-spilled non-commutative binop.** The 1-output analogue
    of `stackDiscHS_store_valspilled_preserve` / `stackDiscHS_read1_spilled_preserve`: value `y`
    spilled, key `x` live. Emit restores+DUPs `y` and DUPs `x` (`base ++ [y, y, x]`), the op consumes
    both operands and pushes `out`, leaving the kept restored value and the output
    (`base ++ [y, out]`, net +2), the freed slot settles, dead spills released — re-establishing
    `StackDiscHS` at headroom `k` (from `k+2`). -/
theorem stackDiscHS_binop_valspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offy d_x : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 2 ≤ 15)
    (hfresh : ¬ Operand.Var out ∈ base) (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_nonCommBinopVar_spilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_valspilled hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off' hlook
  · show (base ++ [Operand.Var y, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var y, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_y
      refine ⟨ww, ?_⟩
      rw [h', lookupVar_updateVar_ne vs out y val (Ne.symm hoy)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a value-spilled non-commutative binop.** The reroute of
    `stackDisc_nonCommBinopVar_step_S` off `StackDiscH.noSpill`: `StackDiscHS (k+2)` drives the
    restore+dup of the spilled value `y`, the DUP of the live key `x`, the binop, and the invariant
    re-establishment — bundling `StackDiscHS k` inside the existential. Composes
    `genRegularInstPlan_nonCommBinopVar_spilled_sim` with `stackDiscHS_binop_valspilled_preserve`. The
    2-in-1-out analogue of the value-spilled store reroute. -/
theorem stackDiscHS_nonCommBinop_valspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offy idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
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
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_x : d_x + 2 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_nonCommBinopVar_spilled_sim hname hncomm hnjmp hcompute hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x
    hvx hvy hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_binop_valspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hoy hstack0 hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x hfresh
    ⟨wy, hwy⟩ hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a key-spilled non-commutative binop.** Key `x` spilled, value
    `y` live. Emit DUPs `y` and restores+DUPs `x` (`base ++ [y, x, x]`), the `SWAP2 ; SWAP1` reorder
    gives `base ++ [x, y, x]`, the op consumes both operands and pushes `out`, leaving the kept restored
    key and the output (`base ++ [x, out]`, net +2), the freed slot settles, dead spills released —
    re-establishing `StackDiscHS` at headroom `k` (from `k+2`). -/
theorem stackDiscHS_binop_keyspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offx d_y : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hdef_x : ∃ w, lookupVar x vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_nonCommBinopVar_keyspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_keyspilled hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var x) o off' hlook
  · show (base ++ [Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var x, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_x
      refine ⟨ww, ?_⟩
      rw [h', lookupVar_updateVar_ne vs out x val (Ne.symm hox)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a key-spilled non-commutative binop.** The reroute of
    `stackDisc_nonCommBinopVar_step_S` off `StackDiscH.noSpill` for the *non-positioned* key-spilled
    config: `StackDiscHS (k+2)` drives the DUP of the live value `y`, the restore+dup of the spilled
    key `x`, the `SWAP2 ; SWAP1` reorder, the binop, and the invariant re-establishment. Composes
    `genRegularInstPlan_nonCommBinopVar_keyspilled_sim` with `stackDiscHS_binop_keyspilled_preserve` —
    the first StackDiscHS 2-in-1-out producer with a genuine reorder. -/
theorem stackDiscHS_nonCommBinop_keyspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offx idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
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
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_nonCommBinopVar_keyspilled_sim hname hncomm hnjmp hcompute hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex
    hvx hvy hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_binop_keyspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hox hstack0 hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex hfresh
    ⟨wx, hwx⟩ hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-spilled non-commutative binop.** Both operands spilled.
    Emit restores+DUPs each (`base ++ [y, y, x, x]`), the `SWAP2 ; SWAP1` reorder gives
    `base ++ [y, x, y, x]`, the op consumes both operands and pushes `out`, leaving both kept restored
    operands and the output (`base ++ [y, x, out]`, net +3 — the deepest binop reroute), both slots
    settle, dead spills released — re-establishing `StackDiscHS` at headroom `k` (from `k+3`). -/
theorem stackDiscHS_binop_bothspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offx offy : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hdef_x : ∃ w, lookupVar x vs = some w) (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_nonCommBinopVar_bothspilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hspill_y hlivey hspill_x hlivex, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_bothspilled hstack0 hspill_y hlivey hspill_x hlivex hxy]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off'
          (aremove_lookup_some _ (Operand.Var x) o off' hlook)
  · show (base ++ [Operand.Var y, Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var y, Operand.Var x, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_y
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out y val (Ne.symm hoy)]; exact hww
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_x
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out x val (Ne.symm hox)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a both-spilled non-commutative binop.** The reroute of
    `stackDisc_nonCommBinopVar_step_S` off `StackDiscH.noSpill` for the both-spilled config:
    `StackDiscHS (k+3)` drives the restore+dup of both operands, the `SWAP2 ; SWAP1` reorder, the
    binop, and the invariant re-establishment. Composes
    `genRegularInstPlan_nonCommBinopVar_bothspilled_sim` with `stackDiscHS_binop_bothspilled_preserve` —
    both operands come off slots, so no live-stack membership hypothesis is needed. -/
theorem stackDiscHS_nonCommBinop_bothspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offx offy idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }))
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
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_nonCommBinopVar_bothspilled_sim hname hncomm hnjmp hcompute hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hspill_y hlivey hspill_x hlivex hvx hvy hsd.spillWf hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_binop_bothspilled_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hox hoy hstack0 hlive hspill_y hlivey hspill_x hlivex hfresh ⟨wx, hwx⟩ ⟨wy, hwy⟩
    hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-operands-live store.** Neither operand spilled, but the
    state may carry *other* spills. Emit DUPs both operands (`base ++ [y, x]`), the store consumes them
    (net 0), the unrelated spills are untouched, dead spills released — `StackDiscHS k → k`. The
    spill-aware analogue of `stackDisc_sstore_preserve` that *preserves* rather than requires no-spill;
    the fourth store config needed for the universal `BodyStepHS` dispatcher. -/
theorem stackDiscHS_store_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y name : String} {idx k d_y d_x' : Nat} {base : List Operand} {wx wy : bytes32}
    (hsd : StackDiscHS k ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x') (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base } : PlanState) = { ps with stack := base } := by
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show base.length + k ≤ 15
    have := hsd.shallow; rw [hstack0] at this; exact this
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- **Spill-aware body step for a both-operands-live store.** The no-restore config of the SSTORE
    reroute: both operands on the stack (the state may carry unrelated spills). `StackDiscHS k` drives
    the two DUPs and the store, preserving the invariant at the same headroom (net 0). Composes
    `genRegularInstPlan_sstore_sim` with `stackDiscHS_store_bothlive_preserve`. -/
theorem stackDiscHS_sstore_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y : String} {base : List Operand} {idx k : Nat}
    (hsd : StackDiscHS k ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
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
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_sim hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
    hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hvx hvy hdisp hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_store_bothlive_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hstack0 hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq

/-- **`StackDiscHS` preservation across a value-spilled commutative binop.** As
    `stackDiscHS_binop_valspilled_preserve` but through the commutative branch (same plan/state):
    value `y` spilled, `x` live, net +2 (`base ++ [y, out]`), `StackDiscHS (k+2) → k`. -/
theorem stackDiscHS_commBinop_valspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offy d_x : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 2 ≤ 15)
    (hfresh : ¬ Operand.Var out ∈ base) (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_commBinopVar_valspilled_eq hname hcomm hops houts hxy hstack0
      hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_valspilled hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off' hlook
  · show (base ++ [Operand.Var y, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var y, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_y
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out y val (Ne.symm hoy)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a value-spilled commutative binop.** The reroute of
    `stackDisc_commBinopVar_step_S` off `StackDiscH.noSpill` for the value-spilled config. Composes
    `genRegularInstPlan_commBinopVar_valspilled_sim` with `stackDiscHS_commBinop_valspilled_preserve`. -/
theorem stackDiscHS_commBinop_valspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offy idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
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
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_x : d_x + 2 ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_commBinopVar_valspilled_sim hname hcomm hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x
    hvx hvy hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_commBinop_valspilled_preserve (idx := idx) hsd hmemmono hname hcomm
    hops houts hxy hoy hstack0 hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x hfresh
    ⟨wy, hwy⟩ hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-operands-live non-commutative binop.** Neither operand
    spilled, but the state may carry *other* spills. Emit DUPs both operands, the op consumes them and
    pushes `out` (net +1, `base ++ [out]`), the unrelated spills untouched, dead spills released —
    `StackDiscHS (k+1) → k`. Unlike the spilled configs (which restore operands back onto the stack,
    net +2/+3), this fits the fold's uniform fuel; the fourth binop config for the dispatcher. -/
theorem stackDiscHS_binop_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k d_y d_x' : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x') (hsmall_x' : d_x' ≤ 15)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hlive
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var out] } : PlanState) = { ps with stack := base ++ [Operand.Var out] } := by
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show (base ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **`StackDiscHS` preservation across a both-live COMMUTATIVE binop.** Commutative-branch twin of
    `stackDiscHS_binop_bothlive_preserve`: same final state `base ++ [out]`, so only the plan-eq
    (`genRegularInstPlan_commBinopVar_eq`) differs. -/
theorem stackDiscHS_commBinop_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k d_y d_x' : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x') (hsmall_x' : d_x' ≤ 15)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy hstack0 hlive
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var out] } : PlanState) = { ps with stack := base ++ [Operand.Var out] } := by
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show (base ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩


/-- **Spill-aware body step for a both-operands-live non-commutative binop.** Both operands on the
    stack (state may carry unrelated spills). `StackDiscHS (k+1)` drives the two DUPs, the binop, and
    the invariant re-establishment (net +1). Composes `genRegularInstPlan_nonCommBinopVar_sim` with
    `stackDiscHS_binop_bothlive_preserve`. The config that fits the uniform-fuel fold. -/
theorem stackDiscHS_nonCommBinop_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hox : out ≠ x := by rintro rfl; exact hfresh (hstack0 ▸ hxmem)
  have hoy : out ≠ y := by rintro rfl; exact hfresh (hstack0 ▸ hymem)
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_nonCommBinopVar_sim hname hncomm hnjmp hcompute hops houts hxy hox hoy
    hstack0 hlive hfresh hspill_out hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x'
    hsmall_x' hlenx' hvx hvy hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_binop_bothlive_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hstack0 hlive hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x'
    hsmall_x' hfresh hstepEq hoptnoop

/-- **Both-live COMMUTATIVE binop step** (ADD / MUL / AND / OR / XOR / EQ, both operands on the stack).
    The one cell of the spill matrix that was missing: all three commutative *spilled* cases existed, but
    not the both-live one — which is the single most common instruction shape. -/
theorem stackDiscHS_commBinop_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hox : out ≠ x := by rintro rfl; exact hfresh (hstack0 ▸ hxmem)
  have hoy : out ≠ y := by rintro rfl; exact hfresh (hstack0 ▸ hymem)
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_commBinopVar_sim hname hcomm hops houts hxy hox hoy
    hstack0 hlive hfresh hspill_out hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x'
    hsmall_x' hlenx' hvx hvy hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_commBinop_bothlive_preserve (idx := idx) hsd hmemmono hname hcomm
    hops houts hxy hstack0 hlive hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x'
    hsmall_x' hfresh hstepEq hoptnoop


/-- **`StackDiscHS` preservation across a key-spilled commutative binop.** As
    `stackDiscHS_binop_keyspilled_preserve` but through the commutative branch (same final state
    `base ++ [x, out]`): key `x` spilled, value `y` live, net +2, `StackDiscHS (k+2) → k`. -/
theorem stackDiscHS_commBinop_keyspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offx d_y : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hdef_x : ∃ w, lookupVar x vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_commBinopVar_keyspilled_eq hname hcomm hops houts hxy hstack0
      hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_keyspilled hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var x) o off' hlook
  · show (base ++ [Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var x, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_x
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out x val (Ne.symm hox)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a key-spilled commutative binop.** The commutative-binop key-spilled
    reroute: `StackDiscHS (k+2)` drives DUP `y`, restore `x`, the `SWAP1 ; SWAP2` (swapped-order) reorder,
    the binop, and the invariant re-establishment. Composes
    `genRegularInstPlan_commBinopVar_keyspilled_sim` (needs `hfcomm`) with
    `stackDiscHS_commBinop_keyspilled_preserve`. -/
theorem stackDiscHS_commBinop_keyspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offx idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
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
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_commBinopVar_keyspilled_sim hname hcomm hfcomm hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex
    hvx hvy hsd.spillWf hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_commBinop_keyspilled_preserve (idx := idx) hsd hmemmono hname hcomm
    hops houts hxy hox hstack0 hlive hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex hfresh
    ⟨wx, hwx⟩ hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-spilled commutative binop.** As
    `stackDiscHS_binop_bothspilled_preserve` but through the commutative branch (same final state
    `base ++ [y, x, out]`): both operands spilled, net +3, `StackDiscHS (k+3) → k`. -/
theorem stackDiscHS_commBinop_bothspilled_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y out name : String} {idx k offx offy : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hdef_x : ∃ w, lookupVar x vs = some w) (hdef_y : ∃ w, lookupVar y vs = some w)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_commBinopVar_bothspilled_eq hname hcomm hops houts hxy hstack0
      hlive hspill_y hlivey hspill_x hlivex, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emit2_bothspilled hstack0 hspill_y hlivey hspill_x hlivex hxy]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var y) o off'
          (aremove_lookup_some _ (Operand.Var x) o off' hlook)
  · show (base ++ [Operand.Var y, Operand.Var x, Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro z hz
    show ∃ w, lookupVar z { updateVar out val vs with instIdx := idx + 1 } = some w
    have hlk : lookupVar z { updateVar out val vs with instIdx := idx + 1 }
        = lookupVar z (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var z ∈ base ++ [Operand.Var y, Operand.Var x, Operand.Var out] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z val hzout]; exact hww⟩
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_y
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out y val (Ne.symm hoy)]; exact hww
    · injection h with h'
      obtain ⟨ww, hww⟩ := hdef_x
      refine ⟨ww, ?_⟩; rw [h', lookupVar_updateVar_ne vs out x val (Ne.symm hox)]; exact hww
    · injection h with h'
      exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a both-spilled commutative binop.** Completes the commutative binop
    spill matrix. `StackDiscHS (k+3)` drives the two restores, the `SWAP1 ; SWAP2` (swapped-order)
    reorder, the binop, and the invariant re-establishment. Composes
    `genRegularInstPlan_commBinopVar_bothspilled_sim` (needs `hfcomm`) with
    `stackDiscHS_commBinop_bothspilled_preserve`. -/
theorem stackDiscHS_commBinop_bothspilled_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out name : String} {base : List Operand} {offx offy idx k : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y) (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nextLiveness.contains y = true)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var out] }))
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
  obtain ⟨wx, hwx⟩ := venomAsmRel_spilled_defined hrel hspill_x
  obtain ⟨wy, hwy⟩ := venomAsmRel_spilled_defined hrel hspill_y
  have hvx : operandVal vs lo (Operand.Var x) = some wx := by rw [operandVal_var_eq_lookupVar]; exact hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := by rw [operandVal_var_eq_lookupVar]; exact hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hsim := genRegularInstPlan_commBinopVar_bothspilled_sim hname hcomm hfcomm hops houts
    hxy hox hoy hstack0 hlive hfresh hspill_out hspill_y hlivey hspill_x hlivex hvx hvy hsd.spillWf hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_commBinop_bothspilled_preserve (idx := idx) hsd hmemmono hname hcomm
    hops houts hxy hox hoy hstack0 hlive hspill_y hlivey hspill_x hlivex hfresh ⟨wx, hwx⟩ ⟨wy, hwy⟩
    hstepEq hoptnoop

/-- Shallow-only ternop DUP-depth chain: `stackDisc_ternopVar_depths` needs only the headroom bound
    (`length ≤ 14`), not `noSpill` — so it applies under `StackDiscHS` too (the state may carry
    unrelated spills). -/
theorem ternopVar_depths_of_shallow {ps : PlanState} {x y z : String}
    (hshallow : ps.stack.length ≤ 14)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hzmem : Operand.Var z ∈ ps.stack) :
    ∃ d_z d_y d_x,
      stackGetDepth (Operand.Var z) ps.stack = some d_z ∧ d_z ≤ 15 ∧ d_z < ps.stack.length ∧
      stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some (d_y + 1) ∧ d_y + 1 ≤ 15 ∧
        d_y + 1 < (stackDup d_z ps.stack).length ∧
      stackGetDepth (Operand.Var x) (stackDup (d_y + 1) (stackDup d_z ps.stack)) = some (d_x + 2) ∧
        d_x + 2 ≤ 15 ∧ d_x + 2 < (stackDup (d_y + 1) (stackDup d_z ps.stack)).length := by
  obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hpeekZ : stackPeek d_z ps.stack = Operand.Var z := stackGetDepth_peek hdepth_z
  have hdupZ : stackDup d_z ps.stack = ps.stack ++ [Operand.Var z] := by unfold stackDup; rw [hpeekZ]
  have hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some (d_y + 1) := by
    rw [hdupZ, stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
  have hsy : stackDup (d_y + 1) (stackDup d_z ps.stack) = ps.stack ++ [Operand.Var z, Operand.Var y] := by
    rw [hdupZ]
    have hpy : stackPeek (d_y + 1) (ps.stack ++ [Operand.Var z]) = Operand.Var y := by
      rw [← hdupZ]; exact stackGetDepth_peek hdepth_y'
    unfold stackDup; rw [hpy]; simp
  have hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup (d_y + 1) (stackDup d_z ps.stack)) = some (d_x + 2) := by
    rw [hsy, show ps.stack ++ [Operand.Var z, Operand.Var y]
          = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxy,
        stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  refine ⟨d_z, d_y, d_x, hdepth_z, by omega, hlenz, hdepth_y', by omega, ?_, hdepth_x'', by omega, ?_⟩
  · rw [hdupZ]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [hsy]; simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **`StackDiscHS` preservation across a both-operands-live ternop.** All three operands on the stack
    (state may carry unrelated spills). Emit DUPs all three, the op consumes them and pushes `out`
    (net +1, `base ++ [out]`), unrelated spills untouched, dead spills released — `StackDiscHS (k+1) → k`.
    The ternop analogue of `stackDiscHS_binop_bothlive_preserve`. -/
theorem stackDiscHS_ternop_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x y z out name : String} {idx k d_z d_y' d_x'' : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none) (hlivez : nextLiveness.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z) (hsmall_z : d_z ≤ 15)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y') (hsmall_y : d_y' ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_x : d_x'' ≤ 15)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz hstack0 hlive
      hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y hnospill_x hlivex
      hdepth_x'' hsmall_x, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var out] } : PlanState) = { ps with stack := base ++ [Operand.Var out] } := by
    rw [hrev, emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey
      hdepth_y' hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show (base ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro w hw
    show ∃ ww, lookupVar w { updateVar out val vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar w { updateVar out val vs with instIdx := idx + 1 } = lookupVar w (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var w ∈ base ++ [Operand.Var out] at hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · have hwout : w ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined w (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out w val hwout]; exact hww⟩
    · injection h with h'; exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a both-operands-live ternop** (ADDMOD/MULMOD). All three operands on
    the stack (state may carry unrelated spills). `StackDiscHS (k+1)` drives the three DUPs, the ternop,
    and the invariant re-establishment (net +1). Composes `genRegularInstPlan_ternopVar_sim` with
    `stackDiscHS_ternop_bothlive_preserve`; the 3-in-1-out config that fits the uniform-fuel fold. -/
theorem stackDiscHS_ternopVar_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y z out name : String} {base : List Operand} {idx k : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack) (hzmem : Operand.Var z ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none) (hlivez : nextLiveness.contains z = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  have hshallow : ps.stack.length ≤ 14 := by have := hsd.shallow; omega
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'', hsmall_x, hlenx''⟩ :=
    ternopVar_depths_of_shallow hshallow hxy hyz hxz hxmem hymem hzmem
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wz, hwz⟩ := hsd.defined z hzmem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hvz : operandVal vs lo (Operand.Var z) = some wz := hwz
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) :=
    stepInstBase_3opVar hdispatch hops houts hwx hwy hwz
  have hsim := genRegularInstPlan_ternopVar_sim hname hncomm hnjmp hcompute hops houts hxy hyz hxz
    hox hoy hoz hstack0 hlive hfresh hspill_out hnospill_z hlivez hdepth_z hsmall_z hlenz hnospill_y
    hlivey hdepth_y' hsmall_y hleny' hnospill_x hlivex hdepth_x'' hsmall_x hlenx'' hvx hvy hvz hdisp
    hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_ternop_bothlive_preserve (idx := idx) hsd hmemmono hname hncomm hnjmp hcompute
    hops houts hxy hyz hxz hstack0 hlive hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y
    hnospill_x hlivex hdepth_x'' hsmall_x hfresh hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-operands-live 1-input read.** The operand `x` is on the
    stack (state may carry unrelated spills). Emit DUPs `x`, the read consumes it and pushes `out`
    (net +1, `base ++ [out]`), unrelated spills untouched, dead spills released — `StackDiscHS (k+1) → k`.
    The 1-in-1-out read analogue of `stackDiscHS_binop_bothlive_preserve`. -/
theorem stackDiscHS_read1_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {x out name : String} {idx k dist : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist) (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base ++ [Operand.Var out] } : PlanState) = { ps with stack := base ++ [Operand.Var out] } := by
    rw [hrev, emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show (base ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro w hw
    show ∃ ww, lookupVar w { updateVar out val vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar w { updateVar out val vs with instIdx := idx + 1 } = lookupVar w (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var w ∈ base ++ [Operand.Var out] at hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · have hwout : w ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined w (by rw [hstack0]; exact h)
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out w val hwout]; exact hww⟩
    · injection h with h'; exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a both-operands-live 1-input read.** The operand `x` on the stack, the
    state may carry unrelated spills. `StackDiscHS (k+1)` drives the DUP, the read (`asmUnop f`), and the
    invariant re-establishment (net +1). Composes `genRegularInstPlan_unopVar_sim` (which only requires
    the operand unspilled) with `stackDiscHS_read1_bothlive_preserve`. Generic over the read `f`
    (`hstepF` gives its Venom step) — covers TLOAD / SLOAD / CALLDATALOAD / account-query reads. -/
theorem stackDiscHS_unopVar_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x out name : String} {base : List Operand} {idx k : Nat}
    {f : bytes32 → bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hstepF : ∀ ww, operandVal vs lo (Operand.Var x) = some ww →
        stepInstBase inst vs = ExecResult.OK (updateVar out (f ww) vs))
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hxbase : Operand.Var x ∈ base := by rw [← hstack0]; exact hxmem
  have hlen' : dist < base.length := by rw [← hstack0]; exact hlen
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) := hstepF w hval
  have hsim := genRegularInstPlan_unopVar_sim hname hnjmp hcompute hops houts hstack0 hlive hnospill
    hlivex hdepth hsmall hpeek hlen' hxbase hval hfresh hspill_out hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read1_bothlive_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts
    hstack0 hlive hnospill hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop

/-- **Both-live TLOAD step** — the state-read twin of `stackDiscHS_unopVar_bothlive_step_S` (which needs a
    PURE `f`/`asmUnop`, so it cannot cover a storage/transient read). State reads previously had only the
    SPILLED case at the spill-aware level. -/
theorem stackDiscHS_tload_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x out : String} {base : List Operand} {idx k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "TLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => tload key s) inst vs)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hxbase : Operand.Var x ∈ base := by rw [← hstack0]; exact hxmem
  have hlen' : dist < base.length := by rw [← hstack0]; exact hlen
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (tload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_tload_sim hname hnjmp hcompute hops houts hstack0 hlive hnospill
    hlivex hdepth hsmall hpeek hlen' hxbase hval hfresh hspill_out hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read1_bothlive_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts
    hstack0 hlive hnospill hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop


/-- **Both-live SLOAD step** — the state-read twin of `stackDiscHS_unopVar_bothlive_step_S` (which needs a
    PURE `f`/`asmUnop`, so it cannot cover a storage/transient read). State reads previously had only the
    SPILLED case at the spill-aware level. -/
theorem stackDiscHS_sload_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x out : String} {base : List Operand} {idx k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nextLiveness.contains x = true)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => sload key s) inst vs)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hxbase : Operand.Var x ∈ base := by rw [← hstack0]; exact hxmem
  have hlen' : dist < base.length := by rw [← hstack0]; exact hlen
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (sload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_sload_sim hname hnjmp hcompute hops houts hstack0 hlive hnospill
    hlivex hdepth hsmall hpeek hlen' hxbase hval hfresh hspill_out hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read1_bothlive_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts
    hstack0 hlive hnospill hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop


/-- **`StackDiscHS` preservation across a 0-input context-push read** (ADDRESS/CALLER/CODESIZE/…). No
    operands; the op pushes `out` (net +1, `base ++ [out]`); the state may carry unrelated spills, which
    are untouched, dead spills released — `StackDiscHS (k+1) → k`. -/
theorem stackDiscHS_read0_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {out name : String} {idx k : Nat} {base : List Operand} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = []) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive, hoptnoop]
  apply releaseDeadSpills_stackDiscHS
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro w hw
    show ∃ ww, lookupVar w { updateVar out val vs with instIdx := idx + 1 } = some ww
    have hlk : lookupVar w { updateVar out val vs with instIdx := idx + 1 } = lookupVar w (updateVar out val vs) := rfl
    rw [hlk]
    change Operand.Var w ∈ ps.stack ++ [Operand.Var out] at hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · have hwout : w ≠ out := by rintro rfl; exact hfresh (hstack0 ▸ h)
      obtain ⟨ww, hww⟩ := hsd.defined w h
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out w val hwout]; exact hww⟩
    · injection h with h'; exact ⟨val, by rw [h']; exact lookupVar_updateVar_self vs out val⟩

/-- **Spill-aware body step for a 0-input context-push read.** No operands, so nothing can be spilled
    on the input side; `StackDiscHS (k+1)` drives the push and re-establishes the invariant (net +1),
    the state's unrelated spills preserved. Composes `genRegularInstPlan_read0_sim` with
    `stackDiscHS_read0_preserve`. Generic over the pushed value `v` (`hstepEq` gives its Venom step) —
    covers ADDRESS/CALLER/CALLVALUE/CODESIZE/GAS/… and SELFBALANCE. -/
theorem stackDiscHS_read0_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {out name : String} {base : List Operand} {idx k : Nat} {val : bytes32}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = []) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ base) (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hdisp : ∀ (h : as.pc < prog.length),
        prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog as = asmPushVal val as)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] }))
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
  have hfresh' : ¬ Operand.Var out ∈ ps.stack := by rw [hstack0]; exact hfresh
  have hsim := genRegularInstPlan_read0_sim hname hnjmp hcompute hops houts hlive hfresh' hspill_out
    hdisp hoptnoop hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_updateVar (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_read0_preserve (idx := idx) hsd hmemmono hname hnjmp hcompute hops houts hstack0
    hlive hfresh hstepEq hoptnoop

/-- **`StackDiscHS` preservation across a both-operands-live 3-input copy** (CALLDATACOPY/…). Three
    operands on the stack; the op consumes them and writes memory (no output, net 0). The state may
    carry unrelated spills — untouched (the write region is below `fnEom`, the spill slots above it via
    `hspillReg`), memory only grows, dead spills released — `StackDiscHS (k+1) → k`. The 3-in-0-out
    analogue of `stackDiscHS_store_bothlive_preserve`. -/
theorem stackDiscHS_copy_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs vs' : VenomState} {as as' : AsmState}
    {a b c name : String} {idx k d_z d_y' d_x'' : Nat} {base : List Operand}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hstepEq : stepInstBase inst vs = ExecResult.OK vs')
    (hvareq : ∀ w, lookupVar w vs' = lookupVar w vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z) (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y') (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_a : d_x'' ≤ 15) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0
      hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea
      hdepth_a hsmall_a]
  apply releaseDeadSpills_stackDiscHS
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := base } : PlanState) = { ps with stack := base } := by
    rw [hrev, emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb
      hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { vs' with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show base.length + k ≤ 15
    have := hsd.shallow; rw [hstack0] at this; omega
  · intro w hw
    show ∃ ww, lookupVar w { vs' with instIdx := idx + 1 } = some ww
    have hlk : lookupVar w { vs' with instIdx := idx + 1 } = lookupVar w vs' := rfl
    rw [hlk, hvareq w]
    exact hsd.defined w (by rw [hstack0]; exact hw)

/-- **Spill-aware body step for a both-operands-live CALLDATACOPY.** All three operands on the stack
    (state may carry unrelated spills, `hspillReg` keeping their slots above the copy region).
    `StackDiscHS (k+1)` drives the three DUPs and the copy (net 0), the invariant re-established with
    the state's spills preserved. Composes `genRegularInstPlan_calldatacopy_sim` with
    `stackDiscHS_copy_bothlive_preserve`. -/
theorem stackDiscHS_calldatacopy_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {a b c : String} {base : List Operand} {idx k : Nat}
    (hsd : StackDiscHS (k + 1) ps vs as)
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hamem : Operand.Var a ∈ ps.stack) (hbmem : Operand.Var b ∈ ps.stack) (hcmem : Operand.Var c ∈ ps.stack)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hstepEqF : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK
          (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, operandVal vs lo (Operand.Var a) = some wa → operandVal vs lo (Operand.Var c) = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
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
  have hshallow : ps.stack.length ≤ 14 := by have := hsd.shallow; omega
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    ternopVar_depths_of_shallow (x := a) (y := b) (z := c) hshallow hab hbc hac hamem hbmem hcmem
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hva hvc
  have hstepEq : stepInstBase inst vs = ExecResult.OK
      (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqF wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_calldatacopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops houts hab hbc hac
    hstack0 hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb
    hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_copy_bothlive_preserve (idx := idx) hsd hmemmono hstepEq (fun w => rfl) hname hncomm hnjmp
    hcompute hops houts hab hbc hac hstack0 hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb
    hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a

/-- **`StackDiscHS` preservation across a both-operands-live LOG** (variable arity). The emit DUPs all
    `es` operands, LOG consumes them and appends an event (no output, net 0); the state's unrelated
    spills are untouched, memory only grows, dead spills released — `StackDiscHS k → k`. The N-ary
    analogue of `stackDiscHS_copy_bothlive_preserve` (LOG touches only `logs`, not the var env). -/
theorem stackDiscHS_log_bothlive_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {as as' : AsmState}
    {es : List String} {dists : List Nat} {tc : bytes32} {k idx : Nat} {L : List Event}
    (hsd : StackDiscHS k ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscHS k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' := by
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths]
  apply releaseDeadSpills_stackDiscHS
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
        stack := ps.stack } : PlanState) = { ps with stack := ps.stack } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness es dists ps hnospill hdepths]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · exact fun _ _ h => h
  · show ps.stack.length + k ≤ 15
    exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z hz

/-- **Spill-aware body step for a both-operands-live LOG** (variable arity, demand `n` = topic
    count). All `n + 2` operands on the stack (state may carry unrelated spills); the emit-depth
    chain derives from `.shallow` alone (`emitDepthsOk_of_bounds`). `StackDiscHS (k + n)` covers the
    peak DUP reach and is re-established at `k` (net 0). Composes `genRegularInstPlan_log_sim` with
    `stackDiscHS_log_bothlive_preserve`. -/
theorem stackDiscHS_log_bothlive_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {es : List String} {tc : bytes32} {n k idx : Nat}
    {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscHS (k + n) ps vs as)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hmemes : ∀ v ∈ es, Operand.Var v ∈ ps.stack)
    (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : (es.map Operand.Var).reverse.map (fun o => operandVal vs lo o) = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
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
  have hbound : ps.stack.length + es.length ≤ 17 := by
    have := hsd.shallow; omega
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds es ps.stack hbound hnd hmemes hlive
  have hsim := genRegularInstPlan_log_sim (offsetToPc := offsetToPc) hopc hhead hcompute houts rfl hnd
    hnospill hdepths hlenes htc htlen hvals hcov hbelow hsize hn hrel hblock
  refine bodyStepS_of_sim (gvBodyStep_of_ok (idx := idx) hstepEq hsim) (fun as' hmemmono => ?_)
  exact stackDiscHS_log_bothlive_preserve (idx := idx) (hsd.mono (by omega)) hmemmono hopc hhead
    hcompute houts hnd hnospill hdepths hstepEq

/-- **`BodyStepG` for SSTORE** — the first *0-output* body-fold producer. Exercises the general fold:
    with `outsOf (inst,idx) = []` the headroom delta is 0 (`StackDiscH j → StackDiscH j`) and the
    stack is unchanged (`S ++ [] = S`). Stores now chain via `bodyStepsReadyG_cons`. -/
theorem bodyStepG_sstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun key val s => sstore key val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_sstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for TSTORE (transient-store twin of SSTORE)

The transient-storage twin of the SSTORE producer — `tstore` preserves `vars` just like `sstore`, so
the headroom / stack reasoning is identical; only the emit sim (`genRegularInstPlan_tstore_sim`) and
venom step (`tstore`) differ. Reuses the generic `genRegularInstPlan_sstore_eq`/`_outStack`. -/

theorem stackDisc_tstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (tstore wx wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { tstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for TSTORE (transient twin of `stackDisc_sstore_step_S`). -/
theorem stackDisc_tstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "TSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => tstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (tstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_tstore_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_tstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`BodyStepG` for TSTORE** — a 0-output producer (transient-store twin of `bodyStepG_sstore`). -/
theorem bodyStepG_tstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun key val s => tstore key val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_tstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for MSTORE (a 0-output *memory* store)

Unlike the shared-state stores, MSTORE's emit step is a memory write, so it carries a per-state
memory-safety precondition (`hmemsafe`: the write window is covered and below the spill region) — the
invariant the codegen guarantees but that lives outside `StackDiscH`. Everything else mirrors the
shared-state stores (`mstore` preserves `vars`; `hspillReg` is vacuous under `noSpill`). -/

theorem stackDisc_mstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (mstore wx.toNat wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { mstore wx.toNat wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for MSTORE: derives depths + the offset value, pulls the memory-
    safety facts from `hmemsafe`, discharges `hspillReg` vacuously from `noSpill`, runs the sim. -/
theorem stackDisc_mstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun addr val s => mstore addr.toNat val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ w, lookupVar x vs = some w →
        w.toNat ≤ vs.memory.size ∧ ((w.toNat + 32 + 31) / 32) * 32 ≤ as.memory.size ∧
        w.toNat + 32 ≤ ps.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  obtain ⟨hcovV, hcovA, hsafe⟩ := hmemsafe wx hwx
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (mstore wx.toNat wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_mstore_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hcovV hcovA hsafe hspillReg hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_mstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`BodyStepG` for MSTORE** — a 0-output producer for a *memory* store, carrying the per-state
    memory-safety precondition `hmemsafe` (write window covered + below the spill region), the
    invariant the codegen guarantees but that lives outside `StackDiscH`. -/
theorem bodyStepG_mstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore addr.toNat val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 32 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 32 ≤ p.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey (fun w hw => hmemsafe p v s w hrel hw) hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for MSTORE8 (single-byte memory store)

The single-byte twin of the MSTORE producer (`+1` write window instead of `+32`). Same shape;
only `emit_mstore8_sim`/`mstore8` and the `+1` memory-safety bound differ. -/

/-- Headroom preservation for an MSTORE8 (single-byte twin of `stackDisc_mstore_preserve`). -/
theorem stackDisc_mstore8_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 wx.toNat wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { mstore8 wx.toNat wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

theorem stackDisc_mstore8_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ w, lookupVar x vs = some w →
        w.toNat ≤ vs.memory.size ∧ ((w.toNat + 1 + 31) / 32) * 32 ≤ as.memory.size ∧
        w.toNat + 1 ≤ ps.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow hshallow hxmem hymem
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  obtain ⟨hcovV, hcovA, hsafe⟩ := hmemsafe wx hwx
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 wx.toNat wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_mstore8_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hcovV hcovA hsafe hspillReg hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_mstore8_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

theorem bodyStepG_mstore8
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 1 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 1 ≤ p.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mstore8_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey (fun w hw => hmemsafe p v s w hrel hw) hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepH` producer for CALLDATACOPY (the first 3-input 0-output producer)

Exercises the demand-decoupled fold at `dem = 1`: a 3-input 0-output op whose 3rd DUP reaches
`original_depth + 2` needs `StackDiscH 1` even though `outsOf = []`. The `dem = 1` input supplies it;
the (net-0) headroom is weakened `StackDiscH (j+1) → StackDiscH j` on the way out. -/

/-- Output stack of a copy: `ps.stack` (unchanged — no output). -/
theorem genRegularInstPlan_copy_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {a b c : String} {base : List Operand} {name : String} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z) (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y') (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_a : d_x'' ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  rw [releaseDeadSpills_stack]; show base = ps.stack; exact hstack0.symm

/-- Headroom preservation for a copy: `StackDiscH k` unchanged (no output; the memory write preserves vars). -/
theorem stackDisc_copy_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {a b c : String} {base : List Operand} {name : String}
    {idx k d_z d_y' d_x'' : Nat} {bytes : ByteArray} {wa : bytes32}
    (hsd : StackDiscH k ps vs)
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z) (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y') (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_a : d_x'' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat bytes vs)) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
    have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
    rw [hrev, emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { writeMemoryWithExpansion wa.toNat bytes vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + k ≤ 15; rw [← hstack0]; exact hsd.shallow
  · intro z' hz'; show ∃ w, lookupVar z' vs = some w; exact hsd.defined z' (by rw [hstack0]; exact hz')

/-- The `StackIsVars`-aware body step for CALLDATACOPY at demand 1: derives the 3 input depths from
    `StackDiscH 1`, pulls the memory-safety facts from `hmemsafe`, runs the sim, and weakens the
    (unchanged) headroom `StackDiscH (j+1) → StackDiscH j`. -/
theorem stackDisc_calldatacopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_calldatacopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := (⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for CALLDATACOPY at demand 1** — the first 3-input 0-output producer, exercising the
    demand-decoupled fold. Carries the CALLDATACOPY semantics (`hstepEqFn`) and per-state memory safety
    (`hmemsafe`) as hypotheses; `dem = 1` supplies the 3rd DUP's reach. -/
theorem bodyStepH_calldatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_calldatacopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for CODECOPY at demand 1 — the CODECOPY twin of
    `stackDisc_calldatacopy_step_S` (source `vs.code`, sim `genRegularInstPlan_codecopy_sim`). -/
theorem stackDisc_codecopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "CODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_codecopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := (⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for CODECOPY at demand 1** — the CODECOPY twin of `bodyStepH_calldatacopy`; a second
    3-input 0-output producer through the demand-decoupled fold, with source `code`. -/
theorem bodyStepH_codecopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_codecopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepH` producer for EXTCODECOPY (the first 4-input 0-output producer)

Exercises the demand-decoupled fold at `dem = 2`: a 4-input 0-output op whose 4th DUP reaches
`original_depth + 3` needs `StackDiscH 2` even though `outsOf = []`. The source of the copy is
`account.code` selected by the *addr* input (`a`); the dst/size safety is on inputs `b`/`d`. -/

/-- Output stack of a 4-input 0-output copy: `ps.stack` (unchanged). Quad twin of
    `genRegularInstPlan_copy_outStack`. -/
theorem genRegularInstPlan_copy4_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {a b c d : String} {base : List Operand} {name : String} {d_d d_c d_b d_a : Nat}
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hstack0 : ps.stack = base)
    (hnospill_d : alookup' ps.spilled (Operand.Var d) = none) (hlive_d : nextLiveness.contains d = true)
    (hdepth_d : stackGetDepth (Operand.Var d) ps.stack = some d_d) (hsmall_d : d_d ≤ 15)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlive_c : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) (stackDup d_d ps.stack) = some d_c) (hsmall_c : d_c ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hlive_b : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_c (stackDup d_d ps.stack)) = some d_b) (hsmall_b : d_b ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlive_a : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_b (stackDup d_c (stackDup d_d ps.stack))) = some d_a) (hsmall_a : d_a ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_noOutput4Var_ops_eq hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd
      hstack0 hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c hnospill_b hlive_b
      hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a]
  rw [releaseDeadSpills_stack]; show base = ps.stack; exact hstack0.symm

/-- Headroom preservation for a 4-input 0-output copy: `StackDiscH k` unchanged. Quad twin of
    `stackDisc_copy_preserve` (write offset `woff`, generic `bytes`). -/
theorem stackDisc_copy4_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {a b c d : String} {base : List Operand} {name : String}
    {idx k d_d d_c d_b d_a : Nat} {bytes : ByteArray} {woff : bytes32}
    (hsd : StackDiscH k ps vs)
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hstack0 : ps.stack = base)
    (hnospill_d : alookup' ps.spilled (Operand.Var d) = none) (hlive_d : nextLiveness.contains d = true)
    (hdepth_d : stackGetDepth (Operand.Var d) ps.stack = some d_d) (hsmall_d : d_d ≤ 15)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlive_c : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) (stackDup d_d ps.stack) = some d_c) (hsmall_c : d_c ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hlive_b : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_c (stackDup d_d ps.stack)) = some d_b) (hsmall_b : d_b ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlive_a : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_b (stackDup d_c (stackDup d_d ps.stack))) = some d_a) (hsmall_a : d_a ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion woff.toNat bytes vs)) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_noOutput4Var_ops_eq hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd
      hstack0 hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c hnospill_b hlive_b
      hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
    have hrev : inst.operands.reverse = [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
    rw [hrev, emitInputPlan_quad_var_eq hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c
        hnospill_b hlive_b hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { writeMemoryWithExpansion woff.toNat bytes vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + k ≤ 15; rw [← hstack0]; exact hsd.shallow
  · intro z' hz'; show ∃ w, lookupVar z' vs = some w; exact hsd.defined z' (by rw [hstack0]; exact hz')

/-- The `StackIsVars`-aware body step for EXTCODECOPY at demand 2 — the 4-input twin of
    `stackDisc_codecopy_step_S` (source `account.code` selected by input `a`, sim
    `genRegularInstPlan_extcodecopy_sim`). Needs `StackDiscH (j + 2)` for the 4th DUP's `+3` reach. -/
theorem stackDisc_extcodecopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c d : String} {j idx : Nat}
    (hsd : StackDiscH (j + 2) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "EXTCODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true)
    (hlivec : nextLiveness.contains c = true) (hlived : nextLiveness.contains d = true)
    (hstepEqFn : ∀ wa wb wc wd, lookupVar a vs = some wa → lookupVar b vs = some wb →
        lookupVar c vs = some wc → lookupVar d vs = some wd →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wb.toNat
          ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs))
    (hmemsafe : ∀ wb wd, lookupVar b vs = some wb → lookupVar d vs = some wd →
        wb.toNat ≤ vs.memory.size ∧ ((wb.toNat + wd.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wb.toNat + wd.toNat ≤ ps.alloc.fnEom ∧ 0 < wd.toNat ∧ wd.toNat < USize.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd2 : StackDiscH 2 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  have hdmem : Operand.Var d ∈ ps.stack := stackIsVars_mem hsv hdS
  obtain ⟨d_d, d_c, d_b, d_a, hdepth_d, hsmall_d, hlend, hdepth_c, hsmall_c, hlenc,
      hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_quadVar_depths (a := a) (b := b) (c := c) (d := d) hsd2 hab hac had hbc hbd hcd hamem hbmem hcmem hdmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  have hnospill_d : alookup' ps.spilled (Operand.Var d) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  obtain ⟨wd, hwd⟩ := hsd.defined d hdmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  have hvd : operandVal vs lo (Operand.Var d) = some wd := hwd
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wb wd hwb hwd
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wb.toNat
      ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs) :=
    hstepEqFn wa wb wc wd hwa hwb hwc hwd
  have hsim := genRegularInstPlan_extcodecopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hac had hbc hbd hcd rfl hnospill_d hlived hdepth_d hsmall_d hlend hnospill_c hlivec hdepth_c
    hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb hnospill_a hlivea hdepth_a hsmall_a hlena
    hva hvb hvc hvd hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy4_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel) (idx := idx)
      (bytes := (⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat)
      (woff := wb)
      hsd hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd rfl hnospill_d hlived hdepth_d hsmall_d
      hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy4_outStack hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd rfl
      hnospill_d hlived hdepth_d hsmall_d hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b
      hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for EXTCODECOPY at demand 2** — the first 4-input 0-output producer through the
    demand-decoupled fold. Carries the EXTCODECOPY semantics (`hstepEqFn`, source = `account.code`
    selected by the addr input) and per-state memory safety (`hmemsafe` on dst/size); `dem = 2`
    supplies the 4th DUP's reach. -/
theorem bodyStepH_extcodecopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c d : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "EXTCODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true)
    (hlivec : nextLiveness.contains c = true) (hlived : nextLiveness.contains d = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc wd, lookupVar a v = some wa → lookupVar b v = some wb →
        lookupVar c v = some wc → lookupVar d v = some wd →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wb.toNat
          ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) v.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wb wd, venomAsmRel lo p v s →
        lookupVar b v = some wb → lookupVar d v = some wd →
        wb.toNat ≤ v.memory.size ∧ ((wb.toNat + wd.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wb.toNat + wd.toNat ≤ p.alloc.fnEom ∧ 0 < wd.toNat ∧ wd.toNat < USize.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      2 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_extcodecopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hac had hbc hbd hcd haS hbS hcS hdS hlivea hliveb hlivec hlived
    (fun wa wb wc wd ha hb hc hd => hstepEqFn v wa wb wc wd ha hb hc hd)
    (fun wb wd hb hd => hmemsafe p v s wb wd hrel hb hd) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for RETURNDATACOPY at demand 1 — the twin of
    `stackDisc_codecopy_step_S`, with source `vs.returndata` and the extra OOB-safety `hnooobFn`
    (`srcOff + sz ≤ returndata.size`) threaded into the in-bounds sim. -/
theorem stackDisc_returndatacopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "RETURNDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.returndata.readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hnooobFn : ∀ wb wc, lookupVar b vs = some wb → lookupVar c vs = some wc → wb.toNat + wc.toNat ≤ vs.returndata.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hnooob : wb.toNat + wc.toNat ≤ vs.returndata.size := hnooobFn wb wc hwb hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.returndata.readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_returndatacopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hnooob hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := vs.returndata.readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for RETURNDATACOPY at demand 1** — the first copy-family producer with a fault
    branch. The demand-decoupled fold still applies on the in-bounds path: `hnooobFn` (per-state
    `srcOff + sz ≤ returndata.size`) selects the OK case, aligned with Venom (both fault OOB identically). -/
theorem bodyStepH_returndatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "RETURNDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.returndata.readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hnooobFn : ∀ (v : VenomState) wb wc, lookupVar b v = some wb → lookupVar c v = some wc → wb.toNat + wc.toNat ≤ v.returndata.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_returndatacopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc)
    (fun wb wc hb hc => hnooobFn v wb wc hb hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for MCOPY at demand 1 — the memory→memory copy. Twin of
    `stackDisc_returndatacopy_step_S`, but the source is `vs.memory` (bridged via `memoryRel`) and the
    extra facts are source-safety + source-coverage (`hsrcsafeFn`), threaded into the sim. -/
theorem stackDisc_mcopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MCOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.memory.readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsrcsafeFn : ∀ wb wc, lookupVar b vs = some wb → lookupVar c vs = some wc →
        wb.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  obtain ⟨hsrcsafe, hcovS⟩ := hsrcsafeFn wb wc hwb hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.memory.readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_mcopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hcovS hsafe hsrcsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := vs.memory.readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for MCOPY at demand 1** — the memory→memory copy producer, the last of the copy
    family. The demand-decoupled fold applies with the source read bridged through `memoryRel`
    (source-safety `srcOff + sz ≤ fnEom`) rather than an equality conjunct. -/
theorem bodyStepH_mcopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MCOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.memory.readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsrcsafeFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wb wc, venomAsmRel lo p v s → lookupVar b v = some wb → lookupVar c v = some wc →
        wb.toNat + wc.toNat ≤ p.alloc.fnEom ∧ ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mcopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc)
    (fun wb wc hb hc => hsrcsafeFn p v s wb wc hrel hb hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- LOG output stack = input stack (no outputs, dead-spill release doesn't touch stack). -/
theorem genRegularInstPlan_log_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {es : List String} {dists : List Nat} {tc : bytes32}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths, releaseDeadSpills_stack]

/-- LOG headroom preservation: `StackDiscH k` unchanged (no output; appending a log doesn't touch the
    var environment). LOG analog of `stackDisc_copy_preserve`. -/
theorem stackDisc_log_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {es : List String} {dists : List Nat} {tc : bytes32}
    {k idx : Nat} {L : List Event}
    (hsd : StackDiscH k ps vs)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with stack := ps.stack } : PlanState)
      = { ps with stack := ps.stack } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness es dists ps hnospill hdepths]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · exact hsd.shallow
  · intro z' hz'; show ∃ w, lookupVar z' vs = some w; exact hsd.defined z' hz'

/-- The `StackIsVars`-aware LOG body step at demand `n`: derives the emit-depth chain from
    `StackDiscH (j + n)` (`stackDisc_nVar_depths`), runs the sim, weakens the (unchanged) headroom
    `StackDiscH (j + n) → StackDiscH j`. -/
theorem stackDisc_log_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S es : List String} {tc : bytes32} {n j idx : Nat}
    {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscH (j + n) ps vs) (hsv : StackIsVars S ps)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S) (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : (es.map Operand.Var).reverse.map (fun o => operandVal vs lo o) = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hmemes : ∀ w ∈ es, Operand.Var w ∈ ps.stack := fun w hw => stackIsVars_mem hsv (hesS w hw)
  have hnospill : ∀ w ∈ es, alookup' ps.spilled (Operand.Var w) = none := fun w _ => hsd.noSpill _
  have hsdn : StackDiscH (es.length - 2) ps vs := by
    rw [hlenes]; exact StackDiscH.mono hsd (by omega)
  obtain ⟨dists, hdepths⟩ := stackDisc_nVar_depths es hsdn hnd hmemes hlive
  have hsim := genRegularInstPlan_log_sim (offsetToPc := offsetToPc) hopc hhead hcompute houts rfl hnd
    hnospill hdepths hlenes htc htlen hvals hcov hbelow hsize hn hrel hblock
  refine ⟨gvBodyStep_of_ok hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_log_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel) (idx := idx)
      hsd hopc hhead hcompute houts hnd hnospill hdepths hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_log_outStack hopc hhead hcompute houts hnd hnospill hdepths]
    exact hsv

/-- **`BodyStepH` for LOG at demand `n`** — the first variable-arity producer through the demand fold.
    The demand `n` (= topic count = `es.length - 2`) supplies the reach of the deepest input DUP. A
    per-state `hlogFn` provides the operand values, memory safety, and LOG semantics for each Venom
    state (the LOG analog of the copies' `hstepEqFn`/`hmemsafe`). -/
theorem bodyStepH_log
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S es : List String} {tc : bytes32} {n idx : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S) (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (hlogFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = (offset :: size :: topics).map some ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase inst v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      n (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hstepEq⟩ := hlogFn p v s hrel
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_log_step_S (idx := idx) hsd hsv hopc hhead hcompute houts
    hnd hesS hlive hlenes htc hn htlen hvals hcov hbelow hsize hstepEq hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### Mixed-arity demonstration (0- and 1-output ops in one body)

The payoff of the general fold: a 1-output binop (bridged via `bodyStepG_of_bodyStep`) and a 0-output
store chain via `bodyStepsReadyG_cons`, then fold through `genBlockBodyG_sim_inv` into a whole
2-instruction body sim — proving 0- and 1-output ops genuinely compose in one body. -/

/-- A commutative var-binop (1 output `o1`) then an SSTORE (0 outputs) chain via `bodyStepsReadyG_cons`:
    the binop ready at `S`, the store ready at `S ++ [o1]` (its `outsOf = []` keeps `S ++ [o1]`). -/
theorem bodyStepsReadyG_binop_store
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 n1 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "SSTORE") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execWrite2 (fun key val s => sstore key val s) i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1])
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s) :
    BodyStepsReadyG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      [(i1, idx1), (i2, idx2)] S := by
  have hstep1 : BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (i1, idx1) S :=
    bodyStepG_of_bodyStep houts1
      (bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
        (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
        (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1)
  have hstep2 : BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (i2, idx2) (S ++ [o1]) :=
    bodyStepG_sstore (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
      (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
      (nextIsTerminator := true) (curBbLabel := curBbLabel)
      hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S hlivex2 hlivey2 hdisp2
  have hout1 : outsOf (i1, idx1) = [o1] := by rw [outsOf, houts1]
  refine bodyStepsReadyG_cons hstep1 ?_
  rw [hout1]
  exact bodyStepsReadyG_cons hstep2 bodyStepsReadyG_nil

/-- **End-to-end mixed-arity body sim.** Feeds `bodyStepsReadyG_binop_store` through
    `genBlockBodyG_sim_inv`: a binop (1 output) then a store (0 outputs) run as one body, ending OK,
    still related, discipline at 0, stack now `S ++ [o1]` (the store added nothing). Headroom is 1 —
    `(l.flatMap outsOf).length = ([o1] ++ []).length`. The concrete demonstration that 0- and 1-output
    ops compose end-to-end in the general fold. -/
theorem genBlockBodyG_binop_store_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 n1 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "SSTORE") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execWrite2 (fun key val s => sstore key val s) i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1])
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hsd0 : StackDiscH (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).flatMap outsOf).length ps0 vs0)
    (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].flatMap outsOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyG_binop_store (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx1 := idx1) (idx2 := idx2) (curBbLabel := curBbLabel)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
    hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S hlivex2 hlivey2 hdisp2
  exact genBlockBodyG_sim_inv
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ### Demand-fold mixed-arity demonstration (1-output binop then a 3-input 0-output copy)

The demand-fold (`genBlockBodyH_sim_inv`) analog of `genBlockBodyG_binop_store_sim`. The store demo
runs through the output-count fold, which structurally cannot carry a copy (a 3-input 0-output op needs
more headroom than its output count grants). This threads a commutative binop (1 output) then a
CALLDATACOPY (3 inputs, 0 outputs) through the *demand* fold with `dem = fun _ => 1` — so the required
headroom is `Σ dem = 2`, one more than the output count `(l.flatMap outsOf).length = 1`. That extra
unit is exactly the reach the copy's deepest DUP needs and the output count does not pay for. -/
theorem bodyStepsReadyH_binop_calldatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 n1 a2 b2 c2 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "CALLDATACOPY") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hops2 : i2.operands = [Operand.Var a2, Operand.Var b2, Operand.Var c2]) (houts2 : i2.outputs = [])
    (hab2 : a2 ≠ b2) (hbc2 : b2 ≠ c2) (hac2 : a2 ≠ c2)
    (ha2S : a2 ∈ S ++ [o1]) (hb2S : b2 ∈ S ++ [o1]) (hc2S : c2 ∈ S ++ [o1])
    (hlivea2 : nextLiveness.contains a2 = true) (hliveb2 : nextLiveness.contains b2 = true) (hlivec2 : nextLiveness.contains c2 = true)
    (hstepEqFn2 : ∀ (v : VenomState) wa wb wc, lookupVar a2 v = some wa → lookupVar b2 v = some wb → lookupVar c2 v = some wc →
        stepInstBase i2 v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe2 : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a2 v = some wa → lookupVar c2 v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepsReadyH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => 1) [(i1, idx1), (i2, idx2)] S := by
  have hstep1 : BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      1 (i1, idx1) S :=
    bodyStepH_of_bodyStepG (by simp [outsOf, houts1])
      (bodyStepG_of_bodyStep houts1
        (bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
          (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
          (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1))
  have hstep2 : BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      1 (i2, idx2) (S ++ [o1]) :=
    bodyStepH_calldatacopy (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
      (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
      (nextIsTerminator := true) (curBbLabel := curBbLabel)
      hname2 hncomm2 hnjmp2 hcompute2 hops2 houts2 hab2 hbc2 hac2 ha2S hb2S hc2S hlivea2 hliveb2 hlivec2 hstepEqFn2 hmemsafe2
  refine bodyStepsReadyH_cons hstep1 ?_
  have hout1 : outsOf (i1, idx1) = [o1] := by rw [outsOf, houts1]
  rw [hout1]
  exact bodyStepsReadyH_cons hstep2 bodyStepsReadyH_nil

/-- **End-to-end demand-fold mixed-arity body sim.** Feeds `bodyStepsReadyH_binop_calldatacopy` through
    `genBlockBodyH_sim_inv`: a binop (1 output) then a CALLDATACOPY (3 inputs, 0 outputs) run as one
    body, ending OK, still related, discipline at 0, stack now `S ++ [o1]` (the copy added nothing).
    Headroom is `Σ dem = 2` — strictly more than the output count 1 — the concrete witness that the
    demand-decoupled fold composes a 3-input 0-output copy that the output-count fold cannot. -/
theorem genBlockBodyH_binop_calldatacopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 n1 a2 b2 c2 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "CALLDATACOPY") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hops2 : i2.operands = [Operand.Var a2, Operand.Var b2, Operand.Var c2]) (houts2 : i2.outputs = [])
    (hab2 : a2 ≠ b2) (hbc2 : b2 ≠ c2) (hac2 : a2 ≠ c2)
    (ha2S : a2 ∈ S ++ [o1]) (hb2S : b2 ∈ S ++ [o1]) (hc2S : c2 ∈ S ++ [o1])
    (hlivea2 : nextLiveness.contains a2 = true) (hliveb2 : nextLiveness.contains b2 = true) (hlivec2 : nextLiveness.contains c2 = true)
    (hstepEqFn2 : ∀ (v : VenomState) wa wb wc, lookupVar a2 v = some wa → lookupVar b2 v = some wb → lookupVar c2 v = some wc →
        stepInstBase i2 v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe2 : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a2 v = some wa → lookupVar c2 v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsd0 : StackDiscH 2 ps0 vs0)
    (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].flatMap outsOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyH_binop_calldatacopy (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx1 := idx1) (idx2 := idx2) (curBbLabel := curBbLabel)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
    hname2 hncomm2 hnjmp2 hcompute2 hops2 houts2 hab2 hbc2 hac2 ha2S hb2S hc2S hlivea2 hliveb2 hlivec2 hstepEqFn2 hmemsafe2
  exact genBlockBodyH_sim_inv
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    (fun _ => 1) [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ## Permutation-threading body fold (active-swap regime)

The active-swap counterpart of `genBlockBody_sim_inv_S`: threads `StackPerm` (up to permutation)
instead of the exact-order `StackIsVars`, so it admits per-instruction steps that *reorder* the stack
(the active optimistic swap). Identical fold structure — the per-instruction readiness predicate
`BodyStepsReadyP` pins `S` per position and concludes `StackPerm (S ++ [outOf x])`; the active-swap
step `genRegularInstPlan_commBinopVar_sim_swap` (+ `optimisticSwapPlan_stackPerm`) discharges each
entry. -/
def BodyStepsReadyP (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S =>
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → StackPerm S p → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
        StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
        StackPerm (S ++ [outOf x]) (gp x p).2)
      ∧ BodyStepsReadyP lo offsetToPc prog gp xs (S ++ [outOf x])

/-- **Permutation-threading body fold.** As `genBlockBody_sim_inv_S` but with `StackPerm` (so it
    covers blocks whose instructions reorder the stack via the optimistic swap). Folds
    `BodyStepsReadyP` one entry per instruction, threading `StackDiscH` (`l.length → 0`) and
    `StackPerm` (`S0 → S0 ++ l.map outOf`). -/
theorem genBlockBody_sim_inv_P {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyP lo offsetToPc prog gp l S0 →
      StackDiscH l.length ps0 vs0 → StackPerm S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
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
             StackPerm (S0 ++ l.map outOf)
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

/-- **Spill-aware single body step.** The `StackDiscHS` analogue of `BodyStep`: from the spill-aware
    invariant `StackDiscHS (j+1)`, `StackPerm S`, and `venomAsmRel`, instruction `x` runs its emitted
    plan and re-establishes `StackDiscHS j` **inside the existential** (tied to the post-run asm state,
    since `spillWf` reads its memory size) plus `StackPerm (S ++ [outOf x])`. Exactly the shape produced
    by every `stackDiscHS_*_step_S` reroute. -/
def BodyStepHS (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscHS (j + 1) p v s → StackPerm S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length ∧
           StackDiscHS j (gp x p).2 (gvBodyStep x v) s') ∧
    StackPerm (S ++ [outOf x]) (gp x p).2

/-- **Spill-aware per-instruction body-step readiness.** The `StackDiscHS` analogue of
    `BodyStepsReadyP`: `BodyStepHS` for the head at `S`, then readiness for the tail at `S ++ [outOf x]`
    (the S-thread). -/
def BodyStepsReadyHS (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepHS lo offsetToPc prog gp x S ∧ BodyStepsReadyHS lo offsetToPc prog gp xs (S ++ [outOf x])

/-- Empty body is trivially ready. -/
theorem bodyStepsReadyHS_nil {lo offsetToPc prog gp S} :
    BodyStepsReadyHS lo offsetToPc prog gp [] S := trivial

/-- Cons a ready head step onto a ready tail — the spill-aware analogue of `bodyStepsReady_cons`. -/
theorem bodyStepsReadyHS_cons {lo offsetToPc prog gp x xs S}
    (hhead : BodyStepHS lo offsetToPc prog gp x S)
    (htail : BodyStepsReadyHS lo offsetToPc prog gp xs (S ++ [outOf x])) :
    BodyStepsReadyHS lo offsetToPc prog gp (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Spill-aware body fold.** The `StackDiscHS` analogue of `genBlockBody_sim_inv_P`: folds
    `BodyStepsReadyHS` one entry per instruction, threading the spill-aware invariant
    (`StackDiscHS l.length → StackDiscHS 0`, bundled inside the final existential) and `StackPerm`
    (`S0 → S0 ++ l.map outOf`). The integration point — any block whose instructions each have a
    `stackDiscHS_*_step_S` producer (repackaged as `BodyStepHS`) feeds straight in. -/
theorem genBlockBody_sim_inv_HS {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyHS lo offsetToPc prog gp l S0 →
      StackDiscHS l.length ps0 vs0 as0 → StackPerm S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
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
             StackDiscHS 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             StackPerm (S0 ++ l.map outOf)
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
    obtain ⟨⟨as1, hrun1, hrel1, hpc1, hsd1⟩, hsv1⟩ := hstepx ps0 vs0 as0 xs.length hsd0 hsv0 hrel0 hb1
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


/-- **Spill-free-over-`D`.** None of the vars in a *fixed* set `D` is spilled. Threaded with `D` = the
    block's full var set (`S0 ++ all outputs`), so it covers both on-stack operands (`hnospill`) and a
    fresh output (`hspill_out`) — the freshness `StackPerm`/growing-`S` disjointness cannot supply.
    Preserved by every regular instruction (they only *remove* spills, never add). -/
def SpillFree (D : List String) (p : PlanState) : Prop :=
  ∀ v ∈ D, alookup' p.spilled (Operand.Var v) = none

/-- A `none` lookup stays `none` after `releaseDeadSpills` (the fold only removes entries). -/
theorem alookup_releaseDeadSpills_none {nextLiveness : List String} {ps : PlanState} {op : Operand}
    (h : alookup' ps.spilled op = none) :
    alookup' (releaseDeadSpills nextLiveness ps).spilled op = none := by
  rcases hlk : alookup' (releaseDeadSpills nextLiveness ps).spilled op with _ | off
  · rfl
  · exfalso
    have hlk' : AssocList.lookup Operand Nat (releaseDeadSpills nextLiveness ps).spilled op = some off := hlk
    rw [releaseDeadSpills_eq_foldl] at hlk'
    have hsub := (releaseDeadSpills_foldl_inv nextLiveness ps.spilled ps).2.2.2 op off hlk'
    have hnone : AssocList.lookup Operand Nat ps.spilled op = none := h
    rw [hnone] at hsub; nomatch hsub

/-- `releaseDeadSpills` preserves `SpillFree D`. -/
theorem releaseDeadSpills_spillFree {nextLiveness : List String} {D : List String} {ps : PlanState}
    (h : SpillFree D ps) : SpillFree D (releaseDeadSpills nextLiveness ps) :=
  fun v hv => alookup_releaseDeadSpills_none (h v hv)

/-- **Disjointness-threading single body step.** As `BodyStepHS` but also given/producing `SpillFree D`
    (`D` fixed). This is the shape a *both-operands-live* step in a possibly-spilled state satisfies:
    `SpillFree D` gives `hnospill` for each on-stack operand *and* `hspill_out` for the fresh output. -/
def BodyStepHSD (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (D : List String) (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscHS (j + 1) p v s → StackPerm S p → SpillFree D p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length ∧
           StackDiscHS j (gp x p).2 (gvBodyStep x v) s') ∧
    StackPerm (S ++ [outOf x]) (gp x p).2 ∧ SpillFree D (gp x p).2

/-- Per-instruction readiness for the disjointness-threading fold. -/
def BodyStepsReadyHSD (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (D : List String) : List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepHSD lo offsetToPc prog gp D x S ∧ BodyStepsReadyHSD lo offsetToPc prog gp D xs (S ++ [outOf x])

theorem bodyStepsReadyHSD_nil {lo offsetToPc prog gp D S} :
    BodyStepsReadyHSD lo offsetToPc prog gp D [] S := trivial

theorem bodyStepsReadyHSD_cons {lo offsetToPc prog gp D x xs S}
    (hhead : BodyStepHSD lo offsetToPc prog gp D x S)
    (htail : BodyStepsReadyHSD lo offsetToPc prog gp D xs (S ++ [outOf x])) :
    BodyStepsReadyHSD lo offsetToPc prog gp D (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Disjointness-threading body fold.** As `genBlockBody_sim_inv_HS` but also threading `SpillFree D`
    (fixed `D`). A block of both-operands-live steps (each net +1, fitting the uniform fuel) in a
    possibly-spilled state folds to a whole-body sim preserving all three invariants. -/
theorem genBlockBody_sim_inv_HSD {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} {D : List String}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyHSD lo offsetToPc prog gp D l S0 →
      StackDiscHS l.length ps0 vs0 as0 → StackPerm S0 ps0 → SpillFree D ps0 →
      venomAsmRel lo ps0 vs0 as0 →
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
             StackDiscHS 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             StackPerm (S0 ++ l.map outOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 ∧
             SpillFree D
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hdj0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
    · simpa using hdj0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hdj0 hrel0 hblock
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
    obtain ⟨⟨as1, hrun1, hrel1, hpc1, hsd1⟩, hsv1, hdj1⟩ := hstepx ps0 vs0 as0 xs.length hsd0 hsv0 hdj0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv', hdj'⟩ :=
      ih (S0 ++ [outOf x]) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hdj1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_, hdj'⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'

/-- **Both-live binop as a `BodyStepHSD`.** Packages `stackDiscHS_nonCommBinop_bothlive_step_S` into the
    disjointness-threading fold's step: from `StackPerm S` (`x, y ∈ S`, `out ∉ S`) and `SpillFree D`
    (`x, y, out ∈ D`) it reads every side condition the both-live binop producer needs — `hxmem`/`hymem`
    (`stackPerm_mem`), `hnospill_x`/`hnospill_y`/`hspill_out` (`SpillFree`), `hfresh`
    (`stackPerm_not_mem`) — and re-establishes `StackPerm (S ++ [out])` and `SpillFree D`. The concrete
    non-vacuous feed of `genBlockBody_sim_inv_HSD`: a block of both-live binops in a possibly-spilled
    state folds to a whole-body sim. -/
theorem bodyStepHSD_nonCommBinop_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {D S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y]) (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxD : x ∈ D) (hyD : y ∈ D) (houtD : out ∈ D)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSD lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      D (inst, idx) S := by
  intro p v s j hsd hsv hsf hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hymem := stackPerm_mem hsv hyS
  have hnospill_x := hsf x hxD
  have hnospill_y := hsf y hyD
  have hspill_out := hsf out houtD
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  -- the both-live binop sim + StackDiscHS
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_nonCommBinop_bothlive_step_S hsd hname hncomm
    hnjmp hcompute (hdispatch v) hops houts hxy rfl hxmem hymem hlive hfresh hspill_out hnospill_y
    hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
  -- the final plan state, in closed form
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
  refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩, ?_, ?_⟩
  · -- StackPerm (S ++ [outOf (inst,idx)])
    rw [hout, hfinal]
    exact stackPerm_of_stack_append hsv (by rw [releaseDeadSpills_stack])
  · -- SpillFree D
    rw [hfinal]
    intro w hw
    exact alookup_releaseDeadSpills_none (show alookup' ({ p with stack := p.stack ++ [Operand.Var out] } : PlanState).spilled (Operand.Var w) = none from hsf w hw)

/-- **Both-live ternop as a `BodyStepHSD`.** Packages `stackDiscHS_ternopVar_bothlive_step_S` into the
    disjointness-threading fold's step (the 3-in-1-out analogue of `bodyStepHSD_nonCommBinop_bothlive`):
    from `StackPerm S` (`x, y, z ∈ S`, `out ∉ S`) and `SpillFree D` (`x, y, z, out ∈ D`) it reads every
    side condition the both-live ternop producer needs and re-establishes `StackPerm (S ++ [out])` and
    `SpillFree D`. Extends the concrete non-vacuous fold feed to ADDMOD/MULMOD. -/
theorem bodyStepHSD_ternopVar_bothlive
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {D S : List String} {x y z out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z]) (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D) (houtD : out ∈ D)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : ∀ (p : PlanState), optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStepHSD lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      D (inst, idx) S := by
  intro p v s j hsd hsv hsf hrel hblock
  have hxmem := stackPerm_mem hsv hxS
  have hymem := stackPerm_mem hsv hyS
  have hzmem := stackPerm_mem hsv hzS
  have hnospill_x := hsf x hxD
  have hnospill_y := hsf y hyD
  have hnospill_z := hsf z hzD
  have hspill_out := hsf out houtD
  have hfresh : ¬ Operand.Var out ∈ p.stack := stackPerm_not_mem hsv houtS
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hoz : out ≠ z := by rintro rfl; exact hfresh hzmem
  obtain ⟨as', hrun, hrel', hpc, hsd'⟩ := stackDiscHS_ternopVar_bothlive_step_S hsd hname hncomm
    hnjmp hcompute (hdispatch v) hops houts hxy hyz hxz hox hoy hoz rfl hxmem hymem hzmem hlive hfresh
    hspill_out hnospill_z hlivez hnospill_y hlivey hnospill_x hlivex hdisp (hoptnoop p) hrel hblock
  have hshallow : p.stack.length ≤ 14 := by have := hsd.shallow; omega
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
  refine ⟨⟨as', hrun, hrel', hpc, hsd'⟩, ?_, ?_⟩
  · rw [hout, hfinal]
    exact stackPerm_of_stack_append hsv (by rw [releaseDeadSpills_stack])
  · rw [hfinal]
    intro w hw
    exact alookup_releaseDeadSpills_none (show alookup' ({ p with stack := p.stack ++ [Operand.Var out] } : PlanState).spilled (Operand.Var w) = none from hsf w hw)

end EvmYul.Venom.Hol.Codegen

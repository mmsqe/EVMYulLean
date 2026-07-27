import EvmYul.Venom.Hol.Codegen.GenInstSim.BinopSim

/-!
# GenInstSim — JoinProducers

Non-commutative binop + ternary sims, the genuine multi-swap / single-rotation join reconciliations,
and the consume-operand / SSTORE / same-var / unary / spilled-value producers.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

variable {offsetToPc : AssocList Nat Nat}

/-! ## Non-commutative binop (now sound after the operand-order fix)

With `computeOperands` reversing the operand list (semantic→stack order), the emitted pair is
`[Lit b, Lit a]`, so the asm computes `f a b` directly — matching `execPure2 f [op1,op2] = f a b`
even for non-commutative `f`. This is the case the old (un-reversed) codegen miscompiled. The
structural decomposition is *simpler* than the commutative one: with `isCommutative = false` the
cheaper-order `if` is skipped, so `operands' = operands = inst.operands.reverse` directly. -/

/-- Structural decomposition of `generateRegularInstPlan` for a **non-commutative** binop with two
    distinct literal operands. Same plan shape as the commutative case, but without the
    commutative cheaper-order dispatch. -/
theorem genRegularInstPlan_nonCommBinopLit_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {a b : bytes32} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hab : a ≠ b)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Lit b, Operand.Lit a] := by rw [hops]; rfl
  have hallLit : ∀ op ∈ ([Operand.Lit b, Operand.Lit a] : List Operand), ∃ v, op = Operand.Lit v := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> exact ⟨_, rfl⟩
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Lit b, Operand.Lit a] := by
    rw [hrev]
    have := emitInputPlan_stack_allLit inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps hallLit
    rw [this, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Lit b, Operand.Lit a] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1
    rw [← h2]; exact hps1
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_lit_nil base b a ps1 hps1' (Ne.symm hab),
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- The runnable sim for a non-commutative binop with two distinct literal operands. The asm
    computes `f a b` directly (no commutativity needed) — the case the un-reversed codegen got
    wrong. -/
theorem genRegularInstPlan_nonCommBinopLit_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hab : a ≠ b)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Lit b, Operand.Lit a] := by rw [hops]; rfl
  rw [genRegularInstPlan_nonCommBinopLit_eq hname hncomm hnjmp hcompute hops houts hab hstack0 hlive,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Lit b, Operand.Lit a] := by
    rw [hps1def, emitInputPlan_pair_lit_eq, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emitInputPlan_pair_lit_eq]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := emitInputPlan_pair_lit_sim hrel hbI
  have hstacktop : as1.stack = a :: b :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_lit hrelI hps1stack
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **SUB instantiation** — the first non-commutative binop simulation, sound *only because* of the
    operand-order fix (the un-reversed codegen computed `b - a`). End to end: the generated plan
    for `out := SUB (Lit a) (Lit b)` simulates the Venom step setting `out := a - b`. -/
theorem genRegularInstPlan_subLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hsub : inst.opcode = Opcode.SUB)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (a - b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hsub]; rfl) (by rw [hsub]; rfl)
    (by rw [hsub]; decide) (by simp [computeOperands, hsub]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sub_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-! ## Per-instruction execution sim (3-input ternary opcode: ADDMOD/MULMOD)

The 3-input analog of the non-commutative var-binop sim. The ternary opcodes are not commutative
(no cheaper-order dispatch), so the plan shape mirrors `genRegularInstPlan_nonCommBinopVar_*` with
three DUPs for the inputs, a 3-wide reorder no-op, a 3-wide pop, and the same kept output. -/

/-- `stackPop 3 (base ++ [x, y, z]) = base`. The 3-input companion of `stackPop_2_append_pair`. -/
theorem stackPop_3_append_triple (base : List Operand) (x y z : Operand) :
    stackPop 3 (base ++ [x, y, z]) = base := by
  unfold stackPop; simp

/-- `get!` at the three append-tail positions of `base ++ [a, b, c]`. -/
theorem getbang_append_triple_0 (base : List Operand) (a b c : Operand) :
    (base ++ [a, b, c])[base.length]! = a := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

theorem getbang_append_triple_1 (base : List Operand) (a b c : Operand) :
    (base ++ [a, b, c])[base.length + 1]! = b := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

theorem getbang_append_triple_2 (base : List Operand) (a b c : Operand) :
    (base ++ [a, b, c])[base.length + 2]! = c := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

/-- `stackPeek` at depths 0/1/2 of `base ++ [a, b, c]` (TOS = `c`). -/
theorem stackPeek_0_append_triple (base : List Operand) (a b c : Operand) :
    stackPeek 0 (base ++ [a, b, c]) = c := by
  unfold stackPeek
  rw [show (base ++ [a, b, c]).length - 1 - 0 = base.length + 2 from by simp]
  exact getbang_append_triple_2 base a b c

theorem stackPeek_1_append_triple (base : List Operand) (a b c : Operand) :
    stackPeek 1 (base ++ [a, b, c]) = b := by
  unfold stackPeek
  rw [show (base ++ [a, b, c]).length - 1 - 1 = base.length + 1 from by simp]
  exact getbang_append_triple_1 base a b c

theorem stackPeek_2_append_triple (base : List Operand) (a b c : Operand) :
    stackPeek 2 (base ++ [a, b, c]) = a := by
  unfold stackPeek
  rw [show (base ++ [a, b, c]).length - 1 - 2 = base.length from by simp]
  exact getbang_append_triple_0 base a b c

/-- A list of length ≥ 3 is `get!0 :: get!1 :: get!2 :: drop 3`. -/
theorem list_eq_get3 {α} [Inhabited α] (l : List α) (h : 3 ≤ l.length) :
    l = l[0]! :: l[1]! :: l[2]! :: l.drop 3 := by
  match l with
  | c0 :: c1 :: c2 :: rest => rfl
  | [] => simp at h
  | [c0] => simp at h
  | [c0, c1] => simp at h

/-! ### Genuine multi-swap join reconciliation (`perm_reaches`, 3-element case)

The identity join (`reorderPlan_vars_nil`) and the transposition join (`reorderPlan_swapped_pair_var`)
are handled. The next step of the general `perm_reaches` — where `reorderPlan` synthesises the target
layout with *two* swaps and must not disturb an already-placed element — is the 3-cycle. These are the
triple `stackSwap` helpers and the concrete 3-cycle reconciliation. -/

/-- `stackSwap 2` on `base ++ [x, y, z]` (z = TOS) swaps TOS with the depth-2 element. -/
theorem stackSwap_2_append_triple (base : List Operand) (x y z : Operand) :
    stackSwap 2 (base ++ [x, y, z]) = base ++ [z, y, x] := by
  have hlen : (base ++ [x, y, z]).length = base.length + 3 := by simp
  have htop : (base ++ [x, y, z])[base.length + 2]! = z := getbang_append_triple_2 base x y z
  have htgt : (base ++ [x, y, z])[base.length]! = x := getbang_append_triple_0 base x y z
  have hset1 : (base ++ [x, y, z]).set (base.length + 2) x = base ++ [x, y, x] := by
    rw [List.set_append_right (base.length + 2) x (by omega)]; simp
  have hset2 : (base ++ [x, y, x]).set base.length z = base ++ [z, y, x] := by
    rw [List.set_append_right base.length z (by omega)]; simp
  unfold stackSwap
  simp only [hlen, show base.length + 3 - 1 = base.length + 2 from by omega,
    show base.length + 2 - 2 = base.length from by omega, htop, htgt, hset1, hset2]

/-- `stackSwap 1` on `base ++ [x, y, z]` (z = TOS) swaps the top two, keeping the depth-2 element. -/
theorem stackSwap_1_append_triple (base : List Operand) (x y z : Operand) :
    stackSwap 1 (base ++ [x, y, z]) = base ++ [x, z, y] := by
  have hlen : (base ++ [x, y, z]).length = base.length + 3 := by simp
  have htop : (base ++ [x, y, z])[base.length + 2]! = z := getbang_append_triple_2 base x y z
  have htgt : (base ++ [x, y, z])[base.length + 1]! = y := getbang_append_triple_1 base x y z
  have hset1 : (base ++ [x, y, z]).set (base.length + 2) y = base ++ [x, y, y] := by
    rw [List.set_append_right (base.length + 2) y (by omega)]; simp
  have hset2 : (base ++ [x, y, y]).set (base.length + 1) z = base ++ [x, z, y] := by
    rw [List.set_append_right (base.length + 1) z (by omega)]; simp
  unfold stackSwap
  simp only [hlen, show base.length + 3 - 1 = base.length + 2 from by omega,
    show base.length + 2 - 1 = base.length + 1 from by omega, htop, htgt, hset1, hset2]

/-- TOS of a triple `base ++ [x, y, z]` sits at depth 0. -/
theorem stackGetDepth_triple_tos (base : List Operand) (x y z : Operand) :
    stackGetDepth z (base ++ [x, y, z]) = some 0 := by
  simp [stackGetDepth, stackFind, List.reverse_append]

/-- `doSwap 2` is a single `SWAP2`. -/
theorem doSwap_two (ps : PlanState) :
    doSwap 2 ps = ([StackOp.SOSwap 2], { ps with stack := stackSwap 2 ps.stack }) := by
  unfold doSwap; simp

/-- **A genuine 3-cycle join reconciliation.** For the target entry layout `[a, b, c]` and a predecessor
    that leaves the 3-cycle permutation `[b, c, a]` on top of the stack (`a` = TOS), `reorderPlan`
    synthesises the target layout with two swaps (`SWAP2 ; SWAP1`). This is the smallest genuine
    `perm_reaches` case beyond the transposition `reorderPlan_swapped_pair_var`: step 0 places `a` at the
    deepest target slot (depth 2), and step 1's `SWAP1` — over the top two — does **not** disturb that
    placed `a` (the "doesn't disturb already-placed" property that distinguishes the general reorder from
    a single transposition). The stack result needs no distinctness hypothesis — each reorder step's
    operand is threaded through the TOS, so it is located unconditionally. -/
theorem reorderPlan_3cycle_var (base : List Operand) (a b c : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var b, Operand.Var c, Operand.Var a]) :
    (reorderPlan [Operand.Var a, Operand.Var b, Operand.Var c] ps).2.stack
      = base ++ [Operand.Var a, Operand.Var b, Operand.Var c] := by
  -- step 0: op `a` (at TOS) → depth 2 via SWAP2, leaving `base ++ [a, c, b]`
  have hstep0 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c] 0 (Operand.Var a) ps
      = ([StackOp.SOSwap 2], { ps with stack := base ++ [Operand.Var a, Operand.Var c, Operand.Var b] }) := by
    have hd : stackGetDepth (Operand.Var a) ps.stack = some 0 := by
      rw [hstack]; exact stackGetDepth_triple_tos base (Operand.Var b) (Operand.Var c) (Operand.Var a)
    have hsw : stackSwap 2 ps.stack = base ++ [Operand.Var a, Operand.Var c, Operand.Var b] := by
      rw [hstack]; exact stackSwap_2_append_triple base (Operand.Var b) (Operand.Var c) (Operand.Var a)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_two, hsw]
  -- step 1: op `b` (now at TOS) → depth 1 via SWAP1, leaving `base ++ [a, b, c]`; `a` at depth 2 untouched
  have hstep1 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c] 1 (Operand.Var b)
      { ps with stack := base ++ [Operand.Var a, Operand.Var c, Operand.Var b] }
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c] }) := by
    have hd : stackGetDepth (Operand.Var b) (base ++ [Operand.Var a, Operand.Var c, Operand.Var b]) = some 0 :=
      stackGetDepth_triple_tos base (Operand.Var a) (Operand.Var c) (Operand.Var b)
    have hsw : stackSwap 1 (base ++ [Operand.Var a, Operand.Var c, Operand.Var b])
        = base ++ [Operand.Var a, Operand.Var b, Operand.Var c] :=
      stackSwap_1_append_triple base (Operand.Var a) (Operand.Var c) (Operand.Var b)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_one, hsw]
  -- step 2: op `c` (now at TOS) is already at its target depth 0 → no-op
  have hstep2 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c] 2 (Operand.Var c)
      { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c] }
      = ([], { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var c) (base ++ [Operand.Var a, Operand.Var b, Operand.Var c]) = some 0
    exact stackGetDepth_triple_tos base (Operand.Var a) (Operand.Var b) (Operand.Var c)
  unfold reorderPlan
  have henum : ([Operand.Var a, Operand.Var b, Operand.Var c]).enum
      = [(0, Operand.Var a), (1, Operand.Var b), (2, Operand.Var c)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, hstep2,
    List.append_nil, List.nil_append]


/-! ### 4-input (quad) stack helpers — the 3→4 ports for EXTCODECOPY's 4-input plan. -/

theorem getbang_append_quad_0 (base : List Operand) (a b c d : Operand) :
    (base ++ [a, b, c, d])[base.length]! = a := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

theorem getbang_append_quad_1 (base : List Operand) (a b c d : Operand) :
    (base ++ [a, b, c, d])[base.length + 1]! = b := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

theorem getbang_append_quad_2 (base : List Operand) (a b c d : Operand) :
    (base ++ [a, b, c, d])[base.length + 2]! = c := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

theorem getbang_append_quad_3 (base : List Operand) (a b c d : Operand) :
    (base ++ [a, b, c, d])[base.length + 3]! = d := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

/-- `stackPeek` at depths 0/1/2/3 of `base ++ [a, b, c, d]` (TOS = `d`). -/
theorem stackPeek_0_append_quad (base : List Operand) (a b c d : Operand) :
    stackPeek 0 (base ++ [a, b, c, d]) = d := by
  unfold stackPeek
  rw [show (base ++ [a, b, c, d]).length - 1 - 0 = base.length + 3 from by simp]
  exact getbang_append_quad_3 base a b c d

theorem stackPeek_1_append_quad (base : List Operand) (a b c d : Operand) :
    stackPeek 1 (base ++ [a, b, c, d]) = c := by
  unfold stackPeek
  rw [show (base ++ [a, b, c, d]).length - 1 - 1 = base.length + 2 from by simp]
  exact getbang_append_quad_2 base a b c d

theorem stackPeek_2_append_quad (base : List Operand) (a b c d : Operand) :
    stackPeek 2 (base ++ [a, b, c, d]) = b := by
  unfold stackPeek
  rw [show (base ++ [a, b, c, d]).length - 1 - 2 = base.length + 1 from by simp]
  exact getbang_append_quad_1 base a b c d

theorem stackPeek_3_append_quad (base : List Operand) (a b c d : Operand) :
    stackPeek 3 (base ++ [a, b, c, d]) = a := by
  unfold stackPeek
  rw [show (base ++ [a, b, c, d]).length - 1 - 3 = base.length from by simp]
  exact getbang_append_quad_0 base a b c d

/-- `stackPop 4 (base ++ [a, b, c, d]) = base`. -/
theorem stackPop_4_append_quad (base : List Operand) (a b c d : Operand) :
    stackPop 4 (base ++ [a, b, c, d]) = base := by
  unfold stackPop; simp

/-- A list of length ≥ 4 is `get!0 :: get!1 :: get!2 :: get!3 :: drop 4`. -/
theorem list_eq_get4 {α} [Inhabited α] (l : List α) (h : 4 ≤ l.length) :
    l = l[0]! :: l[1]! :: l[2]! :: l[3]! :: l.drop 4 := by
  match l with
  | c0 :: c1 :: c2 :: c3 :: rest => rfl
  | [] => simp at h
  | [c0] => simp at h
  | [c0, c1] => simp at h
  | [c0, c1, c2] => simp at h

/-! ### Genuine multi-swap join reconciliation (`perm_reaches`, 4-element rotation)

The 4-element continuation of `reorderPlan_3cycle_var`: the single left-rotation, exercising the
"doesn't disturb **two** already-placed elements" case (after steps 0–1 both `a` at depth 3 and `b` at
depth 2 must survive step 2's shallow `SWAP1`). Triple `stackSwap` had `stackSwap_{1,2}_append_triple`;
here the quad `stackSwap_{1,2,3}_append_quad` ports (over the existing `getbang_append_quad_*`). -/

/-- `stackSwap 3` on `base ++ [w, x, y, z]` (z = TOS) swaps TOS with the depth-3 element. -/
theorem stackSwap_3_append_quad (base : List Operand) (w x y z : Operand) :
    stackSwap 3 (base ++ [w, x, y, z]) = base ++ [z, x, y, w] := by
  have hlen : (base ++ [w, x, y, z]).length = base.length + 4 := by simp
  have htop : (base ++ [w, x, y, z])[base.length + 3]! = z := getbang_append_quad_3 base w x y z
  have htgt : (base ++ [w, x, y, z])[base.length]! = w := getbang_append_quad_0 base w x y z
  have hset1 : (base ++ [w, x, y, z]).set (base.length + 3) w = base ++ [w, x, y, w] := by
    rw [List.set_append_right (base.length + 3) w (by omega)]; simp
  have hset2 : (base ++ [w, x, y, w]).set base.length z = base ++ [z, x, y, w] := by
    rw [List.set_append_right base.length z (by omega)]; simp
  unfold stackSwap
  simp only [hlen, show base.length + 4 - 1 = base.length + 3 from by omega,
    show base.length + 3 - 3 = base.length from by omega, htop, htgt, hset1, hset2]

/-- `stackSwap 2` on `base ++ [w, x, y, z]` (z = TOS) swaps TOS with the depth-2 element. -/
theorem stackSwap_2_append_quad (base : List Operand) (w x y z : Operand) :
    stackSwap 2 (base ++ [w, x, y, z]) = base ++ [w, z, y, x] := by
  have hlen : (base ++ [w, x, y, z]).length = base.length + 4 := by simp
  have htop : (base ++ [w, x, y, z])[base.length + 3]! = z := getbang_append_quad_3 base w x y z
  have htgt : (base ++ [w, x, y, z])[base.length + 1]! = x := getbang_append_quad_1 base w x y z
  have hset1 : (base ++ [w, x, y, z]).set (base.length + 3) x = base ++ [w, x, y, x] := by
    rw [List.set_append_right (base.length + 3) x (by omega)]; simp
  have hset2 : (base ++ [w, x, y, x]).set (base.length + 1) z = base ++ [w, z, y, x] := by
    rw [List.set_append_right (base.length + 1) z (by omega)]; simp
  unfold stackSwap
  simp only [hlen, show base.length + 4 - 1 = base.length + 3 from by omega,
    show base.length + 3 - 2 = base.length + 1 from by omega, htop, htgt, hset1, hset2]

/-- `stackSwap 1` on `base ++ [w, x, y, z]` (z = TOS) swaps the top two. -/
theorem stackSwap_1_append_quad (base : List Operand) (w x y z : Operand) :
    stackSwap 1 (base ++ [w, x, y, z]) = base ++ [w, x, z, y] := by
  have hlen : (base ++ [w, x, y, z]).length = base.length + 4 := by simp
  have htop : (base ++ [w, x, y, z])[base.length + 3]! = z := getbang_append_quad_3 base w x y z
  have htgt : (base ++ [w, x, y, z])[base.length + 2]! = y := getbang_append_quad_2 base w x y z
  have hset1 : (base ++ [w, x, y, z]).set (base.length + 3) y = base ++ [w, x, y, y] := by
    rw [List.set_append_right (base.length + 3) y (by omega)]; simp
  have hset2 : (base ++ [w, x, y, y]).set (base.length + 2) z = base ++ [w, x, z, y] := by
    rw [List.set_append_right (base.length + 2) z (by omega)]; simp
  unfold stackSwap
  simp only [hlen, show base.length + 4 - 1 = base.length + 3 from by omega,
    show base.length + 3 - 1 = base.length + 2 from by omega, htop, htgt, hset1, hset2]

/-- TOS of a quad `base ++ [w, x, y, z]` sits at depth 0. -/
theorem stackGetDepth_quad_tos (base : List Operand) (w x y z : Operand) :
    stackGetDepth z (base ++ [w, x, y, z]) = some 0 := by
  simp [stackGetDepth, stackFind, List.reverse_append]

/-- `doSwap 3` is a single `SWAP3`. -/
theorem doSwap_three (ps : PlanState) :
    doSwap 3 ps = ([StackOp.SOSwap 3], { ps with stack := stackSwap 3 ps.stack }) := by
  unfold doSwap; simp

/-- **A genuine 4-element rotation join reconciliation.** For the target entry layout `[a, b, c, d]` and
    a predecessor leaving the single left-rotation `[b, c, d, a]` on top (`a` = TOS), `reorderPlan`
    synthesises the target with three swaps (`SWAP3 ; SWAP2 ; SWAP1`). Extends the 3-cycle
    (`reorderPlan_3cycle_var`) to the "doesn't disturb **two** already-placed elements" case: after steps
    0–1, `a` sits at depth 3 and `b` at depth 2, and step 2's `SWAP1` (over the top two) leaves both
    untouched. The stack result is unconditional (each step threads its operand through the TOS). -/
theorem reorderPlan_4rotate_var (base : List Operand) (a b c d : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var b, Operand.Var c, Operand.Var d, Operand.Var a]) :
    (reorderPlan [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] ps).2.stack
      = base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] := by
  -- step 0: `a` (TOS) → depth 3 via SWAP3, leaving `base ++ [a, c, d, b]`
  have hstep0 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] 0 (Operand.Var a) ps
      = ([StackOp.SOSwap 3], { ps with stack := base ++ [Operand.Var a, Operand.Var c, Operand.Var d, Operand.Var b] }) := by
    have hd : stackGetDepth (Operand.Var a) ps.stack = some 0 := by
      rw [hstack]; exact stackGetDepth_quad_tos base (Operand.Var b) (Operand.Var c) (Operand.Var d) (Operand.Var a)
    have hsw : stackSwap 3 ps.stack = base ++ [Operand.Var a, Operand.Var c, Operand.Var d, Operand.Var b] := by
      rw [hstack]; exact stackSwap_3_append_quad base (Operand.Var b) (Operand.Var c) (Operand.Var d) (Operand.Var a)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_three, hsw]
  -- step 1: `b` (TOS) → depth 2 via SWAP2, leaving `base ++ [a, b, d, c]`; `a` at depth 3 untouched
  have hstep1 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] 1 (Operand.Var b)
      { ps with stack := base ++ [Operand.Var a, Operand.Var c, Operand.Var d, Operand.Var b] }
      = ([StackOp.SOSwap 2], { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var d, Operand.Var c] }) := by
    have hd : stackGetDepth (Operand.Var b) (base ++ [Operand.Var a, Operand.Var c, Operand.Var d, Operand.Var b]) = some 0 :=
      stackGetDepth_quad_tos base (Operand.Var a) (Operand.Var c) (Operand.Var d) (Operand.Var b)
    have hsw : stackSwap 2 (base ++ [Operand.Var a, Operand.Var c, Operand.Var d, Operand.Var b])
        = base ++ [Operand.Var a, Operand.Var b, Operand.Var d, Operand.Var c] :=
      stackSwap_2_append_quad base (Operand.Var a) (Operand.Var c) (Operand.Var d) (Operand.Var b)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_two, hsw]
  -- step 2: `c` (TOS) → depth 1 via SWAP1, leaving `base ++ [a, b, c, d]`; `a`(3), `b`(2) untouched
  have hstep2 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] 2 (Operand.Var c)
      { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var d, Operand.Var c] }
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] }) := by
    have hd : stackGetDepth (Operand.Var c) (base ++ [Operand.Var a, Operand.Var b, Operand.Var d, Operand.Var c]) = some 0 :=
      stackGetDepth_quad_tos base (Operand.Var a) (Operand.Var b) (Operand.Var d) (Operand.Var c)
    have hsw : stackSwap 1 (base ++ [Operand.Var a, Operand.Var b, Operand.Var d, Operand.Var c])
        = base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] :=
      stackSwap_1_append_quad base (Operand.Var a) (Operand.Var b) (Operand.Var d) (Operand.Var c)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_one, hsw]
  -- step 3: `d` (TOS) already at target depth 0 → no-op
  have hstep3 : reorderOne () [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] 3 (Operand.Var d)
      { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] }
      = ([], { ps with stack := base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var d) (base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) = some 0
    exact stackGetDepth_quad_tos base (Operand.Var a) (Operand.Var b) (Operand.Var c) (Operand.Var d)
  unfold reorderPlan
  have henum : ([Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]).enum
      = [(0, Operand.Var a), (1, Operand.Var b), (2, Operand.Var c), (3, Operand.Var d)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, hstep2, hstep3,
    List.append_nil, List.nil_append]

/-! ### General single-rotation join reconciliation (`perm_reaches`, any length)

The concrete 3-cycle / 4-rotation above are the `n = 3, 4` instances of the general single left-rotation,
which `reorderPlan_rotate` proves for **any** length. The two general building blocks: `stackSwap`
localises to the top (active) segment (`stackSwap_append_right`) and a swap to the deepest slot exchanges
a segment's endpoints (`stackSwap_endpoints`). The rotation keeps the operand to place at the TOS at
every step, so `reorderOne` locates it unconditionally (`reorderOne_tos_stack`) — no nodup needed. -/

/-- One left-rotation of a stack segment: the deepest element moves to the TOS. -/
def rotate1 : List Operand → List Operand
  | [] => []
  | a :: l => l ++ [a]

/-- **`stackSwap` localises to the top segment.** When the swap distance `d` stays within the top part
    `high` of a stack `low ++ high` (`d < high.length`), the swap touches only `high`:
    `stackSwap d (low ++ high) = low ++ stackSwap d high`. The base of the stack (`low`) is untouched —
    the reusable core of the general `perm_reaches` induction (a reorder step over the active region
    leaves the already-placed prefix intact). -/
theorem stackSwap_append_right (low high : List Operand) (d : Nat) (hd : d < high.length) :
    stackSwap d (low ++ high) = low ++ stackSwap d high := by
  unfold stackSwap
  simp only [List.length_append]
  have h1 : low.length + high.length - 1 = low.length + (high.length - 1) := by omega
  rw [h1]
  have h2 : low.length + (high.length - 1) - d = low.length + (high.length - 1 - d) := by omega
  rw [h2]
  have g1 : (low ++ high)[low.length + (high.length - 1)]! = high[high.length - 1]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, ← List.getElem!_eq_getElem?_getD]
  have g2 : (low ++ high)[low.length + (high.length - 1 - d)]! = high[high.length - 1 - d]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, ← List.getElem!_eq_getElem?_getD]
  rw [g1, g2, List.set_append_right _ _ (Nat.le_add_right _ _),
      List.set_append_right _ _ (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]

/-- **Swapping to the deepest slot swaps a segment's endpoints.** `stackSwap (mid.length + 1)` on
    `a :: mid ++ [z]` (TOS = `z`, deepest = `a`) exchanges top and bottom, keeping the middle — the shape
    a `reorderPlan` rotation step produces. Companion to `stackSwap_append_right`. -/
theorem stackSwap_endpoints (a z : Operand) (mid : List Operand) :
    stackSwap (mid.length + 1) (a :: mid ++ [z]) = z :: mid ++ [a] := by
  have hl : (a :: mid ++ [z]).length = mid.length + 2 := by simp
  have htop : (a :: mid ++ [z])[mid.length + 1]! = z := by
    rw [List.getElem!_eq_getElem?_getD]
    show ((a :: (mid ++ [z]))[mid.length + 1]?).getD default = z
    rw [List.getElem?_cons_succ, List.getElem?_append_right (le_refl _)]
    simp
  have htgt : (a :: mid ++ [z])[0]! = a := by simp
  have hset1 : (a :: mid ++ [z]).set (mid.length + 1) a = a :: (mid ++ [a]) := by
    show (a :: (mid ++ [z])).set (mid.length + 1) a = a :: (mid ++ [a])
    rw [List.set_cons_succ]
    congr 1
    rw [List.set_append_right mid.length a (le_refl _)]
    simp
  unfold stackSwap
  rw [hl]
  simp only [show mid.length + 2 - 1 = mid.length + 1 from by omega,
    show mid.length + 1 - (mid.length + 1) = 0 from by omega, htop, htgt, hset1]
  show (a :: (mid ++ [a])).set 0 z = z :: mid ++ [a]
  rw [List.set_cons_zero, List.cons_append]

/-- `stackSwap 0` is the identity. -/
theorem stackSwap_zero (stk : List Operand) : stackSwap 0 stk = stk := by
  unfold stackSwap
  simp only [Nat.sub_zero, List.set_set]
  rcases stk with _ | ⟨h, t⟩
  · rfl
  · have hpos : (h :: t).length - 1 < (h :: t).length := by simp
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hpos, Option.getD_some,
        List.set_getElem_self]

/-- The TOS of `l ++ [op]` is `op`, at depth 0. -/
theorem stackGetDepth_snoc_self (op : Operand) (l : List Operand) :
    stackGetDepth op (l ++ [op]) = some 0 := by
  simp [stackGetDepth, stackFind, List.reverse_append]

/-- The deepest element of a `[y, x, x]` triple is at depth 2 (`y ≠ x`; the two `x`'s above it are
    scanned first, and any deeper `y` in `base` is never reached — found at depth 2 unconditionally). -/
theorem stackGetDepth_triple_deep (base : List Operand) (y x : String) (hyx : y ≠ x) :
    stackGetDepth (Operand.Var y) (base ++ [Operand.Var y, Operand.Var x, Operand.Var x]) = some 2 := by
  rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var x]
        = ((base ++ [Operand.Var y]) ++ [Operand.Var x]) ++ [Operand.Var x] from by simp,
      stackGetDepth_append_ne ((base ++ [Operand.Var y]) ++ [Operand.Var x]) hyx,
      stackGetDepth_append_ne (base ++ [Operand.Var y]) hyx,
      stackGetDepth_snoc_self]; rfl

/-- **Key-spilled store reorder — the first genuine non-positioned reorder-under-spill.** For target
    `[Var y, Var x]` and a stack `base ++ [y, x, x]` (the live value `y` DUP'd, then the spilled key `x`
    restored+DUP'd), `reorderPlan` synthesises two swaps `SWAP2 ; SWAP1`: the deep `y` (depth 2) moves to
    its target depth 1, then `x` is already at depth 0. Unlike the value-spilled config (reorder `[]`),
    the restored operand needs real swaps to reach its store position. Adapts the `reorderPlan_3cycle_var`
    technique with the triple-append swap lemmas. -/
theorem reorderPlan_keyspilled (base : List Operand) (x y : String) (ps : PlanState) (hxy : x ≠ y)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) := by
  have hstep0 : reorderOne () [Operand.Var y, Operand.Var x] 0 (Operand.Var y) ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    have hd : stackGetDepth (Operand.Var y) ps.stack = some 2 := by
      rw [hstack]; exact stackGetDepth_triple_deep base y x (Ne.symm hxy)
    have hsw2 : stackSwap 2 ps.stack = base ++ [Operand.Var x, Operand.Var x, Operand.Var y] := by
      rw [hstack]; exact stackSwap_2_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)
    have hsw1 : stackSwap 1 (base ++ [Operand.Var x, Operand.Var x, Operand.Var y])
        = base ++ [Operand.Var x, Operand.Var y, Operand.Var x] :=
      stackSwap_1_append_triple base (Operand.Var x) (Operand.Var x) (Operand.Var y)
    unfold reorderOne
    simp [hd, doSwap_two, doSwap_one, hsw2, hsw1]
  have hstep1 : reorderOne () [Operand.Var y, Operand.Var x] 1 (Operand.Var x)
      { ps with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }
      = ([], { ps with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var x) (base ++ [Operand.Var x, Operand.Var y, Operand.Var x]) = some 0
    exact stackGetDepth_triple_tos base (Operand.Var x) (Operand.Var y) (Operand.Var x)
  unfold reorderPlan
  have henum : ([Operand.Var y, Operand.Var x]).enum = [(0, Operand.Var y), (1, Operand.Var x)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.append_nil, List.nil_append]

/-- Deepest `y` in a both-spilled emit stack `base ++ [y, y, x, x]` is at depth 2 (the two `x`'s above
    are scanned first; the nearer `y` sits at the snoc boundary). The quad analogue of
    `stackGetDepth_triple_deep`. -/
theorem stackGetDepth_quad_deep (base : List Operand) (y x : String) (hyx : y ≠ x) :
    stackGetDepth (Operand.Var y)
      (base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]) = some 2 := by
  rw [show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
        = ((base ++ [Operand.Var y, Operand.Var y]) ++ [Operand.Var x]) ++ [Operand.Var x] from by simp,
      stackGetDepth_append_ne ((base ++ [Operand.Var y, Operand.Var y]) ++ [Operand.Var x]) hyx,
      stackGetDepth_append_ne (base ++ [Operand.Var y, Operand.Var y]) hyx,
      show base ++ [Operand.Var y, Operand.Var y] = (base ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
      stackGetDepth_snoc_self]; rfl

/-- **Both-spilled store reorder.** For target `[Var y, Var x]` on `base ++ [y, y, x, x]` (both operands
    restored+DUP'd, two copies each), `reorderPlan` synthesises the same `SWAP2 ; SWAP1` as the
    key-spilled case: the deep `y` (depth 2) moves to its target depth 1, `x` is already at TOS —
    leaving `base ++ [y, x, y, x]`. -/
theorem reorderPlan_bothspilled (base : List Operand) (x y : String) (ps : PlanState) (hxy : x ≠ y)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1],
         { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) := by
  have hstep0 : reorderOne () [Operand.Var y, Operand.Var x] 0 (Operand.Var y) ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1],
         { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    have hd : stackGetDepth (Operand.Var y) ps.stack = some 2 := by
      rw [hstack]; exact stackGetDepth_quad_deep base y x (Ne.symm hxy)
    have hsw2 : stackSwap 2 ps.stack
        = base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] := by
      rw [hstack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
            = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
          stackSwap_2_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
      simp
    have hsw1 : stackSwap 1 (base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y])
        = base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] := by
      rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y]
            = (base ++ [Operand.Var y]) ++ [Operand.Var x, Operand.Var x, Operand.Var y] from by simp,
          stackSwap_1_append_triple (base ++ [Operand.Var y]) (Operand.Var x) (Operand.Var x) (Operand.Var y)]
      simp
    unfold reorderOne
    simp [hd, doSwap_two, doSwap_one, hsw2, hsw1]
  have hstep1 : reorderOne () [Operand.Var y, Operand.Var x] 1 (Operand.Var x)
      { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }
      = ([], { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var x)
      (base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]) = some 0
    rw [show base ++ [Operand.Var y, Operand.Var x, Operand.Var y, Operand.Var x]
          = (base ++ [Operand.Var y, Operand.Var x, Operand.Var y]) ++ [Operand.Var x] from by simp]
    exact stackGetDepth_snoc_self (Operand.Var x) (base ++ [Operand.Var y, Operand.Var x, Operand.Var y])
  unfold reorderPlan
  have henum : ([Operand.Var y, Operand.Var x]).enum = [(0, Operand.Var y), (1, Operand.Var x)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.append_nil, List.nil_append]

-- LS emit .2 (y live, x spilled): stack base ++ [y, x, x], x's slot freed.
/-- Deepest `z` in a first-spilled ternop emit stack `base ++ [z, y, x, x]` is at depth 3. -/
theorem stackGetDepth_quad_deepest (base : List Operand) (z y x : String)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    stackGetDepth (Operand.Var z)
      (base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x]) = some 3 := by
  rw [show base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x]
        = (((base ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var x]) ++ [Operand.Var x]
        from by simp,
      stackGetDepth_append_ne (((base ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var x]) hzx,
      stackGetDepth_append_ne ((base ++ [Operand.Var z]) ++ [Operand.Var y]) hzx,
      stackGetDepth_append_ne (base ++ [Operand.Var z]) hzy,
      stackGetDepth_snoc_self]; rfl

/-- **First-spilled ternop reorder.** For target `[Var z, Var y, Var x]` on `base ++ [z, y, x, x]`
    (the spilled `x` restored+DUP'd, `z`/`y` live-DUP'd below), `reorderPlan` synthesises
    `SWAP3 ; SWAP2 ; SWAP1`: the deep `z` (depth 3) moves to its target depth 2 (two swaps), `y`
    lands at TOS and one `SWAP1` sends it home — leaving `base ++ [x, z, y, x]`, the operands
    positioned over the kept restored copy. -/
theorem reorderPlan_ternop_firstspilled (base : List Operand) (x y z : String) (ps : PlanState)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hstack : ps.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var z, Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1],
         { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
  have hstep0 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 0 (Operand.Var z) ps
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2],
         { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y] }) := by
    have hd : stackGetDepth (Operand.Var z) ps.stack = some 3 := by
      rw [hstack]; exact stackGetDepth_quad_deepest base z y x (Ne.symm hyz) (Ne.symm hxz)
    have hsw3 : stackSwap 3 ps.stack
        = base ++ [Operand.Var x, Operand.Var y, Operand.Var x, Operand.Var z] := by
      rw [hstack]
      exact stackSwap_3_append_quad base (Operand.Var z) (Operand.Var y) (Operand.Var x) (Operand.Var x)
    have hsw2 : stackSwap 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var x, Operand.Var z])
        = base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y] :=
      stackSwap_2_append_quad base (Operand.Var x) (Operand.Var y) (Operand.Var x) (Operand.Var z)
    unfold reorderOne
    simp [hd, doSwap_three, doSwap_two, hsw3, hsw2]
  have hstep1 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 1 (Operand.Var y)
      { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y] }
      = ([StackOp.SOSwap 1],
         { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
    have h := reorderOne_dist0 (targetOps := [Operand.Var z, Operand.Var y, Operand.Var x])
      (idx := 1) (op := Operand.Var y)
      (ps := { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y] })
      (f := 1) rfl
      (stackGetDepth_quad_tos base (Operand.Var x) (Operand.Var z) (Operand.Var x) (Operand.Var y))
      (by decide) (by decide)
    rw [h]
    rw [show stackSwap 1 (base ++ [Operand.Var x, Operand.Var z, Operand.Var x, Operand.Var y])
          = base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] from
        stackSwap_1_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var x) (Operand.Var y)]
  have hstep2 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 2 (Operand.Var x)
      { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] }
      = ([], { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var x)
        (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var x]) = some 0
    exact stackGetDepth_quad_tos base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var x)
  unfold reorderPlan
  have henum : ([Operand.Var z, Operand.Var y, Operand.Var x]).enum
      = [(0, Operand.Var z), (1, Operand.Var y), (2, Operand.Var x)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, hstep2, List.append_nil,
    List.nil_append]
  rfl

/-- Deepest `x` in the mid-spilled intermediate `base ++ [x, z, y, y]` is at depth 3. -/
theorem stackGetDepth_quad_deepest' (base : List Operand) (x z y : String)
    (hxz : x ≠ z) (hxy : x ≠ y) :
    stackGetDepth (Operand.Var x)
      (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y]) = some 3 := by
  rw [show base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y]
        = (((base ++ [Operand.Var x]) ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var y]
        from by simp,
      stackGetDepth_append_ne (((base ++ [Operand.Var x]) ++ [Operand.Var z]) ++ [Operand.Var y]) hxy,
      stackGetDepth_append_ne ((base ++ [Operand.Var x]) ++ [Operand.Var z]) hxy,
      stackGetDepth_append_ne (base ++ [Operand.Var x]) hxz,
      stackGetDepth_snoc_self]; rfl

/-- Deepest `z` in a mid-spilled ternop emit stack `base ++ [z, y, y, x]` is at depth 3. -/
theorem stackGetDepth_quad_deepest'' (base : List Operand) (z y x : String)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    stackGetDepth (Operand.Var z)
      (base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x]) = some 3 := by
  rw [show base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x]
        = (((base ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var y]) ++ [Operand.Var x]
        from by simp,
      stackGetDepth_append_ne (((base ++ [Operand.Var z]) ++ [Operand.Var y]) ++ [Operand.Var y]) hzx,
      stackGetDepth_append_ne ((base ++ [Operand.Var z]) ++ [Operand.Var y]) hzy,
      stackGetDepth_append_ne (base ++ [Operand.Var z]) hzy,
      stackGetDepth_snoc_self]; rfl

/-- **Mid-spilled ternop reorder.** For target `[Var z, Var y, Var x]` on `base ++ [z, y, y, x]`
    (the spilled `y` restored+DUP'd between the live DUPs), `reorderPlan` synthesises
    `SWAP3 ; SWAP2 ; SWAP1 ; SWAP3`: the deep `z` moves to its target (two swaps), the `SWAP1`
    exchanges the two equal `y` copies (a stack no-op), and the final `SWAP3` lifts `x` from the
    bottom of the working region to TOS — leaving `base ++ [y, z, y, x]`, positioned over the kept
    `y`. -/
theorem reorderPlan_ternop_midspilled (base : List Operand) (x y z : String) (ps : PlanState)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hstack : ps.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var y, Operand.Var x]) :
    reorderPlan [Operand.Var z, Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOSwap 3],
         { ps with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
  have hstep0 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 0 (Operand.Var z) ps
      = ([StackOp.SOSwap 3, StackOp.SOSwap 2],
         { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] }) := by
    have hd : stackGetDepth (Operand.Var z) ps.stack = some 3 := by
      rw [hstack]; exact stackGetDepth_quad_deepest'' base z y x (Ne.symm hyz) (Ne.symm hxz)
    have hsw3 : stackSwap 3 ps.stack
        = base ++ [Operand.Var x, Operand.Var y, Operand.Var y, Operand.Var z] := by
      rw [hstack]
      exact stackSwap_3_append_quad base (Operand.Var z) (Operand.Var y) (Operand.Var y) (Operand.Var x)
    have hsw2 : stackSwap 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var y, Operand.Var z])
        = base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] :=
      stackSwap_2_append_quad base (Operand.Var x) (Operand.Var y) (Operand.Var y) (Operand.Var z)
    unfold reorderOne
    simp [hd, doSwap_three, doSwap_two, hsw3, hsw2]
  have hstep1 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 1 (Operand.Var y)
      { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] }
      = ([StackOp.SOSwap 1],
         { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] }) := by
    have h := reorderOne_dist0 (targetOps := [Operand.Var z, Operand.Var y, Operand.Var x])
      (idx := 1) (op := Operand.Var y)
      (ps := { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] })
      (f := 1) rfl
      (stackGetDepth_quad_tos base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var y))
      (by decide) (by decide)
    rw [h]
    rw [show stackSwap 1 (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y])
          = base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] from
        stackSwap_1_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var y)]
  have hstep2 : reorderOne () [Operand.Var z, Operand.Var y, Operand.Var x] 2 (Operand.Var x)
      { ps with stack := base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y] }
      = ([StackOp.SOSwap 3],
         { ps with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
    have hd : stackGetDepth (Operand.Var x)
        (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y]) = some 3 :=
      stackGetDepth_quad_deepest' base x z y hxz hxy
    have hsw3 : stackSwap 3 (base ++ [Operand.Var x, Operand.Var z, Operand.Var y, Operand.Var y])
        = base ++ [Operand.Var y, Operand.Var z, Operand.Var y, Operand.Var x] :=
      stackSwap_3_append_quad base (Operand.Var x) (Operand.Var z) (Operand.Var y) (Operand.Var y)
    have hds0 : doSwap 0 ({ ps with stack := base ++ [Operand.Var y, Operand.Var z, Operand.Var y,
        Operand.Var x] } : PlanState) = ([], { ps with stack := base ++ [Operand.Var y,
        Operand.Var z, Operand.Var y, Operand.Var x] }) := by
      rw [doSwap, if_pos rfl]
    unfold reorderOne
    simp [hd, doSwap_three, hsw3, hds0]
  unfold reorderPlan
  have henum : ([Operand.Var z, Operand.Var y, Operand.Var x]).enum
      = [(0, Operand.Var z), (1, Operand.Var y), (2, Operand.Var x)] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, hstep2, List.nil_append]
  rfl

/-- **Both-spilled binop reorder — swapped (commutative) order.** For target `[Var x, Var y]`
    (picked on the `reorderCost` tie) and emit stack `base ++ [y, y, x, x]`, `reorderPlan`
    synthesises `SWAP1 ; SWAP2` (SWAP1 transposes the two equal `x`'s, a stack no-op; SWAP2
    rotates a deep `y` to TOS) leaving `base ++ [y, x, x, y]`. -/
theorem reorderPlan_bothspilled_swapped (base : List Operand) (x y : String) (ps : PlanState) (hxy : x ≠ y)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var x, Operand.Var y] ps
      = ([StackOp.SOSwap 1, StackOp.SOSwap 2],
         { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }) := by
  have hstep0 : reorderOne () [Operand.Var x, Operand.Var y] 0 (Operand.Var x) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] }) := by
    have hd : stackGetDepth (Operand.Var x) ps.stack = some 0 := by
      rw [hstack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
            = (base ++ [Operand.Var y, Operand.Var y, Operand.Var x]) ++ [Operand.Var x] from by simp,
          stackGetDepth_snoc_self]
    have hsw1 : stackSwap 1 ps.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] := by
      rw [hstack, show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
            = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
          stackSwap_1_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_one, hsw1]
  have hstep1 : reorderOne () [Operand.Var x, Operand.Var y] 1 (Operand.Var y)
      { ps with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x] }
      = ([StackOp.SOSwap 2], { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    have hd : stackGetDepth (Operand.Var y)
        (base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]) = some 2 :=
      stackGetDepth_quad_deep base y x (Ne.symm hxy)
    have hsw2 : stackSwap 2 (base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x])
        = base ++ [Operand.Var y, Operand.Var x, Operand.Var x, Operand.Var y] := by
      rw [show base ++ [Operand.Var y, Operand.Var y, Operand.Var x, Operand.Var x]
            = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x, Operand.Var x] from by simp,
          stackSwap_2_append_triple (base ++ [Operand.Var y]) (Operand.Var y) (Operand.Var x) (Operand.Var x)]
      simp
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_two, hsw2]
  unfold reorderPlan
  have henum : ([Operand.Var x, Operand.Var y]).enum = [(0, Operand.Var x), (1, Operand.Var y)] := rfl
  rw [henum]
  simp [List.foldl_cons, List.foldl_nil, hstep0, hstep1]


theorem emit2_keyspilled {opc nl x y ps base offx d_y}
    (hstack0 : ps.stack = base)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none) (hlivey : nl.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y) (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx) (hlivex : nl.contains x = true) :
    (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var x), alloc := freeSpillSlot offx ps.alloc } := by
  have hpeeky : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupy : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeeky]
  set ps1 : PlanState := { ps with stack := stackDup d_y ps.stack } with hps1def
  have hdd : doDup d_y ps = ([StackOp.SODup (d_y + 1)], ps1) := by rw [hps1def]; unfold doDup; rw [if_pos hsmall_y]
  have hhead : emitOneInput opc nl (Operand.Var y) ps = ([StackOp.SODup (d_y + 1)], ps1) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospill_y, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivey, if_true, hdepth_y, hdd, List.nil_append]
  have hps1stack : ps1.stack = ps.stack ++ [Operand.Var y] := by rw [hps1def, hdupy]
  have hspillx1 : alookup' ps1.spilled (Operand.Var x) = some offx := by rw [hps1def]; exact hspill_x
  have htail : emitOneInput opc nl (Operand.Var x) ps1
      = ([StackOp.SORestore offx, StackOp.SODup 1],
         { ps1 with stack := ps1.stack ++ [Operand.Var x, Operand.Var x],
                    spilled := aremove ps1.spilled (Operand.Var x), alloc := freeSpillSlot offx ps1.alloc }) :=
    emitOneInput_var_spilled_eq hspillx1 hlivex
  have hemit2 : (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { ps1 with stack := ps1.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps1.spilled (Operand.Var x), alloc := freeSpillSlot offx ps1.alloc } := by
    unfold emitInputPlan; simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hemit2, hps1stack, hstack0, hps1def]; simp

/-- **Key-spilled store plan reduction.** `SSTORE x y`, key `x` spilled, value `y` live: emit leaves
    `base ++ [y, x, x]`, the reorder is the non-trivial `SWAP2 ; SWAP1` (`reorderPlan_keyspilled`)
    giving `base ++ [x, y, x]`, `stackPop 2` leaves `base ++ [x]` (the kept restored key). -/
theorem genRegularInstPlan_sstore_keyspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y : String} {base : List Operand} {name : String} {offx d_y : Nat}
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
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
           ++ [StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
             stack := base ++ [Operand.Var x] }) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [← h2, hemit2]
  have hreorder : reorderPlan [Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_keyspilled base x y ps1 hxy hps1stack
  have hpop2 : stackPop 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var x]) = base ++ [Operand.Var x] := by
    rw [show base ++ [Operand.Var x, Operand.Var y, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]
  simp [generateEmitOps_evmName hname, hreorder, hpop2, hncomm, hnjmp]

/-- **`reorderOne` on a TOS operand: its plan-stack effect is `stackSwap finalDist`.** When `op` is the
    TOS (`stackGetDepth op = some 0`) and the final depth is in range, `reorderOne` leaves
    `stackSwap (targetOps.length - 1 - idx) ps.stack` — uniformly (the `finalDist = 0` case is
    `stackSwap 0 = id`). No distinctness needed. -/
theorem reorderOne_tos_stack {targetOps : List Operand} {idx : Nat} {op : Operand} {ps : PlanState}
    (hd : stackGetDepth op ps.stack = some 0)
    (hfd : targetOps.length - 1 - idx < ps.stack.length) :
    (reorderOne () targetOps idx op ps).2.stack
      = stackSwap (targetOps.length - 1 - idx) ps.stack := by
  unfold reorderOne
  simp only [hd]
  by_cases hf0 : targetOps.length - 1 - idx = 0
  · rw [if_pos hf0.symm, hf0, stackSwap_zero]
  · rw [if_neg (fun h => hf0 h.symm)]
    show (doSwap (targetOps.length - 1 - idx) (doSwap 0 ps).2).2.stack = _
    rw [doSwap_zero]
    exact doSwap_stack_ne0 hf0 hfd

/-- **The fold invariant for the general rotation.** Processing the tail of the `reorderPlan` fold
    (`zipIdx`-entries `(op, idx)` of `suf.zipIdx pre.length`) from a stack `base ++ pre ++ rotate1 suf`
    yields `base ++ pre ++ suf = base ++ T`. Each step's operand is the TOS of the active segment
    (`rotate1` puts it there), so `reorderOne` swaps it to the segment's deepest slot
    (`stackSwap_endpoints`) without touching `base ++ pre` (`stackSwap_append_right`), extending the
    placed prefix by one. No nodup needed. -/
theorem reorderPlan_rotate_aux (T base : List Operand) :
    ∀ (suf pre : List Operand) (acc : List StackOp) (ps : PlanState),
    T = pre ++ suf →
    ps.stack = base ++ pre ++ rotate1 suf →
    (List.foldl (fun (a : List StackOp × PlanState) (p : Operand × Nat) =>
       (a.1 ++ (reorderOne () T p.2 p.1 a.2).1, (reorderOne () T p.2 p.1 a.2).2))
       (acc, ps) (suf.zipIdx pre.length)).2.stack = base ++ T := by
  intro suf
  induction suf with
  | nil =>
    intro pre acc ps hT hstk
    simp only [List.zipIdx_nil, List.foldl_nil]
    rw [hstk]; simp only [rotate1, List.append_nil]
    rw [hT]; simp
  | cons op rest ih =>
    intro pre acc ps hT hstk
    rw [show (op :: rest).zipIdx pre.length = (op, pre.length) :: rest.zipIdx (pre.length + 1) from rfl,
        List.foldl_cons]
    have hstk_snoc : ps.stack = base ++ pre ++ rest ++ [op] := by
      rw [hstk]; simp only [rotate1]; rw [← List.append_assoc]
    have hstk_split : ps.stack = (base ++ pre) ++ (rest ++ [op]) := by
      rw [hstk]; simp only [rotate1]
    have hlen : T.length - 1 - pre.length = rest.length := by
      have hTl : T.length = pre.length + (rest.length + 1) := by
        rw [hT]; simp only [List.length_append, List.length_cons]
      omega
    have hdep : stackGetDepth op ps.stack = some 0 := by
      rw [hstk_snoc]; exact stackGetDepth_snoc_self op (base ++ pre ++ rest)
    have hfd : T.length - 1 - pre.length < ps.stack.length := by
      rw [hlen, hstk_snoc]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hps'stk : (reorderOne () T pre.length op ps).2.stack
        = base ++ (pre ++ [op]) ++ rotate1 rest := by
      rw [reorderOne_tos_stack hdep hfd, hlen, hstk_split]
      rw [stackSwap_append_right (base ++ pre) (rest ++ [op]) rest.length (by simp)]
      cases rest with
      | nil =>
        simp only [rotate1, List.length_nil, List.nil_append]
        rw [stackSwap_zero]; simp [List.append_assoc]
      | cons r rs =>
        have hsw : stackSwap (r :: rs).length ((r :: rs) ++ [op]) = op :: (rs ++ [r]) := by
          show stackSwap (rs.length + 1) (r :: (rs ++ [op])) = op :: (rs ++ [r])
          exact stackSwap_endpoints r op rs
        rw [hsw]
        simp [rotate1, List.append_assoc]
    have hrec := ih (pre ++ [op]) (acc ++ (reorderOne () T pre.length op ps).1)
      (reorderOne () T pre.length op ps).2 (by rw [hT]; simp) hps'stk
    rw [show pre.length + 1 = (pre ++ [op]).length from by simp]
    exact hrec

/-- **General single-rotation join reconciliation (`perm_reaches`, any length).** For any target entry
    layout `T` and a predecessor that leaves the single left-rotation `rotate1 T` on top of the stack
    (`base ++ rotate1 T`), `reorderPlan T` synthesises `base ++ T`. Generalises `reorderPlan_3cycle_var`
    (`T = [a,b,c]`, `rotate1 = [b,c,a]`) and `reorderPlan_4rotate_var` (`T = [a,b,c,d]`) to arbitrary
    length. Needs **no distinctness / nodup** — the rotation keeps the operand to place at the TOS at
    every step, so each `reorderOne` locates it unconditionally. -/
theorem reorderPlan_rotate (T base : List Operand) (ps : PlanState)
    (hstk : ps.stack = base ++ rotate1 T) :
    (reorderPlan T ps).2.stack = base ++ T := by
  unfold reorderPlan
  rw [show T.enum = (T.zipIdx 0).map (fun p => (p.2, p.1)) from rfl, List.foldl_map]
  exact reorderPlan_rotate_aux T base T [] [] ps (by simp) (by simpa using hstk)

/-- The asm stack holds the four top plan vars' values (`base ++ [Var z, Var y, Var x, Var w]`, `w`=TOS).
    The 4-input twin of `venomAsmRel_asmStack_top3_var`. -/
theorem venomAsmRel_asmStack_top4_var {lo ps vs as} {base : List Operand} {w x y z : String}
    {ww wx wy wz : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x, Operand.Var w])
    (hvw : operandVal vs lo (Operand.Var w) = some ww)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz) :
    as.stack = ww :: wx :: wy :: wz :: as.stack.drop 4 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 4 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = ww := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_quad, hvw] at hp
    exact (Option.some.inj hp).symm
  have h1 : as.stack[1]! = wx := by
    have hp := planStackRel_peek hStk (dist := 1) (by rw [hstack]; simp)
    rw [hstack, stackPeek_1_append_quad, hvx] at hp
    exact (Option.some.inj hp).symm
  have h2 : as.stack[2]! = wy := by
    have hp := planStackRel_peek hStk (dist := 2) (by rw [hstack]; simp)
    rw [hstack, stackPeek_2_append_quad, hvy] at hp
    exact (Option.some.inj hp).symm
  have h3 : as.stack[3]! = wz := by
    have hp := planStackRel_peek hStk (dist := 3) (by rw [hstack]; simp)
    rw [hstack, stackPeek_3_append_quad, hvz] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get4 as.stack hge]
  rw [h0, h1, h2, h3]

/-- The N-input emitter specialised to four vars — the quad twin of `emitInputPlan_triple_var_eq`. -/
theorem emitInputPlan_quad_var_eq {opc nl w z y x ps d_w d_z d_y d_x}
    (hnospill_w : alookup' ps.spilled (Operand.Var w) = none)
    (hlivew : nl.contains w = true)
    (hdepth_w : stackGetDepth (Operand.Var w) ps.stack = some d_w)
    (hsmall_w : d_w ≤ 15)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nl.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) (stackDup d_w ps.stack) = some d_z)
    (hsmall_z : d_z ≤ 15)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) (stackDup d_z (stackDup d_w ps.stack)) = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) (stackDup d_y (stackDup d_z (stackDup d_w ps.stack))) = some d_x)
    (hsmall_x : d_x ≤ 15) :
    emitInputPlan opc [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] nl ps
      = ([StackOp.SODup (d_w + 1), StackOp.SODup (d_z + 1), StackOp.SODup (d_y + 1), StackOp.SODup (d_x + 1)],
         { ps with stack := ps.stack ++ [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] }) := by
  have hdupW : stackDup d_w ps.stack = ps.stack ++ [Operand.Var w] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_w]
  have hdz : stackGetDepth (Operand.Var z) (ps.stack ++ [Operand.Var w]) = some d_z := hdupW ▸ hdepth_z
  have hdupZ : stackDup d_z (ps.stack ++ [Operand.Var w]) = (ps.stack ++ [Operand.Var w]) ++ [Operand.Var z] := by
    unfold stackDup; rw [stackGetDepth_peek hdz]
  have hdy : stackGetDepth (Operand.Var y) ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) = some d_y := by
    rw [← hdupZ, ← hdupW]; exact hdepth_y
  have hdupY : stackDup d_y ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z])
      = ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdy]
  have hdx : stackGetDepth (Operand.Var x) (((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) ++ [Operand.Var y]) = some d_x := by
    rw [← hdupY, ← hdupZ, ← hdupW]; exact hdepth_x
  have h := emitInputPlan_allVars_eq opc nl [w, z, y, x] [d_w, d_z, d_y, d_x] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl; exacts [hnospill_w, hnospill_z, hnospill_y, hnospill_x])
    ⟨hlivew, hdepth_w, hsmall_w, hlivez, hdz, hsmall_z, hlivey, hdy, hsmall_y, hlivex, hdx, hsmall_x, trivial⟩
  simpa using h

/-- `reorderPlan [Var a, Var b, Var c, Var d]` is a no-op when the quad is already positioned. The
    4-input twin of `reorderPlan_triple_var_nil`. -/
theorem reorderPlan_quad_var_nil (base : List Operand) (a b c d : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    reorderPlan [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] ps = ([], ps) := by
  have hba : (Operand.Var b == Operand.Var a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hab (Operand.Var.inj h).symm
  have hca : (Operand.Var c == Operand.Var a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hac (Operand.Var.inj h).symm
  have hda : (Operand.Var d == Operand.Var a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact had (Operand.Var.inj h).symm
  have hcb : (Operand.Var c == Operand.Var b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hbc (Operand.Var.inj h).symm
  have hdb : (Operand.Var d == Operand.Var b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hbd (Operand.Var.inj h).symm
  have hdc : (Operand.Var d == Operand.Var c) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hcd (Operand.Var.inj h).symm
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  have henum : ([Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]).enum
      = [(0, Operand.Var a), (1, Operand.Var b), (2, Operand.Var c), (3, Operand.Var d)] := rfl
  rw [henum] at hp
  rw [hstack]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · show stackGetDepth (Operand.Var a)
      (base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) = some 3
    simp [stackGetDepth, stackFind, List.reverse_append, hba, hca, hda]
  · show stackGetDepth (Operand.Var b)
      (base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) = some 2
    simp [stackGetDepth, stackFind, List.reverse_append, hcb, hdb]
  · show stackGetDepth (Operand.Var c)
      (base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) = some 1
    simp [stackGetDepth, stackFind, List.reverse_append, hdc]
  · show stackGetDepth (Operand.Var d)
      (base ++ [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d]) = some 0
    simp [stackGetDepth, stackFind, List.reverse_append]

/-- `reorderPlan [Var a, Var b, Var c]` is a no-op when that triple is already positioned (`Var a`
    at depth 2, `Var b` at depth 1, `Var c` at depth 0). The 3-input counterpart of
    `reorderPlan_pair_var_nil`. -/
theorem reorderPlan_triple_var_nil (base : List Operand) (a b c : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var a, Operand.Var b, Operand.Var c])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    reorderPlan [Operand.Var a, Operand.Var b, Operand.Var c] ps = ([], ps) := by
  have hba : (Operand.Var b == Operand.Var a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hab (Operand.Var.inj h).symm
  have hca : (Operand.Var c == Operand.Var a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hac (Operand.Var.inj h).symm
  have hcb : (Operand.Var c == Operand.Var b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hbc (Operand.Var.inj h).symm
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  have henum : ([Operand.Var a, Operand.Var b, Operand.Var c]).enum
      = [(0, Operand.Var a), (1, Operand.Var b), (2, Operand.Var c)] := rfl
  rw [henum] at hp
  rw [hstack]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · show stackGetDepth (Operand.Var a) (base ++ [Operand.Var a, Operand.Var b, Operand.Var c]) = some 2
    simp [stackGetDepth, stackFind, List.reverse_append, hba, hca]
  · show stackGetDepth (Operand.Var b) (base ++ [Operand.Var a, Operand.Var b, Operand.Var c]) = some 1
    simp [stackGetDepth, stackFind, List.reverse_append, hcb]
  · show stackGetDepth (Operand.Var c) (base ++ [Operand.Var a, Operand.Var b, Operand.Var c]) = some 0
    simp [stackGetDepth, stackFind, List.reverse_append]

/-- With plan stack `base ++ [Var z, Var y, Var x]` and `x`/`y`/`z` valued `wx`/`wy`/`wz` in `vs`,
    the asm stack top three are `wx` (TOS), `wy`, `wz`. The 3-input counterpart of
    `venomAsmRel_asmStack_top2_var`. -/
theorem venomAsmRel_asmStack_top3_var {lo ps vs as} {base : List Operand} {x y z : String}
    {wx wy wz : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x])
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz) :
    as.stack = wx :: wy :: wz :: as.stack.drop 3 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 3 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = wx := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_triple, hvx] at hp
    exact (Option.some.inj hp).symm
  have h1 : as.stack[1]! = wy := by
    have hp := planStackRel_peek hStk (dist := 1) (by rw [hstack]; simp)
    rw [hstack, stackPeek_1_append_triple, hvy] at hp
    exact (Option.some.inj hp).symm
  have h2 : as.stack[2]! = wz := by
    have hp := planStackRel_peek hStk (dist := 2) (by rw [hstack]; simp)
    rw [hstack, stackPeek_2_append_triple, hvz] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get3 as.stack hge]
  rw [h0, h1, h2]

/-- `get!` in `getElem?` form for a valid index (bytes32). -/
private theorem getbang? (l : List bytes32) (i : Nat) (hi : i < l.length) :
    l[i]? = some (l[i]!) := by
  simp [List.getElem?_eq_getElem hi, List.getElem!_eq_getElem?_getD]

/-- `get!` past an append-left (Operand). -/
private theorem get!_append_left_op (l1 l2 : List Operand) (i : Nat) (hi : i < l1.length) :
    (l1 ++ l2)[i]! = l1[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]

/-- `get!` commutes with `map` at a valid index. -/
private theorem get!_mapD {α β} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    (l.map f)[i]! = f (l[i]!) := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]

/-- **The asm stack top equals the reversed operand values.** For `ps.stack = base ++ os`, the top
    `os.length` entries of the asm stack are the values of `os.reverse` (top-to-bottom), so
    `as.stack = ws ++ as.stack.drop os.length` when `os.reverse`'s operand values are `ws`. The N-input
    generalisation of the fixed-arity `venomAsmRel_asmStack_top2/3_var`, driven by `planStackRel`'s
    per-position value correspondence rather than per-depth `stackPeek` unfolding. -/
theorem venomAsmRel_asmStack_topVals {lo ps vs as} {base os : List Operand} {ws : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ os)
    (hvals : os.reverse.map (fun o => operandVal vs lo o) = ws.map some) :
    as.stack = ws ++ as.stack.drop os.length := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hwlen : os.length = ws.length := by
    have := congrArg List.length hvals
    simpa [List.length_map, List.length_reverse] using this
  have hoslen : os.length ≤ as.stack.length := by
    rw [← hlen, hstack, List.length_append]; omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < os.length
  · have hilen : i < as.stack.length := by omega
    have hiw : i < ws.length := by omega
    have hrevlen : i < os.reverse.length := by rw [List.length_reverse]; exact hi
    have hps : operandVal vs lo (os.reverse[i]!) = some (as.stack[i]!) := by
      have h := hStk.2 i (by rw [hstack, List.length_append]; omega)
      rw [hstack, List.reverse_append, get!_append_left_op os.reverse base.reverse i hrevlen] at h
      exact h
    have hvi : operandVal vs lo (os.reverse[i]!) = some (ws[i]!) := by
      have hm := congrArg (fun l => l[i]!) hvals
      rw [get!_mapD (fun o => operandVal vs lo o) os.reverse i hrevlen,
          get!_mapD some ws i hiw] at hm
      exact hm
    have hasw : as.stack[i]! = ws[i]! := Option.some.inj (hps ▸ hvi)
    rw [getbang? as.stack i hilen, List.getElem?_append_left hiw, getbang? ws i hiw, hasw]
  · push Not at hi
    rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1
    omega

/-- Input-emission sim for a var triple `[Var z, Var y, Var x]` (all live, non-spilled): run the
    three `DUP`s (composes three `doDup_sim`s). The 3-input counterpart of
    `emitInputPlan_pair_var_sim`; each later operand's depth lives in the post-previous-DUP stack. -/
theorem emitInputPlan_triple_var_sim {opc nl x y z ps lo vs as prog d_z d_y' d_x''}
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nl.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15)
    (_hlenz : d_z < ps.stack.length)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15)
    (_hleny' : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15)
    (_hlenx'' : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x]
             nl ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2
             vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc
             [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1).length := by
  have hdupZ : stackDup d_z ps.stack = ps.stack ++ [Operand.Var z] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_z]
  have hdy : stackGetDepth (Operand.Var y) (ps.stack ++ [Operand.Var z]) = some d_y' := hdupZ ▸ hdepth_y'
  have hdupY : stackDup d_y' (ps.stack ++ [Operand.Var z]) = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdy]
  have hdx : stackGetDepth (Operand.Var x) ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) = some d_x'' := by
    rw [← hdupY, ← hdupZ]; exact hdepth_x''
  obtain ⟨as', h1, h2, h3, _⟩ := emitInputPlan_allVars_sim (offsetToPc := offsetToPc) opc nl [z, y, x] [d_z, d_y', d_x''] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl; exacts [hnospill_z, hnospill_y, hnospill_x])
    ⟨hlivez, hdepth_z, hsmall_z, hlivey, hdy, hsmall_y, hlivex, hdx, hsmall_x, trivial⟩ hrel hblock
  exact ⟨as', by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- Memory-augmented triple input emission: the 3 DUPs preserve asm memory (`doDup_runAsm_mem` × 3).
    The 3-input analog of `emitInputPlan_pair_var_sim`'s `hmemI`. -/
theorem emitInputPlan_triple_var_sim_mem {opc nl x y z ps lo vs as prog d_z d_y' d_x''}
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nl.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15)
    (_hlenz : d_z < ps.stack.length)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15)
    (_hleny' : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15)
    (_hlenx'' : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1).length ∧
           as'.memory = as.memory := by
  have hdupZ : stackDup d_z ps.stack = ps.stack ++ [Operand.Var z] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_z]
  have hdy : stackGetDepth (Operand.Var y) (ps.stack ++ [Operand.Var z]) = some d_y' := hdupZ ▸ hdepth_y'
  have hdupY : stackDup d_y' (ps.stack ++ [Operand.Var z]) = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdy]
  have hdx : stackGetDepth (Operand.Var x) ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) = some d_x'' := by
    rw [← hdupY, ← hdupZ]; exact hdepth_x''
  have h := emitInputPlan_allVars_sim (offsetToPc := offsetToPc) opc nl [z, y, x] [d_z, d_y', d_x''] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl; exacts [hnospill_z, hnospill_y, hnospill_x])
    ⟨hlivez, hdepth_z, hsmall_z, hlivey, hdy, hsmall_y, hlivex, hdx, hsmall_x, trivial⟩ hrel hblock
  simpa using h

/-- The quad twin of `emitInputPlan_triple_var_sim_mem` — the 4-var input emission runs OK, preserves
    `venomAsmRel`, and leaves memory unchanged (four DUPs). -/
theorem emitInputPlan_quad_var_sim_mem {opc nl w z y x ps lo vs as prog d_w d_z d_y d_x}
    (hnospill_w : alookup' ps.spilled (Operand.Var w) = none)
    (hlivew : nl.contains w = true)
    (hdepth_w : stackGetDepth (Operand.Var w) ps.stack = some d_w)
    (hsmall_w : d_w ≤ 15)
    (_hlenw : d_w < ps.stack.length)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nl.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) (stackDup d_w ps.stack) = some d_z)
    (hsmall_z : d_z ≤ 15)
    (_hlenz : d_z < (stackDup d_w ps.stack).length)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) (stackDup d_z (stackDup d_w ps.stack)) = some d_y)
    (hsmall_y : d_y ≤ 15)
    (_hleny : d_y < (stackDup d_z (stackDup d_w ps.stack)).length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) (stackDup d_y (stackDup d_z (stackDup d_w ps.stack))) = some d_x)
    (hsmall_x : d_x ≤ 15)
    (_hlenx : d_x < (stackDup d_y (stackDup d_z (stackDup d_w ps.stack))).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var w, Operand.Var z, Operand.Var y, Operand.Var x] nl ps).1).length ∧
           as'.memory = as.memory := by
  have hdupW : stackDup d_w ps.stack = ps.stack ++ [Operand.Var w] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_w]
  have hdz : stackGetDepth (Operand.Var z) (ps.stack ++ [Operand.Var w]) = some d_z := hdupW ▸ hdepth_z
  have hdupZ : stackDup d_z (ps.stack ++ [Operand.Var w]) = (ps.stack ++ [Operand.Var w]) ++ [Operand.Var z] := by
    unfold stackDup; rw [stackGetDepth_peek hdz]
  have hdy : stackGetDepth (Operand.Var y) ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) = some d_y := by
    rw [← hdupZ, ← hdupW]; exact hdepth_y
  have hdupY : stackDup d_y ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z])
      = ((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdy]
  have hdx : stackGetDepth (Operand.Var x) (((ps.stack ++ [Operand.Var w]) ++ [Operand.Var z]) ++ [Operand.Var y]) = some d_x := by
    rw [← hdupY, ← hdupZ, ← hdupW]; exact hdepth_x
  have h := emitInputPlan_allVars_sim (offsetToPc := offsetToPc) opc nl [w, z, y, x] [d_w, d_z, d_y, d_x] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl; exacts [hnospill_w, hnospill_z, hnospill_y, hnospill_x])
    ⟨hlivew, hdepth_w, hsmall_w, hlivez, hdz, hsmall_z, hlivey, hdy, hsmall_y, hlivex, hdx, hsmall_x, trivial⟩ hrel hblock
  simpa using h

/-- Plan reduction for a no-output 3-var op (the copies): `3 DUPs ++ [SOEmit name]`, plan state popped
    back to `base` then `releaseDeadSpills`. The 3-input analog of `genRegularInstPlan_sstore_eq`. -/
theorem genRegularInstPlan_copy_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {a b c : String} {base : List Operand} {name : String} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none)
    (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z)
    (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none)
    (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y')
    (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none)
    (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_a : d_x'' ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base }) := by
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  have hpvar := emitInputPlan_triple_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname,
        reorderPlan_triple_var_nil base c b a ps1 hps1' (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac),
        hps1', stackPop_3_append_triple, hncomm, hnjmp]

/-- **Structural decomposition of `generateRegularInstPlan` for a 4-input, no-output op** (EXTCODECOPY).
    The 4-input twin of `genRegularInstPlan_copy_eq`: emit four DUPs (`emitInputPlan_quad_var_eq`) + the
    op, no reorder (`reorderPlan_quad_var_nil`), pop 4 (`stackPop_4_append_quad`). -/
theorem genRegularInstPlan_noOutput4Var_ops_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {a b c d : String} {base : List Operand} {name : String}
    {d_d d_c d_b d_a : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d])
    (houts : inst.outputs = [])
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
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base }) := by
  have hrev : inst.operands.reverse = [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  have hpvar := emitInputPlan_quad_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c
    hnospill_b hlive_b hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname,
        reorderPlan_quad_var_nil base d c b a ps1 hps1'
          (Ne.symm hcd) (Ne.symm hbd) (Ne.symm had) (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab),
        hps1', stackPop_4_append_quad, hncomm, hnjmp]

/-- **Structural decomposition of `generateRegularInstPlan` for a LOG** with all-variable operands.
    LOG drops its `Lit` topic-count head then reverses the rest to stack order (offset on top, via
    `computeOperands` = `tail.reverse`), emitting the `n+2` DUPs (`emitInputPlan_allVars_eq`) then
    `LOGn`; no reorder (`reorderPlan_allVars_nil` — already positioned), not commutative, no outputs.
    The arbitrary-arity analog of `genRegularInstPlan_copy_eq`, and the first consumer of the N-input
    emission toolkit. -/
theorem genRegularInstPlan_log_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {es : List String} {dists : List Nat} {tc : bytes32} {base : List Operand}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnd : es.Nodup)
    (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1 ++ [StackOp.SOEmit ("LOG" ++ toString tc.toNat)],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with stack := base }) := by
  have hcL : isCommutative Opcode.LOG = false := rfl
  have hjL : ¬ (Opcode.LOG = Opcode.JMP) := by decide
  have hpvar := emitInputPlan_allVars_eq Opcode.LOG nextLiveness es dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hopc, hhead, hcompute, houts]
  rcases hemit : emitInputPlan Opcode.LOG (es.map Operand.Var) nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ es.map Operand.Var := by
    have h2 : (emitInputPlan Opcode.LOG (es.map Operand.Var) nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [← h2, hpvar, hstack0]
  have hpop : stackPop es.length (base ++ es.map Operand.Var) = base := by
    have h := stackPop_append_top base (es.map Operand.Var); rwa [List.length_map] at h
  simp [hcL, hjL,
        reorderPlan_allVars_nil base es ps1 hps1' hnd,
        hps1', hpop, generateEmitOps_log hopc]

/-- **Runnable LOG sim through the generator** (`n+2` DUPs then `LOGn`), all-variable operands. Consumes
    the N-input toolkit end-to-end: `genRegularInstPlan_log_eq` (plan) → `emitInputPlan_allVars_sim`
    (run the DUPs) → `venomAsmRel_asmStack_topVals` (offset/size/topics land on top) → `emit_log_sim`
    (append the event) → `releaseDeadSpills`. The variable-arity analog of the copy sims. -/
theorem genRegularInstPlan_log_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {es : List String} {dists : List Nat} {tc : bytes32} {base : List Operand}
    {n : Nat} {offset size : bytes32} {topics : List bytes32}
    (hopc : inst.opcode = Opcode.LOG)
    (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var)
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnd : es.Nodup)
    (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack)
    (hlenes : es.length = n + 2)
    (htc : tc.toNat = n)
    (htlen : topics.length = n)
    (hvals : (es.map Operand.Var).reverse.map (fun o => operandVal vs lo o) = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) (hn : n ≤ 4)
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
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts hstack0 hnd hnospill hdepths, hcompute] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode (es.map Operand.Var) nextLiveness ps).2 with hps1def
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness es dists ps hnospill hdepths
  have hps1stack : ps1.stack = base ++ es.map Operand.Var := by rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ :=
    emitInputPlan_allVars_sim inst.opcode nextLiveness es dists ps hnospill hdepths hrel hbI
  have hstacktop : as1.stack = offset :: size :: topics ++ as1.stack.drop (es.map Operand.Var).length :=
    venomAsmRel_asmStack_topVals hrelI hps1stack hvals
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]) := by
    rw [hpcI, ← htc]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_log_sim hrelI hstacktop htlen (by rw [hmemI]; exact hcov) (by rw [hps1alloc]; exact hbelow) hsize hn hbE'
  have hps5 : ({ ps1 with stack := stackPop (n + 2) ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, ← hlenes]
    have h := stackPop_append_top base (es.map Operand.Var); rw [List.length_map] at h; rw [h]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [List.length_append, htc]; exact runAsm_compose hrunI hrunE
  · rw [List.length_append, htc, hpcE, hpcI]; omega

/-- Runnable sim for CALLDATACOPY through the generator (`3 DUPs` then `CALLDATACOPY`). The 3-input
    memory-write analog of the store sims; the source (`calldata`) is bridged to the Venom side. -/
theorem genRegularInstPlan_calldatacopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b c : String} {wa wb wc : bytes32} {base : List Operand} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none)
    (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z)
    (hsmall_c : d_z ≤ 15)
    (hlenc : d_z < ps.stack.length)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none)
    (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y')
    (hsmall_b : d_y' ≤ 15)
    (hlenb : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none)
    (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_a : d_x'' ≤ 15)
    (hlena : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hva : operandVal vs lo (Operand.Var a) = some wa)
    (hvb : operandVal vs lo (Operand.Var b) = some wb)
    (hvc : operandVal vs lo (Operand.Var c) = some wc)
    (hcovV : wa.toNat ≤ vs.memory.size)
    (hcovA : ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wa.toNat + wc.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wc.toNat) (hsize : wc.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps)
      = ([StackOp.SODup (d_z + 1), StackOp.SODup (d_y' + 1), StackOp.SODup (d_x'' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var c, Operand.Var b, Operand.Var a] }) :=
    emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a
  have hps1stack : ps1.stack = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_triple_var_sim_mem hnospill_c hlivec hdepth_c
    hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hrel hbI
  have hstacktop : as1.stack = wa :: wb :: wc :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hva hvb hvc
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALLDATACOPY"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_calldatacopy_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) hpos hsize (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
  have hps5 : ({ ps1 with stack := stackPop 3 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_3_append_triple]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Runnable sim for CODECOPY through the generator (`3 DUPs` then `CODECOPY`). Near-identical to
    `genRegularInstPlan_calldatacopy_sim`; the only difference is the copy source (`vs.code` bridged
    via the `code` conjunct instead of `vs.callCtx.calldata`) and the emitted opcode name. -/
theorem genRegularInstPlan_codecopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b c : String} {wa wb wc : bytes32} {base : List Operand} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CODECOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none)
    (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z)
    (hsmall_c : d_z ≤ 15)
    (hlenc : d_z < ps.stack.length)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none)
    (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y')
    (hsmall_b : d_y' ≤ 15)
    (hlenb : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none)
    (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_a : d_x'' ≤ 15)
    (hlena : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hva : operandVal vs lo (Operand.Var a) = some wa)
    (hvb : operandVal vs lo (Operand.Var b) = some wb)
    (hvc : operandVal vs lo (Operand.Var c) = some wc)
    (hcovV : wa.toNat ≤ vs.memory.size)
    (hcovA : ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wa.toNat + wc.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wc.toNat) (hsize : wc.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (writeMemoryWithExpansion wa.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps)
      = ([StackOp.SODup (d_z + 1), StackOp.SODup (d_y' + 1), StackOp.SODup (d_x'' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var c, Operand.Var b, Operand.Var a] }) :=
    emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a
  have hps1stack : ps1.stack = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_triple_var_sim_mem hnospill_c hlivec hdepth_c
    hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hrel hbI
  have hstacktop : as1.stack = wa :: wb :: wc :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hva hvb hvc
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CODECOPY"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_codecopy_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) hpos hsize (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
  have hps5 : ({ ps1 with stack := stackPop 3 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_3_append_triple]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **EXTCODECOPY instruction sim** — the 4-input account-code → memory copy over the real codegen plan.
    The 4-input twin of `genRegularInstPlan_codecopy_sim`: the quad plan-eq/emit-sim
    (`genRegularInstPlan_noOutput4Var_ops_eq` / `emitInputPlan_quad_var_sim_mem`), the four top values
    via `venomAsmRel_asmStack_top4_var`, then `emit_extcodecopy_sim` (memory coverage threaded through
    `hmemI`/`hps1alloc`, exactly as the copy sims do). -/
theorem genRegularInstPlan_extcodecopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b c d : String} {wa wb wc wd : bytes32} {base : List Operand} {d_d d_c d_b d_a : Nat}
    (hname : opcodeToEvmName inst.opcode = some "EXTCODECOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hstack0 : ps.stack = base)
    (hnospill_d : alookup' ps.spilled (Operand.Var d) = none) (hlive_d : nextLiveness.contains d = true)
    (hdepth_d : stackGetDepth (Operand.Var d) ps.stack = some d_d) (hsmall_d : d_d ≤ 15) (hlend : d_d < ps.stack.length)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlive_c : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) (stackDup d_d ps.stack) = some d_c) (hsmall_c : d_c ≤ 15) (hlenc : d_c < (stackDup d_d ps.stack).length)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hlive_b : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_c (stackDup d_d ps.stack)) = some d_b) (hsmall_b : d_b ≤ 15) (hlenb : d_b < (stackDup d_c (stackDup d_d ps.stack)).length)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlive_a : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_b (stackDup d_c (stackDup d_d ps.stack))) = some d_a) (hsmall_a : d_a ≤ 15) (hlena : d_a < (stackDup d_b (stackDup d_c (stackDup d_d ps.stack))).length)
    (hva : operandVal vs lo (Operand.Var a) = some wa) (hvb : operandVal vs lo (Operand.Var b) = some wb)
    (hvc : operandVal vs lo (Operand.Var c) = some wc) (hvd : operandVal vs lo (Operand.Var d) = some wd)
    (hcovV : wb.toNat ≤ vs.memory.size)
    (hcovA : ((wb.toNat + wd.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wb.toNat + wd.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wd.toNat) (hsize : wd.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (writeMemoryWithExpansion wb.toNat
               ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  rw [genRegularInstPlan_noOutput4Var_ops_eq hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd
      hstack0 hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c hnospill_b hlive_b
      hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps)
      = ([StackOp.SODup (d_d + 1), StackOp.SODup (d_c + 1), StackOp.SODup (d_b + 1), StackOp.SODup (d_a + 1)],
         { ps with stack := ps.stack ++ [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] }) :=
    emitInputPlan_quad_var_eq hnospill_d hlive_d hdepth_d hsmall_d hnospill_c hlive_c hdepth_c hsmall_c
      hnospill_b hlive_b hdepth_b hsmall_b hnospill_a hlive_a hdepth_a hsmall_a
  have hps1stack : ps1.stack = base ++ [Operand.Var d, Operand.Var c, Operand.Var b, Operand.Var a] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_quad_var_sim_mem hnospill_d hlive_d hdepth_d
    hsmall_d hlend hnospill_c hlive_c hdepth_c hsmall_c hlenc hnospill_b hlive_b hdepth_b hsmall_b hlenb
    hnospill_a hlive_a hdepth_a hsmall_a hlena hrel hbI
  have hstacktop : as1.stack = wa :: wb :: wc :: wd :: as1.stack.drop 4 :=
    venomAsmRel_asmStack_top4_var hrelI hps1stack hva hvb hvc hvd
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "EXTCODECOPY"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_extcodecopy_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) hpos hsize (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
  have hps5 : ({ ps1 with stack := stackPop 4 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_4_append_quad]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Runnable sim for RETURNDATACOPY through the generator on the **in-bounds** path (`3 DUPs` then
    `RETURNDATACOPY`). The first copy op with a fault branch: `hnooob` (`srcOff + sz ≤ returndata.size`)
    selects the OK case; out-of-bounds faults on both sides identically and is excluded. Source
    `vs.returndata` bridged via the `returndata` conjunct. -/
theorem genRegularInstPlan_returndatacopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b c : String} {wa wb wc : bytes32} {base : List Operand} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "RETURNDATACOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none)
    (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z)
    (hsmall_c : d_z ≤ 15)
    (hlenc : d_z < ps.stack.length)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none)
    (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y')
    (hsmall_b : d_y' ≤ 15)
    (hlenb : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none)
    (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_a : d_x'' ≤ 15)
    (hlena : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hva : operandVal vs lo (Operand.Var a) = some wa)
    (hvb : operandVal vs lo (Operand.Var b) = some wb)
    (hvc : operandVal vs lo (Operand.Var c) = some wc)
    (hcovV : wa.toNat ≤ vs.memory.size)
    (hcovA : ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wa.toNat + wc.toNat ≤ ps.alloc.fnEom)
    (hnooob : wb.toNat + wc.toNat ≤ vs.returndata.size)
    (hpos : 0 < wc.toNat) (hsize : wc.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (writeMemoryWithExpansion wa.toNat (vs.returndata.readWithPadding wb.toNat wc.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps)
      = ([StackOp.SODup (d_z + 1), StackOp.SODup (d_y' + 1), StackOp.SODup (d_x'' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var c, Operand.Var b, Operand.Var a] }) :=
    emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a
  have hps1stack : ps1.stack = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_triple_var_sim_mem hnospill_c hlivec hdepth_c
    hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hrel hbI
  have hstacktop : as1.stack = wa :: wb :: wc :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hva hvb hvc
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "RETURNDATACOPY"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_returndatacopy_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) hnooob hpos hsize (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
  have hps5 : ({ ps1 with stack := stackPop 3 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_3_append_triple]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Runnable sim for MCOPY through the generator (`3 DUPs` then `MCOPY`). The memory→memory copy: source
    `vs.memory` bridged through `memoryRel` (source-safety `hsrcsafe : srcOff + sz ≤ fnEom`), with `hcovS`
    covering the source window so the asm `max`-expansion is a no-op. -/
theorem genRegularInstPlan_mcopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b c : String} {wa wb wc : bytes32} {base : List Operand} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MCOPY")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c])
    (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none)
    (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z)
    (hsmall_c : d_z ≤ 15)
    (hlenc : d_z < ps.stack.length)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none)
    (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y')
    (hsmall_b : d_y' ≤ 15)
    (hlenb : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none)
    (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_a : d_x'' ≤ 15)
    (hlena : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hva : operandVal vs lo (Operand.Var a) = some wa)
    (hvb : operandVal vs lo (Operand.Var b) = some wb)
    (hvc : operandVal vs lo (Operand.Var c) = some wc)
    (hcovV : wa.toNat ≤ vs.memory.size)
    (hcovA : ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hcovS : ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wa.toNat + wc.toNat ≤ ps.alloc.fnEom)
    (hsrcsafe : wb.toNat + wc.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wc.toNat) (hsize : wc.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (writeMemoryWithExpansion wa.toNat (vs.memory.readWithPadding wb.toNat wc.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var c, Operand.Var b, Operand.Var a] nextLiveness ps)
      = ([StackOp.SODup (d_z + 1), StackOp.SODup (d_y' + 1), StackOp.SODup (d_x'' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var c, Operand.Var b, Operand.Var a] }) :=
    emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a
  have hps1stack : ps1.stack = base ++ [Operand.Var c, Operand.Var b, Operand.Var a] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_triple_var_sim_mem hnospill_c hlivec hdepth_c
    hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hrel hbI
  have hstacktop : as1.stack = wa :: wb :: wc :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hva hvb hvc
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "MCOPY"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_mcopy_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA) (by rw [hmemI]; exact hcovS)
      (by rw [hps1alloc]; exact hsafe) (by rw [hps1alloc]; exact hsrcsafe) hpos hsize
      (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
  have hps5 : ({ ps1 with stack := stackPop 3 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_3_append_triple]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Structural decomposition of `generateRegularInstPlan` for a **non-commutative** binop with two
    distinct *variable* operands (both live, non-spilled). The var counterpart of
    `genRegularInstPlan_nonCommBinopLit_eq`: same plan shape (`base := ps.stack`, inputs DUP'd and
    kept, output kept), but no commutative cheaper-order dispatch. -/
theorem genRegularInstPlan_nonCommBinopVar_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y : String} {out : String} {base : List Operand} {name : String} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hpvar := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1
    rw [← h2]; exact hps1
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_nil base y x ps1 hps1' (Ne.symm hxy),
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- The runnable sim for a **non-commutative** binop with two distinct *variable* operands. The asm
    computes `f wx wy` directly (no commutativity needed) — the var analog of
    `genRegularInstPlan_nonCommBinopLit_sim`, and the case the un-reversed codegen miscompiled. -/
theorem genRegularInstPlan_nonCommBinopVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {d_y d_x' : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hox : out ≠ x)
    (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hlive
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x',
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x', hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x']; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y hsmall_y
    hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **SHA3 instruction sim** — the 2-input memory-hash over the real codegen plan. Same non-commutative
    2-var plan scaffolding as `genRegularInstPlan_nonCommBinopVar_sim`, but the emit is `emit_sha3_sim`
    (reading memory + keccak) rather than a stack binop; the memory-coverage conditions are threaded
    through the input-emission (`hmemI` / `hps1alloc`), exactly as the copy/LOG sims do. -/
theorem genRegularInstPlan_sha3_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand}
    {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SHA3")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hox : out ≠ x)
    (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hcov : ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : wx.toNat + wy.toNat ≤ ps.alloc.fnEom)
    (hsize : wy.toNat < USize.size)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SHA3" →
        asmStep offsetToPc prog s = asmSha3 s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2
             (updateVar out (keccak256 (readMemory wx.toNat wy.toNat vs)) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hlive
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x',
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps)
      = ([StackOp.SODup (d_y + 1), StackOp.SODup (d_x' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var x] }) :=
    emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hpvar]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
    hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SHA3"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_sha3_sim hrelI hstacktop (by rw [hmemI]; exact hcov) (by rw [hps1alloc]; exact hbelow) hsize
      hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-! ## Consume-operand binop: the dead-operand (no-DUP) body atom

The DUP-based `step_S` atoms require both operands to be *live* (DUP'd, kept on the stack). The dual
case — a binop whose operands are **dead** (consumed) — is the one that closes a terminating block:
the last value-producing instruction before a halting terminator necessarily consumes its operands.
For a non-commutative op `c := f x y` with `x, y` dead and already at the top of the stack
(`base ++ [Var y, Var x]`, `x` = TOS — the layout for which `computeOperands`' reversed `[y,x]` needs
no reorder) in a **halting** block, `emitOneInput` emits nothing for each dead operand, the
commutative branch is skipped (`isCommutative = false`), the reorder is a no-op
(`reorderPlan_pair_var_nil`), the dead output isn't popped (`isHalting`), and the optimistic swap is
skipped (dead output) — so the whole plan collapses to a single `[SOEmit name]` that the EVM op
consumes both operands with. This is the missing consume atom that lets a var-operand body precede a
halt. -/

/-- `emitInputPlan` of two dead (non-spilled) variable operands is a no-op (neither is DUP'd). -/
theorem emitInputPlan_pair_var_dead (opc : Opcode) (nl : List String) (x y : String) (ps : PlanState)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nl.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nl.contains x = false) :
    emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps = ([], ps) := by
  have hone_y : emitOneInput opc nl (Operand.Var y) ps = ([], ps) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospill_y, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hdead_y, List.nil_append]
  have hone_x : emitOneInput opc nl (Operand.Var x) ps = ([], ps) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospill_x, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hdead_x, List.nil_append]
  unfold emitInputPlan
  simp only [List.foldl_cons, List.foldl_nil, hone_y, hone_x, List.append_nil]

/-- **Plan decomposition for a consume-operand binop** (dead operands at the top, dead output,
    halting block): the whole plan is a single `[SOEmit name]`, with the post-state stack the base
    with the operands replaced by the output. -/
theorem genRegularInstPlan_consumeBinopVar_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y : String} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base ++ [Operand.Var y, Operand.Var x])
    (hdead_out : nextLiveness.contains out = false)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nextLiveness.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nextLiveness.contains x = false) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness true nextIsTerminator curBbLabel ps
      = ([StackOp.SOEmit name],
         releaseDeadSpills nextLiveness { ps with stack := base ++ [Operand.Var out] }) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit := emitInputPlan_pair_var_dead inst.opcode nextLiveness x y ps
    hnospill_y hdead_y hnospill_x hdead_x
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rw [hemit]
  have hnotmem : out ∉ nextLiveness := by simpa using hdead_out
  simp [generateEmitOps_evmName hname,
    reorderPlan_pair_var_nil base y x ps hstack0 (Ne.symm hxy),
    hstack0, stackPop_2_append_pair, stackPush, hncomm, hnjmp, hnotmem]

/-- **Runnable sim for a consume-operand binop**: the single emitted op consumes the two operands
    (`wx` on TOS, `wy` below — the codegen reversal already put them in semantic order) and pushes
    `f wx wy`, matching the Venom step `vs → updateVar out (f wx wy) vs`. The asm side reuses
    `emit_binop_sim` directly — there are no DUPs to compose. The dead-operand counterpart of
    `genRegularInstPlan_nonCommBinopVar_sim`; this is what discharges the body's last instruction
    before a halt. -/
theorem genRegularInstPlan_consumeBinopVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base ++ [Operand.Var y, Operand.Var x])
    (hfreshbase : ¬ (Operand.Var out) ∈ base)
    (hdead_out : nextLiveness.contains out = false)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nextLiveness.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nextLiveness.contains x = false)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness true
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness true
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness true
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness true nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_consumeBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
        hdead_out hnospill_y hdead_y hnospill_x hdead_x] at hblock ⊢
  have hstacktop : as.stack = wx :: wy :: as.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrel hstack0 hvx hvy
  have hfresh' : ¬ (Operand.Var out) ∈ ps.stack := by
    rw [hstack0]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · exact hfreshbase h
    · exact hoy (Operand.Var.inj h)
    · exact hox (Operand.Var.inj h)
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrel hstacktop hfresh' hspill_out hblock (fun h hg => hdisp as h hg)
  have hps6 : ({ ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) } : PlanState)
      = { ps with stack := base ++ [Operand.Var out] } := by
    rw [hstack0, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, hrunE, hrelR, hpcE⟩

/-! ## Input-emission decomposition for no-output 2-var instructions (RETURN/REVERT/store)

A non-`JMP` instruction with **two variable operands and no output** (RETURN/REVERT, and the store
ops) lowers to exactly the two-operand input-emission followed by a single `SOEmit name`: the
`outputs = []` branch skips the output push / optimistic swap / popmany, the join is empty (non-`JMP`)
and the final reorder is a no-op (the operands are already positioned by `emitInputPlan`). This is the
structural decomposition the terminal/store per-instruction sims compose over. -/

/-- **Plan decomposition** for a no-output 2-var instruction: the emitted ops are the reversed
    two-operand input-emission `++ [SOEmit name]`. (Only the ops `.1` — the post-pop plan state is
    irrelevant for a terminal.) -/
theorem genRegularInstPlan_noOutput2Var_ops_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y : String} {base : List Operand} {name : String} {d_y d_x' : Nat}
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
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
        curBbLabel ps).1
      = (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name] := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hpvar := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname, reorderPlan_pair_var_nil base y x ps1 hps1' (Ne.symm hxy),
        hps1', stackPop_2_append_pair, hncomm, hnjmp]

/-! ## SSTORE through the real generator (a no-output 2-var store)

The full plan reduction + sim for a no-output 2-var op (SSTORE/MSTORE) through `generateRegularInstPlan`:
`2 DUPs ++ [SOEmit name]`, popping the two DUP'd copies back to `base` then `releaseDeadSpills`. The
building block for the *0-output* body-fold producer `bodyStepG_sstore`. -/

/-- Plan reduction for a no-output 2-var op: `2 DUPs ++ [SOEmit name]`, plan state popped back to
    `base` then `releaseDeadSpills`. -/
theorem genRegularInstPlan_sstore_eq
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
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base }) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hpvar := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_nil base y x ps1 hps1' (Ne.symm hxy),
        hps1', stackPop_2_append_pair, hncomm, hnjmp]

/-- Runnable sim for SSTORE through the generator: `2 DUPs` then `SSTORE`, applying `sstore wx wy`. The
    no-output counterpart of `genRegularInstPlan_nonCommBinopVar_sim` (uses `emit_sstore_sim`, no
    output push). -/
theorem genRegularInstPlan_sstore_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
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
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (sstore wx wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x', hstack0]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
    hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_sstore_sim hrelI hstacktop hbE' (fun h hg => hdisp as1 h hg)
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-! ### Same-var store (`x = y`) — the operand-distinctness edge case

`genRegularInstPlan_sstore_eq/_sim` assume `x ≠ y` (the reorder is `[]` via `reorderPlan_pair_var_nil`).
When a store repeats a single var (`SSTORE x x`), the final reorder is one **no-op `SWAP1`**
(`reorderPlan_pair_var_same` — the two copies are equal, so the swap changes neither the plan stack nor
the asm value stack), and both key and value read the same word `wx`. These twins close the `x = y`
coverage gap for the store class (whose `RegularStepG` disjunct is stated only for `x ≠ y`). -/

/-- Plan reduction for a no-output *same-var* 2-input store `[Var x, Var x]`: `2 DUPs ++ [SWAP1, op]`.
    The `x = y` twin of `genRegularInstPlan_sstore_eq`, whose final reorder is one (no-op) `SWAP1`
    (`reorderPlan_pair_var_same`) rather than `[]`. -/
theorem genRegularInstPlan_sstore_same_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x : String} {base : List Operand} {name : String} {d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
           ++ [StackOp.SOSwap 1, StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base }) := by
  have hrev : inst.operands.reverse = [Operand.Var x, Operand.Var x] := by rw [hops]; rfl
  have hd0 : stackGetDepth (Operand.Var x) (stackDup d_x ps.stack) = some 0 :=
    stackGetDepth_stackDup_self ps.stack d_x hdepth_x
  have hpvar := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_x hlivex hdepth_x hsmall_x hnospill_x hlivex hd0 (by omega)
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var x, Operand.Var x] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var x, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps).2 = ps1 := by
      rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_same base x ps1 hps1',
        hps1', stackPop_2_append_pair, hncomm, hnjmp]

/-- Runnable sim for a same-var SSTORE `SSTORE x x` through the generator: `2 DUPs`, a no-op `SWAP1`
    (the two copies are equal), then `SSTORE`, applying `sstore wx wx`. The `x = y` twin of
    `genRegularInstPlan_sstore_sim`; the store reads the same word `wx` for both key and value. -/
theorem genRegularInstPlan_sstore_same_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x : String} {wx : bytes32} {base : List Operand} {d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x ≤ 15)
    (hlenx : d_x < ps.stack.length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (sstore wx wx vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_same_eq hname hncomm hnjmp hcompute hops houts hstack0 hnospill_x hlivex
      hdepth_x hsmall_x, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps).2 with hps1def
  have hd0 : stackGetDepth (Operand.Var x) (stackDup d_x ps.stack) = some 0 :=
    stackGetDepth_stackDup_self ps.stack d_x hdepth_x
  have hps1stack : ps1.stack = base ++ [Operand.Var x, Operand.Var x] := by
    rw [hps1def, emitInputPlan_pair_var_eq hnospill_x hlivex hdepth_x hsmall_x hnospill_x hlivex
      hd0 (by omega), hstack0]
  -- split the block: emit ++ [SWAP1] ++ [SSTORE]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbRest⟩ := asmBlockAt_append hblock
  -- run emit
  obtain ⟨as1, hrunI, hrelI, hpcI, _⟩ := emitInputPlan_pair_var_same_sim (offsetToPc := offsetToPc)
    hnospill_x hlivex hdepth_x hsmall_x hlenx hrel hbI
  -- further split [SWAP1, SSTORE] = [SWAP1] ++ [SSTORE]
  have hbRest2 : asmBlockAt prog
      (as.pc + (executePlan (emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps).1).length)
      (executePlan ([StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"])) := hbRest
  rw [executePlan_append] at hbRest2
  obtain ⟨hbSwap0, hbStore0⟩ := asmBlockAt_append hbRest2
  -- run SWAP1 (a no-op on equal values)
  have hswapstack : stackSwap 1 ps1.stack = ps1.stack := by rw [hps1stack, stackSwap_1_append_pair]
  have hdoSwap : doSwap 1 ps1 = ([StackOp.SOSwap 1], ps1) := by
    unfold doSwap
    rw [if_neg (by decide : ¬ (1 = 0)), if_pos (by decide : 1 ≤ 16)]
    congr 1
    rw [hswapstack]
  have hlen1 : (1 : Nat) < ps1.stack.length := by rw [hps1stack]; simp
  have hbSwap : asmBlockAt prog as1.pc (executePlan [StackOp.SOSwap 1]) := by rw [hpcI]; exact hbSwap0
  obtain ⟨as2, hrunSwap, hrelSwap, hpcSwap⟩ :=
    doSwap_sim (offsetToPc := offsetToPc) hdoSwap hrelI hlen1 hbSwap (by intro h; omega)
  -- as2 still has wx :: wx on top
  have hstacktop2 : as2.stack = wx :: wx :: as2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelSwap hps1stack hvx hvx
  -- run SSTORE
  have hbStore : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by
    rw [hpcSwap, hpcI]; exact hbStore0
  obtain ⟨as3, hrunStore, hrelStore, hpcStore⟩ :=
    emit_sstore_sim hrelSwap hstacktop2 hbStore (fun h hg => hdisp as2 h hg)
  -- assemble
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelStore
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelStore
  have hlenEq : (executePlan ((emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps).1
        ++ [StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"])).length
      = (executePlan (emitInputPlan inst.opcode [Operand.Var x, Operand.Var x] nextLiveness ps).1).length
        + ((executePlan [StackOp.SOSwap 1]).length + (executePlan [StackOp.SOEmit "SSTORE"]).length) := by
    rw [show ([StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"] : List StackOp)
          = [StackOp.SOSwap 1] ++ [StackOp.SOEmit "SSTORE"] from rfl,
       executePlan_append, executePlan_append, List.length_append, List.length_append]
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [hlenEq]; exact runAsm_compose hrunI (runAsm_compose hrunSwap hrunStore)
  · rw [hlenEq, hpcStore, hpcSwap, hpcI]; omega

/-- Runnable sim for TSTORE through the generator — the transient-store twin of
    `genRegularInstPlan_sstore_sim` (reuses the generic `genRegularInstPlan_sstore_eq`; `emit_tstore_sim`
    needs no dispatch hypothesis). -/
theorem genRegularInstPlan_tstore_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TSTORE")
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
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (tstore wx wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x', hstack0]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
    hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "TSTORE"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ := emit_tstore_sim hrelI hstacktop hbE'
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Runnable sim for MSTORE through the generator. Like the shared-state stores but the emit step is a
    *memory* write (`emit_mstore_sim`), so it carries the memory-safety side conditions: the write
    window is covered (`hcovV`/`hcovA`) and below the spill region (`hsafe`), and spill slots are above
    `fnEom` (`hspillReg`, vacuous in the no-spill regime). Reuses the generic `genRegularInstPlan_sstore_eq`. -/
theorem genRegularInstPlan_mstore_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE")
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
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hcovV : wx.toNat ≤ vs.memory.size)
    (hcovA : ((wx.toNat + 32 + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wx.toNat + 32 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (mstore wx.toNat wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps)
      = ([StackOp.SODup (d_y + 1), StackOp.SODup (d_x' + 1)], { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var x] }) :=
    emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
    hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "MSTORE"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_mstore_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
      (fun h hg => hdisp as1 h hg)
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Runnable sim for MSTORE8 through the generator — the single-byte twin of `genRegularInstPlan_mstore_sim`
    (`+1` write window instead of `+32`). -/
theorem genRegularInstPlan_mstore8_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
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
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hcovV : wx.toNat ≤ vs.memory.size)
    (hcovA : ((wx.toNat + 1 + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wx.toNat + 1 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (mstore8 wx.toNat wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hpvar : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps)
      = ([StackOp.SODup (d_y + 1), StackOp.SODup (d_x' + 1)], { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var x] }) :=
    emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, hpvar, hstack0]
  have hps1alloc : ps1.alloc = ps.alloc := by rw [hps1def, hpvar]
  have hps1spill : ps1.spilled = ps.spilled := by rw [hps1def, hpvar]
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
    hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "MSTORE8"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_mstore8_sim hrelI hstacktop hcovV (by rw [hmemI]; exact hcovA)
      (by rw [hps1alloc]; exact hsafe) (by rw [hps1spill, hps1alloc]; exact hspillReg) hbE'
      (fun h hg => hdisp as1 h hg)
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Full per-instruction terminal sim for an empty-returndata `RETURN`** (`sz = 0`): composes the
    input-emission decomposition (`genRegularInstPlan_noOutput2Var_ops_eq`) with the input-emission
    sim (`emitInputPlan_pair_var_sim`) and the compute step (`emit_return_sim`). End to end, running
    the whole `generateRegularInstPlan` plan from `venomAsmRel` reaches `AsmHalt` with the observable
    effects of the Venom `RETURN` (`venomAsmTerminalRel`). The `sz = 0` case needs no memory coverage
    (the returned slice is empty); `ps1.alloc = ps.alloc` (input-emission only DUPs) discharges the
    `fnEom` side condition. -/
theorem genRegularInstPlan_return_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "RETURN")
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
    (hsmall_y : d_y ≤ 15) (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hcov : wy.toNat = 0 ∨ ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hlen : wy.toNat < USize.size)
    (hsafe : wx.toNat + wy.toNat ≤ ps.alloc.fnEom)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
             isHalting nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (setReturndata (readMemory wx.toNat wy.toNat vs) vs)) as' := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_noOutput2Var_ops_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y hsmall_y
    hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hps1eq : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2
      = { ps with stack := base ++ [Operand.Var y, Operand.Var x] } := by
    rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x'
          hsmall_x', hstack0]
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by rw [hps1eq]
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "RETURN"]) := by rw [hpcI]; exact hbE
  have hsafe' : wx.toNat + wy.toNat
      ≤ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.alloc.fnEom := by
    rw [hps1eq]; show wx.toNat + wy.toNat ≤ ps.alloc.fnEom; omega
  have hcov' : wy.toNat = 0 ∨ ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as1.memory.size := by
    rw [hmemI]; exact hcov
  obtain ⟨as2, hrunE, htermE⟩ :=
    emit_return_sim hrelI hstacktop hcov' hsafe' hlen hbE'
  refine ⟨as2, ?_, htermE⟩
  rw [executePlan_append, List.length_append, runAsm_append_ok hrunI]
  exact hrunE

/-- **Full per-instruction terminal sim for an empty-returndata `REVERT`** (`sz = 0`): the
    `AsmRevert` companion of `genRegularInstPlan_return_sim`. -/
theorem genRegularInstPlan_revert_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {d_y d_x' : Nat}
    (hname : opcodeToEvmName inst.opcode = some "REVERT")
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
    (hsmall_y : d_y ≤ 15) (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hcov : wy.toNat = 0 ∨ ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hlen : wy.toNat < USize.size)
    (hsafe : wx.toNat + wy.toNat ≤ ps.alloc.fnEom)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
             isHalting nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel (revertState (setReturndata (readMemory wx.toNat wy.toNat vs) vs)) as' := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_noOutput2Var_ops_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y hsmall_y
    hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hps1eq : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2
      = { ps with stack := base ++ [Operand.Var y, Operand.Var x] } := by
    rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x'
          hsmall_x', hstack0]
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by rw [hps1eq]
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "REVERT"]) := by rw [hpcI]; exact hbE
  have hsafe' : wx.toNat + wy.toNat
      ≤ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.alloc.fnEom := by
    rw [hps1eq]; show wx.toNat + wy.toNat ≤ ps.alloc.fnEom; omega
  have hcov' : wy.toNat = 0 ∨ ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ as1.memory.size := by
    rw [hmemI]; exact hcov
  obtain ⟨as2, hrunE, htermE⟩ :=
    emit_revert_sim hrelI hstacktop hcov' hsafe' hlen hbE'
  refine ⟨as2, ?_, htermE⟩
  rw [executePlan_append, List.length_append, runAsm_append_ok hrunI]
  exact hrunE

/-- The **active-swap** runnable sim for a non-commutative binop (the optimistic swap genuinely
    reorders the stack, run via `optimisticSwapPlan_sim`). The non-comm counterpart of
    `genRegularInstPlan_commBinopVar_sim_swap`; the output plan stack is a permutation of
    `base ++ [Var out]` (tracked by `StackPerm` at the fold). -/
theorem genRegularInstPlan_nonCommBinopVar_sim_swap
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {d_y d_x' : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15) (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                 stack := base ++ [Operand.Var out] } : PlanState).stack = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := base ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := base ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (base ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hlive
        hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x', hrev] at hblock ⊢
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by
    rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x', hstack0]
  have hps1spill : AssocList.lookup Operand Nat
      (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled
      (Operand.Var out) = none := by
    rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x']; exact hspill
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbIE, hbS⟩ := asmBlockAt_append hblock
  rw [executePlan_append] at hbIE
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hbIE
  obtain ⟨as1, hrunI, hrelI, hpcI, hmemI⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y hsmall_y
    hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈
      (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := stackPush (Operand.Var out)
          (stackPop 2 (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack) }
        : PlanState)
      = { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hbSpc : as.pc + (executePlan ((emitInputPlan inst.opcode [Operand.Var y, Operand.Var x]
      nextLiveness ps).1 ++ [StackOp.SOEmit name])).length = as2.pc := by
    rw [executePlan_append, List.length_append, hpcE, hpcI]; omega
  rw [hbSpc] at hbS
  obtain ⟨as3, hrunS, hrelS, hpcS⟩ := optimisticSwapPlan_sim hrelE hbS hswap
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelS
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append, List.length_append]
    exact runAsm_compose (runAsm_compose hrunI hrunE) hrunS
  · rw [executePlan_append, List.length_append, List.length_append, hpcS, hpcE, hpcI]; omega

/-- Structural decomposition of `generateRegularInstPlan` for a **ternary** opcode with three
    distinct *variable* operands (all live, non-spilled). The 3-input counterpart of
    `genRegularInstPlan_nonCommBinopVar_eq`: same plan shape with three DUPs, a 3-wide reorder no-op,
    and a 3-wide pop. -/
theorem genRegularInstPlan_ternopVar_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y z : String} {out : String} {base : List Operand} {name : String} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hpvar := emitInputPlan_triple_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y
    hnospill_x hlivex hdepth_x'' hsmall_x
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
        nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1
    rw [← h2]; exact hps1
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname,
        reorderPlan_triple_var_nil base z y x ps1 hps1' (Ne.symm hyz) (Ne.symm hxy) (Ne.symm hxz),
        hps1', stackPop_3_append_triple, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- The runnable sim for a **ternary** opcode with three distinct *variable* operands. The asm
    computes `f wx wy wz` (`asmTernop`); the 3-input counterpart of
    `genRegularInstPlan_nonCommBinopVar_sim`. The Venom step is `updateVar out (f wx wy wz)`. -/
theorem genRegularInstPlan_ternopVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y z : String} {wx wy wz : bytes32} {out : String} {base : List Operand} {name : String}
    {d_z d_y' d_x'' : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15)
    (hlenz : d_z < ps.stack.length)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15)
    (hleny' : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15)
    (hlenx'' : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy wz) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz hstack0
        hlive hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y hnospill_x
        hlivex hdepth_x'' hsmall_x,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
    nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hps1def, emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey
      hdepth_y' hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey
      hdepth_y' hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := emitInputPlan_triple_var_sim hnospill_z hlivez hdepth_z
    hsmall_z hlenz hnospill_y hlivey hdepth_y' hsmall_y hleny' hnospill_x hlivex hdepth_x'' hsmall_x
    hlenx'' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: wz :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hvx hvy hvz
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_3op_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 3 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_3_append_triple]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- The **active-swap** runnable sim for a ternary opcode (the optimistic swap genuinely reorders the
    stack, so its asm segment is run via `optimisticSwapPlan_sim`). The 3-input counterpart of
    `genRegularInstPlan_commBinopVar_sim_swap`; the output plan stack is a permutation of
    `base ++ [Var out]` (tracked by `StackPerm` at the fold). -/
theorem genRegularInstPlan_ternopVar_sim_swap
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y z : String} {wx wy wz : bytes32} {out : String} {base : List Operand} {name : String}
    {d_z d_y' d_x'' : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nextLiveness.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15) (hlenz : d_z < ps.stack.length)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15) (hleny' : d_y' < (stackDup d_z ps.stack).length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15) (hlenx'' : d_x'' < (stackDup d_y' (stackDup d_z ps.stack)).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hvz : operandVal vs lo (Operand.Var z) = some wz)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                   nextLiveness ps).2 with stack := base ++ [Operand.Var out] } : PlanState).stack
                 = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := base ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := base ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (base ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy wz) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz hstack0
        hlive hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y' hsmall_y hnospill_x
        hlivex hdepth_x'' hsmall_x, hrev] at hblock ⊢
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
      nextLiveness ps).2.stack = base ++ [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y'
      hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x, hstack0]
  have hps1spill : AssocList.lookup Operand Nat
      (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled
      (Operand.Var out) = none := by
    rw [emitInputPlan_triple_var_eq hnospill_z hlivez hdepth_z hsmall_z hnospill_y hlivey hdepth_y'
      hsmall_y hnospill_x hlivex hdepth_x'' hsmall_x]; exact hspill
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbIE, hbS⟩ := asmBlockAt_append hblock
  rw [executePlan_append] at hbIE
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hbIE
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := emitInputPlan_triple_var_sim hnospill_z hlivez hdepth_z
    hsmall_z hlenz hnospill_y hlivey hdepth_y' hsmall_y hleny' hnospill_x hlivex hdepth_x'' hsmall_x
    hlenx'' hrel hbI
  have hstacktop : as1.stack = wx :: wy :: wz :: as1.stack.drop 3 :=
    venomAsmRel_asmStack_top3_var hrelI hps1stack hvx hvy hvz
  have hfresh1 : ¬ (Operand.Var out) ∈
      (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_3op_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := stackPush (Operand.Var out)
          (stackPop 3 (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2.stack) }
        : PlanState)
      = { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_3_append_triple]; rfl
  rw [hps6] at hrelE
  have hbSpc : as.pc + (executePlan ((emitInputPlan inst.opcode
      [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).1
      ++ [StackOp.SOEmit name])).length = as2.pc := by
    rw [executePlan_append, List.length_append, hpcE, hpcI]; omega
  rw [hbSpc] at hbS
  obtain ⟨as3, hrunS, hrelS, hpcS⟩ := optimisticSwapPlan_sim hrelE hbS hswap
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelS
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append, List.length_append]
    exact runAsm_compose (runAsm_compose hrunI hrunE) hrunS
  · rw [executePlan_append, List.length_append, List.length_append, hpcS, hpcE, hpcI]; omega

/-- DIV instantiation — non-commutative arithmetic (`safeDiv`). -/
theorem genRegularInstPlan_divLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hdiv : inst.opcode = Opcode.Div)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (safeDiv a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hdiv]; rfl) (by rw [hdiv]; rfl)
    (by rw [hdiv]; decide) (by simp [computeOperands, hdiv]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_div_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SHL instantiation — the shift that was *doubly* wrong before the fixes (codegen reversal +
    semantics). `f a b = b <<< a` (shift-first); the asm and Venom functions are now defeq. -/
theorem genRegularInstPlan_shlLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hshl : inst.opcode = Opcode.SHL)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (b <<< a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (f := fun a b => b <<< a)
    (by rw [hshl]; rfl) (by rw [hshl]; rfl)
    (by rw [hshl]; decide) (by simp [computeOperands, hshl]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_shl_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SLT instantiation — signed comparison (`UInt256.slt`). -/
theorem genRegularInstPlan_sltLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hslt : inst.opcode = Opcode.SLT)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.slt a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hslt]; rfl) (by rw [hslt]; rfl)
    (by rw [hslt]; decide) (by simp [computeOperands, hslt]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_slt_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- LT instantiation — unsigned comparison (`boolToWord (a < b)`). -/
theorem genRegularInstPlan_ltLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hlt : inst.opcode = Opcode.LT)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (boolToWord (a < b)) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (f := fun x y => boolToWord (x < y))
    (by rw [hlt]; rfl) (by rw [hlt]; rfl)
    (by rw [hlt]; decide) (by simp [computeOperands, hlt]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_lt_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- GT instantiation — unsigned comparison (`boolToWord (a > b)`). -/
theorem genRegularInstPlan_gtLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hgt : inst.opcode = Opcode.GT)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b]) (houts : inst.outputs = [out])
    (hab : a ≠ b) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (boolToWord (a > b)) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (f := fun x y => boolToWord (x > y))
    (by rw [hgt]; rfl) (by rw [hgt]; rfl)
    (by rw [hgt]; decide) (by simp [computeOperands, hgt]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_gt_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-! ## Single-literal unary-op execution sim

The 1-operand analog of the binop structural sim, for `ISZERO`/`NOT`. Single-operand supporting
lemmas (1-input duals of the pair ones) feed `genRegularInstPlan_unopLit_{eq,sim}`. The commutative
cheaper-order `if` is skipped because `operands.length ≥ 2` is false for one operand. -/

/-- `get!` at the end of `base ++ [x]` is `x`. -/
theorem getbang_append_single (base : List Operand) (x : Operand) :
    (base ++ [x])[base.length]! = x := by
  rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
  simp

/-- TOS of `base ++ [x]` is `x`. -/
theorem stackPeek_0_append_single (base : List Operand) (x : Operand) :
    stackPeek 0 (base ++ [x]) = x := by
  unfold stackPeek
  rw [show (base ++ [x]).length - 1 - 0 = base.length from by simp]
  exact getbang_append_single base x

/-- `stackPop 1` removes the single operand a unary op emitted, leaving the base. -/
theorem stackPop_1_append_single (base : List Operand) (x : Operand) :
    stackPop 1 (base ++ [x]) = base := by unfold stackPop; simp

/-- A list of length ≥ 1 is `get!0 :: drop 1`. -/
theorem list_eq_get1 {α} [Inhabited α] (l : List α) (h : 1 ≤ l.length) :
    l = l[0]! :: l.drop 1 := by
  match l with
  | c0 :: rest => rfl
  | [] => simp at h

/-- `Lit a` sits at depth 0 (TOS) of `base ++ [Lit a]`. -/
theorem stackGetDepth_tos_single (base : List Operand) (x : Operand) :
    stackGetDepth x (base ++ [x]) = some 0 := by
  simp [stackGetDepth, stackFind, List.reverse_append]

/-- `emitInputPlan` of a single literal is one `PUSH`; the operand lands on top. -/
theorem emitInputPlan_single_lit_eq (opc : Opcode) (nl : List String) (a : bytes32) (ps : PlanState) :
    emitInputPlan opc [Operand.Lit a] nl ps
      = ([StackOp.SOPush (Operand.Lit a)], { ps with stack := ps.stack ++ [Operand.Lit a] }) := by
  unfold emitInputPlan
  simp only [List.foldl_cons, List.foldl_nil, emitOneInput_lit_eq, stackPush, List.nil_append]

/-- `reorderPlan [Lit a]` is a no-op when `Lit a` is already on top. -/
theorem reorderPlan_single_lit_nil (base : List Operand) (a : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a]) :
    reorderPlan [Operand.Lit a] ps = ([], ps) := by
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  simp only [List.enum, List.zipIdx, List.map, List.mem_singleton] at hp
  subst hp
  show stackGetDepth (Operand.Lit a) ps.stack = some 0
  rw [hstack]; exact stackGetDepth_tos_single base (Operand.Lit a)

/-- `reorderPlan [Var x]` is a no-op when `Var x` is already on top (the var counterpart of
    `reorderPlan_single_lit_nil`). -/
theorem reorderPlan_single_var_nil (base : List Operand) (x : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x]) :
    reorderPlan [Operand.Var x] ps = ([], ps) := by
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  simp only [List.enum, List.zipIdx, List.map, List.mem_singleton] at hp
  subst hp
  show stackGetDepth (Operand.Var x) ps.stack = some 0
  rw [hstack]; exact stackGetDepth_tos_single base (Operand.Var x)

/-- With the plan stack `base ++ [Lit a]`, the asm stack top is `a`. -/
theorem venomAsmRel_asmStack_top1_lit {lo ps vs as} {base : List Operand} {a : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Lit a]) :
    as.stack = a :: as.stack.drop 1 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 1 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = a := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_single] at hp
    simp only [operandVal] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get1 as.stack hge]
  rw [h0]

/-- With the plan stack `base ++ [Var x]` and `x` valued `w` in `vs`, the asm stack top is `w`.
    The var counterpart of `venomAsmRel_asmStack_top1_lit` (value comes from `operandVal`, not a
    literal). -/
theorem venomAsmRel_asmStack_top1_var {lo ps vs as} {base : List Operand} {x : String} {w : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Var x])
    (hval : operandVal vs lo (Operand.Var x) = some w) :
    as.stack = w :: as.stack.drop 1 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 1 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = w := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_single, hval] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get1 as.stack hge]
  rw [h0]

/-- Input-emission sim for a single live var: run the one `DUP` (composes `doDup_sim`). The var
    counterpart of `emitInputPlan_single_lit_sim` (`DUP` instead of `PUSH`). -/
theorem emitInputPlan_single_var_sim {opc nl x ps lo vs as prog dist}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlive : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hrel : venomAsmRel lo ps vs as)
    (hlen : dist < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var x] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var x] nl ps).1).length := by
  have hemit : emitInputPlan opc [Operand.Var x] nl ps = doDup dist ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append]
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlive, if_true, hdepth, hdd, List.nil_append]
  rw [hemit] at hblock ⊢
  exact doDup_sim rfl hsmall hrel hlen hblock

/-- **`emitInputPlan` sim for a single SPILLED live var** — fold-level lift of the spilling connective.
    A one-operand `emitInputPlan` is `emitOneInput`, so this threads `emitOneInput_sim_var_spilled`
    through the real fold, demonstrating spilling composes at the `emitInputPlan` layer. -/
theorem emitInputPlan_single_var_sim_spilled {opc nl v ps lo vs as prog off}
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nl.contains v = true)
    (hrel : venomAsmRel lo ps vs as)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1).length := by
  have hemit : emitInputPlan opc [Operand.Var v] nl ps = emitOneInput opc nl (Operand.Var v) ps := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append, Prod.mk.eta]
  rw [hemit] at hblock ⊢
  exact emitOneInput_sim_var_spilled (opc := opc) (offsetToPc := offsetToPc) hspill hlive rfl hrel hspillWf hblock

/-- `aremove` preserves a `none` lookup at any key (removing a key can't create an entry). -/
theorem aremove_lookup_none {β} (m : AssocList Operand β) (k o : Operand)
    (h : AssocList.lookup Operand β m o = none) :
    AssocList.lookup Operand β (aremove m k) o = none := by
  rcases hr : AssocList.lookup Operand β (aremove m k) o with _ | v
  · rfl
  · rw [aremove_lookup_some m k o v hr] at h; exact absurd h (by simp)

/-- **`emitInputPlan` sim for a mixed pair `[spilled v, live w]`** — the fold genuinely composes the
    spilled-restore path (`emitOneInput_sim_var_spilled`) for the head with the ordinary DUP path
    (inlined) for the tail. After the head, `v` sits atop (`ps.stack ++ [v, v]`) and its spill entry is
    gone, so `w`'s depth shifts by 2 and `w` stays unspilled. Concrete demonstration that spilling
    threads through `emitInputPlan` alongside a normal operand. -/
theorem emitInputPlan_pair_spill_first_sim {opc nl v w ps lo vs as prog off d}
    (hvw : v ≠ w)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hnospillw : alookup' ps.spilled (Operand.Var w) = none)
    (hdepthw : stackGetDepth (Operand.Var w) ps.stack = some d) (hsmall : d + 2 ≤ 15)
    (hlenw : d < ps.stack.length)
    (hrel : venomAsmRel lo ps vs as)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length := by
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                    spilled := aremove ps.spilled (Operand.Var v),
                                    alloc := freeSpillSlot off ps.alloc } with hps1def
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore off, StackOp.SODup 1], ps1) :=
    emitOneInput_var_spilled_eq hspill hlivev
  have hps1stack : ps1.stack = ps.stack ++ [Operand.Var v, Operand.Var v] := by rw [hps1def]
  have hdepthw1 : stackGetDepth (Operand.Var w) ps1.stack = some (d + 2) := by
    rw [hps1stack,
        show ps.stack ++ [Operand.Var v, Operand.Var v]
          = (ps.stack ++ [Operand.Var v]) ++ [Operand.Var v] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var v]) (Ne.symm hvw),
        stackGetDepth_append_ne ps.stack (Ne.symm hvw), hdepthw]; rfl
  have hnospillw1 : alookup' ps1.spilled (Operand.Var w) = none := by
    rw [hps1def]; exact aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var w) hnospillw
  have hlenw1 : d + 2 < ps1.stack.length := by
    rw [hps1stack]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hddred : doDup (d + 2) ps1
      = ([StackOp.SODup (d + 2 + 1)], { ps1 with stack := stackDup (d + 2) ps1.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have htail : emitOneInput opc nl (Operand.Var w) ps1
      = ([StackOp.SODup (d + 2 + 1)], { ps1 with stack := stackDup (d + 2) ps1.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillw1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivew, if_true, hdepthw1, hddred, List.nil_append]
  have hfold : emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps
      = ([StackOp.SORestore off, StackOp.SODup 1] ++ [StackOp.SODup (d + 2 + 1)],
         { ps1 with stack := stackDup (d + 2) ps1.stack }) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hfold] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbHead, hbTail⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunHead, hrelHead, hpcHead⟩ :=
    emitOneInput_sim_var_spilled (offsetToPc := offsetToPc) hspill hlivev hhead hrel hspillWf hbHead
  have hbTail' : asmBlockAt prog as1.pc (executePlan [StackOp.SODup (d + 2 + 1)]) := by
    rw [hpcHead]; exact hbTail
  obtain ⟨as2, hrunTail, hrelTail, hpcTail⟩ :=
    doDup_sim (offsetToPc := offsetToPc) hddred hsmall hrelHead hlenw1 hbTail'
  have hlen : (executePlan ([StackOp.SORestore off, StackOp.SODup 1] ++ [StackOp.SODup (d + 2 + 1)])).length
      = (executePlan [StackOp.SORestore off, StackOp.SODup 1]).length
        + (executePlan [StackOp.SODup (d + 2 + 1)]).length := by
    rw [executePlan_append, List.length_append]
  refine ⟨as2, ?_, hrelTail, ?_⟩
  · rw [hlen]; exact runAsm_compose hrunHead hrunTail
  · rw [hlen, hpcTail, hpcHead]; omega

/-! ### Spilled-value store — the first 2-operand spill-aware producer (Gap C)

The `x ≠ y` store with the **value** operand `y` spilled and the **key** `x` live. The emit restores+dups
`y` and dups `x`, leaving `base ++ [y, y, x]`; crucially, the store's operands `[Var y, Var x]` are
**still positioned** on top (`(base ++ [y]) ++ [y, x]`), so the reorder is `[]` — the case where the
2-operand reorder-under-spill is trivial. `stackPop 2` leaves `base ++ [y]` (the kept restored `y`). -/

/-- **Spilled-value plan reduction for a no-output 2-var store** — the value-spilled reroute of
    `genRegularInstPlan_sstore_eq`. -/
theorem genRegularInstPlan_sstore_spilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y : String} {base : List Operand} {name : String} {offy d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name],
         releaseDeadSpills nextLiveness
           { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
             stack := base ++ [Operand.Var y] }) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  set psY : PlanState := { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y], spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc } with hpsYdef
  have hhead : emitOneInput inst.opcode nextLiveness (Operand.Var y) ps
      = ([StackOp.SORestore offy, StackOp.SODup 1], psY) := emitOneInput_var_spilled_eq hspill_y hlivey
  have hpsYstack : psY.stack = ps.stack ++ [Operand.Var y, Operand.Var y] := by rw [hpsYdef]
  have hdepthx1 : stackGetDepth (Operand.Var x) psY.stack = some (d_x + 2) := by
    rw [hpsYstack,
        show ps.stack ++ [Operand.Var y, Operand.Var y]
          = (ps.stack ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var y]) hxy,
        stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hnospillx1 : alookup' psY.spilled (Operand.Var x) = none := by
    rw [hpsYdef]; exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var x) hnospill_x
  have hpeekx : stackPeek (d_x + 2) psY.stack = Operand.Var x := stackGetDepth_peek hdepthx1
  have hddred : doDup (d_x + 2) psY
      = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
    unfold doDup; rw [if_pos hsmall_x]
  have htail : emitOneInput inst.opcode nextLiveness (Operand.Var x) psY
      = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillx1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepthx1, hddred, List.nil_append]
  have hemit2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2
      = { psY with stack := stackDup (d_x + 2) psY.stack } := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  have hdupx : stackDup (d_x + 2) psY.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    unfold stackDup; rw [hpeekx, hpsYstack, hstack0]; simp
  have hemitstack : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [hrev, hemit2]; exact hdupx
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1flat : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [hrev] at hemitstack; rw [← h2]; exact hemitstack
  have hps1 : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1flat]; simp
  have hpop2 : stackPop 2 ps1.stack = base ++ [Operand.Var y] := by
    rw [hps1, stackPop_2_append_pair]
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_nil (base ++ [Operand.Var y]) y x ps1 hps1 (Ne.symm hxy),
        hpop2, hncomm, hnjmp]

/-- **Spilled-value SSTORE sim.** The value-operand-spilled reroute of `genRegularInstPlan_sstore_sim`:
    restore the value `y`, DUP the key `x`, run SSTORE — the whole plan preserves `venomAsmRel` across
    `sstore wx wy`. The first *2-operand* spill-aware producer (the reorder is `[]` because the emit
    leaves the operands positioned). -/
theorem genRegularInstPlan_sstore_spilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {base : List Operand} {offy d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (sstore wx wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenx : d_x < ps.stack.length := stackGetDepth_lt_length hdepth_x
  rw [genRegularInstPlan_sstore_spilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hspill_y
      hlivey hnospill_x hlivex hdepth_x hsmall_x, hrev] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by
    have hemit2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack
        = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
      have hhead : emitOneInput inst.opcode nextLiveness (Operand.Var y) ps
          = ([StackOp.SORestore offy, StackOp.SODup 1],
             { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y],
                       spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc }) :=
        emitOneInput_var_spilled_eq hspill_y hlivey
      set psY : PlanState := { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y], spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc } with hpsYdef
      have hpsYstack : psY.stack = ps.stack ++ [Operand.Var y, Operand.Var y] := by rw [hpsYdef]
      have hdepthx1 : stackGetDepth (Operand.Var x) psY.stack = some (d_x + 2) := by
        rw [hpsYstack, show ps.stack ++ [Operand.Var y, Operand.Var y] = (ps.stack ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
            stackGetDepth_append_ne (ps.stack ++ [Operand.Var y]) hxy, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
      have hnospillx1 : alookup' psY.spilled (Operand.Var x) = none := by
        rw [hpsYdef]; exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var x) hnospill_x
      have hpeekx : stackPeek (d_x + 2) psY.stack = Operand.Var x := stackGetDepth_peek hdepthx1
      have hddred : doDup (d_x + 2) psY = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
        unfold doDup; rw [if_pos hsmall_x]
      have htail : emitOneInput inst.opcode nextLiveness (Operand.Var x) psY
          = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
        unfold emitOneInput
        simp only [isVarOperand, hnospillx1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
          if_false, hlivex, if_true, hdepthx1, hddred, List.nil_append]
      have hemit2' : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2
          = { psY with stack := stackDup (d_x + 2) psY.stack } := by
        unfold emitInputPlan; simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
      rw [hemit2']; show stackDup (d_x + 2) psY.stack = _
      unfold stackDup; rw [hpeekx, hpsYstack, hstack0]; simp
    rw [hps1def, hemit2]; simp
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_first_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hlivey hlivex
      hnospill_x hdepth_x hsmall_x hlenx hrel hspillWf hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SSTORE"]) := by rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_sstore_sim hrelI hstacktop hbE' (fun h hg => hdisp as1 h hg)
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base ++ [Operand.Var y] } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-! ### Spilled-value binop — the 1-output 2-operand spill-aware producer (Gap C) -/

-- shared: full emit .2 for value-spilled 2-var op (y spilled, x live): stack base ++ [y, y, x],
-- y's slot freed. (Public: also consumed by the value-spilled store fold-producer preservation.)
theorem emit2_valspilled {opc nl x y ps base offy d_x}
    (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nl.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nl.contains x = true)
    (hxy : x ≠ y)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 2 ≤ 15) :
    (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { ps with stack := base ++ [Operand.Var y, Operand.Var y, Operand.Var x],
                  spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc } := by
  have hhead : emitOneInput opc nl (Operand.Var y) ps
      = ([StackOp.SORestore offy, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y],
                   spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc }) :=
    emitOneInput_var_spilled_eq hspill_y hlivey
  set psY : PlanState := { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var y], spilled := aremove ps.spilled (Operand.Var y), alloc := freeSpillSlot offy ps.alloc } with hpsYdef
  have hpsYstack : psY.stack = ps.stack ++ [Operand.Var y, Operand.Var y] := by rw [hpsYdef]
  have hdepthx1 : stackGetDepth (Operand.Var x) psY.stack = some (d_x + 2) := by
    rw [hpsYstack, show ps.stack ++ [Operand.Var y, Operand.Var y] = (ps.stack ++ [Operand.Var y]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var y]) hxy, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hnospillx1 : alookup' psY.spilled (Operand.Var x) = none := by
    rw [hpsYdef]; exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var x) hnospill_x
  have hpeekx : stackPeek (d_x + 2) psY.stack = Operand.Var x := stackGetDepth_peek hdepthx1
  have hddred : doDup (d_x + 2) psY = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
    unfold doDup; rw [if_pos hsmall_x]
  have htail : emitOneInput opc nl (Operand.Var x) psY
      = ([StackOp.SODup (d_x + 2 + 1)], { psY with stack := stackDup (d_x + 2) psY.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillx1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivex, if_true, hdepthx1, hddred, List.nil_append]
  have hemit2 : (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2
      = { psY with stack := stackDup (d_x + 2) psY.stack } := by
    unfold emitInputPlan; simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  have hdupx : stackDup (d_x + 2) psY.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    unfold stackDup; rw [hpeekx, hpsYstack, hstack0]; simp
  rw [hemit2, hdupx]

private theorem emitstack_valspilled {opc nl x y ps base offy d_x}
    (hstack0 : ps.stack = base)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy) (hlivey : nl.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none) (hlivex : nl.contains x = true)
    (hxy : x ≠ y)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x) (hsmall_x : d_x + 2 ≤ 15) :
    (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2.stack
      = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
  rw [emit2_valspilled hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x]

/-- **Spilled-value plan reduction for a 1-output 2-var op** (non-commutative binop). Value operand `y`
    spilled, first operand `x` live: emit leaves `base ++ [y, y, x]`, operands positioned (reorder `[]`),
    `stackPop 2` then push `out` gives the optSwap intermediate `base ++ [Var y, Var out]`. -/
theorem genRegularInstPlan_nonCommBinopVar_spilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offy d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var y, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var y, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemitstack : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [hrev]; exact emitstack_valspilled hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1flat : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by
    rw [hrev] at hemitstack; rw [← h2]; exact hemitstack
  have hps1 : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1flat]; simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 ps1.stack ++ [Operand.Var out] = base ++ [Operand.Var y, Operand.Var out] := by
    rw [hps1, stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_nil (base ++ [Operand.Var y]) y x ps1 hps1 (Ne.symm hxy),
        hpush, stackPush, popmanyPlan_nil, hmem, hncomm, hnjmp]

/-- **Spilled-value non-commutative binop sim.** Value operand `y` spilled, first `x` live: restore `y`,
    DUP `x`, run the binop, push `out` — whole plan preserves `venomAsmRel` across `out := f wx wy`. The
    binop-class instance of the Gap-C reroute (2-operand-positioned config + output-handling under spill). -/
theorem genRegularInstPlan_nonCommBinopVar_spilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offy d_x : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
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
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenx : d_x < ps.stack.length := stackGetDepth_lt_length hdepth_x
  rw [genRegularInstPlan_nonCommBinopVar_spilled_eq hname hncomm hnjmp hcompute hops houts hxy hstack0
      hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hemit2 := emit2_valspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x
  have hps1stack : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, hemit2]; simp
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemit2]
    show alookup' (aremove ps.spilled (Operand.Var y)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var out) hspill_out
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_first_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hlivey hlivex
      hnospill_x hdepth_x hsmall_x hlenx hrel hspillWf hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro ((h | h) | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Value-spilled commutative binop plan reduction.** Value `y` spilled, `x` live. The
    commutative dispatch resolves to the positioned order (opsA cost 0 < opsB cost 1), so the plan
    matches the non-commutative value-spilled binop (intermediate `base ++ [y, out]`); `f`'s
    symmetry makes the order irrelevant to the result. -/
theorem genRegularInstPlan_commBinopVar_valspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offy d_x : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var y, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var y, Operand.Var out] }).2) := by
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_valspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1flat : ps1.stack = base ++ [Operand.Var y, Operand.Var y, Operand.Var x] := by rw [← h2, hemit2]
  have hps1'' : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by rw [hps1flat]; simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 ps1.stack ++ [Operand.Var out] = base ++ [Operand.Var y, Operand.Var out] := by
    rw [hps1'', stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_var_nil (base ++ [Operand.Var y]) y x ps1 hps1'' (Ne.symm hxy),
        reorderPlan_swapped_pair_var (base ++ [Operand.Var y]) y x ps1 hps1'',
        hpush, stackPush, popmanyPlan_nil, hmem, reorderCost, hcomm, hjmp]

/-- **Key-spilled store/binop reorder — swapped (commutative) order.** For target `[Var x, Var y]`
    (the swapped operand order a commutative binop picks on a `reorderCost` tie) and the emit stack
    `base ++ [y, x, x]`, `reorderPlan` synthesises `SWAP1 ; SWAP2`: the first `SWAP1` transposes the two
    equal `x`'s (a no-op on the stack, moving `x` toward depth 1), the `SWAP2` rotates the deep `y` to
    TOS — leaving `base ++ [x, x, y]`. -/
theorem reorderPlan_keyspilled_swapped (base : List Operand) (x y : String) (ps : PlanState) (hxy : x ≠ y)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x]) :
    reorderPlan [Operand.Var x, Operand.Var y] ps
      = ([StackOp.SOSwap 1, StackOp.SOSwap 2],
         { ps with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }) := by
  -- step 0: op `x` (TOS, depth 0) → target depth 1 via SWAP1; swapping the two equal `x`'s is a stack no-op
  have hstep0 : reorderOne () [Operand.Var x, Operand.Var y] 0 (Operand.Var x) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] }) := by
    have hd : stackGetDepth (Operand.Var x) ps.stack = some 0 := by
      rw [hstack]; exact stackGetDepth_triple_tos base (Operand.Var y) (Operand.Var x) (Operand.Var x)
    have hsw1 : stackSwap 1 ps.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
      rw [hstack]; exact stackSwap_1_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_one, hsw1]
  -- step 1: op `y` (depth 2) → target depth 0 (TOS) via SWAP2, leaving `base ++ [x, x, y]`
  have hstep1 : reorderOne () [Operand.Var x, Operand.Var y] 1 (Operand.Var y)
      { ps with stack := base ++ [Operand.Var y, Operand.Var x, Operand.Var x] }
      = ([StackOp.SOSwap 2], { ps with stack := base ++ [Operand.Var x, Operand.Var x, Operand.Var y] }) := by
    have hd : stackGetDepth (Operand.Var y) (base ++ [Operand.Var y, Operand.Var x, Operand.Var x]) = some 2 :=
      stackGetDepth_triple_deep base y x (Ne.symm hxy)
    have hsw2 : stackSwap 2 (base ++ [Operand.Var y, Operand.Var x, Operand.Var x])
        = base ++ [Operand.Var x, Operand.Var x, Operand.Var y] :=
      stackSwap_2_append_triple base (Operand.Var y) (Operand.Var x) (Operand.Var x)
    unfold reorderOne
    simp [hd, doSwap_zero, doSwap_two, hsw2]
  unfold reorderPlan
  have henum : ([Operand.Var x, Operand.Var y]).enum = [(0, Operand.Var x), (1, Operand.Var y)] := rfl
  rw [henum]
  simp [List.foldl_cons, List.foldl_nil, hstep0, hstep1]


/-- **Key-spilled commutative binop plan reduction.** Key `x` spilled, value `y` live. Emit leaves
    `base ++ [y, x, x]`; both operand orders reorder at equal cost 2 (SWAP2;SWAP1 vs SWAP1;SWAP2), so the
    commutative dispatch takes the *swapped* order `[x, y]` (`reorderPlan_keyspilled_swapped` →
    `SWAP1 ; SWAP2`, `base ++ [x, x, y]`); `stackPop 2` then push `out` gives the optSwap intermediate
    `base ++ [x, out]`. -/
theorem genRegularInstPlan_commBinopVar_keyspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offx d_y : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 1, StackOp.SOSwap 2] ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var x, Operand.Var out] }).2) := by
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1flat : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by rw [← h2, hemit2]
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 (base ++ [Operand.Var x, Operand.Var x, Operand.Var y]) ++ [Operand.Var out]
      = base ++ [Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var x, Operand.Var x, Operand.Var y] = (base ++ [Operand.Var x]) ++ [Operand.Var x, Operand.Var y] from by simp,
        stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname,
        reorderPlan_keyspilled base x y ps1 hxy hps1flat,
        reorderPlan_keyspilled_swapped base x y ps1 hxy hps1flat,
        hpush, stackPush, popmanyPlan_nil, hmem, reorderCost, hcomm, hjmp]


/-- **Value-spilled commutative binop sim.** As the non-commutative value-spilled binop sim but
    through the commutative branch (same plan/state). Preserves `venomAsmRel` across
    `out := f wx wy`. -/
theorem genRegularInstPlan_commBinopVar_valspilled_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {x y out : String} {wx wy : bytes32} {base : List Operand}
    {name : String} {offy d_x : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill_out : alookup' ps.spilled (Operand.Var out) = none)
    (hspill_y : alookup' ps.spilled (Operand.Var y) = some offy)
    (hlivey : nextLiveness.contains y = true)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall_x : d_x + 2 ≤ 15)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
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
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hlenx : d_x < ps.stack.length := stackGetDepth_lt_length hdepth_x
  rw [genRegularInstPlan_commBinopVar_valspilled_eq hname hcomm hops houts hxy hstack0
      hlive hspill_y hlivey hnospill_x hlivex hdepth_x hsmall_x, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with hps1def
  have hemit2 := emit2_valspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hspill_y hlivey hnospill_x hlivex hxy hdepth_x hsmall_x
  have hps1stack : ps1.stack = (base ++ [Operand.Var y]) ++ [Operand.Var y, Operand.Var x] := by
    rw [hps1def, hemit2]; simp
  have hps1spill : alookup' ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemit2]
    show alookup' (aremove ps.spilled (Operand.Var y)) (Operand.Var out) = none
    exact aremove_lookup_none ps.spilled (Operand.Var y) (Operand.Var out) hspill_out
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_pair_spill_first_sim (offsetToPc := offsetToPc) (Ne.symm hxy) hspill_y hlivey hlivex
      hnospill_x hdepth_x hsmall_x hlenx hrel hspillWf hbI
  have hstacktop : as1.stack = wx :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var hrelI hps1stack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro ((h | h) | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var y, Operand.Var out] } := by
    rw [hps1stack, stackPop_2_append_pair]; simp [stackPush, List.append_assoc]
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Key-spilled non-commutative binop plan reduction.** Key `x` spilled, value `y` live: emit DUPs
    `y` and restores+DUPs `x` (`base ++ [y, x, x]`), the reorder is the non-trivial `SWAP2 ; SWAP1`
    (`reorderPlan_keyspilled`) giving `base ++ [x, y, x]`, then the op pops two and pushes `out`
    (optSwap intermediate `base ++ [x, out]`). The reorder+output combination — assembles the
    key-spilled store reorder with the value-spilled binop's output handling. -/
theorem genRegularInstPlan_nonCommBinopVar_keyspilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x y out : String} {base : List Operand} {name : String} {offx d_y : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hspill_x : alookup' ps.spilled (Operand.Var x) = some offx)
    (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOSwap 2, StackOp.SOSwap 1] ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var x, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hemit2 := emit2_keyspilled (opc := inst.opcode) (nl := nextLiveness) hstack0 hnospill_y hlivey hdepth_y hsmall_y hspill_x hlivex
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Var x, Operand.Var x] := by
    rw [← h2, hemit2]
  have hreorder : reorderPlan [Operand.Var y, Operand.Var x] ps1
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps1 with stack := base ++ [Operand.Var x, Operand.Var y, Operand.Var x] }) :=
    reorderPlan_keyspilled base x y ps1 hxy hps1stack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpush : stackPop 2 (base ++ [Operand.Var x, Operand.Var y, Operand.Var x]) ++ [Operand.Var out]
      = base ++ [Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var x, Operand.Var y, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var y, Operand.Var x] from by simp,
        stackPop_2_append_pair]; simp [List.append_assoc]
  simp [generateEmitOps_evmName hname, hreorder, hpush, stackPush, popmanyPlan_nil, hmem, hncomm, hnjmp]

/-- Input-emission sim for a single literal: run the one `PUSH`. -/
theorem emitInputPlan_single_lit_sim {opc nl a ps lo vs as prog}
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Lit a] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Lit a] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Lit a] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Lit a] nl ps).1).length := by
  rw [emitInputPlan_single_lit_eq] at hblock ⊢
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    emitOneInput_sim_lit (emitOneInput_lit_eq opc nl a ps) hrel hblock
  exact ⟨as1, hrun1, by simpa [stackPush] using hrel1, hpc1⟩

/-- Structural decomposition of `generateRegularInstPlan` for a single-literal unary op. -/
theorem genRegularInstPlan_unopLit_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {a : bytes32} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Lit a] := by rw [hops]; rfl
  have hallLit : ∀ op ∈ ([Operand.Lit a] : List Operand), ∃ v, op = Operand.Lit v := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    subst hop; exact ⟨_, rfl⟩
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Lit a] := by
    rw [hrev]
    have := emitInputPlan_stack_allLit inst.opcode [Operand.Lit a] nextLiveness ps hallLit
    rw [this, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Lit a] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Lit a] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Lit a] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1
    rw [← h2]; exact hps1
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname, reorderPlan_single_lit_nil base a ps1 hps1',
        hps1', stackPop_1_append_single, stackPush, popmanyPlan_nil, hmem, hnjmp]

/-- The runnable sim for a single-literal unary op: the generated plan for `out := OP (Lit a)`
    simulates the Venom step `out := f a`. -/
theorem genRegularInstPlan_unopLit_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Lit a] := by rw [hops]; rfl
  rw [genRegularInstPlan_unopLit_eq hname hnjmp hcompute hops houts hstack0 hlive,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Lit a] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Lit a] := by
    rw [hps1def, emitInputPlan_single_lit_eq, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, emitInputPlan_single_lit_eq]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := emitInputPlan_single_lit_sim hrel hbI
  have hstacktop : as1.stack = a :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_lit hrelI hps1stack
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_unop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- Structural decomposition of `generateRegularInstPlan` for a single-var unary op: the input is
    one `DUP` (var counterpart of `genRegularInstPlan_unopLit_eq`'s `PUSH`). -/
theorem genRegularInstPlan_unopVar_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x out : String} {base : List Operand} {name : String} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1
            ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
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
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by
    rw [hrev, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1
    rw [← h2]; exact hps1
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname, reorderPlan_single_var_nil base x ps1 hps1',
        hps1', stackPop_1_append_single, stackPush, popmanyPlan_nil, hmem, hnjmp]

/-- **Spilled plan reduction for a single-var unary op.** The `x`-spilled counterpart of
    `genRegularInstPlan_unopVar_eq`: the emit *restores+dups* the spilled operand (so `x` transitions
    onto the stack), leaving the pre-op stack `base ++ [Var x]` and the post-op `base ++ [Var x, Var out]`
    (the no-spill version pops `x` back into `base`, so its intermediate is `base ++ [Var out]`). The
    plan structure — `emit ++ [op] ++ optSwap ++ releaseDeadSpills` — is the same; only the stack
    accounting differs. A building block for rerouting the read-class body producer off
    `StackDiscH.noSpill`. -/
theorem genRegularInstPlan_unopVar_spilled_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x out : String} {base : List Operand} {name : String} {off : Nat}
    (hname : opcodeToEvmName inst.opcode = some name) (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hspill : alookup' ps.spilled (Operand.Var x) = some off) (hlivex : nextLiveness.contains x = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = (((emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
                    stack := base ++ [Operand.Var x, Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
               stack := base ++ [Operand.Var x, Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hemiteq : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var x, Operand.Var x],
                   spilled := aremove ps.spilled (Operand.Var x), alloc := freeSpillSlot off ps.alloc }) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, List.nil_append, emitOneInput_var_spilled_eq hspill hlivex]
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var x, Operand.Var x] := by rw [hrev, hemiteq, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var x, Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  have hps1'' : ps1.stack = (base ++ [Operand.Var x]) ++ [Operand.Var x] := by rw [hps1']; simp
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop 1 (base ++ [Operand.Var x, Operand.Var x]) ++ [Operand.Var out]
      = base ++ [Operand.Var x, Operand.Var out] := by
    rw [show base ++ [Operand.Var x, Operand.Var x] = (base ++ [Operand.Var x]) ++ [Operand.Var x] from by simp,
        stackPop_1_append_single]; simp
  simp [generateEmitOps_evmName hname, reorderPlan_single_var_nil (base ++ [Operand.Var x]) x ps1 hps1'',
        hps1', hpop, stackPush, popmanyPlan_nil, hmem, hnjmp]

/-- The runnable sim for a single-var unary op: the generated plan for `out := OP (Var x)`
    simulates the Venom step `out := f w`, where `w` is `x`'s value. The first var-operand
    per-instruction sim (DUP the input instead of PUSH; value via `venomAsmRel_asmStack_top1_var`). -/
theorem genRegularInstPlan_unopVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {name : String} {dist : Nat} {w : bytes32}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f w) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
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
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with hps1def
  have hps1stack : ps1.stack = base ++ [Operand.Var x] := by
    rw [hps1def, hemiteq, hdo]
    show stackDup dist ps.stack = base ++ [Operand.Var x]
    simp only [stackDup]; rw [hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat ps1.spilled (Operand.Var out) = none := by
    rw [hps1def, hemiteq, hdo]; exact hspill
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_unop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Active-swap variant of the unary var-op sim.** Drops the `hoptnoop` no-op assumption — the
    optimistic swap may reorder the stack, run via `optimisticSwapPlan_sim` as a third asm segment.
    The unary counterpart of `genRegularInstPlan_commBinopVar_sim_swap`; composes single-var input
    emission, `emit_unop_sim`, `optimisticSwapPlan_sim`, and `releaseDeadSpills_sim`. -/
theorem genRegularInstPlan_unopVar_sim_swap
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {name : String} {dist : Nat} {w : bytes32}
    {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hlen : dist < base.length)
    (hxbase : Operand.Var x ∈ base)
    (hval : operandVal vs lo (Operand.Var x) = some w)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
    (hswap : ∀ d, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                 stack := base ++ [Operand.Var out] } : PlanState).stack = some d →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := base ++ [Operand.Var out] }
            = doSwap d
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := base ++ [Operand.Var out] } →
            d ≤ 16 ∧ d < (base ++ [Operand.Var out]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f w) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts hstack0 hlive hnospill hlivex
      hdepth hsmall hpeek, hrev] at hblock ⊢
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by
    rw [emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek, hstack0]
  have hps1spill : AssocList.lookup Operand Nat
      (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.spilled (Operand.Var out) = none := by
    rw [emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall hpeek]; exact hspill
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbIE, hbS⟩ := asmBlockAt_append hblock
  rw [executePlan_append] at hbIE
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hbIE
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall
    hrel (by rw [hstack0]; exact hlen) hbI
  have hstacktop : as1.stack = w :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hval
  have hfresh1 : ¬ (Operand.Var out) ∈
      (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.stack := by
    rw [hps1stack]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hfresh h
    · rw [← h] at hxbase; exact hfresh hxbase
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_unop_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
        stack := stackPush (Operand.Var out)
          (stackPop 1 (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.stack) }
        : PlanState)
      = { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hbSpc : as.pc + (executePlan ((emitInputPlan inst.opcode [Operand.Var x]
      nextLiveness ps).1 ++ [StackOp.SOEmit name])).length = as2.pc := by
    rw [executePlan_append, List.length_append, hpcE, hpcI]; omega
  rw [hbSpc] at hbS
  obtain ⟨as3, hrunS, hrelS, hpcS⟩ := optimisticSwapPlan_sim hrelE hbS hswap
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelS
  refine ⟨as3, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append, List.length_append]
    exact runAsm_compose (runAsm_compose hrunI hrunE) hrunS
  · rw [executePlan_append, List.length_append, List.length_append, hpcS, hpcE, hpcI]; omega

end EvmYul.Venom.Hol.Codegen

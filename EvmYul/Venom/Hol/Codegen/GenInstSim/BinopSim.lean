import EvmYul.Venom.Hol.Codegen.GenInstSim.ReorderLayout

/-!
# GenInstSim — BinopSim

generateRegularInstPlan assembly support + asm-stack-top extraction, then the full per-instruction
execution sim for the commutative all-literal binop through the real generator.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

variable {offsetToPc : AssocList Nat Nat}

/-! ## generateRegularInstPlan assembly support

Closed forms for the remaining `generateRegularInstPlan` let-chain steps of a commutative
all-literal binop: the operand list (`computeOperands`), the compute-step stack pop, and the
commutative cheaper-order `if`. -/

/-- `stackPop 2` removes the two operands a binop emitted, leaving the base. -/
theorem stackPop_2_append_pair (base : List Operand) (x y : Operand) :
    stackPop 2 (base ++ [x, y]) = base := by
  unfold stackPop; simp

/-- The commutative cheaper-order `if` resolves to its first branch for a distinct literal
    pair already on top: `reorderCost opsA (0) < reorderCost opsB (1)`. Reusable closed form
    of the commutative-branch dispatch for the `generateRegularInstPlan` assembly. -/
theorem commutative_choice_pair_lit {α : Type} (base : List Operand) (a b : bytes32)
    (ps2 : PlanState) (hstack : ps2.stack = base ++ [Operand.Lit a, Operand.Lit b])
    (hab : a ≠ b) (P Q : α) :
    (if reorderCost (reorderPlan [Operand.Lit a, Operand.Lit b] ps2).1
        < reorderCost (reorderPlan [Operand.Lit b, Operand.Lit a] ps2).1 then P else Q) = P := by
  rw [reorderPlan_pair_lit_nil base a b ps2 hstack hab,
      reorderPlan_swapped_pair_lit base a b ps2 hstack]
  simp [reorderCost]

/-- For any commutative opcode, `computeOperands` is the operand list *reversed* (none of the
    commutative opcodes is a jump/log opcode, so it hits the pure-op branch, which reverses
    semantic→stack order — see `computeOperands`). -/
theorem computeOperands_of_commutative (inst : Instruction)
    (h : isCommutative inst.opcode = true) : computeOperands inst = inst.operands.reverse := by
  unfold computeOperands; cases hop : inst.opcode <;> simp_all [isCommutative]

/-- No commutative opcode is `JMP`. -/
theorem commutative_ne_jmp {opc : Opcode} (h : isCommutative opc = true) : opc ≠ Opcode.JMP := by
  cases opc <;> simp_all [isCommutative]

/-- **Structural decomposition of `generateRegularInstPlan` for a commutative binop**, stated once
    for *any* operand pair (single live output, not halting). Every let-chain step resolves via the
    closed forms above: `computeOperands` gives the reversed operand list (commutative ⇒ not a
    jump/log opcode), the join is a no-op (not `JMP`), the commutative `if` picks `operands` (the
    positioned order costs 0, the swapped one costs one `SWAP1` — `reorderPlan_pair_nil` /
    `reorderPlan_swapped_pair`), the final reorder is a no-op, the compute pops the two operands
    and pushes the output, `generateEmitOps` yields `[SOEmit name]`, the dead-output pop is empty
    (output live). The plan is `inputOps ++ [SOEmit name] ++ optOps`, threaded through the
    optimistic swap and dead-spill release.

    Nothing here reads the operands' *class* — the only inputs are that the emitted pair lands
    positioned on `base` (`hemitstack`, supplied by the caller's `emitInputPlan_*_eq`) and that the
    two differ (`hqp`). So the literal, var, and **mixed Var/Lit** binops are all instances. -/
theorem genRegularInstPlan_commBinopPair_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {p q : Operand} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [q, p])
    (houts : inst.outputs = [out])
    (hqp : q ≠ p)
    (hlive : nextLiveness.contains out = true)
    (hemitstack : (emitInputPlan inst.opcode [p, q] nextLiveness ps).2.stack = base ++ [p, q]) :
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
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  -- The codegen reverses the operands (semantic→stack order), so the emitted pair is `[p, q]`.
  have hrev : inst.operands.reverse = [p, q] := by rw [hops]; rfl
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [p, q] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [p, q] := by
    have h2 : (emitInputPlan inst.opcode [p, q] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [← h2]; exact hemitstack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_nil base p q ps1 hps1' hqp,
        reorderPlan_swapped_pair base p q ps1 hps1',
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        reorderCost, hcomm, hjmp]

/-- **Structural decomposition for the MIRROR stack order.** Same as `genRegularInstPlan_commBinopPair_eq`
    but the emitted pair lands as `base ++ [x, y]` (operands' natural order) rather than
    `base ++ [reverse]`. The commutative cheaper-order `if` then picks the *other* branch — the
    operands' own order is already positioned (cost 0), `computeOperands` (the reverse) would cost a
    `SWAP1` — so the reorder is still nil and the plan is still bare. Used by the consuming
    dead-operand mirror case, where the generator emits nothing and the operands sit in `[x, y]`
    order (`y` on top). -/
theorem genRegularInstPlan_commBinopPairMirror_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y : Operand} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [x, y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hlive : nextLiveness.contains out = true)
    (hemitstack : (emitInputPlan inst.opcode [y, x] nextLiveness ps).2.stack = base ++ [x, y]) :
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
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  have hrev : inst.operands.reverse = [y, x] := by rw [hops]; rfl
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [y, x] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [x, y] := by
    have h2 : (emitInputPlan inst.opcode [y, x] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [← h2]; exact hemitstack
  have hmem : out ∈ nextLiveness := by simpa using hlive
  simp [generateEmitOps_evmName hname,
        reorderPlan_pair_nil base x y ps1 hps1' (Ne.symm hxy),
        reorderPlan_swapped_pair base x y ps1 hps1',
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        reorderCost, hcomm, hjmp]

/-- Structural decomposition of `generateRegularInstPlan` for a commutative binop with two
    distinct literal operands — the all-literal instance of `genRegularInstPlan_commBinopPair_eq`,
    whose `hemitstack` is `emitInputPlan_stack_allLit`. -/
theorem genRegularInstPlan_commBinopLit_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {a b : bytes32} {out : String} {base : List Operand} {name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
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
  have hallLit : ∀ op ∈ ([Operand.Lit b, Operand.Lit a] : List Operand), ∃ v, op = Operand.Lit v := by
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> exact ⟨_, rfl⟩
  refine genRegularInstPlan_commBinopPair_eq hname hcomm hops houts
    (fun h => hab (Operand.Lit.inj h)) hlive ?_
  rw [emitInputPlan_stack_allLit inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps hallLit,
      hstack0]

/-! ## Asm-stack-top extraction (compute-step precondition)

`emit_binop_sim` needs the operand values on top of the asm stack (`as.stack = v₁::v₂::rest`).
This extracts that from `planStackRel` once the plan stack is positioned as `base ++ [Lit a,
Lit b]` (which input-emission establishes). -/

theorem stackPeek_0_append_pair (base : List Operand) (x y : Operand) :
    stackPeek 0 (base ++ [x, y]) = y := by
  unfold stackPeek
  rw [show (base ++ [x, y]).length - 1 - 0 = base.length + 1 from by simp]
  exact getbang_append_pair_snd base x y

theorem stackPeek_1_append_pair (base : List Operand) (x y : Operand) :
    stackPeek 1 (base ++ [x, y]) = x := by
  unfold stackPeek
  rw [show (base ++ [x, y]).length - 1 - 1 = base.length from by simp]
  exact getbang_append_pair_fst base x y

/-- A list of length ≥ 2 is `get!0 :: get!1 :: drop 2`. -/
theorem list_eq_get2 {α} [Inhabited α] (l : List α) (h : 2 ≤ l.length) :
    l = l[0]! :: l[1]! :: l.drop 2 := by
  match l with
  | c0 :: c1 :: rest => rfl
  | [] => simp at h
  | [c0] => simp at h

/-- **Asm stack top two = the plan-top operand pair's values.** With the plan stack positioned as
    `base ++ [p, q]` and the two operands valued `wp`/`wq`, the asm stack is `wq :: wp :: rest`
    (plan LAST = asm TOS). This produces `emit_binop_sim`'s `hstack`. Class-agnostic: `p` and `q`
    may each be a literal or a var, so the literal, var, and **mixed Var/Lit** pairs are all
    instances (a literal's `operandVal` is `rfl`). -/
theorem venomAsmRel_asmStack_top2 {lo ps vs as} {base : List Operand} {p q : Operand}
    {wp wq : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [p, q])
    (hvp : operandVal vs lo p = some wp)
    (hvq : operandVal vs lo q = some wq) :
    as.stack = wq :: wp :: as.stack.drop 2 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 2 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = wq := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_pair, hvq] at hp
    exact (Option.some.inj hp).symm
  have h1 : as.stack[1]! = wp := by
    have hp := planStackRel_peek hStk (dist := 1) (by rw [hstack]; simp)
    rw [hstack, stackPeek_1_append_pair, hvp] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get2 as.stack hge]
  rw [h0, h1]

/-- With the plan stack positioned as `base ++ [Lit a, Lit b]`, the asm stack is
    `b :: a :: rest` — the operand values on top (TOS = `b`, the last operand). This produces
    `emit_binop_sim`'s `hstack`. -/
theorem venomAsmRel_asmStack_top2_lit {lo ps vs as} {base : List Operand} {a b : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    as.stack = b :: a :: as.stack.drop 2 :=
  venomAsmRel_asmStack_top2 hrel hstack rfl rfl

/-- With plan stack `base ++ [Var y, Var x]` and `x`/`y` valued `wx`/`wy` in `vs`, the asm stack
    top two are `wx` (TOS) and `wy`. The var counterpart of `venomAsmRel_asmStack_top2_lit` (values
    from `operandVal`). -/
theorem venomAsmRel_asmStack_top2_var {lo ps vs as} {base : List Operand} {x y : String}
    {wx wy : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var x])
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy) :
    as.stack = wx :: wy :: as.stack.drop 2 :=
  venomAsmRel_asmStack_top2 hrel hstack hvy hvx

/-- **Asm stack top = the plan-top operands' values.** If the plan stack is `base ++ ops` and each of
    `ops` evaluates (in order) to `vals`, then the asm stack's top `ops.length` entries are `vals`
    reversed (plan LAST = asm TOS), the rest untouched. The N-operand generalisation of
    `venomAsmRel_asmStack_top2_var` — the connector between an N-input emit and an N-ary op's step
    (e.g. the 7 operands of a `CALL`). -/
theorem venomAsmRel_asmStack_topOps {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    {as : AsmState} {base ops : List Operand} {vals : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ ops)
    (hvals : List.map (operandVal vs lo) ops = List.map some vals) :
    as.stack = vals.reverse ++ as.stack.drop ops.length := by
  obtain ⟨hStk, _⟩ := hrel
  have hlenpv : ops.length = vals.length := by
    have := congrArg List.length hvals; simpa using this
  have hlenas : ps.stack.length = as.stack.length := hStk.1
  have hge : ops.length ≤ as.stack.length := by
    rw [← hlenas, hstack, List.length_append]; omega
  have htake : as.stack.take ops.length = vals.reverse := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_reverse]; omega
    · intro i hi1 hi2
      have hi : i < ops.length := by rw [List.length_take] at hi1; omega
      have hivals : i < vals.length := by omega
      have hjops : ops.length - 1 - i < ops.length := by omega
      have hjvals : ops.length - 1 - i < vals.length := by omega
      have hps_i : i < ps.stack.length := by rw [hstack, List.length_append]; omega
      have hrel_i := hStk.2 i hps_i
      have hrevidx : ps.stack.reverse[i]! = ops[ops.length - 1 - i]'hjops := by
        rw [hstack, List.reverse_append,
            getElem!_pos _ i (by rw [List.length_append, List.length_reverse]; omega),
            List.getElem_append_left (by rw [List.length_reverse]; omega), List.getElem_reverse]
      rw [hrevidx] at hrel_i
      have hmapj : operandVal vs lo (ops[ops.length - 1 - i]'hjops) = some (vals[ops.length - 1 - i]'hjvals) := by
        have h : (List.map (operandVal vs lo) ops)[ops.length - 1 - i]? = (List.map some vals)[ops.length - 1 - i]? := by
          rw [hvals]
        rw [List.getElem?_map, List.getElem?_map,
            List.getElem?_eq_getElem hjops, List.getElem?_eq_getElem hjvals] at h
        simpa using h
      rw [hmapj] at hrel_i
      have hasi : as.stack[i]'(by omega) = vals[ops.length - 1 - i]'hjvals := by
        rw [← getElem!_pos as.stack i (by omega)]
        exact (Option.some.inj hrel_i).symm
      rw [List.getElem_take, hasi, List.getElem_reverse]
      congr 1
      omega
  calc as.stack = as.stack.take ops.length ++ as.stack.drop ops.length := (List.take_append_drop _ _).symm
    _ = vals.reverse ++ as.stack.drop ops.length := by rw [htake]

/-- **CALL step in block context.** Wraps `call_step_stateAgree` + `asmStep_call_ok` into a runnable
    one-step block: given the 7 operand values on the asm stack top and the shared fields agreeing,
    running the `SOEmit "CALL"` op (`runAsm 1`) reaches a state agreeing with the Venom
    `stepExternalCall` writeback on all shared `venomAsmRel` fields, advancing the pc by 1. The asm-
    execution half of a CALL block sim (the emission half is `emitInputPlan_allVars_sim` +
    `venomAsmRel_asmStack_topOps`). -/
theorem call_asmStep_block_sim {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {gas addr value aOff aSz rOff rSz : bytes32} {stk : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : as.stack = gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = as.accounts) (hmem : vs.memory = as.memory)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcall : evmCall subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as.memory.readWithPadding aOff.toNat aSz.toNat).toList as.txCtx.gasprice 0 (!as.callCtx.static)
      = (success, newAccs, ret))
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALL"])) :
    ∃ s'', runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory = s''.memory
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).transient = s''.transient
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).logs = s''.logs
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).callCtx = s''.callCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).txCtx = s''.txCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).blockCtx = s''.blockCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).code = s''.code
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).prevHashes = s''.prevHashes
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk ∧ s''.pc = as.pc + 1 := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  obtain ⟨s'', hstep, hasmOK, hacc', hmem', hrd', htr', hlg', hcc', htx', hbc', hcode', hph', hout', hstk'⟩ :=
    call_step_stateAgree hopc heval hout hstk hacc hmem hcc htx htr hlg hbc hcode hph hcall
  have hstepeq : asmStep offsetToPc prog as = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpc hget]; exact hasmOK
  have hpcadv : s''.pc = as.pc + 1 := by
    have hcalleq : asmCall as = AsmResult.AsmOK s'' := hasmOK
    unfold asmCall at hcalleq
    rw [hstk] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  refine ⟨s'', ?_, hstep, hacc', hmem', hrd', htr', hlg', hcc', htx', hbc', hcode', hph', hout', hstk', hpcadv⟩
  show runAsm 1 offsetToPc prog as = AsmResult.AsmOK s''
  rw [runAsm_succ_ok hpc hstepeq]; rfl

/-! ## Per-instruction execution sim (commutative all-literal binop)

The capstone of this file: running the generated plan for a commutative binop with two
literal operands preserves `venomAsmRel` across the Venom step. Composes the input-emission
sim, `emit_binop_sim`, and `releaseDeadSpills_sim` over the structural decomposition. -/

theorem bytes32_add_comm (a b : bytes32) : a + b = b + a := by
  show UInt256.add a b = UInt256.add b a
  simp only [UInt256.add]; rw [add_comm a.val b.val]

theorem bytes32_mul_comm (a b : bytes32) : a * b = b * a := by
  show UInt256.mul a b = UInt256.mul b a
  simp only [UInt256.mul]; rw [mul_comm a.val b.val]

theorem optimisticSwapPlan_terminator {dfg : DfgAnalysis} {inst : Instruction}
    {nl : List String} {ps : PlanState} :
    optimisticSwapPlan dfg inst nl true ps = ([], ps) := by
  unfold optimisticSwapPlan; simp

/-- Emitting one literal input is a single `PUSH`. -/
theorem emitOneInput_lit_eq (opc : Opcode) (nl : List String) (v : bytes32) (p : PlanState) :
    emitOneInput opc nl (Operand.Lit v) p
      = ([StackOp.SOPush (Operand.Lit v)], { p with stack := stackPush (Operand.Lit v) p.stack }) := by
  unfold emitOneInput
  simp only [isVarOperand, Bool.false_and, Bool.false_eq_true, if_false, List.nil_append]

/-- Emitting a literal pair is two `PUSH`es; the operands land on top. -/
theorem emitInputPlan_pair_lit_eq (opc : Opcode) (nl : List String) (a b : bytes32) (ps : PlanState) :
    emitInputPlan opc [Operand.Lit a, Operand.Lit b] nl ps
      = ([StackOp.SOPush (Operand.Lit a), StackOp.SOPush (Operand.Lit b)],
         { ps with stack := ps.stack ++ [Operand.Lit a, Operand.Lit b] }) := by
  unfold emitInputPlan
  simp only [List.foldl_cons, List.foldl_nil, emitOneInput_lit_eq, stackPush, List.nil_append,
             List.append_assoc, List.cons_append]

/-- Input-emission sim for a literal pair: run the two `PUSH`es (composes two
    `emitOneInput_sim_lit`s). -/
theorem emitInputPlan_pair_lit_sim {opc nl a b ps lo vs as prog}
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Lit a, Operand.Lit b] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Lit a, Operand.Lit b] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Lit a, Operand.Lit b] nl ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (emitInputPlan opc [Operand.Lit a, Operand.Lit b] nl ps).1).length := by
  rw [emitInputPlan_pair_lit_eq] at hblock ⊢
  rw [show ([StackOp.SOPush (Operand.Lit a), StackOp.SOPush (Operand.Lit b)] : List StackOp)
        = [StackOp.SOPush (Operand.Lit a)] ++ [StackOp.SOPush (Operand.Lit b)] from rfl,
      executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    emitOneInput_sim_lit (emitOneInput_lit_eq opc nl a ps) hrel hb1
  have hb2' : asmBlockAt prog as1.pc (executePlan [StackOp.SOPush (Operand.Lit b)]) := by
    rw [hpc1]; exact hb2
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emitOneInput_sim_lit (emitOneInput_lit_eq opc nl b _) hrel1 hb2'
  refine ⟨as2, ?_, ?_, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · simpa [stackPush, List.append_assoc] using hrel2
  · rw [List.length_append, hpc2, hpc1]; omega

/-- Input-emission sim for a var pair `[Var y, Var x]` (both live, non-spilled): run the two `DUP`s
    (composes two `doDup_sim`s). Unlike the literal pair, the second operand's depth `d_x'` is in the
    post-first-DUP stack `stackDup d_y ps.stack` (the stack grew by 1), supplied as a hypothesis. -/
theorem emitInputPlan_pair_var_sim {opc nl x y ps lo vs as prog d_y d_x'}
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hleny : d_y < ps.stack.length)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15)
    (hlenx' : d_x' < (stackDup d_y ps.stack).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps).1).length ∧
           as'.memory = as.memory := by
  have hemitY : emitOneInput opc nl (Operand.Var y) ps = doDup d_y ps := by
    rcases hdd : doDup d_y ps with ⟨_, _⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill_y, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivey, if_true, hdepth_y, hdd, List.nil_append]
  have hdoY : doDup d_y ps
      = ([StackOp.SODup (d_y + 1)], { ps with stack := stackDup d_y ps.stack }) := by
    unfold doDup; rw [if_pos hsmall_y]
  set ps1 : PlanState := { ps with stack := stackDup d_y ps.stack } with hps1def
  have hemitX : emitOneInput opc nl (Operand.Var x) ps1 = doDup d_x' ps1 := by
    rcases hdd : doDup d_x' ps1 with ⟨_, _⟩
    unfold emitOneInput
    simp only [isVarOperand, (show alookup' ps1.spilled (Operand.Var x) = none from hnospill_x),
      Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, hlivex, if_true,
      (show stackGetDepth (Operand.Var x) ps1.stack = some d_x' from hdepth_x'), hdd, List.nil_append]
  have hdoX : doDup d_x' ps1
      = ([StackOp.SODup (d_x' + 1)], { ps1 with stack := stackDup d_x' ps1.stack }) := by
    unfold doDup; rw [if_pos hsmall_x']
  -- the two-instruction fold (both DUPs reduced)
  have hfold : emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps
      = ([StackOp.SODup (d_y + 1)] ++ [StackOp.SODup (d_x' + 1)],
         { ps1 with stack := stackDup d_x' ps1.stack }) := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hemitY, hdoY, hemitX, hdoX, List.nil_append]
  rw [hfold] at hblock ⊢
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ := doDup_sim hdoY hsmall_y hrel hleny hb1
  have hb2' : asmBlockAt prog as1.pc (executePlan [StackOp.SODup (d_x' + 1)]) := by
    rw [hpc1]; exact hb2
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    doDup_sim hdoX hsmall_x' hrel1 (by rw [hps1def]; exact hlenx') hb2'
  have hlenas_y : d_y < as.stack.length := by obtain ⟨hStk, _⟩ := hrel; rw [← hStk.1]; exact hleny
  have hlenas_x : d_x' < as1.stack.length := by
    obtain ⟨hStk1, _⟩ := hrel1; rw [← hStk1.1, hps1def]; exact hlenx'
  refine ⟨as2, ?_, hrel2, ?_,
    (doDup_runAsm_mem hsmall_x' hlenas_x hb2' hrun2).trans
      (doDup_runAsm_mem hsmall_y hlenas_y hb1 hrun1)⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · rw [List.length_append, hpc2, hpc1]; omega

/-- **Duping a var puts it at depth 0.** After `stackDup d` (which appends the peeked element to the
    top), if that peek was `Var x` (`d` = `x`'s depth) then `Var x` is now the top (depth 0). The
    same-var analogue of `stackGetDepth_append_ne` — the fact that lets the (distinctness-agnostic)
    `emitInputPlan_pair_var_sim` also cover a *repeated* operand `[Var x, Var x]`. -/
theorem stackGetDepth_stackDup_self {x : String} (stk : List Operand) (d : Nat)
    (hd : stackGetDepth (Operand.Var x) stk = some d) :
    stackGetDepth (Operand.Var x) (stackDup d stk) = some 0 := by
  have hpeek : stackPeek d stk = Operand.Var x := stackGetDepth_peek hd
  unfold stackGetDepth stackDup
  rw [hpeek]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, stackFind, beq_self_eq_true, if_true]

/-- **Input-emission sim for a *repeated* var operand `[Var x, Var x]`.** The `x = y` case the
    distinctness assumption `x ≠ y` (in the store/binop classifiers) excluded: the codegen dups `x`
    from its slot, then dups it again from the top (depth `0`). Reuses the distinctness-agnostic
    `emitInputPlan_pair_var_sim` at `d_x' = 0` (via `stackGetDepth_stackDup_self`), so a same-var
    2-input op's operand-emission plan-sim needs no new distinct-depth reasoning — closing the
    operand-emission half of the `x = y` coverage gap. -/
theorem emitInputPlan_pair_var_same_sim {opc nl x ps lo vs as prog offsetToPc d_x}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlive : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some d_x)
    (hsmall : d_x ≤ 15) (hlen : d_x < ps.stack.length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var x, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var x, Operand.Var x] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var x, Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (emitInputPlan opc [Operand.Var x, Operand.Var x] nl ps).1).length ∧
           as'.memory = as.memory := by
  have hd0 : stackGetDepth (Operand.Var x) (stackDup d_x ps.stack) = some 0 :=
    stackGetDepth_stackDup_self ps.stack d_x hdepth
  have hlen0 : 0 < (stackDup d_x ps.stack).length := by unfold stackDup; simp
  exact emitInputPlan_pair_var_sim (offsetToPc := offsetToPc)
    hnospill hlive hdepth hsmall hlen hnospill hlive hd0 (by omega) hlen0 hrel hblock

/-! ## Mixed Var/Lit operand pairs

The all-literal (`PUSH ; PUSH`) and all-var (`DUP ; DUP`) input plans are the two extremes; a real
binop routinely mixes them (`ADD %x, 5`). Emission is still one asm instruction per operand, but the
classes *interleave*: a literal's `PUSH` is unconditional and grows the stack, so a var emitted after
one is DUP'd from a depth measured on the already-grown stack. Stating each operand's step in the one
shape both classes share — *one op, and the operand itself appended to the plan stack* — makes the
two-operand fold class-agnostic, and all four class combinations become instances of it. -/

/-- Emitting one live, non-spilled var input is a single `DUP` that appends the var itself
    (`stackDup d s = s ++ [stackPeek d s]`, and the depth pins the peek). The var counterpart of
    `emitOneInput_lit_eq`, in the same append shape. -/
theorem emitOneInput_var_eq {opc nl x ps d}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlive : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some d)
    (hsmall : d ≤ 15) :
    emitOneInput opc nl (Operand.Var x) ps
      = ([StackOp.SODup (d + 1)], { ps with stack := ps.stack ++ [Operand.Var x] }) := by
  have hdup : stackDup d ps.stack = ps.stack ++ [Operand.Var x] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth]
  have hdo : doDup d ps
      = ([StackOp.SODup (d + 1)], { ps with stack := ps.stack ++ [Operand.Var x] }) := by
    unfold doDup; rw [if_pos hsmall, hdup]
  have hemit : emitOneInput opc nl (Operand.Var x) ps = doDup d ps := by
    rcases hdd : doDup d ps with ⟨_, _⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlive, if_true, hdepth, hdd, List.nil_append]
  rw [hemit, hdo]

/-- **The two-operand input fold, stated once.** Given each operand's closed form — one stack op,
    the operand appended — the fold emits both in order and lands the pair on top of the original
    stack. `emitOneInput_lit_eq` and `emitOneInput_var_eq` supply the two hypothesis shapes, so the
    literal, var, and both mixed pairs are instances; the second operand's hypothesis is stated at
    the *post-first-operand* state, which is exactly where the interleaving lives. -/
theorem emitInputPlan_pair_eq {opc nl ps} {p q : Operand} {s1 s2 : StackOp}
    (h1 : emitOneInput opc nl p ps = ([s1], { ps with stack := ps.stack ++ [p] }))
    (h2 : emitOneInput opc nl q { ps with stack := ps.stack ++ [p] }
            = ([s2], { ps with stack := ps.stack ++ [p] ++ [q] })) :
    emitInputPlan opc [p, q] nl ps = ([s1, s2], { ps with stack := ps.stack ++ [p, q] }) := by
  unfold emitInputPlan
  simp only [List.foldl_cons, List.foldl_nil, h1, h2, List.nil_append, List.append_assoc,
    List.cons_append]

/-- **Mixed input plan `[Lit b, Var x]`** — the emit order of the source shape `OP %x, b`
    (`computeOperands` reverses): one `PUSH`, then one `DUP`. The var's depth `d_x` is measured on
    the *already-pushed* stack `ps.stack ++ [Lit b]` — the PUSH-then-DUP interleaving that neither
    fixed-class pair lemma needed. -/
theorem emitInputPlan_pair_litVar_eq {opc nl ps} {b : bytes32} {x : String} {d_x : Nat}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlive : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Lit b]) = some d_x)
    (hsmall : d_x ≤ 15) :
    emitInputPlan opc [Operand.Lit b, Operand.Var x] nl ps
      = ([StackOp.SOPush (Operand.Lit b), StackOp.SODup (d_x + 1)],
         { ps with stack := ps.stack ++ [Operand.Lit b, Operand.Var x] }) :=
  emitInputPlan_pair_eq (emitOneInput_lit_eq opc nl b ps)
    (emitOneInput_var_eq hnospill hlive hdepth hsmall)

/-- **Mixed input plan `[Var y, Lit a]`** — the emit order of the source shape `OP a, %y`: one `DUP`,
    then one `PUSH`. The mirror of `emitInputPlan_pair_litVar_eq`; here the var goes first, so its
    depth is measured on the original stack and the literal's `PUSH` carries no side condition. -/
theorem emitInputPlan_pair_varLit_eq {opc nl ps} {y : String} {a : bytes32} {d_y : Nat}
    (hnospill : alookup' ps.spilled (Operand.Var y) = none)
    (hlive : nl.contains y = true)
    (hdepth : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall : d_y ≤ 15) :
    emitInputPlan opc [Operand.Var y, Operand.Lit a] nl ps
      = ([StackOp.SODup (d_y + 1), StackOp.SOPush (Operand.Lit a)],
         { ps with stack := ps.stack ++ [Operand.Var y, Operand.Lit a] }) :=
  emitInputPlan_pair_eq (emitOneInput_var_eq hnospill hlive hdepth hsmall)
    (emitOneInput_lit_eq opc nl a _)

/-- One literal input's sim in the append shape: `PUSH v` runs one instruction and appends
    `Lit v` to the plan stack. -/
theorem emitOneInput_sim_lit_append {opc : Opcode} {nl : List String} {v ps lo vs as prog}
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOPush (Operand.Lit v)])) :
    ∃ as', runAsm (executePlan [StackOp.SOPush (Operand.Lit v)]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := ps.stack ++ [Operand.Lit v] } vs as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOPush (Operand.Lit v)]).length :=
  emitOneInput_sim_lit (emitOneInput_lit_eq opc nl v ps) hrel hblock

/-- One var input's sim in the same append shape: `DUP (d+1)` runs one instruction and appends
    `Var x` to the plan stack. Together with `emitOneInput_sim_lit_append` this is what lets a
    mixed pair compose one step of each class. -/
theorem emitOneInput_sim_var_append {x ps d lo vs as prog}
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some d)
    (hsmall : d ≤ 15) (hlen : d < ps.stack.length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SODup (d + 1)])) :
    ∃ as', runAsm (executePlan [StackOp.SODup (d + 1)]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := ps.stack ++ [Operand.Var x] } vs as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SODup (d + 1)]).length := by
  have hdup : stackDup d ps.stack = ps.stack ++ [Operand.Var x] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth]
  have hdo : doDup d ps
      = ([StackOp.SODup (d + 1)], { ps with stack := ps.stack ++ [Operand.Var x] }) := by
    unfold doDup; rw [if_pos hsmall, hdup]
  exact doDup_sim hdo hsmall hrel hlen hblock

/-- Input-emission sim for the mixed pair `[Lit b, Var x]`: run the `PUSH`, then the `DUP` from the
    grown stack. The **PUSH-and-DUP interleaving** lemma — the all-literal (`emitInputPlan_pair_lit_sim`)
    and all-var (`emitInputPlan_pair_var_sim`) sims only ever composed two steps of one class. -/
theorem emitInputPlan_pair_litVar_sim {opc nl ps lo vs as prog} {b : bytes32} {x : String}
    {d_x : Nat}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlive : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Lit b]) = some d_x)
    (hsmall : d_x ≤ 15)
    (hlen : d_x < (ps.stack ++ [Operand.Lit b]).length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Lit b, Operand.Var x] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Lit b, Operand.Var x] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Lit b, Operand.Var x] nl ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (emitInputPlan opc [Operand.Lit b, Operand.Var x] nl ps).1).length := by
  rw [emitInputPlan_pair_litVar_eq hnospill hlive hdepth hsmall] at hblock ⊢
  rw [show ([StackOp.SOPush (Operand.Lit b), StackOp.SODup (d_x + 1)] : List StackOp)
        = [StackOp.SOPush (Operand.Lit b)] ++ [StackOp.SODup (d_x + 1)] from rfl,
      executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    emitOneInput_sim_lit_append (opc := opc) (nl := nl) hrel hb1
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emitOneInput_sim_var_append (x := x) hdepth hsmall hlen hrel1 (by rw [hpc1]; exact hb2)
  refine ⟨as2, ?_, ?_, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · simpa [List.append_assoc] using hrel2
  · rw [List.length_append, hpc2, hpc1]; omega

/-- Input-emission sim for the mixed pair `[Var y, Lit a]`: run the `DUP`, then the `PUSH` — the
    mirror of `emitInputPlan_pair_litVar_sim`. -/
theorem emitInputPlan_pair_varLit_sim {opc nl ps lo vs as prog} {y : String} {a : bytes32}
    {d_y : Nat}
    (hnospill : alookup' ps.spilled (Operand.Var y) = none)
    (hlive : nl.contains y = true)
    (hdepth : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall : d_y ≤ 15)
    (hlen : d_y < ps.stack.length)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (emitInputPlan opc [Operand.Var y, Operand.Lit a] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var y, Operand.Lit a] nl ps).1).length
             offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var y, Operand.Lit a] nl ps).2 vs as' ∧
           as'.pc = as.pc
             + (executePlan (emitInputPlan opc [Operand.Var y, Operand.Lit a] nl ps).1).length := by
  rw [emitInputPlan_pair_varLit_eq hnospill hlive hdepth hsmall] at hblock ⊢
  rw [show ([StackOp.SODup (d_y + 1), StackOp.SOPush (Operand.Lit a)] : List StackOp)
        = [StackOp.SODup (d_y + 1)] ++ [StackOp.SOPush (Operand.Lit a)] from rfl,
      executePlan_append] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    emitOneInput_sim_var_append (x := y) hdepth hsmall hlen hrel hb1
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emitOneInput_sim_lit_append (opc := opc) (nl := nl) (v := a) hrel1 (by rw [hpc1]; exact hb2)
  refine ⟨as2, ?_, ?_, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrun1 hrun2
  · simpa [List.append_assoc] using hrel2
  · rw [List.length_append, hpc2, hpc1]; omega

/-! ## DEAD var operands — the consuming regime

Every arm above emits one instruction per operand and *grows* the plan stack. That is the
**duplicated-use** regime: `emitOneInput` only DUPs a var that is still live after the instruction.
For a var whose last use IS this instruction, it emits **nothing** — the value is already on the
stack and the opcode consumes it in place, so the stack *shrinks*. Since the last use of any value
is dead there, this is the ordinary SSA shape, not a corner case.

What makes the plan layer reusable unchanged: `genRegularInstPlan_commBinopPair_eq` constrains only
*where the operands end up* (`hemitstack`), never how they got there. Emission that runs zero
instructions and leaves the operands already positioned satisfies it just as DUP-emission does. -/

/-- Emitting a **dead** (and non-spilled) var input emits nothing and leaves the plan state alone —
    the operand is already on the stack and the opcode will consume it in place. -/
theorem emitOneInput_deadVar_eq {opc nl x ps}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hdead : nl.contains x = false) :
    emitOneInput opc nl (Operand.Var x) ps = ([], ps) := by
  unfold emitOneInput
  simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
    if_false, hdead, List.nil_append]

/-- A pair of dead var operands emits nothing at all: the input plan is empty and the plan state is
    untouched, so the operands stay exactly where the previous instructions left them. -/
theorem emitInputPlan_pair_dead_eq {opc nl x y ps}
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nl.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nl.contains x = false) :
    emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps = ([], ps) := by
  unfold emitInputPlan
  simp only [List.foldl_cons, List.foldl_nil,
    emitOneInput_deadVar_eq hnospill_y hdead_y, emitOneInput_deadVar_eq hnospill_x hdead_x,
    List.append_nil]

/-- Growing-stack depth chain for N-input emission: emitting `vs` (all live vars) from a base stack
    DUPs each `v_i` at depth `d_i` computed on the stack grown by the prior DUPs. The structured
    hypothesis behind `emitInputPlan_allVars_eq`; the fixed `single`/`pair`/`triple` `_var_eq` lemmas
    are its 1-, 2-, 3-element specialisations (their `stackDup d_y ps.stack` = `ps.stack ++ [Var y]`). -/
def emitDepthsOk (nl : List String) : List String → List Nat → List Operand → Prop
  | [], [], _ => True
  | v :: vs, d :: dists, base =>
      nl.contains v = true ∧ stackGetDepth (Operand.Var v) base = some d ∧ d ≤ 15 ∧
      emitDepthsOk nl vs dists (base ++ [Operand.Var v])
  | _, _, _ => False

/-- **Closed form of the N-input all-variable emission plan.** The general induction behind the fixed
    `single`/`pair`/`triple` `_var_eq` lemmas: emitting a list of distinct live non-spilled vars DUPs
    each at its (growing-stack) depth, leaving `ps.stack ++ vs.map Var`. Unblocks arbitrary-arity ops
    (e.g. LOG0–LOG4) whose input count exceeds the hand-rolled 3. -/
theorem emitInputPlan_allVars_eq (opc : Opcode) (nl : List String) :
    ∀ (vs : List String) (dists : List Nat) (ps : PlanState),
      (∀ v ∈ vs, alookup' ps.spilled (Operand.Var v) = none) →
      emitDepthsOk nl vs dists ps.stack →
      emitInputPlan opc (vs.map Operand.Var) nl ps
        = (dists.map (fun d => StackOp.SODup (d + 1)),
           { ps with stack := ps.stack ++ vs.map Operand.Var }) := by
  intro vs
  induction vs with
  | nil =>
    intro dists ps _ hd
    cases dists with
    | nil =>
      show emitInputPlan opc [] nl ps = _
      unfold emitInputPlan
      simp
    | cons d ds => exact hd.elim
  | cons v vs ih =>
    intro dists ps hns hd
    cases dists with
    | nil => exact hd.elim
    | cons d ds =>
      obtain ⟨hlive, hdepth, hsmall, htail⟩ := hd
      have hnsv : alookup' ps.spilled (Operand.Var v) = none := hns v List.mem_cons_self
      have hemit : emitOneInput opc nl (Operand.Var v) ps
          = ([StackOp.SODup (d + 1)], { ps with stack := ps.stack ++ [Operand.Var v] }) := by
        have hd1 : emitOneInput opc nl (Operand.Var v) ps = doDup d ps := by
          rcases hdd : doDup d ps with ⟨_, _⟩
          unfold emitOneInput
          simp only [isVarOperand, hnsv, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
            if_false, hlive, if_true, hdepth, hdd, List.nil_append]
        have hd2 : doDup d ps = ([StackOp.SODup (d + 1)], { ps with stack := stackDup d ps.stack }) := by
          unfold doDup; rw [if_pos hsmall]
        have hpeek : stackPeek d ps.stack = Operand.Var v := stackGetDepth_peek hdepth
        have hdup : stackDup d ps.stack = ps.stack ++ [Operand.Var v] := by unfold stackDup; rw [hpeek]
        rw [hd1, hd2, hdup]
      set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v] } with hps1
      have hih : emitInputPlan opc (vs.map Operand.Var) nl ps1
          = (ds.map (fun d => StackOp.SODup (d + 1)), { ps1 with stack := ps1.stack ++ vs.map Operand.Var }) := by
        apply ih ds ps1
        · intro v' hv'; rw [hps1]; exact hns v' (List.mem_cons_of_mem _ hv')
        · rw [hps1]; exact htail
      have hpeel : emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps
          = ([StackOp.SODup (d + 1)] ++ (emitInputPlan opc (vs.map Operand.Var) nl ps1).1,
             (emitInputPlan opc (vs.map Operand.Var) nl ps1).2) := by
        show (Operand.Var v :: vs.map Operand.Var).foldl
            (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps) = _
        rw [List.foldl_cons]
        simp only [List.nil_append, hemit]
        exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (vs.map Operand.Var) [StackOp.SODup (d + 1)] ps1
      show emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps = _
      rw [hpeel, hih]
      refine Prod.ext ?_ ?_
      · show [StackOp.SODup (d + 1)] ++ ds.map (fun d => StackOp.SODup (d + 1))
          = (d :: ds).map (fun d => StackOp.SODup (d + 1))
        rw [List.map_cons]; rfl
      · show ({ ps1 with stack := ps1.stack ++ vs.map Operand.Var } : PlanState)
          = { ps with stack := ps.stack ++ (v :: vs).map Operand.Var }
        rw [hps1]
        congr 1
        rw [List.map_cons, List.append_assoc]
        rfl

/-- **Runnable N-input all-variable emission sim.** The memory-preserving sim companion of
    `emitInputPlan_allVars_eq`: running the `N` DUPs preserves `venomAsmRel` (with the same Venom
    state — emission doesn't touch it), advances the pc by the plan length, and leaves asm memory
    unchanged. The N-input generalisation of `emitInputPlan_triple_var_sim_mem`; the per-DUP length
    side-conditions follow from the depth chain (`stackGetDepth_lt_length`), so `emitDepthsOk` is the
    only spec needed. Induction peels one DUP per step via `doDup_sim`/`doDup_runAsm_mem`. -/
theorem emitInputPlan_allVars_sim (opc : Opcode) (nl : List String) :
    ∀ (vs : List String) (dists : List Nat) (ps : PlanState)
      {lo : AssocList String Nat} {vst : VenomState} {as : AsmState} {prog : List AsmInst},
      (∀ v ∈ vs, alookup' ps.spilled (Operand.Var v) = none) →
      emitDepthsOk nl vs dists ps.stack →
      venomAsmRel lo ps vst as →
      asmBlockAt prog as.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1) →
      ∃ as', runAsm (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length offsetToPc prog as
               = AsmResult.AsmOK as' ∧
             venomAsmRel lo (emitInputPlan opc (vs.map Operand.Var) nl ps).2 vst as' ∧
             as'.pc = as.pc + (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps).1).length ∧
             as'.memory = as.memory := by
  intro vs
  induction vs with
  | nil =>
    intro dists ps lo vst as prog _ _ hrel hblock
    refine ⟨as, ?_, ?_, ?_, rfl⟩
    · show runAsm (executePlan (emitInputPlan opc [] nl ps).1).length offsetToPc prog as = _
      simp [emitInputPlan, executePlan, runAsm]
    · simpa [emitInputPlan] using hrel
    · simp [emitInputPlan, executePlan]
  | cons v vs ih =>
    intro dists ps lo vst as prog hns hd hrel hblock
    cases dists with
    | nil => exact hd.elim
    | cons d ds =>
      obtain ⟨hlive, hdepth, hsmall, htail⟩ := hd
      have hnsv : alookup' ps.spilled (Operand.Var v) = none := hns v List.mem_cons_self
      have hpeek : stackPeek d ps.stack = Operand.Var v := stackGetDepth_peek hdepth
      have hdup : stackDup d ps.stack = ps.stack ++ [Operand.Var v] := by unfold stackDup; rw [hpeek]
      set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v] } with hps1
      have hdo' : doDup d ps = ([StackOp.SODup (d + 1)], ps1) := by
        unfold doDup; rw [if_pos hsmall, hdup]
      have hemit : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SODup (d + 1)], ps1) := by
        rw [show emitOneInput opc nl (Operand.Var v) ps = doDup d ps from ?_, hdo']
        rcases hdd : doDup d ps with ⟨_, _⟩
        unfold emitOneInput
        simp only [isVarOperand, hnsv, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
          if_false, hlive, if_true, hdepth, hdd, List.nil_append]
      have hpeel : emitInputPlan opc (Operand.Var v :: vs.map Operand.Var) nl ps
          = ([StackOp.SODup (d + 1)] ++ (emitInputPlan opc (vs.map Operand.Var) nl ps1).1,
             (emitInputPlan opc (vs.map Operand.Var) nl ps1).2) := by
        show (Operand.Var v :: vs.map Operand.Var).foldl
            (fun acc op => (acc.1 ++ (emitOneInput opc nl op acc.2).1, (emitOneInput opc nl op acc.2).2)) ([], ps) = _
        rw [List.foldl_cons]
        simp only [List.nil_append, hemit]
        exact foldl_ops_acc (fun q op => emitOneInput opc nl op q) (vs.map Operand.Var) [StackOp.SODup (d + 1)] ps1
      rw [List.map_cons] at hblock ⊢
      rw [hpeel] at hblock ⊢
      rw [executePlan_append] at hblock ⊢
      obtain ⟨hb1, hbrest⟩ := asmBlockAt_append hblock
      have hlen : d < ps.stack.length := stackGetDepth_lt_length hdepth
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ := doDup_sim hdo' hsmall hrel hlen hb1
      have hmem1 : as1.memory = as.memory := doDup_runAsm_mem hsmall (hrel.1.1 ▸ hlen) hb1 hrun1
      have hbrest' : asmBlockAt prog as1.pc (executePlan (emitInputPlan opc (vs.map Operand.Var) nl ps1).1) := by
        rw [hpc1]; exact hbrest
      obtain ⟨as', hrun', hrel', hpc', hmem'⟩ :=
        ih ds ps1 (lo := lo) (vst := vst) (as := as1) (prog := prog)
          (fun v' hv' => hns v' (List.mem_cons_of_mem _ hv')) htail hrel1 hbrest'
      refine ⟨as', ?_, hrel', ?_, ?_⟩
      · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
      · rw [List.length_append, hpc', hpc1]; omega
      · rw [hmem', hmem1]

/-- **CALL block core sim: emit operands, then run CALL.** The end-to-end asm ↔ Venom correspondence
    for the `emit(operands) ++ [SOEmit "CALL"]` core of a compiled CALL block. The N-input emit
    (`emitInputPlan_allVars_sim`) places the operand values on the asm stack top (`venomAsmRel_asmStack_topOps`),
    and the CALL step (`call_asmStep_block_sim`) runs the shared sub-EVM. Result: running the whole
    segment reaches a state agreeing with the Venom `stepExternalCall` writeback on the shared observable
    `venomAsmRel` fields (accounts / memory / returndata) with the output var reading back `success`.
    Memory-agreement `vs.memory = as.memory` is an explicit hypothesis (as the store disjuncts carry
    `hmemsafe`); the residual for the full generated-plan block is the reorder + output-handling tail of
    `generateRegularInstPlan` and re-establishing `memoryRel`/`planSpillRel` from region write-safety. -/
theorem call_block_emit_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hmem : vs.memory = as.memory)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory = s''.memory
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.CALL nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.CALL nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨_, _, _, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  have hmem1 : vs.memory = as1.memory := by rw [hmem, hmemE]
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 (!as1.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1, ← hmem1]; exact hcall
  have hbCall' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALL"]) := by rw [hpcE]; exact hbCall
  obtain ⟨s'', hrunC, hstepV, hacc', hmem', hrd', _, _, _, _, _, _, _, hout', _, _⟩ :=
    call_asmStep_block_sim hopc heval hout htop hacc1.symm hmem1 hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1 hbCall'
  refine ⟨s'', ?_, hstepV, hacc', hmem', hrd', hout'⟩
  rw [executePlan_append, List.length_append]
  exact runAsm_compose hrunE hrunC


/-- **`memoryRel` survives writing the same data at the same offset into both memories.** In the
    write window both sides read the written byte; outside it both frame to the old bytes, which
    agreed. No region hypothesis needed for the relation itself (the window bytes are EQUAL, not
    merely unrelated) — only offset coverage for the write primitive's clean behavior. -/
theorem memoryRel_write_same {alloc : SpillAlloc} {m1 m2 data : ByteArray} {off : Nat}
    (hmem : memoryRel alloc m1 m2)
    (h1 : off ≤ m1.size) (h2 : off ≤ m2.size) :
    memoryRel alloc (data.write 0 m1 off data.size) (data.write 0 m2 off data.size) := by
  intro i hi
  by_cases hz : data.size = 0
  · rw [show data.write 0 m1 off data.size = m1 from by rw [hz]; simp [ByteArray.write],
        show data.write 0 m2 off data.size = m2 from by rw [hz]; simp [ByteArray.write]]
    exact hmem i hi
  · exact readByte_write_congr data m1 m2 off i (Nat.pos_of_ne_zero hz) h1 h2 (hmem i hi)

/-- Bytes at or above `off + data.size` are untouched by the write (the spill-slot frame for a
    below-`fnEom` writeback). -/
theorem readByte_write_frame_ge {data m : ByteArray} {off i : Nat}
    (hoff : off ≤ m.size) (hge : off + data.size ≤ i) :
    readByte i (data.write 0 m off data.size) = readByte i m := by
  by_cases hz : data.size = 0
  · rw [show data.write 0 m off data.size = m from by rw [hz]; simp [ByteArray.write]]
  · exact readByte_write_disjoint data m off i (Nat.pos_of_ne_zero hz) hoff (Or.inr hge)

/-- **CALL writeback agreement, `memoryRel` form.** For the same `evmCall` result over memories
    agreeing OUTSIDE the spill region, the two writebacks (same returndata slice, same offset,
    below the spill region) keep the memories `memoryRel`-related AND leave every asm byte at or
    above `fnEom` untouched — the spill slots survive, so `planSpillRel` can be re-established.
    The region-rebuild core the full-equality `callWriteback_asmCallWriteback_agree` could not
    provide. -/
theorem callWriteback_asmCallWriteback_agree_rel (alloc : SpillAlloc) (out : String)
    (rOff rSz : Nat) (success : bytes32) (newAccs : Accounts) (ret : List byte)
    (stk : List bytes32) (vs : VenomState) (s : AsmState)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hro1 : rOff ≤ vs.memory.size) (hro2 : rOff ≤ s.memory.size)
    (hbelow : rOff + rSz ≤ alloc.fnEom) :
    ∃ s'', asmCallWriteback rOff rSz success newAccs ret stk s = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff rSz success newAccs ret vs).accounts = s''.accounts
      ∧ memoryRel alloc (callWriteback out rOff rSz success newAccs ret vs).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i s.memory)
      ∧ (callWriteback out rOff rSz success newAccs ret vs).returndata = s''.returndata
      ∧ lookupVar out (callWriteback out rOff rSz success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  have hretsz : (⟨(ret.take rSz).toArray⟩ : ByteArray).size ≤ rSz := by
    show (ret.take rSz).toArray.size ≤ rSz
    rw [List.size_toArray]
    exact le_trans (List.length_take_le rSz ret) (Nat.le_refl _)
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · show (callWriteback _ _ _ _ _ _ _).accounts = newAccs
    simp only [callWriteback, updateVar, writeMemoryWithExpansion]
  · show memoryRel alloc (callWriteback _ _ _ _ _ _ _).memory _
    simp only [callWriteback, updateVar, writeMemoryWithExpansion]
    exact memoryRel_write_same hmem hro1 hro2
  · intro i hi
    show readByte i ((⟨(ret.take rSz).toArray⟩ : ByteArray).write 0 s.memory rOff
        (⟨(ret.take rSz).toArray⟩ : ByteArray).size) = readByte i s.memory
    exact readByte_write_frame_ge hro2 (by omega)
  · show (callWriteback _ _ _ _ _ _ _).returndata = ⟨ret.toArray⟩
    simp only [callWriteback, updateVar, writeMemoryWithExpansion]
  · simp only [callWriteback, updateVar, writeMemoryWithExpansion, lookupVar, alookup, ainsert,
      AssocList.insert, AssocList.lookup, beq_self_eq_true, if_true]

/-- **CALL evmCall alignment, `memoryRel` form**: with the calldata window below the spill
    region, both sides read the SAME calldata (`memoryRel_readWithPadding_slice`) and hence run
    the same sub-EVM call. -/
theorem asmCall_stepExternalCall_same_evmCall_rel {alloc : SpillAlloc}
    {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {gas addr value aOff aSz rOff rSz : bytes32} {stk : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : s.stack = gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = s.accounts)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcall : evmCall subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (s.memory.readWithPadding aOff.toNat aSz.toNat).toList s.txCtx.gasprice 0 (!s.callCtx.static)
      = (success, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmCall s = asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s := by
  have hcd : vs.memory.readWithPadding aOff.toNat aSz.toNat
      = s.memory.readWithPadding aOff.toNat aSz.toNat :=
    memoryRel_readWithPadding_slice hmem hargs haszlt
  have hcallV : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (readMemory aOff.toNat aSz.toNat vs).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hcd]; exact hcall
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcallV]
  · unfold asmCall; rw [hstk]; simp only [hcall]

/-- **CALL step, full `memoryRel` correspondence.** The region-rebuild replacement for
    `call_step_stateAgree`: instead of full memory equality, the memories are `memoryRel`-related
    with the calldata and returndata windows below the spill region — the step preserves the
    relation AND every asm spill byte, closing the documented residual for the full generated-plan
    CALL producer. -/
theorem call_step_stateAgree_rel {alloc : SpillAlloc} {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {gas addr value aOff aSz rOff rSz : bytes32}
    {stk : List bytes32} {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : as.stack = gas :: addr :: value :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = as.accounts)
    (hmem : memoryRel alloc vs.memory as.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size) (hro2 : rOff.toNat ≤ as.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ alloc.fnEom)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcall : evmCall subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as.memory.readWithPadding aOff.toNat aSz.toNat).toList as.txCtx.gasprice 0 (!as.callCtx.static)
      = (success, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmCall as = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ memoryRel alloc (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).transient = s''.transient
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).logs = s''.logs
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).callCtx = s''.callCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).txCtx = s''.txCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).blockCtx = s''.blockCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).code = s''.code
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).prevHashes = s''.prevHashes
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmCall_stepExternalCall_same_evmCall_rel hopc heval hout hstk hacc hmem hargs haszlt
      hcc htx hcall
  obtain ⟨s'', hs''eq, hacc', hmem', hframe', hrd', hout', hstk'⟩ :=
    callWriteback_asmCallWriteback_agree_rel alloc out rOff.toNat rSz.toNat success newAccs ret
      stk vs as hmem hro1 hro2 hretbelow
  have hconcrete := hs''eq
  simp only [asmCallWriteback] at hconcrete
  injection hconcrete with hc
  refine ⟨s'', hstep, by rw [hasmeq]; exact hs''eq, hacc', hmem', hframe', hrd',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout', hstk'⟩
  · show (callWriteback _ _ _ _ _ _ _).transient = s''.transient
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htr
  · show (callWriteback _ _ _ _ _ _ _).logs = s''.logs
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hlg
  · show (callWriteback _ _ _ _ _ _ _).callCtx = s''.callCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcc
  · show (callWriteback _ _ _ _ _ _ _).txCtx = s''.txCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htx
  · show (callWriteback _ _ _ _ _ _ _).blockCtx = s''.blockCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hbc
  · show (callWriteback _ _ _ _ _ _ _).code = s''.code
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcode
  · show (callWriteback _ _ _ _ _ _ _).prevHashes = s''.prevHashes
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hph

/-- **CALL block core sim, `memoryRel` form** — the region-rebuild producer core. Emits the 7
    operands and runs CALL under the honest `venomAsmRel` memory conjunct (`memoryRel`, memories
    agree OUTSIDE the spill region) instead of full equality: the calldata/returndata windows lie
    below `fnEom`, so both sides run the same sub-EVM call, the writebacks keep the memories
    related, and every asm spill byte survives (`planSpillRel` re-establishable). Replaces
    `call_block_emit_sim`'s `vs.memory = as.memory` hypothesis — the documented residual. -/
theorem call_block_emit_sim_rel {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ ps.alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ ps.alloc.fnEom)
    (hfnEom : ps.alloc.fnEom ≤ as.memory.size)
    (hcall : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (vs.memory.readWithPadding aOff.toNat aSz.toNat).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ memoryRel ps.alloc
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory s''.memory
      ∧ (∀ i, ps.alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.CALL nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.CALL nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨_, _, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  have hps'alloc : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  rw [hps'alloc] at hmemrel1
  have hmemrel1' : memoryRel ps.alloc vs.memory as1.memory := hmemrel1
  have hro2 : rOff.toNat ≤ as1.memory.size := by
    rw [hmemE]
    omega
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 (!as1.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1' hargs haszlt]
    exact hcall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', _, _, _, _, _, _, _, hout', hstk'⟩ :=
    call_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1' hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  refine ⟨s'', ?_, hstepV, hacc', hmemrel', ?_, hrd', hout'⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · intro i hi
    rw [hframe' i hi, hmemE]

/-- **CALL plan reduction** (all-live 7 distinct var operands): emit the operands (already
    positioned — `reorderPlan_allVars_nil`), `CALL` pops them and pushes the success flag bound
    to `out` — intermediate stack `base ++ [Var out]`. The named-1-output N-ary analogue of
    `genRegularInstPlan_log_eq`. -/
theorem genRegularInstPlan_call_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {ovars : List String} {dists : List Nat} {out : String} {base : List Operand}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "CALL"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ ovars.map Operand.Var := by
    rw [← h2, hpvar, hstack0]
  have hreorder := reorderPlan_allVars_nil base ovars ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop ovars.length (base ++ ovars.map Operand.Var) = base := by
    have h := stackPop_append_top base (ovars.map Operand.Var)
    rwa [List.length_map] at h
  simp [generateEmitOps_evmName hname, hreorder, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- Closed form of the var-pair input plan: two `DUP`s, leaving the operands `[Var y, Var x]`
    DUP'd onto the original stack. Because `stackDup d s = s ++ [stackPeek d s]` and the depth
    hypotheses pin the peeked operands (via `stackGetDepth_peek`), the resulting stack is
    `ps.stack ++ [Var y, Var x]` — the var counterpart of `emitInputPlan_pair_lit_eq` (which
    appends the two pushed literals). The plan-equation companion to `emitInputPlan_pair_var_sim`. -/
theorem emitInputPlan_pair_var_eq {opc nl x y ps d_y d_x'}
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) :
    emitInputPlan opc [Operand.Var y, Operand.Var x] nl ps
      = ([StackOp.SODup (d_y + 1), StackOp.SODup (d_x' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var y, Operand.Var x] }) := by
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_y]
  have hdx : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Var y]) = some d_x' := hdupY ▸ hdepth_x'
  have h := emitInputPlan_allVars_eq opc nl [y, x] [d_y, d_x'] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl; exacts [hnospill_y, hnospill_x])
    ⟨hlivey, hdepth_y, hsmall_y, hlivex, hdx, hsmall_x', trivial⟩
  simpa using h

/-- Closed form of the single-var input plan: one `DUP`, leaving `Var x` DUP'd onto the stack
    (`ps.stack ++ [Var x]`). The single-operand counterpart of `emitInputPlan_pair_var_eq`. -/
theorem emitInputPlan_single_var_eq {opc nl x ps dist}
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x) :
    emitInputPlan opc [Operand.Var x] nl ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := ps.stack ++ [Operand.Var x] }) := by
  have h := emitInputPlan_allVars_eq opc nl [x] [dist] ps
    (by intro v hv; simp only [List.mem_singleton] at hv; subst hv; exact hnospill)
    ⟨hlivex, hdepth, hsmall, trivial⟩
  simpa using h

/-- Closed form of the triple-var input plan: three `DUP`s, leaving `[Var z, Var y, Var x]` DUP'd
    onto the original stack (`ps.stack ++ [Var z, Var y, Var x]`). The 3-operand counterpart of
    `emitInputPlan_pair_var_eq` (each operand's depth is in the post-previous-DUP stack). Foundation
    for the 3-operand opcode class (ADDMOD/MULMOD). -/
theorem emitInputPlan_triple_var_eq {opc nl x y z ps d_z d_y' d_x''}
    (hnospill_z : alookup' ps.spilled (Operand.Var z) = none)
    (hlivez : nl.contains z = true)
    (hdepth_z : stackGetDepth (Operand.Var z) ps.stack = some d_z)
    (hsmall_z : d_z ≤ 15)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nl.contains y = true)
    (hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some d_y')
    (hsmall_y : d_y' ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nl.contains x = true)
    (hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'')
    (hsmall_x : d_x'' ≤ 15) :
    emitInputPlan opc [Operand.Var z, Operand.Var y, Operand.Var x] nl ps
      = ([StackOp.SODup (d_z + 1), StackOp.SODup (d_y' + 1), StackOp.SODup (d_x'' + 1)],
         { ps with stack := ps.stack ++ [Operand.Var z, Operand.Var y, Operand.Var x] }) := by
  have hdupZ : stackDup d_z ps.stack = ps.stack ++ [Operand.Var z] := by
    unfold stackDup; rw [stackGetDepth_peek hdepth_z]
  have hdy : stackGetDepth (Operand.Var y) (ps.stack ++ [Operand.Var z]) = some d_y' := hdupZ ▸ hdepth_y'
  have hdupY : stackDup d_y' (ps.stack ++ [Operand.Var z]) = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var y] := by
    unfold stackDup; rw [stackGetDepth_peek hdy]
  have hdx : stackGetDepth (Operand.Var x) ((ps.stack ++ [Operand.Var z]) ++ [Operand.Var y]) = some d_x'' := by
    rw [← hdupY, ← hdupZ]; exact hdepth_x''
  have h := emitInputPlan_allVars_eq opc nl [z, y, x] [d_z, d_y', d_x''] ps
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl; exacts [hnospill_z, hnospill_y, hnospill_x])
    ⟨hlivez, hdepth_z, hsmall_z, hlivey, hdy, hsmall_y, hlivex, hdx, hsmall_x, trivial⟩
  simpa using h

/-- The Venom step of a binop with two *variable* operands is `updateVar out (f wx wy)`. Bridges
    `stepInstBase` (the block semantics) to the `updateVar` form the per-instruction asm sims
    conclude on — `hdispatch` ties the opcode to its pure binary op (`execPure2 f`), proved per
    opcode by unfolding `stepInstBase`. Feeds the body-fold `gvBodyStep` (`instIdx`-invisible), so a
    per-instruction var-binop sim and this bridge together satisfy `genBlockBody_sim`'s `hstep`. -/
theorem stepInstBase_binopVar {inst : Instruction} {v : VenomState} {x y out : String}
    {wx wy : bytes32} {f : bytes32 → bytes32 → bytes32}
    (hdispatch : stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hvx : lookupVar x v = some wx)
    (hvy : lookupVar y v = some wy) :
    stepInstBase inst v = ExecResult.OK (updateVar out (f wx wy) v) := by
  rw [hdispatch]
  unfold execPure2
  rw [hops, houts]
  simp only [evalOperand, hvx, hvy]

/-- `operandVal` agrees with `evalOperand` on a variable operand (both are `lookupVar`); the label
    offsets `lo` are irrelevant for vars. Lets the asm-side operand value (`operandVal`, from
    `venomAsmRel`) feed the Venom-side step (`evalOperand`/`lookupVar`, in `stepInstBase`). -/
theorem operandVal_var_eq_lookupVar (vs : VenomState) (lo : AssocList String Nat) (x : String) :
    operandVal vs lo (Operand.Var x) = lookupVar x vs := rfl


/-- `callWriteback` changes only `out`'s binding among the operand-visible state. -/
theorem callWriteback_operandVal_ne {lo : AssocList String Nat} {out : String}
    {rOff rSz : Nat} {success : bytes32} {newAccs : Accounts} {ret : List byte}
    {vs : VenomState} {op : Operand} (h : op ≠ Operand.Var out) :
    operandVal (callWriteback out rOff rSz success newAccs ret vs) lo op
      = operandVal vs lo op := by
  simp only [callWriteback]
  rw [operandVal_updateVar_ne _ _ _ _ _ h]
  cases op with
  | Var w => rfl
  | Lit w => rfl
  | Label l => rfl

/-- `planStackRel` is stable under a Venom-state change that preserves every stack operand's
    value. -/
theorem planStackRel_env_congr {lo : AssocList String Nat} {vs vs' : VenomState}
    {psStack : List Operand} {asmStack : List bytes32}
    (hcongr : ∀ o ∈ psStack, operandVal vs' lo o = operandVal vs lo o)
    (h : planStackRel lo vs psStack asmStack) :
    planStackRel lo vs' psStack asmStack := by
  refine ⟨h.1, fun i hi => ?_⟩
  have hi' : i < psStack.reverse.length := by rw [List.length_reverse]; exact hi
  have hb : psStack.reverse[i]! = psStack.reverse[i] := getElem!_pos psStack.reverse i hi'
  rw [hb, hcongr _ (List.mem_reverse.mp (List.getElem_mem hi'))]
  rw [← hb]
  exact h.2 i hi

/-- `planSpillRel` is stable under a value-preserving env change plus a per-slot memory frame. -/
theorem planSpillRel_frame_congr {lo : AssocList String Nat} {vs vs' : VenomState}
    {spl : SpilledMap} {m m' : ByteArray}
    (h : planSpillRel lo vs spl m)
    (hcongr : ∀ op off, AssocList.lookup Operand Nat spl op = some off →
        operandVal vs' lo op = operandVal vs lo op)
    (hframe : ∀ op off, AssocList.lookup Operand Nat spl op = some off →
        m'.readWithPadding off 32 = m.readWithPadding off 32) :
    planSpillRel lo vs' spl m' := by
  intro op off hlook
  obtain ⟨v, hov, hword⟩ := h op off hlook
  exact ⟨v, by rw [hcongr op off hlook]; exact hov,
    by rw [hframe op off hlook]; exact hword⟩

set_option maxHeartbeats 800000 in
/-- **Full-relation CALL block core**: emit the 7 live operands and run CALL under the honest
    `memoryRel` memory conjunct — concluding the COMPLETE `venomAsmRel` at the popped-and-pushed
    plan state and the writeback Venom state. `planStackRel` rebuilds by pop-7/push-out over the
    `callWriteback`-stable operand values; `planSpillRel` rebuilds from the spill-slot byte frame
    (the returndata window lies below the spill region). The producer-grade replacement for
    `call_block_emit_sim`. -/
theorem call_block_emit_rel_full {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.CALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
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
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "CALL"])).length := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.CALL nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.CALL nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have hps'spill : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.spilled
      = ps.spilled := by rw [hemiteq]
  have hps'alloc : (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 7 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 7 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  rw [hps'alloc] at hmemrel1
  have hro2 : rOff.toNat ≤ as1.memory.size := by
    rw [hmemE]
    omega
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 (!as1.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1 hargs haszlt]
    exact hcall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    call_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1 hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  -- pc: the CALL writeback advances by one
  have hpcadv : s''.pc = as1.pc + 1 := by
    have hcalleq : asmCall as1 = AsmResult.AsmOK s'' := hasmOK
    unfold asmCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_call_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CALL"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  -- operand values are callWriteback-stable away from `out`
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · intro hc; rw [hc] at h; exact hfreshS h
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      exact houtov (hwe' ▸ hw)
  -- planStackRel: env-congr, pop 7, push out
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 7 ≤ (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    rw [List.length_map] at this
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 7 (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top ps.stack (ovars.map Operand.Var)
  rw [hpop7] at hStkFinal
  have hdrop7 : as1.stack.drop 7 = as1.stack.drop 7 := rfl
  -- planSpillRel: env-congr + per-slot byte frame
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.spilled s''.memory := by
    rw [hps'spill]
    rw [hps'spill] at hSpill1
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc, hspill_out] at hlook
      simp at hlook
    · intro op off hlook
      have hge : ps.alloc.fnEom ≤ off := hspillReg op off hlook
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off 32 h32
      intro k hk
      have := hframe' (off + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var out]) s''.stack
      rw [hstk']
      show planStackRel lo cb (ps.stack ++ [Operand.Var out]) (success :: as1.stack.drop 7)
      have hpush : stackPush (Operand.Var out) ps.stack = ps.stack ++ [Operand.Var out] := rfl
      rw [← hpush]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.CALL (ovars.map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      rw [hps'alloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv, hpcE]
    rfl

/-- **The full generated-plan CALL producer sim** — the deep item closed: running the ENTIRE
    `generateRegularInstPlan` output for a CALL (7 live operands, positioned; the sub-EVM runs on
    calldata below the spill region; the writeback lands below it too) preserves the complete
    `venomAsmRel` against the Venom `stepExternalCall` writeback. Composes the plan reduction
    (`genRegularInstPlan_call_eq`), the full-relation core (`call_block_emit_rel_full`), and
    `releaseDeadSpills_sim`. -/
theorem genRegularInstPlan_call_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {dists : List Nat} {out : String}
    {base : List Operand} {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
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
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  rw [genRegularInstPlan_call_eq hopc hcompute houts hstack0 hnd hnospill hdepths hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    call_block_emit_rel_full (offsetToPc := offsetToPc) hopc heval houts hnospill hdepths hvals
      hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov hspill_out hspillReg hcall
      hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩
/-- **STATICCALL correspondence core: both interpreters run the identical sub-EVM** — the
    6-operand, zero-value, non-permissioned sibling of `asmCall_stepExternalCall_same_evmCall_rel`. -/
theorem asmStaticCall_stepExternalCall_same_evmCall_rel {alloc : SpillAlloc}
    {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {gas addr aOff aSz rOff rSz : bytes32} {stk : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.STATICCALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : s.stack = gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = s.accounts)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcall : evmCall subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩
      (s.memory.readWithPadding aOff.toNat aSz.toNat).toList s.txCtx.gasprice 0 false
      = (success, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmStaticCall s = asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s := by
  have hcd : vs.memory.readWithPadding aOff.toNat aSz.toNat
      = s.memory.readWithPadding aOff.toNat aSz.toNat :=
    memoryRel_readWithPadding_slice hmem hargs haszlt
  have hcallV : evmCall subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩
      (readMemory aOff.toNat aSz.toNat vs).toList vs.txCtx.gasprice 0 false
      = (success, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hcd]; exact hcall
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcallV]
  · unfold asmStaticCall; rw [hstk]; simp only [hcall]

/-- **STATICCALL step, full `memoryRel` correspondence** — the 6-operand mirror of
    `call_step_stateAgree_rel`: same shared `callWriteback`/`asmCallWriteback` agree core, the
    sub-EVM runs with zero value and `perm = false`. -/
theorem staticcall_step_stateAgree_rel {alloc : SpillAlloc} {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {gas addr aOff aSz rOff rSz : bytes32}
    {stk : List bytes32} {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.STATICCALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : as.stack = gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = as.accounts)
    (hmem : memoryRel alloc vs.memory as.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size) (hro2 : rOff.toNat ≤ as.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ alloc.fnEom)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcall : evmCall subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩
      (as.memory.readWithPadding aOff.toNat aSz.toNat).toList as.txCtx.gasprice 0 false
      = (success, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmStaticCall as = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ memoryRel alloc (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).transient = s''.transient
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).logs = s''.logs
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).callCtx = s''.callCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).txCtx = s''.txCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).blockCtx = s''.blockCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).code = s''.code
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).prevHashes = s''.prevHashes
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmStaticCall_stepExternalCall_same_evmCall_rel hopc heval hout hstk hacc hmem hargs haszlt
      hcc htx hcall
  obtain ⟨s'', hs''eq, hacc', hmem', hframe', hrd', hout', hstk'⟩ :=
    callWriteback_asmCallWriteback_agree_rel alloc out rOff.toNat rSz.toNat success newAccs ret
      stk vs as hmem hro1 hro2 hretbelow
  have hconcrete := hs''eq
  simp only [asmCallWriteback] at hconcrete
  injection hconcrete with hc
  refine ⟨s'', hstep, by rw [hasmeq]; exact hs''eq, hacc', hmem', hframe', hrd',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout', hstk'⟩
  · show (callWriteback _ _ _ _ _ _ _).transient = s''.transient
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htr
  · show (callWriteback _ _ _ _ _ _ _).logs = s''.logs
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hlg
  · show (callWriteback _ _ _ _ _ _ _).callCtx = s''.callCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcc
  · show (callWriteback _ _ _ _ _ _ _).txCtx = s''.txCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htx
  · show (callWriteback _ _ _ _ _ _ _).blockCtx = s''.blockCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hbc
  · show (callWriteback _ _ _ _ _ _ _).code = s''.code
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcode
  · show (callWriteback _ _ _ _ _ _ _).prevHashes = s''.prevHashes
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hph

/-- **Full-relation STATICCALL block core** — the 6-operand mirror of `call_block_emit_rel_full`:
    emit the operands and run STATICCALL, concluding the COMPLETE `venomAsmRel` at net +1 and the
    writeback state. -/
theorem staticcall_block_emit_rel_full {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.STATICCALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
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
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "STATICCALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "STATICCALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "STATICCALL"])).length := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.STATICCALL nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.STATICCALL nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have hps'spill : (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.spilled
      = ps.spilled := by rw [hemiteq]
  have hps'alloc : (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 6 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 6 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  rw [hps'alloc] at hmemrel1
  have hro2 : rOff.toNat ≤ as1.memory.size := by
    rw [hmemE]
    omega
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas ⟨0⟩ ⟨0⟩
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 false
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1 hargs haszlt]
    exact hcall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    staticcall_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1 hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  -- pc: the CALL writeback advances by one
  have hpcadv : s''.pc = as1.pc + 1 := by
    have hcalleq : asmStaticCall as1 = AsmResult.AsmOK s'' := hasmOK
    unfold asmStaticCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_staticcall_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "STATICCALL"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  -- operand values are callWriteback-stable away from `out`
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · intro hc; rw [hc] at h; exact hfreshS h
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      exact houtov (hwe' ▸ hw)
  -- planStackRel: env-congr, pop 7, push out
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 6 ≤ (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    rw [List.length_map] at this
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 6 (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top ps.stack (ovars.map Operand.Var)
  rw [hpop7] at hStkFinal
  have hdrop7 : as1.stack.drop 6 = as1.stack.drop 6 := rfl
  -- planSpillRel: env-congr + per-slot byte frame
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.spilled s''.memory := by
    rw [hps'spill]
    rw [hps'spill] at hSpill1
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc, hspill_out] at hlook
      simp at hlook
    · intro op off hlook
      have hge : ps.alloc.fnEom ≤ off := hspillReg op off hlook
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off 32 h32
      intro k hk
      have := hframe' (off + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var out]) s''.stack
      rw [hstk']
      show planStackRel lo cb (ps.stack ++ [Operand.Var out]) (success :: as1.stack.drop 6)
      have hpush : stackPush (Operand.Var out) ps.stack = ps.stack ++ [Operand.Var out] := rfl
      rw [← hpush]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.STATICCALL (ovars.map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      rw [hps'alloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv, hpcE]
    rfl

/-- **STATICCALL plan reduction** (all-live 6 distinct var operands): the 6-operand mirror of
    `genRegularInstPlan_call_eq`. -/
theorem genRegularInstPlan_staticcall_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {ovars : List String} {dists : List Nat} {out : String} {base : List Operand}
    (hopc : inst.opcode = Opcode.STATICCALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "STATICCALL"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "STATICCALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ ovars.map Operand.Var := by
    rw [← h2, hpvar, hstack0]
  have hreorder := reorderPlan_allVars_nil base ovars ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop ovars.length (base ++ ovars.map Operand.Var) = base := by
    have h := stackPop_append_top base (ovars.map Operand.Var)
    rwa [List.length_map] at h
  simp [generateEmitOps_evmName hname, hreorder, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **The full generated-plan STATICCALL producer sim** — running the ENTIRE
    `generateRegularInstPlan` output for a STATICCALL (6 live operands, positioned) preserves the
    complete `venomAsmRel` against the Venom `stepExternalCall` writeback. The first non-CALL
    external-call producer, mirrored off the CALL chain. -/
theorem genRegularInstPlan_staticcall_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {dists : List Nat} {out : String}
    {base : List Operand} {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.STATICCALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
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
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  rw [genRegularInstPlan_staticcall_eq hopc hcompute houts hstack0 hnd hnospill hdepths hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    staticcall_block_emit_rel_full (offsetToPc := offsetToPc) hopc heval houts hnospill hdepths hvals
      hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov hspill_out hspillReg hcall
      hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-- **DELEGATECALL correspondence core: both interpreters run the identical sub-EVM** — the
    6-operand caller-context sibling (recipient = self, code = addr, apparent value = own callvalue) of `asmCall_stepExternalCall_same_evmCall_rel`. -/
theorem asmDelegateCall_stepExternalCall_same_evmCall_rel {alloc : SpillAlloc}
    {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {gas addr aOff aSz rOff rSz : bytes32} {stk : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : s.stack = gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = s.accounts)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcall : evmCall subEvmFuel s.accounts s.callCtx.caller s.txCtx.origin
      s.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ s.callCtx.callvalue
      (s.memory.readWithPadding aOff.toNat aSz.toNat).toList s.txCtx.gasprice 0 (!s.callCtx.static)
      = (success, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmDelegateCall s = asmCallWriteback rOff.toNat rSz.toNat success newAccs ret stk s := by
  have hcd : vs.memory.readWithPadding aOff.toNat aSz.toNat
      = s.memory.readWithPadding aOff.toNat aSz.toNat :=
    memoryRel_readWithPadding_slice hmem hargs haszlt
  have hcallV : evmCall subEvmFuel vs.accounts vs.callCtx.caller vs.txCtx.origin
      vs.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ vs.callCtx.callvalue
      (readMemory aOff.toNat aSz.toNat vs).toList vs.txCtx.gasprice 0 (!vs.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hcd]; exact hcall
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcallV]
  · unfold asmDelegateCall; rw [hstk]; simp only [hcall]

/-- **DELEGATECALL step, full `memoryRel` correspondence** — the 6-operand mirror of
    `call_step_stateAgree_rel`: same shared `callWriteback`/`asmCallWriteback` agree core, the
    sub-EVM runs `addr`'s code in the caller's own context. -/
theorem delegatecall_step_stateAgree_rel {alloc : SpillAlloc} {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {gas addr aOff aSz rOff rSz : bytes32}
    {stk : List bytes32} {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hstk : as.stack = gas :: addr :: aOff :: aSz :: rOff :: rSz :: stk)
    (hacc : vs.accounts = as.accounts)
    (hmem : memoryRel alloc vs.memory as.memory)
    (hargs : aOff.toNat + aSz.toNat ≤ alloc.fnEom) (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ vs.memory.size) (hro2 : rOff.toNat ≤ as.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ alloc.fnEom)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcall : evmCall subEvmFuel as.accounts as.callCtx.caller as.txCtx.origin
      as.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ as.callCtx.callvalue
      (as.memory.readWithPadding aOff.toNat aSz.toNat).toList as.txCtx.gasprice 0 (!as.callCtx.static)
      = (success, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ asmDelegateCall as = AsmResult.AsmOK s''
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).accounts = s''.accounts
      ∧ memoryRel alloc (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).returndata = s''.returndata
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).transient = s''.transient
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).logs = s''.logs
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).callCtx = s''.callCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).txCtx = s''.txCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).blockCtx = s''.blockCtx
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).code = s''.code
      ∧ (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs).prevHashes = s''.prevHashes
      ∧ lookupVar out (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) = some success
      ∧ s''.stack = success :: stk := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmDelegateCall_stepExternalCall_same_evmCall_rel hopc heval hout hstk hacc hmem hargs haszlt
      hcc htx hcall
  obtain ⟨s'', hs''eq, hacc', hmem', hframe', hrd', hout', hstk'⟩ :=
    callWriteback_asmCallWriteback_agree_rel alloc out rOff.toNat rSz.toNat success newAccs ret
      stk vs as hmem hro1 hro2 hretbelow
  have hconcrete := hs''eq
  simp only [asmCallWriteback] at hconcrete
  injection hconcrete with hc
  refine ⟨s'', hstep, by rw [hasmeq]; exact hs''eq, hacc', hmem', hframe', hrd',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout', hstk'⟩
  · show (callWriteback _ _ _ _ _ _ _).transient = s''.transient
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htr
  · show (callWriteback _ _ _ _ _ _ _).logs = s''.logs
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hlg
  · show (callWriteback _ _ _ _ _ _ _).callCtx = s''.callCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcc
  · show (callWriteback _ _ _ _ _ _ _).txCtx = s''.txCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact htx
  · show (callWriteback _ _ _ _ _ _ _).blockCtx = s''.blockCtx
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hbc
  · show (callWriteback _ _ _ _ _ _ _).code = s''.code
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hcode
  · show (callWriteback _ _ _ _ _ _ _).prevHashes = s''.prevHashes
    rw [← hc]; simp only [callWriteback, updateVar, writeMemoryWithExpansion, asmNext]; exact hph

/-- **Full-relation DELEGATECALL block core** — the 6-operand mirror of `call_block_emit_rel_full`:
    emit the operands and run DELEGATECALL, concluding the COMPLETE `venomAsmRel` at net +1 and the
    writeback state. -/
theorem delegatecall_block_emit_rel_full {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (heval : evalOperands inst.operands vs = some [gas, addr, aOff, aSz, rOff, rSz])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
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
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "DELEGATECALL"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "DELEGATECALL"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs)
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var out] }
          (callWriteback out rOff.toNat rSz.toNat success newAccs ret vs) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "DELEGATECALL"])).length := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.DELEGATECALL nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.DELEGATECALL nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have hps'spill : (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.spilled
      = ps.spilled := by rw [hemiteq]
  have hps'alloc : (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 6 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 6 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  rw [hps'alloc] at hmemrel1
  have hro2 : rOff.toNat ≤ as1.memory.size := by
    rw [hmemE]
    omega
  have hcall1 : evmCall subEvmFuel as1.accounts as1.callCtx.caller as1.txCtx.origin
      as1.callCtx.contract (AccountAddress.ofUInt256 addr) gas ⟨0⟩ as1.callCtx.callvalue
      (as1.memory.readWithPadding aOff.toNat aSz.toNat).toList as1.txCtx.gasprice 0 (!as1.callCtx.static)
      = (success, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1 hargs haszlt]
    exact hcall
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk'⟩ :=
    delegatecall_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1 hargs haszlt hro1 hro2 hretbelow hcc1.symm htx1.symm htr1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcall1
  -- pc: the CALL writeback advances by one
  have hpcadv : s''.pc = as1.pc + 1 := by
    have hcalleq : asmDelegateCall as1 = AsmResult.AsmOK s'' := hasmOK
    unfold asmDelegateCall at hcalleq
    rw [htop] at hcalleq
    simp only [asmCallWriteback] at hcalleq
    injection hcalleq with hc
    rw [← hc]; rfl
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_delegatecall_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "DELEGATECALL"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := callWriteback out rOff.toNat rSz.toNat success newAccs ret vs with hcbdef
  -- operand values are callWriteback-stable away from `out`
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine callWriteback_operandVal_ne ?_
    rcases List.mem_append.mp ho with h | h
    · intro hc; rw [hc] at h; exact hfreshS h
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      exact houtov (hwe' ▸ hw)
  -- planStackRel: env-congr, pop 7, push out
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen7 : 6 ≤ (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    rw [List.length_map] at this
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some success := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen7) houtval
  have hpop7 : stackPop 6 (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top ps.stack (ovars.map Operand.Var)
  rw [hpop7] at hStkFinal
  have hdrop7 : as1.stack.drop 6 = as1.stack.drop 6 := rfl
  -- planSpillRel: env-congr + per-slot byte frame
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.spilled s''.memory := by
    rw [hps'spill]
    rw [hps'spill] at hSpill1
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off hlook
      refine callWriteback_operandVal_ne ?_
      intro hc
      rw [hc, hspill_out] at hlook
      simp at hlook
    · intro op off hlook
      have hge : ps.alloc.fnEom ≤ off := hspillReg op off hlook
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off 32 h32
      intro k hk
      have := hframe' (off + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var out]) s''.stack
      rw [hstk']
      show planStackRel lo cb (ps.stack ++ [Operand.Var out]) (success :: as1.stack.drop 6)
      have hpush : stackPush (Operand.Var out) ps.stack = ps.stack ++ [Operand.Var out] := rfl
      rw [← hpush]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.DELEGATECALL (ovars.map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      rw [hps'alloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv, hpcE]
    rfl

/-- **DELEGATECALL plan reduction** (all-live 6 distinct var operands): the 6-operand mirror of
    `genRegularInstPlan_call_eq`. -/
theorem genRegularInstPlan_delegatecall_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {ovars : List String} {dists : List Nat} {out : String} {base : List Operand}
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "DELEGATECALL"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "DELEGATECALL" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ ovars.map Operand.Var := by
    rw [← h2, hpvar, hstack0]
  have hreorder := reorderPlan_allVars_nil base ovars ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop ovars.length (base ++ ovars.map Operand.Var) = base := by
    have h := stackPop_append_top base (ovars.map Operand.Var)
    rwa [List.length_map] at h
  simp [generateEmitOps_evmName hname, hreorder, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **The full generated-plan DELEGATECALL producer sim** — running the ENTIRE
    `generateRegularInstPlan` output for a DELEGATECALL (6 live operands, positioned) preserves the
    complete `venomAsmRel` against the Venom `stepExternalCall` writeback. Runs `addr`'s code in the
    caller's own context; mirrored off the STATICCALL chain. -/
theorem genRegularInstPlan_delegatecall_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {dists : List Nat} {out : String}
    {base : List Operand} {gas addr aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.DELEGATECALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
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
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  rw [genRegularInstPlan_delegatecall_eq hopc hcompute houts hstack0 hnd hnospill hdepths hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    delegatecall_block_emit_rel_full (offsetToPc := offsetToPc) hopc heval houts hnospill hdepths hvals
      hvalrev hargs haszlt hro1 hretbelow hfnEom hfreshS houtov hspill_out hspillReg hcall
      hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-- **CREATE correspondence core: both interpreters run the identical sub-EVM creation.** The
    init code is read below the spill region, so the `memoryRel` slice agreement makes both
    sides run the same `evmCreate`; the writebacks are variable-bind + accounts only (no memory
    write, no returndata). -/
theorem asmCreate_stepExternalCall_same_evmCreate_rel {alloc : SpillAlloc}
    {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {value off size : bytes32} {stk : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE)
    (heval : evalOperands inst.operands vs = some [value, off, size])
    (hout : inst.outputs = [out])
    (hstk : s.stack = value :: off :: size :: stk)
    (hacc : vs.accounts = s.accounts)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hargs : off.toNat + size.toNat ≤ alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcreate : evmCreate subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      value (s.memory.readWithPadding off.toNat size.toNat).toList s.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ asmCreate s
        = AsmResult.AsmOK { asmNext s with stack := addrOrZero :: stk, accounts := newAccs } := by
  have hcd : vs.memory.readWithPadding off.toNat size.toNat
      = s.memory.readWithPadding off.toNat size.toNat :=
    memoryRel_readWithPadding_slice hmem hargs hszlt
  have hcreateV : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (readMemory off.toNat size.toNat vs).toList vs.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hcd]; exact hcreate
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcreateV]
  · unfold asmCreate; rw [hstk]; simp only [hcreate]

/-- **CREATE step, full `memoryRel` correspondence.** Both writebacks leave memory untouched, so
    the relation and every asm byte carry over trivially; accounts update to the creation result
    and the new address (or zero) binds to `out` / pushes onto the stack. -/
theorem create_step_stateAgree_rel {alloc : SpillAlloc} {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {value off size : bytes32}
    {stk : List bytes32} {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE)
    (heval : evalOperands inst.operands vs = some [value, off, size])
    (hout : inst.outputs = [out])
    (hstk : as.stack = value :: off :: size :: stk)
    (hacc : vs.accounts = as.accounts)
    (hmem : memoryRel alloc vs.memory as.memory)
    (hargs : off.toNat + size.toNat ≤ alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hrd : vs.returndata = as.returndata)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcreate : evmCreate subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      value (as.memory.readWithPadding off.toNat size.toNat).toList as.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ asmCreate as = AsmResult.AsmOK s''
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).accounts = s''.accounts
      ∧ memoryRel alloc (updateVar out addrOrZero { vs with accounts := newAccs }).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).returndata = s''.returndata
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).transient = s''.transient
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).logs = s''.logs
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).callCtx = s''.callCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).txCtx = s''.txCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).blockCtx = s''.blockCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).code = s''.code
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).prevHashes = s''.prevHashes
      ∧ lookupVar out (updateVar out addrOrZero { vs with accounts := newAccs }) = some addrOrZero
      ∧ s''.stack = addrOrZero :: stk
      ∧ s''.pc = as.pc + 1 := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmCreate_stepExternalCall_same_evmCreate_rel hopc heval hout hstk hacc hmem hargs hszlt
      hcc htx hcreate
  refine ⟨{ asmNext as with stack := addrOrZero :: stk, accounts := newAccs },
    hstep, hasmeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    lookupVar_updateVar_self _ _ _, rfl, rfl⟩
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).accounts = newAccs
    simp only [updateVar]
  · show memoryRel alloc (updateVar out addrOrZero { vs with accounts := newAccs }).memory as.memory
    simp only [updateVar]
    exact hmem
  · intro i _
    rfl
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).returndata = as.returndata
    simp only [updateVar]
    exact hrd
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).transient = as.transient
    simp only [updateVar]
    exact htr
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).logs = as.logs
    simp only [updateVar]
    exact hlg
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).callCtx = as.callCtx
    simp only [updateVar]
    exact hcc
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).txCtx = as.txCtx
    simp only [updateVar]
    exact htx
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).blockCtx = as.blockCtx
    simp only [updateVar]
    exact hbc
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).code = as.code
    simp only [updateVar]
    exact hcode
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).prevHashes = as.prevHashes
    simp only [updateVar]
    exact hph

set_option maxHeartbeats 800000 in
/-- **Full-relation CREATE block core**: emit the 3 operands and run CREATE — concluding the
    COMPLETE `venomAsmRel` at net +1 (the created address binds to `out`) and the writeback
    state. Memories are untouched, so the memory/spill conjuncts carry over directly. -/
theorem create_block_emit_rel_full {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {value off size : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.CREATE)
    (heval : evalOperands inst.operands vs = some [value, off, size])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CREATE"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CREATE"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var out] }
          (updateVar out addrOrZero { vs with accounts := newAccs }) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "CREATE"])).length := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.CREATE nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.CREATE nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have hps'spill : (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.spilled
      = ps.spilled := by rw [hemiteq]
  have hps'alloc : (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 3 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 3 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  rw [hps'alloc] at hmemrel1
  have hcreate1 : evmCreate subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      value (as1.memory.readWithPadding off.toNat size.toNat).toList as1.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1 hargs hszlt]
    exact hcreate
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk', hpcadv0⟩ :=
    create_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1 hargs hszlt hcc1.symm htx1.symm htr1.symm hrd1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcreate1
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_create_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CREATE"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := updateVar out addrOrZero { vs with accounts := newAccs } with hcbdef
  have hstable : ∀ (o : Operand), o ≠ Operand.Var out → operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hcbdef, operandVal_updateVar_ne _ _ _ _ _ ho]
    cases o with
    | Var w => rfl
    | Lit w => rfl
    | Label l => rfl
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine hstable o ?_
    rcases List.mem_append.mp ho with h | h
    · intro hc; rw [hc] at h; exact hfreshS h
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      exact houtov (hwe' ▸ hw)
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen3 : 3 ≤ (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    rw [List.length_map] at this
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some addrOrZero := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen3) houtval
  have hpop3 : stackPop 3 (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top ps.stack (ovars.map Operand.Var)
  rw [hpop3] at hStkFinal
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.spilled s''.memory := by
    rw [hps'spill]
    rw [hps'spill] at hSpill1
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off' hlook
      refine hstable op ?_
      intro hc
      rw [hc, hspill_out] at hlook
      simp at hlook
    · intro op off' hlook
      have hge : ps.alloc.fnEom ≤ off' := hspillReg op off' hlook
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off' 32 h32
      intro k hk
      have := hframe' (off' + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var out]) s''.stack
      rw [hstk']
      show planStackRel lo cb (ps.stack ++ [Operand.Var out]) (addrOrZero :: as1.stack.drop 3)
      have hpush : stackPush (Operand.Var out) ps.stack = ps.stack ++ [Operand.Var out] := rfl
      rw [← hpush]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.CREATE (ovars.map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      rw [hps'alloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv0, hpcE]
    rfl

/-- **CREATE plan reduction** (all-live 3 distinct var operands): emit the operands (already
    positioned — `reorderPlan_allVars_nil`), `CREATE` pops them and pushes the new address bound
    to `out` — net `+1`. -/
theorem genRegularInstPlan_create_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {ovars : List String} {dists : List Nat} {out : String} {base : List Operand}
    (hopc : inst.opcode = Opcode.CREATE)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "CREATE"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CREATE" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ ovars.map Operand.Var := by
    rw [← h2, hpvar, hstack0]
  have hreorder := reorderPlan_allVars_nil base ovars ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop ovars.length (base ++ ovars.map Operand.Var) = base := by
    have h := stackPop_append_top base (ovars.map Operand.Var)
    rwa [List.length_map] at h
  simp [generateEmitOps_evmName hname, hreorder, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **The full generated-plan CREATE producer sim** — running the ENTIRE
    `generateRegularInstPlan` output for a CREATE (3 live operands, positioned; init code below
    the spill region) preserves the complete `venomAsmRel` against the Venom `stepExternalCall`
    writeback. The creation sibling of `genRegularInstPlan_call_sim`. -/
theorem genRegularInstPlan_create_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {dists : List Nat} {out : String}
    {base : List Operand} {value off size : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [value, off, size])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 none
      = (addrOrZero, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_create_eq hopc hcompute houts hstack0 hnd hnospill hdepths hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    create_block_emit_rel_full (offsetToPc := offsetToPc) hopc heval houts hnospill hdepths hvals
      hvalrev hargs hszlt hfreshS houtov hspill_out hspillReg hcreate hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-- **CREATE2 correspondence core: both interpreters run the identical sub-EVM creation.** The
    init code is read below the spill region, so the `memoryRel` slice agreement makes both
    sides run the same `evmCreate`; the writebacks are variable-bind + accounts only (no memory
    write, no returndata). -/
theorem asmCreate2_stepExternalCall_same_evmCreate_rel {alloc : SpillAlloc}
    {vs : VenomState} {s : AsmState} {inst : Instruction}
    {out : String} {value off size salt : bytes32} {stk : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE2)
    (heval : evalOperands inst.operands vs = some [value, off, size, salt])
    (hout : inst.outputs = [out])
    (hstk : s.stack = value :: off :: size :: salt :: stk)
    (hacc : vs.accounts = s.accounts)
    (hmem : memoryRel alloc vs.memory s.memory)
    (hargs : off.toNat + size.toNat ≤ alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hcc : vs.callCtx = s.callCtx) (htx : vs.txCtx = s.txCtx)
    (hcreate : evmCreate subEvmFuel s.accounts s.callCtx.contract s.txCtx.origin
      value (s.memory.readWithPadding off.toNat size.toNat).toList s.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret)) :
    stepExternalCall subEvmFuel inst vs
        = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ asmCreate2 s
        = AsmResult.AsmOK { asmNext s with stack := addrOrZero :: stk, accounts := newAccs } := by
  have hcd : vs.memory.readWithPadding off.toNat size.toNat
      = s.memory.readWithPadding off.toNat size.toNat :=
    memoryRel_readWithPadding_slice hmem hargs hszlt
  have hcreateV : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (readMemory off.toNat size.toNat vs).toList vs.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret) := by
    rw [hacc, hcc, htx, readMemory, hcd]; exact hcreate
  refine ⟨?_, ?_⟩
  · unfold stepExternalCall; rw [heval]; simp only [bind, Option.bind, hopc, hout, hcreateV]
  · unfold asmCreate2; rw [hstk]; simp only [hcreate]

/-- **CREATE2 step, full `memoryRel` correspondence.** Both writebacks leave memory untouched, so
    the relation and every asm byte carry over trivially; accounts update to the creation result
    and the new address (or zero) binds to `out` / pushes onto the stack. -/
theorem create2_step_stateAgree_rel {alloc : SpillAlloc} {vs : VenomState} {as : AsmState}
    {inst : Instruction} {out : String} {value off size salt : bytes32}
    {stk : List bytes32} {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE2)
    (heval : evalOperands inst.operands vs = some [value, off, size, salt])
    (hout : inst.outputs = [out])
    (hstk : as.stack = value :: off :: size :: salt :: stk)
    (hacc : vs.accounts = as.accounts)
    (hmem : memoryRel alloc vs.memory as.memory)
    (hargs : off.toNat + size.toNat ≤ alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hcc : vs.callCtx = as.callCtx) (htx : vs.txCtx = as.txCtx)
    (htr : vs.transient = as.transient)
    (hrd : vs.returndata = as.returndata)
    (hlg : vs.logs = as.logs) (hbc : vs.blockCtx = as.blockCtx)
    (hcode : vs.code = as.code) (hph : vs.prevHashes = as.prevHashes)
    (hcreate : evmCreate subEvmFuel as.accounts as.callCtx.contract as.txCtx.origin
      value (as.memory.readWithPadding off.toNat size.toNat).toList as.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret)) :
    ∃ s'',
      stepExternalCall subEvmFuel inst vs
        = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ asmCreate2 as = AsmResult.AsmOK s''
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).accounts = s''.accounts
      ∧ memoryRel alloc (updateVar out addrOrZero { vs with accounts := newAccs }).memory s''.memory
      ∧ (∀ i, alloc.fnEom ≤ i → readByte i s''.memory = readByte i as.memory)
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).returndata = s''.returndata
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).transient = s''.transient
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).logs = s''.logs
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).callCtx = s''.callCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).txCtx = s''.txCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).blockCtx = s''.blockCtx
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).code = s''.code
      ∧ (updateVar out addrOrZero { vs with accounts := newAccs }).prevHashes = s''.prevHashes
      ∧ lookupVar out (updateVar out addrOrZero { vs with accounts := newAccs }) = some addrOrZero
      ∧ s''.stack = addrOrZero :: stk
      ∧ s''.pc = as.pc + 1 := by
  obtain ⟨hstep, hasmeq⟩ :=
    asmCreate2_stepExternalCall_same_evmCreate_rel hopc heval hout hstk hacc hmem hargs hszlt
      hcc htx hcreate
  refine ⟨{ asmNext as with stack := addrOrZero :: stk, accounts := newAccs },
    hstep, hasmeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    lookupVar_updateVar_self _ _ _, rfl, rfl⟩
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).accounts = newAccs
    simp only [updateVar]
  · show memoryRel alloc (updateVar out addrOrZero { vs with accounts := newAccs }).memory as.memory
    simp only [updateVar]
    exact hmem
  · intro i _
    rfl
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).returndata = as.returndata
    simp only [updateVar]
    exact hrd
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).transient = as.transient
    simp only [updateVar]
    exact htr
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).logs = as.logs
    simp only [updateVar]
    exact hlg
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).callCtx = as.callCtx
    simp only [updateVar]
    exact hcc
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).txCtx = as.txCtx
    simp only [updateVar]
    exact htx
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).blockCtx = as.blockCtx
    simp only [updateVar]
    exact hbc
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).code = as.code
    simp only [updateVar]
    exact hcode
  · show (updateVar out addrOrZero { vs with accounts := newAccs }).prevHashes = as.prevHashes
    simp only [updateVar]
    exact hph

set_option maxHeartbeats 800000 in
/-- **Full-relation CREATE2 block core**: emit the 4 operands and run CREATE2 — concluding the
    COMPLETE `venomAsmRel` at net +1 (the created address binds to `out`) and the writeback
    state. Memories are untouched, so the memory/spill conjuncts carry over directly. -/
theorem create2_block_emit_rel_full {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {inst : Instruction}
    {out : String} {ovars : List String} {dists : List Nat} {nl : List String}
    {value off size salt : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte} {ps : PlanState}
    (hopc : inst.opcode = Opcode.CREATE2)
    (heval : evalOperands inst.operands vs = some [value, off, size, salt])
    (hout : inst.outputs = [out])
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nl ovars dists ps.stack)
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size, salt])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan ((emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).1 ++ [StackOp.SOEmit "CREATE2"]))) :
    ∃ s'', runAsm (executePlan ((emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).1
             ++ [StackOp.SOEmit "CREATE2"])).length offsetToPc prog as = AsmResult.AsmOK s''
      ∧ stepExternalCall subEvmFuel inst vs
          = some (updateVar out addrOrZero { vs with accounts := newAccs })
      ∧ venomAsmRel lo
          { (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2 with
            stack := ps.stack ++ [Operand.Var out] }
          (updateVar out addrOrZero { vs with accounts := newAccs }) s''
      ∧ s''.pc = as.pc + (executePlan ((emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).1
          ++ [StackOp.SOEmit "CREATE2"])).length := by
  have hemiteq := emitInputPlan_allVars_eq Opcode.CREATE2 nl ovars dists ps hnospill hdepths
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbCall⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunE, hrelE, hpcE, hmemE⟩ :=
    emitInputPlan_allVars_sim (offsetToPc := offsetToPc) Opcode.CREATE2 nl ovars dists ps hnospill hdepths hrel hbI
  have hps'stack : (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack ++ ovars.map Operand.Var := by rw [hemiteq]
  have hps'spill : (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.spilled
      = ps.spilled := by rw [hemiteq]
  have hps'alloc : (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.alloc = ps.alloc := by
    rw [hemiteq]
  have htop := venomAsmRel_asmStack_topOps (base := ps.stack) (ops := ovars.map Operand.Var) (vals := vals)
    hrelE hps'stack hvals
  rw [hvalrev] at htop
  have hlenops : (ovars.map Operand.Var).length = 4 := by
    rw [List.length_map]
    have h1 : ovars.length = vals.length := by
      have := congrArg List.length hvals; simpa [List.length_map] using this
    have h2 : vals.length = 4 := by
      have := congrArg List.length hvalrev; simpa using this
    omega
  rw [hlenops] at htop
  obtain ⟨hStk1, hSpill1, hmemrel1, hacc1, htr1, hrd1, hlg1, hcc1, htx1, hbc1, hcode1, hph1⟩ := hrelE
  rw [hps'alloc] at hmemrel1
  have hcreate1 : evmCreate subEvmFuel as1.accounts as1.callCtx.contract as1.txCtx.origin
      value (as1.memory.readWithPadding off.toNat size.toNat).toList as1.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret) := by
    rw [hacc1, hcc1, htx1,
        ← memoryRel_readWithPadding_slice hmemrel1 hargs hszlt]
    exact hcreate
  obtain ⟨hpcC, hgetC⟩ := asmBlockAt_one (by rw [← hpcE] at hbCall; exact hbCall)
  obtain ⟨s'', hstepV, hasmOK, hacc', hmemrel', hframe', hrd', htr', hlg', hcc', htx', hbc',
    hcode', hph', hout', hstk', hpcadv0⟩ :=
    create2_step_stateAgree_rel (alloc := ps.alloc) (as := as1) hopc heval hout htop
      hacc1.symm hmemrel1 hargs hszlt hcc1.symm htx1.symm htr1.symm hrd1.symm
      hlg1.symm hbc1.symm hcode1.symm hph1.symm hcreate1
  have hstepeq : asmStep offsetToPc prog as1 = AsmResult.AsmOK s'' := by
    rw [asmStep_create2_ok hpcC hgetC]; exact hasmOK
  have hrunC : runAsm (executePlan [StackOp.SOEmit "CREATE2"]).length offsetToPc prog as1
      = AsmResult.AsmOK s'' := by
    show runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK s''
    rw [runAsm_succ_ok hpcC hstepeq]; rfl
  set cb := updateVar out addrOrZero { vs with accounts := newAccs } with hcbdef
  have hstable : ∀ (o : Operand), o ≠ Operand.Var out → operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hcbdef, operandVal_updateVar_ne _ _ _ _ _ ho]
    cases o with
    | Var w => rfl
    | Lit w => rfl
    | Label l => rfl
  have hcongrStack : ∀ o ∈ (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.stack,
      operandVal cb lo o = operandVal vs lo o := by
    intro o ho
    rw [hps'stack] at ho
    refine hstable o ?_
    rcases List.mem_append.mp ho with h | h
    · intro hc; rw [hc] at h; exact hfreshS h
    · intro hc
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hc] at hwe
      injection hwe with hwe'
      exact houtov (hwe' ▸ hw)
  have hStkCb : planStackRel lo cb
      (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.stack as1.stack :=
    planStackRel_env_congr hcongrStack hStk1
  have hlen4 : 4 ≤ (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.stack.length := by
    rw [hps'stack, List.length_append]
    have := hlenops
    rw [List.length_map] at this
    omega
  have houtval : operandVal cb lo (Operand.Var out) = some addrOrZero := by
    rw [operandVal_var_eq_lookupVar]; exact hout'
  have hStkFinal := planStackRel_push (planStackRel_popN hStkCb hlen4) houtval
  have hpop4 : stackPop 4 (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.stack
      = ps.stack := by
    rw [hps'stack, ← hlenops]
    exact stackPop_append_top ps.stack (ovars.map Operand.Var)
  rw [hpop4] at hStkFinal
  have hSpillFinal : planSpillRel lo cb
      (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.spilled s''.memory := by
    rw [hps'spill]
    rw [hps'spill] at hSpill1
    refine planSpillRel_frame_congr hSpill1 ?_ ?_
    · intro op off' hlook
      refine hstable op ?_
      intro hc
      rw [hc, hspill_out] at hlook
      simp at hlook
    · intro op off' hlook
      have hge : ps.alloc.fnEom ≤ off' := hspillReg op off' hlook
      have h32 : (32 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by norm_num) USize.le_size
      apply ByteArray.readWithPadding_congr _ _ off' 32 h32
      intro k hk
      have := hframe' (off' + k) (by omega)
      rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at this
      exact this
  refine ⟨s'', ?_, hstepV, ?_, ?_⟩
  · rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunE hrunC
  · refine ⟨?_, hSpillFinal, ?_, hacc'.symm, htr'.symm, hrd'.symm, hlg'.symm, hcc'.symm,
      htx'.symm, hbc'.symm, hcode'.symm, hph'.symm⟩
    · show planStackRel lo cb (ps.stack ++ [Operand.Var out]) s''.stack
      rw [hstk']
      show planStackRel lo cb (ps.stack ++ [Operand.Var out]) (addrOrZero :: as1.stack.drop 4)
      have hpush : stackPush (Operand.Var out) ps.stack = ps.stack ++ [Operand.Var out] := rfl
      rw [← hpush]
      exact hStkFinal
    · show memoryRel (emitInputPlan Opcode.CREATE2 (ovars.map Operand.Var) nl ps).2.alloc
        cb.memory s''.memory
      rw [hps'alloc]
      exact hmemrel'
  · rw [executePlan_append, List.length_append, hpcadv0, hpcE]
    rfl

/-- **CREATE2 plan reduction** (all-live 4 distinct var operands): emit the operands (already
    positioned — `reorderPlan_allVars_nil`), `CREATE` pops them and pushes the new address bound
    to `out` — net `+1`. -/
theorem genRegularInstPlan_create2_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {ovars : List String} {dists : List Nat} {out : String} {base : List Operand}
    (hopc : inst.opcode = Opcode.CREATE2)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps
      = (((emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).1
            ++ [StackOp.SOEmit "CREATE2"]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
                    stack := base ++ [Operand.Var out] }).1),
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
               stack := base ++ [Operand.Var out] }).2) := by
  have hname : opcodeToEvmName inst.opcode = some "CREATE2" := by rw [hopc]; rfl
  have hncomm : isCommutative inst.opcode = false := by rw [hopc]; rfl
  have hnjmp : ¬ (inst.opcode = Opcode.JMP) := by rw [hopc]; decide
  have hpvar := emitInputPlan_allVars_eq inst.opcode nextLiveness ovars dists ps hnospill hdepths
  unfold generateRegularInstPlan
  simp only [hcompute, houts]
  rcases hemit : emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps
    with ⟨inputOps, ps1⟩
  have h2 : (emitInputPlan inst.opcode (ovars.map Operand.Var) nextLiveness ps).2 = ps1 := by
    rw [hemit]
  have hps1' : ps1.stack = base ++ ovars.map Operand.Var := by
    rw [← h2, hpvar, hstack0]
  have hreorder := reorderPlan_allVars_nil base ovars ps1 hps1' hnd
  have hmem : out ∈ nextLiveness := by simpa using hlive
  have hpop : stackPop ovars.length (base ++ ovars.map Operand.Var) = base := by
    have h := stackPop_append_top base (ovars.map Operand.Var)
    rwa [List.length_map] at h
  simp [generateEmitOps_evmName hname, hreorder, hps1', hpop, stackPush, popmanyPlan_nil, hmem,
        hncomm, hnjmp]

/-- **The full generated-plan CREATE2 producer sim** — running the ENTIRE
    `generateRegularInstPlan` output for a CREATE2 (4 live operands, positioned; init code below
    the spill region) preserves the complete `venomAsmRel` against the Venom `stepExternalCall`
    writeback. The salted sibling of `genRegularInstPlan_create_sim`. -/
theorem genRegularInstPlan_create2_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {ovars : List String} {dists : List Nat} {out : String}
    {base : List Operand} {value off size salt : bytes32} {vals : List bytes32}
    {addrOrZero : bytes32} {newAccs : Accounts} {ret : List byte}
    (hopc : inst.opcode = Opcode.CREATE2)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base)
    (hnd : ovars.Nodup)
    (hnospill : ∀ v ∈ ovars, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness ovars dists ps.stack)
    (hlive : nextLiveness.contains out = true)
    (heval : evalOperands inst.operands vs = some [value, off, size, salt])
    (hvals : List.map (operandVal vs lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [value, off, size, salt])
    (hargs : off.toNat + size.toNat ≤ ps.alloc.fnEom) (hszlt : size.toNat < USize.size)
    (hfreshS : ¬ Operand.Var out ∈ ps.stack) (houtov : out ∉ ovars)
    (hspill_out : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
        ps.alloc.fnEom ≤ off')
    (hcreate : evmCreate subEvmFuel vs.accounts vs.callCtx.contract vs.txCtx.origin
      value (vs.memory.readWithPadding off.toNat size.toNat).toList vs.txCtx.gasprice 0 (some (wordToBytes salt).toList)
      = (addrOrZero, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_create2_eq hopc hcompute houts hstack0 hnd hnospill hdepths hlive,
      hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  rw [hcompute, hopc] at hblock ⊢
  rw [← hstack0]
  obtain ⟨s'', hrun, hstepV, hrelF, hpcF⟩ :=
    create2_block_emit_rel_full (offsetToPc := offsetToPc) hopc heval houts hnospill hdepths hvals
      hvalrev hargs hszlt hfreshS houtov hspill_out hspillReg hcreate hrel hblock
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelF
  exact ⟨s'', hrun, hstepV, hrelR, hpcF⟩

/-- The Venom step of a unary op with a variable operand is `updateVar out (f w)`. The unary
    counterpart of `stepInstBase_binopVar` (`execPure1` instead of `execPure2`). -/
theorem stepInstBase_unopVar {inst : Instruction} {v : VenomState} {x out : String}
    {w : bytes32} {f : bytes32 → bytes32}
    (hdispatch : stepInstBase inst v = execPure1 f inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hvx : lookupVar x v = some w) :
    stepInstBase inst v = ExecResult.OK (updateVar out (f w) v) := by
  rw [hdispatch]
  unfold execPure1
  rw [hops, houts]
  simp only [evalOperand, hvx]

/-- The Venom step of a ternary op with three variable operands is `updateVar out (f wx wy wz)`. The
    3-input counterpart of `stepInstBase_binopVar` (`execPure3` instead of `execPure2`); feeds the
    body-fold `gvBodyStep` for ADDMOD/MULMOD. -/
theorem stepInstBase_3opVar {inst : Instruction} {v : VenomState} {x y z out : String}
    {wx wy wz : bytes32} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hdispatch : stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hvx : lookupVar x v = some wx)
    (hvy : lookupVar y v = some wy)
    (hvz : lookupVar z v = some wz) :
    stepInstBase inst v = ExecResult.OK (updateVar out (f wx wy wz) v) := by
  rw [hdispatch]
  unfold execPure3
  rw [hops, houts]
  simp only [evalOperand, hvx, hvy, hvz]

/-- **Structural decomposition of `generateRegularInstPlan` for a commutative binop** with two
    distinct *variable* operands (both live, non-spilled; single live output, not halting). The var
    counterpart of `genRegularInstPlan_commBinopLit_eq`: identical plan shape, but the inputs are
    DUP'd (not pushed), so `base := ps.stack` (the operands sit on top of the *whole* original
    stack). The commutative cheaper-order `if` still picks the un-swapped (positioned, cost 0)
    order over the swapped (cost 1) one; the live inputs are not popped, the live output is kept. -/
theorem genRegularInstPlan_commBinopVar_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x y : String} {out : String} {base : List Operand} {name : String} {d_y d_x' : Nat}
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
  refine genRegularInstPlan_commBinopPair_eq hname hcomm hops houts
    (fun h => hxy (Operand.Var.inj h)) hlive ?_
  rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
        hdepth_x' hsmall_x', hstack0]

/-- **Per-instruction execution sim for a commutative binop, stated once for any operand pair**
    (optimistic swap a no-op). Composes the caller's input-emission sim (`hemitsim`),
    `emit_binop_sim`, and `releaseDeadSpills_sim` over `genRegularInstPlan_commBinopPair_eq`. The
    asm computes `f wq wp` directly — the codegen reversal already put the operands in semantic
    order — matching the Venom step `vs → updateVar out (f wq wp) vs`, so no commutativity bridge
    is needed on either side.

    Class-agnostic like its `_eq`: the operands enter only through `hemitstack` (where they land),
    `hemitsim` (how they get there), `hvp`/`hvq` (their values) and the freshness/distinctness
    side conditions. The all-literal, all-var, and **mixed Var/Lit** sims are its instances. -/
theorem genRegularInstPlan_commBinopPair_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {p q : Operand} {wp wq : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [q, p])
    (houts : inst.outputs = [out])
    (hqp : q ≠ p)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (houtp : Operand.Var out ≠ p) (houtq : Operand.Var out ≠ q)
    (hemitstack : (emitInputPlan inst.opcode [p, q] nextLiveness ps).2.stack = base ++ [p, q])
    (hemitspill : AssocList.lookup Operand Nat
      (emitInputPlan inst.opcode [p, q] nextLiveness ps).2.spilled (Operand.Var out) = none)
    (hemitsim : asmBlockAt prog as.pc
        (executePlan (emitInputPlan inst.opcode [p, q] nextLiveness ps).1) →
      ∃ as1, runAsm (executePlan (emitInputPlan inst.opcode [p, q] nextLiveness ps).1).length
               offsetToPc prog as = AsmResult.AsmOK as1 ∧
             venomAsmRel lo (emitInputPlan inst.opcode [p, q] nextLiveness ps).2 vs as1 ∧
             as1.pc = as.pc
               + (executePlan (emitInputPlan inst.opcode [p, q] nextLiveness ps).1).length)
    (hvp : operandVal vs lo p = some wp)
    (hvq : operandVal vs lo q = some wq)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wq wp) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [p, q] := by rw [hops]; rfl
  rw [genRegularInstPlan_commBinopPair_eq hname hcomm hops houts hqp hlive hemitstack,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [p, q] nextLiveness ps).2 with hps1def
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := hemitsim hbI
  have hstacktop : as1.stack = wq :: wp :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2 hrelI hemitstack hvp hvq
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1def, hemitstack]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hemitspill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1def, hemitstack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Per-instruction execution sim for the MIRROR stack order.** Operands `[x, y]` sit as
    `base ++ [x, y]` (`y` on top), so the asm pops `y` first and computes `f wy wx` where Venom
    computes `f wx wy`. Bridged by `hfcomm : f wx wy = f wy wx` — commutativity of `f` *as a
    function*, strictly stronger than the `isCommutative` opcode flag. This is the arm the generator
    actually reaches bare for a consuming op (`deadTopFn`), the mirror of
    `genRegularInstPlan_commBinopPair_sim`. -/
theorem genRegularInstPlan_commBinopPairMirror_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : Operand} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [x, y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hfcomm : f wx wy = f wy wx)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (houtx : Operand.Var out ≠ x) (houty : Operand.Var out ≠ y)
    (hemitstack : (emitInputPlan inst.opcode [y, x] nextLiveness ps).2.stack = base ++ [x, y])
    (hemitspill : AssocList.lookup Operand Nat
      (emitInputPlan inst.opcode [y, x] nextLiveness ps).2.spilled (Operand.Var out) = none)
    (hemitsim : asmBlockAt prog as.pc
        (executePlan (emitInputPlan inst.opcode [y, x] nextLiveness ps).1) →
      ∃ as1, runAsm (executePlan (emitInputPlan inst.opcode [y, x] nextLiveness ps).1).length
               offsetToPc prog as = AsmResult.AsmOK as1 ∧
             venomAsmRel lo (emitInputPlan inst.opcode [y, x] nextLiveness ps).2 vs as1 ∧
             as1.pc = as.pc
               + (executePlan (emitInputPlan inst.opcode [y, x] nextLiveness ps).1).length)
    (hvx : operandVal vs lo x = some wx)
    (hvy : operandVal vs lo y = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base ++ [Operand.Var out] }))
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
  have hrev : inst.operands.reverse = [y, x] := by rw [hops]; rfl
  rw [genRegularInstPlan_commBinopPairMirror_eq hname hcomm hops houts hxy hlive hemitstack,
      hoptnoop, hrev] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode [y, x] nextLiveness ps).2 with hps1def
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ := hemitsim hbI
  have hstacktop : as1.stack = wy :: wx :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2 hrelI hemitstack hvx hvy
  have hfresh1 : ¬ (Operand.Var out) ∈ ps1.stack := by
    rw [hps1def, hemitstack]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> simp_all
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_binop_sim hrelI hstacktop hfresh1 hemitspill hbE' (fun h hg => hdisp as1 h hg)
  rw [← hfcomm] at hrelE
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 2 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1def, hemitstack, stackPop_2_append_pair]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Per-instruction execution sim** for a commutative binop with two distinct *variable*
    operands (both live, non-spilled), when the optimistic swap is a no-op (`hoptnoop`). The var
    counterpart of `genRegularInstPlan_commBinopLit_sim`: composes `emitInputPlan_pair_var_sim`
    (two DUPs), `emit_binop_sim`, and `releaseDeadSpills_sim` over the var decomposition. The asm
    computes `f wx wy` directly (operands already in semantic order after the codegen reversal),
    matching the Venom step `vs → updateVar out (f wx wy) vs`. -/
theorem genRegularInstPlan_commBinopVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {d_y d_x' : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
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
  have hemitstack : (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by
    rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x', hstack0]
  refine genRegularInstPlan_commBinopPair_sim hname hcomm hops houts
    (fun h => hxy (Operand.Var.inj h)) hlive hfresh
    (fun h => hoy (Operand.Var.inj h)) (fun h => hox (Operand.Var.inj h)) hemitstack ?_ ?_
    hvy hvx hdisp hoptnoop hblock
  · rw [emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex
      hdepth_x' hsmall_x']; exact hspill
  · intro hbI
    obtain ⟨as1, hrunI, hrelI, hpcI, _⟩ := emitInputPlan_pair_var_sim hnospill_y hlivey hdepth_y
      hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hrel hbI
    exact ⟨as1, hrunI, hrelI, hpcI⟩

/-- **Active-swap variant of the commutative var-binop sim.** Drops the `hoptnoop` no-op assumption:
    the optimistic swap may genuinely reorder the stack, so its asm segment is run via
    `optimisticSwapPlan_sim` (vs-preserving) instead of being eliminated. Composes input emission,
    `emit_binop_sim`, `optimisticSwapPlan_sim` (the third asm segment), and `releaseDeadSpills_sim`.
    The Venom step is still `updateVar out (f wx wy) vs` (the swap is a pure stack reshuffle). `hswap`
    is `optimisticSwapPlan_sim`'s in-range bound on the post-emit stack `base ++ [Var out]`. The
    output plan stack is a *permutation* of `base ++ [Var out]`, tracked by `StackPerm`
    (`optimisticSwapPlan_stackPerm`) — so this composes with a `StackPerm`-threading fold. -/
theorem genRegularInstPlan_commBinopVar_sim_swap
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {d_y d_x' : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
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
  rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy hstack0 hlive
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

/-- **Per-instruction execution sim** for a commutative binop with two distinct literal
    operands, when the optimistic swap is a no-op (`hoptnoop`). Running the generated plan
    preserves `venomAsmRel` across the Venom step `vs → updateVar out (f a b) vs`, where `f` is
    the opcode's binary operation (`hdisp` ties `asmStep name` to `asmBinop f`, `hfcomm` is its
    commutativity, which bridges the asm/Venom argument-order swap). Composes the
    input-emission sim, `emit_binop_sim`, and `releaseDeadSpills_sim` over
    `genRegularInstPlan_commBinopLit_eq`. FFI-axiom-free: a literal binop touches no memory.

    `hoptnoop` holds when the next instruction is a terminator (via
    `optimisticSwapPlan_terminator`) or, more generally, when the output is already the
    next-scheduled var (the common well-scheduled case) — so this covers the mid-block case
    that the block-simulation fold needs, not just terminator-next. -/
theorem genRegularInstPlan_commBinopLit_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {a b : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
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
  -- The codegen reverses the operands, so the emitted (and asm-stacked) pair is `b, a` (TOS = a).
  -- The asm therefore computes `f a b` *directly* (matching Venom), with no commutativity bridge.
  have hemitstack : (emitInputPlan inst.opcode [Operand.Lit b, Operand.Lit a] nextLiveness ps).2.stack
      = base ++ [Operand.Lit b, Operand.Lit a] := by
    rw [emitInputPlan_pair_lit_eq, hstack0]
  refine genRegularInstPlan_commBinopPair_sim hname hcomm hops houts
    (fun h => hab (Operand.Lit.inj h)) hlive hfresh (by simp) (by simp) hemitstack ?_
    (fun hbI => emitInputPlan_pair_lit_sim hrel hbI) rfl rfl hdisp hoptnoop hblock
  · rw [emitInputPlan_pair_lit_eq]; exact hspill

/-- ADD instantiation of `genRegularInstPlan_commBinopLit_sim` — the first complete
    regular-opcode instruction simulation, end to end. -/
theorem genRegularInstPlan_addLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hadd : inst.opcode = Opcode.ADD)
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
             curBbLabel ps).2 (updateVar out (a + b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_commBinopLit_sim (by rw [hadd]; rfl) (by rw [hadd]; rfl) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_add_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- MUL instantiation — a second commutative opcode, confirming the generalization. -/
theorem genRegularInstPlan_mulLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hmul : inst.opcode = Opcode.MUL)
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
             curBbLabel ps).2 (updateVar out (a * b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_commBinopLit_sim (by rw [hmul]; rfl) (by rw [hmul]; rfl) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_mul_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-! ## Per-instruction execution sim (commutative binop, mixed Var/Lit operands)

The two remaining operand-class combinations, `OP %x, b` and `OP a, %y`. Both are instances of
`genRegularInstPlan_commBinopPair_sim`; the only new ingredient is the interleaved input emission
(`emitInputPlan_pair_litVar_sim` / `emitInputPlan_pair_varLit_sim`). Note the asymmetry in the depth
hypothesis: with the literal emitted *first* the var is DUP'd from the already-pushed stack
`ps.stack ++ [Lit b]`, whereas with the var first its depth is read off `ps.stack` directly. -/

/-- **Per-instruction execution sim for a commutative binop with operands `[Var x, Lit b]`**
    (`OP %x, b`), when the optimistic swap is a no-op. Compiled to `PUSH b ; DUP(d_x+1) ; OP`, so
    `d_x` is the var's depth in the *pushed* stack. The Venom step is `updateVar out (f wx b) vs`;
    the asm computes it directly (the codegen reversal already restored semantic order). -/
theorem genRegularInstPlan_commBinopVarLit_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x : String} {b wx : bytes32} {out : String} {base : List Operand} {name : String}
    {d_x : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hox : out ≠ x)
    (hstack0 : ps.stack = base)
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Lit b]) = some d_x)
    (hsmall_x : d_x ≤ 15)
    (hlenx : d_x < (ps.stack ++ [Operand.Lit b]).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
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
             nextIsTerminator curBbLabel ps).2 (updateVar out (f wx b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hemitstack : (emitInputPlan inst.opcode [Operand.Lit b, Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Lit b, Operand.Var x] := by
    rw [emitInputPlan_pair_litVar_eq hnospill_x hlivex hdepth_x hsmall_x, hstack0]
  refine genRegularInstPlan_commBinopPair_sim hname hcomm hops houts (by simp) hlive hfresh
    (by simp) (fun h => hox (Operand.Var.inj h)) hemitstack ?_
    (fun hbI => emitInputPlan_pair_litVar_sim hnospill_x hlivex hdepth_x hsmall_x hlenx hrel hbI)
    rfl hvx hdisp hoptnoop hblock
  · rw [emitInputPlan_pair_litVar_eq hnospill_x hlivex hdepth_x hsmall_x]; exact hspill

/-- **Per-instruction execution sim for a commutative binop with operands `[Lit a, Var y]`**
    (`OP a, %y`) — the mirror of `genRegularInstPlan_commBinopVarLit_sim`. Compiled to
    `DUP(d_y+1) ; PUSH a ; OP`, so `d_y` is the var's depth in the *original* stack. The Venom step
    is `updateVar out (f a wy) vs`. -/
theorem genRegularInstPlan_commBinopLitVar_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {y : String} {a wy : bytes32} {out : String} {base : List Operand} {name : String}
    {d_y : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [out])
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
             nextIsTerminator curBbLabel ps).2 (updateVar out (f a wy) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hemitstack : (emitInputPlan inst.opcode [Operand.Var y, Operand.Lit a] nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Lit a] := by
    rw [emitInputPlan_pair_varLit_eq hnospill_y hlivey hdepth_y hsmall_y, hstack0]
  refine genRegularInstPlan_commBinopPair_sim hname hcomm hops houts (by simp) hlive hfresh
    (fun h => hoy (Operand.Var.inj h)) (by simp) hemitstack ?_
    (fun hbI => emitInputPlan_pair_varLit_sim hnospill_y hlivey hdepth_y hsmall_y hleny hrel hbI)
    hvy rfl hdisp hoptnoop hblock
  · rw [emitInputPlan_pair_varLit_eq hnospill_y hlivey hdepth_y hsmall_y]; exact hspill

/-- ADD instantiation of the mixed `[Var x, Lit b]` sim — `%out = add %x, b` on the real
    generator, the mixed-operand counterpart of `genRegularInstPlan_addLit_sim`. -/
theorem genRegularInstPlan_addVarLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {x : String} {b wx : bytes32} {out : String} {base : List Operand} {d_x : Nat}
    (hadd : inst.opcode = Opcode.ADD)
    (hops : inst.operands = [Operand.Var x, Operand.Lit b]) (houts : inst.outputs = [out])
    (hox : out ≠ x) (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Lit b]) = some d_x)
    (hsmall_x : d_x ≤ 15) (hlenx : d_x < (ps.stack ++ [Operand.Lit b]).length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (wx + b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_commBinopVarLit_sim (by rw [hadd]; rfl) (by rw [hadd]; rfl) hops houts hox
    hstack0 hlive hfresh hspill hnospill_x hlivex hdepth_x hsmall_x hlenx hvx
    (fun _ h hg => asmStep_add_ok h hg) optimisticSwapPlan_terminator hrel hblock

/-! ## Per-instruction execution sim (commutative binop, DEAD operands — the consuming regime)

Both operands' last use is this instruction, so emission is empty and the opcode consumes them in
place: the plan is just `[SOEmit name]` and the stack goes `base ++ [Var y, Var x] ↦ base ++ [Var out]`
— it **shrinks** by one, where every arm above grows it by one.

Note what is NOT needed here: `genRegularInstPlan_commBinopPair_{eq,sim}` apply unchanged. They
constrain only where the operands END UP (`hemitstack`), never how they got there, so
"already positioned, emit nothing" discharges the same obligation that "DUP them into place" does.
The operands must be the top two (`hstack : ps.stack = base ++ [Var y, Var x]`) — for a commutative
opcode the cheaper-order `if` then picks the nil reorder, exactly as in the live case. -/

/-- **Per-instruction execution sim for a commutative binop whose operands are both DEAD** and
    already the top two of the stack. Emission is empty (`emitInputPlan_pair_dead_eq`), so the asm
    segment is the single `SOEmit`, and the plan stack shrinks: `base ++ [Var y, Var x]` becomes
    `base ++ [Var out]`. The Venom step is `updateVar out (f wx wy) vs`. -/
theorem genRegularInstPlan_commBinopDead_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var x])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nextLiveness.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nextLiveness.contains x = false)
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
  have hemit := emitInputPlan_pair_dead_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hdead_y hnospill_x hdead_x
  refine genRegularInstPlan_commBinopPair_sim hname hcomm hops houts
    (fun h => hxy (Operand.Var.inj h)) hlive hfresh
    (fun h => hoy (Operand.Var.inj h)) (fun h => hox (Operand.Var.inj h))
    (by rw [hemit]; exact hstack) (by rw [hemit]; exact hspill) ?_ hvy hvx hdisp hoptnoop hblock
  -- emission runs zero asm instructions, so the input-segment sim is the identity
  intro _
  exact ⟨as, by rw [hemit]; rfl, by rw [hemit]; exact hrel, by rw [hemit]; simp [executePlan]⟩

/-- **Per-instruction sim for a commutative binop, both operands DEAD, in the MIRROR order** — the
    config the generator actually emits bare for a consuming op (`deadTopFn`): stack
    `base ++ [Var x, Var y]` (`y` on top), operands `[Var x, Var y]`, emission empty, `↦ base ++
    [Var out]`. The asm computes `f wy wx`, bridged to Venom's `f wx wy` by `hfcomm`. -/
theorem genRegularInstPlan_commBinopDeadMirror_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x y : String} {wx wy : bytes32} {out : String} {base : List Operand} {name : String}
    {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hfcomm : f wx wy = f wy wx)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nextLiveness.contains y = false)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hdead_x : nextLiveness.contains x = false)
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
  have hemit := emitInputPlan_pair_dead_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hdead_y hnospill_x hdead_x
  refine genRegularInstPlan_commBinopPairMirror_sim hname hcomm hops houts
    (fun h => hxy (Operand.Var.inj h)) hfcomm hlive hfresh
    (fun h => hox (Operand.Var.inj h)) (fun h => hoy (Operand.Var.inj h))
    (by rw [hemit]; exact hstack) (by rw [hemit]; exact hspill) ?_ hvx hvy hdisp hoptnoop hblock
  intro _
  exact ⟨as, by rw [hemit]; rfl, by rw [hemit]; exact hrel, by rw [hemit]; simp [executePlan]⟩

end EvmYul.Venom.Hol.Codegen

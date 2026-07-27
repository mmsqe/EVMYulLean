/-
GenBlockSimComp / Phase 5 — regular body & entry discharge

Split part of `GenBlockSimComp`; see that module's header for the full roadmap.
This part continues the single `EvmYul.Venom.Hol.Codegen` namespace and imports
the previous part, so the whole was cut horizontally with no change in meaning.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.GrowthFolds

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-! ## Per-instruction regular-op step (comm/non-comm binops, unops, ternops)

`RegularStep` is the per-instruction 1-output regular-op class: a 4-way choice (commutative binop /
non-commutative binop / unop / ternop) over a shared output skeleton, each carrying exactly the facts
its `bodyStep_*` producer needs. It is the building block the general 0/1-output body fold below
(`RegularStepG`/`RegularBodyG`) dispatches its 1-output case to (via `regularStep_toBodyStep`). The
non-commutative/unop/ternop `optimisticSwapPlan` no-op obligation is free because the shared `gp` uses
`nextIsTerminator = true` (`optimisticSwapPlan … true = ([], ps)`). -/

/-- **Per-instruction regular-op step** (1-output var ops): a shared output skeleton
    (`out`/`name`/`outputs = [out]`/`out ∉ S`/`live out`) plus a 4-way choice of operand shape —
    commutative binop / non-commutative binop / unop / ternop — each carrying exactly the facts its
    `bodyStep_*` producer needs. -/
def RegularStep (nextLiveness : List String) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (inst : Instruction) (S : List String) : Prop :=
  ∃ (out name : String), inst.outputs = [out] ∧ opcodeToEvmName inst.opcode = some name ∧
    out ∉ S ∧ nextLiveness.contains out = true ∧
    ( -- commutative binop
      (∃ (x y : String) (f : bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = true ∧ (∀ v, stepInstBase inst v = execPure2 f inst v) ∧
        inst.operands = [Operand.Var x, Operand.Var y] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
        nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s))
    ∨ -- non-commutative binop
      (∃ (x y : String) (f : bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = false ∧ inst.opcode ≠ Opcode.JMP ∧
        computeOperands inst = inst.operands.reverse ∧ (∀ v, stepInstBase inst v = execPure2 f inst v) ∧
        inst.operands = [Operand.Var x, Operand.Var y] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
        nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s))
    ∨ -- unop
      (∃ (x : String) (f : bytes32 → bytes32),
        inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
        (∀ v, stepInstBase inst v = execPure1 f inst v) ∧
        inst.operands = [Operand.Var x] ∧ x ∈ S ∧ nextLiveness.contains x = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s))
    ∨ -- ternop
      (∃ (x y z : String) (f : bytes32 → bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = false ∧ inst.opcode ≠ Opcode.JMP ∧
        computeOperands inst = inst.operands.reverse ∧ (∀ v, stepInstBase inst v = execPure3 f inst v) ∧
        inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z] ∧
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x ∈ S ∧ y ∈ S ∧ z ∈ S ∧
        nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧ nextLiveness.contains z = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s))
    ∨ -- commutative binop, BOTH operands literal (compiled to `PUSH b ; PUSH a ; OP`): no DUPs,
      -- no stack-var interaction, so the operands need no `∈ S` membership and no liveness.
      (∃ (av bv : bytes32) (f : bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = true ∧ (∀ v, stepInstBase inst v = execPure2 f inst v) ∧
        inst.operands = [Operand.Lit av, Operand.Lit bv] ∧ av ≠ bv ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s))
    ∨ -- commutative binop, MIXED `[Var x, Lit bv]` (compiled to `PUSH bv ; DUP ; OP`): one var, so
      -- `x ∈ S` and its liveness are needed, but no operand distinctness (the classes differ).
      (∃ (x : String) (bv : bytes32) (f : bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = true ∧ (∀ v, stepInstBase inst v = execPure2 f inst v) ∧
        inst.operands = [Operand.Var x, Operand.Lit bv] ∧ x ∈ S ∧
        nextLiveness.contains x = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s))
    ∨ -- commutative binop, MIXED `[Lit av, Var y]` (compiled to `DUP ; PUSH av ; OP`) — the mirror.
      (∃ (y : String) (av : bytes32) (f : bytes32 → bytes32 → bytes32),
        isCommutative inst.opcode = true ∧ (∀ v, stepInstBase inst v = execPure2 f inst v) ∧
        inst.operands = [Operand.Lit av, Operand.Var y] ∧ y ∈ S ∧
        nextLiveness.contains y = true ∧
        (∀ (s : AsmState) (h : s.pc < prog.length),
          prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)))

/-! ## Fully general 0/1-output regular body (arithmetic + storage stores)

A 1-output-only body fold excludes observable-effect 0-output ops. This is the general 0/1-output fold
(`BodyStepG`/`BodyStepsReadyG`/
`genBlockBodyG_sim_inv`, headroom = `Σ outsOf`): `RegularStepG` allows each instruction to be a
1-output `RegularStep` or a 0-output storage store (SSTORE/TSTORE), `RegularBodyG` threads it, and
`bodyStepsReadyG_regular_list` dispatches — a 1-output op bridged into the general fold by
`bodyStepG_of_bodyStep ∘ regularStep_toBodyStep`, a store by `bodyStepG_{sstore,tstore}`. The missing
prefix composition (`genBlockPrefixBodyG_sim_inv`) is the `genBlockBodyG_sim_inv` twin of
`genBlockPrefixBody_sim_inv`. `genBlockSimulation_regularGN_halt` wires it into the first per-block
`hsim` mixing observable-effect and value-producing instructions.

(Memory stores MSTORE/MSTORE8 additionally need a per-instruction memory-coverage hypothesis
`hmemsafe`; LOG/CALLDATACOPY use the demand-decoupled fold `genBlockBodyH_sim_inv` — both are further
extensions of this shape.) -/

/-- The `BodyStep` for a 1-output regular op (`RegularStep`), factored so the general 0/1-output body
    fold can dispatch its 1-output case to it (bridged into `BodyStepG` by `bodyStepG_of_bodyStep`). -/
theorem regularStep_toBodyStep
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {inst : Instruction} {S : List String} {k : Nat}
    (h : RegularStep nextLiveness offsetToPc prog inst S) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, k) S := by
  obtain ⟨out, name, houts, hname, houtS, hlive, hdisj⟩ := h
  rcases hdisj with
    ⟨x, y, f, hcomm, hdisp', hops, hxy, hxS, hyS, hlivex, hlivey, hdisp⟩ |
    ⟨x, y, f, hncomm, hnjmp, hcompute, hdisp', hops, hxy, hxS, hyS, hlivex, hlivey, hdisp⟩ |
    ⟨x, f, hnjmp, hcompute, hdisp', hops, hxS, hlivex, hdisp⟩ |
    ⟨x, y, z, f, hncomm, hnjmp, hcompute, hdisp', hops, hxy, hyz, hxz, hxS, hyS, hzS, hlivex, hlivey, hlivez, hdisp⟩ |
    ⟨av, bv, f, hcomm, hdisp', hops, hab, hdisp⟩ |
    ⟨x, bv, f, hcomm, hdisp', hops, hxS, hlivex, hdisp⟩ |
    ⟨y, av, f, hcomm, hdisp', hops, hyS, hlivey, hdisp⟩
  · exact bodyStep_commBinop (idx := k) hname hcomm hdisp' hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp
  · exact bodyStep_nonCommBinopVar (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute
      hdisp' hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp (fun p => by simp [optimisticSwapPlan])
  · exact bodyStep_unopVar (idx := k) (nextIsTerminator := true) hname hnjmp hcompute hdisp' hops houts
      hxS houtS hlive hlivex hdisp (fun p => by simp [optimisticSwapPlan])
  · exact bodyStep_ternopVar (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute hdisp'
      hops houts hxy hyz hxz hxS hyS hzS houtS hlive hlivex hlivey hlivez hdisp
      (fun p => by simp [optimisticSwapPlan])
  · exact bodyStep_commBinopLit (idx := k) hname hcomm hdisp' hops houts hab houtS hlive hdisp
  · exact bodyStep_commBinopVarLit (idx := k) hname hcomm hdisp' hops houts hxS houtS hlive hlivex
      hdisp
  · exact bodyStep_commBinopLitVar (idx := k) hname hcomm hdisp' hops houts hyS houtS hlive hlivey
      hdisp

/-- **Invariant-threading prefix-body sim for the general 0/1-output fold.** The `BodyStepsReadyG`
    twin of `genBlockPrefixBody_sim_inv`: runs the block's `SOLabel` prefix then the body via
    `genBlockBodyG_sim_inv` (headroom `Σ outsOf`), landing the asm at `sEnd`. -/
theorem genBlockPrefixBodyG_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hready : BodyStepsReadyG lo offsetToPc prog gp (front.zipIdx 0) S0)
    (hsd0 : StackDiscH ((front.zipIdx 0).flatMap outsOf).length ps0 vs0)
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
    genBlockBodyG_sim_inv gp (front.zipIdx 0) S0 ps0 vs0 as1 hready hsd0 hsv0 h1rel hbody'
  rw [execBodyThread_eq_gvFold front 0 vs0 sEnd hthread] at h2rel
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Per-instruction general regular step** (0- and 1-output): a 1-output `RegularStep`, a 0-output
    storage store (SSTORE / TSTORE), or a 0-output memory store (MSTORE / MSTORE8). The memory stores
    additionally carry a per-instruction memory-coverage obligation `hmemsafe` (the write window lies
    within user memory and below the spill region), so `RegularStepG` is parameterised by the relation's
    `lo`. -/
def RegularStepG (lo : AssocList String Nat) (nextLiveness : List String)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (inst : Instruction) (S : List String) : Prop :=
  RegularStep nextLiveness offsetToPc prog inst S
  ∨ (∃ (x y : String),
      opcodeToEvmName inst.opcode = some "SSTORE" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execWrite2 (fun key val s => sstore key val s) inst v) ∧
      inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
      nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s))
  ∨ (∃ (x y : String),
      opcodeToEvmName inst.opcode = some "TSTORE" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execWrite2 (fun key val s => tstore key val s) inst v) ∧
      inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
      nextLiveness.contains x = true ∧ nextLiveness.contains y = true)
  ∨ (∃ (x y : String),
      opcodeToEvmName inst.opcode = some "MSTORE" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore addr.toNat val s) inst v) ∧
      inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
      nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 32 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 32 ≤ p.alloc.fnEom) ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s))
  ∨ (∃ (x y : String),
      opcodeToEvmName inst.opcode = some "MSTORE8" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst v) ∧
      inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [] ∧ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧
      nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 1 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 1 ≤ p.alloc.fnEom) ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s))
  ∨ (∃ (out name : String) (fV : VenomState → bytes32) (fA : AsmState → bytes32),
      opcodeToEvmName inst.opcode = some name ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      inst.operands = [] ∧ inst.outputs = [out] ∧ out ∉ S ∧ nextLiveness.contains out = true ∧
      (∀ v, stepInstBase inst v = ExecResult.OK (updateVar out (fV v) v)) ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fA s) s) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v))
  ∨ (∃ (x out name : String) (fRead : bytes32 → Accounts → bytes32),
      opcodeToEvmName inst.opcode = some name ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execRead1 (fun addr s => fRead addr s.accounts) inst v) ∧
      inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧ x ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s))
  ∨ (∃ (x out : String),
      opcodeToEvmName inst.opcode = some "TLOAD" ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execRead1 (fun key s => tload key s) inst v) ∧
      inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧ x ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s))
  ∨ (∃ (x out : String),
      opcodeToEvmName inst.opcode = some "CALLDATALOAD" ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execRead1 (fun offset s =>
          wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) inst v) ∧
      inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧ x ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "CALLDATALOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun offset s =>
            wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s))
  ∨ (∃ (x y out : String),
      inst.opcode = Opcode.SHA3 ∧
      inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [out] ∧
      x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wx wy,
        venomAsmRel lo p v s → lookupVar x v = some wx → lookupVar y v = some wy →
        ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wx.toNat + wy.toNat ≤ p.alloc.fnEom ∧ wy.toNat < USize.size) ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SHA3" → asmStep offsetToPc prog s = asmSha3 s))
  ∨ (∃ (x out : String),
      opcodeToEvmName inst.opcode = some "SLOAD" ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execRead1 (fun key s => sload key s) inst v) ∧
      inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧ x ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s))
  ∨ (∃ (x out : String),
      opcodeToEvmName inst.opcode = some "BLOCKHASH" ∧ inst.opcode ≠ Opcode.JMP ∧
      computeOperands inst = inst.operands.reverse ∧
      (∀ v, stepInstBase inst v = execRead1 (fun v s => s.blockCtx.blockhash v.toNat) inst v) ∧
      inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧ x ∈ S ∧ out ∉ S ∧
      nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧
      (∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "BLOCKHASH" →
          asmStep offsetToPc prog s = asmStateUnop (fun v s => s.blockCtx.blockhash v.toNat) s))

/-! ### Gap-B: deriving `RegularStepG` from a well-formedness predicate

`RegularStepG`'s disjuncts bundle two kinds of fact: (1) *structural* — the operands are the distinct
live vars, in the tracked stack `S` and in `nextLiveness`, with the right outputs — which a SSA +
liveness pass supplies; and (2) *opcode-specific* — the semantics (`stepInstBase = execWrite2 …`) and the
asm sim — which follow from `inst.opcode`. The classifiers below package (1) as a WF predicate and
discharge (2) from the opcode, so `RegularStepG` for a whole opcode class reduces to a WF check —
generalising the hand-proved concrete instances (`sstore_regularBodyG` &c.) to *any* instruction of the
class. (The remaining gap-B step is deriving the WF predicate itself from a formalised SSA/liveness
analysis; here it is stated as the hypothesis a correct pass would establish.) -/

/-- **Well-formedness of a 2-input var-store instruction** — the facts a SSA + liveness pass supplies:
    the two operands are the distinct live vars `x, y` (both in the tracked stack `S` and in
    `nextLiveness`), and there are no outputs. Exactly the derivable-from-analysis content of a
    `RegularStepG` store disjunct; the opcode-specific parts come from `inst.opcode`. -/
def RegularStoreWf (nextLiveness S : List String) (x y : String) (inst : Instruction) : Prop :=
  inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [] ∧
  x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ nextLiveness.contains x = true ∧ nextLiveness.contains y = true

/-- **Gap-B classifier for the SSTORE class.** `RegularStepG` for *any* SSTORE instruction, derived from
    `RegularStoreWf` (the SSA/liveness facts) with the opcode-specific parts discharged from
    `inst.opcode = SSTORE`. Generalises the hand-proved `sstore_regularBodyG` (a fixed instruction) to the
    whole SSTORE class, reducing its `RegularStepG` obligation to the WF predicate. -/
theorem regularStepG_sstore_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x y : String}
    (hopc : inst.opcode = Opcode.SSTORE) (hwf : RegularStoreWf nextLiveness S x y inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩ := hwf
  right; left
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, hops, houts, hxy, hxS, hyS, hlivex, hlivey, ?_⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execWrite2, hops]
  · intro s h hp; exact asmStep_sstore_ok h hp

/-- **Gap-B classifier for the TSTORE class** (transient store — no memory-safety / asm-sim conjunct). -/
theorem regularStepG_tstore_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x y : String}
    (hopc : inst.opcode = Opcode.TSTORE) (hwf : RegularStoreWf nextLiveness S x y inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩ := hwf
  right; right; left
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execWrite2, hops]

/-- **Well-formedness of a 2-input memory-store instruction** (MSTORE / MSTORE8) — the store WF facts
    plus the per-instruction memory-coverage obligation on the address operand `x` (the write window of
    `wsz` bytes lies within user memory and below the spill region). `wsz = 32` for MSTORE, `1` for
    MSTORE8. Exactly the derivable-from-analysis + memory-safety content of a memory-store disjunct. -/
def RegularMemStoreWf (lo : AssocList String Nat) (nextLiveness S : List String) (x y : String)
    (inst : Instruction) (wsz : Nat) : Prop :=
  RegularStoreWf nextLiveness S x y inst ∧
  (∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
    venomAsmRel lo p v s → lookupVar x v = some w →
    w.toNat ≤ v.memory.size ∧ ((w.toNat + wsz + 31) / 32) * 32 ≤ s.memory.size ∧
    w.toNat + wsz ≤ p.alloc.fnEom)

/-- **Gap-B classifier for the MSTORE class.** `RegularStepG` for any MSTORE instruction, from
    `RegularMemStoreWf … 32` (SSA/liveness + memory-safety) with the opcode-specific parts discharged
    from `inst.opcode = MSTORE`. -/
theorem regularStepG_mstore_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x y : String}
    (hopc : inst.opcode = Opcode.MSTORE) (hwf : RegularMemStoreWf lo nextLiveness S x y inst 32) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨⟨hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩, hmemsafe⟩ := hwf
  right; right; right; left
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, hops, houts, hxy, hxS, hyS, hlivex, hlivey, hmemsafe, ?_⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execWrite2, hops]
  · intro s h hp; exact asmStep_mstore_ok h hp

/-- **Gap-B classifier for the MSTORE8 class** — as `regularStepG_mstore_of_wf` with the 1-byte
    write window (`RegularMemStoreWf … 1`). -/
theorem regularStepG_mstore8_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x y : String}
    (hopc : inst.opcode = Opcode.MSTORE8) (hwf : RegularMemStoreWf lo nextLiveness S x y inst 1) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨⟨hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩, hmemsafe⟩ := hwf
  right; right; right; right; left
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, hops, houts, hxy, hxS, hyS, hlivex, hlivey, hmemsafe, ?_⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execWrite2, hops]
  · intro s h hp; exact asmStep_mstore8_ok h hp

/-- **Well-formedness of a 1-input 1-output read instruction** (TLOAD / CALLDATALOAD) — the single
    operand `x` is a live var in the tracked stack `S`, the output `out` is fresh (`∉ S`), and both are
    live in `nextLiveness`. The derivable-from-analysis content of a read disjunct. -/
def RegularUnaryReadWf (nextLiveness S : List String) (x out : String) (inst : Instruction) : Prop :=
  inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧
  x ∈ S ∧ out ∉ S ∧ nextLiveness.contains out = true ∧ nextLiveness.contains x = true

/-- **Gap-B classifier for the TLOAD class.** -/
theorem regularStepG_tload_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x out : String}
    (hopc : inst.opcode = Opcode.TLOAD) (hwf : RegularUnaryReadWf nextLiveness S x out inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxS, houtS, hliveout, hlivex⟩ := hwf
  right; right; right; right; right; right; right; left
  refine ⟨x, out, ?_, ?_, ?_, ?_, hops, houts, hxS, houtS, hliveout, hlivex, ?_⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execRead1, hops]
  · intro s h hp; exact asmStep_tload_ok h hp

/-- **Gap-B classifier for the CALLDATALOAD class.** -/
theorem regularStepG_calldataload_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x out : String}
    (hopc : inst.opcode = Opcode.CALLDATALOAD) (hwf : RegularUnaryReadWf nextLiveness S x out inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxS, houtS, hliveout, hlivex⟩ := hwf
  right; right; right; right; right; right; right; right; left
  refine ⟨x, out, ?_, ?_, ?_, ?_, hops, houts, hxS, houtS, hliveout, hlivex, ?_⟩
  · rw [hopc]; rfl
  · rw [hopc]; decide
  · simp [computeOperands, hopc, hops]
  · intro v; simp only [stepInstBase, hopc, execRead1, hops]
  · intro s h hp; exact asmStep_calldataload_ok h hp

/-- **Well-formedness of the SHA3 instruction** (2-input 1-output, keccak of a memory slice) — the two
    distinct live operands `x, y` in `S`, the fresh live output `out`, and the memory-coverage
    obligation on the `(offset, size)` window. The derivable-from-analysis + memory-safety content of
    the SHA3 disjunct. -/
def RegularSha3Wf (lo : AssocList String Nat) (nextLiveness S : List String) (x y out : String)
    (inst : Instruction) : Prop :=
  inst.operands = [Operand.Var x, Operand.Var y] ∧ inst.outputs = [out] ∧
  x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ out ∉ S ∧
  nextLiveness.contains out = true ∧ nextLiveness.contains x = true ∧ nextLiveness.contains y = true ∧
  (∀ (p : PlanState) (v : VenomState) (s : AsmState) wx wy,
    venomAsmRel lo p v s → lookupVar x v = some wx → lookupVar y v = some wy →
    ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
    wx.toNat + wy.toNat ≤ p.alloc.fnEom ∧ wy.toNat < USize.size)

/-- **Gap-B classifier for the SHA3 class.** -/
theorem regularStepG_sha3_of_wf {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x y out : String}
    (hopc : inst.opcode = Opcode.SHA3) (hwf : RegularSha3Wf lo nextLiveness S x y out inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxy, hxS, hyS, houtS, hliveout, hlivex, hlivey, hmemsafe⟩ := hwf
  right; right; right; right; right; right; right; right; right; left
  exact ⟨x, y, out, hopc, hops, houts, hxy, hxS, hyS, houtS, hliveout, hlivex, hlivey, hmemsafe,
    fun s h hp => asmStep_sha3_ok h hp⟩

/-- **Well-formedness of a 0-input 1-output environment op** (CALLER / GAS / ADDRESS / …) — a fresh
    live output `out` and no operands. The derivable-from-analysis content of an env disjunct. -/
def RegularEnvWf (nextLiveness S : List String) (out : String) (inst : Instruction) : Prop :=
  inst.operands = [] ∧ inst.outputs = [out] ∧ out ∉ S ∧ nextLiveness.contains out = true

/-- **Gap-B classifier for the environment-op class.** Unlike the fixed-opcode classifiers, the env
    disjunct is parametric over the opcode `name` and the value functions `fV`/`fA`, so those
    opcode-specific facts (the name mapping, the semantics, the asm push-sim, and their agreement under
    `venomAsmRel`) are supplied as hypotheses; the WF predicate carries the structural part. -/
theorem regularStepG_env_of_facts {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {out name : String} {fV : VenomState → bytes32} {fA : AsmState → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name) (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hsem : ∀ v, stepInstBase inst v = ExecResult.OK (updateVar out (fV v) v))
    (hasm : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fA s) s)
    (hrel : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v)
    (hwf : RegularEnvWf nextLiveness S out inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, houtS, hliveout⟩ := hwf
  right; right; right; right; right; left
  exact ⟨out, name, fV, fA, hname, hnjmp, hcompute, hops, houts, houtS, hliveout, hsem, hasm, hrel⟩

/-- **Well-formedness of a 1-input 1-output account read** (SLOAD / BALANCE / EXTCODESIZE / …) — the
    operand `x` live in `S`, the output `out` fresh, both live. The derivable-from-analysis content of
    the generic read disjunct. -/
def RegularAccountReadWf (nextLiveness S : List String) (x out : String) (inst : Instruction) : Prop :=
  inst.operands = [Operand.Var x] ∧ inst.outputs = [out] ∧
  x ∈ S ∧ out ∉ S ∧ nextLiveness.contains out = true ∧ nextLiveness.contains x = true

/-- **Gap-B classifier for the generic account-read class.** As `regularStepG_env_of_facts`, the read
    disjunct is parametric over `name`/`fRead`; those opcode-specific facts are supplied as hypotheses
    and the WF predicate carries the structural part. -/
theorem regularStepG_read_of_facts {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {inst : Instruction} {S : List String}
    {x out name : String} {fRead : bytes32 → Accounts → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name) (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hsem : ∀ v, stepInstBase inst v = execRead1 (fun addr s => fRead addr s.accounts) inst v)
    (hasm : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
          asmStep offsetToPc prog s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s)
    (hwf : RegularAccountReadWf nextLiveness S x out inst) :
    RegularStepG lo nextLiveness offsetToPc prog inst S := by
  obtain ⟨hops, houts, hxS, houtS, hliveout, hlivex⟩ := hwf
  right; right; right; right; right; right; left
  exact ⟨x, out, name, fRead, hname, hnjmp, hcompute, hsem, hops, houts, hxS, houtS, hliveout, hlivex, hasm⟩

/-- **Straight-line general regular-op body** (mixed 0- and 1-output ops): each instruction a
    `RegularStepG`, the tracked stack growing by each output. -/
def RegularBodyG (lo : AssocList String Nat) (nextLiveness : List String)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) :
    List Instruction → List String → Prop
  | [], _ => True
  | inst :: rest, S =>
      RegularStepG lo nextLiveness offsetToPc prog inst S ∧
      RegularBodyG lo nextLiveness offsetToPc prog rest (S ++ inst.outputs)

/-! ### Gap-B structural facts: the tracked stack is the accumulated outputs

`RegularBodyG` threads the tracked stack as `S ++ inst.outputs`, so at position `k` it is exactly
`S0 ++ (instrs.take k).flatMap outputs` — the base plus the outputs of the earlier instructions. This
pins the classifier's *structural* hypotheses (`x ∈ S`, `out ∉ S`) to plain facts about definitions: a
used var is in `S` because it was defined earlier (def-before-use), and an output is fresh in `S`
because it was not defined before (SSA single-definition). -/

/-- **Operand availability from an earlier definition.** A var defined by an instruction `j < k` is in
    the accumulated-outputs tracked stack at position `k` — the `x ∈ S` structural fact a def-before-use
    (SSA) pass supplies. -/
theorem operand_mem_stackAt (base : List String) (instrs : List Instruction) (k j : Nat) (x : String)
    (hjk : j < k) (hj : j < instrs.length) (hx : x ∈ (instrs.get ⟨j, hj⟩).outputs) :
    x ∈ base ++ (instrs.take k).flatMap (·.outputs) := by
  apply List.mem_append_right
  rw [List.mem_flatMap]
  have hjtk : j < (instrs.take k).length := by rw [List.length_take]; omega
  refine ⟨(instrs.take k)[j]'hjtk, List.getElem_mem hjtk, ?_⟩
  rw [List.getElem_take]
  rwa [List.get_eq_getElem] at hx

/-- **Output freshness.** A var not in the base and not an output of any earlier instruction is absent
    from the accumulated-outputs tracked stack at position `k` — the `out ∉ S` structural fact a
    single-definition (SSA) pass supplies. -/
theorem output_not_mem_stackAt (base : List String) (instrs : List Instruction) (k : Nat) (out : String)
    (hbase : out ∉ base)
    (hfresh : ∀ j (hj : j < instrs.length), j < k → out ∉ (instrs.get ⟨j, hj⟩).outputs) :
    out ∉ base ++ (instrs.take k).flatMap (·.outputs) := by
  intro hmem
  rw [List.mem_append] at hmem
  rcases hmem with h | h
  · exact hbase h
  · rw [List.mem_flatMap] at h
    obtain ⟨inst, hinst, hout⟩ := h
    rw [List.mem_iff_getElem] at hinst
    obtain ⟨j, hjlt, hgetj⟩ := hinst
    have hjk : j < k := by rw [List.length_take] at hjlt; omega
    have hjinstrs : j < instrs.length := by rw [List.length_take] at hjlt; omega
    subst hgetj
    rw [List.getElem_take] at hout
    exact hfresh j hjinstrs hjk hout

/-- **Body-level classifier: assemble `RegularBodyG` from per-position `RegularStepG`.** The tracked
    stack at position `k` is exactly the base plus the outputs of the earlier instructions
    (`S0 ++ (instrs.take k).flatMap outputs`), so a `RegularStepG` at each position — whose `x ∈ S` /
    `out ∉ S` facts come from `operand_mem_stackAt` / `output_not_mem_stackAt` — yields the whole body.
    The bridge from the per-instruction classifiers to a straight-line block body. -/
theorem RegularBodyG_of_steps {lo : AssocList String Nat} {nextLiveness : List String}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} (instrs : List Instruction) (S0 : List String)
    (hsteps : ∀ k (hk : k < instrs.length),
      RegularStepG lo nextLiveness offsetToPc prog (instrs.get ⟨k, hk⟩)
        (S0 ++ (instrs.take k).flatMap (·.outputs))) :
    RegularBodyG lo nextLiveness offsetToPc prog instrs S0 := by
  induction instrs generalizing S0 with
  | nil => trivial
  | cons inst rest ih =>
    refine ⟨?_, ?_⟩
    · have h0 := hsteps 0 (by simp)
      simpa using h0
    · apply ih
      intro k hk
      have hk1 := hsteps (k + 1) (by simpa using Nat.succ_lt_succ hk)
      simpa [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using hk1

/-- **Gap-B capstone (store class): `RegularStoreWf` fully derived from SSA + liveness facts.** For a
    store `SSTORE x y` at position `k` of a WF function's block, the well-formedness predicate the
    classifier `regularStepG_sstore_of_wf` consumes is discharged entirely from analysis facts:
    `x ∈ S` / `y ∈ S` from def-before-use (each operand defined by an earlier instruction) via
    `operand_mem_stackAt` (the tracked stack `S` being the accumulated outputs); and
    `nextLiveness.contains x/y` from the operands being reused later (not redefined between) via
    `liveVarsAt_contains_of_use_later` (`nextLiveness = liveVarsAt … lbl0 (k+1)`). The remaining fields
    (`operands`, `outputs`, `x ≠ y`) are syntactic. End-to-end validation of the gap-B discharge for a
    concrete opcode class: composed with `regularStepG_sstore_of_wf` it gives `RegularStepG` from
    analysis facts alone. -/
theorem regularStoreWf_of_ssa {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {S0 : List String} {k : Nat} {x y : String} {inst : Instruction}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (hdefy : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ y ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husey : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      y ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → y ∉ (bb.instructions.get ⟨m, hm⟩).outputs)) :
    RegularStoreWf (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1))
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) x y inst := by
  obtain ⟨jx, hjx, hjxk, hxdef⟩ := hdefx
  obtain ⟨jy, hjy, hjyk, hydef⟩ := hdefy
  obtain ⟨ux, hux, huxk, huxphi, hxuse, hxnodef⟩ := husex
  obtain ⟨uy, huy, huyk, huyphi, hyuse, hynodef⟩ := husey
  refine ⟨hops, houts, hxy, ?_, ?_, ?_, ?_⟩
  · exact operand_mem_stackAt S0 bb.instructions k jx x hjxk hjx hxdef
  · exact operand_mem_stackAt S0 bb.instructions k jy y hjyk hjy hydef
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl hux huxk huxphi hxuse hxnodef
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl huy huyk huyphi hyuse hynodef

/-- **Gap-B capstone (SHA3 class): `RegularSha3Wf` from SSA + liveness facts.** Like
    `regularStoreWf_of_ssa` but for a 1-output op, so it additionally discharges `out ∉ S` (from
    single-definition, via `output_not_mem_stackAt`) and `nextLiveness.contains out` (the output being
    used later). The memory-coverage obligation is carried as a hypothesis (opcode-specific). Exercises
    the *output* half of the structural bridge that the (0-output) store capstone does not. -/
theorem regularSha3Wf_of_ssa {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {lo : AssocList String Nat} {S0 : List String} {k : Nat} {x y out : String} {inst : Instruction}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (hdefy : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ y ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (houtbase : out ∉ S0)
    (houtfresh : ∀ (j : Nat) (hj : j < bb.instructions.length), j < k → out ∉ (bb.instructions.get ⟨j, hj⟩).outputs)
    (huseo : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      out ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → out ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husey : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      y ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → y ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wx wy,
      venomAsmRel lo p v s → lookupVar x v = some wx → lookupVar y v = some wy →
      ((wx.toNat + wy.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
      wx.toNat + wy.toNat ≤ p.alloc.fnEom ∧ wy.toNat < USize.size) :
    RegularSha3Wf lo (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1))
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) x y out inst := by
  obtain ⟨jx, hjx, hjxk, hxdef⟩ := hdefx
  obtain ⟨jy, hjy, hjyk, hydef⟩ := hdefy
  obtain ⟨uo, huo, huok, huophi, house, honodef⟩ := huseo
  obtain ⟨ux, hux, huxk, huxphi, hxuse, hxnodef⟩ := husex
  obtain ⟨uy, huy, huyk, huyphi, hyuse, hynodef⟩ := husey
  refine ⟨hops, houts, hxy, ?_, ?_, ?_, ?_, ?_, ?_, hmemsafe⟩
  · exact operand_mem_stackAt S0 bb.instructions k jx x hjxk hjx hxdef
  · exact operand_mem_stackAt S0 bb.instructions k jy y hjyk hjy hydef
  · exact output_not_mem_stackAt S0 bb.instructions k out houtbase houtfresh
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl huo huok huophi house honodef
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl hux huxk huxphi hxuse hxnodef
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl huy huyk huyphi hyuse hynodef

/-- **Gap-B capstone (read class): `RegularUnaryReadWf` from SSA + liveness facts.** The 1-input
    1-output shape (TLOAD / CALLDATALOAD): a single operand `x` (in `S` from def-before-use), a fresh
    output `out` (`∉ S` from single-definition), both live in `nextLiveness`. Completes the operand-shape
    coverage of the gap-B discharge (0-out/2-op store, 1-out/2-op SHA3, 1-out/1-op read). -/
theorem regularUnaryReadWf_of_ssa {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {S0 : List String} {k : Nat} {x out : String} {inst : Instruction}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (houtbase : out ∉ S0)
    (houtfresh : ∀ (j : Nat) (hj : j < bb.instructions.length), j < k → out ∉ (bb.instructions.get ⟨j, hj⟩).outputs)
    (huseo : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      out ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → out ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs)) :
    RegularUnaryReadWf (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1))
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) x out inst := by
  obtain ⟨jx, hjx, hjxk, hxdef⟩ := hdefx
  obtain ⟨uo, huo, huok, huophi, house, honodef⟩ := huseo
  obtain ⟨ux, hux, huxk, huxphi, hxuse, hxnodef⟩ := husex
  refine ⟨hops, houts, ?_, ?_, ?_, ?_⟩
  · exact operand_mem_stackAt S0 bb.instructions k jx x hjxk hjx hxdef
  · exact output_not_mem_stackAt S0 bb.instructions k out houtbase houtfresh
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl huo huok huophi house honodef
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl hux huxk huxphi hxuse hxnodef

/-- **Gap-B capstone (environment-op class): `RegularEnvWf` from SSA + liveness facts.** The 0-input
    1-output shape (CALLER / GAS / ADDRESS / …): no operands to discharge, a fresh output `out` (`∉ S`
    from single-definition) live in `nextLiveness`. -/
theorem regularEnvWf_of_ssa {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {S0 : List String} {k : Nat} {out : String} {inst : Instruction}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtbase : out ∉ S0)
    (houtfresh : ∀ (j : Nat) (hj : j < bb.instructions.length), j < k → out ∉ (bb.instructions.get ⟨j, hj⟩).outputs)
    (huseo : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      out ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → out ∉ (bb.instructions.get ⟨m, hm⟩).outputs)) :
    RegularEnvWf (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1))
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) out inst := by
  obtain ⟨uo, huo, huok, huophi, house, honodef⟩ := huseo
  refine ⟨hops, houts, ?_, ?_⟩
  · exact output_not_mem_stackAt S0 bb.instructions k out houtbase houtfresh
  · exact liveVarsAt_contains_of_use_later hnd hfind hlbl huo huok huophi house honodef

/-- **Gap-B capstone (memory-store class): `RegularMemStoreWf` from SSA + liveness facts.** The 2-input
    0-output memory store (MSTORE `wsz = 32` / MSTORE8 `wsz = 1`): the store WF (`regularStoreWf_of_ssa`)
    plus the per-instruction memory-coverage obligation carried as an opcode-specific hypothesis. -/
theorem regularMemStoreWf_of_ssa {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {lo : AssocList String Nat} {S0 : List String} {k : Nat} {x y : String} {inst : Instruction} {wsz : Nat}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (hdefy : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ y ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husey : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      y ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → y ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
      venomAsmRel lo p v s → lookupVar x v = some w →
      w.toNat ≤ v.memory.size ∧ ((w.toNat + wsz + 31) / 32) * 32 ≤ s.memory.size ∧
      w.toNat + wsz ≤ p.alloc.fnEom) :
    RegularMemStoreWf lo (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1))
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) x y inst wsz :=
  ⟨regularStoreWf_of_ssa hnd hfind hlbl hops houts hxy hdefx hdefy husex husey, hmemsafe⟩

/-! ### `RegularStepG` directly from analysis facts

The `*_of_ssa` WF capstones compose with the `regularStepG_*_of_wf` classifiers to give `RegularStepG`
(the classifier's actual output) directly from SSA/liveness facts — the end product a body-level
discharge feeds to `RegularBodyG_of_steps`. Two representatives below (0-output store, 1-output read);
the other classes follow identically by swapping the classifier + WF-capstone pair. -/

/-- **SSTORE `RegularStepG` from analysis facts** — `regularStepG_sstore_of_wf ∘ regularStoreWf_of_ssa`. -/
theorem regularStepG_sstore_of_ssa {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {S0 : List String} {k : Nat} {x y : String} {inst : Instruction}
    (hopc : inst.opcode = Opcode.SSTORE)
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (hdefy : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ y ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husey : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      y ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → y ∉ (bb.instructions.get ⟨m, hm⟩).outputs)) :
    RegularStepG lo (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1)) offsetToPc prog inst
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) :=
  regularStepG_sstore_of_wf hopc (regularStoreWf_of_ssa hnd hfind hlbl hops houts hxy hdefx hdefy husex husey)

/-- **TLOAD `RegularStepG` from analysis facts** — `regularStepG_tload_of_wf ∘ regularUnaryReadWf_of_ssa`. -/
theorem regularStepG_tload_of_ssa {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {fuel : Nat} {fn : IrFunction} {lbl0 : String} {bb : BasicBlock}
    {S0 : List String} {k : Nat} {x out : String} {inst : Instruction}
    (hopc : inst.opcode = Opcode.TLOAD)
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hdefx : ∃ (j : Nat) (hj : j < bb.instructions.length), j < k ∧ x ∈ (bb.instructions.get ⟨j, hj⟩).outputs)
    (houtbase : out ∉ S0)
    (houtfresh : ∀ (j : Nat) (hj : j < bb.instructions.length), j < k → out ∉ (bb.instructions.get ⟨j, hj⟩).outputs)
    (huseo : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      out ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → out ∉ (bb.instructions.get ⟨m, hm⟩).outputs))
    (husex : ∃ (j : Nat) (hj : j < bb.instructions.length), k + 1 ≤ j ∧
      (bb.instructions.get ⟨j, hj⟩).opcode ≠ Opcode.PHI ∧
      x ∈ operandVars (bb.instructions.get ⟨j, hj⟩).operands ∧
      (∀ m (hm : m < bb.instructions.length), k + 1 ≤ m → m < j → x ∉ (bb.instructions.get ⟨m, hm⟩).outputs)) :
    RegularStepG lo (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 (k + 1)) offsetToPc prog inst
      (S0 ++ (bb.instructions.take k).flatMap (·.outputs)) :=
  regularStepG_tload_of_wf hopc (regularUnaryReadWf_of_ssa hnd hfind hlbl hops houts hdefx houtbase houtfresh huseo husex)

/-- **Per-instruction `RegularStepG → BodyStepG` dispatch.** Factored out of
    `bodyStepsReadyG_regular_list` so the demand-threaded H-fold supplier can reuse the whole
    0/1-output opcode coverage (arithmetic / stores / reads / SHA3) via `bodyStepH_of_bodyStepG`. -/
theorem bodyStepG_of_regularStepG
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {inst : Instruction} {S : List String} {k : Nat}
    (hstep : RegularStepG lo nextLiveness offsetToPc prog inst S) :
    BodyStepG lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, k) S := by
  rcases hstep with hreg |
    ⟨x, y, hname, hncomm, hnjmp, hcompute, hdisp', hops, houts, hxy, hxS, hyS, hlivex, hlivey, hdisp⟩ |
    ⟨x, y, hname, hncomm, hnjmp, hcompute, hdisp', hops, houts, hxy, hxS, hyS, hlivex, hlivey⟩ |
    ⟨x, y, hname, hncomm, hnjmp, hcompute, hdisp', hops, houts, hxy, hxS, hyS, hlivex, hlivey, hmemsafe, hdisp⟩ |
    ⟨x, y, hname, hncomm, hnjmp, hcompute, hdisp', hops, houts, hxy, hxS, hyS, hlivex, hlivey, hmemsafe, hdisp⟩ |
    ⟨out, name, fV, fA, hname, hnjmp, hcompute, hops, houts, houtS, hlive, hstepEq, hdispAsm, hfield⟩ |
    ⟨x, out, name, fRead, hname, hnjmp, hcompute, hdispatch, hops, houts, hxS, houtS, hlive, hlivex, hdisp⟩ |
    ⟨x, out, hname, hnjmp, hcompute, hdispatch, hops, houts, hxS, houtS, hlive, hlivex, hdisp⟩ |
    ⟨x, out, hname, hnjmp, hcompute, hdispatch, hops, houts, hxS, houtS, hlive, hlivex, hdisp⟩ |
    ⟨x, y, out, hop, hops, houts, hxy, hxS, hyS, houtS, hlive, hlivex, hlivey, hmemsafe, hdisp⟩ |
    ⟨x, out, hname, hnjmp, hcompute, hdispatch, hops, houts, hxS, houtS, hlive, hlivex, hdisp⟩ |
    ⟨x, out, hname, hnjmp, hcompute, hdispatch, hops, houts, hxS, houtS, hlive, hlivex, hdisp⟩
  · have hsingle : ∃ o, inst.outputs = [o] := by
      obtain ⟨o, _, ho, _⟩ := hreg; exact ⟨o, ho⟩
    obtain ⟨o, ho⟩ := hsingle
    exact bodyStepG_of_bodyStep (out := o) ho (regularStep_toBodyStep hreg)
  · exact bodyStepG_sstore (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute
      hdisp' hops houts hxy hxS hyS hlivex hlivey hdisp
  · exact bodyStepG_tstore (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute
      hdisp' hops houts hxy hxS hyS hlivex hlivey
  · exact bodyStepG_mstore (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute
      hdisp' hops houts hxy hxS hyS hlivex hlivey hmemsafe hdisp
  · exact bodyStepG_mstore8 (idx := k) (nextIsTerminator := true) hname hncomm hnjmp hcompute
      hdisp' hops houts hxy hxS hyS hlivex hlivey hmemsafe hdisp
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_ctxPush0 (idx := k) hname hnjmp hcompute hops houts houtS hlive hstepEq hdispAsm hfield)
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_accountRead (idx := k) hname hnjmp hcompute hdispatch hops houts hxS houtS hlive hlivex
        hdisp (fun p => by simp [optimisticSwapPlan]))
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_tload (idx := k) hname hnjmp hcompute hdispatch hops houts hxS houtS hlive hlivex
        hdisp (fun p => by simp [optimisticSwapPlan]))
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_calldataload (idx := k) hname hnjmp hcompute hdispatch hops houts hxS houtS hlive hlivex
        hdisp (fun p => by simp [optimisticSwapPlan]))
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_sha3 (idx := k) hop hops houts hxy hxS hyS houtS hlive hlivex hlivey hmemsafe
        hdisp (fun p => by simp [optimisticSwapPlan]))
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_sload (idx := k) hname hnjmp hcompute hdispatch hops houts hxS houtS hlive hlivex
        hdisp (fun p => by simp [optimisticSwapPlan]))
  · exact bodyStepG_of_bodyStep (out := out) houts
      (bodyStep_blockhash (idx := k) hname hnjmp hcompute hdispatch hops houts hxS houtS hlive hlivex
        hdisp (fun p => by simp [optimisticSwapPlan]))

/-- **N-instruction general body-fold readiness** (mixed 0/1-output). By induction, dispatching each
    `RegularStepG` via `bodyStepG_of_regularStepG`. -/
theorem bodyStepsReadyG_regular_list
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} :
    ∀ (body : List Instruction) (S : List String) (k : Nat),
      RegularBodyG lo nextLiveness offsetToPc prog body S →
      BodyStepsReadyG lo offsetToPc prog
        (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
        (body.zipIdx k) S := by
  intro body
  induction body with
  | nil => intro S k _; exact bodyStepsReadyG_nil
  | cons inst rest ih =>
    intro S k h
    rw [List.zipIdx_cons]
    obtain ⟨hstep, htail⟩ := h
    have hoo : outsOf (inst, k) = inst.outputs := by simp [outsOf]
    refine bodyStepsReadyG_cons ?_ ?_
    · exact bodyStepG_of_regularStepG hstep
    · rw [hoo]; exact ih (S ++ inst.outputs) (k + 1) htail

/-! ### Demand-threaded H-fold supplier (adds the 0-output memory copies)

The G-fold `bodyStepsReadyG_regular_list` cannot take the 0-output multi-input copies: a copy's input
DUPs need headroom its 0 outputs don't supply. The demand-threaded H-fold (`genBlockBodyH_sim_inv`,
per-instruction demand) does. `RegularStepH` classifies each instruction at a uniform body demand `dem`
— a lifted `RegularStepG` (`outputs.length ≤ dem`) or a demand-1 copy (`1 ≤ dem`) — `RegularBodyH`
threads it, and `bodyStepsReadyH_regular_list` dispatches, relaxing every op to `dem` via
`bodyStepH_relax`. -/

/-- **Demand relaxation.** A `BodyStepH` at demand `dem1` is one at any `dem2 ≥ dem1`: the fold hands
    more headroom (`StackDiscH (j + dem2)`), which weakens to what the op needs (`StackDiscH (j + dem1)`)
    while the output headroom `StackDiscH j` is unchanged. Lets every op relax to a uniform body demand. -/
theorem bodyStepH_relax {lo offsetToPc prog gp dem1 dem2 x S}
    (hle : dem1 ≤ dem2) (h : BodyStepH lo offsetToPc prog gp dem1 x S) :
    BodyStepH lo offsetToPc prog gp dem2 x S := by
  intro p v s j hsd hsv hrel hblock
  exact h p v s j (StackDiscH.mono hsd (by omega)) hsv hrel hblock

/-- **Per-instruction general regular step for the demand-threaded H-fold**, at a uniform body demand
    `dem`. Either a 0/1-output `RegularStepG` (lifted, `outputs.length ≤ dem`) or a demand-1 memory copy
    (CALLDATACOPY / CODECOPY, `1 ≤ dem`) — the 0-output multi-input ops the G-fold cannot take. -/
def RegularStepH (lo : AssocList String Nat) (nextLiveness : List String)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (dem : Nat) (inst : Instruction) (S : List String) : Prop :=
  (RegularStepG lo nextLiveness offsetToPc prog inst S ∧ inst.outputs.length ≤ dem)
  ∨ (∃ (a b c : String),
      opcodeToEvmName inst.opcode = some "CALLDATACOPY" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c] ∧ inst.outputs = [] ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      nextLiveness.contains a = true ∧ nextLiveness.contains b = true ∧ nextLiveness.contains c = true ∧
      (∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v)) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) ∧
      1 ≤ dem)
  ∨ (∃ (a b c : String),
      opcodeToEvmName inst.opcode = some "CODECOPY" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c] ∧ inst.outputs = [] ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      nextLiveness.contains a = true ∧ nextLiveness.contains b = true ∧ nextLiveness.contains c = true ∧
      (∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v)) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) ∧
      1 ≤ dem)
  ∨ (∃ (a b c d : String),
      opcodeToEvmName inst.opcode = some "EXTCODECOPY" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c, Operand.Var d] ∧ inst.outputs = [] ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      nextLiveness.contains a = true ∧ nextLiveness.contains b = true ∧
      nextLiveness.contains c = true ∧ nextLiveness.contains d = true ∧
      (∀ (v : VenomState) wa wb wc wd, lookupVar a v = some wa → lookupVar b v = some wb →
        lookupVar c v = some wc → lookupVar d v = some wd →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wb.toNat
          ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) v.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) v)) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wb wd, venomAsmRel lo p v s →
        lookupVar b v = some wb → lookupVar d v = some wd →
        wb.toNat ≤ v.memory.size ∧ ((wb.toNat + wd.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wb.toNat + wd.toNat ≤ p.alloc.fnEom ∧ 0 < wd.toNat ∧ wd.toNat < USize.size) ∧
      2 ≤ dem)
  ∨ (∃ (a b c : String),
      opcodeToEvmName inst.opcode = some "RETURNDATACOPY" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c] ∧ inst.outputs = [] ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      nextLiveness.contains a = true ∧ nextLiveness.contains b = true ∧ nextLiveness.contains c = true ∧
      (∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.returndata.readWithPadding wb.toNat wc.toNat) v)) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) ∧
      (∀ (v : VenomState) wb wc, lookupVar b v = some wb → lookupVar c v = some wc → wb.toNat + wc.toNat ≤ v.returndata.size) ∧
      1 ≤ dem)
  ∨ (∃ (a b c : String),
      opcodeToEvmName inst.opcode = some "MCOPY" ∧ isCommutative inst.opcode = false ∧
      inst.opcode ≠ Opcode.JMP ∧ computeOperands inst = inst.operands.reverse ∧
      inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c] ∧ inst.outputs = [] ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      nextLiveness.contains a = true ∧ nextLiveness.contains b = true ∧ nextLiveness.contains c = true ∧
      (∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.memory.readWithPadding wb.toNat wc.toNat) v)) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) wb wc, venomAsmRel lo p v s → lookupVar b v = some wb → lookupVar c v = some wc →
        wb.toNat + wc.toNat ≤ p.alloc.fnEom ∧ ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size) ∧
      1 ≤ dem)
  ∨ (∃ (es : List String) (tc : bytes32) (n : Nat),
      inst.opcode = Opcode.LOG ∧ inst.operands.head! = Operand.Lit tc ∧
      computeOperands inst = es.map Operand.Var ∧ inst.outputs = [] ∧
      es.Nodup ∧ (∀ v ∈ es, v ∈ S) ∧ (∀ v ∈ es, nextLiveness.contains v = true) ∧
      es.length = n + 2 ∧ tc.toNat = n ∧ n ≤ 4 ∧
      (∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = (offset :: size :: topics).map some ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧ size.toNat < USize.size ∧
          stepInstBase inst v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) ∧
      n ≤ dem)

/-- **Straight-line body for the demand-threaded fold** at a uniform demand `dem`: each instruction a
    `RegularStepH … dem`. -/
def RegularBodyH (lo : AssocList String Nat) (nextLiveness : List String)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (dem : Nat) :
    List Instruction → List String → Prop
  | [], _ => True
  | inst :: rest, S =>
      RegularStepH lo nextLiveness offsetToPc prog dem inst S ∧
      RegularBodyH lo nextLiveness offsetToPc prog dem rest (S ++ inst.outputs)

/-- **N-instruction demand-threaded body-fold readiness** at a uniform demand. Dispatches each
    `RegularStepH`: a G-fold op via `bodyStepG_of_regularStepG` + `bodyStepH_of_bodyStepG`, a copy via
    its producer + `bodyStepH_relax`. Covers bodies mixing arithmetic/stores/reads/SHA3 with the
    0-output memory copies — feedable to `genBlockBodyH_sim_inv`. -/
theorem bodyStepsReadyH_regular_list
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat} :
    ∀ (body : List Instruction) (S : List String) (k : Nat),
      RegularBodyH lo nextLiveness offsetToPc prog dem body S →
      BodyStepsReadyH lo offsetToPc prog
        (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
        (fun _ => dem)
        (body.zipIdx k) S := by
  intro body
  induction body with
  | nil => intro S k _; exact bodyStepsReadyH_nil
  | cons inst rest ih =>
    intro S k h
    rw [List.zipIdx_cons]
    obtain ⟨hstep, htail⟩ := h
    have hoo : outsOf (inst, k) = inst.outputs := by simp [outsOf]
    refine bodyStepsReadyH_cons ?_ ?_
    · rcases hstep with ⟨hreg, hdem⟩ |
        ⟨a, b, c, hname, hncomm, hnjmp, hcompute, hops, houts, hab, hbc, hac, haS, hbS, hcS,
          hlivea, hliveb, hlivec, hstepEqFn, hmemsafe, hdem1⟩ |
        ⟨a, b, c, hname, hncomm, hnjmp, hcompute, hops, houts, hab, hbc, hac, haS, hbS, hcS,
          hlivea, hliveb, hlivec, hstepEqFn, hmemsafe, hdem1⟩ |
        ⟨a, b, c, d, hname, hncomm, hnjmp, hcompute, hops, houts, hab, hac, had, hbc, hbd, hcd,
          haS, hbS, hcS, hdS, hlivea, hliveb, hlivec, hlived, hstepEqFn, hmemsafe, hdem2⟩ |
        ⟨a, b, c, hname, hncomm, hnjmp, hcompute, hops, houts, hab, hbc, hac, haS, hbS, hcS,
          hlivea, hliveb, hlivec, hstepEqFn, hmemsafe, hnooobFn, hdem1⟩ |
        ⟨a, b, c, hname, hncomm, hnjmp, hcompute, hops, houts, hab, hbc, hac, haS, hbS, hcS,
          hlivea, hliveb, hlivec, hstepEqFn, hmemsafe, hsrcsafeFn, hdem1⟩ |
        ⟨es, tc, n, hopc, hhead, hcompute, houts, hnd, hesS, hlive, hlenes, htc, hn, hlogFn, hndem⟩
      · exact bodyStepH_of_bodyStepG (by rw [hoo]; exact hdem) (bodyStepG_of_regularStepG hreg)
      · exact bodyStepH_relax hdem1
          (bodyStepH_calldatacopy (idx := k) hname hncomm hnjmp hcompute hops houts hab hbc hac
            haS hbS hcS hlivea hliveb hlivec hstepEqFn hmemsafe)
      · exact bodyStepH_relax hdem1
          (bodyStepH_codecopy (idx := k) hname hncomm hnjmp hcompute hops houts hab hbc hac
            haS hbS hcS hlivea hliveb hlivec hstepEqFn hmemsafe)
      · exact bodyStepH_relax hdem2
          (bodyStepH_extcodecopy (idx := k) hname hncomm hnjmp hcompute hops houts hab hac had hbc hbd hcd
            haS hbS hcS hdS hlivea hliveb hlivec hlived hstepEqFn hmemsafe)
      · exact bodyStepH_relax hdem1
          (bodyStepH_returndatacopy (idx := k) hname hncomm hnjmp hcompute hops houts hab hbc hac
            haS hbS hcS hlivea hliveb hlivec hstepEqFn hmemsafe hnooobFn)
      · exact bodyStepH_relax hdem1
          (bodyStepH_mcopy (idx := k) hname hncomm hnjmp hcompute hops houts hab hbc hac
            haS hbS hcS hlivea hliveb hlivec hstepEqFn hmemsafe hsrcsafeFn)
      · exact bodyStepH_relax hndem
          (bodyStepH_log (idx := k) hopc hhead hcompute houts hnd hesS hlive hlenes htc hn hlogFn)
    · rw [hoo]; exact ih (S ++ inst.outputs) (k + 1) htail

/-! ## Discharging `htermrun` for the operand-less terminal terminators (STOP / INVALID)

The block sims take `htermrun` (the terminator's residual-budget asm run from the post-body state to
its terminal result) as a hypothesis. For the operand-less terminators — STOP (halt) and INVALID
(fault) — it is discharged directly: when the terminator's `AsmOp` sits at `pc = asm.pc + bodyLen` (the
plan position `genBlockPlan_singleBody_split` gives), the single `asmStep` there halts/faults, and the
halt/fault is absorbing (any remaining budget is ignored). -/

/-- A STOP at the current pc halts with any positive budget (`AsmHalt` is absorbing). -/
theorem runAsm_stop {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {asMid : AsmState}
    (n : Nat) (hpc : asMid.pc < prog.length)
    (hget : prog.get ⟨asMid.pc, hpc⟩ = AsmInst.AsmOp "STOP") :
    runAsm (n + 1) offsetToPc prog asMid = AsmResult.AsmHalt (asmNext asMid) := by
  unfold runAsm; rw [asmStep_stop_ok hpc hget]

/-- **Halt-arm block sim from a body run.** Composes a whole-program body run (`hbodyrun`: `bodyLen`
    steps to the post-body state `asMid`, still `venomAsmRel`-related) with a `STOP` at `asMid.pc` to
    produce exactly what `hstep_halt_block` consumes: `runAsm N … = AsmHalt (asmNext asMid)` (any budget
    `N ≥ bodyLen + 1`, via `runAsm_stop` + `runAsm_le_of_ne_ok`) together with `venomAsmTerminalRel`
    (pc-independent, from the post-body relation). The terminal-block half of (a) over the whole program
    — the plug-in the halt arm needs, from the general body-fold `genBlockBodyH_sim_inv`. -/
theorem blockSim_halt_of_body {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asm asMid : AsmState} {bodyLen N : Nat} {lo : AssocList String Nat}
    {psPostBody : PlanState} {sPostBody : VenomState}
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (hrel : venomAsmRel lo psPostBody sPostBody asMid)
    (hpc : asMid.pc < prog.length)
    (hstop : prog.get ⟨asMid.pc, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : bodyLen + 1 ≤ N) :
    runAsm N offsetToPc prog asm = AsmResult.AsmHalt (asmNext asMid) ∧
      venomAsmTerminalRel sPostBody (asmNext asMid) := by
  have hhalt : runAsm (bodyLen + 1) offsetToPc prog asm = AsmResult.AsmHalt (asmNext asMid) := by
    rw [runAsm_add_ok hbodyrun]; exact runAsm_stop 0 hpc hstop
  refine ⟨runAsm_le_of_ne_ok (by intro s h; exact AsmResult.noConfusion h) hle hhalt, ?_⟩
  exact venomAsmRel_terminal lo psPostBody sPostBody (asmNext asMid) (venomAsmRel_setPc hrel)

/-- **Discharge `htermrun` for a STOP terminator.** When the resolved program has `AsmOp "STOP"` at
    `pc = asm.pc + bodyLen` (the terminator's plan sits right after the label + body, as
    `genBlockPlan_singleBody_split` places it), the block sims' `htermrun` obligation
    (`runAsm (prog.length - bodyLen) … asMid = AsmHalt asFin`) holds with `asFin = asmNext asMid`. -/
theorem htermrun_of_stop {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (asm : AsmState) (bodyLen : Nat)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
    ∀ asMid : AsmState, asMid.pc = asm.pc + bodyLen →
      runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt (asmNext asMid) := by
  intro asMid hpc
  have hpc' : asMid.pc < prog.length := by rw [hpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hpc]; exact hget
  obtain ⟨m, hm⟩ : ∃ m, prog.length - bodyLen = m + 1 := ⟨prog.length - bodyLen - 1, by omega⟩
  rw [hm]; exact runAsm_stop m hpc' hget'

/-- An INVALID at the current pc faults with any positive budget (`AsmFault` is absorbing). -/
theorem runAsm_invalid {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {asMid : AsmState}
    (n : Nat) (hpc : asMid.pc < prog.length)
    (hget : prog.get ⟨asMid.pc, hpc⟩ = AsmInst.AsmOp "INVALID") :
    runAsm (n + 1) offsetToPc prog asMid
      = AsmResult.AsmFault { asmNext asMid with returndata := ByteArray.empty } := by
  unfold runAsm; rw [asmStep_invalid_ok hpc hget]

/-- **Discharge `htermrun` for an INVALID terminator** (the fault companion of `htermrun_of_stop`;
    feeds the `AsmFault` arm, `genBlockSimulation_body_fault`). -/
theorem htermrun_of_invalid {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (asm : AsmState) (bodyLen : Nat)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID") :
    ∀ asMid : AsmState, asMid.pc = asm.pc + bodyLen →
      runAsm (prog.length - bodyLen) offsetToPc prog asMid
        = AsmResult.AsmFault { asmNext asMid with returndata := ByteArray.empty } := by
  intro asMid hpc
  have hpc' : asMid.pc < prog.length := by rw [hpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hpc]; exact hget
  obtain ⟨m, hm⟩ : ∃ m, prog.length - bodyLen = m + 1 := ⟨prog.length - bodyLen - 1, by omega⟩
  rw [hm]; exact runAsm_invalid m hpc' hget'

/-- A RETURN at the current pc, with `off`/`sz` on top of a covered memory, halts (one step). The
    operand-terminator analog of `runAsm_stop`: unlike STOP, RETURN pops `off`/`sz` and sets
    `returndata = memory[off, off+sz)` (`asmReturnOp_ok`), so `asFin` is the popped/returndata'd state,
    not `asmNext asMid`. -/
theorem runAsm_return {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {asMid : AsmState}
    {off sz : bytes32} {rest : List bytes32}
    (n : Nat) (hpc : asMid.pc < prog.length)
    (hget : prog.get ⟨asMid.pc, hpc⟩ = AsmInst.AsmOp "RETURN")
    (hstack : asMid.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size) :
    runAsm (n + 1) offsetToPc prog asMid = AsmResult.AsmHalt ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory }) := by
  unfold runAsm; rw [asmStep_return_ok hpc hget, asmReturnOp_ok hstack hcov]

/-- A REVERT at the current pc, with `off`/`sz` on top of a covered memory, aborts (one step). The
    `AsmRevert` companion of `runAsm_return`. -/
theorem runAsm_revert {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {asMid : AsmState}
    {off sz : bytes32} {rest : List bytes32}
    (n : Nat) (hpc : asMid.pc < prog.length)
    (hget : prog.get ⟨asMid.pc, hpc⟩ = AsmInst.AsmOp "REVERT")
    (hstack : asMid.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size) :
    runAsm (n + 1) offsetToPc prog asMid = AsmResult.AsmRevert ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory }) := by
  unfold runAsm; rw [asmStep_revert_ok hpc hget, asmRevertOp_ok hstack hcov]

/-- **Discharge `htermrun` for a RETURN terminator.** The operand-terminator analog of
    `htermrun_of_stop`: the RETURN plan sits at `pc = asm.pc + bodyLen`, and the body left `off`/`sz`
    on top of a covered memory. Feeds the `AsmHalt` arm (`genBlockSimulation_body_halt`) with
    `asFin` = the popped/returndata'd `asMid` — paired with `venomAsmRel_return` for `htermrel`. -/
theorem htermrun_of_return {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (asm : AsmState) (bodyLen : Nat) {off sz : bytes32} {rest : List bytes32}
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "RETURN") :
    ∀ asMid : AsmState, asMid.pc = asm.pc + bodyLen → asMid.stack = off :: sz :: rest →
      (sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size) →
      runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory }) := by
  intro asMid hpc hstack hcov
  have hpc' : asMid.pc < prog.length := by rw [hpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "RETURN" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hpc]; exact hget
  obtain ⟨m, hm⟩ : ∃ m, prog.length - bodyLen = m + 1 := ⟨prog.length - bodyLen - 1, by omega⟩
  rw [hm]; exact runAsm_return m hpc' hget' hstack hcov

/-- **Discharge `htermrun` for a REVERT terminator** (the `AsmRevert` companion of
    `htermrun_of_return`; feeds `genBlockSimulation_body_revert`, paired with `venomAsmRel_revert`). -/
theorem htermrun_of_revert {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (asm : AsmState) (bodyLen : Nat) {off sz : bytes32} {rest : List bytes32}
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "REVERT") :
    ∀ asMid : AsmState, asMid.pc = asm.pc + bodyLen → asMid.stack = off :: sz :: rest →
      (sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size) →
      runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmRevert ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory }) := by
  intro asMid hpc hstack hcov
  have hpc' : asMid.pc < prog.length := by rw [hpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "REVERT" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hpc]; exact hget
  obtain ⟨m, hm⟩ : ∃ m, prog.length - bodyLen = m + 1 := ⟨prog.length - bodyLen - 1, by omega⟩
  rw [hm]; exact runAsm_revert m hpc' hget' hstack hcov

/-- **Non-empty-body RETURN-terminated block sim.** The operand-terminator companion of
    `genBlockSimulation_body_halt` for `RETURN`: the body runs to `asMid` (asm) / `sEnd` (Venom), the
    body having positioned the RETURN operands `off`/`sz` on top of the asm stack
    (`hstack : asMid.stack = off :: sz :: rest`) with values matching `sEnd`'s `evalOperand`
    (`hoffval`/`hszval`), and RETURN halts with `returndata = memory[off, off+sz)`. Composes
    `htermrun_of_return` (asm RETURN one step) with `venomAsmRel_return` (the returndata slice matches
    via `memoryRel`), fed to `genBlockSimulation_body_halt`. The isolated `hstack`/`hoffval`/`hszval` are
    the operand-positioning facts the 0-operand STOP block sim did not need — the terminator-input
    emission of `generateFnPlan`, to be discharged from the post-body plan stack (`planStackRel`). -/
theorem genBlockSimulation_body_return
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' ps : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (asMid : AsmState) (bodyLen : Nat)
    {offOp szOp : Operand} {off sz : bytes32} {rest : List bytes32}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (htermRETURN : term.opcode = Opcode.RETURN) (htermops : term.operands = [offOp, szOp])
    (hoffval : evalOperand offOp sEnd = some off) (hszval : evalOperand szOp sEnd = some sz)
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (hpcMid : asMid.pc = asm.pc + bodyLen)
    (hstack : asMid.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size)
    (hrelMid : venomAsmRel labelOffsets ps sEnd asMid)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlenSz : sz.toNat < USize.size)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hbodyLenLe : bodyLen ≤ prog.length) :
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
  have hstep : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) := by
    simp only [stepInstBase, htermRETURN, htermops, hoffval, hszval]
  have histerm : isTerminator term.opcode = true := by rw [htermRETURN]; decide
  refine genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    front term hd tl sEnd (haltState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) asMid
    ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory })
    bodyLen hbb hcons hphi hnonterm hthread histerm hstep hbodyrun
    (htermrun_of_return asm bodyLen hlt hget asMid hpcMid hstack hcov) hbodyLenLe
    (venomAsmRel_return hrelMid hsafe hlenSz)

/-- **Non-empty-body REVERT-terminated block sim** — the `RevertAbort` companion of
    `genBlockSimulation_body_return`. Same operand-positioning shape; composes `htermrun_of_revert`
    with `venomAsmRel_revert`, fed to `genBlockSimulation_body_revert`. -/
theorem genBlockSimulation_body_revertOp
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' ps : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (asMid : AsmState) (bodyLen : Nat)
    {offOp szOp : Operand} {off sz : bytes32} {rest : List bytes32}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (htermREVERT : term.opcode = Opcode.REVERT) (htermops : term.operands = [offOp, szOp])
    (hoffval : evalOperand offOp sEnd = some off) (hszval : evalOperand szOp sEnd = some sz)
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (hpcMid : asMid.pc = asm.pc + bodyLen)
    (hstack : asMid.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size)
    (hrelMid : venomAsmRel labelOffsets ps sEnd asMid)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlenSz : sz.toNat < USize.size)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "REVERT")
    (hbodyLenLe : bodyLen ≤ prog.length) :
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
  have hstep : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) := by
    simp only [stepInstBase, htermREVERT, htermops, hoffval, hszval]
  have histerm : isTerminator term.opcode = true := by rw [htermREVERT]; decide
  refine genBlockSimulation_body_revert (labelOffsets := labelOffsets) (ps' := ps')
    front term hd tl sEnd (revertState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) asMid
    ({ asMid with stack := rest, returndata := asMid.memory.readWithPadding off.toNat sz.toNat, memory := asMid.memory })
    bodyLen hbb hcons hphi hnonterm hthread histerm hstep hbodyrun
    (htermrun_of_revert asm bodyLen hlt hget asMid hpcMid hstack hcov) hbodyLenLe
    (venomAsmRel_revert hrelMid hsafe hlenSz)

/-- **Reading the terminator operands off a positioned plan stack.** For a plan stack of the form
    `base ++ [szOp, offOp]` (LAST = TOS, so `offOp` is on top), `stackPeek 0 = offOp` and
    `stackPeek 1 = szOp`. This discharges the RETURN/REVERT plan-stack block sim's `hpeek0`/`hpeek1`
    hypotheses once the terminator's operands are positioned on top by `generateRegularInstPlan`'s
    input emission (`emitInputPlan` + the final `reorderPlan`). -/
theorem stackPeek_top2 (base : List Operand) (szOp offOp : Operand) :
    stackPeek 0 (base ++ [szOp, offOp]) = offOp ∧ stackPeek 1 (base ++ [szOp, offOp]) = szOp := by
  refine ⟨?_, ?_⟩
  · show (base ++ [szOp, offOp])[(base ++ [szOp, offOp]).length - 1 - 0]! = offOp
    rw [getElem!_eq_getElem?_getD, List.length_append, List.getElem?_append_right (by simp)]
    simp
  · show (base ++ [szOp, offOp])[(base ++ [szOp, offOp]).length - 1 - 1]! = szOp
    rw [getElem!_eq_getElem?_getD, List.length_append, List.getElem?_append_right (by simp)]
    simp

/-- **Top-2 asm values from a plan stack whose top-2 operands are known.** From `planStackRel`
    (`venomAsmRel`'s stack component) with the two top-of-stack plan operands `offOp = stackPeek 0`,
    `szOp = stackPeek 1` evaluating (`operandVal`) to `off`/`sz`, the asm stack is `off :: sz :: rest`.
    This discharges the RETURN/REVERT block sim's operand-positioning hypothesis `hstack` from the
    post-body plan stack — the terminator reads its operands off the top of the scheduled stack. -/
theorem asmStack_top2_of_planStackRel {lo : AssocList String Nat} {vs : VenomState}
    {psStack : List Operand} {asmStack : List bytes32}
    {offOp szOp : Operand} {off sz : bytes32}
    (hrel : planStackRel lo vs psStack asmStack)
    (hlen : 2 ≤ psStack.length)
    (h0 : stackPeek 0 psStack = offOp) (h1 : stackPeek 1 psStack = szOp)
    (hoff : operandVal vs lo offOp = some off) (hsz : operandVal vs lo szOp = some sz) :
    ∃ rest, asmStack = off :: sz :: rest := by
  have hlenEq := hrel.1
  have e0 := planStackRel_peek hrel (dist := 0) (by omega)
  have e1 := planStackRel_peek hrel (dist := 1) (by omega)
  rw [h0, hoff] at e0
  rw [h1, hsz] at e1
  have hlenA : 2 ≤ asmStack.length := hlenEq ▸ hlen
  rcases asmStack with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hlenA
  · simp at hlenA
  · refine ⟨t, ?_⟩
    have ha : a = off := by simpa using e0.symm
    have hb : b = sz := by simpa using e1.symm
    rw [ha, hb]

/-- **RETURN block sim with operand-positioning discharged from the plan stack.** The plan-stack
    variant of `genBlockSimulation_body_return`: instead of assuming `asMid.stack = off :: sz :: rest`
    directly, it *derives* it from `venomAsmRel` at `asMid` together with the post-body plan stack
    having the RETURN operands as its top two entries (`stackPeek 0/1 = offOp/szOp`) —
    `asmStack_top2_of_planStackRel` turns those into the concrete asm stack shape. `hoff`/`hsz` are the
    asm-side operand values (`operandVal`), `heoff`/`hesz` the Venom-side ones (`evalOperand`) — equal
    for `Var`/`Lit` operands. This closes the RETURN operand-positioning coupling from the scheduled
    stack: the only remaining input is that the post-body plan stack has the terminator's operands on
    top, a fact of `generateFnPlan`'s terminator-input emission. -/
theorem genBlockSimulation_body_return_ps
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' ps : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (asMid : AsmState) (bodyLen : Nat)
    {offOp szOp : Operand} {off sz : bytes32}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (htermRETURN : term.opcode = Opcode.RETURN) (htermops : term.operands = [offOp, szOp])
    (heoff : evalOperand offOp sEnd = some off) (hesz : evalOperand szOp sEnd = some sz)
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (hpcMid : asMid.pc = asm.pc + bodyLen)
    (hrelMid : venomAsmRel labelOffsets ps sEnd asMid)
    (hplen : 2 ≤ ps.stack.length)
    (hpeek0 : stackPeek 0 ps.stack = offOp) (hpeek1 : stackPeek 1 ps.stack = szOp)
    (hoff : operandVal sEnd labelOffsets offOp = some off)
    (hsz : operandVal sEnd labelOffsets szOp = some sz)
    (hcovOff : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ asMid.memory.size)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlenSz : sz.toNat < USize.size)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hbodyLenLe : bodyLen ≤ prog.length) :
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
  obtain ⟨rest, hstack⟩ := asmStack_top2_of_planStackRel hrelMid.1 hplen hpeek0 hpeek1 hoff hsz
  exact genBlockSimulation_body_return front term hd tl sEnd asMid bodyLen
    hbb hcons hphi hnonterm hthread htermRETURN htermops heoff hesz hbodyrun hpcMid hstack hcovOff
    hrelMid hsafe hlenSz hlt hget hbodyLenLe

/-- **General N-instruction mixed 0/1-output regular-op body block sim (Halt terminator).** A block
    whose body is *any* straight-line list of regular ops mixing 1-output arithmetic (comm/non-comm
    binops, unops, ternops) and 0-output storage stores (SSTORE/TSTORE), followed by a halting
    terminator. The whole-length general body fold comes from `bodyStepsReadyG_regular_list`, folded by
    `genBlockPrefixBodyG_sim_inv` and glued by `genBlockSimulation_body_halt`. The first per-block
    `hsim` mixing observable-effect (0-output) and value-producing (1-output) instructions. -/
theorem genBlockSimulation_regularGN_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd sEndTerm : VenomState} {asFin : AsmState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
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
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  exact genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    body term hd tl sEnd sEndTerm asMid asFin bodyLen
    hbb hcons hphi hnonterm hthread histerm hstepterm hbrun (htermrun asMid hbpc) hlen htermrel

/-- **Invariant-threading prefix-body sim for the demand-threaded H-fold.** The `BodyStepsReadyH` twin
    of `genBlockPrefixBodyG_sim_inv`: runs the block's `SOLabel` prefix then the body via
    `genBlockBodyH_sim_inv` (headroom `Σ dem`), landing the asm at `sEnd`. -/
theorem genBlockPrefixBodyH_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hready : BodyStepsReadyH lo offsetToPc prog gp dem (front.zipIdx 0) S0)
    (hsd0 : StackDiscH ((front.zipIdx 0).map dem).sum ps0 vs0)
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
    genBlockBodyH_sim_inv gp dem (front.zipIdx 0) S0 ps0 vs0 as1 hready hsd0 hsv0 h1rel hbody'
  rw [execBodyThread_eq_gvFold front 0 vs0 sEnd hthread] at h2rel
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Halt-terminated regular block over the demand-threaded H-fold body.** The H-fold twin of
    `genBlockSimulation_regularGN_halt`: the body is a `RegularBodyH … dem` (so it may contain the
    0-output memory copies / LOG that the G-fold cannot take), fed through `bodyStepsReadyH_regular_list`
    + `genBlockPrefixBodyH_sim_inv`; the halting terminator is handled by the shared
    `genBlockSimulation_body_halt`. Discharges the per-block `hbsim` clause for a halting block of any
    modeled instructions. -/
theorem genBlockSimulation_regularHN_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel dem : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd sEndTerm : VenomState} {asFin : AsmState}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
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
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  exact genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    body term hd tl sEnd sEndTerm asMid asFin bodyLen
    hbb hcons hphi hnonterm hthread histerm hstepterm hbrun (htermrun asMid hbpc) hlen htermrel

/-- **STOP-terminated regular block, terminator side discharged internally.** Variant of
    `genBlockSimulation_regularGN_halt` specialised to a STOP terminator
    (`stepInstBase term sEnd = Halt (haltState sEnd)`). Where `_halt` takes the terminator's asm run
    (`htermrun`) and terminal relation (`htermrel`) against a *fixed* `asFin` as hypotheses, this
    variant produces the post-body asm state `asMid` internally (via `genBlockPrefixBodyG_sim_inv`) and
    fixes the terminal asm state to `asmNext asMid`: `htermrun` is discharged by `htermrun_of_stop`
    (the STOP `AsmOp` at `pc = asm.pc + bodyLen` halts), and `htermrel` by `venomAsmRel_terminal` on the
    post-body relation `hbrel` (STOP and `asmNext` preserve the observable fields, so the terminal rel
    at the halt equals it at the post-body state). Replaces the `htermrun`/`htermrel`/`asFin` triple
    with one layout fact: the STOP `AsmOp` sits at `asm.pc + bodyLen`. -/
theorem genBlockSimulation_regularGN_stop
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
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
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  refine genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    body term hd tl sEnd (haltState sEnd) asMid (asmNext asMid) bodyLen
    hbb hcons hphi hnonterm hthread histerm hstepterm hbrun
    (htermrun_of_stop asm bodyLen hlt hget asMid hbpc) (by omega) ?_
  exact venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel

/-- **STOP-terminated regular block over the demand-threaded H-fold body**, terminator discharged
    internally. The H-fold twin of `genBlockSimulation_regularGN_stop`: body a `RegularBodyH … dem`
    (copies / LOG allowed); the STOP `AsmOp` at `pc = asm.pc + bodyLen` discharges `htermrun`
    (`htermrun_of_stop`) and the terminal relation (`venomAsmRel_terminal` on the post-body relation). -/
theorem genBlockSimulation_regularHN_stop
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel dem : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
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
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  refine genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    body term hd tl sEnd (haltState sEnd) asMid (asmNext asMid) bodyLen
    hbb hcons hphi hnonterm hthread histerm hstepterm hbrun
    (htermrun_of_stop asm bodyLen hlt hget asMid hbpc) (by omega) ?_
  exact venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel

/-- **Residual-budget asm run for a var-reading regular body + STOP** — `hasm_stop` (bare STOP)
    generalized from an empty body to any `RegularBodyG` body. The body runs `bodyLen` steps to the
    post-body asm state (`genBlockPrefixBodyG_sim_inv`), the STOP one more step (`runAsm_stop`), and
    `runAsm_le_of_ne_ok` absorbs the total `bodyLen + 1` up to any larger `budget`. This is the shape
    `hfsim_jmp_then_terminal`'s `hterm` obligation needs — the block sim at the *residual* budget from
    the post-JMP mid-state — so it plugs a **non-entry var-reading block** into the CFG composition. -/
theorem hasm_regularStop
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen budget : Nat}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog asm = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState sEnd) as' := by
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hbpc]; exact hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog asm = AsmResult.AsmHalt (asmNext asMid) := by
    rw [runAsm_append_ok hbrun]; exact runAsm_stop 0 hpc' hget'
  exact ⟨asmNext asMid, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel⟩

/-- **Residual asm run for a demand-threaded H-fold body + JMP** — the JMP-continue counterpart of
    `hasm_regularStop`, and the H-fold twin (no G-fold version exists). The block's body (a
    `RegularBodyH … dem`, so copies / LOG allowed) runs `bodyLen` steps to the post-body asm state
    (`genBlockPrefixBodyH_sim_inv`), then the `push-label target ; JUMP` terminator runs two more
    (`resolved_jump_sim`) to the successor's pc `idx`, `venomAsmRel`-preserved (pc-independent). Supplies
    the asm side of the OK-continue `hbsim` clause — the `runAsm blockLen … = AsmOK asm'` that
    `hbsim_continue_clause` transitions to the successor's budget. -/
theorem hasm_regularHN_jmp
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel target : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem off idx : Nat}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asm', runAsm (bodyLen + 2) offsetToPc prog asm = AsmResult.AsmOK asm' ∧
            venomAsmRel labelOffsets ((body.zipIdx 0).foldl
              (fun acc z => (acc.1 ++
                ((fun (w : Instruction × Nat) (p : PlanState) =>
                  generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
                ((fun (w : Instruction × Nat) (p : PlanState) =>
                  generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
              ([], ps0)).2 sEnd asm' ∧
            asm'.pc = idx := by
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hpush' : prog.get ⟨asMid.pc, hpc1'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target) := by
    rw [show (⟨asMid.pc, hpc1'⟩ : Fin _) = ⟨asm.pc + bodyLen, hpc1⟩ from Fin.ext hbpc]; exact hpush
  have hpc2' : asMid.pc + 1 < prog.length := by rw [hbpc]; exact hpc2
  have hjump' : prog.get ⟨asMid.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" := by
    have e : asMid.pc + 1 = asm.pc + bodyLen + 1 := by rw [hbpc]
    conv_lhs => rw [show (⟨asMid.pc + 1, hpc2'⟩ : Fin prog.length) = ⟨asm.pc + bodyLen + 1, hpc2⟩ from Fin.ext e]
    exact hjump
  have hjrun : runAsm 2 offsetToPc prog asMid = AsmResult.AsmOK { asMid with pc := idx } :=
    resolved_jump_sim hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk
  refine ⟨{ asMid with pc := idx }, ?_, venomAsmRel_setPc hbrel, rfl⟩
  rw [runAsm_add_ok hbrun]; exact hjrun

/-- **Generic per-block simulation for a JMP-terminated block** (H-fold track) — the
non-halting, continue-arm sibling of `genBlockSimulation_regularHN_stop`. A block
`body ++ [JMP target]` with an arbitrary demand-threaded modeled body (`RegularBodyH`,
so copies/LOG allowed): the Venom side runs to `OK (jumpTo target sEnd)` (`runBlock_ok`),
and the asm side runs the body + resolved JUMP to land at the successor's code index
`idx` with `venomAsmRel` re-established there (`hasm_regularHN_jmp`; `jumpTo` only touches
control-flow fields, which `venomAsmRel` ignores, so the relation transports by defeq).
This is the per-block hstep the CFG walk consumes at a JMP edge — the missing continue
case that, with the halt/abort cases, completes the terminator dispatch. -/
theorem genBlockSimulation_regularHN_jmp
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel target : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem off idx extraFuel : Nat}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runBlock (body.length + (extraFuel + 1)) ctx bb vs = ExecResult.OK (jumpTo target sEnd) ∧
    ∃ asm', runAsm (bodyLen + 2) offsetToPc prog asm = AsmResult.AsmOK asm' ∧ asm'.pc = idx ∧
      venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
        ([], ps0)).2 (jumpTo target sEnd) asm' := by
  refine ⟨runBlock_ok ctx bb extraFuel body term hd tl vs sEnd (jumpTo target sEnd)
      hbb hcons hphi hnonterm hthread hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asm', hrun, hrel, hpc⟩ :=
    hasm_regularHN_jmp (vs := vs) (target := target) hbody hsd0 hsv0 hrel0 hthread hblock
      hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  exact ⟨asm', hrun, hpc, hrel⟩

/-- **Generic per-block JNZ-taken simulation** (H-fold track) — the conditional
continue-arm (`cond ≠ 0`): a block `body ++ [JNZ c ifNz ifZ]` whose condition var
`c` sits at the fold-output TOS, with the branch TAKEN. The Venom side runs to
`OK (jumpTo ifNz sEnd)`; the asm side runs body + `DUP1 ; push ifNz ; JUMPI` (taken)
to land at the `ifNz` code index `idx` with `venomAsmRel` re-established. Completes
the H-fold per-block terminator dispatch (halt / abort / return / JMP / JNZ). -/
theorem hasm_regularHN_jnz_taken
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel ifNz : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem off idx : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hstkF : ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd labelOffsets (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpc1 : asm.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨asm.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : asm.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨asm.pc + bodyLen + 1, hpc2⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat labelOffsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : asm.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog asm = AsmResult.AsmOK asMid ∧
            venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2 sEnd asMid ∧
            asMid.pc = idx := by
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpush' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpush
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have ejumpi : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := idx } :=
    resolved_jumpi_taken_sim (by rw [hs1]) hcond hpc2' hpush' hoff_lk hoff hpc3' hjumpi' hidx_lk
  have hfinal : ({ s1 with stack := cond :: rest, pc := idx } : AsmState)
      = { asMid with pc := idx } := by
    rw [hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idx } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejumpi
  refine ⟨{ asMid with pc := idx }, ?_, venomAsmRel_setPc hbrel, rfl⟩
  rw [show bodyLen + 3 = bodyLen + (1 + 2) from rfl, runAsm_add_ok hbrun,
      show (1 + 2 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]
  exact ejumpi

/-- **Generic per-block simulation for a JNZ-taken block** (H-fold track) — packages
`hasm_regularHN_jnz_taken` (asm) with `runBlock_ok` (Venom → `OK (jumpTo ifNz sEnd)`).
The per-block hstep the CFG walk consumes at a taken conditional edge; `jumpTo` only
touches control-flow fields, so `venomAsmRel` at the successor holds by defeq. -/
theorem genBlockSimulation_regularHN_jnz_taken
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel ifNz : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem off idx extraFuel : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
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
    (hstkF : ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd labelOffsets (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpc1 : asm.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨asm.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : asm.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨asm.pc + bodyLen + 1, hpc2⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat labelOffsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : asm.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runBlock (body.length + (extraFuel + 1)) ctx bb vs = ExecResult.OK (jumpTo ifNz sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog asm = AsmResult.AsmOK asMid ∧ asMid.pc = idx ∧
      venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2 (jumpTo ifNz sEnd) asMid := by
  refine ⟨runBlock_ok ctx bb extraFuel body term hd tl vs sEnd (jumpTo ifNz sEnd)
      hbb hcons hphi hnonterm hthread hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc⟩ :=
    hasm_regularHN_jnz_taken (vs := vs) (ifNz := ifNz) (base := base) (c := c) (cond := cond)
      hbody hsd0 hsv0 hrel0 hthread hblock hbodyLenEq hstkF hcval hcond hpc1 hdup hpc2 hpush
      hoff_lk hoff hpc3 hjumpi hidx_lk
  exact ⟨asMid, hrun, hpc, hrel⟩

/-- **Generic per-block JNZ-not-taken simulation** (H-fold track) — the conditional
fall-through arm (`cond = 0`): body + `DUP1 ; push ifNz ; JUMPI` (falls through) `;
push ifZ ; JUMP`, landing at the `ifZ` code index `idxZ` with `venomAsmRel`. The
`cond = 0` twin of `hasm_regularHN_jnz_taken`; completes the H-fold JNZ dispatch. -/
theorem hasm_regularHN_jnz_nottaken
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel ifNz ifZ : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem offNz offZ idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hstkF : ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd labelOffsets (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hpc1 : asm.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨asm.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : asm.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨asm.pc + bodyLen + 1, hpc2⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat labelOffsets ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : asm.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : asm.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨asm.pc + bodyLen + 3, hpc4⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat labelOffsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : asm.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨asm.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog asm = AsmResult.AsmOK asMid ∧
            venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2 sEnd asMid ∧
            asMid.pc = idxZ := by
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpushNz' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpushNz
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have efall : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := s1.pc + 2 } :=
    resolved_jumpi_nottaken_sim (by rw [hs1, hcond]) hpc2' hpushNz' hoffNz_lk hoffNz hpc3' hjumpi'
  set s2 := ({ s1 with stack := cond :: rest, pc := s1.pc + 2 } : AsmState) with hs2
  have hs2pc : s2.pc = asMid.pc + 3 := by rw [hs2]; show s1.pc + 2 = _; rw [hs1pc]
  have hpc4' : s2.pc < prog.length := by rw [hs2pc, hbpc]; exact hpc4
  have hpushZ' : prog.get ⟨s2.pc, hpc4'⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifZ) :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hpushZ
  have hpc5' : s2.pc + 1 < prog.length := by rw [hs2pc, hbpc]; exact hpc5
  have hjump' : prog.get ⟨s2.pc + 1, hpc5'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hjump
  have ejump : runAsm 2 offsetToPc prog s2 = AsmResult.AsmOK { s2 with pc := idxZ } :=
    resolved_jump_sim hpc4' hpushZ' hoffZ_lk hoffZ hpc5' hjump' hidxZ_lk
  have hfinal : ({ s2 with pc := idxZ } : AsmState) = { asMid with pc := idxZ } := by
    rw [hs2, hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idxZ } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejump
  refine ⟨{ asMid with pc := idxZ }, ?_, venomAsmRel_setPc hbrel, rfl⟩
  have e01 : runAsm 3 offsetToPc prog asMid = AsmResult.AsmOK s2 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]; exact efall
  have e02 : runAsm 5 offsetToPc prog asMid = AsmResult.AsmOK { asMid with pc := idxZ } := by
    rw [show (5 : Nat) = 3 + 2 from rfl, runAsm_add_ok e01]; exact ejump
  rw [runAsm_add_ok hbrun]; exact e02

/-- **Generic per-block simulation for a JNZ-not-taken block** (H-fold track) — packages
`hasm_regularHN_jnz_nottaken` (asm) with `runBlock_ok` (Venom → `OK (jumpTo ifZ sEnd)`).
The per-block hstep at a fall-through conditional edge; with the taken sibling, the
H-fold per-block terminator dispatch is complete (halt/abort/return/JMP/JNZ). -/
theorem genBlockSimulation_regularHN_jnz_nottaken
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel ifNz ifZ : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem offNz offZ idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
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
    (hstkF : ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd labelOffsets (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hpc1 : asm.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨asm.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : asm.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨asm.pc + bodyLen + 1, hpc2⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat labelOffsets ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : asm.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨asm.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : asm.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨asm.pc + bodyLen + 3, hpc4⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat labelOffsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : asm.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨asm.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    runBlock (body.length + (extraFuel + 1)) ctx bb vs = ExecResult.OK (jumpTo ifZ sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog asm = AsmResult.AsmOK asMid ∧ asMid.pc = idxZ ∧
      venomAsmRel labelOffsets ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2 (jumpTo ifZ sEnd) asMid := by
  refine ⟨runBlock_ok ctx bb extraFuel body term hd tl vs sEnd (jumpTo ifZ sEnd)
      hbb hcons hphi hnonterm hthread hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc⟩ :=
    hasm_regularHN_jnz_nottaken (vs := vs) (ifNz := ifNz) (ifZ := ifZ) (base := base) (c := c)
      (cond := cond) hbody hsd0 hsv0 hrel0 hthread hblock hbodyLenEq hstkF hcval hcond hpc1 hdup
      hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact ⟨asMid, hrun, hpc, hrel⟩

/-- **Residual asm run for a demand-threaded H-fold body + STOP** — the STOP-terminated counterpart of
    `hasm_regularHN_jmp`, and the H-fold twin of `hasm_regularStop` (the G-fold residual STOP block).
    The block's body (a `RegularBodyH … dem`, so copies / LOG allowed) runs `bodyLen` steps to the
    post-body asm state (`genBlockPrefixBodyH_sim_inv`), then the `STOP` at `pc = asm.pc + bodyLen`
    halts (`runAsm_stop`), stretched to any `budget ≥ bodyLen + 1` (`runAsm_le_of_ne_ok`), with the
    terminal relation on the post-body state. Supplies the asm side of a residual-budget STOP successor
    block — feeds `hfsim_jmp_then_halt` for a JMP-into-copy-block function. -/
theorem hasm_regularHN_stop
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem budget : Nat}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog asm = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState sEnd) as' := by
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hbpc]; exact hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog asm = AsmResult.AsmHalt (asmNext asMid) := by
    rw [runAsm_append_ok hbrun]; exact runAsm_stop 0 hpc' hget'
  exact ⟨asmNext asMid, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel⟩

/-- **Residual-budget asm run for an H-fold regular body + literal REVERT** (`PUSH sz ; PUSH off ;
    REVERT`, the canonical compiled `revert(0,0)`-shape block, `sz = 0`). The `AsmRevert` companion
    of `hasm_regularHN_stop`: the body folds to `asMid`, the two pushes place `off :: sz` on top,
    `REVERT` reverts with `returndata = memory[off, off+sz)` (empty at `sz = 0`), absorbed into any
    sufficient budget. The terminal relation is built from the post-body `venomAsmRel` fields (the
    pushes touch only stack/pc). -/
theorem hasm_regularHN_revert_lit
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen dem budget : Nat}
    {b1 b2 : List byte} {off sz : bytes32}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).map (fun _ => dem)).sum ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hsafe : off.toNat + sz.toNat ≤ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).2.alloc.fnEom)
    (hlt1 : asm.pc + bodyLen < prog.length)
    (hget1 : prog.get ⟨asm.pc + bodyLen, hlt1⟩ = AsmInst.AsmPush b1)
    (hlt2 : asm.pc + bodyLen + 1 < prog.length)
    (hget2 : prog.get ⟨asm.pc + bodyLen + 1, hlt2⟩ = AsmInst.AsmPush b2)
    (hlt3 : asm.pc + bodyLen + 2 < prog.length)
    (hget3 : prog.get ⟨asm.pc + bodyLen + 2, hlt3⟩ = AsmInst.AsmOp "REVERT")
    (hv1 : wordOfBytes (List.toByteArray (List.replicate (32 - b1.length) (0 : byte) ++ b1)) = sz)
    (hv2 : wordOfBytes (List.toByteArray (List.replicate (32 - b2.length) (0 : byte) ++ b2)) = off)
    (hsz0 : sz.toNat = 0)
    (hbudget : bodyLen + 3 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog asm = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel
             (revertState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) as' := by
  have hlen : sz.toNat < USize.size := by rw [hsz0]; exact USize.size_pos
  have hready := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyH_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => dem)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  -- the three-instruction tail from asMid
  set s2 : AsmState := { asmNext asMid with stack := sz :: asMid.stack } with hs2
  set s3 : AsmState := { asmNext s2 with stack := off :: s2.stack } with hs3
  have p2 : s2.pc = asm.pc + bodyLen + 1 := by rw [hs2]; show asMid.pc + 1 = _; rw [hbpc]
  have p3 : s3.pc = asm.pc + bodyLen + 2 := by rw [hs3]; show s2.pc + 1 = _; rw [p2]
  have hb1 : asMid.pc < prog.length := by rw [hbpc]; exact hlt1
  have hb2 : s2.pc < prog.length := by rw [p2]; exact hlt2
  have hb3 : s3.pc < prog.length := by rw [p3]; exact hlt3
  have g1 : prog.get ⟨asMid.pc, hb1⟩ = AsmInst.AsmPush b1 := prog_get_transfer hbpc hget1
  have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmPush b2 := prog_get_transfer p2 hget2
  have g3 : prog.get ⟨s3.pc, hb3⟩ = AsmInst.AsmOp "REVERT" := prog_get_transfer p3 hget3
  have e1 : asmStep offsetToPc prog asMid = AsmResult.AsmOK s2 := by
    rw [asmStep_push_ok hb1 g1, hv1]; rfl
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK s3 := by
    rw [asmStep_push_ok hb2 g2, hv2]; rfl
  have hstack3 : s3.stack = off :: sz :: asMid.stack := by rw [hs3, hs2]
  have hcompose : runAsm (bodyLen + 3) offsetToPc prog asm
      = AsmResult.AsmRevert ({ s3 with
                                 stack := asMid.stack,
                                 returndata := s3.memory.readWithPadding off.toNat sz.toNat,
                                 memory := s3.memory }) := by
    rw [runAsm_append_ok hbrun, show (3 : Nat) = 1+1+1 from rfl,
        runAsm_succ_ok hb1 e1, runAsm_succ_ok hb2 e2]
    exact runAsm_revert 0 hb3 g3 hstack3 (Or.inl hsz0)
  obtain ⟨_, _, hMem, hAcc, hTrans, _, hLog, _, _, _, _, _⟩ := hbrel
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ⟨hAcc, hTrans, ?_, hLog⟩⟩
  show s3.memory.readWithPadding off.toNat sz.toNat = readMemory off.toNat sz.toNat sEnd
  unfold readMemory
  exact (memoryRel_readWithPadding_slice hMem hsafe hlen).symm

/-- **Spill-aware block-prefix fold** (`JUMPDEST` + padded varying-growth body): the HSVP twin of
    `genBlockPrefixBodyH_sim_inv`. The gains-carrying list `lg` projects to the block's indexed
    body (`hfront`), so the Venom side is the plain `execBodyThread`; the conclusion additionally
    re-establishes `StackDiscHS P` and the grown `StackPerm` at the fold output — the spill-aware
    facts a successor block (or terminator segment) consumes. -/
theorem genBlockPrefixBodyHSVP_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (lg : List ((Instruction × Nat) × List String))
    (front : List Instruction) (S0 : List String) (M0 : AssocList Operand Nat)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1))) :
    ∃ as', runAsm (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
              (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd as' ∧
           as'.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length ∧
           StackDiscHS P (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd as' ∧
           StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
             (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  rw [executePlan_append] at hblock
  obtain ⟨hpre, hbody⟩ := asmBlockAt_append hblock
  obtain ⟨as1, h1run, h1rel, h1pc⟩ := soLabel_sim lo ps0 vs0 as0 prog l hrel0 hpre
  have hsd1 : StackDiscHS (totalGain lg + P) ps0 vs0 as1 :=
    hsd0.rebuild (runAsm_memory_size_mono h1run) (fun _ _ h => h) hsd0.shallow hsd0.defined
  have hbody' : asmBlockAt prog as1.pc
      (executePlan (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1) := by
    rw [h1pc]; exact hbody
  obtain ⟨as', h2run, h2rel, h2pc, h2sd, h2sv⟩ :=
    genBlockBody_sim_inv_HSVP P gp lg S0 M0 ps0 vs0 as1 hready hsd1 hsv0 hspM h1rel hbody'
  have hveq : lg.foldl (fun v x => gvBodyStep x.1 v) vs0 = sEnd := by
    have h1 : lg.foldl (fun v x => gvBodyStep x.1 v) vs0
        = (lg.map Prod.fst).foldl (fun v x => gvBodyStep x v) vs0 := by
      rw [List.foldl_map]
    rw [h1, hfront]
    exact execBodyThread_eq_gvFold front 0 vs0 sEnd hthread
  rw [hveq] at h2rel h2sd
  obtain ⟨hrun, hrel, hpc⟩ := plan_seq_sim' h1run h1pc h2run h2rel h2pc
  exact ⟨as', hrun, hrel, hpc, h2sd, h2sv⟩


/-- **Spill-aware entry segment** (HSVP prefix + resolved `push-label ; JUMP`): the HSVP twin of
    `hasm_regularHN_jmp`, generic in the plan generator. Runs to the successor's pc with the
    relation AND the spill-aware invariants re-established at the fold output — choosing the
    padding `P := ` (successor's fuel) threads the invariant straight into the next block. -/
theorem hasm_regularHSVP_jmp {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (bodyLen + 2) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      asMid.pc = idx ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
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

/-- **Spill-aware generic per-block JMP simulation** (HSVP track) — the spilling
counterpart of `genBlockSimulation_regularHN_jmp`. For a block `front ++ [JMP target]`
with an HSVP (spill-threaded) body, the Venom side runs to `OK (jumpTo target sEnd)`
(`runBlock_ok`), and the asm side runs body + resolved JUMP to land at the successor's
code index `idx` with the full successor-entry package re-established: `venomAsmRel`,
`StackDiscHS P` (the spill-aware depth invariant), and `StackPerm` (the grown live-var
shape) — exactly the `Entry`-invariant components the generic CFG walk threads across a
JMP edge (`jumpTo` touches only control-flow fields, which all three ignore, so they
transport by defeq). The reusable spill-aware per-block hstep for the generic-hbsim
Step 2. -/
theorem genBlockSimulation_regularHSVP_jmp
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat} (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
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
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
        (jumpTo target sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2
        (jumpTo target sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo target sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jmp (vs0 := vs0) (target := target) P hfront hready hsd0 hsv0 hspM hrel0
      hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩

/-- **Spill-aware JNZ-taken entry segment** (HSVP prefix + `DUP1 ; push-label ifNz ; JUMPI`): the
    conditional-branch twin of `hasm_regularHSVP_jmp`, for a condition variable sitting at the top
    of the fold output stack (the common shape: the body's last instruction computed it). The DUP'd
    condition is consumed by the taken `JUMPI`, restoring the fold-exit asm stack — so the relation
    AND spill-aware invariants land at the branch target exactly as at a JMP successor. -/
theorem hasm_regularHSVP_jnz_taken {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l ifNz : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    -- the condition: a var at the fold-output TOS, non-zero
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    -- the resolved conditional tail
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      asMid.pc = idx ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  -- DUP1
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  -- push-label ifNz ; JUMPI, taken
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpush' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpush
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have ejumpi : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := idx } :=
    resolved_jumpi_taken_sim (by rw [hs1]) hcond hpc2' hpush' hoff_lk hoff hpc3' hjumpi' hidx_lk
  -- the taken JUMPI restores the fold-exit stack: the final state is asMid at the target pc
  have hfinal : ({ s1 with stack := cond :: rest, pc := idx } : AsmState)
      = { asMid with pc := idx } := by
    rw [hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idx } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejumpi
  refine ⟨{ asMid with pc := idx }, ?_, venomAsmRel_setPc hbrel, rfl,
    hbsd.rebuild (Nat.le_refl _) (fun _ _ h => h) hbsd.shallow hbsd.defined, hbsv⟩
  rw [show bodyLen + 3 = bodyLen + (1 + 2) from rfl, runAsm_add_ok hbrun,
      show (1 + 2 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]
  exact ejumpi

/-- **Spill-aware JNZ-not-taken entry segment** (HSVP prefix +
    `DUP1 ; push-label ifNz ; JUMPI ; push-label ifZ ; JUMP`): the zero-condition twin of
    `hasm_regularHSVP_jnz_taken`. The `JUMPI` falls through (consuming the DUP'd zero and the
    pushed `ifNz` destination, restoring the fold-exit asm stack) and the trailing
    `push-label ifZ ; JUMP` lands at the `ifZ` target with the invariants intact. -/
theorem hasm_regularHSVP_jnz_nottaken {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l ifNz ifZ : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {bodyLen offNz offZ idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    -- the condition: a var at the fold-output TOS, zero
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    -- the resolved conditional tail
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as0.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as0.pc + bodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as0.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      asMid.pc = idxZ ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 sEnd asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  obtain ⟨rest, hrest⟩ : ∃ rest, asMid.stack = cond :: rest :=
    ⟨asMid.stack.drop 1, venomAsmRel_asmStack_top1_var hbrel hstkF hcval⟩
  -- DUP1
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hdup' : prog.get ⟨asMid.pc, hpc1'⟩ = AsmInst.AsmOp "DUP1" := prog_get_transfer hbpc hdup
  have hlen0 : 0 < asMid.stack.length := by rw [hrest]; simp
  have hget0 : asMid.stack.get ⟨0, hlen0⟩ = cond := by simp [hrest]
  have e0 : asmStep offsetToPc prog asMid
      = AsmResult.AsmOK ({ asmNext asMid with stack := cond :: cond :: rest }) := by
    rw [asmStep_dup_ok (n := 1) hpc1' (by rw [hdup']; rfl) (by norm_num) (by norm_num)]
    show asmDup 0 asMid = _
    unfold asmDup
    rw [dif_pos hlen0, hget0, hrest]
  set s1 := ({ asmNext asMid with stack := cond :: cond :: rest } : AsmState) with hs1
  have hs1pc : s1.pc = asMid.pc + 1 := rfl
  -- push-label ifNz ; JUMPI, NOT taken (condition zero)
  have hpc2' : s1.pc < prog.length := by rw [hs1pc, hbpc]; exact hpc2
  have hpushNz' : prog.get ⟨s1.pc, hpc2'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz) :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hpushNz
  have hpc3' : s1.pc + 1 < prog.length := by rw [hs1pc, hbpc]; exact hpc3
  have hjumpi' : prog.get ⟨s1.pc + 1, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hs1pc, hbpc]) hjumpi
  have efall : runAsm 2 offsetToPc prog s1
      = AsmResult.AsmOK { s1 with stack := cond :: rest, pc := s1.pc + 2 } :=
    resolved_jumpi_nottaken_sim (by rw [hs1, hcond]) hpc2' hpushNz' hoffNz_lk hoffNz
      hpc3' hjumpi'
  set s2 := ({ s1 with stack := cond :: rest, pc := s1.pc + 2 } : AsmState) with hs2
  have hs2pc : s2.pc = asMid.pc + 3 := by rw [hs2]; show s1.pc + 2 = _; rw [hs1pc]
  -- push-label ifZ ; JUMP
  have hpc4' : s2.pc < prog.length := by rw [hs2pc, hbpc]; exact hpc4
  have hpushZ' : prog.get ⟨s2.pc, hpc4'⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ) :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hpushZ
  have hpc5' : s2.pc + 1 < prog.length := by rw [hs2pc, hbpc]; exact hpc5
  have hjump' : prog.get ⟨s2.pc + 1, hpc5'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hs2pc, hbpc]) hjump
  have ejump : runAsm 2 offsetToPc prog s2 = AsmResult.AsmOK { s2 with pc := idxZ } :=
    resolved_jump_sim hpc4' hpushZ' hoffZ_lk hoffZ hpc5' hjump' hidxZ_lk
  -- the fall-through restored the fold-exit stack: the final state is asMid at the ifZ target
  have hfinal : ({ s2 with pc := idxZ } : AsmState) = { asMid with pc := idxZ } := by
    rw [hs2, hs1]
    show ({ asmNext asMid with stack := cond :: rest, pc := idxZ } : AsmState) = _
    rw [← hrest]
    rfl
  rw [hfinal] at ejump
  refine ⟨{ asMid with pc := idxZ }, ?_, venomAsmRel_setPc hbrel, rfl,
    hbsd.rebuild (Nat.le_refl _) (fun _ _ h => h) hbsd.shallow hbsd.defined, hbsv⟩
  have e01 : runAsm 3 offsetToPc prog asMid = AsmResult.AsmOK s2 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, runAsm_succ_ok hpc1' e0]
    exact efall
  have e02 : runAsm 5 offsetToPc prog asMid = AsmResult.AsmOK { asMid with pc := idxZ } := by
    rw [show (5 : Nat) = 3 + 2 from rfl, runAsm_add_ok e01]
    exact ejump
  rw [runAsm_add_ok hbrun]
  exact e02

/-- **Spill-aware generic per-block JNZ-taken simulation** (HSVP track) — the spilling
counterpart of `genBlockSimulation_regularHN_jnz_taken`. Packages
`hasm_regularHSVP_jnz_taken` (asm) with `runBlock_ok` (Venom → `OK (jumpTo ifNz sEnd)`),
re-establishing the successor-entry triple `venomAsmRel + StackDiscHS + StackPerm` across
the taken conditional edge. The spill-aware per-block hstep the generic walk threads. -/
theorem genBlockSimulation_regularHSVP_jnz_taken
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    {ifNz : String} {off idx : Nat}
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo ifNz sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 3) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧ asMid.pc = idx ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 (jumpTo ifNz sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 (jumpTo ifNz sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo ifNz sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jnz_taken (vs0 := vs0) (ifNz := ifNz) (base := base) (c := c) (cond := cond)
      P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hstkF hcval hcond hpc1 hdup
      hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩

/-- **Spill-aware generic per-block JNZ-not-taken simulation** (HSVP track) — the
`cond = 0` fall-through twin: packages `hasm_regularHSVP_jnz_nottaken` with `runBlock_ok`
(Venom → `OK (jumpTo ifZ sEnd)`). With the taken sibling, the HSVP JNZ per-block dispatch
is complete. -/
theorem genBlockSimulation_regularHSVP_jnz_nottaken
    {ctx : VenomContext} {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel : Nat}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    {ifNz ifZ : String} {offNz offZ idxZ : Nat}
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hdup : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as0.pc + bodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as0.pc + bodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as0.pc + bodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as0.pc + bodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as0.pc + bodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ) :
    runBlock (front.length + (extraFuel + 1)) ctx bb vs0 = ExecResult.OK (jumpTo ifZ sEnd) ∧
    ∃ asMid, runAsm (bodyLen + 5) offsetToPc prog as0 = AsmResult.AsmOK asMid ∧ asMid.pc = idxZ ∧
      venomAsmRel lo (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 (jumpTo ifZ sEnd) asMid ∧
      StackDiscHS P (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 (jumpTo ifZ sEnd) asMid ∧
      StackPerm (S0 ++ lg.flatMap (fun e => e.2)) (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  refine ⟨runBlock_ok ctx bb extraFuel front term hd tl vs0 sEnd (jumpTo ifZ sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step histerm hnohalt, ?_⟩
  obtain ⟨asMid, hrun, hrel, hpc, hsd, hsv⟩ :=
    hasm_regularHSVP_jnz_nottaken (vs0 := vs0) (ifNz := ifNz) (ifZ := ifZ) (base := base) (c := c)
      (cond := cond) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hstkF hcval
      hcond hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5
      hjump hidxZ_lk
  exact ⟨asMid, hrun, hpc, hrel, ⟨hsd.spillWf, hsd.shallow, hsd.defined⟩, hsv⟩

/-- **Spill-aware residual STOP segment**: the HSVP twin of `hasm_regularHN_stop`, generic in the
    plan generator. -/
theorem hasm_regularHSVP_stop {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState sEnd) as' := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, _, _⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := prog_get_transfer hbpc hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog as0 = AsmResult.AsmHalt (asmNext asMid) := by
    rw [runAsm_append_ok hbrun]; exact runAsm_stop 0 hpc' hget'
  exact ⟨asmNext asMid, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         venomAsmRel_terminal lo _ sEnd asMid hbrel⟩

/-- **Spill-aware residual INVALID segment**: the HSVP fault twin of `hasm_regularHSVP_stop`,
    generic in the plan generator. Both sides clear returndata on the fault (Venom via
    `setReturndata empty`, asm via the `AsmFault { … with returndata := empty }` witness), so
    the terminal relation is unconditional (`empty = empty`). Supplies the `AsmFault` asm side of
    `hstep_regularHSVP_invalid`. -/
theorem hasm_regularHSVP_invalid {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel (haltState (setReturndata ByteArray.empty sEnd)) as' := by
  obtain ⟨asMid, hbrun, hbrel, hbpc, _, _⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
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

set_option maxHeartbeats 3200000 in
/-- **Spill-aware residual CALL+STOP segment** — the asm side of a halting block whose body ends
    in an external CALL: label + prefix HSVP fold, then the full generated CALL plan
    (`genRegularInstPlan_call_sim` at the fold output, entry budget `totalGain lg + 7` covering
    the 7-DUP peak), then `STOP` halts with the writeback state related terminally. The concrete
    `hasm` feed for `hterm_halt_extcall` (with the block's `front2 = []`). -/
theorem hasm_regularHSVP_call_stop {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    {bodyLen callLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP 7 lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + 7) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    -- the CALL instruction at the fold output
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hovarsS : ∀ v ∈ ovars, v ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.spilled = M1)
    (hovM : ∀ v ∈ ovars, alookup' M1 (Operand.Var v) = none)
    (heval : evalOperands inst.operands sEnd = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal sEnd lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ sEnd.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hfnEom0 : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom ≤ as0.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack)
    (houtov : out ∉ ovars)
    (hspill_outM : AssocList.lookup Operand Nat M1 (Operand.Var out) = none)
    (hspillRegM : ∀ op off, AssocList.lookup Operand Nat M1 op = some off →
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], ps0)).2.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel sEnd.accounts sEnd.callCtx.contract sEnd.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (sEnd.memory.readWithPadding aOff.toNat aSz.toNat).toList sEnd.txCtx.gasprice 0
      (!sEnd.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }))
    -- layout
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
            curBbLabel (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
              ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hcallLenEq : callLen = (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
        nextLiveness false nextIsTerminator curBbLabel (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + callLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + callLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : bodyLen + callLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel
             (haltState { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with
               instIdx := front.length + 1 }) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbcall⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv 7 l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have hmono1 : as0.memory.size ≤ asMid.memory.size := runAsm_memory_size_mono hbrun
  -- the CALL producer sim at the fold output
  have hbound : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length + ovars.length ≤ 17 := by
    have h1 := hbsd.shallow
    have h2 : ovars.length = 7 := by
      have ha : ovars.length = vals.length := by
        have := congrArg List.length hvals; simpa [List.length_map] using this
      have hb : vals.length = 7 := by
        have := congrArg List.length hvalrev; simpa using this
      omega
    omega
  have hmemes : ∀ v ∈ ovars, Operand.Var v ∈ (lg.foldl
      (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack :=
    fun v hv => stackPerm_mem hbsv (hovarsS v hv)
  obtain ⟨dists, hdepths⟩ := emitDepthsOk_of_bounds ovars _ hbound hnd hmemes hliveall
  have hnospillF : ∀ v ∈ ovars, alookup' (lg.foldl
      (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      (Operand.Var v) = none := by
    intro v hv
    rw [hspMF]
    exact hovM v hv
  have hspill_outF : AssocList.lookup Operand Nat (lg.foldl
      (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      (Operand.Var out) = none := by
    rw [hspMF]; exact hspill_outM
  have hspillRegF : ∀ op off, AssocList.lookup Operand Nat (lg.foldl
      (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled op
      = some off →
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom ≤ off := by
    intro op off hlook
    rw [hspMF] at hlook
    exact hspillRegM op off hlook
  have hbcall' : asmBlockAt prog asMid.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel (lg.foldl
          (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbcall
  obtain ⟨asCall, hcrun, hstepV, hcrel, hcpc⟩ :=
    genRegularInstPlan_call_sim (offsetToPc := offsetToPc) hopc hcompute houts rfl hnd hnospillF
      hdepths hlive heval hvals hvalrev hargs haszlt hro1 hretbelow
      (le_trans hfnEom0 hmono1) hfreshS houtov hspill_outF hspillRegF hcall hoptnoop hbrel hbcall'
  rw [← hcallLenEq] at hcrun hcpc
  -- STOP
  have hpc' : asCall.pc < prog.length := by rw [hcpc, hbpc]; omega
  have hget' : prog.get ⟨asCall.pc, hpc'⟩ = AsmInst.AsmOp "STOP" := by
    refine prog_get_transfer ?_ hget
    rw [hcpc, hbpc]
  have hcompose : runAsm (bodyLen + (callLen + 1)) offsetToPc prog as0
      = AsmResult.AsmHalt (asmNext asCall) := by
    rw [runAsm_append_ok hbrun, runAsm_append_ok hcrun]
    exact runAsm_stop 0 hpc' hget'
  have hrelIdx : venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
      false nextIsTerminator curBbLabel (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2
      { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with
        instIdx := front.length + 1 } asCall := hcrel
  refine ⟨asmNext asCall,
    runAsm_le_of_ne_ok (fun s => by simp) (by omega : bodyLen + (callLen + 1) ≤ budget) hcompose,
    venomAsmRel_terminal lo _ _ asCall hrelIdx⟩

set_option maxHeartbeats 1600000 in
/-- **Spill-aware residual CALL+RETURN segment** — the most common contract tail: label +
    prefix HSVP fold, the full generated CALL plan (named `(cops, cps)` to keep the statement
    tractable), then the two RETURN operands DUP'd from the post-call stack and `RETURN`
    halting with `returndata = memory[woff, woff+wsz)` at the writeback state. The RETURN
    sibling of `hasm_regularHSVP_call_stop`, grafting `hasm_regularHSVP_return_var`'s tail
    onto the CALL step atom (`stackDiscHS_call_step` at `k := 0` supplies the post-call
    shallow bound). -/
theorem hasm_regularHSVP_call_return_var {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    {bodyLen callLen emitLen budget : Nat}
    {offv szv : String} {woff wsz : bytes32} {opc2 : Opcode}
    {cops : List StackOp} {cps : PlanState}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP 7 lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + 7) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    -- the CALL instruction at the fold output
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hovarsS : ∀ v ∈ ovars, v ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.spilled = M1)
    (hovM : ∀ v ∈ ovars, alookup' M1 (Operand.Var v) = none)
    (heval : evalOperands inst.operands sEnd = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal sEnd lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ sEnd.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hfnEom0 : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom ≤ as0.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack)
    (houtov : out ∉ ovars)
    (hspill_outM : AssocList.lookup Operand Nat M1 (Operand.Var out) = none)
    (hspillRegM : ∀ op off, AssocList.lookup Operand Nat M1 op = some off →
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], ps0)).2.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel sEnd.accounts sEnd.callCtx.contract sEnd.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (sEnd.memory.readWithPadding aOff.toNat aSz.toNat).toList sEnd.txCtx.gasprice 0
      (!sEnd.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }))
    -- the CALL plan named
    (hcplan : generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 = (cops, cps))
    -- the RETURN operands at the post-call plan state / writeback
    (hoffCP : Operand.Var offv ∈ cps.stack)
    (hszCP : Operand.Var szv ∈ cps.stack)
    (hoffMC : alookup' cps.spilled (Operand.Var offv) = none)
    (hszMC : alookup' cps.spilled (Operand.Var szv) = none)
    (hliveoff : nextLiveness.contains offv = true) (hliveszv : nextLiveness.contains szv = true)
    (hvoffW : lookupVar offv (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) = some woff)
    (hvszW : lookupVar szv (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafeR : woff.toNat + wsz.toNat ≤ cps.alloc.fnEom)
    (hlenR : wsz.toNat < USize.size)
    -- layout
    (hblock : asmBlockAt prog as0.pc
      (executePlan ((([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1) ++ cops)
        ++ (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hcallLenEq : callLen = (executePlan cops).length)
    (hemitLenEq : emitLen = (executePlan
        (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1).length)
    (hlt : as0.pc + bodyLen + callLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + callLen + emitLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hbudget : bodyLen + callLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel
             (haltState (setReturndata (readMemory woff.toNat wsz.toNat
               { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 })
               { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 })) as' := by
  rw [executePlan_append, executePlan_append] at hblock
  obtain ⟨hbCallSeg, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨hbpre, hbcall⟩ := asmBlockAt_append hbCallSeg
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv 7 l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have hmono1 : as0.memory.size ≤ asMid.memory.size := runAsm_memory_size_mono hbrun
  have hmemesC : ∀ v ∈ ovars, Operand.Var v ∈ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack :=
    fun v hv => stackPerm_mem hbsv (hovarsS v hv)
  have hnospillF : ∀ v ∈ ovars, alookup' (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled (Operand.Var v) = none := by
    intro v hv
    rw [hspMF]
    exact hovM v hv
  have hspill_outF : AssocList.lookup Operand Nat (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled (Operand.Var out) = none := by
    rw [hspMF]; exact hspill_outM
  have hspillRegF : ∀ op off, AssocList.lookup Operand Nat (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled op = some off →
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom ≤ off := by
    intro op off hlook
    rw [hspMF] at hlook
    exact hspillRegM op off hlook
  have hbcall' : asmBlockAt prog asMid.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hcplan, hbpc, hbodyLenEq]; exact hbcall
  obtain ⟨asCall, hcrun, hstepV, hcrel, hcpc, hcsd⟩ :=
    stackDiscHS_call_step (k := 0) (offsetToPc := offsetToPc)
      (by simpa using hbsd) hopc hcompute houts hnd hmemesC hnospillF hliveall hlive heval hvals
      hvalrev hargs haszlt hro1 hretbelow (le_trans hfnEom0 hmono1) hfreshS houtov hspill_outF
      hspillRegF hcall hoptnoop hbrel hbcall'
  rw [hcplan] at hcrun hcrel hcpc hcsd
  rw [← hcallLenEq] at hcrun hcpc
  have hmono2 : asMid.memory.size ≤ asCall.memory.size := runAsm_memory_size_mono hcrun
  -- RETURN operand depths at the post-call plan state
  have hshallowC : cps.stack.length ≤ 15 := by
    have := hcsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallowC hoffCP hszCP
  have hbemit' : asmBlockAt prog asCall.pc
      (executePlan (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1) := by
    rw [List.length_append] at hbemit
    rw [hcpc, hbpc, hbodyLenEq, hcallLenEq,
        show as0.pc + (executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length
            + (executePlan cops).length
          = as0.pc + ((executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length
            + (executePlan cops).length) from by omega]
    exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hszMC hliveszv hdepth_y hsmall_y
      hleny hoffMC hliveoff hdepth_x' hsmall_x' hlenx' hcrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- operand values at the writeback, on the asm top
  have hemitstack : (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness
      cps).2.stack = cps.stack ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hszMC hliveszv hdepth_y hsmall_y hoffMC hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoffW hvszW
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hcpc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "RETURN" :=
    prog_get_transfer (by rw [hepc, hcpc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact le_trans hmono1 hmono2
  have hcompose : runAsm (bodyLen + callLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmHalt ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + callLen + emitLen + 1 = bodyLen + (callLen + (emitLen + 1)) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok hcrun, runAsm_add_ok herun]
    exact runAsm_return 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc2
      [Operand.Var szv, Operand.Var offv] nextLiveness cps).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hszMC hliveszv hdepth_y hsmall_y hoffMC hliveoff
      hdepth_x' hsmall_x']
    exact hsafeR
  have herel' : venomAsmRel lo (emitInputPlan opc2
      [Operand.Var szv, Operand.Var offv] nextLiveness cps).2
      { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 } asMid2 := herel
  exact venomAsmRel_return (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel' hsafe' hlenR

set_option maxHeartbeats 1600000 in
/-- **Spill-aware residual CALL+REVERT segment** — the revert-bubbling tail: label + prefix
    HSVP fold, the full generated CALL plan (named `(cops, cps)`), then the two REVERT operands
    DUP'd from the post-call stack and `REVERT` aborting with
    `returndata = memory[woff, woff+wsz)` at the writeback state. The `AsmRevert` twin of
    `hasm_regularHSVP_call_return_var`; feeds `hterm_revert_extcall`. -/
theorem hasm_regularHSVP_call_revert_var {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    {bodyLen callLen emitLen budget : Nat}
    {offv szv : String} {woff wsz : bytes32} {opc2 : Opcode}
    {cops : List StackOp} {cps : PlanState}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP 7 lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + 7) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    -- the CALL instruction at the fold output
    (hopc : inst.opcode = Opcode.CALL)
    (hcompute : computeOperands inst = ovars.map Operand.Var)
    (houts : inst.outputs = [out])
    (hnd : ovars.Nodup)
    (hovarsS : ∀ v ∈ ovars, v ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hliveall : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hlive : nextLiveness.contains out = true)
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.spilled = M1)
    (hovM : ∀ v ∈ ovars, alookup' M1 (Operand.Var v) = none)
    (heval : evalOperands inst.operands sEnd = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvals : List.map (operandVal sEnd lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrev : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargs : aOff.toNat + aSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (haszlt : aSz.toNat < USize.size)
    (hro1 : rOff.toNat ≤ sEnd.memory.size)
    (hretbelow : rOff.toNat + rSz.toNat ≤ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hfnEom0 : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom ≤ as0.memory.size)
    (hfreshS : ¬ Operand.Var out ∈ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack)
    (houtov : out ∉ ovars)
    (hspill_outM : AssocList.lookup Operand Nat M1 (Operand.Var out) = none)
    (hspillRegM : ∀ op off, AssocList.lookup Operand Nat M1 op = some off →
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
          ([], ps0)).2.alloc.fnEom ≤ off)
    (hcall : evmCall subEvmFuel sEnd.accounts sEnd.callCtx.contract sEnd.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (sEnd.memory.readWithPadding aOff.toNat aSz.toNat).toList sEnd.txCtx.gasprice 0
      (!sEnd.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode (computeOperands inst) nextLiveness (lg.foldl
            (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2 with
          stack := (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], ps0)).2.stack ++ [Operand.Var out] }))
    -- the CALL plan named
    (hcplan : generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2 = (cops, cps))
    -- the RETURN operands at the post-call plan state / writeback
    (hoffCP : Operand.Var offv ∈ cps.stack)
    (hszCP : Operand.Var szv ∈ cps.stack)
    (hoffMC : alookup' cps.spilled (Operand.Var offv) = none)
    (hszMC : alookup' cps.spilled (Operand.Var szv) = none)
    (hliveoff : nextLiveness.contains offv = true) (hliveszv : nextLiveness.contains szv = true)
    (hvoffW : lookupVar offv (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) = some woff)
    (hvszW : lookupVar szv (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafeR : woff.toNat + wsz.toNat ≤ cps.alloc.fnEom)
    (hlenR : wsz.toNat < USize.size)
    -- layout
    (hblock : asmBlockAt prog as0.pc
      (executePlan ((([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1) ++ cops)
        ++ (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hcallLenEq : callLen = (executePlan cops).length)
    (hemitLenEq : emitLen = (executePlan
        (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1).length)
    (hlt : as0.pc + bodyLen + callLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + callLen + emitLen, hlt⟩ = AsmInst.AsmOp "REVERT")
    (hbudget : bodyLen + callLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel
             (revertState (setReturndata (readMemory woff.toNat wsz.toNat
               { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 })
               { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 })) as' := by
  rw [executePlan_append, executePlan_append] at hblock
  obtain ⟨hbCallSeg, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨hbpre, hbcall⟩ := asmBlockAt_append hbCallSeg
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv 7 l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have hmono1 : as0.memory.size ≤ asMid.memory.size := runAsm_memory_size_mono hbrun
  have hmemesC : ∀ v ∈ ovars, Operand.Var v ∈ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack :=
    fun v hv => stackPerm_mem hbsv (hovarsS v hv)
  have hnospillF : ∀ v ∈ ovars, alookup' (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled (Operand.Var v) = none := by
    intro v hv
    rw [hspMF]
    exact hovM v hv
  have hspill_outF : AssocList.lookup Operand Nat (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled (Operand.Var out) = none := by
    rw [hspMF]; exact hspill_outM
  have hspillRegF : ∀ op off, AssocList.lookup Operand Nat (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled op = some off →
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom ≤ off := by
    intro op off hlook
    rw [hspMF] at hlook
    exact hspillRegM op off hlook
  have hbcall' : asmBlockAt prog asMid.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hcplan, hbpc, hbodyLenEq]; exact hbcall
  obtain ⟨asCall, hcrun, hstepV, hcrel, hcpc, hcsd⟩ :=
    stackDiscHS_call_step (k := 0) (offsetToPc := offsetToPc)
      (by simpa using hbsd) hopc hcompute houts hnd hmemesC hnospillF hliveall hlive heval hvals
      hvalrev hargs haszlt hro1 hretbelow (le_trans hfnEom0 hmono1) hfreshS houtov hspill_outF
      hspillRegF hcall hoptnoop hbrel hbcall'
  rw [hcplan] at hcrun hcrel hcpc hcsd
  rw [← hcallLenEq] at hcrun hcpc
  have hmono2 : asMid.memory.size ≤ asCall.memory.size := runAsm_memory_size_mono hcrun
  -- RETURN operand depths at the post-call plan state
  have hshallowC : cps.stack.length ≤ 15 := by
    have := hcsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallowC hoffCP hszCP
  have hbemit' : asmBlockAt prog asCall.pc
      (executePlan (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1) := by
    rw [List.length_append] at hbemit
    rw [hcpc, hbpc, hbodyLenEq, hcallLenEq,
        show as0.pc + (executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length
            + (executePlan cops).length
          = as0.pc + ((executePlan ([StackOp.SOLabel l] ++ (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length
            + (executePlan cops).length) from by omega]
    exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hszMC hliveszv hdepth_y hsmall_y
      hleny hoffMC hliveoff hdepth_x' hsmall_x' hlenx' hcrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- operand values at the writeback, on the asm top
  have hemitstack : (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness
      cps).2.stack = cps.stack ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hszMC hliveszv hdepth_y hsmall_y hoffMC hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoffW hvszW
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hcpc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "REVERT" :=
    prog_get_transfer (by rw [hepc, hcpc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact le_trans hmono1 hmono2
  have hcompose : runAsm (bodyLen + callLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmRevert ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + callLen + emitLen + 1 = bodyLen + (callLen + (emitLen + 1)) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok hcrun, runAsm_add_ok herun]
    exact runAsm_revert 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc2
      [Operand.Var szv, Operand.Var offv] nextLiveness cps).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hszMC hliveszv hdepth_y hsmall_y hoffMC hliveoff
      hdepth_x' hsmall_x']
    exact hsafeR
  have herel' : venomAsmRel lo (emitInputPlan opc2
      [Operand.Var szv, Operand.Var offv] nextLiveness cps).2
      { (callWriteback out rOff.toNat rSz.toNat success newAccs ret sEnd) with instIdx := front.length + 1 } asMid2 := herel
  exact venomAsmRel_revert (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel' hsafe' hlenR

/-- **Spill-aware residual RETURN segment with VAR operands** — the operand-positioned terminator
    tail: after the HSVP body, the two live return operands are DUP'd from the (possibly spilled)
    plan stack (`emitInputPlan_pair_var_sim`), land as values on the asm top
    (`venomAsmRel_asmStack_top2_var`), and `RETURN` halts with
    `returndata = memory[woff, woff+wsz)`; the memory coverage is checked at the ENTRY state and
    lifted across the whole run by `runAsm_memory_size_mono`. Fills the residual noted at
    `genBlockSimulation_body_return` (terminator-input emission from the post-body plan stack). -/
theorem hasm_regularHSVP_return_var {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    -- the return operands: live members of the grown shape, unspilled in the exit map
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    -- memory facts, checked at the entry state / the fold output
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    -- layout
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
    (hbudget : bodyLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel
             (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  -- operand membership + depths at the fold output
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  -- run the operand emission
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- the operand values on the asm top
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  -- RETURN halts; coverage lifted from the entry state across the whole run
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "RETURN" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact runAsm_memory_size_mono hbrun
  have hcompose : runAsm (bodyLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmHalt ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + emitLen + 1 = bodyLen + (emitLen + 1) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok herun]
    exact runAsm_return 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  exact venomAsmRel_return (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel hsafe' hlen

/-- **Spill-aware residual REVERT segment with VAR operands** — the `AsmRevert` twin of
    `hasm_regularHSVP_return_var` (operand-positioned revert of computed data, not just the
    literal `revert(0,0)` shape). -/
theorem hasm_regularHSVP_revert_var {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    -- the return operands: live members of the grown shape, unspilled in the exit map
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    -- memory facts, checked at the entry state / the fold output
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    -- layout
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
    (hbudget : bodyLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel
             (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  -- operand membership + depths at the fold output
  have hoffmem := stackPerm_mem hbsv hoffS
  have hszmem := stackPerm_mem hbsv hszS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d_y, d_x', hdepth_y, hsmall_y, hleny, hdepth_x', hsmall_x', hlenx'⟩ :=
    binopVar_depths_of_shallow (x := offv) (y := szv) hshallow hoffmem hszmem
  have hnospill_sz := alookup_of_spilled_eq hspMF hszM
  have hnospill_off := alookup_of_spilled_eq hspMF hoffM
  -- run the operand emission
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc, hemem⟩ :=
    emitInputPlan_pair_var_sim (offsetToPc := offsetToPc) hnospill_sz hliveszv hdepth_y hsmall_y
      hleny hnospill_off hliveoff hdepth_x' hsmall_x' hlenx' hbrel hbemit'
  rw [← hemitLenEq] at herun hepc
  -- the operand values on the asm top
  have hemitstack : (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var szv, Operand.Var offv] := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
  have htop : asMid2.stack = woff :: wsz :: asMid2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_var herel hemitstack hvoff hvsz
  -- RETURN halts; coverage lifted from the entry state across the whole run
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "REVERT" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asMid2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans h ?_)
      rw [hemem]
      exact runAsm_memory_size_mono hbrun
  have hcompose : runAsm (bodyLen + emitLen + 1) offsetToPc prog as0
      = AsmResult.AsmRevert ({ asMid2 with
                               stack := asMid2.stack.drop 2,
                               returndata := asMid2.memory.readWithPadding woff.toNat wsz.toNat,
                               memory := asMid2.memory }) := by
    rw [show bodyLen + emitLen + 1 = bodyLen + (emitLen + 1) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok herun]
    exact runAsm_revert 0 hpc' hget' htop hcov
  refine ⟨_, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, ?_⟩
  have hsafe' : woff.toNat + wsz.toNat ≤ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.alloc.fnEom := by
    rw [emitInputPlan_pair_var_eq hnospill_sz hliveszv hdepth_y hsmall_y hnospill_off hliveoff
      hdepth_x' hsmall_x']
    exact hsafe
  exact venomAsmRel_revert (off := woff) (sz := wsz) (rest := asMid2.stack.drop 2)
    herel hsafe' hlen

/-- **Residual-budget asm run for a var-reading regular body + INVALID** — the fault companion of
    `hasm_regularStop`. Same structure with `runAsm_invalid` (fault, `AsmFault` is absorbing under
    `runAsm_le_of_ne_ok`); the terminal relation is at `haltState (setReturndata empty sEnd)` (INVALID
    clears returndata). Both sides clear returndata (Venom via `setReturndata empty`, asm via the
    `AsmFault { … with returndata := empty }` witness), so the terminal match is unconditional
    (`empty = empty`). Supplies the `AsmFault` `hterm` of `hfsim_jmp_then_fault` for a non-entry
    var-reading INVALID block. -/
theorem hasm_regularInvalid
    {vs : VenomState} {asm : AsmState} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState} {bodyLen budget : Nat}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
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
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hbudget : bodyLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog asm = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel (haltState (setReturndata ByteArray.empty sEnd)) as' := by
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc' : asMid.pc < prog.length := by rw [hbpc]; exact hlt
  have hget' : prog.get ⟨asMid.pc, hpc'⟩ = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨asMid.pc, hpc'⟩ : Fin _) = ⟨asm.pc + bodyLen, hlt⟩ from Fin.ext hbpc]; exact hget
  have hcompose : runAsm (bodyLen + 1) offsetToPc prog asm
      = AsmResult.AsmFault { asmNext asMid with returndata := ByteArray.empty } := by
    rw [runAsm_append_ok hbrun]; exact runAsm_invalid 0 hpc' hget'
  obtain ⟨hacc, htr, _, hlog⟩ := venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel
  exact ⟨{ asmNext asMid with returndata := ByteArray.empty },
         runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose,
         ⟨hacc, htr, rfl, hlog⟩⟩

/-- **INVALID-terminated regular block, terminator side discharged internally.** The fault companion
    of `genBlockSimulation_regularGN_stop`, for a terminator whose Venom step is
    `Abort ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd))` (INVALID / faulting opcodes).
    Same internal-`asMid` structure: `htermrun` via `htermrun_of_invalid` (the INVALID `AsmOp` faults),
    and `htermrel` via `venomAsmRel_terminal` on the post-body relation. Unlike STOP, the Venom fault
    *clears returndata* — and so does the asm `INVALID` (the `AsmFault { … with returndata := empty }`
    witness), so the terminal returndata match is unconditional (`empty = empty`, no `hrdEmpty`). -/
theorem genBlockSimulation_regularGN_invalid
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S0)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ((body.zipIdx 0).flatMap outsOf).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)).length)
    (hlt : asm.pc + bodyLen < prog.length)
    (hget : prog.get ⟨asm.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID") :
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
  have hready := bodyStepsReadyG_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (lo := labelOffsets) (offsetToPc := offsetToPc) (prog := prog)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) body S0 0 hbody
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBodyG_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      body S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  refine genBlockSimulation_body_fault (labelOffsets := labelOffsets) (ps' := ps')
    body term hd tl sEnd (haltState (setReturndata ByteArray.empty sEnd)) asMid
    { asmNext asMid with returndata := ByteArray.empty } bodyLen
    hbb hcons hphi hnonterm hthread histerm hstepterm hbrun
    (htermrun_of_invalid asm bodyLen hlt hget asMid hbpc) (by omega) ?_
  obtain ⟨hacc, htr, _, hlog⟩ := venomAsmRel_terminal labelOffsets _ sEnd asMid hbrel
  exact ⟨hacc, htr, rfl, hlog⟩

/-! ## Discharging the state invariants for an entry block

The block-sim lemmas above take the state-relation invariants `hsd0` (`StackDiscH`), `hsv0`
(`StackIsVars`), `hrel0` (`venomAsmRel`) as hypotheses. For a function-**entry** block starting from
the canonical initial config — plan state `initPlanState fnEom` (empty stack, no spills), empty tracked
stack `S0 = []`, and the canonical asm image `asmOfVenom vs` (empty stack, `pc = 0`, shared state
copied) — all three are *derivable*, so an entry block's per-block `hsim` needs none of them. What
remains of the invariant layer is only the headroom bound `hk : … ≤ 15`; the block-structure and
program-layout facts (`hblock`/`htermrun`) are inherently about the concrete compiled program. -/

/-- Canonical asm image of a Venom state: empty stack, `pc = 0`, all shared state/environment copied.
    The named form of the state `initial_state_bridge` constructs. -/
def asmOfVenom (vs : VenomState) : AsmState :=
  { stack := [], memory := vs.memory, accounts := vs.accounts, transient := vs.transient,
    returndata := vs.returndata, logs := vs.logs, pc := 0, callCtx := vs.callCtx,
    txCtx := vs.txCtx, blockCtx := vs.blockCtx, code := vs.code, prevHashes := vs.prevHashes }

@[simp] theorem asmOfVenom_pc (vs : VenomState) : (asmOfVenom vs).pc = 0 := rfl

/-- **`venomAsmRel` for the canonical initial config** (`initPlanState` ↔ `asmOfVenom`). The named
    reusable form of `initial_state_bridge`'s relation proof: empty plan/asm stack (`planStackRel`),
    no spills (`planSpillRel` vacuous), equal memory outside the empty spill region (`memoryRel`), and
    all shared fields copied. Discharges the `hrel0` invariant for an entry block. -/
theorem venomAsmRel_asmOfVenom {vs : VenomState} {labelOffsets : AssocList String Nat} {fnEom : Nat} :
    venomAsmRel labelOffsets (initPlanState fnEom) vs (asmOfVenom vs) := by
  unfold venomAsmRel initPlanState asmOfVenom
  refine ⟨⟨rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro op off h; rw [AssocList.lookup] at h; simp at h
  · unfold memoryRel initSpillAlloc; intro i _; rfl

/-- **`StackIsVars` for the empty entry stack.** Discharges `hsv0` for an entry block (`S0 = []`). -/
theorem stackIsVars_initPlanState {fnEom : Nat} : StackIsVars [] (initPlanState fnEom) := by
  simp [StackIsVars, initPlanState]

/-- **`StackDiscH` for the initial plan state.** Empty stack ⇒ no spills, `defined` vacuous, and the
    headroom `k` alone must fit under 15. Discharges `hsd0` for an entry block. -/
theorem stackDiscH_initPlanState {k fnEom : Nat} {vs : VenomState} (h : k ≤ 15) :
    StackDiscH k (initPlanState fnEom) vs where
  noSpill := by intro op; rfl
  shallow := by simp [initPlanState]; omega
  defined := by intro z hz; simp [initPlanState] at hz

/-- **Entry-block instance with the state invariants discharged.** For a function-entry block starting
    from the canonical initial config (`ps0 = initPlanState fnEom`, empty tracked stack, asm state
    `asmOfVenom`), the three state-relation invariants `hsd0`/`hsv0`/`hrel0` of
    `genBlockSimulation_regularGN_halt` are discharged internally (`stackDiscH_initPlanState` /
    `stackIsVars_initPlanState` / `venomAsmRel_asmOfVenom`) — only the headroom bound `hk ≤ 15` remains
    of the invariant layer. What is left are the block-structure facts (`hbb`/`hcons`/…) and the
    program-layout facts (`hblock`/`htermrun`, inherently about the concrete compiled program). -/
theorem genBlockSimulation_regularGN_entry_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness : List String}
    {sEnd sEndTerm : VenomState} {asFin : AsmState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body [])
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hk : ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog (asmOfVenom { vs with instIdx := 0 }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)).length)
    (hlen : bodyLen ≤ prog.length)
    (htermrun : ∀ asMid : AsmState, asMid.pc = (asmOfVenom { vs with instIdx := 0 }).pc + bodyLen →
        runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt asFin)
    (htermrel : venomAsmTerminalRel sEndTerm asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_halt (ps' := ps') (ps0 := initPlanState fnEom) (S0 := [])
    (asm := asmOfVenom { vs with instIdx := 0 })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_initPlanState hk) stackIsVars_initPlanState venomAsmRel_asmOfVenom
    hthread hstepterm hblock bodyLen hbodyLenEq hlen htermrun htermrel

/-- **Entry STOP-block, all invariants discharged.** The STOP companion of
    `genBlockSimulation_regularGN_entry_halt`: `genBlockSimulation_regularGN_stop` from the canonical
    entry config (`ps0 = initPlanState fnEom`, `S0 = []`, asm `asmOfVenom`) — the three state invariants
    via the `initPlanState` lemmas, and the terminator side (STOP) internally. Only the headroom `hk`,
    the block layout `hblock`, and the STOP `AsmOp` position `hget` remain — no `htermrun`/`htermrel`. -/
theorem genBlockSimulation_regularGN_stop_entry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness : List String} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body [])
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hk : ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog (asmOfVenom { vs with instIdx := 0 }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)).length)
    (hlt : (asmOfVenom { vs with instIdx := 0 }).pc + bodyLen < prog.length)
    (hget : prog.get ⟨(asmOfVenom { vs with instIdx := 0 }).pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_stop (ps' := ps') (ps0 := initPlanState fnEom) (S0 := [])
    (asm := asmOfVenom { vs with instIdx := 0 })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_initPlanState hk) stackIsVars_initPlanState venomAsmRel_asmOfVenom
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-- **Entry STOP-block over the demand-threaded H-fold body, all invariants discharged.** The H-fold
    twin of `genBlockSimulation_regularGN_stop_entry`: `genBlockSimulation_regularHN_stop` from the
    canonical entry config (`ps0 = initPlanState fnEom`, `S0 = []`, asm `asmOfVenom`) — the three state
    invariants via the `initPlanState` lemmas, the STOP terminator internally. Only the headroom `hk`
    (now `Σ dem ≤ 15`), the block layout `hblock`, and the STOP position `hget` remain. Discharges the
    per-block `hbsim` for a single-block function whose body may contain copies / LOG. -/
theorem genBlockSimulation_regularHN_stop_entry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom dem : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness : List String} {sEnd : VenomState}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body [])
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hk : ((body.zipIdx 0).map (fun _ => dem)).sum ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog (asmOfVenom { vs with instIdx := 0 }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)).length)
    (hlt : (asmOfVenom { vs with instIdx := 0 }).pc + bodyLen < prog.length)
    (hget : prog.get ⟨(asmOfVenom { vs with instIdx := 0 }).pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularHN_stop (ps' := ps') (ps0 := initPlanState fnEom) (S0 := []) (dem := dem)
    (asm := asmOfVenom { vs with instIdx := 0 })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_initPlanState hk) stackIsVars_initPlanState venomAsmRel_asmOfVenom
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-- **Entry INVALID-block, all invariants discharged.** The fault companion of
    `genBlockSimulation_regularGN_stop_entry` (via `genBlockSimulation_regularGN_invalid`); the
    terminal returndata match is unconditional (both sides clear returndata on the fault). -/
theorem genBlockSimulation_regularGN_invalid_entry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness : List String} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body [])
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hk : ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hblock : asmBlockAt prog (asmOfVenom { vs with instIdx := 0 }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], initPlanState fnEom)).1)).length)
    (hlt : (asmOfVenom { vs with instIdx := 0 }).pc + bodyLen < prog.length)
    (hget : prog.get ⟨(asmOfVenom { vs with instIdx := 0 }).pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            (asmOfVenom { vs with instIdx := 0 }) = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_invalid (ps' := ps') (ps0 := initPlanState fnEom) (S0 := [])
    (asm := asmOfVenom { vs with instIdx := 0 })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_initPlanState hk) stackIsVars_initPlanState venomAsmRel_asmOfVenom
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-! ## Discharging the state invariants for a live-var stack (general block entry)

The entry discharge above fixes the plan stack to empty (`S0 = []`), so it only applies to a block with
an empty body. Real blocks reached mid-CFG start with live vars on the stack (`S0 ≠ []`) — a JMP
predecessor leaves the reconciled values there. This generalises the discharge to any such config: for a
plan stack of live vars `S.map Var` (all defined in `vs`) and the canonical asm stack `asmStackOf`
holding their values, the three state invariants hold. The key piece is `planStackRel_asmStackOf` — a
plan stack whose operands all have defined values relates to the asm stack of those values. -/

/-- Canonical asm stack for a plan stack of operands: each operand's value (HD = TOS). -/
def asmStackOf (vs : VenomState) (lo : AssocList String Nat) (psStack : List Operand) : List bytes32 :=
  psStack.reverse.map (fun op => (operandVal vs lo op).getD default)

/-- **`planStackRel` for the canonical asm stack.** If every plan-stack operand has a defined value,
    the plan stack relates to the asm stack of those values (`asmStackOf`). -/
theorem planStackRel_asmStackOf {lo : AssocList String Nat} {vs : VenomState} (psStack : List Operand)
    (hdef : ∀ op ∈ psStack, ∃ w, operandVal vs lo op = some w) :
    planStackRel lo vs psStack (asmStackOf vs lo psStack) := by
  refine ⟨by simp [asmStackOf], ?_⟩
  intro i hi
  have hi' : i < psStack.reverse.length := by rw [List.length_reverse]; exact hi
  have hmem : psStack.reverse[i]! ∈ psStack := by
    rw [← List.mem_reverse, getElem!_pos psStack.reverse i hi']
    exact List.getElem_mem hi'
  obtain ⟨w, hw⟩ := hdef _ hmem
  have hget : (asmStackOf vs lo psStack)[i]! = (operandVal vs lo (psStack.reverse[i]!)).getD default := by
    simp only [asmStackOf]
    rw [getElem!_pos _ i (by rw [List.length_map, List.length_reverse]; exact hi),
        getElem!_pos psStack.reverse i hi', List.getElem_map]
  rw [hget, hw, Option.getD_some]

/-- **`venomAsmRel` for a live-var plan stack.** Given a Venom state whose vars `S` are all defined,
    the plan state `initPlanState` with stack `S.map Var` relates to the canonical asm state whose
    stack holds those vars' values (the general block-entry config: live vars on the stack). Discharges
    `hrel0` for any block whose entry plan stack is `S.map Var` — not only the empty entry (`S = []`). -/
theorem venomAsmRel_varStack {vs : VenomState} {lo : AssocList String Nat} {fnEom : Nat}
    {S : List String} (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w) :
    venomAsmRel lo { initPlanState fnEom with stack := S.map Operand.Var } vs
      { asmOfVenom vs with stack := asmStackOf vs lo (S.map Operand.Var) } := by
  refine ⟨planStackRel_asmStackOf _ ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro op hop
    simp only [List.mem_map] at hop
    obtain ⟨z, hz, rfl⟩ := hop
    obtain ⟨w, hw⟩ := hdef z hz
    exact ⟨w, hw⟩
  · intro op off h; simp only [initPlanState] at h; simp [AssocList.lookup] at h
  · simp only [initPlanState, memoryRel, initSpillAlloc, asmOfVenom]; intro i _; trivial

/-- **`StackIsVars` for the live-var plan stack** (holds by construction). -/
theorem stackIsVars_varStack {fnEom : Nat} {S : List String} :
    StackIsVars S { initPlanState fnEom with stack := S.map Operand.Var } := rfl

/-- **`StackDiscH` for the live-var plan stack.** No spills, `S.length + k ≤ 15`, and every stack var
    defined in `vs`. -/
theorem stackDiscH_varStack {k fnEom : Nat} {vs : VenomState} {S : List String}
    (hlen : S.length + k ≤ 15) (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w) :
    StackDiscH k { initPlanState fnEom with stack := S.map Operand.Var } vs where
  noSpill := by intro op; rfl
  shallow := by simpa using hlen
  defined := by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨z', hz', heq⟩ := hz
    obtain ⟨w, hw⟩ := hdef z' hz'
    rw [Operand.Var.injEq] at heq; subst heq
    exact ⟨w, hw⟩

/-! ### Spill-aware entry discharges

At a function entry (or a JMP-predecessor live-var config) there are NO spills yet, so the
spill-aware invariant is free: `spillWf` is vacuous and `StackDiscHS` reduces to the already
dischargeable `StackDiscH`. These discharge the HSV/HSVP fold and chain entry hypotheses
(`hsd0`/`hsv0`/`hspM`, with the entry map `M0 = []`) — the allocator's stack-bound obligation at
entry is exactly the arithmetic side condition `… ≤ 15`. -/

/-- Spill-aware invariant at the canonical entry config, any headroom `k ≤ 15` (in particular
    `totalGain l + P` for a padded fold over the entry block). -/
theorem stackDiscHS_initPlanState {k fnEom : Nat} {vs : VenomState} {as : AsmState} (h : k ≤ 15) :
    StackDiscHS k (initPlanState fnEom) vs as :=
  StackDiscHS.of_stackDiscH (stackDiscH_initPlanState h)

/-- Spill-aware invariant at the live-var entry config (the JMP-predecessor shape). -/
theorem stackDiscHS_varStack {k fnEom : Nat} {vs : VenomState} {as : AsmState} {S : List String}
    (hlen : S.length + k ≤ 15) (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w) :
    StackDiscHS k { initPlanState fnEom with stack := S.map Operand.Var } vs as :=
  StackDiscHS.of_stackDiscH (stackDiscH_varStack hlen hdef)

/-- The entry configs carry the empty exact spilled map (`M0 = []` for the HSV/HSVP threading). -/
theorem initPlanState_spilled (fnEom : Nat) :
    (initPlanState fnEom).spilled = ([] : AssocList Operand Nat) := rfl

theorem varStack_spilled (fnEom : Nat) (S : List String) :
    ({ initPlanState fnEom with stack := S.map Operand.Var } : PlanState).spilled
      = ([] : AssocList Operand Nat) := rfl

/-- `StackPerm` at the entry configs (the HSV/HSVP folds thread `StackPerm`, not the exact-order
    `StackIsVars`). -/
theorem stackPerm_initPlanState (fnEom : Nat) : StackPerm [] (initPlanState fnEom) :=
  stackIsVars_perm rfl

theorem stackPerm_varStack (fnEom : Nat) (S : List String) :
    StackPerm S { initPlanState fnEom with stack := S.map Operand.Var } :=
  stackIsVars_perm stackIsVars_varStack

/-- **Live-var-stack block instance with the state invariants discharged.** For a block whose entry
    plan stack is the live vars `S` (all defined in `vs`) — the config a JMP predecessor leaves on the
    stack — the three state-relation invariants `hsd0`/`hsv0`/`hrel0` of
    `genBlockSimulation_regularGN_halt` are discharged internally via the `*_varStack` lemmas, starting
    from the canonical asm state (var values on the stack). Only the headroom bound
    (`S.length + … ≤ 15`), the var-definedness `hdef`, and the program-layout facts remain. Generalises
    `genBlockSimulation_regularGN_entry_halt` from `S = []` to any live-var stack. -/
theorem genBlockSimulation_regularGN_varentry_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S : List String}
    {sEnd sEndTerm : VenomState} {asFin : AsmState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w)
    (hlenS : S.length + ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)).length)
    (hlen : bodyLen ≤ prog.length)
    (htermrun : ∀ asMid : AsmState,
        asMid.pc = ({ asmOfVenom { vs with instIdx := 0 } with
            stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen →
        runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt asFin)
    (htermrel : venomAsmTerminalRel sEndTerm asFin) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_halt (ps' := ps')
    (ps0 := { initPlanState fnEom with stack := S.map Operand.Var })
    (asm := { asmOfVenom { vs with instIdx := 0 } with
              stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_varStack hlenS hdef) stackIsVars_varStack (venomAsmRel_varStack hdef)
    hthread hstepterm hblock bodyLen hbodyLenEq hlen htermrun htermrel

/-- **Live-var-stack STOP-block, all invariants discharged.** The STOP companion of
    `genBlockSimulation_regularGN_varentry_halt`; generalises `genBlockSimulation_regularGN_stop_entry`
    from `S = []` to any live-var entry stack `S` (all defined in `vs`) via the `*_varStack` lemmas. -/
theorem genBlockSimulation_regularGN_stop_varentry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S : List String} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w)
    (hlenS : S.length + ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)).length)
    (hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen
          < prog.length)
    (hget : prog.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen,
          hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_stop (ps' := ps')
    (ps0 := { initPlanState fnEom with stack := S.map Operand.Var })
    (asm := { asmOfVenom { vs with instIdx := 0 } with
              stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_varStack hlenS hdef) stackIsVars_varStack (venomAsmRel_varStack hdef)
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-- **Live-var-stack INVALID-block, all invariants discharged.** The fault companion of
    `genBlockSimulation_regularGN_stop_varentry` (via `genBlockSimulation_regularGN_invalid`); the
    terminal returndata match is unconditional (both sides clear returndata on the fault). -/
theorem genBlockSimulation_regularGN_invalid_varentry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S : List String} {sEnd : VenomState}
    (hbody : RegularBodyG labelOffsets nextLiveness offsetToPc prog body S)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w)
    (hlenS : S.length + ((body.zipIdx 0).flatMap outsOf).length ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hblock : asmBlockAt prog
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)).length)
    (hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen
          < prog.length)
    (hget : prog.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen,
          hlt⟩ = AsmInst.AsmOp "INVALID") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularGN_invalid (ps' := ps')
    (ps0 := { initPlanState fnEom with stack := S.map Operand.Var })
    (asm := { asmOfVenom { vs with instIdx := 0 } with
              stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_varStack hlenS hdef) stackIsVars_varStack (venomAsmRel_varStack hdef)
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-- **Live-var-stack STOP-block over the demand-threaded H-fold body, all invariants discharged.**
    The H-fold twin of `genBlockSimulation_regularGN_stop_varentry`: body a `RegularBodyH … dem`
    (copies / LOG allowed), entry plan stack the live vars `S` (all defined in `vs` — the config a JMP
    predecessor leaves on the stack). The three state invariants `hsd0`/`hsv0`/`hrel0` of
    `genBlockSimulation_regularHN_stop` are discharged internally via the `*_varStack` lemmas, with the
    headroom now `S.length + Σ dem ≤ 15`. Only that headroom, the var-definedness `hdef`, the block
    layout `hblock`, and the STOP position `hget` remain — discharging the per-block `hbsim` for a
    live-var-entry copy/LOG block that STOPs. -/
theorem genBlockSimulation_regularHN_stop_varentry
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel fnEom dem : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {body : List Instruction} {term hd : Instruction} {tl : List Instruction}
    {l curBbLabel : String} {nextLiveness S : List String} {sEnd : VenomState}
    (hbody : RegularBodyH labelOffsets nextLiveness offsetToPc prog dem body S)
    (hbb : bb.instructions = body ++ [term])
    (hcons : body ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ body, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hdef : ∀ z ∈ S, ∃ w, lookupVar z vs = some w)
    (hlenS : S.length + ((body.zipIdx 0).map (fun _ => dem)).sum ≤ 15)
    (hthread : execBodyThread body 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hblock : asmBlockAt prog
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((body.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], { initPlanState fnEom with stack := S.map Operand.Var })).1)).length)
    (hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen
          < prog.length)
    (hget : prog.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) }).pc + bodyLen,
          hlt⟩ = AsmInst.AsmOp "STOP") :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) :=
  genBlockSimulation_regularHN_stop (ps' := ps') (dem := dem)
    (ps0 := { initPlanState fnEom with stack := S.map Operand.Var })
    (asm := { asmOfVenom { vs with instIdx := 0 } with
              stack := asmStackOf { vs with instIdx := 0 } labelOffsets (S.map Operand.Var) })
    hbody hbb hcons hphi hnonterm histerm
    (stackDiscH_varStack hlenS hdef) stackIsVars_varStack (venomAsmRel_varStack hdef)
    hthread hstepterm hblock bodyLen hbodyLenEq hlt hget

/-! ## Discharging `hblock` from the plan structure (`asmResolve` layout)

The block sims take `hblock` (the resolved whole-function program contains the block's plan at its
entry pc) as a hypothesis. For a non-control-flow block whose plan emits no label/offset pushes
(arithmetic + stores + STOP/RETURN/REVERT/INVALID — the class the general body fold covers),
`asmResolve` is the identity (`asmResolve_executePlan_id`), so the resolved program *is*
`executePlan` of the plan; and when the whole-function plan decomposes as `pre ++ blockOps ++ post`
(the block generated after the earlier blocks), `executePlan` distributes over the concatenation and
the block sits at `pc = (executePlan pre).length` — `asmBlockAt_middle`. This reduces `hblock` to the
plan decomposition + label-freeness, both derivable from the concrete codegen output. -/

/-- **A plan is a block at pc 0 of itself ++ anything** (`asmBlockAt (insts ++ rest) 0 insts`). The
    entry-block (`pc = 0`) case: the block's compiled instructions form the program's prefix. -/
theorem asmBlockAt_prefix (insts rest : List AsmInst) : asmBlockAt (insts ++ rest) 0 insts := by
  refine ⟨by simp, ?_⟩
  intro j hj; simp only [Nat.zero_add]; rw [List.getElem?_append_left hj]

/-- **A plan is a block at its offset in a concatenated program** (`asmBlockAt (pre ++ insts ++ rest)
    pre.length insts`). The general (mid-CFG) form: a block's compiled instructions sit at pc
    `pre.length` when the whole-function program is `pre ++ block ++ rest`. -/
theorem asmBlockAt_middle (pre insts rest : List AsmInst) :
    asmBlockAt (pre ++ insts ++ rest) pre.length insts := by
  refine ⟨by simp, ?_⟩
  intro j hj
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]

/-- **Discharge `hblock` from `asmResolve` for a label-free function plan.** When the whole-function
    plan decomposes as `pre ++ blockOps ++ post` and emits no label/offset pushes (a non-control-flow
    body: arithmetic + stores, terminated by STOP/RETURN/REVERT/INVALID — so `asmResolve` is the
    identity, `asmResolve_executePlan_id`), the resolved program is exactly
    `executePlan pre ++ executePlan blockOps ++ executePlan post`, and the block sits at
    `pc = (executePlan pre).length` (`0` for the entry block). This is the `hblock` obligation of the
    block sims, reduced to the plan decomposition + label-freeness — the codegen-layout fact. -/
theorem asmBlockAt_of_labelFree_plan (pre blockOps post : List StackOp) {prog : List AsmInst}
    (hprog : prog = (asmResolve (executePlan (pre ++ blockOps ++ post))).1)
    (hL : ∀ op ∈ pre ++ blockOps ++ post, ∀ a ∈ execStackOp op, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (hO : ∀ op ∈ pre ++ blockOps ++ post, ∀ a ∈ execStackOp op, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    asmBlockAt prog (executePlan pre).length (executePlan blockOps) := by
  rw [hprog, asmResolve_executePlan_id _ hL hO, executePlan_append, executePlan_append]
  exact asmBlockAt_middle (executePlan pre) (executePlan blockOps) (executePlan post)

/-- **Computable label-freeness of a plan op.** `false` exactly for the three ops that emit an
    `AsmPushLabel`/`AsmPushOfst` (`SOPush (Label _)`, `SOPushLabel`, `SOPushOfst`); `true` otherwise —
    a decidable per-op check that a plan is a non-control-flow (arithmetic/store/JUMPDEST) plan. -/
def stackOpLabelFree : StackOp → Bool
  | StackOp.SOPush (Operand.Label _) => false
  | StackOp.SOPushLabel _ => false
  | StackOp.SOPushOfst _ _ => false
  | _ => true

/-- A label-free op's asm contains no `AsmPushLabel`/`AsmPushOfst`. -/
theorem execStackOp_ne_pushLabel {op : StackOp} {a : AsmInst}
    (h : stackOpLabelFree op = true) (ha : a ∈ execStackOp op) :
    (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl) ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) := by
  cases op with
  | SOPush operand =>
    cases operand with
    | Lit v => simp only [execStackOp, List.mem_singleton] at ha; subst ha; simp
    | Var x => simp only [execStackOp, List.not_mem_nil] at ha
    | Label l => simp [stackOpLabelFree] at h
  | SOPop n => simp only [execStackOp, List.mem_replicate] at ha; obtain ⟨_, rfl⟩ := ha; simp
  | SOSwap n => simp only [execStackOp, List.mem_singleton] at ha; subst ha; simp
  | SODup n => simp only [execStackOp, List.mem_singleton] at ha; subst ha; simp
  | SOPoke _ _ => simp only [execStackOp, List.not_mem_nil] at ha
  | SOSpill off =>
    simp only [execStackOp, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp
  | SORestore off =>
    simp only [execStackOp, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp
  | SOEmit opc => simp only [execStackOp, List.mem_singleton] at ha; subst ha; simp
  | SOLabel lbl => simp only [execStackOp, List.mem_singleton] at ha; subst ha; simp
  | SOPushLabel l => simp [stackOpLabelFree] at h
  | SOPushOfst l d => simp [stackOpLabelFree] at h

/-- Plan-level: a plan all of whose ops are label-free emits no `AsmPushLabel`/`AsmPushOfst`. -/
theorem executePlan_ne_pushLabel {ops : List StackOp} {a : AsmInst}
    (hfree : ops.all stackOpLabelFree = true) (ha : a ∈ executePlan ops) :
    (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl) ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) := by
  have ha2 : a ∈ ops.flatMap execStackOp := ha
  rw [List.mem_flatMap] at ha2
  obtain ⟨op, hop, ha'⟩ := ha2
  exact execStackOp_ne_pushLabel (List.all_eq_true.mp hfree op hop) ha'

/-- **Discharge `hblock` from a decidable label-free check.** The computable-predicate form of
    `asmBlockAt_of_labelFree_plan`: `(pre ++ blockOps ++ post).all stackOpLabelFree` (a `Bool` check on
    the plan, dischargeable by `decide`/`rfl` for a concrete plan) suffices for the `asmResolve`
    identity, so the block sits at `pc = (executePlan pre).length`. -/
theorem asmBlockAt_of_planLabelFree (pre blockOps post : List StackOp) {prog : List AsmInst}
    (hprog : prog = (asmResolve (executePlan (pre ++ blockOps ++ post))).1)
    (hfree : (pre ++ blockOps ++ post).all stackOpLabelFree = true) :
    asmBlockAt prog (executePlan pre).length (executePlan blockOps) := by
  refine asmBlockAt_of_labelFree_plan pre blockOps post hprog ?_ ?_
  · intro op hop a ha lbl
    exact (executePlan_ne_pushLabel hfree
      (show a ∈ (pre ++ blockOps ++ post).flatMap execStackOp from List.mem_flatMap.mpr ⟨op, hop, ha⟩)).1 lbl
  · intro op hop a ha lbl d
    exact (executePlan_ne_pushLabel hfree
      (show a ∈ (pre ++ blockOps ++ post).flatMap execStackOp from List.mem_flatMap.mpr ⟨op, hop, ha⟩)).2 lbl d

/-- **Aligned-JMP tail resolves to `hpush`/`hjump`.** In the resolved program of a plan whose asm has
    the JMP tail `[AsmPushLabel target, AsmOp "JUMP"]` at position `pre.length` (right after the
    label+body asm — `pre.length = as0.pc + bodyLen`), the resolved instruction there is
    `resolveInst offsets (AsmPushLabel target)` and the next is `AsmOp "JUMP"` — exactly
    `hstep_regularHSVP_jmp`'s `hpush`/`hjump`, since `asmResolve` is pointwise (`asmResolve_fst`) and
    `resolveInst` fixes `AsmOp` (`resolveInst_AsmOp`). The asm-layout companion of
    `generateBlockPlan_aligned_jmp` (whose block plan ends in that tail). -/
theorem aligned_jmp_tail_resolved (pre B : List AsmInst) (target : String) :
    (∃ h : pre.length <
        ((asmResolve (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)).1).length,
      ((asmResolve (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)).1)[pre.length]'h
        = resolveInst (computeLabelOffsets (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)).2
            (AsmInst.AsmPushLabel target)) ∧
    (∃ h : pre.length + 1 <
        ((asmResolve (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)).1).length,
      ((asmResolve (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)).1)[pre.length + 1]'h
        = AsmInst.AsmOp "JUMP") := by
  have hlen : (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B).length
      = pre.length + 2 + B.length := by simp [List.length_append]; ring
  rw [asmResolve_fst]
  refine ⟨⟨by rw [List.length_map]; omega, ?_⟩, ⟨by rw [List.length_map]; omega, ?_⟩⟩
  · rw [List.getElem_map]
    congr 1
    simp
  · rw [List.getElem_map]
    have : (pre ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] ++ B)[pre.length + 1]'(by omega)
        = AsmInst.AsmOp "JUMP" := by simp
    rw [this, resolveInst_AsmOp]

/-- **Aligned-JMP block asm structure.** The compiled asm of an aligned JMP block (plan
    `[SOLabel l] ++ body ++ [SOPushLabel target, SOEmit "JUMP"]`, per `generateBlockPlan_aligned_jmp`)
    is the label+body asm followed by `[AsmPushLabel target, AsmOp "JUMP"]` — the plan→asm bridge
    feeding `aligned_jmp_tail_resolved` (with `pre := executePlan ([SOLabel l] ++ body)`). -/
theorem executePlan_aligned_jmp_block (l : String) (body : List StackOp) (target : String) :
    executePlan ([StackOp.SOLabel l] ++ body ++ [StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"])
      = executePlan ([StackOp.SOLabel l] ++ body) ++ [AsmInst.AsmPushLabel target, AsmInst.AsmOp "JUMP"] := by
  rw [executePlan_append]; congr 1

/-- **Aligned bare-halting block asm structure.** The compiled asm of an aligned STOP/INVALID block
    (plan `[SOLabel l] ++ body ++ [SOEmit name]`, per `generateBlockPlan_aligned_bareHalt`) is the
    label+body asm followed by the single `[AsmOp name]` — the plan→asm bridge feeding
    `aligned_bareHalt_tail_resolved` (bare-op analogue of `executePlan_aligned_jmp_block`). -/
theorem executePlan_aligned_bareHalt_block (l : String) (body : List StackOp) (name : String) :
    executePlan ([StackOp.SOLabel l] ++ body ++ [StackOp.SOEmit name])
      = executePlan ([StackOp.SOLabel l] ++ body) ++ [AsmInst.AsmOp name] := by
  rw [executePlan_append]; congr 1

/-- **Bare-halting tail resolves to `AsmOp name` at `pre.length`.** `asmResolve` is pointwise
    (`asmResolve_fst`) and `resolveInst` leaves a bare `AsmOp` unchanged, so the terminal op sits at its
    unresolved index `pre.length` (= `as0.pc + bodyLen`). Bare-op analogue of `aligned_jmp_tail_resolved`
    (single position, no label push). -/
theorem aligned_bareHalt_tail_resolved (pre B : List AsmInst) (name : String) :
    ∃ h : pre.length < ((asmResolve (pre ++ [AsmInst.AsmOp name] ++ B)).1).length,
      ((asmResolve (pre ++ [AsmInst.AsmOp name] ++ B)).1)[pre.length]'h = AsmInst.AsmOp name := by
  have hlen : (pre ++ [AsmInst.AsmOp name] ++ B).length = pre.length + 1 + B.length := by
    simp [List.length_append]; ring
  rw [asmResolve_fst]
  refine ⟨by rw [List.length_map]; omega, ?_⟩
  rw [List.getElem_map]
  have : (pre ++ [AsmInst.AsmOp name] ++ B)[pre.length]'(by omega) = AsmInst.AsmOp name := by simp
  rw [this, resolveInst_AsmOp]

/-- **Aligned JNZ block asm structure.** The compiled asm of an aligned JNZ block (plan
    `[SOLabel l] ++ body ++ [SODup 1, SOPushLabel ifNz, SOEmit "JUMPI", SOPushLabel ifZ, SOEmit "JUMP"]`)
    is the label+body asm followed by the 5-op tail `[DUP1, push ifNz, JUMPI, push ifZ, JUMP]`. -/
theorem executePlan_aligned_jnz_block (l : String) (body : List StackOp) (ifNz ifZ : String) :
    executePlan ([StackOp.SOLabel l] ++ body ++ [StackOp.SODup 1, StackOp.SOPushLabel ifNz,
        StackOp.SOEmit "JUMPI", StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"])
      = executePlan ([StackOp.SOLabel l] ++ body) ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
          AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] := by
  rw [executePlan_append]; congr 1

/-- **JNZ 5-op tail resolves pointwise.** `asmResolve` is pointwise (`asmResolve_fst`) and `resolveInst`
    fixes bare `AsmOp`s while resolving the two `AsmPushLabel`s, so the DUP1/JUMPI/JUMP sit at their
    unresolved indices and the two label pushes resolve to `resolveInst offsets (AsmPushLabel …)` — exactly
    `hstep_regularHSVP_jnz_{taken,nottaken}`'s `hdup`/`hpushNz`/`hjumpi`/`hpushZ`/`hjump`. -/
theorem aligned_jnz_tail_resolved (pre B : List AsmInst) (ifNz ifZ : String) :
    (∃ h : pre.length < (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
        AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1.length,
      (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
        AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1[pre.length]'h = AsmInst.AsmOp "DUP1") ∧
    (∃ h : pre.length + 1 < (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
        AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1.length,
      (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
        AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1[pre.length + 1]'h
          = resolveInst (computeLabelOffsets (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
              AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).2
              (AsmInst.AsmPushLabel ifNz)) ∧
    (∃ h : pre.length + 2 < (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
        AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1.length,
      (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
        AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1[pre.length + 2]'h = AsmInst.AsmOp "JUMPI") ∧
    (∃ h : pre.length + 3 < (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
        AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1.length,
      (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
        AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1[pre.length + 3]'h
          = resolveInst (computeLabelOffsets (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
              AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).2
              (AsmInst.AsmPushLabel ifZ)) ∧
    (∃ h : pre.length + 4 < (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz,
        AsmInst.AsmOp "JUMPI", AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1.length,
      (asmResolve (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
        AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B)).1[pre.length + 4]'h = AsmInst.AsmOp "JUMP") := by
  have hlen : (pre ++ [AsmInst.AsmOp "DUP1", AsmInst.AsmPushLabel ifNz, AsmInst.AsmOp "JUMPI",
      AsmInst.AsmPushLabel ifZ, AsmInst.AsmOp "JUMP"] ++ B).length = pre.length + 5 + B.length := by
    simp [List.length_append]; ring
  rw [asmResolve_fst]
  refine ⟨⟨by rw [List.length_map]; omega, ?_⟩, ⟨by rw [List.length_map]; omega, ?_⟩,
    ⟨by rw [List.length_map]; omega, ?_⟩, ⟨by rw [List.length_map]; omega, ?_⟩,
    ⟨by rw [List.length_map]; omega, ?_⟩⟩
  · rw [List.getElem_map, show (pre ++ _ ++ B)[pre.length]'(by omega) = AsmInst.AsmOp "DUP1" from by simp,
      resolveInst_AsmOp]
  · rw [List.getElem_map]; congr 1
    simp
  · rw [List.getElem_map, show (pre ++ _ ++ B)[pre.length + 2]'(by omega) = AsmInst.AsmOp "JUMPI" from by simp,
      resolveInst_AsmOp]
  · rw [List.getElem_map]; congr 1
    simp
  · rw [List.getElem_map, show (pre ++ _ ++ B)[pre.length + 4]'(by omega) = AsmInst.AsmOp "JUMP" from by simp,
      resolveInst_AsmOp]

/-! ## Body-plan match: `isHalting` is irrelevant for a live-output instruction

The body fold above compiles each instruction with `isHalting = false`, whereas the real
`generateBlockPlan` uses `bbIsHalting bb` (`true` for a block ending in STOP/RETURN/…). `isHalting`
gates only one branch of `generateRegularInstPlan` — `if ¬isHalting then popmanyPlan dead else ([])`,
where `dead` is the outputs already dead at this point. When every output is still live (`dead = []`,
`popmanyPlan [] = ([], ps)`) both `isHalting` values yield the same plan. For a **single-instruction
body** the sole instruction is the one before the terminator, so the generator uses
`nextIsTerminator = true` (= the fold's uniform value) too — leaving `isHalting` as the only mismatch,
which this closes: the fold's `isHalting = false` plan equals the generator's `bbIsHalting` plan for a
live-output body. -/

/-- **`isHalting` is irrelevant to a live-output regular instruction's plan.** When every output of
    `inst` is live in `nextLiveness` (`dead = []`), the two `isHalting` values give the same
    `generateRegularInstPlan` output — the fold's `isHalting = false` matches the generator's
    `bbIsHalting`. -/
theorem generateRegularInstPlan_isHalting_irrel
    (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis) (fn : IrFunction)
    (inst : Instruction) (nextLiveness : List String) (nextIsTerminator : Bool) (curBbLabel : String)
    (ps : PlanState) (b : Bool)
    (hlive : ∀ out ∈ inst.outputs, nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = generateRegularInstPlan liveness dfg cfg fn inst nextLiveness b nextIsTerminator curBbLabel ps := by
  have hdead : inst.outputs.filter (fun out => decide (¬ nextLiveness.contains out = true)) = [] := by
    rw [List.filter_eq_nil_iff]; intro out hout
    simp only [decide_eq_true_eq, not_not]; exact hlive out hout
  unfold generateRegularInstPlan
  simp only [hdead, List.map_nil, popmanyPlan_nil, ite_self]

/-- **Fold-level assembly: the concrete `generateBlockPlan` for a single-instruction body IS
    `[SOLabel] ++ body_fold ++ termOps`.** For a block `bb.instructions = [inst, term]` (one
    non-terminator instruction with a live output, then a terminator; no params, not single-pred), the
    generated block plan decomposes with the *body fold's own form* for the instruction step —
    `generateRegularInstPlan … inst (liveVarsAt … 1) false true bb.label ps` — followed by the
    terminator's plan `termOps`. Chains `genBlockPlan_regular` (block plan = `SOLabel :: fold`),
    the `[inst, term]` fold computation (`instOps_fold_split`-shaped), and
    `generateRegularInstPlan_isHalting_irrel` (the generator's `bbIsHalting` inst step equals the
    fold's `isHalting = false` step). This is what makes `hblock`'s block plan `[SOLabel] ++ body_fold`
    a genuine prefix of the *actual* compiled program for a single-instruction body. -/
theorem genBlockPlan_singleBody_split
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    {inst term : Instruction}
    (hbb : bb.instructions = [inst, term])
    (hinstP : inst.opcode ≠ Opcode.PARAM) (htermP : term.opcode ≠ Opcode.PARAM)
    (histerm : isTerminator term.opcode = true)
    (hlive : ∀ out ∈ inst.outputs, (liveVarsAt liveness bb.label 1).contains out = true)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts bb, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    ∃ termOps, blockOps = [StackOp.SOLabel bb.label]
      ++ (generateRegularInstPlan liveness dfg cfg fn inst (liveVarsAt liveness bb.label 1) false true bb.label ps).1
      ++ termOps := by
  have hnparam : getParams bb.instructions = [] := by rw [hbb]; simp [getParams, hinstP]
  have hnpi : nonParamInsts bb = [inst, term] := by
    rw [nonParamInsts, hbb]; simp [hinstP, htermP]
  have hbop := genBlockPlan_regular hentry hnotsingle hreg hplan
  rw [hbop, hnpi, hnparam, hbb]
  simp only [List.length_cons, List.length_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.getElem!_cons_succ, List.getElem!_cons_zero,
    histerm, Nat.zero_add]
  norm_num
  rw [generateRegularInstPlan_isHalting_irrel liveness dfg cfg fn inst (liveVarsAt liveness bb.label 1)
    true bb.label ps (bbIsHalting bb) hlive]
  exact ⟨_, rfl⟩

/-! ## Concrete assembly: `hblock` discharged from `generateFnPlan`

The pieces above — `generateFnPlan_entry_isPrefix` (entry plan is the fn plan's prefix),
`genBlockPlan_singleBody_split` (block plan = `[SOLabel] ++ body_fold ++ termOps`),
`asmBlockAt_of_planLabelFree` (label-free ⇒ `asmResolve` identity) — compose into one concrete
statement: for a single-instruction-body entry block, the block sims' `hblock` obligation holds *from
the actual `generateFnPlan` output*, with no `hblock` assumption. Only structural facts (block shape,
output liveness, codegen-readiness, a decidable label-free check) remain. -/

/-- **`hblock` fully discharged from `generateFnPlan` for a single-instruction-body entry block.** For
    a function whose entry block is `[inst, term]` (a non-terminator with a live output, then a
    terminator) and whose whole compiled plan is label-free, the resolved program has the block plan
    `[SOLabel entry.label] ++ instStep` at pc 0 — no `hblock` assumption; the program layout is derived
    from the real codegen output. -/
theorem hblock_singleBody_entry_discharged
    {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock} {inst term : Instruction}
    {ops : List StackOp} {ps : PlanState}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hheadeq : fn.blocks.head? = some entry)
    (hbb : entry.instructions = [inst, term])
    (hinstP : inst.opcode ≠ Opcode.PARAM) (htermP : term.opcode ≠ Opcode.PARAM)
    (histerm : isTerminator term.opcode = true)
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1).contains out = true)
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hfree : ops.all stackOpLabelFree = true) :
    asmBlockAt (asmResolve (executePlan ops)).1 0
      (executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1) false true entry.label
            { initPlanState fnEom with labelCounter := lblCtr }).1)) := by
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  obtain ⟨termOps, hsplit⟩ := genBlockPlan_singleBody_split hbb hinstP htermP histerm hlive
    (fun e he => by rw [hheadeq] at he; injection he with he; subst he; rw [hbb]; simp [getParams, hinstP])
    hnotsingle hreg hbp
  have hopsEq : ops = ([StackOp.SOLabel entry.label]
      ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
          (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
          (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1) false true entry.label
          { initPlanState fnEom with labelCounter := lblCtr }).1) ++ (termOps ++ rest) := by
    rw [hops, hsplit]; simp [List.append_assoc]
  refine asmBlockAt_of_planLabelFree [] _ (termOps ++ rest) ?_ ?_
  · simp only [List.nil_append]; rw [hopsEq]
  · simp only [List.nil_append]; rw [← hopsEq]; exact hfree

/-! ## `hget`: the terminal `AsmOp` position discharged from `generateFnPlan` (STOP)

`hblock_singleBody_entry_discharged` places the label + body at pc 0, but the block sims additionally
need `hget` — the terminator's `AsmOp` at `pc = bodyLen`. For a STOP terminator this is now derived
from the same `generateFnPlan` output: `genBlockPlan_singleBody_split_stop` pins the terminator's plan
to the concrete `[SOEmit "STOP"]` (via `generateRegularInstPlan_emit_noIO`, since a well-formed STOP
has no operands/outputs), so the resolved program's `AsmOp "STOP"` sits right after the executed
label + body. -/

/-- **Single-instruction-body block plan, STOP terminator, with `termOps` pinned.** Strengthens
    `genBlockPlan_singleBody_split`: for `bb.instructions = [inst, term]` with `term` a well-formed STOP
    (`opcode = STOP`, no operands/outputs), the block plan is exactly
    `[SOLabel] ++ instStep ++ [SOEmit "STOP"]` — the terminator's plan is the concrete `[SOEmit "STOP"]`
    (via `generateRegularInstPlan_emit_noIO`), not an opaque existential. This is what pins the STOP
    `AsmOp` position: it sits right after the label + body. -/
theorem genBlockPlan_singleBody_split_stop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    {inst term : Instruction}
    (hbb : bb.instructions = [inst, term])
    (hinstP : inst.opcode ≠ Opcode.PARAM) (htermP : term.opcode ≠ Opcode.PARAM)
    (histerm : isTerminator term.opcode = true)
    (hterm_stop : term.opcode = Opcode.STOP)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hlive : ∀ out ∈ inst.outputs, (liveVarsAt liveness bb.label 1).contains out = true)
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts bb, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = [StackOp.SOLabel bb.label]
      ++ (generateRegularInstPlan liveness dfg cfg fn inst (liveVarsAt liveness bb.label 1) false true bb.label ps).1
      ++ [StackOp.SOEmit "STOP"] := by
  have hnparam : getParams bb.instructions = [] := by rw [hbb]; simp [getParams, hinstP]
  have hnpi : nonParamInsts bb = [inst, term] := by
    rw [nonParamInsts, hbb]; simp [hinstP, htermP]
  have hbop := genBlockPlan_regular hentry hnotsingle hreg hplan
  have htname : opcodeToEvmName term.opcode = some "STOP" := by rw [hterm_stop]; rfl
  rw [hbop, hnpi, hnparam, hbb]
  simp only [List.length_cons, List.length_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.getElem!_cons_succ, List.getElem!_cons_zero,
    histerm, Nat.zero_add]
  norm_num
  rw [generateRegularInstPlan_isHalting_irrel liveness dfg cfg fn inst (liveVarsAt liveness bb.label 1)
    true bb.label ps (bbIsHalting bb) hlive]
  rw [generateRegularInstPlan_emit_noIO (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    hterm_ops hterm_outs htname]

/-- **STOP `AsmOp` position via the resolved segment** (the general `hget` foundation). For any plan
    `ops = pre ++ [SOEmit "STOP"] ++ post`, the resolved program has `AsmOp "STOP"` at
    `pc = (executePlan pre).length` — the STOP is a label-push-free 1-op segment, so `asmResolve` fixes
    it in place regardless of labels elsewhere (e.g. a JMP). This subsumes the whole-program-label-free
    entry `hget`: the entry/param/non-entry discharges below all instantiate it (`pre` = the block's
    label + body, `post` = the rest of the function) — with no `ops.all stackOpLabelFree` assumption. -/
theorem hget_stop_segment {ops pre post : List StackOp}
    (hopsEq : ops = pre ++ [StackOp.SOEmit "STOP"] ++ post) :
    ∃ hlt : (executePlan pre).length < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨(executePlan pre).length, hlt⟩ = AsmInst.AsmOp "STOP" := by
  have hep : executePlan ops = executePlan pre ++ [AsmInst.AsmOp "STOP"] ++ executePlan post := by
    rw [hopsEq, executePlan_append, executePlan_append,
      show executePlan [StackOp.SOEmit "STOP"] = [AsmInst.AsmOp "STOP"] from by
        simp [executePlan, execStackOp]]
  rw [hep]
  have hblk := asmBlockAt_resolved_of_middle_no_label (executePlan pre) [AsmInst.AsmOp "STOP"]
    (executePlan post)
    (by intro a ha lbl; simp only [List.mem_singleton] at ha; subst ha; simp)
    (by intro a ha lbl d; simp only [List.mem_singleton] at ha; subst ha; simp)
  exact asmBlockAt_one hblk

/-- **`hget` (the STOP `AsmOp` position) discharged from `generateFnPlan`** for a single-instruction-body
    STOP-terminated entry block. Companion of `hblock_singleBody_entry_discharged`: the resolved program
    has `AsmOp "STOP"` at `pc = bodyLen` (the length of the executed label + body). Together they supply
    both program-layout facts the STOP block sims (`genBlockSimulation_regularGN_stop_entry`) need, from
    the real codegen output — no `hblock`/`hget` assumptions. Discharges via the general
    `hget_stop_segment`. -/
theorem hget_singleBody_stop_entry_discharged
    {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock} {inst term : Instruction}
    {ops : List StackOp} {ps : PlanState}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hheadeq : fn.blocks.head? = some entry)
    (hbb : entry.instructions = [inst, term])
    (hinstP : inst.opcode ≠ Opcode.PARAM) (htermP : term.opcode ≠ Opcode.PARAM)
    (histerm : isTerminator term.opcode = true)
    (hterm_stop : term.opcode = Opcode.STOP)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hlive : ∀ out ∈ inst.outputs,
      (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1).contains out = true)
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP) :
    ∃ hlt : (executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1) false true entry.label
            { initPlanState fnEom with labelCounter := lblCtr }).1)).length
        < (asmResolve (executePlan ops)).1.length,
      (asmResolve (executePlan ops)).1.get ⟨(executePlan ([StackOp.SOLabel entry.label]
        ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
            (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
            (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1) false true entry.label
            { initPlanState fnEom with labelCounter := lblCtr }).1)).length, hlt⟩
        = AsmInst.AsmOp "STOP" := by
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  have hsplit := genBlockPlan_singleBody_split_stop hbb hinstP htermP histerm hterm_stop hterm_ops
    hterm_outs hlive
    (fun e he => by rw [hheadeq] at he; injection he with he; subst he; rw [hbb]; simp [getParams, hinstP])
    hnotsingle hreg hbp
  have hopsEq : ops = (([StackOp.SOLabel entry.label]
      ++ (generateRegularInstPlan (livenessAnalyzeFuel (fnPlanFuel fn) fn)
          (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn inst
          (liveVarsAt (livenessAnalyzeFuel (fnPlanFuel fn) fn) entry.label 1) false true entry.label
          { initPlanState fnEom with labelCounter := lblCtr }).1) ++ [StackOp.SOEmit "STOP"]) ++ rest := by
    rw [hops, hsplit]
  exact hget_stop_segment hopsEq

/-! ## First fully-concrete capstone: a bare-STOP entry function from `generateFnPlan`

The var-reading tension is not a gap in the layout discharge but is *baked into* `RegularStep`: every
body instruction requires `inst.operands = [Operand.Var x, …]` with `x ∈ S` (the tracked stack), so
`RegularBodyG … body []` is unsatisfiable for any non-empty `body` at an entry (empty `S`) — even a
literal-reading op has no `RegularStep` case. Hence the only *closeable* concrete STOP entry block is
the empty-body one: `entry = [STOP]`. That case, however, closes end-to-end with **zero** layout
assumptions — `hblock`/`hget` are both derived from the real `generateFnPlan` output — giving the first
fully-concrete `runBlock ↔ runAsm` correspondence for a whole (trivial) compiled function. Non-trivial
bodies need either a param-loading prefix or a non-entry block position (the standing ④ frontier). -/

/-- Bare-terminator (single no-IO terminator) block plan, name-parametric: `[SOLabel l, SOEmit name]`.
    The empty-body twin of `genBlockPlan_singleBody_split_stop`; serves both the STOP and INVALID
    entry-function capstones. -/
theorem genBlockPlan_bareTerm_split
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState} {term : Instruction}
    {name : String}
    (hbb : bb.instructions = [term])
    (htermP : term.opcode ≠ Opcode.PARAM)
    (hterm_name : opcodeToEvmName term.opcode = some name)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts bb, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = [StackOp.SOLabel bb.label, StackOp.SOEmit name] := by
  have hnparam : getParams bb.instructions = [] := by rw [hbb]; simp [getParams, htermP]
  have hnpi : nonParamInsts bb = [term] := by rw [nonParamInsts, hbb]; simp [htermP]
  have hbop := genBlockPlan_regular hentry hnotsingle hreg hplan
  rw [hbop, hnpi, hnparam, hbb]
  simp only [List.length_cons, List.length_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil, List.nil_append]
  rw [generateRegularInstPlan_emit_noIO (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    hterm_ops hterm_outs hterm_name]

/-- **Full concrete codegen correctness for a bare-STOP entry function** (`entry = [STOP]`). The first
    fully-concrete, zero-layout-assumption end-to-end block sim from the real `generateFnPlan` output:
    `runBlock` on the entry block corresponds to `runAsm` on the resolved program, with the terminal
    relation at the STOP halt. `hblock` (`AsmLabel` at pc 0) and `hget` (`AsmOp "STOP"` at pc 1) are
    both derived here from the bare-STOP block plan `[SOLabel, SOEmit "STOP"]`; the body is empty so the
    var-reading tension does not arise. Only the function's structural / codegen-readiness facts remain
    as hypotheses. -/
theorem codegen_bareStop_entry_correct
    {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock}
    {term : Instruction} {ops : List StackOp} {ps : PlanState} {vs : VenomState} {fuel : Nat}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hheadeq : fn.blocks.head? = some entry)
    (hbb : entry.instructions = [term])
    (htermP : term.opcode ≠ Opcode.PARAM)
    (hterm_stop : term.opcode = Opcode.STOP)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hfree : ops.all stackOpLabelFree = true) :
    (match runBlock fuel ctx entry vs with
     | ExecResult.OK vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
            (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
            (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
            offsetToPc (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
            offsetToPc (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  have hname : opcodeToEvmName term.opcode = some "STOP" := by rw [hterm_stop]; rfl
  have hsplit := genBlockPlan_bareTerm_split hbb htermP hname hterm_ops hterm_outs
    (fun e he => by rw [hheadeq] at he; injection he with he; subst he; rw [hbb]; simp [getParams, htermP])
    hnotsingle hreg hbp
  have hopsEq : ops = [StackOp.SOLabel entry.label, StackOp.SOEmit "STOP"] ++ rest := by rw [hops, hsplit]
  have hpre1 : ([] : List StackOp) ++ [StackOp.SOLabel entry.label] ++ ([StackOp.SOEmit "STOP"] ++ rest) = ops := by
    rw [hopsEq]; simp
  have hpre2 : [StackOp.SOLabel entry.label] ++ [StackOp.SOEmit "STOP"] ++ rest = ops := by
    rw [hopsEq]; simp
  have hblock : asmBlockAt (asmResolve (executePlan ops)).1 0 (executePlan [StackOp.SOLabel entry.label]) := by
    have := asmBlockAt_of_planLabelFree [] [StackOp.SOLabel entry.label] ([StackOp.SOEmit "STOP"] ++ rest)
      (prog := (asmResolve (executePlan ops)).1) (by rw [hpre1]) (by rw [hpre1]; exact hfree)
    simpa [executePlan] using this
  have hgetBlk : asmBlockAt (asmResolve (executePlan ops)).1 1 (executePlan [StackOp.SOEmit "STOP"]) := by
    have := asmBlockAt_of_planLabelFree [StackOp.SOLabel entry.label] [StackOp.SOEmit "STOP"] rest
      (prog := (asmResolve (executePlan ops)).1) (by rw [hpre2]) (by rw [hpre2]; exact hfree)
    simpa [executePlan, execStackOp] using this
  rw [show executePlan [StackOp.SOEmit "STOP"] = [AsmInst.AsmOp "STOP"] from by
    simp [executePlan, execStackOp]] at hgetBlk
  obtain ⟨hlt1, hget1⟩ := asmBlockAt_one hgetBlk
  exact genBlockSimulation_regularGN_stop_entry
    (labelOffsets := labelOffsets) (ps' := ps') (offsetToPc := offsetToPc) (fnEom := fnEom)
    (liveness := livenessAnalyzeFuel (fnPlanFuel fn) fn) (dfg := DfgAnalysis.buildFunction fn)
    (cfg := cfgAnalyze fn) (fn := fn) (body := []) (term := term) (hd := term) (tl := [])
    (l := entry.label) (curBbLabel := entry.label) (nextLiveness := []) (sEnd := { vs with instIdx := 0 })
    (bodyLen := 1)
    True.intro hbb rfl (by rw [hterm_stop]; decide) (by intro inst hinst; simp at hinst)
    (by rw [hterm_stop]; decide) (by decide) rfl (by simp only [stepInstBase, hterm_stop])
    (by simpa using hblock) rfl (by simpa using hlt1) (by simpa using hget1)

/-- **Full concrete codegen correctness for a bare-INVALID entry function** (`entry = [INVALID]`). The
    fault companion of `codegen_bareStop_entry_correct`; identical layout discharge (via
    `genBlockPlan_bareTerm_split` with `name = "INVALID"`) into `genBlockSimulation_regularGN_invalid_entry`,
    additionally needing `hrd : vs.returndata = empty` (the in-scope assumption — the INVALID Venom step
    clears returndata; the asm fault never sets it). -/
theorem codegen_bareInvalid_entry_correct
    {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat} {entry : BasicBlock}
    {term : Instruction} {ops : List StackOp} {ps : PlanState} {vs : VenomState} {fuel : Nat}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (hgen : generateFnPlan fn fnEom lblCtr = some (ops, ps))
    (hheadeq : fn.blocks.head? = some entry)
    (hbb : entry.instructions = [term])
    (htermP : term.opcode ≠ Opcode.PARAM)
    (hterm_invalid : term.opcode = Opcode.INVALID)
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hfn : ∀ bb ∈ fn.blocks, ∀ i ∈ bb.instructions, codegenReadyInst i)
    (hnotsingle : ((cfgAnalyze fn).predsOf entry.label).length ≠ 1)
    (hreg : ∀ i ∈ nonParamInsts entry, ¬ isPreCodegenOpcode i.opcode ∧
      i.opcode ≠ Opcode.PHI ∧ i.opcode ≠ Opcode.OFFSET ∧ i.opcode ≠ Opcode.PARAM ∧ i.opcode ≠ Opcode.NOP)
    (hfree : ops.all stackOpLabelFree = true) :
    (match runBlock fuel ctx entry vs with
     | ExecResult.OK vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
            (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
            (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
            offsetToPc (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
            offsetToPc (asmResolve (executePlan ops)).1 (asmOfVenom { vs with instIdx := 0 })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  obtain ⟨blockOps, ps'2, rest, hbp, hops⟩ := generateFnPlan_entry_isPrefix hheadeq hfn hgen
  have hname : opcodeToEvmName term.opcode = some "INVALID" := by rw [hterm_invalid]; rfl
  have hsplit := genBlockPlan_bareTerm_split hbb htermP hname hterm_ops hterm_outs
    (fun e he => by rw [hheadeq] at he; injection he with he; subst he; rw [hbb]; simp [getParams, htermP])
    hnotsingle hreg hbp
  have hopsEq : ops = [StackOp.SOLabel entry.label, StackOp.SOEmit "INVALID"] ++ rest := by rw [hops, hsplit]
  have hpre1 : ([] : List StackOp) ++ [StackOp.SOLabel entry.label] ++ ([StackOp.SOEmit "INVALID"] ++ rest) = ops := by
    rw [hopsEq]; simp
  have hpre2 : [StackOp.SOLabel entry.label] ++ [StackOp.SOEmit "INVALID"] ++ rest = ops := by
    rw [hopsEq]; simp
  have hblock : asmBlockAt (asmResolve (executePlan ops)).1 0 (executePlan [StackOp.SOLabel entry.label]) := by
    have := asmBlockAt_of_planLabelFree [] [StackOp.SOLabel entry.label] ([StackOp.SOEmit "INVALID"] ++ rest)
      (prog := (asmResolve (executePlan ops)).1) (by rw [hpre1]) (by rw [hpre1]; exact hfree)
    simpa [executePlan] using this
  have hgetBlk : asmBlockAt (asmResolve (executePlan ops)).1 1 (executePlan [StackOp.SOEmit "INVALID"]) := by
    have := asmBlockAt_of_planLabelFree [StackOp.SOLabel entry.label] [StackOp.SOEmit "INVALID"] rest
      (prog := (asmResolve (executePlan ops)).1) (by rw [hpre2]) (by rw [hpre2]; exact hfree)
    simpa [executePlan, execStackOp] using this
  rw [show executePlan [StackOp.SOEmit "INVALID"] = [AsmInst.AsmOp "INVALID"] from by
    simp [executePlan, execStackOp]] at hgetBlk
  obtain ⟨hlt1, hget1⟩ := asmBlockAt_one hgetBlk
  exact genBlockSimulation_regularGN_invalid_entry
    (labelOffsets := labelOffsets) (ps' := ps') (offsetToPc := offsetToPc) (fnEom := fnEom)
    (liveness := livenessAnalyzeFuel (fnPlanFuel fn) fn) (dfg := DfgAnalysis.buildFunction fn)
    (cfg := cfgAnalyze fn) (fn := fn) (body := []) (term := term) (hd := term) (tl := [])
    (l := entry.label) (curBbLabel := entry.label) (nextLiveness := []) (sEnd := { vs with instIdx := 0 })
    (bodyLen := 1)
    True.intro hbb rfl (by rw [hterm_invalid]; decide) (by intro inst hinst; simp at hinst)
    (by rw [hterm_invalid]; decide) (by decide) rfl (by simp only [stepInstBase, hterm_invalid])
    (by simpa using hblock) rfl (by simpa using hlt1) (by simpa using hget1)

end EvmYul.Venom.Hol.Codegen

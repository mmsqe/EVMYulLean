import EvmYul.Venom.Hol.Codegen.GenBlockSimSupport
import EvmYul.Venom.Hol.Codegen.PlanSim

/-!
# GenInstSim — ComputeAtoms

Per-instruction step sims: single-op atoms (var-preservation, block-prefix, dispatch, halting
terminals, DUP, input emission) and the per-opcode compute steps (binops/ternops/value-push/store/
memory/load/SHA3/storage/calldata/account/LOG/copy/unary).
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

variable {offsetToPc : AssocList Nat Nat}


/-- For a length-1 plan segment, `asmBlockAt` gives the pc bound and the single
    instruction sitting at the pc. Shared by the single-op sims below. -/
theorem asmBlockAt_one {prog : List AsmInst} {pc : Nat} {a : AsmInst}
    (h : asmBlockAt prog pc [a]) :
    ∃ hpc : pc < prog.length, prog.get ⟨pc, hpc⟩ = a := by
  have hpc : pc < prog.length := by have := h.1; simp only [List.length_singleton] at this; omega
  exact ⟨hpc, by simpa using asmBlockAt_get h (j := 0) (by simp)⟩

/-- `NOP`: the generator emits no ops and the Venom step is a no-op, so the (empty)
    asm program trivially preserves `venomAsmRel` and leaves the pc unchanged. -/
theorem genInstPlan_sim_nop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hnop : inst.opcode = Opcode.NOP)
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps'))
    (hrel : venomAsmRel lo ps vs as) :
    ops = [] ∧ ps' = ps ∧ stepInstBase inst vs = ExecResult.OK vs ∧
    runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as ∧
    venomAsmRel lo ps' vs as ∧ as.pc = as.pc + (executePlan ops).length := by
  -- generate_inst_plan reaches the NOP branch: ops = [], ps' = ps
  simp only [generateInstPlan, hnop, isPreCodegenOpcode] at hgen
  obtain ⟨rfl, rfl⟩ := hgen
  -- `executePlan [] = []`, so the asm run is `runAsm 0 = AsmOK as` and the pc is unchanged
  refine ⟨rfl, rfl, ?_, rfl, hrel, rfl⟩
  -- step_inst_base NOP = OK vs
  simp only [stepInstBase, hnop]

/-! ## Variable-update preservation

The reusable enabler for every var-defining instruction's simulation: defining a
fresh variable (one absent from both the plan stack and the spill map) preserves
`venomAsmRel`, because `venomAsmRel` only reads `vs.vars` through `operandVal` on
stack/spilled operands — all of which differ from the fresh output. -/

/-- `List.lookup` is unaffected by filtering out a *different* key. -/
theorem listLookup_filter_ne {α β} [BEq α] [LawfulBEq α] (m : List (α × β)) (k o : α) (h : o ≠ k) :
    List.lookup o (m.filter (fun x => x.1 != k)) = List.lookup o m := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [List.filter_cons]
    by_cases hk : k' = k
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.lookup_cons,
        beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, if_false]
      exact ih
    · have hne : (k' != k) = true := by simp [bne_iff_ne, hk]
      simp only [hne, if_true, List.lookup_cons]
      by_cases hko : o == k'
      · simp only [hko]
      · simp only [hko]; exact ih

/-- Looking up a key sees through an insert of a *different* key. -/
theorem assocLookup_insert_ne {α β} [BEq α] [LawfulBEq α] (m : AssocList α β) (k o : α) (v : β)
    (h : o ≠ k) :
    AssocList.lookup α β (AssocList.insert α β m k v) o = AssocList.lookup α β m o := by
  rw [assocLookup_eq_listLookup, assocLookup_eq_listLookup]
  simp only [AssocList.insert, List.lookup_cons, beq_eq_false_iff_ne.mpr h]
  exact listLookup_filter_ne m k o h

/-- `lookupVar` sees through an update of a *different* variable. -/
theorem lookupVar_updateVar_ne (vs : VenomState) (out w : String) (v : bytes32) (h : w ≠ out) :
    lookupVar w (updateVar out v vs) = lookupVar w vs := by
  unfold lookupVar updateVar alookup ainsert
  exact assocLookup_insert_ne vs.vars out w v h

/-- `lookupVar` of a just-updated variable returns the new value — the output-value tie:
    after `execPure2 f` sets `out := f v1 v2`, `operandVal … (Var out) = some (f v1 v2)`. -/
theorem lookupVar_updateVar_self (vs : VenomState) (out : String) (v : bytes32) :
    lookupVar out (updateVar out v vs) = some v := by
  unfold lookupVar updateVar alookup ainsert
  simp [AssocList.insert, AssocList.lookup]

/-- `operandVal` is unchanged by updating a variable absent from the operand. -/
theorem operandVal_updateVar_ne (vs : VenomState) (lo : AssocList String Nat) (out : String)
    (v : bytes32) (op : Operand) (h : op ≠ Operand.Var out) :
    operandVal (updateVar out v vs) lo op = operandVal vs lo op := by
  cases op with
  | Var w => exact lookupVar_updateVar_ne vs out w v (fun hw => h (by rw [hw]))
  | Lit w => rfl
  | Label l => rfl

/-- **`venom_asm_rel_update_var`**: defining a fresh variable (absent from both the plan
    stack and the spill map) preserves `venomAsmRel`. The reusable enabler for every
    var-defining instruction's simulation (PARAM, the regular non-terminal opcodes …). -/
theorem venomAsmRel_updateVar (lo : AssocList String Nat) (ps : PlanState) (vs : VenomState)
    (as : AsmState) (out : String) (v : bytes32)
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo ps (updateVar out v vs) as := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  refine ⟨?_, ?_, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · -- planStackRel: every stack operand differs from `Var out`
    obtain ⟨hlen, hget⟩ := hStk
    refine ⟨hlen, fun i hi => ?_⟩
    have hi' : i < ps.stack.reverse.length := by rw [List.length_reverse]; exact hi
    have hmem : ps.stack.reverse[i]! ∈ ps.stack := by
      rw [List_get!_eq_get ps.stack.reverse i hi']
      have := List.get_mem ps.stack.reverse ⟨i, hi'⟩
      rwa [List.mem_reverse] at this
    rw [operandVal_updateVar_ne vs lo out v _ (fun hc => hstack (hc ▸ hmem))]
    exact hget i hi
  · -- planSpillRel: every spilled key differs from `Var out`
    intro op off hlk
    have hop : op ≠ Operand.Var out := fun hc => by rw [hc, hspill] at hlk; exact absurd hlk (by simp)
    rw [operandVal_updateVar_ne vs lo out v _ hop]
    exact hSpill op off hlk

/-- `PARAM`: the generator emits no ops; the Venom step defines a single (SSA-)fresh
    output variable, so the (empty) asm preserves `venomAsmRel` via `venomAsmRel_updateVar`. -/
theorem genInstPlan_sim_param
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {lo : AssocList String Nat}
    {vs vs' : VenomState} {as : AsmState} {prog : List AsmInst}
    (hparam : inst.opcode = Opcode.PARAM)
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hstep : stepInstBase inst vs = ExecResult.OK vs')
    (hfresh : ∀ out ∈ inst.outputs, ¬ (Operand.Var out) ∈ ps.stack ∧
               AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    ops = [] ∧ ps' = ps ∧
    runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as ∧
    venomAsmRel lo ps' vs' as ∧ as.pc = as.pc + (executePlan ops).length := by
  simp only [generateInstPlan, hparam, isPreCodegenOpcode] at hgen
  obtain ⟨rfl, rfl⟩ := hgen
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  -- Unpack the PARAM step: success requires operands = [Lit idx], i in range, outputs = [out],
  -- and yields vs' = updateVar out _ vs.
  simp only [stepInstBase, hparam] at hstep
  split at hstep
  · split at hstep
    · split at hstep
      · rename_i out heq
        injection hstep with hstep'
        subst hstep'
        have hf := hfresh out (by rw [heq]; exact List.mem_singleton_self out)
        exact venomAsmRel_updateVar lo ps vs as out _ hrel hf.1 hf.2
      · exact absurd hstep (by simp)
    · exact absurd hstep (by simp)
  · exact absurd hstep (by simp)

/-! ## Block-prefix ops

The block plan opens with `[SOLabel bb.label]` (a JUMPDEST). Its asm is a pure
pc-advance, so it preserves `venomAsmRel` — the first segment `genBlockSimulation`
sequences (via `plan_seq_sim`) before the clean-stack prefix and the instruction fold. -/

/-- Single-step `asmStep` on `AsmLabel` advances the pc (a JUMPDEST marker is a no-op
    on the EVM state). -/
theorem asmStep_label_ok {offsetToPc prog s l}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmLabel l) :
    asmStep offsetToPc prog s = AsmResult.AsmOK (asmNext s) := by
  unfold asmStep; rw [dif_pos hpc, hprog]

/-- `SOLabel` (the block's leading JUMPDEST): emits one `AsmLabel`, which only advances
    the pc, so `venomAsmRel` is preserved (it does not depend on the pc). -/
theorem soLabel_sim (lo : AssocList String Nat) (ps : PlanState) (vs : VenomState)
    (as : AsmState) (prog : List AsmInst) (l : String)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel l])) :
    ∃ as', runAsm (executePlan [StackOp.SOLabel l]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps vs as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOLabel l]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨asmNext as, ?_, hrel, ?_⟩
  · show runAsm 1 offsetToPc prog as = AsmResult.AsmOK (asmNext as)
    rw [runAsm_succ_ok hpc (asmStep_label_ok hpc hget)]
    rfl
  · rfl

/-! ## Regular-opcode dispatch

The gateway every remaining per-instruction sim (the regular / halting / aborting
opcodes — ADD, RETURN, STOP, …) goes through: for any opcode that is not one of the
specially-handled cases (pre-codegen / PHI / OFFSET / PARAM / NOP), `generate_inst_plan`
is exactly `generate_regular_inst_plan`. Those sims then reduce to reasoning about
`generateRegularInstPlan` (its `inputOps ++ joinOps ++ reorderOps ++ emitOps [++ popOps
++ optOps]` decomposition, on `reorderPlan_sim` + the spill sims). -/

/-- `generate_inst_plan` is `generate_regular_inst_plan` for every non-special opcode. -/
theorem generateInstPlan_regular_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps : PlanState}
    (h0 : ¬ isPreCodegenOpcode inst.opcode)
    (hphi : inst.opcode ≠ Opcode.PHI) (hoff : inst.opcode ≠ Opcode.OFFSET)
    (hparam : inst.opcode ≠ Opcode.PARAM) (hnop : inst.opcode ≠ Opcode.NOP) :
    generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
      = some (generateRegularInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm
                curBb ps) := by
  unfold generateInstPlan
  rw [if_neg h0, if_neg hphi, if_neg hoff, if_neg hparam, if_neg hnop]

/-! ## Terminal opcodes (halting)

The first terminal sim: STOP. The generator emits a single `SOEmit "STOP"`; the Venom
step halts (`haltState`) and the asm `STOP` halts (`AsmHalt`), with observable effects
in agreement (`venomAsmTerminalRel`, which `venomAsmRel` implies). This is the shape
`genBlockSimulation`'s Halt branch consumes for the block's final instruction.

The generator half is factored as a reusable no-IO decomposition (the
`gen_inst_terminal_setup` analog): every no-operand/no-output opcode with an EVM name
plans to exactly `[SOEmit name]`. -/

/-- Generator decomposition for any no-input/no-output opcode mapping to a single EVM
    name: `generate_regular_inst_plan` emits exactly `[SOEmit name]` (no input ops, no
    reorder, no output handling). -/
theorem generateRegularInstPlan_emit_noIO
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps : PlanState} {name : String}
    (hops : inst.operands = []) (houts : inst.outputs = [])
    (hname : opcodeToEvmName inst.opcode = some name) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps).1
      = [StackOp.SOEmit name] := by
  simp [generateRegularInstPlan, computeOperands, hops, houts, emitInputPlan, generateEmitOps,
    hname, reorderPlan, getNonLabelOperands, List.enum]

/-- Generator decomposition through the dispatch gateway: a no-IO opcode with an EVM name
    (and not specially handled) plans to exactly `[SOEmit name]`. -/
theorem generateInstPlan_emit_noIO
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {name : String}
    (h0 : ¬ isPreCodegenOpcode inst.opcode)
    (hphi : inst.opcode ≠ Opcode.PHI) (hoff : inst.opcode ≠ Opcode.OFFSET)
    (hparam : inst.opcode ≠ Opcode.PARAM) (hnop : inst.opcode ≠ Opcode.NOP)
    (hops : inst.operands = []) (houts : inst.outputs = [])
    (hname : opcodeToEvmName inst.opcode = some name)
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps')) :
    ops = [StackOp.SOEmit name] := by
  rw [generateInstPlan_regular_eq h0 hphi hoff hparam hnop, Option.some.injEq] at hgen
  have h := congrArg Prod.fst hgen
  rw [generateRegularInstPlan_emit_noIO hops houts hname] at h
  exact h.symm

/-- Single-step `asmStep` on `AsmOp "STOP"` halts. -/
theorem asmStep_stop_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "STOP") :
    asmStep offsetToPc prog s = AsmResult.AsmHalt (asmNext s) := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `STOP` (terminal/halting): the generator emits `[SOEmit "STOP"]`; the Venom step
    halts (`haltState`) and the asm `STOP` halts (`AsmHalt`), with observable effects
    in agreement (`venomAsmTerminalRel`, which follows from `venomAsmRel`). -/
theorem genInstPlan_sim_stop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hstop : inst.opcode = Opcode.STOP) (hops : inst.operands = []) (houts : inst.outputs = [])
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ops = [StackOp.SOEmit "STOP"] ∧
    stepInstBase inst vs = ExecResult.Halt (haltState vs) ∧
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState vs) as' := by
  have hops_eq : ops = [StackOp.SOEmit "STOP"] :=
    generateInstPlan_emit_noIO (by rw [hstop]; decide) (by rw [hstop]; decide)
      (by rw [hstop]; decide) (by rw [hstop]; decide) (by rw [hstop]; decide)
      hops houts (by rw [hstop]; rfl) hgen
  subst hops_eq
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨rfl, by simp only [stepInstBase, hstop], asmNext as, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = AsmResult.AsmHalt (asmNext as)
    unfold runAsm
    rw [asmStep_stop_ok hpc hget]
  · exact venomAsmRel_terminal lo ps vs as hrel

/-- Single-step `asmStep` on `AsmOp "INVALID"` faults. -/
theorem asmStep_invalid_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "INVALID") :
    asmStep offsetToPc prog s = AsmResult.AsmFault { asmNext s with returndata := ByteArray.empty } := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `INVALID` (terminal/aborting, `ExHaltAbort`): the generator emits `[SOEmit "INVALID"]`;
    the Venom step aborts with returndata cleared and the asm `INVALID` faults (`AsmFault`).
    `venomAsmTerminalRel` holds **unconditionally**: both sides clear returndata (the Venom
    step via `setReturndata empty`, the asm `INVALID` via `AsmFault { asmNext s with
    returndata := empty }`), so the terminal returndata match is `empty = empty` by `rfl`. -/
theorem genInstPlan_sim_invalid
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hinv : inst.opcode = Opcode.INVALID) (hops : inst.operands = []) (houts : inst.outputs = [])
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ops = [StackOp.SOEmit "INVALID"] ∧
    stepInstBase inst vs
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vs)) ∧
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel (haltState (setReturndata ByteArray.empty vs)) as' := by
  have hops_eq : ops = [StackOp.SOEmit "INVALID"] :=
    generateInstPlan_emit_noIO (by rw [hinv]; decide) (by rw [hinv]; decide)
      (by rw [hinv]; decide) (by rw [hinv]; decide) (by rw [hinv]; decide)
      hops houts (by rw [hinv]; rfl) hgen
  subst hops_eq
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  obtain ⟨_, _, _, hAcc, hTrans, _, hLog, _⟩ := hrel
  refine ⟨rfl, by simp only [stepInstBase, hinv], { asmNext as with returndata := ByteArray.empty }, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = AsmResult.AsmFault { asmNext as with returndata := ByteArray.empty }
    unfold runAsm
    rw [asmStep_invalid_ok hpc hget]
  · exact ⟨hAcc, hTrans, rfl, hLog⟩

/-- **Asm-side sim for a bare STOP terminal block** (`[SOLabel l, SOEmit "STOP"]`) — the simplest
    `hasm` for `hfsim_jmp_then_halt`. Running the block (`JUMPDEST ; STOP`) from the block's entry
    `asMid` halts (`AsmHalt`) with the observable effects in agreement (`venomAsmTerminalRel`); any
    extra budget is absorbed (`AsmHalt` is fuel-monotone). Reduces `hasm` to the two whole-program
    inputs the caller still supplies: the resolved `asmBlockAt` for the block at `asMid.pc`, and the
    `venomAsmRel` relating `asMid` to the terminal block's entry Venom state `vs`. -/
theorem hasm_stop {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {asMid : AsmState}
    {l : String} {budget : Nat} {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    (hrel : venomAsmRel lo ps vs asMid)
    (hblock : asmBlockAt prog asMid.pc (executePlan [StackOp.SOLabel l, StackOp.SOEmit "STOP"]))
    (hbudget : 2 ≤ budget) :
    ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel (haltState vs) asm' := by
  rw [show [StackOp.SOLabel l, StackOp.SOEmit "STOP"]
        = [StackOp.SOLabel l] ++ [StackOp.SOEmit "STOP"] from rfl, executePlan_append] at hblock
  obtain ⟨hbLabel, hbStop⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ := soLabel_sim lo ps vs asMid prog l hrel hbLabel
  have hbStop' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "STOP"]) := by
    rw [hpc1]; exact hbStop
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hbStop'
  have hstop2 : runAsm 2 offsetToPc prog asMid = AsmResult.AsmHalt (asmNext as1) := by
    rw [show (2 : Nat) = (executePlan [StackOp.SOLabel l]).length + 1 from rfl,
        runAsm_append_ok hrun1]
    unfold runAsm; rw [asmStep_stop_ok hpc hget]
  exact ⟨asmNext as1, runAsm_le_of_ne_ok (fun s => by simp) hbudget hstop2,
         venomAsmRel_terminal lo ps vs as1 hrel1⟩

/-! ## RETURN / REVERT — operand-carrying terminals (returndata = memory slice)

Unlike the operand-less STOP/INVALID, these pop `off`/`sz` and halt/revert with
`returndata = memory[off, off+sz)`, so the terminal-rel obligation has real content: the
`returndata` conjunct must match. Venom reads `vs.memory.readWithPadding off sz` (no expansion);
asm reads `(asmExpandMemory … as.memory).readWithPadding off sz`. With the asm memory covering the
(rounded) window (`hcov`, true under `spillMemCovered`) the expansion is a no-op; the slice lying
below the spill region (`hsafe : off+sz ≤ fnEom`) makes the two memories agree on it byte-for-byte
(`memoryRel_readWithPadding_slice`). -/

/-- `asmStep` dispatch for `RETURN`. -/
theorem asmStep_return_ok {offsetToPc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "RETURN") :
    asmStep offsetToPc prog s = asmReturnOp s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `REVERT`. -/
theorem asmStep_revert_ok {offsetToPc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "REVERT") :
    asmStep offsetToPc prog s = asmRevertOp s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmReturnOp` on a 2-deep stack with the asm memory covering the (rounded) returned window
    (or empty `sz`) halts (`AsmHalt`) with `returndata = memory[off, off+sz)` — the in-place
    `asmExpandMemory` is a no-op. -/
theorem asmReturnOp_ok {off sz stk s}
    (hs : s.stack = off :: sz :: stk)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmReturnOp s = AsmResult.AsmHalt
      { s with stack := stk, returndata := s.memory.readWithPadding off.toNat sz.toNat, memory := s.memory } := by
  have hmem : (if sz.toNat = 0 then s.memory
               else asmExpandMemory (off.toNat + sz.toNat) s.memory) = s.memory := by
    rcases hcov with h0 | hc
    · rw [if_pos h0]
    · by_cases h0 : sz.toNat = 0
      · rw [if_pos h0]
      · rw [if_neg h0, asmExpandMemory_of_covered _ _ hc]
  simp only [asmReturnOp, hs, hmem]

/-- `asmRevertOp` companion of `asmReturnOp_ok` (aborts via `AsmRevert`). -/
theorem asmRevertOp_ok {off sz stk s}
    (hs : s.stack = off :: sz :: stk)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmRevertOp s = AsmResult.AsmRevert
      { s with stack := stk, returndata := s.memory.readWithPadding off.toNat sz.toNat, memory := s.memory } := by
  have hmem : (if sz.toNat = 0 then s.memory
               else asmExpandMemory (off.toNat + sz.toNat) s.memory) = s.memory := by
    rcases hcov with h0 | hc
    · rw [if_pos h0]
    · by_cases h0 : sz.toNat = 0
      · rw [if_pos h0]
      · rw [if_neg h0, asmExpandMemory_of_covered _ _ hc]
  simp only [asmRevertOp, hs, hmem]

/-- **RETURN terminal relation**: the returned memory slice matches. Venom `RETURN` halts with
    `returndata = vs.memory[off,off+sz)`, asm halts with `as.memory[off,off+sz)`; `memoryRel` +
    the slice below `fnEom` (`hsafe`) give equality (`memoryRel_readWithPadding_slice`); the other
    observable fields are unchanged on both sides. -/
theorem venomAsmRel_return {lo ps vs as} {off sz : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlen : sz.toNat < USize.size) :
    venomAsmTerminalRel
      (haltState (setReturndata (readMemory off.toNat sz.toNat vs) vs))
      { as with stack := rest, returndata := as.memory.readWithPadding off.toNat sz.toNat, memory := as.memory } := by
  obtain ⟨_, _, hMem, hAcc, hTrans, _, hLog, _, _, _, _, _⟩ := hrel
  refine ⟨hAcc, hTrans, ?_, hLog⟩
  show as.memory.readWithPadding off.toNat sz.toNat = readMemory off.toNat sz.toNat vs
  unfold readMemory
  exact (memoryRel_readWithPadding_slice hMem hsafe hlen).symm

/-- **REVERT terminal relation** (the `RevertAbort` companion of `venomAsmRel_return`). -/
theorem venomAsmRel_revert {lo ps vs as} {off sz : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlen : sz.toNat < USize.size) :
    venomAsmTerminalRel
      (revertState (setReturndata (readMemory off.toNat sz.toNat vs) vs))
      { as with stack := rest, returndata := as.memory.readWithPadding off.toNat sz.toNat, memory := as.memory } := by
  obtain ⟨_, _, hMem, hAcc, hTrans, _, hLog, _, _, _, _, _⟩ := hrel
  refine ⟨hAcc, hTrans, ?_, hLog⟩
  show as.memory.readWithPadding off.toNat sz.toNat = readMemory off.toNat sz.toNat vs
  unfold readMemory
  exact (memoryRel_readWithPadding_slice hMem hsafe hlen).symm

/-- The runnable RETURN terminal sim: running the emitted `[SOEmit "RETURN"]` from a state with
    `off`/`sz` on top halts (`AsmHalt`) with observable effects matching the Venom `RETURN` result
    (`venomAsmTerminalRel`, returndata = the memory slice). The operand-carrying analog of the STOP
    leg of `hasm_stop`; `off`/`sz` are positioned by the standard input-emission. -/
theorem emit_return_sim {ps lo vs as prog off sz rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlen : sz.toNat < USize.size)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "RETURN"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "RETURN"]).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (setReturndata (readMemory off.toNat sz.toNat vs) vs)) as' := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨{ as with stack := rest, returndata := as.memory.readWithPadding off.toNat sz.toNat, memory := as.memory }, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    unfold runAsm
    rw [asmStep_return_ok hpc hget, asmReturnOp_ok hstack hcov]
  · exact venomAsmRel_return hrel hsafe hlen

/-- The runnable REVERT terminal sim (the `AsmRevert` companion of `emit_return_sim`). -/
theorem emit_revert_sim {ps lo vs as prog off sz rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hlen : sz.toNat < USize.size)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "REVERT"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "REVERT"]).length offsetToPc prog as
             = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel (revertState (setReturndata (readMemory off.toNat sz.toNat vs) vs)) as' := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨{ as with stack := rest, returndata := as.memory.readWithPadding off.toNat sz.toNat, memory := as.memory }, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    unfold runAsm
    rw [asmStep_revert_ok hpc hget, asmRevertOp_ok hstack hcov]
  · exact venomAsmRel_revert hrel hsafe hlen

/-! ## SELFDESTRUCT — single-operand terminal (account transfer)

`SELFDESTRUCT` pops the beneficiary address and halts, transferring the contract's balance to it
(`selfdestruct`). The asm side now implements it (`asmSelfdestruct`, reusing the Venom `selfdestruct`
on the converted state), so the terminal-rel obligation is the `accounts` match: both sides apply the
same pure `selfdestruct` to equal `accounts`/`callCtx`. No memory is touched (unlike RETURN/REVERT). -/

/-- `selfdestruct`'s output `accounts` is a pure function of the input `accounts` and the executing
    contract (`callCtx.contract`). The SELFDESTRUCT analog of `sstore_accounts_congr`. -/
theorem selfdestruct_accounts_congr (addr : bytes32) {s1 s2 : VenomState}
    (ha : s1.accounts = s2.accounts) (hc : s1.callCtx = s2.callCtx) :
    (selfdestruct addr s1).accounts = (selfdestruct addr s2).accounts := by
  simp only [selfdestruct, ha, hc]

/-- `asmStep` dispatch for `SELFDESTRUCT`. -/
theorem asmStep_selfdestruct_ok {offsetToPc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SELFDESTRUCT") :
    asmStep offsetToPc prog s = asmSelfdestruct s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmSelfdestruct` on a 1+-deep stack pops the beneficiary and halts with the transferred accounts. -/
theorem asmSelfdestruct_ok {addr stk s} (hs : s.stack = addr :: stk) :
    asmSelfdestruct s = AsmResult.AsmHalt
      { asmNext s with stack := stk, accounts := (selfdestruct addr s.toVenomState).accounts } := by
  unfold asmSelfdestruct; rw [hs]

/-- The Venom step of a `SELFDESTRUCT` with operand valued `addr` is `Halt (haltState (selfdestruct
    addr v))` — bridges the inline `stepInstBase` arm to the named helper. -/
theorem stepInstBase_selfdestruct {inst : Instruction} {v : VenomState} {op : Operand} {addr : bytes32}
    (hsd : inst.opcode = Opcode.SELFDESTRUCT)
    (hops : inst.operands = [op])
    (hv : evalOperand op v = some addr) :
    stepInstBase inst v = ExecResult.Halt (haltState (selfdestruct addr v)) := by
  simp only [stepInstBase, hsd, hops, hv]; rfl

/-- **The SELFDESTRUCT terminal relation**: the post-destruct accounts match. Both sides apply the
    same `selfdestruct` to equal `accounts`/`callCtx` (`selfdestruct_accounts_congr`); the other
    observable fields are unchanged on both sides. -/
theorem venomAsmRel_selfdestruct {lo ps vs as} {addr : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = addr :: rest) :
    venomAsmTerminalRel (haltState (selfdestruct addr vs))
      { asmNext as with stack := rest, accounts := (selfdestruct addr as.toVenomState).accounts } := by
  obtain ⟨_, _, _, hAcc, hTrans, hRet, hLog, hCall, _, _, _, _⟩ := hrel
  exact ⟨selfdestruct_accounts_congr addr hAcc hCall, hTrans, hRet, hLog⟩

/-- The runnable SELFDESTRUCT terminal sim: running the emitted `[SOEmit "SELFDESTRUCT"]` from a state
    with the beneficiary on top halts (`AsmHalt`) with the transferred accounts matching the Venom
    `SELFDESTRUCT` result (`venomAsmTerminalRel`). -/
theorem emit_selfdestruct_sim {ps lo vs as prog} {addr : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = addr :: rest)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "SELFDESTRUCT"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "SELFDESTRUCT"]).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (selfdestruct addr vs)) as' := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨{ asmNext as with stack := rest, accounts := (selfdestruct addr as.toVenomState).accounts }, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    unfold runAsm
    rw [asmStep_selfdestruct_ok hpc hget, asmSelfdestruct_ok hstack]
  · exact venomAsmRel_selfdestruct hrel hstack

/-! ## Stack-op simulation: DUP

`doDup` is the input-emission workhorse (`emitOneInput`'s live-var case duplicates an
operand already on the stack). For `dist ≤ 15` it emits a single `DUP(dist+1)`, which
pushes `asmStack[dist]` — matching the plan-side `stackDup dist` — so `venomAsmRel` is
preserved via `planStackRel_dup`. The DUP analog of `doSwap_sim`'s small case (the
`dist > 15` spill-chunk case mirrors `doSwap_big_sim` and is deferred). -/

/-- Single-step `asmStep` on `AsmOp (dupName n)` (1 ≤ n ≤ 16) dispatches to
    `asmDup (n-1)` (mirrors `asmStep_swap_ok`). -/
theorem asmStep_dup_ok {offsetToPc prog s n}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp (dupName n))
    (hn0 : 0 < n) (hn16 : n ≤ 16) :
    asmStep offsetToPc prog s = asmDup (n - 1) s := by
  interval_cases n <;> unfold asmStep <;> rw [dif_pos hpc, hprog] <;> rfl

/-- `doDup` simulation (small case, `dist ≤ 15`): the emitted `DUP(dist+1)` pushes
    `asmStack[dist]`, matching the plan-side `stackDup dist` — `venomAsmRel` preserved via
    `planStackRel_dup`. -/
theorem doDup_sim {dist ps ps' ops labelOffsets vs as prog}
    (hdup : doDup dist ps = (ops, ps'))
    (hsmall : dist ≤ 15)
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : dist < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have hdo : doDup dist ps
      = ([StackOp.SODup (dist + 1)], { ps with stack := stackDup dist ps.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  rw [hdo] at hdup
  obtain ⟨rfl, rfl⟩ := hdup
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlenas : dist < as.stack.length := by rw [← hStk.1]; exact hlen
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK ({ asmNext as with stack := as.stack.get ⟨dist, hlenas⟩ :: as.stack }) := by
    rw [asmStep_dup_ok hpc hget (by omega) (by omega), Nat.add_sub_cancel]
    unfold asmDup; rw [dif_pos hlenas]
  refine ⟨{ asmNext as with stack := as.stack.get ⟨dist, hlenas⟩ :: as.stack }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · refine ⟨?_, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
    have hps := planStackRel_dup hStk hlen
    rwa [List_get!_eq_get as.stack dist hlenas] at hps
  · rfl

/-- **A `DUP` step preserves asm memory.** `asmDup` only pushes a copied stack element
    (`{ asmNext as with stack := … }`), so the `runAsm` result of the single emitted `DUP` has
    `memory = as.memory`. The memory-preservation companion of `doDup_sim` (kept separate so its
    callers' conclusions are unchanged); threaded through input-emission so a downstream
    `RETURN`/`REVERT` can carry an `as.memory` coverage hypothesis to the post-emission state. -/
theorem doDup_runAsm_mem {dist : Nat} {as as' : AsmState} {prog : List AsmInst}
    (hsmall : dist ≤ 15)
    (hlenas : dist < as.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SODup (dist + 1)]))
    (hrun : runAsm (executePlan [StackOp.SODup (dist + 1)]).length offsetToPc prog as
              = AsmResult.AsmOK as') :
    as'.memory = as.memory := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK ({ asmNext as with stack := as.stack.get ⟨dist, hlenas⟩ :: as.stack }) := by
    rw [asmStep_dup_ok hpc hget (by omega) (by omega), Nat.add_sub_cancel]
    unfold asmDup; rw [dif_pos hlenas]
  have hr : runAsm (executePlan [StackOp.SODup (dist + 1)]).length offsetToPc prog as
      = AsmResult.AsmOK ({ asmNext as with stack := as.stack.get ⟨dist, hlenas⟩ :: as.stack }) := by
    show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  rw [hr] at hrun; injection hrun with hrun; rw [← hrun]; rfl

/-! ## Input emission

`emitInputPlan` brings an instruction's operands to the top of the stack (left to
right), one `emitOneInput` per operand. The main per-operand step is the live-var case:
an operand already on the stack (and not spilled) is duplicated via `doDup` — so its sim
composes `doDup_sim`. (The literal/label push cases and the spilled-restore case follow.) -/

/-- `emitOneInput` simulation, the live-var-on-stack case (operand not spilled): the
    operand is duplicated to TOS via `doDup`, preserving `venomAsmRel` (composes
    `doDup_sim`). -/
theorem emitOneInput_sim_var {opc nextLiveness v ps ops ps' dist labelOffsets vs as prog}
    (hnospill : alookup' ps.spilled (Operand.Var v) = none)
    (hlive : nextLiveness.contains v = true)
    (hdepth : stackGetDepth (Operand.Var v) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hemit : emitOneInput opc nextLiveness (Operand.Var v) ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : dist < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have hemiteq : emitOneInput opc nextLiveness (Operand.Var v) ps = doDup dist ps := by
    rcases hdd : doDup dist ps with ⟨dupOps, ps2⟩
    unfold emitOneInput
    simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlive, if_true, hdepth, hdd, List.nil_append]
  rw [hemiteq] at hemit
  exact doDup_sim hemit hsmall hrel hlen hblock

/-- **`emitOneInput` sim for a SPILLED live var** — the missing connective for spilling. When the input
    var is spilled, `emitOneInput` first `doRestore`s it (`SORestore` = PUSH slot + MLOAD, pushing the
    var freshly on top) then DUPs the restored value; this composes the proven `doRestore_sim` +
    `doDup_sim`. Complements `emitOneInput_sim_var` (which assumes `hnospill`), covering the case every
    existing body producer excludes. `hspillWf` (32-aligned, in-bounds spill slots) is the runtime
    precondition, exactly as `doRestore_sim` needs. -/
theorem emitOneInput_sim_var_spilled {opc nextLiveness v ps ops ps' off labelOffsets vs as prog}
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nextLiveness.contains v = true)
    (hemit : emitOneInput opc nextLiveness (Operand.Var v) ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  set ps1 : PlanState := (doRestore (Operand.Var v) ps).2 with hps1def
  have hres : doRestore (Operand.Var v) ps = ([StackOp.SORestore off], ps1) := by
    rw [hps1def]; unfold doRestore; rw [hspill]
  have hps1stack : ps1.stack = stackPush (Operand.Var v) ps.stack := by
    rw [hps1def]; unfold doRestore; rw [hspill]
  have hgd : stackGetDepth (Operand.Var v) ps1.stack = some 0 := by
    rw [hps1stack]
    simp only [stackGetDepth, stackPush, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, stackFind, beq_self_eq_true, if_true]
  set ps2 : PlanState := (doDup 0 ps1).2 with hps2def
  have hdd : doDup 0 ps1 = ([StackOp.SODup 1], ps2) := by
    rw [hps2def]; unfold doDup; rw [if_pos (by omega : (0 : Nat) ≤ 15)]
  have hemiteq : emitOneInput opc nextLiveness (Operand.Var v) ps
      = ([StackOp.SORestore off] ++ [StackOp.SODup 1], ps2) := by
    unfold emitOneInput
    simp only [isVarOperand, hspill, Option.isSome_some, Bool.and_true, if_true, hres, hlive,
      hgd, hdd]
  rw [hemiteq, Prod.mk.injEq] at hemit
  obtain ⟨hops, hps'⟩ := hemit
  subst ops; subst ps'
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hbR, hbD⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunR, hrelR, hpcR⟩ := doRestore_sim (offsetToPc := offsetToPc) hres hrel hbR hspillWf
  have hbD' : asmBlockAt prog as1.pc (executePlan [StackOp.SODup 1]) := by rw [hpcR]; exact hbD
  have hlen1 : 0 < ps1.stack.length := by rw [hps1stack, stackPush, List.length_append]; simp
  obtain ⟨as2, hrunD, hrelD, hpcD⟩ := doDup_sim (offsetToPc := offsetToPc) hdd (by omega) hrelR hlen1 hbD'
  refine ⟨as2, ?_, hrelD, ?_⟩
  · rw [List.length_append]; exact runAsm_compose hrunR hrunD
  · rw [List.length_append, hpcD, hpcR]; omega

/-- **Explicit reduction of `emitOneInput` on a spilled live var.** Restore (`SORestore off`, pushing
    the var, dropping its spill entry, freeing the slot) then DUP the restored value (`SODup 1`). The
    var ends on top (`ps.stack ++ [Var v, Var v]`); its spill entry is removed. Extracted from the body
    of `emitOneInput_sim_var_spilled` so the fold can compose the resulting state with later operands. -/
theorem emitOneInput_var_spilled_eq {opc nl v ps off}
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nl.contains v = true) :
    emitOneInput opc nl (Operand.Var v) ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
  set ps1 : PlanState := (doRestore (Operand.Var v) ps).2 with hps1def
  have hres : doRestore (Operand.Var v) ps = ([StackOp.SORestore off], ps1) := by
    rw [hps1def]; unfold doRestore; rw [hspill]
  have hps1stack : ps1.stack = stackPush (Operand.Var v) ps.stack := by
    rw [hps1def]; unfold doRestore; rw [hspill]
  have hgd : stackGetDepth (Operand.Var v) ps1.stack = some 0 := by
    rw [hps1stack]
    simp only [stackGetDepth, stackPush, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, stackFind, beq_self_eq_true, if_true]
  set ps2 : PlanState := (doDup 0 ps1).2 with hps2def
  have hdd : doDup 0 ps1 = ([StackOp.SODup 1], ps2) := by
    rw [hps2def]; unfold doDup; rw [if_pos (by omega : (0 : Nat) ≤ 15)]
  have hemiteq : emitOneInput opc nl (Operand.Var v) ps
      = ([StackOp.SORestore off] ++ [StackOp.SODup 1], ps2) := by
    unfold emitOneInput
    simp only [isVarOperand, hspill, Option.isSome_some, Bool.and_true, if_true, hres, hlive, hgd, hdd]
  rw [hemiteq]
  congr 1
  rw [hps2def]; unfold doDup; rw [if_pos (by omega : (0 : Nat) ≤ 15)]
  simp only []
  rw [hps1def]; unfold doRestore; rw [hspill]
  simp only [stackPush, stackDup, stackPeek]
  congr 1
  · rw [show ((ps.stack ++ [Operand.Var v]).length - 1 - 0) = ps.stack.length from by simp]
    rw [show (ps.stack ++ [Operand.Var v])[ps.stack.length]! = Operand.Var v from by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp]
    simp

/-- `UInt256` round-trip: `ofNat` of `toNat` is the identity. -/
theorem uint256_ofNat_toNat_self (w : bytes32) : UInt256.ofNat w.toNat = w := by
  obtain ⟨⟨n, hn⟩⟩ := w
  simp only [UInt256.toNat, UInt256.ofNat, Id.run, Fin.ofNat, UInt256.size] at *
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hn)

/-- `emitOneInput` simulation, the literal case: `PUSH <v>` pushes exactly `v` (codec
    round-trip via `pushed_offset_toNat`), preserving `venomAsmRel` via `planStackRel_push`
    (`operandVal (Lit v) = some v`). -/
theorem emitOneInput_sim_lit {opc nextLiveness v ps ops ps' labelOffsets vs as prog}
    (hemit : emitOneInput opc nextLiveness (Operand.Lit v) ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have hemiteq : emitOneInput opc nextLiveness (Operand.Lit v) ps
      = ([StackOp.SOPush (Operand.Lit v)], { ps with stack := stackPush (Operand.Lit v) ps.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, Bool.false_and, Bool.false_eq_true, if_false, List.nil_append]
  rw [hemiteq] at hemit
  obtain ⟨rfl, rfl⟩ := hemit
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hvlt : v.toNat < 2 ^ 256 := by
    exact v.val.isLt
  have hWv : wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes v.toNat).length)
      (0 : byte) ++ encodeNumBytes v.toNat)) = v := by
    rw [← uint256_ofNat_toNat_self (wordOfBytes _), pushed_offset_toNat v.toNat hvlt,
        uint256_ofNat_toNat_self]
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK ({ asmNext as with stack := v :: as.stack }) := by
    rw [asmStep_push_ok hpc hget, hWv]; rfl
  refine ⟨{ asmNext as with stack := v :: as.stack }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact ⟨planStackRel_push hStk rfl, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk,
      hCode, hPrev⟩
  · rfl

/-- `emitOneInput` simulation, the no-op var cases (not spilled, and either dead or not
    on the stack): no ops emitted, `venomAsmRel` trivially preserved. -/
theorem emitOneInput_sim_var_noop {opc nextLiveness v ps ops ps' labelOffsets vs as prog}
    (hnospill : alookup' ps.spilled (Operand.Var v) = none)
    (hcond : nextLiveness.contains v = false ∨ stackGetDepth (Operand.Var v) ps.stack = none)
    (hemit : emitOneInput opc nextLiveness (Operand.Var v) ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have hemiteq : emitOneInput opc nextLiveness (Operand.Var v) ps = ([], ps) := by
    unfold emitOneInput
    rcases hcond with hdead | hnone
    · simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
        if_false, hdead, List.nil_append]
    · simp only [isVarOperand, hnospill, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
        if_false, hnone]
      split <;> rfl
  rw [hemiteq] at hemit
  obtain ⟨rfl, rfl⟩ := hemit
  exact ⟨as, rfl, hrel, rfl⟩

/-- `emitInputPlan` simulation: the per-operand `emitOneInput` sims compose over the
    operand list via the fold harness `foldl_ops_sim'`. The residual `hstep` is the
    per-operand `emitOneInput` sim — discharged, for a no-spill var/literal operand
    list, by `emitOneInput_sim_var` / `_lit` / `_var_noop`. -/
theorem emitInputPlan_sim {opc operands nextLiveness ps ops ps' labelOffsets vs as prog}
    (hfold : emitInputPlan opc operands nextLiveness ps = (ops, ps'))
    (hstep : ∀ (op : Operand) (p : PlanState) (s : AsmState),
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (emitOneInput opc nextLiveness op p).1) →
        ∃ s', runAsm (executePlan (emitOneInput opc nextLiveness op p).1).length
                offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (emitOneInput opc nextLiveness op p).2 vs s' ∧
              s'.pc = s.pc + (executePlan (emitOneInput opc nextLiveness op p).1).length)
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length :=
  foldl_ops_sim' labelOffsets vs prog offsetToPc
    (fun p op => emitOneInput opc nextLiveness op p) hstep hfold hrel hblock

/-! ## Compute step (binops)

The opcode-emit step for a 2-input arithmetic/bitwise opcode: `generateEmitOps` produces
`[SOEmit name]`, whose asm is the corresponding `AsmOp name`, dispatching to `asmBinop f`
— which pops two and pushes `f a b`. With the inputs already on top (from `emitInputPlan`
+ reorder), `f a b` is exactly the Venom `execPure2 f` result, and `planStackRel_binop`
places it. These are the asm-step dispatch lemmas; the value tie is
`lookupVar_updateVar_self`. -/

/-- `asmBinop` on a 2+-deep stack pops two and pushes the result. -/
theorem asmBinop_ok {f : bytes32 → bytes32 → bytes32} {a b stk s} (hs : s.stack = a :: b :: stk) :
    asmBinop f s = AsmResult.AsmOK ({ asmNext s with stack := f a b :: stk }) := by
  unfold asmBinop; rw [hs]

/-- `asmStep` dispatch for `ADD`. -/
theorem asmStep_add_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "ADD") :
    asmStep o2pc prog s = asmBinop (· + ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SUB`. -/
theorem asmStep_sub_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SUB") :
    asmStep o2pc prog s = asmBinop (· - ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `MUL`. -/
theorem asmStep_mul_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MUL") :
    asmStep o2pc prog s = asmBinop (· * ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_and_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "AND") :
    asmStep o2pc prog s = asmBinop (· &&& ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_or_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "OR") :
    asmStep o2pc prog s = asmBinop (· ||| ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_xor_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "XOR") :
    asmStep o2pc prog s = asmBinop (· ^^^ ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_eq_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "EQ") :
    asmStep o2pc prog s = asmBinop (fun x y => boolToWord (x = y)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_signextend_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SIGNEXTEND") :
    asmStep o2pc prog s = asmBinop signExtend s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_byte_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BYTE") :
    asmStep o2pc prog s = asmBinop evmByte s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `DIV`. -/
theorem asmStep_div_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "DIV") :
    asmStep o2pc prog s = asmBinop safeDiv s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `MOD`. -/
theorem asmStep_mod_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MOD") :
    asmStep o2pc prog s = asmBinop safeMod s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SDIV`. -/
theorem asmStep_sdiv_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SDIV") :
    asmStep o2pc prog s = asmBinop safeSdiv s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SMOD`. -/
theorem asmStep_smod_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SMOD") :
    asmStep o2pc prog s = asmBinop safeSmod s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `EXP`. -/
theorem asmStep_exp_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "EXP") :
    asmStep o2pc prog s = asmBinop UInt256.exp s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SLT`. -/
theorem asmStep_slt_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SLT") :
    asmStep o2pc prog s = asmBinop UInt256.slt s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SGT`. -/
theorem asmStep_sgt_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SGT") :
    asmStep o2pc prog s = asmBinop UInt256.sgt s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SHL` (shift-first, EVM-faithful: `λ a b => b <<< a`). -/
theorem asmStep_shl_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SHL") :
    asmStep o2pc prog s = asmBinop (fun a b => b <<< a) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SHR`. -/
theorem asmStep_shr_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SHR") :
    asmStep o2pc prog s = asmBinop (fun a b => b >>> a) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `SAR`. -/
theorem asmStep_sar_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SAR") :
    asmStep o2pc prog s = asmBinop UInt256.sar s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `LT` (the asm `x.toNat < y.toNat` form is defeq to Venom's `x < y`). -/
theorem asmStep_lt_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "LT") :
    asmStep o2pc prog s = asmBinop (fun x y => boolToWord (x < y)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `GT`. -/
theorem asmStep_gt_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "GT") :
    asmStep o2pc prog s = asmBinop (fun x y => boolToWord (x > y)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmTernop` on a 3+-deep stack pops three and pushes the result (3-input companion of
    `asmBinop_ok`). -/
theorem asmTernop_ok {f : bytes32 → bytes32 → bytes32 → bytes32} {a b c stk s}
    (hs : s.stack = a :: b :: c :: stk) :
    asmTernop f s = AsmResult.AsmOK ({ asmNext s with stack := f a b c :: stk }) := by
  unfold asmTernop; rw [hs]

/-- `asmStep` dispatch for `ADDMOD`. -/
theorem asmStep_addmod_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "ADDMOD") :
    asmStep o2pc prog s = asmTernop addmod s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `MULMOD`. -/
theorem asmStep_mulmod_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MULMOD") :
    asmStep o2pc prog s = asmTernop mulmod s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **The compute-step relation**: with the two inputs on top of the asm stack
    (`as.stack = v1 :: v2 :: rest`) and a fresh output `out`, the post-binop state
    (asm pushes `f v1 v2` and advances the pc, plan pops the two inputs and pushes
    `Var out`, venom sets `out := f v1 v2`) preserves `venomAsmRel`. Composes
    `venomAsmRel_updateVar` (lower stack + spill/mem/shared untouched by the fresh var)
    with `planStackRel_binop` (the new top) and `lookupVar_updateVar_self` (the value
    tie). This is the heart of a 2-input regular opcode's compute step. -/
theorem venomAsmRel_binop {lo ps vs as out} {f : bytes32 → bytes32 → bytes32} {v1 v2 rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v1 :: v2 :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) }
      (updateVar out (f v1 v2) vs)
      { asmNext as with stack := f v1 v2 :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (f v1 v2)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (f v1 v2) vs) lo (Operand.Var out) = some (f v1 v2) := by
    simp only [operandVal]; exact lookupVar_updateVar_self vs out (f v1 v2)
  have hps := planStackRel_binop hStk' hlen2 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for a 2-input opcode: running the emitted `[SOEmit name]`
    (whose asm `AsmOp name` dispatches to `asmBinop f`) from a state with the inputs on top
    advances the pc by 1 and preserves `venomAsmRel`. Wraps `venomAsmRel_binop` with the
    `runAsm` / dispatch plumbing; the per-opcode `hdisp` is supplied by `asmStep_add_ok`,
    `asmStep_sub_ok`, … . -/
theorem emit_binop_sim {name out v1 v2 rest ps lo vs as prog} {f : bytes32 → bytes32 → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v1 :: v2 :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmBinop f as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) }
             (updateVar out (f v1 v2) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := f v1 v2 :: rest } := by
    rw [hdisp hpc hget]; exact asmBinop_ok hstack
  refine ⟨{ asmNext as with stack := f v1 v2 :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_binop hrel hstack hfresh hspill
  · rfl

/-! ## Ternary-op compute step (3-input companions of the binop core)

The 3-input analogs of `asmTernop_ok` / `venomAsmRel_binop` / `emit_binop_sim`, for `ADDMOD` and
`MULMOD`. Same shape as the binop, but the asm pops three (`asmTernop`) and the plan pops three
(`stackPop 3`); there is no operand-order subtlety beyond the uniform reversal already applied. -/

/-- **The 3-input compute-step relation**: with the three inputs on top of the asm stack
    (`as.stack = v1 :: v2 :: v3 :: rest`) and a fresh output `out`, the post-ternop state
    (asm pushes `f v1 v2 v3` and advances the pc, plan pops the three inputs and pushes
    `Var out`, venom sets `out := f v1 v2 v3`) preserves `venomAsmRel`. The 3-input companion of
    `venomAsmRel_binop`: composes `venomAsmRel_updateVar`, `planStackRel_ternop`, and
    `lookupVar_updateVar_self`. -/
theorem venomAsmRel_ternop {lo ps vs as out} {f : bytes32 → bytes32 → bytes32 → bytes32}
    {v1 v2 v3 rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v1 :: v2 :: v3 :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 3 ps.stack) }
      (updateVar out (f v1 v2 v3) vs)
      { asmNext as with stack := f v1 v2 v3 :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen3 : 3 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (f v1 v2 v3)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (f v1 v2 v3) vs) lo (Operand.Var out) = some (f v1 v2 v3) := by
    simp only [operandVal]; exact lookupVar_updateVar_self vs out (f v1 v2 v3)
  have hps := planStackRel_ternop hStk' hlen3 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for a 3-input opcode: running the emitted `[SOEmit name]`
    (whose asm `AsmOp name` dispatches to `asmTernop f`) from a state with the inputs on top
    advances the pc by 1 and preserves `venomAsmRel`. The 3-input companion of `emit_binop_sim`;
    the per-opcode `hdisp` is supplied by `asmStep_addmod_ok` / `asmStep_mulmod_ok`. -/
theorem emit_3op_sim {name out v1 v2 v3 rest ps lo vs as prog}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v1 :: v2 :: v3 :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmTernop f as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 3 ps.stack) }
             (updateVar out (f v1 v2 v3) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := f v1 v2 v3 :: rest } := by
    rw [hdisp hpc hget]; exact asmTernop_ok hstack
  refine ⟨{ asmNext as with stack := f v1 v2 v3 :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_ternop hrel hstack hfresh hspill
  · rfl

/-! ## Value-push compute step (0-input, 1-output context ops: CALLVALUE/CALLER/ADDRESS/GAS/…)

The 0-input companions of the binop/ternop cores. A context op reads a single value from the state
(`execRead0`) and binds it to its output; the plan is just `[SOEmit name]`, whose asm (`asmPushVal`)
pushes the value. Because `venomAsmRel` equates the shared-state fields the value is read from
(`as.callCtx = vs.callCtx`, etc.), the Venom-read value equals the asm-pushed value, so the fresh
output is bound consistently — the 0-pop, 1-push analog of `venomAsmRel_binop`. -/

/-- **The 0-input compute-step relation**: pushing a value `v` (with a fresh output `out`) preserves
    `venomAsmRel` — the asm pushes `v` and advances the pc, the plan pushes `Var out`, and venom sets
    `out := v`. The 0-pop companion of `venomAsmRel_binop`/`venomAsmRel_ternop`, via
    `venomAsmRel_updateVar` + `planStackRel_push` + `lookupVar_updateVar_self`. -/
theorem venomAsmRel_read0 {lo ps vs as out v}
    (hrel : venomAsmRel lo ps vs as)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
      (updateVar out v vs) { asmNext as with stack := v :: as.stack } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out v
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out v vs) lo (Operand.Var out) = some v := by
    simp only [operandVal]; exact lookupVar_updateVar_self vs out v
  exact planStackRel_push hStk' hout

/-- The runnable sim for a 0-input value-push opcode: running `[SOEmit name]` (whose `AsmOp name`
    dispatches to `asmPushVal v`) advances the pc by 1 and preserves `venomAsmRel` with `out := v`.
    The 0-input companion of `emit_binop_sim`/`emit_3op_sim`; the per-opcode `hdisp` is supplied by
    `asmStep_callvalue_ok` (and its CALLER/ADDRESS/… siblings). -/
theorem emit_read0_sim {name out v ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal v as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack } (updateVar out v vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK { asmNext as with stack := v :: as.stack } := by
    rw [hdisp hpc hget]; rfl
  refine ⟨{ asmNext as with stack := v :: as.stack }, ?_, venomAsmRel_read0 hrel hfresh hspill, rfl⟩
  show runAsm 1 offsetToPc prog as = _
  rw [runAsm_succ_ok hpc hstep]; rfl

/-- `emit_read0_sim` with the (trivially true) memory-preservation conjunct exposed: the pushed
    value never touches memory, but the plain `∃ as'` hides it — consumers that must TRACK the
    asm memory size across the push (MEMTOP) need it named. -/
theorem emit_read0_sim_mem {name out v ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal v as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack } (updateVar out v vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length ∧
           as'.memory = as.memory := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK { asmNext as with stack := v :: as.stack } := by
    rw [hdisp hpc hget]; rfl
  refine ⟨{ asmNext as with stack := v :: as.stack }, ?_, venomAsmRel_read0 hrel hfresh hspill, rfl, rfl⟩
  show runAsm 1 offsetToPc prog as = _
  rw [runAsm_succ_ok hpc hstep]; rfl

/-- `emit_ctx_push_sim` with the memory-preservation conjunct (see `emit_read0_sim_mem`). -/
theorem emit_ctx_push_sim_mem {name out ps lo vs as prog offsetToPc}
    {fAsm : AsmState → bytes32} {fV : VenomState → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdispatch : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal (fAsm as) as)
    (hfield : fAsm as = fV vs) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (fV vs) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length ∧
           as'.memory = as.memory := by
  have hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal (fV vs) as := by
    intro h hg; rw [hdispatch h hg, hfield]
  exact emit_read0_sim_mem (v := fV vs) hrel hfresh hspill hblock hdisp

/-- `asmStep` at `AsmOp "MSIZE"` dispatches to the rounded-memory-size push (the `hdisp` for the
    MEMTOP capstone's `emit_ctx_push_sim_mem` step). -/
theorem asmStep_msize_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MSIZE") :
    asmStep o2pc prog s = asmPushVal (EvmYul.UInt256.ofNat ((s.memory.size + 31) / 32 * 32)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` at `AsmOp "CALLVALUE"` dispatches to `asmPushVal s.callCtx.callvalue` (the concrete
    `hdisp` for `emit_read0_sim` on `CALLVALUE`; CALLER/ADDRESS/GAS/ORIGIN/… are identical up to the
    pushed field). -/
theorem asmStep_callvalue_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALLVALUE") :
    asmStep offsetToPc prog s = asmPushVal s.callCtx.callvalue s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-! ### The full 0-input context-field push class (CALLER, ADDRESS, …, CODESIZE)

Every 0-input EVM environment read that the asm interpreter models as `asmPushVal (<field of as>)`:
the Venom side is `execRead0 (fun s => <same field of s>)`, so the pushed value is a pure function of
a *shared/equated* state field (`callCtx`, `txCtx`, `blockCtx`, `code`, or `returndata`). The generic
`emit_ctx_push_sim` reduces each to (i) the per-op `asmStep_<op>_ok` dispatch and (ii) the relevant
`venomAsmRel` field-equality conjunct; the concrete `emit_<op>_sim`s below instantiate it. (The
1-input environment reads — BLOCKHASH, BALANCE, CALLDATALOAD, EXTCODE* — are *not* modelled by
`asmStep` (they fall through to "unknown opcode"), so they have no sim until the asm layer adds them.)
-/

/-- Generic 0-input context-field push: given an asm dispatch producing `asmPushVal (fAsm as)` and a
    field equality `fAsm as = fV vs` (from an equated `venomAsmRel` conjunct), the emitted
    `[SOEmit name]` preserves `venomAsmRel` with the Venom-side `updateVar out (fV vs)`. The many-op
    generalisation of `emit_read0_sim`. -/
theorem emit_ctx_push_sim {name out ps lo vs as prog offsetToPc}
    {fAsm : AsmState → bytes32} {fV : VenomState → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdispatch : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal (fAsm as) as)
    (hfield : fAsm as = fV vs) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (fV vs) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  have hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmPushVal (fV vs) as := by
    intro h hg; rw [hdispatch h hg, hfield]
  exact emit_read0_sim (v := fV vs) hrel hfresh hspill hblock hdisp

/-- `asmStep` dispatch lemmas for the 0-input context pushes (each `unfold; dif_pos; rfl`). -/
theorem asmStep_caller_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALLER") :
    asmStep o2pc prog s = asmPushVal (addressToWord s.callCtx.caller) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_address_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "ADDRESS") :
    asmStep o2pc prog s = asmPushVal (addressToWord s.callCtx.contract) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_gas_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "GAS") :
    asmStep o2pc prog s = asmPushVal (EvmYul.UInt256.ofNat s.callCtx.gas) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_calldatasize_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALLDATASIZE") :
    asmStep o2pc prog s = asmPushVal (EvmYul.UInt256.ofNat s.callCtx.calldata.length) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_origin_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "ORIGIN") :
    asmStep o2pc prog s = asmPushVal (addressToWord s.txCtx.origin) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_gasprice_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "GASPRICE") :
    asmStep o2pc prog s = asmPushVal s.txCtx.gasprice s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_chainid_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CHAINID") :
    asmStep o2pc prog s = asmPushVal s.txCtx.chainid s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_coinbase_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "COINBASE") :
    asmStep o2pc prog s = asmPushVal (addressToWord s.blockCtx.coinbase) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_timestamp_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "TIMESTAMP") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.timestamp s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_number_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "NUMBER") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.number s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_gaslimit_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "GASLIMIT") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.gaslimit s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_basefee_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BASEFEE") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.basefee s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_prevrandao_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "PREVRANDAO") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.prevrandao s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_blobbasefee_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BLOBBASEFEE") :
    asmStep o2pc prog s = asmPushVal s.blockCtx.blobbasefee s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_blockhash_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BLOCKHASH") :
    asmStep o2pc prog s = asmStateUnop (λ v s => s.blockCtx.blockhash v.toNat) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_codesize_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CODESIZE") :
    asmStep o2pc prog s = asmPushVal (EvmYul.UInt256.ofNat s.code.length) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl
theorem asmStep_returndatasize_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "RETURNDATASIZE") :
    asmStep o2pc prog s = asmPushVal (EvmYul.UInt256.ofNat s.returndata.size) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- The runnable context-push sims. Each is `emit_ctx_push_sim` at the matching dispatch lemma and the
    matching `venomAsmRel` conjunct (callCtx `.2⁷.1`, txCtx `.2⁸.1`, blockCtx `.2⁹.1`,
    returndata `.2⁵.1`, code `.2¹⁰.1`). -/
theorem emit_callvalue_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALLVALUE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CALLVALUE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.callCtx.callvalue vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CALLVALUE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.callCtx.callvalue) (fV := fun s => s.callCtx.callvalue)
    hrel hfresh hspill hblock asmStep_callvalue_ok (by simp only [hrel.2.2.2.2.2.2.2.1])
theorem emit_caller_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALLER"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CALLER"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (addressToWord vs.callCtx.caller) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CALLER"]).length :=
  emit_ctx_push_sim (fAsm := fun s => addressToWord s.callCtx.caller)
    (fV := fun s => addressToWord s.callCtx.caller)
    hrel hfresh hspill hblock asmStep_caller_ok (by simp only [hrel.2.2.2.2.2.2.2.1])
theorem emit_address_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "ADDRESS"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "ADDRESS"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (addressToWord vs.callCtx.contract) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "ADDRESS"]).length :=
  emit_ctx_push_sim (fAsm := fun s => addressToWord s.callCtx.contract)
    (fV := fun s => addressToWord s.callCtx.contract)
    hrel hfresh hspill hblock asmStep_address_ok (by simp only [hrel.2.2.2.2.2.2.2.1])
theorem emit_gas_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "GAS"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "GAS"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (EvmYul.UInt256.ofNat vs.callCtx.gas) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "GAS"]).length :=
  emit_ctx_push_sim (fAsm := fun s => EvmYul.UInt256.ofNat s.callCtx.gas)
    (fV := fun s => EvmYul.UInt256.ofNat s.callCtx.gas)
    hrel hfresh hspill hblock asmStep_gas_ok (by simp only [hrel.2.2.2.2.2.2.2.1])
theorem emit_calldatasize_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALLDATASIZE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CALLDATASIZE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (EvmYul.UInt256.ofNat vs.callCtx.calldata.length) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CALLDATASIZE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length)
    (fV := fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length)
    hrel hfresh hspill hblock asmStep_calldatasize_ok (by simp only [hrel.2.2.2.2.2.2.2.1])
theorem emit_origin_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "ORIGIN"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "ORIGIN"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (addressToWord vs.txCtx.origin) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "ORIGIN"]).length :=
  emit_ctx_push_sim (fAsm := fun s => addressToWord s.txCtx.origin)
    (fV := fun s => addressToWord s.txCtx.origin)
    hrel hfresh hspill hblock asmStep_origin_ok (by simp only [hrel.2.2.2.2.2.2.2.2.1])
theorem emit_gasprice_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "GASPRICE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "GASPRICE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.txCtx.gasprice vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "GASPRICE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.txCtx.gasprice) (fV := fun s => s.txCtx.gasprice)
    hrel hfresh hspill hblock asmStep_gasprice_ok (by simp only [hrel.2.2.2.2.2.2.2.2.1])
theorem emit_chainid_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CHAINID"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CHAINID"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.txCtx.chainid vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CHAINID"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.txCtx.chainid) (fV := fun s => s.txCtx.chainid)
    hrel hfresh hspill hblock asmStep_chainid_ok (by simp only [hrel.2.2.2.2.2.2.2.2.1])
theorem emit_coinbase_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "COINBASE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "COINBASE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (addressToWord vs.blockCtx.coinbase) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "COINBASE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => addressToWord s.blockCtx.coinbase)
    (fV := fun s => addressToWord s.blockCtx.coinbase)
    hrel hfresh hspill hblock asmStep_coinbase_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.1])
theorem emit_timestamp_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "TIMESTAMP"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "TIMESTAMP"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.blockCtx.timestamp vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "TIMESTAMP"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.blockCtx.timestamp) (fV := fun s => s.blockCtx.timestamp)
    hrel hfresh hspill hblock asmStep_timestamp_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.1])
theorem emit_number_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "NUMBER"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "NUMBER"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.blockCtx.number vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "NUMBER"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.blockCtx.number) (fV := fun s => s.blockCtx.number)
    hrel hfresh hspill hblock asmStep_number_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.1])
theorem emit_gaslimit_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "GASLIMIT"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "GASLIMIT"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.blockCtx.gaslimit vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "GASLIMIT"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.blockCtx.gaslimit) (fV := fun s => s.blockCtx.gaslimit)
    hrel hfresh hspill hblock asmStep_gaslimit_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.1])
theorem emit_basefee_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "BASEFEE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "BASEFEE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out vs.blockCtx.basefee vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "BASEFEE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => s.blockCtx.basefee) (fV := fun s => s.blockCtx.basefee)
    hrel hfresh hspill hblock asmStep_basefee_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.1])
theorem emit_returndatasize_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "RETURNDATASIZE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "RETURNDATASIZE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (EvmYul.UInt256.ofNat vs.returndata.size) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "RETURNDATASIZE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => EvmYul.UInt256.ofNat s.returndata.size)
    (fV := fun s => EvmYul.UInt256.ofNat s.returndata.size)
    hrel hfresh hspill hblock asmStep_returndatasize_ok (by simp only [hrel.2.2.2.2.2.1])
theorem emit_codesize_sim {out ps lo vs as prog offsetToPc}
    (hrel : venomAsmRel lo ps vs as) (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CODESIZE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CODESIZE"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) ps.stack }
             (updateVar out (EvmYul.UInt256.ofNat vs.code.length) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CODESIZE"]).length :=
  emit_ctx_push_sim (fAsm := fun s => EvmYul.UInt256.ofNat s.code.length)
    (fV := fun s => EvmYul.UInt256.ofNat s.code.length)
    hrel hfresh hspill hblock asmStep_codesize_ok (by simp only [hrel.2.2.2.2.2.2.2.2.2.2.1])

/-! ## Store-op compute step (SSTORE — no-output `execWrite2` to shared state)

A store consumes two operands and produces no output (net stack `0`); it modifies *shared* state
(storage) rather than the stack-relevant `vars`/`memory`. `venomAsmRel`'s stack/spill/memory
conjuncts read `vs.vars`/`vs.memory` (unchanged by `sstore`, so they stay related *definitionally*),
and the `accounts` conjunct is preserved because the asm and Venom stores apply the *same* `sstore`
to the *same* starting `accounts` (`sstore_accounts_congr`). This is the store analog of
`venomAsmRel_binop`. -/

/-- `sstore`'s output `accounts` is a pure function of the input `accounts` and `callCtx.contract`
    (it reads the contract address and storage, writes storage), so it agrees on states that agree on
    those. The asm/Venom bridge for the `accounts` conjunct. -/
theorem sstore_accounts_congr (key value : bytes32) {s1 s2 : VenomState}
    (ha : s1.accounts = s2.accounts) (hc : s1.callCtx = s2.callCtx) :
    (sstore key value s1).accounts = (sstore key value s2).accounts := by
  simp only [sstore, ha, hc]

/-- `asmStep` dispatch for `SSTORE`. -/
theorem asmStep_sstore_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SSTORE") :
    asmStep o2pc prog s = asmSstore s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmSstore` on a 2+-deep stack pops `key`/`value` and writes storage (no push). -/
theorem asmSstore_ok {key value stk s} (hs : s.stack = key :: value :: stk) :
    asmSstore s
      = AsmResult.AsmOK
          { asmNext s with stack := stk, accounts := (sstore key value s.toVenomState).accounts } := by
  unfold asmSstore; rw [hs]

/-- **The store compute-step relation** (SSTORE): with `key`/`value` on top of the asm stack
    (`as.stack = key :: value :: rest`), the post-store state (asm pops two and writes storage, plan
    pops two, venom `sstore key value`) preserves `venomAsmRel`. The stack/spill/memory conjuncts are
    preserved because `sstore` leaves `vars`/`memory` untouched (so `operandVal` is unchanged); the
    `accounts` conjunct is `sstore_accounts_congr`; every other shared field is untouched on both
    sides. The store analog of `venomAsmRel_binop` (no output pushed). -/
theorem venomAsmRel_sstore {lo ps vs as} {key value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: value :: rest) :
    venomAsmRel lo { ps with stack := stackPop 2 ps.stack }
      (sstore key value vs)
      { asmNext as with stack := rest, accounts := (sstore key value as.toVenomState).accounts } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen2
  rw [hstack] at hps
  refine ⟨?_, ?_, ?_, ?_, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · -- planStackRel: sstore leaves vars untouched, so operandVal is unchanged (defeq)
    exact hps
  · -- planSpillRel: spilled/asm-memory unchanged; operandVal unchanged
    exact hSpill
  · -- memoryRel: vs.memory / as.memory / alloc all unchanged
    exact hMem
  · -- accounts: both apply the same sstore to the same starting accounts
    exact sstore_accounts_congr key value hAcc hCall

/-- The Venom step of an SSTORE with operands valued `key`/`value` is `sstore key value`. Bridges
    `stepInstBase` to the `sstore` form the store sim concludes on (`hdispatch` ties the opcode to
    `execWrite2 sstore`, proved by unfolding `stepInstBase`). -/
theorem stepInstBase_sstore {inst : Instruction} {v : VenomState} {op1 op2 : Operand}
    {key value : bytes32}
    (hdispatch : stepInstBase inst v = execWrite2 (fun k val s => sstore k val s) inst v)
    (hops : inst.operands = [op1, op2])
    (hv1 : evalOperand op1 v = some key)
    (hv2 : evalOperand op2 v = some value) :
    stepInstBase inst v = ExecResult.OK (sstore key value v) := by
  rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [hv1, hv2]

/-- The runnable compute-step sim for SSTORE: running the emitted `[SOEmit "SSTORE"]` from a state
    with `key`/`value` on top advances the pc by 1 and preserves `venomAsmRel` across the store. The
    store analog of `emit_binop_sim`; `hdisp` is supplied by `asmStep_sstore_ok`. -/
theorem emit_sstore_sim {ps lo vs as prog key value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: value :: rest)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "SSTORE"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "SSTORE" →
              asmStep offsetToPc prog as = asmSstore as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "SSTORE"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (sstore key value vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "SSTORE"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK
          { asmNext as with stack := rest, accounts := (sstore key value as.toVenomState).accounts } := by
    rw [hdisp hpc hget]; exact asmSstore_ok hstack
  refine ⟨{ asmNext as with stack := rest, accounts := (sstore key value as.toVenomState).accounts }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_sstore hrel hstack
  · rfl

/-! ## Store-op compute step (TSTORE — transient storage, the SSTORE companion)

TSTORE is the transient-storage analog of SSTORE (it has no separate asm function — `asmStep` writes
`transient` inline). Same shape: pop two, write shared state, no push; `tstore` leaves `vars`/`memory`
untouched (so the stack/spill/memory conjuncts hold definitionally) and `accounts` untouched (so that
conjunct is the original); only `transient` changes, via `tstore_transient_congr`. -/

/-- `tstore`'s output `transient` is a pure function of the input `transient` and `callCtx.contract`. -/
theorem tstore_transient_congr (key value : bytes32) {s1 s2 : VenomState}
    (ht : s1.transient = s2.transient) (hc : s1.callCtx = s2.callCtx) :
    (tstore key value s1).transient = (tstore key value s2).transient := by
  simp only [tstore, ht, hc]

/-- `asmStep` at `TSTORE` with `key`/`value` on top pops two and writes transient storage (inline in
    `asmStep` — no separate `asmTstore`). -/
theorem asmStep_tstore_ok {o2pc prog s} {key value stk} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "TSTORE")
    (hs : s.stack = key :: value :: stk) :
    asmStep o2pc prog s
      = AsmResult.AsmOK
          { asmNext s with stack := stk, transient := (tstore key value s.toVenomState).transient } := by
  unfold asmStep; rw [dif_pos hpc, hprog, hs]; rfl

/-- **The store compute-step relation** (TSTORE): the transient-storage companion of
    `venomAsmRel_sstore`. The changed conjunct is `transient` (via `tstore_transient_congr`); `accounts`
    is now the unchanged original. -/
theorem venomAsmRel_tstore {lo ps vs as} {key value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: value :: rest) :
    venomAsmRel lo { ps with stack := stackPop 2 ps.stack }
      (tstore key value vs)
      { asmNext as with stack := rest, transient := (tstore key value as.toVenomState).transient } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen2
  rw [hstack] at hps
  refine ⟨?_, ?_, ?_, hAcc, ?_, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · exact hps
  · exact hSpill
  · exact hMem
  · exact tstore_transient_congr key value hTrans hCall

/-- The Venom step of a TSTORE with operands valued `key`/`value` is `tstore key value`. -/
theorem stepInstBase_tstore {inst : Instruction} {v : VenomState} {op1 op2 : Operand}
    {key value : bytes32}
    (hdispatch : stepInstBase inst v = execWrite2 (fun k val s => tstore k val s) inst v)
    (hops : inst.operands = [op1, op2])
    (hv1 : evalOperand op1 v = some key)
    (hv2 : evalOperand op2 v = some value) :
    stepInstBase inst v = ExecResult.OK (tstore key value v) := by
  rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [hv1, hv2]

/-- The runnable compute-step sim for TSTORE (the SSTORE companion). -/
theorem emit_tstore_sim {ps lo vs as prog key value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: value :: rest)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "TSTORE"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "TSTORE"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (tstore key value vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "TSTORE"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  refine ⟨{ asmNext as with stack := rest, transient := (tstore key value as.toVenomState).transient }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc (asmStep_tstore_ok hpc hget hstack)]; rfl
  · exact venomAsmRel_tstore hrel hstack
  · rfl

/-! ## MSTORE — memory-safety (the spill-region frame)

MSTORE writes a 32-byte word to *user* memory at a runtime offset `off`. Unlike SSTORE/TSTORE it
touches `memory` — the very component the spill allocator co-inhabits. The safety obligation is
`stepMemSafe`: a Venom MSTORE must leave the spill region `[fnEom, nextOffset)` byte-for-byte intact,
so `planSpillRel` survives. For Vyper-generated code the user heap lives strictly below `fnEom`
(`off + 32 ≤ fnEom`), which makes the write window `[off, off+32)` disjoint from every spill slot —
`mstore_readByte_frame` then gives the byte-level frame. -/

/-- **MSTORE is spill-safe when it writes below the spill region.** If the 32-byte MSTORE window
    `[off, off+32)` lies below `fnEom` (`off + 32 ≤ fnEom`, the Vyper user-heap-below-spill layout)
    and memory already covers the write start (`off ≤ memory.size`), the store leaves every byte of
    the spill region `[fnEom, nextOffset)` unchanged — discharging `stepMemSafe`, the per-instruction
    obligation that keeps `planSpillRel` alive across a user MSTORE. -/
theorem mstore_stepMemSafe {alloc : SpillAlloc} {off : Nat} {value : bytes32} {vs : VenomState}
    (hcov : off ≤ vs.memory.size)
    (hsafe : off + 32 ≤ alloc.fnEom) :
    stepMemSafe alloc vs (mstore off value vs) := by
  intro i hi
  show readByte i vs.memory = readByte i (mstore off value vs).memory
  have hmem : (mstore off value vs).memory = (wordToBytes value).write 0 vs.memory off 32 := by
    simp only [mstore, writeMemoryWithExpansion, length_wordToBytes]
  rw [hmem, mstore_readByte_frame value vs.memory off i hcov (Or.inr (by omega))]

/-- `asmMstore` on a 2+-deep stack, with asm memory already covering the rounded write
    window (`hcov` — true under `spillMemCovered`), pops `offset`/`value`, leaves the
    in-place `asmExpandMemory` a no-op (`asmExpandMemory_of_covered`), and writes the
    word at `offset.toNat`. The MSTORE analog of `asmSstore_ok`. -/
theorem asmMstore_ok {offset value stk s}
    (hs : s.stack = offset :: value :: stk)
    (hcov : ((offset.toNat + 32 + 31) / 32) * 32 ≤ s.memory.size) :
    asmMstore s
      = AsmResult.AsmOK
          { asmNext s with stack := stk, memory := (wordToBytes value).write 0 s.memory offset.toNat 32 } := by
  unfold asmMstore
  rw [hs]
  simp only [asmExpandMemory_of_covered (offset.toNat + 32) s.memory hcov]

/-- **The MSTORE compute-step relation.** With `offset`/`value` on top of the asm stack,
    the post-store state (asm pops two and writes the word to user memory at
    `offset.toNat`, plan pops two, venom `mstore offset.toNat value`) preserves
    `venomAsmRel`, **given memory-safety**:
      * `hcovV`/`hcovA` — both memories cover the write start (`off ≤ size`);
      * `hsafe` — the write window `[off, off+32)` lies below the spill region (`off+32 ≤ fnEom`);
      * `hspillReg` — every live spill slot lies at or above `fnEom`.
    `planStackRel` survives because `mstore` leaves `vars` untouched (`operandVal` unchanged);
    `planSpillRel` survives because the write window is disjoint from every spill slot
    (`mstore_readWithPadding_frame`); `memoryRel` survives by write-congruence
    (`mstore_readByte_congr`); all other shared fields are untouched. The memory analog of
    `venomAsmRel_sstore`. -/
theorem venomAsmRel_mstore {lo ps vs as} {offset value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : offset.toNat ≤ as.memory.size)
    (hsafe : offset.toNat + 32 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off') :
    venomAsmRel lo { ps with stack := stackPop 2 ps.stack }
      (mstore offset.toNat value vs)
      { asmNext as with stack := rest, memory := (wordToBytes value).write 0 as.memory offset.toNat 32 } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen2
  rw [hstack] at hps
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · -- planStackRel: mstore leaves vars untouched, so operandVal is unchanged (defeq)
    exact hps
  · -- planSpillRel: the MSTORE window is disjoint from every (≥ fnEom) spill slot
    intro op off' hlook
    obtain ⟨v, hopv, hval⟩ := hSpill op off' hlook
    refine ⟨v, hopv, ?_⟩
    rw [mstore_readWithPadding_frame value as.memory offset.toNat off' hcovA
          (Or.inr (by have := hspillReg op off' hlook; omega))]
    exact hval
  · -- memoryRel: identical word written to both memories, equal outside the spill region
    intro i hi
    have hvmem : (mstore offset.toNat value vs).memory
        = (wordToBytes value).write 0 vs.memory offset.toNat 32 := by
      simp only [mstore, writeMemoryWithExpansion, length_wordToBytes]
    rw [hvmem]
    exact mstore_readByte_congr value vs.memory as.memory offset.toNat i hcovV hcovA (hMem i hi)

/-- **The no-spill MSTORE step + relation, without any `fnEom` bound.** Under `noSpill`
    (`StackDiscH`'s first component) `planSpillRel` is vacuous, and `memoryRel` survives the
    paired identical write unconditionally — the `hsafe : off+32 ≤ fnEom` of
    `venomAsmRel_mstore` exists only to protect spilled slots, which this regime never has.
    Stated against `asmMstore`'s actual (expanding) result; `readByte_asmExpandMemory` bridges
    the expansion. Coverage hypotheses are trivial (`Nat.zero_le`) at literal offset 0. -/
theorem asmMstore_noSpill_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {offset value : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : offset.toNat ≤ (asmExpandMemory (offset.toNat + 32) as.memory).size)
    (hro : ((offset.toNat + 32 + 31) / 32) * 32 < USize.size) :
    asmMstore as = AsmResult.AsmOK { asmNext as with stack := rest, memory := (wordToBytes value).write 0 (asmExpandMemory (offset.toNat + 32) as.memory) offset.toNat 32 }
    ∧ venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (mstore offset.toNat value vs)
        { asmNext as with stack := rest, memory := (wordToBytes value).write 0 (asmExpandMemory (offset.toNat + 32) as.memory) offset.toNat 32 } := by
  constructor
  · simp only [asmMstore, hstack]
  · obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
    have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
    have hps := planStackRel_popN hStk hlen2
    rw [hstack] at hps
    refine ⟨hps, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
    · -- planSpillRel: vacuous under noSpill
      intro op off' hlook
      rw [show AssocList.lookup Operand Nat ps.spilled op = alookup' ps.spilled op from rfl,
          hnospill op] at hlook
      exact absurd hlook (by simp)
    · -- memoryRel: paired identical write; expansion is readByte-invariant
      intro i hi
      have hvmem : (mstore offset.toNat value vs).memory
          = (wordToBytes value).write 0 vs.memory offset.toNat 32 := by
        simp only [mstore, writeMemoryWithExpansion, length_wordToBytes]
      rw [hvmem]
      refine mstore_readByte_congr value vs.memory
        (asmExpandMemory (offset.toNat + 32) as.memory) offset.toNat i hcovV hcovA ?_
      rw [readByte_asmExpandMemory i _ as.memory hro]
      exact hMem i hi

/-- The runnable compute-step sim for MSTORE: running the emitted `[SOEmit "MSTORE"]` from a
    state with `offset`/`value` on top advances the pc by 1 and preserves `venomAsmRel` across
    the (memory-safe) store. The memory analog of `emit_sstore_sim`; `hdisp` is supplied by
    `asmStep_mstore_ok`, the covered-memory write by `asmMstore_ok`. -/
theorem emit_mstore_sim {ps lo vs as prog offset value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : ((offset.toNat + 32 + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : offset.toNat + 32 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "MSTORE"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "MSTORE" →
              asmStep offsetToPc prog as = asmMstore as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "MSTORE"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (mstore offset.toNat value vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "MSTORE"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hcovA' : offset.toNat ≤ as.memory.size := by omega
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := (wordToBytes value).write 0 as.memory offset.toNat 32 } := by
    rw [hdisp hpc hget]; exact asmMstore_ok hstack hcovA
  refine ⟨{ asmNext as with stack := rest, memory := (wordToBytes value).write 0 as.memory offset.toNat 32 }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_mstore hrel hstack hcovV hcovA' hsafe hspillReg
  · rfl

/-! ## Single-byte store compute step (MSTORE8)

The 1-byte sibling of MSTORE: pops `offset`/`value` and writes the single byte `value mod 256` at
`offset`. Same shape as `venomAsmRel_mstore`, but the write width is 1 rather than 32, so the memory
frame / congruence go through the *generic* `byteArray_readWithPadding_write_disjoint` /
`readByte_write_congr` (source size 1) instead of the 32-byte `mstore_*` specialisations. The proof
rewrites the Venom state to an explicit record up front (`hstate`) so the stack/other conjuncts never
force whnf of the symbolic byte-write. -/

theorem asmStep_mstore8_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MSTORE8") :
    asmStep o2pc prog s = asmMstore8 s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmMstore8` on a 2+-deep stack whose 1-byte window is covered: expansion is a no-op, so it pops
    two and writes `value mod 256` at `offset.toNat`. -/
theorem asmMstore8_ok {offset value stk s} (hs : s.stack = offset :: value :: stk)
    (hcov : ((offset.toNat + 1 + 31) / 32) * 32 ≤ s.memory.size) :
    asmMstore8 s = AsmResult.AsmOK { asmNext s with stack := stk, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 s.memory offset.toNat 1 } := by
  unfold asmMstore8; rw [hs]
  simp only [asmExpandMemory_of_covered (offset.toNat + 1) s.memory hcov]

/-- **The MSTORE8 compute-step relation.** The 1-byte analog of `venomAsmRel_mstore`. -/
theorem venomAsmRel_mstore8 {lo ps vs as} {offset value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : offset.toNat ≤ as.memory.size)
    (hsafe : offset.toNat + 1 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off') :
    venomAsmRel lo { ps with stack := stackPop 2 ps.stack }
      (mstore8 offset.toNat value vs)
      { asmNext as with stack := rest, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 as.memory offset.toNat 1 } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen2
  rw [hstack] at hps
  have hsz1 : (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).size = 1 := rfl
  -- rewrite the Venom state to an explicit record so the conjuncts never whnf `mstore8`'s byte-write
  have hstate : mstore8 offset.toNat value vs
      = { vs with memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 vs.memory offset.toNat 1 } := by
    show writeMemoryWithExpansion offset.toNat ⟨#[UInt8.ofNat (value.toNat % 256)]⟩ vs = _
    unfold writeMemoryWithExpansion
    rw [hsz1]
  rw [hstate]
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · exact hps
  · intro op off' hlook
    obtain ⟨v, hopv, hval⟩ := hSpill op off' hlook
    refine ⟨v, hopv, ?_⟩
    have hd := EvmYul.byteArray_readWithPadding_write_disjoint
      (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray) as.memory offset.toNat off' 32
      (by rw [hsz1]; norm_num) hcovA (by rcases USize.size_eq with h | h <;> omega)
      (Or.inr (by rw [hsz1]; have := hspillReg op off' hlook; omega))
    rw [hsz1] at hd
    rw [hd]; exact hval
  · intro i hi
    have hc := readByte_write_congr (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray)
      vs.memory as.memory offset.toNat i (by rw [hsz1]; norm_num) hcovV hcovA (hMem i hi)
    rw [hsz1] at hc
    exact hc

/-- The runnable compute-step sim for MSTORE8; `hdisp` from `asmStep_mstore8_ok`, the covered write
    from `asmMstore8_ok`. -/
theorem emit_mstore8_sim {ps lo vs as prog offset value rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : ((offset.toNat + 1 + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : offset.toNat + 1 ≤ ps.alloc.fnEom)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "MSTORE8"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "MSTORE8" →
              asmStep offsetToPc prog as = asmMstore8 as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "MSTORE8"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (mstore8 offset.toNat value vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "MSTORE8"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hcovA' : offset.toNat ≤ as.memory.size := by omega
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 as.memory offset.toNat 1 } := by
    rw [hdisp hpc hget]; exact asmMstore8_ok hstack hcovA
  refine ⟨{ asmNext as with stack := rest, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 as.memory offset.toNat 1 }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_mstore8 hrel hstack hcovV hcovA' hsafe hspillReg
  · rfl

/-! ## Memory-load compute step (MLOAD — a memory read to a fresh output)

MLOAD pops an `offset` and pushes `mload offset`, a *memory* read. Unlike a pure `unop`, the pushed
value depends on memory, not just the popped operand: the asm side reads `as.memory`, the Venom side
reads `vs.memory`, and the two agree only under `memoryRel`. When the read window lies below the spill
region (`offset+32 ≤ fnEom`) and asm memory already covers it, the expansion is a no-op and the two
reads produce the same word (`memoryRel_readWithPadding_slice`), so the pushed value matches and memory
is unchanged on both sides. The memory-read analog of `venomAsmRel_unop`. -/

/-- `asmMload` on a 1+-deep stack whose read window is already covered: the expansion is a no-op, so
    it pops `offset` and pushes `wordOfBytes (mem.readWithPadding offset.toNat 32)`, memory unchanged.
    The load analog of `asmMstore_ok`. -/
theorem asmMload_ok {offset stk s} (hs : s.stack = offset :: stk)
    (hcov : ((offset.toNat + 32 + 31) / 32) * 32 ≤ s.memory.size) :
    asmMload s
      = AsmResult.AsmOK
          { asmNext s with stack := wordOfBytes (s.memory.readWithPadding offset.toNat 32) :: stk, memory := s.memory } := by
  unfold asmMload
  rw [hs]
  simp only [asmExpandMemory_of_covered (offset.toNat + 32) s.memory hcov]

/-- **The MLOAD compute-step relation.** With `offset` on top of the asm stack and a fresh output
    `out`, the post-load state (asm pops `offset` and pushes the loaded word, plan pops one and pushes
    `Var out`, venom `updateVar out (mload offset.toNat vs)`) preserves `venomAsmRel`. The pushed
    values agree because the read window is below the spill region (`memoryRel_readWithPadding_slice`);
    memory is unchanged on both sides (covered ⇒ expansion no-op). The memory-read analog of
    `venomAsmRel_unop`. -/
theorem venomAsmRel_mload {lo ps vs as out} {offset rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: rest)
    (hbelow : offset.toNat + 32 ≤ ps.alloc.fnEom)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (mload offset.toNat vs) vs)
      { asmNext as with stack := wordOfBytes (as.memory.readWithPadding offset.toNat 32) :: rest, memory := as.memory } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hread : vs.memory.readWithPadding offset.toNat 32 = as.memory.readWithPadding offset.toNat 32 :=
    memoryRel_readWithPadding_slice hMem hbelow (by rcases USize.size_eq with h | h <;> omega)
  have hval : mload offset.toNat vs = wordOfBytes (as.memory.readWithPadding offset.toNat 32) := by
    simp only [mload, readMemory, hread]
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (mload offset.toNat vs)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (mload offset.toNat vs) vs) lo (Operand.Var out)
      = some (wordOfBytes (as.memory.readWithPadding offset.toNat 32)) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for MLOAD: running the emitted `[SOEmit "MLOAD"]` from a state with
    `offset` on top advances the pc by 1 and preserves `venomAsmRel` across the (covered, below-spill)
    load. The memory-read analog of `emit_mstore_sim`; `hdisp` is supplied by `asmStep_mload_ok`, the
    covered read by `asmMload_ok`. -/
theorem emit_mload_sim {ps lo vs as prog offset rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: rest)
    (hcov : ((offset.toNat + 32 + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + 32 ≤ ps.alloc.fnEom)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "MLOAD"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "MLOAD" →
              asmStep offsetToPc prog as = asmMload as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "MLOAD"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (mload offset.toNat vs) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "MLOAD"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := wordOfBytes (as.memory.readWithPadding offset.toNat 32) :: rest, memory := as.memory } := by
    rw [hdisp hpc hget]; exact asmMload_ok hstack hcov
  refine ⟨{ asmNext as with stack := wordOfBytes (as.memory.readWithPadding offset.toNat 32) :: rest, memory := as.memory }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_mload hrel hstack hbelow hfresh hspill
  · rfl

/-! ## SHA3 compute step (a 2-input, variable-length memory *hash*)

The memory-hashing twin of MLOAD, but 2-input (offset, size) and variable-length: pop `offset`/`size`,
push `keccak256` of the memory slice. Under coverage the `asmSha3` expansion is a no-op
(`asmExpandMemory_of_covered`), so memory is unchanged; the reads agree below the spill region
(`memoryRel_readWithPadding_slice`), so the hashes agree (`keccak256` is applied to equal bytes — it
stays opaque, no keccak axiom). The stack shape is a non-commutative binop's (pop 2, push 1). -/

/-- `asmSha3` under coverage: the `asmExpandMemory` is a no-op, so memory is unchanged and the pushed
    value is `keccak256` of the (unexpanded) memory slice. The 2-input, variable-length twin of
    `asmMload_ok`. -/
theorem asmSha3_ok {off sz stk s} (hs : s.stack = off :: sz :: stk)
    (hcov : ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmSha3 s = AsmResult.AsmOK { asmNext s with
        stack := keccak256 (s.memory.readWithPadding off.toNat sz.toNat) :: stk, memory := s.memory } := by
  unfold asmSha3; rw [hs]
  have hmem : (if sz.toNat = 0 then s.memory
      else asmExpandMemory (off.toNat + sz.toNat) s.memory) = s.memory := by
    split
    · rfl
    · exact asmExpandMemory_of_covered (off.toNat + sz.toNat) s.memory hcov
  simp only [hmem]

/-- `asmStep` on a resolved `SHA3` op dispatches to `asmSha3`. -/
theorem asmStep_sha3_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SHA3") :
    asmStep o2pc prog s = asmSha3 s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **The SHA3 compute-step relation.** Pop `offset` and `size`, push `keccak256` of the memory slice.
    The reads agree (below-spill, `memoryRel_readWithPadding_slice`) so the hashes agree; memory is
    unchanged (covered ⇒ expansion no-op). The 2-input, memory-hashing twin of `venomAsmRel_mload`. -/
theorem venomAsmRel_sha3 {lo ps vs as out} {off sz rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = off :: sz :: rest)
    (hbelow : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hsize : sz.toNat < USize.size)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) }
      (updateVar out (keccak256 (readMemory off.toNat sz.toNat vs)) vs)
      { asmNext as with
          stack := keccak256 (as.memory.readWithPadding off.toNat sz.toNat) :: rest, memory := as.memory } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hread : vs.memory.readWithPadding off.toNat sz.toNat
      = as.memory.readWithPadding off.toNat sz.toNat :=
    memoryRel_readWithPadding_slice hMem hbelow hsize
  have hval : keccak256 (readMemory off.toNat sz.toNat vs)
      = keccak256 (as.memory.readWithPadding off.toNat sz.toNat) := by
    simp only [readMemory, hread]
  have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (keccak256 (readMemory off.toNat sz.toNat vs))
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (keccak256 (readMemory off.toNat sz.toNat vs)) vs)
      lo (Operand.Var out)
      = some (keccak256 (as.memory.readWithPadding off.toNat sz.toNat)) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_binop hStk' hlen2 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for SHA3; `hdisp` is supplied by `asmStep_sha3_ok`. -/
theorem emit_sha3_sim {ps lo vs as prog off sz rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = off :: sz :: rest)
    (hcov : ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hsize : sz.toNat < USize.size)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "SHA3"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "SHA3" →
              asmStep offsetToPc prog as = asmSha3 as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "SHA3"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) }
             (updateVar out (keccak256 (readMemory off.toNat sz.toNat vs)) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "SHA3"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK { asmNext as with
      stack := keccak256 (as.memory.readWithPadding off.toNat sz.toNat) :: rest, memory := as.memory } := by
    rw [hdisp hpc hget]; exact asmSha3_ok hstack hcov
  refine ⟨{ asmNext as with
      stack := keccak256 (as.memory.readWithPadding off.toNat sz.toNat) :: rest, memory := as.memory },
    ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_sha3 hrel hstack hbelow hsize hfresh hspill
  · rfl

/-! ## Storage / transient load compute step (SLOAD, TLOAD — read shared state to a fresh output)

SLOAD/TLOAD pop a `key` and push a *shared-state* read (`sload`/`tload`), consuming no memory. Unlike
MLOAD there is no expansion: the read depends only on `accounts`+`callCtx.contract` (SLOAD) or
`transient`+`callCtx.contract` (TLOAD), all of which the `venomAsmRel` conjuncts equate between the
asm and Venom states, so the pushed values agree (`sload_congr`/`tload_congr`) with no memory or FFI
involved. The shared-state analogs of `venomAsmRel_mload`. -/

/-- `sload` reads only `accounts` and `callCtx.contract`, so it agrees on states agreeing on those. -/
theorem sload_congr (key : bytes32) {s1 s2 : VenomState}
    (ha : s1.accounts = s2.accounts) (hc : s1.callCtx = s2.callCtx) :
    sload key s1 = sload key s2 := by
  simp only [sload, contractStorage, ha, hc]

/-- `asmStep` dispatch for `SLOAD`. -/
theorem asmStep_sload_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SLOAD") :
    asmStep o2pc prog s = asmSload s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmSload` on a 1+-deep stack pops `key` and pushes `sload key` (read via `toVenomState`). -/
theorem asmSload_ok {key stk s} (hs : s.stack = key :: stk) :
    asmSload s = AsmResult.AsmOK { asmNext s with stack := sload key s.toVenomState :: stk } := by
  unfold asmSload; rw [hs]

/-- **The SLOAD compute-step relation.** With `key` on top and a fresh output `out`, the post-load
    state preserves `venomAsmRel`: the pushed storage read agrees (`sload_congr`, via the `accounts`
    and `callCtx` conjuncts); no memory is touched. The storage analog of `venomAsmRel_mload`. -/
theorem venomAsmRel_sload {lo ps vs as out} {key rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (sload key vs) vs)
      { asmNext as with stack := sload key as.toVenomState :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : sload key vs = sload key as.toVenomState := sload_congr key hAcc.symm hCall.symm
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (sload key vs)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (sload key vs) vs) lo (Operand.Var out)
      = some (sload key as.toVenomState) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for SLOAD; `hdisp` is supplied by `asmStep_sload_ok`. -/
theorem emit_sload_sim {ps lo vs as prog key rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "SLOAD"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "SLOAD" →
              asmStep offsetToPc prog as = asmSload as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "SLOAD"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (sload key vs) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "SLOAD"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := sload key as.toVenomState :: rest } := by
    rw [hdisp hpc hget]; exact asmSload_ok hstack
  refine ⟨{ asmNext as with stack := sload key as.toVenomState :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_sload hrel hstack hfresh hspill
  · rfl

/-- `tload` reads only `transient` and `callCtx.contract`, so it agrees on states agreeing on those. -/
theorem tload_congr (key : bytes32) {s1 s2 : VenomState}
    (ht : s1.transient = s2.transient) (hc : s1.callCtx = s2.callCtx) :
    tload key s1 = tload key s2 := by
  simp only [tload, contractTransient, ht, hc]

/-- `asmStateUnop` on a 1+-deep stack pops one and pushes `f a s` (the state-reading unop shape used
    by TLOAD and the many-field context ops). -/
theorem asmStateUnop_ok {f : bytes32 → AsmState → bytes32} {a stk s} (hs : s.stack = a :: stk) :
    asmStateUnop f s = AsmResult.AsmOK { asmNext s with stack := f a s :: stk } := by
  unfold asmStateUnop; rw [hs]

/-- `asmStep` dispatch for `TLOAD` (routes through `asmStateUnop … tload`). -/
theorem asmStep_tload_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "TLOAD") :
    asmStep o2pc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **The TLOAD compute-step relation.** The transient-storage twin of `venomAsmRel_sload`; the pushed
    read agrees via `tload_congr` (the `transient` and `callCtx` conjuncts). -/
theorem venomAsmRel_tload {lo ps vs as out} {key rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (tload key vs) vs)
      { asmNext as with stack := tload key as.toVenomState :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : tload key vs = tload key as.toVenomState := tload_congr key hTrans.symm hCall.symm
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (tload key vs)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (tload key vs) vs) lo (Operand.Var out)
      = some (tload key as.toVenomState) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for TLOAD; `hdisp` is supplied by `asmStep_tload_ok`. -/
theorem emit_tload_sim {ps lo vs as prog key rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "TLOAD"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
              asmStep offsetToPc prog as = asmStateUnop (fun k s => tload k s.toVenomState) as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "TLOAD"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (tload key vs) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "TLOAD"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := tload key as.toVenomState :: rest } := by
    rw [hdisp hpc hget]; exact asmStateUnop_ok hstack
  refine ⟨{ asmNext as with stack := tload key as.toVenomState :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_tload hrel hstack hfresh hspill
  · rfl

/-! ## BLOCKHASH (a 1-input read of `blockCtx.blockhash`)

Like TLOAD, a 1-input read into a fresh output, but of the block environment: the asm/Venom
reads agree via the `blockCtx` conjunct of `venomAsmRel` directly (no congr lemma needed). -/

/-- **The BLOCKHASH compute-step relation.** Pop `idx`, push `blockCtx.blockhash idx`; the
    reads agree via `as.blockCtx = vs.blockCtx`. The block-env twin of `venomAsmRel_tload`. -/
theorem venomAsmRel_blockhash {lo ps vs as out} {key rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (vs.blockCtx.blockhash key.toNat) vs)
      { asmNext as with stack := as.blockCtx.blockhash key.toNat :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : vs.blockCtx.blockhash key.toNat = as.blockCtx.blockhash key.toNat := by rw [hBlk]
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (vs.blockCtx.blockhash key.toNat)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (vs.blockCtx.blockhash key.toNat) vs) lo (Operand.Var out)
      = some (as.blockCtx.blockhash key.toNat) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for BLOCKHASH; `hdisp` is supplied by `asmStep_blockhash_ok`. -/
theorem emit_blockhash_sim {ps lo vs as prog key rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "BLOCKHASH"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "BLOCKHASH" →
              asmStep offsetToPc prog as = asmStateUnop (fun v s => s.blockCtx.blockhash v.toNat) as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "BLOCKHASH"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (vs.blockCtx.blockhash key.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "BLOCKHASH"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := as.blockCtx.blockhash key.toNat :: rest } := by
    rw [hdisp hpc hget]; exact asmStateUnop_ok hstack
  refine ⟨{ asmNext as with stack := as.blockCtx.blockhash key.toNat :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_blockhash hrel hstack hfresh hspill
  · rfl



/-! ## BLOBHASH (a 1-input read of `txCtx.blobhashes`, the tx-context blob-hash list) -/

/-- The BLOBHASH read value: the `idx`-th blob hash in the tx context (0 past the end).
    Matches the venom `Opcode.BLOBHASH` semantics inline, so `execRead1`/the asm case unfold to it. -/
def blobhashOf (tx : EvmYul.Venom.Hol.TxContext) (idx : Nat) : bytes32 :=
  if h : idx < tx.blobhashes.length then tx.blobhashes.get ⟨idx, h⟩ else ⟨0⟩

theorem asmStep_blobhash_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BLOBHASH") :
    asmStep o2pc prog s = asmStateUnop (λ v s => blobhashOf s.txCtx v.toNat) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem venomAsmRel_blobhash {lo ps vs as out} {key rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (blobhashOf vs.txCtx key.toNat) vs)
      { asmNext as with stack := blobhashOf as.txCtx key.toNat :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : blobhashOf vs.txCtx key.toNat = blobhashOf as.txCtx key.toNat := by rw [hTx]
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (blobhashOf vs.txCtx key.toNat)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (blobhashOf vs.txCtx key.toNat) vs) lo (Operand.Var out)
      = some (blobhashOf as.txCtx key.toNat) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for BLOBHASH; `hdisp` is supplied by `asmStep_blobhash_ok`. -/
theorem emit_blobhash_sim {ps lo vs as prog key rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "BLOBHASH"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "BLOBHASH" →
              asmStep offsetToPc prog as = asmStateUnop (fun v s => blobhashOf s.txCtx v.toNat) as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "BLOBHASH"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (blobhashOf vs.txCtx key.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "BLOBHASH"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := blobhashOf as.txCtx key.toNat :: rest } := by
    rw [hdisp hpc hget]; exact asmStateUnop_ok hstack
  refine ⟨{ asmNext as with stack := blobhashOf as.txCtx key.toNat :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_blobhash hrel hstack hfresh hspill
  · rfl

/-! ## CALLDATALOAD (a 1-input read of `callCtx.calldata`)

Like TLOAD, a 1-input read into a fresh output, but the read is a 32-byte word of `callCtx.calldata`
(no memory model): the asm/Venom reads agree via the `callCtx` conjunct of `venomAsmRel`. -/

/-- `asmStep` on a resolved `CALLDATALOAD` op reduces to the calldata-word `asmStateUnop`. -/
theorem asmStep_calldataload_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALLDATALOAD") :
    asmStep o2pc prog s = asmStateUnop (fun offset s =>
      wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **The CALLDATALOAD compute-step relation.** Pop `offset`, push the 32-byte calldata word; the reads
    agree via the `callCtx` conjunct (`as.callCtx = vs.callCtx`). The calldata twin of `venomAsmRel_tload`. -/
theorem venomAsmRel_calldataload {lo ps vs as out} {key rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (wordOfBytes
        ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) vs)
      { asmNext as with stack :=
          (wordOfBytes ((⟨as.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : wordOfBytes ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)
      = wordOfBytes ((⟨as.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32) := by
    rw [hCall]
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out
      (wordOfBytes ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32))
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out
      (wordOfBytes ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) vs)
      lo (Operand.Var out)
      = some (wordOfBytes ((⟨as.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for CALLDATALOAD; `hdisp` from `asmStep_calldataload_ok`. -/
theorem emit_calldataload_sim {ps lo vs as prog key rest out}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALLDATALOAD"]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp "CALLDATALOAD" →
              asmStep offsetToPc prog as = asmStateUnop (fun offset s =>
                wordOfBytes ((⟨s.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding offset.toNat 32)) as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CALLDATALOAD"]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (wordOfBytes
               ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CALLDATALOAD"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK { asmNext as with stack :=
      (wordOfBytes ((⟨as.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) :: rest } := by
    rw [hdisp hpc hget]; exact asmStateUnop_ok hstack
  refine ⟨{ asmNext as with stack :=
      (wordOfBytes ((⟨as.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding key.toNat 32)) :: rest },
    ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_calldataload hrel hstack hfresh hspill
  · rfl

/-! ## Account reads (BALANCE / EXTCODESIZE / EXTCODEHASH): a 1-input read of the accounts map

The account-query twins of the TLOAD/SLOAD reads: pop an address, push a pure function of the account
(balance / code length / code hash). The asm machine gained a case per opcode (`asmStateUnop` reading
`s.toVenomState.accounts`), and the asm/Venom reads agree via the `accounts` conjunct of `venomAsmRel`
(`as.accounts = vs.accounts`) — the account analog of `tload_congr`'s `transient` conjunct. The bridge
(`venomAsmRel_accountRead` / `emit_accountRead_sim`) is generic over the read `fRead`; only the
per-opcode `asmStep_*_ok` dispatch differs. -/

/-- `asmStep` on a resolved `BALANCE` op reduces to the account-balance `asmStateUnop`. -/
theorem asmStep_balance_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "BALANCE") :
    asmStep o2pc prog s = asmStateUnop (fun addr s =>
      EvmYul.UInt256.ofNat
        (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).balance) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **Generic account-read compute-step relation.** For any read that is a pure function of the address
    and the accounts map (`fRead`), the asm read (over `as.toVenomState.accounts`) agrees with the Venom
    read (over `vs.accounts`) via the `accounts` conjunct — the account analog of `tload_congr`'s
    `transient` conjunct. BALANCE/EXTCODESIZE/EXTCODEHASH instantiate `fRead`. -/
theorem venomAsmRel_accountRead {lo ps vs as out} {key rest} {fRead : bytes32 → Accounts → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (fRead key vs.accounts) vs)
      { asmNext as with stack := fRead key as.toVenomState.accounts :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hval : fRead key vs.accounts = fRead key as.toVenomState.accounts := by
    have hacc' : as.toVenomState.accounts = vs.accounts := hAcc
    rw [hacc']
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (fRead key vs.accounts)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (fRead key vs.accounts) vs) lo (Operand.Var out)
      = some (fRead key as.toVenomState.accounts) := by
    simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- **Generic account-read emit sim.** The runnable step for any account-read opcode `name` whose asm
    lowering is `asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts)`; `hdisp` is supplied
    by the per-opcode `asmStep_*_ok`. -/
theorem emit_accountRead_sim {ps lo vs as prog key rest out} {name : String}
    {fRead : bytes32 → Accounts → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = key :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as
                = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (fRead key vs.accounts) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := fRead key as.toVenomState.accounts :: rest } := by
    rw [hdisp hpc hget]; exact asmStateUnop_ok hstack
  refine ⟨{ asmNext as with stack := fRead key as.toVenomState.accounts :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_accountRead hrel hstack hfresh hspill
  · rfl

/-- `asmStep` on a resolved `EXTCODESIZE` op reduces to the account-code-length `asmStateUnop`. -/
theorem asmStep_extcodesize_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "EXTCODESIZE") :
    asmStep o2pc prog s = asmStateUnop (fun addr s =>
      EvmYul.UInt256.ofNat
        (lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts).code.length) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` on a resolved `EXTCODEHASH` op reduces to the account-code-hash `asmStateUnop`. -/
theorem asmStep_extcodehash_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "EXTCODEHASH") :
    asmStep o2pc prog s = asmStateUnop (fun addr s =>
      let acct := lookupAccount (AccountAddress.ofUInt256 addr) s.toVenomState.accounts
      if accountEmpty acct then ⟨0⟩ else keccak256 (⟨acct.code.toArray⟩ : ByteArray)) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` on a resolved `SELFBALANCE` op reduces to `asmPushVal` of the executing contract's
    balance (a 0-input env-push reading `callCtx.contract` + `accounts`). -/
theorem asmStep_selfbalance_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "SELFBALANCE") :
    asmStep o2pc prog s
      = asmPushVal (EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-! ## LOG compute step (append an event to the log; observable side effect)

`LOGn` pops `offset`, `size`, and `n` topics, and appends an `Event` built from a memory slice
(`data`), the topics, and `callCtx.contract` (`logger`). The observable-effect analog of the store
sims: the appended event is identical on both sides — `logger` agrees (`callCtx` conjunct), `topics`
are the shared popped values, and `data` agrees because the slice lies below the spill region
(`memoryRel_readWithPadding_slice`). Asm memory is unchanged (covered ⇒ expansion no-op in both the
`size = 0` and `size ≠ 0` branches), and the `logs` conjunct (`as.logs = vs.logs`) is preserved
because the same event is appended to both. Needs `size.toNat < USize.size` — the data length must be
addressable for the slice congruence. -/

/-- `asmLog n` on a well-formed stack (`offset :: size :: topics ++ rest`, `topics.length = n`) whose
    data slice is covered: pops `n+2`, appends the event, memory unchanged. -/
theorem asmLog_ok {n : Nat} {offset size : bytes32} {topics rest s} (hs : s.stack = offset :: size :: topics ++ rest)
    (htlen : topics.length = n)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmLog n s = AsmResult.AsmOK { asmNext s with stack := rest, memory := s.memory, logs := s.logs ++ [{ logger := s.callCtx.contract, topics := topics, data := (s.memory.readWithPadding offset.toNat size.toNat).toList }] } := by
  subst htlen
  unfold asmLog
  rw [hs]
  have hguard : ¬ ((offset :: size :: topics ++ rest).length < topics.length + 2) := by
    simp only [List.length_cons, List.length_append]; omega
  rw [if_neg hguard]
  have hmem : (if size.toNat = 0 then s.memory else asmExpandMemory (offset.toNat + size.toNat) s.memory) = s.memory := by
    by_cases h0 : size.toNat = 0
    · rw [if_pos h0]
    · rw [if_neg h0, asmExpandMemory_of_covered (offset.toNat + size.toNat) s.memory hcov]
  have hhd : (offset :: size :: topics ++ rest).head?.getD (EvmYul.UInt256.ofNat 0) = offset := rfl
  have hget1 : (offset :: size :: topics ++ rest)[1]! = size := rfl
  have hdrop2 : (offset :: size :: topics ++ rest).drop (topics.length + 2) = rest := by simp
  have htake2 : List.take topics.length (List.drop 2 (offset :: size :: topics ++ rest)) = topics := by simp
  simp only [hhd, hget1, hdrop2, htake2, hmem]

/-- **The LOG compute-step relation.** With `offset`/`size`/`n` topics on top, appending the event
    preserves `venomAsmRel`: the two events are equal (logger via `callCtx`, data via the below-spill
    slice), so the `logs` conjunct survives. -/
theorem venomAsmRel_log {lo ps vs as} {n : Nat} {offset size : bytes32} {topics rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: size :: topics ++ rest)
    (htlen : topics.length = n)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) :
    venomAsmRel lo { ps with stack := stackPop (n + 2) ps.stack }
      { vs with logs := vs.logs ++ [{ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList }] }
      { asmNext as with stack := rest, memory := as.memory, logs := as.logs ++ [{ logger := as.callCtx.contract, topics := topics, data := (as.memory.readWithPadding offset.toNat size.toNat).toList }] } := by
  subst htlen
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hslice : vs.memory.readWithPadding offset.toNat size.toNat = as.memory.readWithPadding offset.toNat size.toNat :=
    memoryRel_readWithPadding_slice hMem hbelow hsize
  have hev : ({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)
      = { logger := as.callCtx.contract, topics := topics, data := (as.memory.readWithPadding offset.toNat size.toNat).toList } := by
    rw [hCall, hslice]
  have hlen2 : topics.length + 2 ≤ ps.stack.length := by
    rw [hStk.1, hstack]; simp only [List.length_cons, List.length_append]; omega
  have hps := planStackRel_popN hStk hlen2
  rw [hstack] at hps
  have hdrop : (offset :: size :: topics ++ rest).drop (topics.length + 2) = rest := by simp
  rw [hdrop] at hps
  refine ⟨hps, hSpill, hMem, hAcc, hTrans, hRet, ?_, hCall, hTx, hBlk, hCode, hPrev⟩
  show as.logs ++ [_] = vs.logs ++ [_]
  rw [hLog, hev]

/-- `asmStep` dispatch for `LOGn` (`n ≤ 4`, via the `logTable`). -/
theorem asmStep_log_ok {o2pc prog s n} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp ("LOG" ++ toString n)) (hn : n ≤ 4) :
    asmStep o2pc prog s = asmLog n s := by
  interval_cases n <;> unfold asmStep <;> rw [dif_pos hpc, hprog] <;> rfl

/-- The runnable LOG sim: running the emitted `[SOEmit ("LOG"++n)]` advances the pc by 1 and appends
    the event, preserving `venomAsmRel`. Ties `asmStep_log_ok`, `asmLog_ok`, and `venomAsmRel_log`. -/
theorem emit_log_sim {n ps lo vs as prog offset size topics rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: size :: topics ++ rest)
    (htlen : topics.length = n)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size) (hn : n ≤ 4)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit ("LOG" ++ toString n)])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop (n + 2) ps.stack }
             { vs with logs := vs.logs ++ [{ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList }] } as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit ("LOG" ++ toString n)]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := as.memory, logs := as.logs ++ [{ logger := as.callCtx.contract, topics := topics, data := (as.memory.readWithPadding offset.toNat size.toNat).toList }] } := by
    rw [asmStep_log_ok hpc hget hn]; exact asmLog_ok hstack htlen hcov
  refine ⟨{ asmNext as with stack := rest, memory := as.memory, logs := as.logs ++ [{ logger := as.callCtx.contract, topics := topics, data := (as.memory.readWithPadding offset.toNat size.toNat).toList }] }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_log hrel hstack htlen hbelow hsize
  · rfl

/-! ## Copy-to-memory compute step (CALLDATACOPY, CODECOPY — range write from an equated source)

The range generalisation of MSTORE8: `asmCopyToMem src` pops `destOff`/`srcOff`/`sz` and writes the
`sz`-byte slice `src[srcOff..]` at `destOff`. The source `src` is an *equated* field — `callCtx.calldata`
(CALLDATACOPY) or `code` (CODECOPY) — so both sides write the *same* bytes to their memories, and
`memoryRel` survives via the range `readByte_write_congr`; the write window below the spill region is
framed by the range `byteArray_readWithPadding_write_disjoint`. Restricted to a nonzero copy
(`0 < sz`); `sz < USize.size` is needed so the written slice has length `sz`
(`ByteArray.readWithPadding_size`). (The `sz = 0` case is a no-op that could be added; RETURNDATACOPY
adds an OOB fault branch, and MCOPY a memory→memory read+write, left for follow-up.) -/

theorem asmStep_calldatacopy_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CALLDATACOPY") :
    asmStep o2pc prog s = asmCopyToMem s.callCtx.calldata s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_codecopy_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "CODECOPY") :
    asmStep o2pc prog s = asmCopyToMem s.code s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmCopyToMem` on a 3+-deep stack, nonzero covered copy: pops 3 and writes the `sz`-byte source
    slice at `destOff` (expansion no-op). -/
theorem asmCopyToMem_ok {src : List byte} {destOff srcOff sz stk s} (hs : s.stack = destOff :: srcOff :: sz :: stk)
    (hpos : 0 < sz.toNat)
    (hcov : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmCopyToMem src s = AsmResult.AsmOK { asmNext s with stack := stk, memory := ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 s.memory destOff.toNat sz.toNat } := by
  unfold asmCopyToMem
  rw [hs]
  have hmem : (if sz.toNat = 0 then s.memory else asmExpandMemory (destOff.toNat + sz.toNat) s.memory) = s.memory := by
    rw [if_neg (by omega : ¬ sz.toNat = 0), asmExpandMemory_of_covered (destOff.toNat + sz.toNat) s.memory hcov]
  simp only [hmem]

/-- `asmStep` on a resolved `EXTCODECOPY` op dispatches to `asmExtcodecopy`. -/
theorem asmStep_extcodecopy_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "EXTCODECOPY") :
    asmStep o2pc prog s = asmExtcodecopy s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmExtcodecopy` on a 4-deep stack (`addr :: dst :: src :: sz :: stk`), nonzero covered copy: pops
    4 and writes the `sz`-byte slice of the referenced account's code at `dst` (expansion no-op). Pops
    the address, then delegates to `asmCopyToMem_ok` with the account code as the source. -/
theorem asmExtcodecopy_ok {addr destOff srcOff sz stk s}
    (hs : s.stack = addr :: destOff :: srcOff :: sz :: stk)
    (hpos : 0 < sz.toNat)
    (hcov : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmExtcodecopy s = AsmResult.AsmOK
      { asmNext s with
        stack := stk,
        memory := ((⟨(lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 s.memory destOff.toNat sz.toNat } := by
  unfold asmExtcodecopy
  rw [hs]
  exact asmCopyToMem_ok (src := (lookupAccount (AccountAddress.ofUInt256 addr) s.accounts).code) rfl hpos hcov

/-- **The EXTCODECOPY compute-step relation.** The 4-input (`addr :: dst :: src :: sz`) account-code →
    memory copy. Pops 4; the written bytes are a slice of the referenced account's code, which agrees on
    both sides via the `accounts` conjunct. The account-source, 4-input twin of `venomAsmRel_copyToMem`. -/
theorem venomAsmRel_extcodecopy {lo ps vs as} {wa wb wc wd rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = wa :: wb :: wc :: wd :: rest)
    (hcovV : wb.toNat ≤ vs.memory.size)
    (hcovA : wb.toNat ≤ as.memory.size)
    (hsafe : wb.toNat + wd.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wd.toNat) (hsize : wd.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off') :
    venomAsmRel lo { ps with stack := stackPop 4 ps.stack }
      (writeMemoryWithExpansion wb.toNat
        ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs)
      { asmNext as with
        stack := rest,
        memory := ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat).write 0 as.memory wb.toNat wd.toNat } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  set src := (lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code with hsrc
  have hbssz : ((⟨src.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat).size = wd.toNat :=
    ByteArray.readWithPadding_size _ _ _ hsize
  have hlen4 : 4 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen4
  rw [hstack] at hps
  have hstate : writeMemoryWithExpansion wb.toNat ((⟨src.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs
      = { vs with memory := ((⟨src.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat).write 0 vs.memory wb.toNat wd.toNat } := by
    unfold writeMemoryWithExpansion; rw [hbssz]
  rw [hstate]
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · exact hps
  · intro op off' hlook
    obtain ⟨v, hopv, hval⟩ := hSpill op off' hlook
    refine ⟨v, hopv, ?_⟩
    have hd := EvmYul.byteArray_readWithPadding_write_disjoint
      ((⟨src.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) as.memory wb.toNat off' 32
      (by rw [hbssz]; exact hpos) hcovA (by rcases USize.size_eq with h | h <;> omega)
      (Or.inr (by rw [hbssz]; have := hspillReg op off' hlook; omega))
    rw [hbssz] at hd
    rw [hd]; exact hval
  · intro i hi
    have hc := readByte_write_congr ((⟨src.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat)
      vs.memory as.memory wb.toNat i (by rw [hbssz]; exact hpos) hcovV hcovA (hMem i hi)
    rw [hbssz] at hc
    exact hc

/-- The runnable EXTCODECOPY sim; the asm source (`account[addr].code` over `as.accounts`) is bridged to
    the Venom one via the `accounts` conjunct. `hdisp` from `asmStep_extcodecopy_ok`. -/
theorem emit_extcodecopy_sim {ps lo vs as prog wa wb wc wd rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = wa :: wb :: wc :: wd :: rest)
    (hcovV : wb.toNat ≤ vs.memory.size)
    (hcovA : ((wb.toNat + wd.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : wb.toNat + wd.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < wd.toNat) (hsize : wd.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "EXTCODECOPY"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "EXTCODECOPY"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 4 ps.stack }
             (writeMemoryWithExpansion wb.toNat
               ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "EXTCODECOPY"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hcode : (lookupAccount (AccountAddress.ofUInt256 wa) as.accounts).code
      = (lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code := by rw [hrel.2.2.2.1]
  have hcovA' : wb.toNat ≤ as.memory.size := by omega
  have hstep : asmStep offsetToPc prog as = AsmResult.AsmOK
      { asmNext as with
        stack := rest,
        memory := ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat).write 0 as.memory wb.toNat wd.toNat } := by
    rw [asmStep_extcodecopy_ok hpc hget, asmExtcodecopy_ok hstack hpos hcovA, hcode]
  refine ⟨{ asmNext as with
      stack := rest,
      memory := ((⟨(lookupAccount (AccountAddress.ofUInt256 wa) vs.accounts).code.toArray⟩ : ByteArray).readWithPadding wc.toNat wd.toNat).write 0 as.memory wb.toNat wd.toNat }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_extcodecopy hrel hstack hcovV hcovA' hsafe hpos hsize hspillReg
  · rfl

/-- `asmReturndatacopy` on a 3+-deep stack, nonzero **in-bounds** copy: pops 3 and writes the `sz`-byte
    `returndata` slice at `destOff` (expansion no-op). The OOB fault branch is excluded by `hnooob`. -/
theorem asmReturndatacopy_ok {destOff srcOff sz stk s} (hs : s.stack = destOff :: srcOff :: sz :: stk)
    (hpos : 0 < sz.toNat)
    (hnooob : srcOff.toNat + sz.toNat ≤ s.returndata.size)
    (hcov : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    asmReturndatacopy s = AsmResult.AsmOK { asmNext s with stack := stk, memory := (s.returndata.readWithPadding srcOff.toNat sz.toNat).write 0 s.memory destOff.toNat sz.toNat } := by
  unfold asmReturndatacopy
  rw [hs]
  have hcond : ¬ srcOff.toNat + sz.toNat > s.returndata.size := by omega
  have hmem : (if sz.toNat = 0 then s.memory else asmExpandMemory (destOff.toNat + sz.toNat) s.memory) = s.memory := by
    rw [if_neg (by omega : ¬ sz.toNat = 0), asmExpandMemory_of_covered (destOff.toNat + sz.toNat) s.memory hcov]
  simp only [hcond, if_false, hmem]

/-- `asmStep` on a RETURNDATACOPY instruction reduces to `asmReturndatacopy`. -/
theorem asmStep_returndatacopy_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "RETURNDATACOPY") :
    asmStep o2pc prog s = asmReturndatacopy s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **The copy-to-memory compute-step relation, ByteArray source.** Generalises `venomAsmRel_copyToMem`
    from a `List byte` source (`⟨src.toArray⟩`) to an arbitrary `bytes : ByteArray`; the proof only ever
    uses the source through `bytes.readWithPadding`, whose size is `sz` for any ByteArray. Instantiate
    with `bytes := ⟨src.toArray⟩` for calldata/code, or `bytes := vs.returndata` for returndata. -/
theorem venomAsmRel_copyToMemBA {lo ps vs as} {bytes : ByteArray} {destOff srcOff sz rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : destOff.toNat ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off') :
    venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
      (writeMemoryWithExpansion destOff.toNat (bytes.readWithPadding srcOff.toNat sz.toNat) vs)
      { asmNext as with stack := rest, memory := (bytes.readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hbssz : (bytes.readWithPadding srcOff.toNat sz.toNat).size = sz.toNat :=
    ByteArray.readWithPadding_size _ _ _ hsize
  have hlen3 : 3 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen3
  rw [hstack] at hps
  have hstate : writeMemoryWithExpansion destOff.toNat (bytes.readWithPadding srcOff.toNat sz.toNat) vs
      = { vs with memory := (bytes.readWithPadding srcOff.toNat sz.toNat).write 0 vs.memory destOff.toNat sz.toNat } := by
    unfold writeMemoryWithExpansion; rw [hbssz]
  rw [hstate]
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · exact hps
  · intro op off' hlook
    obtain ⟨v, hopv, hval⟩ := hSpill op off' hlook
    refine ⟨v, hopv, ?_⟩
    have hd := EvmYul.byteArray_readWithPadding_write_disjoint
      (bytes.readWithPadding srcOff.toNat sz.toNat) as.memory destOff.toNat off' 32
      (by rw [hbssz]; exact hpos) hcovA (by rcases USize.size_eq with h | h <;> omega)
      (Or.inr (by rw [hbssz]; have := hspillReg op off' hlook; omega))
    rw [hbssz] at hd
    rw [hd]; exact hval
  · intro i hi
    have hc := readByte_write_congr (bytes.readWithPadding srcOff.toNat sz.toNat)
      vs.memory as.memory destOff.toNat i (by rw [hbssz]; exact hpos) hcovV hcovA (hMem i hi)
    rw [hbssz] at hc
    exact hc

/-- **The copy-to-memory compute-step relation** (CALLDATACOPY / CODECOPY, shared source `src`). Both
    sides write the same `sz` bytes to their memories, so `memoryRel` survives
    (`readByte_write_congr`); the below-spill window is framed
    (`byteArray_readWithPadding_write_disjoint`). Range generalisation of `venomAsmRel_mstore8`. -/
theorem venomAsmRel_copyToMem {lo ps vs as} {src : List byte} {destOff srcOff sz rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : destOff.toNat ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' →
                  ps.alloc.fnEom ≤ off') :
    venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
      (writeMemoryWithExpansion destOff.toNat ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat) vs)
      { asmNext as with stack := rest, memory := ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hbssz : ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).size = sz.toNat :=
    ByteArray.readWithPadding_size _ _ _ hsize
  have hlen3 : 3 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  have hps := planStackRel_popN hStk hlen3
  rw [hstack] at hps
  have hstate : writeMemoryWithExpansion destOff.toNat ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat) vs
      = { vs with memory := ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 vs.memory destOff.toNat sz.toNat } := by
    unfold writeMemoryWithExpansion; rw [hbssz]
  rw [hstate]
  refine ⟨?_, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
  · exact hps
  · intro op off' hlook
    obtain ⟨v, hopv, hval⟩ := hSpill op off' hlook
    refine ⟨v, hopv, ?_⟩
    have hd := EvmYul.byteArray_readWithPadding_write_disjoint
      ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat) as.memory destOff.toNat off' 32
      (by rw [hbssz]; exact hpos) hcovA (by rcases USize.size_eq with h | h <;> omega)
      (Or.inr (by rw [hbssz]; have := hspillReg op off' hlook; omega))
    rw [hbssz] at hd
    rw [hd]; exact hval
  · intro i hi
    have hc := readByte_write_congr ((⟨src.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat)
      vs.memory as.memory destOff.toNat i (by rw [hbssz]; exact hpos) hcovV hcovA (hMem i hi)
    rw [hbssz] at hc
    exact hc

/-- The runnable CALLDATACOPY sim; the asm source (`as.callCtx.calldata`) is bridged to the Venom one
    via the `callCtx` conjunct. -/
theorem emit_calldatacopy_sim {ps lo vs as prog destOff srcOff sz rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CALLDATACOPY"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CALLDATACOPY"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
             (writeMemoryWithExpansion destOff.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CALLDATACOPY"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hcd : as.callCtx.calldata = vs.callCtx.calldata := by rw [hrel.2.2.2.2.2.2.2.1]
  have hcovA' : destOff.toNat ≤ as.memory.size := by omega
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
    rw [asmStep_calldatacopy_ok hpc hget, asmCopyToMem_ok hstack hpos hcovA, hcd]
  refine ⟨{ asmNext as with stack := rest, memory := ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_copyToMem (src := vs.callCtx.calldata) hrel hstack hcovV hcovA' hsafe hpos hsize hspillReg
  · rfl

/-- The runnable CODECOPY sim; the asm source (`as.code`) is bridged to the Venom one via the `code`
    conjunct. -/
theorem emit_codecopy_sim {ps lo vs as prog destOff srcOff sz rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "CODECOPY"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "CODECOPY"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
             (writeMemoryWithExpansion destOff.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "CODECOPY"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hcode : as.code = vs.code := by rw [hrel.2.2.2.2.2.2.2.2.2.2.1]
  have hcovA' : destOff.toNat ≤ as.memory.size := by omega
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
    rw [asmStep_codecopy_ok hpc hget, asmCopyToMem_ok hstack hpos hcovA, hcode]
  refine ⟨{ asmNext as with stack := rest, memory := ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_copyToMem (src := vs.code) hrel hstack hcovV hcovA' hsafe hpos hsize hspillReg
  · rfl

/-- The runnable RETURNDATACOPY sim on the **in-bounds** path. The source (`as.returndata`) is bridged
    to the Venom one via the `returndata` conjunct; `hnooob` selects the OK branch (out-of-bounds
    faults on *both* sides identically, so it is excluded here rather than diverging). -/
theorem emit_returndatacopy_sim {ps lo vs as prog destOff srcOff sz rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hnooob : srcOff.toNat + sz.toNat ≤ vs.returndata.size)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "RETURNDATACOPY"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "RETURNDATACOPY"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
             (writeMemoryWithExpansion destOff.toNat (vs.returndata.readWithPadding srcOff.toNat sz.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "RETURNDATACOPY"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hrd : as.returndata = vs.returndata := hrel.2.2.2.2.2.1
  have hcovA' : destOff.toNat ≤ as.memory.size := by omega
  have hnooobA : srcOff.toNat + sz.toNat ≤ as.returndata.size := by rw [hrd]; exact hnooob
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := (vs.returndata.readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
    rw [asmStep_returndatacopy_ok hpc hget, asmReturndatacopy_ok hstack hpos hnooobA hcovA, hrd]
  refine ⟨{ asmNext as with stack := rest, memory := (vs.returndata.readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_copyToMemBA (bytes := vs.returndata) hrel hstack hcovV hcovA' hsafe hpos hsize hspillReg
  · rfl

/-- `asmMcopy` on a 3+-deep stack, nonzero copy with **both** windows covered: pops 3 and writes the
    `sz`-byte memory slice `[srcOff, srcOff+sz)` at `destOff` (the `max`-expansion is a no-op). -/
theorem asmMcopy_ok {destOff srcOff sz stk s} (hs : s.stack = destOff :: srcOff :: sz :: stk)
    (hpos : 0 < sz.toNat)
    (hcov : ((max (srcOff.toNat + sz.toNat) (destOff.toNat + sz.toNat) + 31) / 32) * 32 ≤ s.memory.size) :
    asmMcopy s = AsmResult.AsmOK { asmNext s with stack := stk, memory := (s.memory.readWithPadding srcOff.toNat sz.toNat).write 0 s.memory destOff.toNat sz.toNat } := by
  unfold asmMcopy
  rw [hs]
  have hmem : (if sz.toNat = 0 then s.memory else asmExpandMemory (max (srcOff.toNat + sz.toNat) (destOff.toNat + sz.toNat)) s.memory) = s.memory := by
    rw [if_neg (by omega : ¬ sz.toNat = 0), asmExpandMemory_of_covered _ s.memory hcov]
  simp only [hmem]

/-- `asmStep` on an MCOPY instruction reduces to `asmMcopy`. -/
theorem asmStep_mcopy_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MCOPY") :
    asmStep o2pc prog s = asmMcopy s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- The runnable MCOPY sim (memory→memory). Unlike the external-source copies, the source is `vs.memory`
    itself, so the source read is bridged through `memoryRel` (`memoryRel_readWithPadding_slice`, needing
    source-safety `srcOff + sz ≤ fnEom`) rather than a simple equality conjunct; `hcovS`/`hcovA` cover the
    `max(src,dst)` window so the asm expansion is a no-op. Then `venomAsmRel_copyToMemBA (bytes := vs.memory)`
    matches `mcopy` exactly (`writeMemoryWithExpansion dst (vs.memory.readWithPadding src sz) vs`). -/
theorem emit_mcopy_sim {ps lo vs as prog destOff srcOff sz rest offsetToPc}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = destOff :: srcOff :: sz :: rest)
    (hcovV : destOff.toNat ≤ vs.memory.size)
    (hcovA : ((destOff.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hcovS : ((srcOff.toNat + sz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafe : destOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hsrcsafe : srcOff.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hpos : 0 < sz.toNat) (hsize : sz.toNat < USize.size)
    (hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off')
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit "MCOPY"])) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit "MCOPY"]).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPop 3 ps.stack }
             (writeMemoryWithExpansion destOff.toNat (vs.memory.readWithPadding srcOff.toNat sz.toNat) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit "MCOPY"]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hMem : memoryRel ps.alloc vs.memory as.memory := hrel.2.2.1
  have hcovA' : destOff.toNat ≤ as.memory.size := by omega
  have hcovMax : ((max (srcOff.toNat + sz.toNat) (destOff.toNat + sz.toNat) + 31) / 32) * 32 ≤ as.memory.size := by
    rcases Nat.le_total (srcOff.toNat + sz.toNat) (destOff.toNat + sz.toNat) with h | h
    · rw [Nat.max_eq_right h]; exact hcovA
    · rw [Nat.max_eq_left h]; exact hcovS
  have hsrcbridge : as.memory.readWithPadding srcOff.toNat sz.toNat = vs.memory.readWithPadding srcOff.toNat sz.toNat :=
    (memoryRel_readWithPadding_slice hMem hsrcsafe hsize).symm
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := rest, memory := (vs.memory.readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat } := by
    rw [asmStep_mcopy_ok hpc hget, asmMcopy_ok hstack hpos hcovMax, hsrcbridge]
  refine ⟨{ asmNext as with stack := rest, memory := (vs.memory.readWithPadding srcOff.toNat sz.toNat).write 0 as.memory destOff.toNat sz.toNat }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_copyToMemBA (bytes := vs.memory) hrel hstack hcovV hcovA' hsafe hpos hsize hspillReg
  · rfl

/-! ## Unary-op compute step (1-input companions of the binop core)

The 1-input analogs of `asmBinop_ok` / `venomAsmRel_binop` / `emit_binop_sim`, for `ISZERO`, `NOT`,
… . Operand-order reversal is a no-op here (`[op1].reverse = [op1]`), so these need no special care. -/

/-- `asmUnop` on a 1+-deep stack pops one and pushes the result. -/
theorem asmUnop_ok {f : bytes32 → bytes32} {a stk s} (hs : s.stack = a :: stk) :
    asmUnop f s = AsmResult.AsmOK ({ asmNext s with stack := f a :: stk }) := by
  unfold asmUnop; rw [hs]

/-- `asmStep` dispatch for `ISZERO`. -/
theorem asmStep_iszero_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "ISZERO") :
    asmStep o2pc prog s = asmUnop UInt256.isZero s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `asmStep` dispatch for `NOT`. -/
theorem asmStep_not_ok {o2pc prog s} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "NOT") :
    asmStep o2pc prog s = asmUnop (~~~ ·) s := by unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- The compute-step relation for a 1-input opcode (1-input companion of `venomAsmRel_binop`):
    input on top, fresh output `out` ⇒ the post-unop state preserves `venomAsmRel`. -/
theorem venomAsmRel_unop {lo ps vs as out} {f : bytes32 → bytes32} {v rest}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none) :
    venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
      (updateVar out (f v) vs)
      { asmNext as with stack := f v :: rest } := by
  obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
  have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
  obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
    venomAsmRel_updateVar lo ps vs as out (f v)
      ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill
  refine ⟨?_, hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
  have hout : operandVal (updateVar out (f v) vs) lo (Operand.Var out) = some (f v) := by
    simp only [operandVal]; exact lookupVar_updateVar_self vs out (f v)
  have hps := planStackRel_unop hStk' hlen1 hout
  rw [hstack] at hps
  simpa using hps

/-- The runnable compute-step sim for a 1-input opcode (1-input companion of `emit_binop_sim`). -/
theorem emit_unop_sim {name out v rest ps lo vs as prog} {f : bytes32 → bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = v :: rest)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hblock : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]))
    (hdisp : ∀ (h : as.pc < prog.length), prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name →
              asmStep offsetToPc prog as = asmUnop f as) :
    ∃ as', runAsm (executePlan [StackOp.SOEmit name]).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
             (updateVar out (f v) vs) as' ∧
           as'.pc = as.pc + (executePlan [StackOp.SOEmit name]).length := by
  obtain ⟨hpc, hget⟩ := asmBlockAt_one hblock
  have hstep : asmStep offsetToPc prog as
      = AsmResult.AsmOK { asmNext as with stack := f v :: rest } := by
    rw [hdisp hpc hget]; exact asmUnop_ok hstack
  refine ⟨{ asmNext as with stack := f v :: rest }, ?_, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = _
    rw [runAsm_succ_ok hpc hstep]; rfl
  · exact venomAsmRel_unop hrel hstack hfresh hspill
  · rfl

end EvmYul.Venom.Hol.Codegen

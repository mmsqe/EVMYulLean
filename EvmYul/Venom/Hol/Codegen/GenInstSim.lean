import EvmYul.Venom.Hol.Codegen.GenBlockSimSupport
import EvmYul.Venom.Hol.Codegen.PlanSim

/-!
# Per-instruction simulation (stage 4b ④)

Towards `genBlockSimulation`: a single instruction's generated ops, run on the asm
interpreter, advance the pc by their length and preserve `venomAsmRel` across the Venom
instruction step. The non-terminal sims are stated in the established `PlanSim` convention

  `∃ as', runAsm (executePlan ops).length [] prog as = AsmOK as' ∧
          venomAsmRel lo ps' vs' as' ∧ as'.pc = as.pc + (executePlan ops).length`

(which `plan_seq_sim` composes); the terminal sims instead reach `AsmHalt`/`AsmFault`
with `venomAsmTerminalRel`. Contents so far:

* trivial opcodes — `genInstPlan_sim_nop`, `genInstPlan_sim_param` (+ the reusable
  `venomAsmRel_updateVar` variable-update infrastructure);
* block prefix — `soLabel_sim` (the leading `JUMPDEST`);
* dispatch — `generateInstPlan_regular_eq` (non-special opcode ⇒ `generateRegularInstPlan`)
  and the no-IO generator decomposition `generate{Regular,}InstPlan_emit_noIO`;
* terminals — `genInstPlan_sim_stop` (Halt) and `genInstPlan_sim_invalid` (ExHaltAbort);
* block asm structure — `executePlan_blockOps`.

The remaining regular/operand-carrying cases (the bulk of vyper-hol's genBlockSimScript)
build on `reorderPlan_sim` / the spill sims and the input-emission machinery.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/- Threaded `offsetToPc` (auto-included only in the simulation lemmas that run `asmStep`/`runAsm`).
   The control-flow-free body sims ignore it, so the proofs are unchanged; this lets them feed the
   `offsetToPc`-generic block-body fold (`foldl_inst_sim`) in the resolved-program capstone. -/
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
    asmStep offsetToPc prog s = AsmResult.AsmFault (asmNext s) := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- `INVALID` (terminal/aborting, `ExHaltAbort`): the generator emits `[SOEmit "INVALID"]`;
    the Venom step aborts with returndata cleared and the asm `INVALID` faults (`AsmFault`).
    `venomAsmTerminalRel` holds given `vs.returndata = empty` (in-scope, since message calls
    are out of scope, returndata is always empty): the Venom step clears returndata while
    `asmStep`'s `AsmFault (asmNext s)` keeps it, so they agree exactly when already empty. -/
theorem genInstPlan_sim_invalid
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLive : List String} {isHalting nextIsTerm : Bool} {curBb : String}
    {ps ps' : PlanState} {ops : List StackOp} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    (hinv : inst.opcode = Opcode.INVALID) (hops : inst.operands = []) (houts : inst.outputs = [])
    (hgen : generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm curBb ps
              = some (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hrd : vs.returndata = ByteArray.empty)
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
  obtain ⟨_, _, _, hAcc, hTrans, hRet, hLog, _⟩ := hrel
  refine ⟨rfl, by simp only [stepInstBase, hinv], asmNext as, ?_, ?_⟩
  · show runAsm 1 offsetToPc prog as = AsmResult.AsmFault (asmNext as)
    unfold runAsm
    rw [asmStep_invalid_ok hpc hget]
  · exact ⟨hAcc, hTrans, hRet.trans hrd, hLog⟩

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

/-- Discharge of the positioning hypothesis for a distinct literal pair already on top:
    `reorderPlan [Lit a, Lit b]` is a no-op when `ps.stack = base ++ [Lit a, Lit b]` and
    `a ≠ b`. This is the concrete reorder-no-op for a 2-input binop after input emission
    (`emitInputPlan_stack_allLit` supplies the `base ++ [Lit a, Lit b]` shape). -/
theorem reorderPlan_pair_lit_nil (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) (hab : a ≠ b) :
    reorderPlan [Operand.Lit a, Operand.Lit b] ps = ([], ps) := by
  have hba : (Operand.Lit b == Operand.Lit a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hab (Operand.Lit.inj h).symm
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  have henum : ([Operand.Lit a, Operand.Lit b]).enum
      = [(0, Operand.Lit a), (1, Operand.Lit b)] := rfl
  rw [henum] at hp
  rw [hstack]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · show stackGetDepth (Operand.Lit a) (base ++ [Operand.Lit a, Operand.Lit b]) = some 1
    simp [stackGetDepth, stackFind, List.reverse_append, hba]
  · show stackGetDepth (Operand.Lit b) (base ++ [Operand.Lit a, Operand.Lit b]) = some 0
    simp [stackGetDepth, stackFind, List.reverse_append]

/-- `reorderPlan [Var x, Var y]` is a no-op when that pair is already positioned (`Var x` at depth 1,
    `Var y` at depth 0). The var counterpart of `reorderPlan_pair_lit_nil` (the commutative `opsA`
    side). -/
theorem reorderPlan_pair_var_nil (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) (hxy : x ≠ y) :
    reorderPlan [Operand.Var x, Operand.Var y] ps = ([], ps) := by
  have hyx : (Operand.Var y == Operand.Var x) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; exact hxy (Operand.Var.inj h).symm
  apply reorderPlan_nil_of_allPositioned
  intro p hp
  have henum : ([Operand.Var x, Operand.Var y]).enum
      = [(0, Operand.Var x), (1, Operand.Var y)] := rfl
  rw [henum] at hp
  rw [hstack]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · show stackGetDepth (Operand.Var x) (base ++ [Operand.Var x, Operand.Var y]) = some 1
    simp [stackGetDepth, stackFind, List.reverse_append, hyx]
  · show stackGetDepth (Operand.Var y) (base ++ [Operand.Var x, Operand.Var y]) = some 0
    simp [stackGetDepth, stackFind, List.reverse_append]

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

/-- Depth-shift under a DUP: appending a *different* var to the bottom-to-top stack pushes every
    other var's depth up by one. `stackDup d s = s ++ [peek]`, so the second operand of a var pair
    sits one deeper after the first DUP — this is the `hdepth_x'` relation the var-binop input needs,
    and the depth-tracking step a per-block stack-discipline invariant maintains across instructions. -/
theorem stackGetDepth_append_ne {x y : String} (stk : List Operand) (h : x ≠ y) :
    stackGetDepth (Operand.Var x) (stk ++ [Operand.Var y])
      = (stackGetDepth (Operand.Var x) stk).map (· + 1) := by
  unfold stackGetDepth
  rw [List.reverse_append]
  have hne : (Operand.Var y == Operand.Var x) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc; injection hc with hc'; exact h hc'.symm
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, stackFind, hne,
    Bool.false_eq_true, if_false]
  cases stackFind (fun z => z == Operand.Var x) stk.reverse <;> simp

/-! ## Positioned nodup var list (join reconciliation, well-scheduled case)

For the inter-block JMP join, the well-scheduled case is when the body already produces the target
block's expected entry layout `S.map Var`, so the join `reorderPlan (S.map Var)` is a no-op. The
foundation is that a **nodup** operand list is positioned as itself: `stackFind` on a nodup list finds
exactly the queried index, so `stackGetDepth L[i] L = some (length-1-i)` — every element is at its own
target depth. -/

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

/-- Step 0 of the swapped-pair reorder: bring `Lit b` (at depth 0) to its target depth 1
    via a single `SWAP1`. -/
theorem reorderOne_swap0 (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderOne () [Operand.Lit b, Operand.Lit a] 0 (Operand.Lit b) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }) := by
  have hdb : stackGetDepth (Operand.Lit b) ps.stack = some 0 := by
    rw [hstack]; exact stackGetDepth_tos base (Operand.Lit a) (Operand.Lit b)
  have hsw : stackSwap 1 ps.stack = base ++ [Operand.Lit b, Operand.Lit a] := by
    rw [hstack]; exact stackSwap_1_append_pair base (Operand.Lit a) (Operand.Lit b)
  unfold reorderOne
  simp [hdb, doSwap_zero, doSwap_one, hsw]

/-- The swapped-pair reorder on a positioned stack costs one `SWAP1` (independent of
    distinctness: `Lit b` is on top, gets swapped down; `Lit a` then sits at its target). -/
theorem reorderPlan_swapped_pair_lit (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderPlan [Operand.Lit b, Operand.Lit a] ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }) := by
  have hstep0 := reorderOne_swap0 base a b ps hstack
  have hstep1 : reorderOne () [Operand.Lit b, Operand.Lit a] 1 (Operand.Lit a)
      { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }
      = ([], { ps with stack := base ++ [Operand.Lit b, Operand.Lit a] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Lit a) (base ++ [Operand.Lit b, Operand.Lit a]) = some 0
    exact stackGetDepth_tos base (Operand.Lit b) (Operand.Lit a)
  unfold reorderPlan
  have henum : ([Operand.Lit b, Operand.Lit a]).enum = [(0, Operand.Lit b), (1, Operand.Lit a)] :=
    rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.append_nil, List.nil_append]

/-- The first `reorderOne` of the swapped var pair does a `SWAP1` (var counterpart of
    `reorderOne_swap0`). -/
theorem reorderOne_swap0_var (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) :
    reorderOne () [Operand.Var y, Operand.Var x] 0 (Operand.Var y) ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var x] }) := by
  have hdb : stackGetDepth (Operand.Var y) ps.stack = some 0 := by
    rw [hstack]; exact stackGetDepth_tos base (Operand.Var x) (Operand.Var y)
  have hsw : stackSwap 1 ps.stack = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hstack]; exact stackSwap_1_append_pair base (Operand.Var x) (Operand.Var y)
  unfold reorderOne
  simp [hdb, doSwap_zero, doSwap_one, hsw]

/-- The swapped var-pair reorder costs one `SWAP1` (var counterpart of
    `reorderPlan_swapped_pair_lit` — the commutative `opsB` side). -/
theorem reorderPlan_swapped_pair_var (base : List Operand) (x y : String) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Var x, Operand.Var y]) :
    reorderPlan [Operand.Var y, Operand.Var x] ps
      = ([StackOp.SOSwap 1], { ps with stack := base ++ [Operand.Var y, Operand.Var x] }) := by
  have hstep0 := reorderOne_swap0_var base x y ps hstack
  have hstep1 : reorderOne () [Operand.Var y, Operand.Var x] 1 (Operand.Var x)
      { ps with stack := base ++ [Operand.Var y, Operand.Var x] }
      = ([], { ps with stack := base ++ [Operand.Var y, Operand.Var x] }) := by
    apply reorderOne_nil_of_positioned
    show stackGetDepth (Operand.Var x) (base ++ [Operand.Var y, Operand.Var x]) = some 0
    exact stackGetDepth_tos base (Operand.Var y) (Operand.Var x)
  unfold reorderPlan
  have henum : ([Operand.Var y, Operand.Var x]).enum = [(0, Operand.Var y), (1, Operand.Var x)] :=
    rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.append_nil, List.nil_append]

/-- `reorderCost` of the swapped-pair reorder is 1 — the `opsB` side, completing the
    commutative-branch comparison (`reorderCost opsA = 0 < 1 = reorderCost opsB`). -/
theorem reorderCost_swapped_pair_lit (base : List Operand) (a b : bytes32) (ps : PlanState)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    reorderCost (reorderPlan [Operand.Lit b, Operand.Lit a] ps).1 = 1 := by
  rw [reorderPlan_swapped_pair_lit base a b ps hstack]; rfl

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

/-- **Structural decomposition of `generateRegularInstPlan` for a commutative binop** with two
    distinct literal operands (single live output, not halting). Every let-chain step resolves
    via the closed forms above: `computeOperands` gives the operand list (commutative ⇒ not a
    jump/log opcode), the join is a no-op (not `JMP`), the commutative `if` picks `operands`,
    the final reorder is a no-op (operands positioned), the compute pops the two operands and
    pushes the output, `generateEmitOps` yields `[SOEmit name]`, the dead-output pop is empty
    (output live). The plan is `inputOps ++ [SOEmit name] ++ optOps`, threaded through the
    optimistic swap and dead-spill release. -/
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
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  -- The codegen reverses the operands (semantic→stack order), so the emitted pair is `[b, a]`.
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
  simp only [hco, hrev, houts]
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
        reorderPlan_swapped_pair_lit base b a ps1 hps1',
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        reorderCost, hcomm, hjmp]

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

/-- With the plan stack positioned as `base ++ [Lit a, Lit b]`, the asm stack is
    `b :: a :: rest` — the operand values on top (TOS = `b`, the last operand). This produces
    `emit_binop_sim`'s `hstack`. -/
theorem venomAsmRel_asmStack_top2_lit {lo ps vs as} {base : List Operand} {a b : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Lit a, Operand.Lit b]) :
    as.stack = b :: a :: as.stack.drop 2 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 2 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = b := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_pair] at hp
    simp only [operandVal] at hp
    exact (Option.some.inj hp).symm
  have h1 : as.stack[1]! = a := by
    have hp := planStackRel_peek hStk (dist := 1) (by rw [hstack]; simp)
    rw [hstack, stackPeek_1_append_pair] at hp
    simp only [operandVal] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get2 as.stack hge]
  rw [h0, h1]

/-- With plan stack `base ++ [Var y, Var x]` and `x`/`y` valued `wx`/`wy` in `vs`, the asm stack
    top two are `wx` (TOS) and `wy`. The var counterpart of `venomAsmRel_asmStack_top2_lit` (values
    from `operandVal`). -/
theorem venomAsmRel_asmStack_top2_var {lo ps vs as} {base : List Operand} {x y : String}
    {wx wy : bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : ps.stack = base ++ [Operand.Var y, Operand.Var x])
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hvy : operandVal vs lo (Operand.Var y) = some wy) :
    as.stack = wx :: wy :: as.stack.drop 2 := by
  obtain ⟨hStk, _⟩ := hrel
  have hlen : ps.stack.length = as.stack.length := hStk.1
  have hge : 2 ≤ as.stack.length := by rw [← hlen, hstack]; simp
  have h0 : as.stack[0]! = wx := by
    have hp := planStackRel_peek hStk (dist := 0) (by rw [hstack]; simp)
    rw [hstack, stackPeek_0_append_pair, hvx] at hp
    exact (Option.some.inj hp).symm
  have h1 : as.stack[1]! = wy := by
    have hp := planStackRel_peek hStk (dist := 1) (by rw [hstack]; simp)
    rw [hstack, stackPeek_1_append_pair, hvy] at hp
    exact (Option.some.inj hp).symm
  conv_lhs => rw [list_eq_get2 as.stack hge]
  rw [h0, h1]

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
  have hco := computeOperands_of_commutative inst hcomm
  have hjmp := commutative_ne_jmp hcomm
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hpvar := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x'
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var y, Operand.Var x] := by
    rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hco, hrev, houts]
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
        reorderPlan_swapped_pair_var base y x ps1 hps1',
        hps1', stackPop_2_append_pair, stackPush, popmanyPlan_nil, hmem,
        reorderCost, hcomm, hjmp]

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
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy hstack0 hlive
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
  have hrev : inst.operands.reverse = [Operand.Lit b, Operand.Lit a] := by rw [hops]; rfl
  rw [genRegularInstPlan_commBinopLit_eq hname hcomm hops houts hab hstack0 hlive,
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

/-! ## 0-input context-push through the real generator (`generateRegularInstPlan`)

The degenerate case of the unary-var family, for a 0-input / 1-output op (`CALLVALUE`, `CALLER`,
`CODESIZE`, …): with no operands, input emission is empty, so the generated plan (under the swap
no-op) is just `[SOEmit name]`, and the sim is `emit_read0_sim` followed by `releaseDeadSpills_sim`.
This is the `generateRegularInstPlan`-level counterpart of `emit_ctx_push_sim` — the piece a body-fold
`BodyStep` producer for context pushes builds on. -/

/-- **Plan decomposition** for a 0-input / 1-output op: no input emission, so the plan is
    `[SOEmit name]` followed by the optimistic swap, with `releaseDeadSpills` on the output state. The
    0-operand analog of `genRegularInstPlan_unopVar_eq`. -/
theorem genRegularInstPlan_read0_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {out name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ([StackOp.SOEmit name]
            ++ (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
                  { ps with stack := ps.stack ++ [Operand.Var out] }).1,
         releaseDeadSpills nextLiveness
           (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
             { ps with stack := ps.stack ++ [Operand.Var out] }).2) := by
  have hrev : inst.operands.reverse = ([] : List Operand) := by rw [hops]; rfl
  have hemit : emitInputPlan inst.opcode ([] : List Operand) nextLiveness ps = ([], ps) := rfl
  have hmem : out ∈ nextLiveness := by simpa using hlive
  unfold generateRegularInstPlan
  simp [hcompute, hrev, hemit, houts, reorderPlan_empty, stackPop_zero, stackPush,
    popmanyPlan_nil, generateEmitOps_evmName hname, hmem, hnjmp]

/-- **The runnable sim for a 0-input context-push op** through `generateRegularInstPlan`. A degenerate
    `genRegularInstPlan_unopVar_sim`: no input emission, so the plan (under the swap no-op) is just
    `[SOEmit name]`, and the sim is `emit_read0_sim` then `releaseDeadSpills_sim`. -/
theorem genRegularInstPlan_read0_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {out name : String} {v : bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hdisp : ∀ (h : as.pc < prog.length),
        prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog as = asmPushVal v as)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out v vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive, hoptnoop] at hblock ⊢
  simp only [List.append_nil] at hblock ⊢
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ := emit_read0_sim hrel hfresh hspill hblock hdisp
  have hpush : ({ ps with stack := stackPush (Operand.Var out) ps.stack } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by rfl
  rw [hpush] at hrelE
  exact ⟨as2, hrunE, releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE, hpcE⟩

/-- **The runnable sim for SLOAD** through `generateRegularInstPlan`. Same plan shape as a unary var-op
    (`genRegularInstPlan_unopVar_eq`: DUP the key, emit `SLOAD`), but the emitted step is a storage
    read (`emit_sload_sim`) rather than a pure unop, so the pushed value is `sload key vs` — a function
    of the input *and* shared state (agreeing via the `accounts`/`callCtx` conjuncts), not just the
    input. The storage-read counterpart of `genRegularInstPlan_unopVar_sim`. -/
theorem genRegularInstPlan_sload_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x out : String} {base : List Operand} {dist : Nat} {w : bytes32}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
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
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out (sload w vs) vs) as' ∧
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
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SLOAD"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, hrelE, hpcE⟩ :=
    emit_sload_sim hrelI hstacktop hfresh1 hps1spill hbE' (fun h hg => hdisp as1 h hg)
  have hps6 : ({ ps1 with stack := stackPush (Operand.Var out) (stackPop 1 ps1.stack) } : PlanState)
      = { ps1 with stack := base ++ [Operand.Var out] } := by
    rw [hps1stack, stackPop_1_append_single]; rfl
  rw [hps6] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨as2, ?_, hrelR, ?_⟩
  · rw [executePlan_append, List.length_append]; exact runAsm_compose hrunI hrunE
  · rw [executePlan_append, List.length_append, hpcE, hpcI]; omega

/-- **Plan decomposition** for a no-output *single*-var instruction (SELFDESTRUCT): the emitted ops
    are the one-operand input-emission `++ [SOEmit name]`. The single-operand analog of
    `genRegularInstPlan_noOutput2Var_ops_eq` (the commutative branch is dead — only one operand). -/
theorem genRegularInstPlan_noOutput1Var_ops_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {x : String} {base : List Operand} {name : String} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting nextIsTerminator
        curBbLabel ps).1
      = (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).1 ++ [StackOp.SOEmit name] := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hpvar := emitInputPlan_single_var_eq (opc := inst.opcode) (nl := nextLiveness)
    hnospill hlivex hdepth hsmall hpeek
  have hps1 : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by rw [hrev, hpvar, hstack0]
  unfold generateRegularInstPlan
  simp only [hcompute, hrev, houts]
  rcases hemit : emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps with ⟨inputOps, ps1⟩
  have hps1' : ps1.stack = base ++ [Operand.Var x] := by
    have h2 : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 = ps1 := by rw [hemit]
    rw [hrev] at hps1; rw [← h2]; exact hps1
  simp [generateEmitOps_evmName hname, reorderPlan_single_var_nil base x ps1 hps1',
        hps1', stackPop_1_append_single, hnjmp]

/-- **Full per-instruction terminal sim for SELFDESTRUCT**: composes the single-operand input-emission
    decomposition with `emitInputPlan_single_var_sim` and `emit_selfdestruct_sim`. Running the whole
    `generateRegularInstPlan` plan from `venomAsmRel` reaches `AsmHalt` with the account transfer of
    the Venom `SELFDESTRUCT` (`venomAsmTerminalRel`). No memory coverage needed (accounts, not memory);
    the first operand-carrying terminal that mutates accounts to be discharged end to end. -/
theorem genRegularInstPlan_selfdestruct_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {x : String} {wx : bytes32} {base : List Operand} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SELFDESTRUCT")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) (hlen : dist < ps.stack.length)
    (hvx : operandVal vs lo (Operand.Var x) = some wx)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness
             isHalting nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (selfdestruct wx vs)) as' := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  rw [genRegularInstPlan_noOutput1Var_ops_eq hname hnjmp hcompute hops houts hstack0 hnospill hlivex
        hdepth hsmall, hrev] at hblock ⊢
  rw [executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI, hpcI⟩ :=
    emitInputPlan_single_var_sim hnospill hlivex hdepth hsmall hrel hlen hbI
  have hps1stack : (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.stack
      = base ++ [Operand.Var x] := by
    rw [emitInputPlan_single_var_eq hnospill hlivex hdepth hsmall (stackGetDepth_peek hdepth), hstack0]
  have hstacktop : as1.stack = wx :: as1.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var hrelI hps1stack hvx
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "SELFDESTRUCT"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨as2, hrunE, htermE⟩ := emit_selfdestruct_sim hrelI hstacktop hbE'
  refine ⟨as2, ?_, htermE⟩
  rw [executePlan_append, List.length_append, runAsm_append_ok hrunI]
  exact hrunE

/-- ISZERO instantiation. -/
theorem genRegularInstPlan_iszeroLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a : bytes32} {out : String} {base : List Operand}
    (hisz : inst.opcode = Opcode.ISZERO)
    (hops : inst.operands = [Operand.Lit a]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (UInt256.isZero a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_unopLit_sim (by rw [hisz]; rfl) (by rw [hisz]; decide)
    (by simp [computeOperands, hisz]) hops houts hstack0 hlive hfresh hspill
    (fun _ h hg => asmStep_iszero_ok h hg) optimisticSwapPlan_terminator hrel hblock

/-- NOT instantiation. -/
theorem genRegularInstPlan_notLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a : bytes32} {out : String} {base : List Operand}
    (hnot : inst.opcode = Opcode.NOT)
    (hops : inst.operands = [Operand.Lit a]) (houts : inst.outputs = [out])
    (hstack0 : ps.stack = base) (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ (Operand.Var out) ∈ base)
    (hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
        curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             true curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false true
             curBbLabel ps).2 (updateVar out (~~~ a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_unopLit_sim (f := (~~~ ·)) (by rw [hnot]; rfl) (by rw [hnot]; decide)
    (by simp [computeOperands, hnot]) hops houts hstack0 hlive hfresh hspill
    (fun _ h hg => asmStep_not_ok h hg) optimisticSwapPlan_terminator hrel hblock

/-! ## Remaining non-commutative binop instantiations

The same-shape opcodes, each a one-liner over `genRegularInstPlan_nonCommBinopLit_sim` with its `f`
and `asmStep_*_ok` dispatch (mechanical copies of `DIV`/`SHL`/`SLT`). -/

/-- MOD instantiation. -/
theorem genRegularInstPlan_modLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.Mod)
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
             curBbLabel ps).2 (updateVar out (safeMod a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_mod_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SDIV instantiation. -/
theorem genRegularInstPlan_sdivLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SDIV)
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
             curBbLabel ps).2 (updateVar out (safeSdiv a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sdiv_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SMOD instantiation. -/
theorem genRegularInstPlan_smodLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SMOD)
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
             curBbLabel ps).2 (updateVar out (safeSmod a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_smod_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- EXP instantiation. -/
theorem genRegularInstPlan_expLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.Exp)
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
             curBbLabel ps).2 (updateVar out (UInt256.exp a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_exp_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SGT instantiation. -/
theorem genRegularInstPlan_sgtLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SGT)
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
             curBbLabel ps).2 (updateVar out (UInt256.sgt a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sgt_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SHR instantiation (shift; `f a b = b >>> a` pinned, like SHL). -/
theorem genRegularInstPlan_shrLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SHR)
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
             curBbLabel ps).2 (updateVar out (b >>> a) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (f := fun a b => b >>> a)
    (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_shr_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-- SAR instantiation. -/
theorem genRegularInstPlan_sarLit_sim
    {liveness dfg cfg fn inst nextLiveness curBbLabel ps lo vs as prog}
    {a b : bytes32} {out : String} {base : List Operand}
    (hop : inst.opcode = Opcode.SAR)
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
             curBbLabel ps).2 (updateVar out (UInt256.sar a b) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false true curBbLabel ps).1).length :=
  genRegularInstPlan_nonCommBinopLit_sim (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide) (by simp [computeOperands, hop]) hops houts hab
    hstack0 hlive hfresh hspill (fun _ h hg => asmStep_sar_ok h hg)
    optimisticSwapPlan_terminator hrel hblock

/-! ## Block plan asm structure

The bridge from the generator decomposition (`generateBlockPlan_decompose`:
`blockOps = SOLabel bb.label :: cleanOps ++ instOps`) to the asm interpreter: the
compiled block is `AsmLabel bb.label :: (executePlan cleanOps ++ executePlan instOps)`.
This is the shape `genBlockSimulation`'s `runAsm`/`plan_seq_sim` reasoning decomposes —
the leading `AsmLabel` runs via `soLabel_sim`, then the clean and instruction segments. -/

/-- `executePlan` of a label-prefixed plan. -/
theorem executePlan_label_cons (l : String) (ops : List StackOp) :
    executePlan (StackOp.SOLabel l :: ops) = AsmInst.AsmLabel l :: executePlan ops := by
  rw [executePlan_cons]; rfl

/-- Asm structure of a decomposed block plan (`SOLabel :: cleanOps ++ instOps`). -/
theorem executePlan_blockOps (l : String) (cleanOps instOps : List StackOp) :
    executePlan (StackOp.SOLabel l :: cleanOps ++ instOps)
      = AsmInst.AsmLabel l :: (executePlan cleanOps ++ executePlan instOps) := by
  rw [executePlan_append, executePlan_label_cons, List.cons_append]

end EvmYul.Venom.Hol.Codegen

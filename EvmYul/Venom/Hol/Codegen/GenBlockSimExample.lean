/-
Concrete, non-vacuous instance of the block simulation (de-vacuification milestone)

`genBlockSimulation` is admitted in general (its proof needs the per-instruction sims for *every*
instruction shape — var operands, memory, phis — plus the block-body fold + CFG composition). This
file discharges a *concrete* instance end to end, with no `sorry`, to validate the whole pipeline
on a real block:

    generateBlockPlan  →  executePlan  →  asmResolve  →  runAsm

for the single-block STOP function `entry: STOP`. It exercises exactly the restated-capstone shape
(resolved program + threaded `offsetToPc`, Halt case) and the control-flow-free composition
(`asmResolve` is the identity on the label-push-free body; each `asmStep` reduces on the concrete
instruction, so the `offsetToPc` is irrelevant here). It is the first checked, non-vacuous block
simulation, de-risking the general proof.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSim
import EvmYul.Venom.Hol.Codegen.GenInstSim
import EvmYul.Venom.Hol.Codegen.AsmResolveProofs
import EvmYul.Venom.Hol.Codegen.GenBlockSimComp
import EvmYul.Venom.Hol.Codegen.AsmSpillMem

namespace EvmYul.Venom.Hol.Codegen.Example
open EvmYul.Venom.Hol EvmYul EvmYul.Venom.Hol.Codegen

/-- The block `entry: STOP` (single instruction, halts). -/
def stopInst : Instruction := { id := 0, opcode := Opcode.STOP, operands := [], outputs := [] }
def stopBB : BasicBlock := { label := "entry", instructions := [stopInst] }
def exLiveness : DfState (List String) := ⟨[], []⟩
def exCfg : CfgAnalysis := ⟨[], [], [], [], []⟩
def stopFn : IrFunction := { name := "main", blocks := [stopBB] }

/-- Core: the resolved program `[JUMPDEST entry ; STOP]` run from `as.pc = 0` halts at `AsmHalt`,
    preserving the terminal relation. (`asmStep_label_ok` then `asmStep_stop_ok`; the `offsetToPc`
    is irrelevant because neither instruction is a JUMP/JUMPI.) -/
theorem stop_runAsm_core
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    ∃ as', runAsm 2 offsetToPc [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState { vs with instIdx := 0 }) as' := by
  have hpc0 : as.pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"].length := by rw [haspc]; decide
  have hpc1 : (asmNext as).pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"].length := by
    show as.pc + 1 < _; rw [haspc]; decide
  have hget0 : [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"].get ⟨as.pc, hpc0⟩
      = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hpc0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext haspc]; rfl
  have hget1 : [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"].get ⟨(asmNext as).pc, hpc1⟩
      = AsmInst.AsmOp "STOP" := by
    rw [show (⟨(asmNext as).pc, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from
          Fin.ext (by show as.pc + 1 = 1; rw [haspc])]; rfl
  refine ⟨asmNext (asmNext as), ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hpc0 (asmStep_label_ok hpc0 hget0)]
    show runAsm 1 offsetToPc _ (asmNext as) = AsmResult.AsmHalt (asmNext (asmNext as))
    unfold runAsm
    rw [asmStep_stop_ok hpc1 hget1]
  · exact venomAsmRel_terminal lo (initPlanState 0) vs as hrel

/-- **Concrete non-vacuous block simulation** (Halt case): the generated + resolved program for the
    single-block STOP function runs from `as.pc = 0` to `AsmHalt`, matching the Venom block step
    (which halts) under `venomAsmTerminalRel`. End-to-end through
    `generateBlockPlan → executePlan → asmResolve → runAsm`; no `sorry`. -/
theorem genBlockSimulation_stop_example
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    let prog := (asmResolve (executePlan (generateBlockPlan exLiveness DfgAnalysis.empty exCfg
                  stopFn stopBB (initPlanState 0)).get!.1)).1
    match runBlock 10 (default : VenomContext) stopBB vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
               venomAsmTerminalRel vs' as'
    | _ => True := by
  have hrun : runBlock 10 (default : VenomContext) stopBB vs
      = ExecResult.Halt (haltState { vs with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
  show match runBlock 10 (default : VenomContext) stopBB vs with
       | ExecResult.Halt vs' =>
           ∃ as', runAsm _ offsetToPc _ as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
       | _ => True
  rw [hrun]
  exact stop_runAsm_core hrel haspc

/-! ## A block with a body instruction: `entry: c := ADD 5 3 ; STOP`

Extends the STOP example with a regular (non-terminator) instruction before the terminator, so the
generated plan has a real body: `[JUMPDEST ; PUSH 3 ; PUSH 5 ; ADD ; STOP]` (operands reversed by
the fixed `computeOperands`; the dead output `c` is not popped because the block is halting). The
control-flow-free body means `asmResolve` is the identity and each `asmStep` is `offsetToPc`-free —
so the run composes the generic dispatch lemmas (`asmStep_label/push/add/stop_ok`) directly with the
threaded `offsetToPc`. The terminal relation only constrains `accounts/transient/returndata/logs`,
all invariant under the body, so it follows from the entry relation (as in the STOP example). -/

def addInst : Instruction := { id := 0, opcode := Opcode.ADD, operands := [Operand.Lit (UInt256.ofNat 5), Operand.Lit (UInt256.ofNat 3)], outputs := ["c"] }
def addStopBB : BasicBlock := { label := "entry", instructions := [addInst, stopInst] }
def addStopFn : IrFunction := { name := "main", blocks := [addStopBB] }

/-- Core: the resolved program `[JUMPDEST ; PUSH b1 ; PUSH b2 ; ADD ; STOP]` run from `as.pc = 0`
    reaches `AsmHalt`, preserving the terminal relation. Generic over the push bytes (their values
    are irrelevant to reaching the halt — only the stack depth matters for the `ADD`). -/
theorem addStop_runAsm_core
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState} {b1 b2 : List byte}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    ∃ as', runAsm 5 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmPush b1, AsmInst.AsmPush b2,
              AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs as' := by
  set prog := [AsmInst.AsmLabel "entry", AsmInst.AsmPush b1, AsmInst.AsmPush b2,
               AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"] with hprogdef
  have hlen : prog.length = 5 := rfl
  set v1 := wordOfBytes (List.toByteArray (List.replicate (32 - b1.length) (0 : byte) ++ b1)) with hv1
  set v2 := wordOfBytes (List.toByteArray (List.replicate (32 - b2.length) (0 : byte) ++ b2)) with hv2
  set s1 : AsmState := asmNext as with hs1
  set s2 : AsmState := { asmNext s1 with stack := v1 :: s1.stack } with hs2
  set s3 : AsmState := { asmNext s2 with stack := v2 :: s2.stack } with hs3
  set s4 : AsmState := { asmNext s3 with stack := (v2 + v1) :: s1.stack } with hs4
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have p3 : s3.pc = 3 := by rw [hs3]; show s2.pc + 1 = 3; rw [p2]
  have p4 : s4.pc = 4 := by rw [hs4]; show s3.pc + 1 = 4; rw [p3]
  have hb0 : as.pc < prog.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < prog.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < prog.length := by rw [p2, hlen]; decide
  have hb3 : s3.pc < prog.length := by rw [p3, hlen]; decide
  have hb4 : s4.pc < prog.length := by rw [p4, hlen]; decide
  have g0 : prog.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : prog.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush b1 := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmPush b2 := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have g3 : prog.get ⟨s3.pc, hb3⟩ = AsmInst.AsmOp "ADD" := by
    rw [show (⟨s3.pc, hb3⟩ : Fin _) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext p3]; rfl
  have g4 : prog.get ⟨s4.pc, hb4⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨s4.pc, hb4⟩ : Fin _) = ⟨4, by rw [hlen]; decide⟩ from Fin.ext p4]; rfl
  have e0 : asmStep offsetToPc prog as = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1]; rfl
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK s3 := by rw [asmStep_push_ok hb2 g2]; rfl
  have e3 : asmStep offsetToPc prog s3 = AsmResult.AsmOK s4 := by
    rw [asmStep_add_ok hb3 g3]; exact asmBinop_ok (by rw [hs3, hs2])
  have e4 : asmStep offsetToPc prog s4 = AsmResult.AsmHalt (asmNext s4) := asmStep_stop_ok hb4 g4
  refine ⟨asmNext s4, ?_, ?_⟩
  · rw [show (5 : Nat) = 1+1+1+1+1 from rfl, runAsm_succ_ok hb0 e0, runAsm_succ_ok hb1 e1,
        runAsm_succ_ok hb2 e2, runAsm_succ_ok hb3 e3]
    show runAsm 1 offsetToPc prog s4 = AsmResult.AsmHalt (asmNext s4)
    unfold runAsm; rw [e4]
  · exact venomAsmRel_terminal lo (initPlanState 0) vs as hrel

/-- **Concrete non-vacuous block simulation with a body** (Halt case): the generated + resolved
    program for `entry: c := ADD 5 3 ; STOP` runs from `as.pc = 0` to `AsmHalt`, matching the Venom
    block step under `venomAsmTerminalRel`. Exercises a regular instruction (the operand-order-fixed
    `ADD`) composed with the terminator, end to end. No `sorry`. -/
theorem genBlockSimulation_addStop_example
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    let prog := (asmResolve (executePlan (generateBlockPlan exLiveness DfgAnalysis.empty exCfg
                  addStopFn addStopBB (initPlanState 0)).get!.1)).1
    match runBlock 10 (default : VenomContext) addStopBB vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
               venomAsmTerminalRel vs' as'
    | _ => True := by
  have hrun : runBlock 10 (default : VenomContext) addStopBB vs
      = ExecResult.Halt (haltState { updateVar "c" (UInt256.ofNat 5 + UInt256.ofNat 3)
          { vs with instIdx := 0 } with instIdx := 1 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, addStopBB, addInst,
          stopInst, stepInstBase, execPure2, evalOperand, isTerminator]
  show match runBlock 10 (default : VenomContext) addStopBB vs with
       | ExecResult.Halt vs' =>
           ∃ as', runAsm _ offsetToPc _ as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
       | _ => True
  rw [hrun]
  obtain ⟨as', hrunAsm, hterm⟩ := addStop_runAsm_core hrel haspc
  exact ⟨as', hrunAsm, hterm⟩

/-! ## Cross-block control flow: `entry: JMP next` / `next: STOP`

The asm-side validation of a *cross-block* jump (the one shape the single-block instances can't
exercise): the resolved whole-function program `[JUMPDEST entry ; PUSH <off next> ; JUMP ;
JUMPDEST next ; STOP]` run from `as.pc = 0` follows the `JUMP` to `next`'s list index (via the
whole-function `offsetToPc`) and halts. The `[push-label ; JUMP]` segment is discharged by
`resolved_jump_sim` (the cross-block control-flow atom), composed with the surrounding label/STOP
steps via `runAsm_add_ok`. The Venom `runBlocks` for this function reduces to `Halt` (entry's `JMP`
flows to `next`, which `STOP`s) — the asm side here is the novel piece. -/

/-- The resolved whole-function program for `entry: JMP next` / `next: STOP`: the `JMP` lowers to
    `[push-label next ; JUMP]`, and `asmResolve` turns the label push into `AsmPush <byte offset of
    next>` (`= padBytes symbolSize (encodeNumBytes 5)` here, the `resolveInst` form). -/
def jmpProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 5)),
   AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "STOP"]

/-- **Cross-block control-flow validation** (asm side): the resolved 2-block program runs from
    `as.pc = 0` to `AsmHalt`, the `JUMP` resolving to `next`'s list index 3 via the whole-function
    `offsetToPc = [(5,3),(0,0)]` (byte offset 5 ↦ index 3). The `[push-label ; JUMP]` segment is
    `resolved_jump_sim`; the rest is the leading `JUMPDEST entry` and trailing `JUMPDEST next ;
    STOP`, sequenced by `runAsm_add_ok`. No `sorry`. -/
theorem jmp_runAsm_core
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    ∃ as', runAsm 5 ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as
             = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs as' := by
  have hlen : jmpProg.length = 5 := rfl
  have hb0 : as.pc < jmpProg.length := by rw [haspc, hlen]; decide
  have g0 : jmpProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  set s1 : AsmState := asmNext as with hs1
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have hb1 : s1.pc < jmpProg.length := by rw [p1, hlen]; decide
  have hb2 : s1.pc + 1 < jmpProg.length := by rw [p1, hlen]; decide
  have gpush : jmpProg.get ⟨s1.pc, hb1⟩
      = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have gjump : jmpProg.get ⟨s1.pc + 1, hb2⟩ = AsmInst.AsmOp "JUMP" := by
    have h2v : s1.pc + 1 = 2 := by rw [p1]
    conv_lhs => rw [show (⟨s1.pc + 1, hb2⟩ : Fin jmpProg.length) = ⟨2, by rw [hlen]; decide⟩ from
                  Fin.ext h2v]
    rfl
  have hjump2 := resolved_jump_sim (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
      (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (prog := jmpProg) (s := s1)
      (target := "next") (off := 5) (idx := 3)
      hb1 gpush (by decide) (by decide) hb2 gjump (by decide)
  set s3 : AsmState := { s1 with pc := 3 } with hs3
  have p3 : s3.pc = 3 := rfl
  have hb3 : s3.pc < jmpProg.length := by rw [p3, hlen]; decide
  have g3 : jmpProg.get ⟨s3.pc, hb3⟩ = AsmInst.AsmLabel "next" := by
    rw [show (⟨s3.pc, hb3⟩ : Fin _) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext p3]; rfl
  set s4 : AsmState := asmNext s3 with hs4
  have p4 : s4.pc = 4 := by rw [hs4]; show s3.pc + 1 = 4; rw [p3]
  have hb4 : s4.pc < jmpProg.length := by rw [p4, hlen]; decide
  have g4 : jmpProg.get ⟨s4.pc, hb4⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨s4.pc, hb4⟩ : Fin _) = ⟨4, by rw [hlen]; decide⟩ from Fin.ext p4]; rfl
  refine ⟨asmNext s4, ?_, ?_⟩
  · rw [show (5 : Nat) = 1 + (2 + 2) from rfl,
        runAsm_add_ok (m := 2 + 2) (runAsm_succ_ok (n := 0) hb0 (asmStep_label_ok hb0 g0))]
    rw [runAsm_add_ok (m := 2) hjump2]
    rw [runAsm_succ_ok (n := 1) hb3 (asmStep_label_ok hb3 g3)]
    show runAsm 1 _ jmpProg s4 = AsmResult.AsmHalt (asmNext s4)
    unfold runAsm; rw [asmStep_stop_ok hb4 g4]
  · exact venomAsmRel_terminal lo (initPlanState 0) vs as hrel

/-! ## Full two-block `hfsim` (entry: JMP next / next: STOP), end to end

Wraps the cross-block asm validation into a complete, concrete, non-vacuous `genFnSimulation`-shaped
`hfsim`: the Venom `runBlocks` for the 2-block function (entry's `JMP` flows to `next`, which `STOP`s)
matches the resolved whole-function program run, via `hfsim_jmp_then_halt`. The entry block's asm run
is discharged by `hentryAsm_bare_jmp` (JUMPDEST ; resolved push-label ; JUMP, landing at `next`'s pc 3
through `offsetToPc[5] = 3`), the terminal block's by `hasm_stop` (JUMPDEST ; STOP -> AsmHalt). The
Venom side — `runBlocks`, fuel, the CFG walk — is fully discharged by `hfsim_jmp_then_halt`. No
`sorry`: the first concrete non-vacuous *multi-block* simulation. -/

def jmpInst : Instruction :=
  { id := 0, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def jmpEntryBB : BasicBlock := { label := "entry", instructions := [jmpInst] }
def stopNextBB : BasicBlock := { label := "next", instructions := [stopInst] }
def jmpStopFn : IrFunction := { name := "main", blocks := [jmpEntryBB, stopNextBB] }

theorem hfsim_jmp_stop_example
    {fuel : Nat} {ctx : VenomContext} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {ps : PlanState}
    (hcurbb : vs.currentBb = "entry") (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo ps vs as) (haspc : as.pc = 0) :
    match runBlocks fuel ctx jmpStopFn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm jmpProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as
                 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm jmpProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as
                 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm jmpProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as
                 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hlen : jmpProg.length = 5 := rfl
  -- entry block asm run: JUMPDEST ; push-label next ; JUMP  ->  AsmOK at next's pc (3)
  have hbLabel : asmBlockAt jmpProg as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]
    refine ⟨by decide, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    interval_cases j
    rfl
  have hpc1 : as.pc + 1 < jmpProg.length := by rw [haspc, hlen]; decide
  have hpush : jmpProg.get ⟨as.pc + 1, hpc1⟩
      = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
    have e : as.pc + 1 = 1 := by omega
    simp only [e]; rfl
  have hpc2 : as.pc + 2 < jmpProg.length := by rw [haspc, hlen]; decide
  have hjump : jmpProg.get ⟨as.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
    have e : as.pc + 2 = 2 := by omega
    simp only [e]; rfl
  obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
    hentryAsm_bare_jmp (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
      (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (off := 5) (idx := 3)
      hrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
  -- terminal block asm run from asMid (pc 3): JUMPDEST next ; STOP  ->  AsmHalt
  have hblockT : asmBlockAt jmpProg asMid.pc (executePlan [StackOp.SOLabel "next", StackOp.SOEmit "STOP"]) := by
    rw [hpcMid]
    refine ⟨by decide, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j <;> rfl
  have hasm := hasm_stop (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat))
    (budget := jmpProg.length - 3) hrelMid hblockT (by decide)
  -- assemble via hfsim_jmp_then_halt (the Venom side is fully discharged inside)
  have hstep_jmp : stepInstBase jmpInst { vs with instIdx := 0 }
      = ExecResult.OK (jumpTo "next" { vs with instIdx := 0 }) := rfl
  have hstep_stop : ∀ s : VenomState, stepInstBase stopInst s = ExecResult.Halt (haltState s) :=
    fun _ => rfl
  refine hfsim_jmp_then_halt
    (entryBb := jmpEntryBB) (termBb := stopNextBB) (n := 3)
    (efront := []) (eterm := jmpInst) (ehd := jmpInst) (etl := [])
    (esEnd := { vs with instIdx := 0 }) (sMid := jumpTo "next" { vs with instIdx := 0 })
    (tfront := []) (tterm := stopInst) (thd := stopInst) (ttl := [])
    (tsEnd := { jumpTo "next" { vs with instIdx := 0 } with instIdx := 0 })
    (tsEnd' := haltState { jumpTo "next" { vs with instIdx := 0 } with instIdx := 0 })
    ?_ rfl rfl (by decide) (by simp) rfl hstep_jmp (by decide) (by simp [jumpTo, hvshalt]) hrunE
    (by rw [hlen]; decide) ?_ rfl rfl (by decide) (by simp) rfl (hstep_stop _) hasm
  · show lookupBlock vs.currentBb jmpStopFn.blocks = some jmpEntryBB
    rw [hcurbb]; rfl
  · show lookupBlock (jumpTo "next" { vs with instIdx := 0 }).currentBb jmpStopFn.blocks = some stopNextBB
    rfl

/-! ## Multi-block `codegen_correct` via `runBlocks_walk`'s per-block `hbsim`

`hfsim_jmp_stop_example` composes the two blocks with the bespoke `hfsim_jmp_then_halt`. Here we instead
drive the **general** CFG-walk engine `runBlocks_walk` directly with a **pc-tracking two-disjunct
`Entry`** relation — the honest multi-block `hbsim` supply. `Entry s asm N` says either (entry block)
`s.currentBb = "entry" ∧ asm at pc 0 ∧ N = 5` or (successor) `s.currentBb = "next" ∧ asm at pc 3 ∧
N = 2`. The entry-block `hbsim` runs the `JMP` (`OK (jumpTo "next" …)`, not halted) and supplies the
walk's *budget transition* `runAsm 5 … = runAsm 2 …` to the successor's pc via `hentryAsm_bare_jmp` +
`runAsm_add_ok`, re-establishing `Entry` at the `next` disjunct; the successor `hbsim` halts via
`hasm_stop`. The simulated program `jmpProg` **is** the real codegen output (`codegen_jmp_stop_prog_eq`).
This is the multi-block generalisation of the single-block `codegen_correct_singleBlockHalt`. -/

def jmpStopCtx : VenomContext := { functions := [jmpStopFn], entry := some "main" }

/-- `jmpProg` is exactly the real codegen output for `jmpStopFn`. -/
theorem codegen_jmp_stop_prog_eq :
    (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 = jmpProg
    ∧ (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2 = ([(5, 3), (0, 0)] : AssocList Nat Nat) :=
  ⟨rfl, rfl⟩

/-- **Multi-block codegen correctness** for `entry: JMP next / next: STOP`, over the real codegen
    program, discharged by `runBlocks_walk` with a pc-tracking `Entry`. -/
theorem codegen_correct_jmp_stop {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jmpStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 5 ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm 5 ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm 5 ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpProg as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hrc : runContext 10 jmpStopCtx vs
      = runBlocks 10 jmpStopCtx jmpStopFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp only [runContext, show jmpStopCtx.entry = some "main" from rfl,
      show lookupFunction "main" jmpStopCtx.functions = some jmpStopFn from rfl,
      runFunction, show fnEntryLabel jmpStopFn = some "entry" from rfl]
  rw [hrc]
  refine runBlocks_walk
    (Entry := fun s asm N =>
      (s.currentBb = "entry" ∧ s.halted = false ∧ asm.pc = 0 ∧ N = 5 ∧ venomAsmRel lo (initPlanState 0) s asm) ∨
      (s.currentBb = "next" ∧ asm.pc = 3 ∧ N = 2 ∧ venomAsmRel lo (initPlanState 0) s asm))
    ?_ 10 _ as 5 (Or.inl ⟨rfl, hvshalt, haspc, rfl, hrel⟩)
  intro s asm N f' bb hE hlk
  rcases hE with ⟨hcur, hhalt, hpc, hN, hvrel⟩ | ⟨hcur, hpc, hN, hvrel⟩
  · have hbbeq : bb = jmpEntryBB := by
      rw [hcur, show lookupBlock "entry" jmpStopFn.blocks = some jmpEntryBB from rfl] at hlk
      exact (Option.some.inj hlk).symm
    subst hbbeq
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, jmpEntryBB, jmpInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx jmpEntryBB s = ExecResult.OK (jumpTo "next" { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jmpEntryBB, jmpInst, stepInstBase, isTerminator, jumpTo, hhalt]
      rw [hrb]
      have hnothalt : (jumpTo "next" { s with instIdx := 0 }).halted = false := by simp [jumpTo, hhalt]
      simp only [hnothalt, Bool.false_eq_true, if_false]
      have hbLabel : asmBlockAt jmpProg asm.pc (executePlan [StackOp.SOLabel "entry"]) := by
        rw [hpc]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hpc1 : asm.pc + 1 < jmpProg.length := by rw [hpc]; decide
      have hpush : jmpProg.get ⟨asm.pc + 1, hpc1⟩
          = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
        have e : asm.pc + 1 = 1 := by rw [hpc]
        conv_lhs => rw [show (⟨asm.pc + 1, hpc1⟩ : Fin jmpProg.length) = ⟨1, by decide⟩ from Fin.ext e]
        rfl
      have hpc2 : asm.pc + 2 < jmpProg.length := by rw [hpc]; decide
      have hjump : jmpProg.get ⟨asm.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
        have e : asm.pc + 2 = 2 := by rw [hpc]
        conv_lhs => rw [show (⟨asm.pc + 2, hpc2⟩ : Fin jmpProg.length) = ⟨2, by decide⟩ from Fin.ext e]
        rfl
      obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
        hentryAsm_bare_jmp (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
          (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (off := 5) (idx := 3) hvrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
      refine ⟨asMid, 2, ?_, Or.inr ⟨by simp [jumpTo], hpcMid, rfl, hrelMid⟩⟩
      rw [hN, show (5 : Nat) = 3 + 2 from rfl, runAsm_add_ok hrunE]
  · have hbbeq : bb = stopNextBB := by
      rw [hcur, show lookupBlock "next" jmpStopFn.blocks = some stopNextBB from rfl] at hlk
      exact (Option.some.inj hlk).symm
    subst hbbeq
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, stopNextBB, stopInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx stopNextBB s = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopNextBB, stopInst, stepInstBase]
      rw [hrb, hN]
      have hblockT : asmBlockAt jmpProg asm.pc (executePlan [StackOp.SOLabel "next", StackOp.SOEmit "STOP"]) := by
        rw [hpc]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 2 := hj; interval_cases j <;> rfl
      exact hasm_stop (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (budget := 2) hvrel hblockT (by decide)

/-! ## Conditional control flow: `entry: JNZ 1 then else` (branch taken)

The asm-side validation of a *conditional* branch — the CFG shape the linear `jmp_runAsm_core` can't
exercise. A JNZ block lowers to `[push-label ifNz ; JUMPI ; push-label ifZ ; JUMP]`; with a non-zero
condition on the stack the `JUMPI` is **taken** (`resolved_jumpi_taken_sim`), consuming `cond` and the
pushed destination and landing at `then`'s list index (3 ↦ here `then` at idx 6 via `offsetToPc[6] = 6`),
skipping the `[push-label else ; JUMP]` fall-through entirely. The resolved 3-block program
`[JUMPDEST entry ; PUSH 1 ; push-label then ; JUMPI ; push-label else ; JUMP ; JUMPDEST then ; STOP ;
JUMPDEST else ; STOP]` then `STOP`s at `then`. The pushed `cond = 1 ≠ 0` is discharged through
`pushed_offset_toNat`; the `[push-label ; JUMPI]` segment is the conditional-branch atom, sequenced
with the surrounding label/push/STOP steps via `runAsm_add_ok`. No `sorry`. -/

/-- The resolved branching program for `entry: JNZ 1 then else / then: STOP / else: STOP`. -/
def jnzProg : List AsmInst :=
  [AsmInst.AsmLabel "entry",
   AsmInst.AsmPush (encodeNumBytes 1),
   AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 11)),
   AsmInst.AsmOp "JUMPI",
   AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 13)),
   AsmInst.AsmOp "JUMP",
   AsmInst.AsmLabel "then",
   AsmInst.AsmOp "STOP",
   AsmInst.AsmLabel "else",
   AsmInst.AsmOp "STOP"]

/-- **Conditional control-flow validation** (asm side): the resolved branching program runs from
    `as.pc = 0` to `AsmHalt`, the non-zero condition making the `JUMPI` jump to `then`'s list index
    6 via the whole-function `offsetToPc = [(6,6),(8,8)]` and skip the `else` fall-through. The
    `[push-label then ; JUMPI]` segment is `resolved_jumpi_taken_sim`; the rest is the leading
    `JUMPDEST ; PUSH cond` and trailing `JUMPDEST then ; STOP`, sequenced by `runAsm_add_ok`. No
    `sorry`: the first concrete conditional-branch asm validation. -/
theorem jnz_runAsm_core
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    ∃ as', runAsm 6 ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as
             = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs as' := by
  set otp : AssocList Nat Nat := [(11, 6), (13, 8)] with hotp
  have hlen : jnzProg.length = 10 := rfl
  set s1 : AsmState := asmNext as with hs1
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  set cond : bytes32 := wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes 1).length) (0 : byte) ++ encodeNumBytes 1)) with hcond
  set s2 : AsmState := { asmNext s1 with stack := cond :: s1.stack } with hs2
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  set s3 : AsmState := { s2 with stack := s1.stack, pc := 6 } with hs3
  have p3 : s3.pc = 6 := rfl
  set s4 : AsmState := asmNext s3 with hs4
  have p4 : s4.pc = 7 := by rw [hs4]; show s3.pc + 1 = 7; rw [p3]
  have hb0 : as.pc < jnzProg.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < jnzProg.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < jnzProg.length := by rw [p2, hlen]; decide
  have hb3 : s3.pc < jnzProg.length := by rw [p3, hlen]; decide
  have hb4 : s4.pc < jnzProg.length := by rw [p4, hlen]; decide
  have g0 : jnzProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : jnzProg.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 1) := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have g6 : jnzProg.get ⟨s3.pc, hb3⟩ = AsmInst.AsmLabel "then" := by
    rw [show (⟨s3.pc, hb3⟩ : Fin _) = ⟨6, by rw [hlen]; decide⟩ from Fin.ext p3]; rfl
  have g7 : jnzProg.get ⟨s4.pc, hb4⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨s4.pc, hb4⟩ : Fin _) = ⟨7, by rw [hlen]; decide⟩ from Fin.ext p4]; rfl
  have p2pc1 : s2.pc + 1 < jnzProg.length := by rw [p2, hlen]; decide
  have hpush : jnzProg.get ⟨s2.pc, hb2⟩
      = resolveInst ([("then", 11), ("else", 13)] : AssocList String Nat) (AsmInst.AsmPushLabel "then") := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have hjumpi : jnzProg.get ⟨s2.pc + 1, p2pc1⟩ = AsmInst.AsmOp "JUMPI" := by
    have e : s2.pc + 1 = 3 := by rw [p2]
    conv_lhs => rw [show (⟨s2.pc + 1, p2pc1⟩ : Fin jnzProg.length) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext e]
    rfl
  have hct : cond.toNat = 1 := by rw [hcond]; exact pushed_offset_toNat 1 (by norm_num)
  have hcondne : cond ≠ EvmYul.UInt256.ofNat 0 := by
    intro h; rw [h, EvmYul.uint256_ofNat_toNat] at hct; simp at hct
  have hpushstep : asmStep otp jnzProg s1 = AsmResult.AsmOK s2 := by
    rw [asmStep_push_ok hb1 g1]; rfl
  have hjmpi2 : runAsm 2 otp jnzProg s2 = AsmResult.AsmOK s3 :=
    resolved_jumpi_taken_sim (offsets := ([("then", 11), ("else", 13)] : AssocList String Nat))
      (offsetToPc := otp) (prog := jnzProg) (s := s2) (ifNz := "then") (off := 11) (idx := 6)
      (stk := s1.stack) rfl hcondne hb2 hpush (by decide) (by decide) p2pc1 hjumpi (by decide)
  refine ⟨asmNext s4, ?_, ?_⟩
  · rw [show (6 : Nat) = 1 + (1 + (2 + (1 + 1))) from rfl,
        runAsm_add_ok (m := 1 + (2 + (1 + 1))) (runAsm_succ_ok (n := 0) hb0 (asmStep_label_ok hb0 g0))]
    rw [runAsm_add_ok (m := 2 + (1 + 1)) (runAsm_succ_ok (n := 0) hb1 hpushstep)]
    rw [runAsm_add_ok (m := 1 + 1) hjmpi2]
    rw [runAsm_add_ok (m := 1) (runAsm_succ_ok (n := 0) hb3 (asmStep_label_ok hb3 g6))]
    show runAsm 1 otp jnzProg s4 = AsmResult.AsmHalt (asmNext s4)
    unfold runAsm; rw [asmStep_stop_ok hb4 g7]
  · exact venomAsmRel_terminal lo (initPlanState 0) vs as hrel

/-! ## Full conditional-branch function: `entry: JNZ 1 then else / then: STOP / else: STOP`

The complete (Venom + asm), concrete, non-vacuous `genFnSimulation`-shaped sim for a *branching*
function — the conditional-control-flow counterpart of `hfsim_jmp_stop_example`. The Venom
`runBlocks` for the 3-block function (entry's `JNZ 1 …` takes the `then` edge, which `STOP`s) matches
the resolved whole-function program run, via `hfsim_jmp_then_halt` (which accepts a JNZ entry since
`JNZ` produces an `OK (jumpTo …)` just like `JMP`). The entry block's asm — `JUMPDEST ; PUSH 1 ;
push-label then ; JUMPI(taken)` — runs 4 steps to `then`'s entry index (6) via the **realistic**
whole-function `offsetToPc = [(11,6),(13,8)]` (`then` at byte 11, `else` at byte 13 — the byte offsets
`asmResolve` computes from the `PUSH1`/`PUSH2` widths), skipping the `else` fall-through; the
condition `1 ≠ 0` (`pushed_offset_toNat`) is what takes the branch. The cond push/JUMPI-pop restores
the stack, so `asMid = {as with pc := 6}` and `venomAsmRel` carries through (`venomAsmRel_setPc`). The
terminal block's asm is `hasm_stop`. No `sorry`: the first concrete non-vacuous *branching*
whole-function simulation. -/

def jnzInstR : Instruction :=
  { id := 0, opcode := Opcode.JNZ,
    operands := [Operand.Lit (UInt256.ofNat 1), Operand.Label "then", Operand.Label "else"], outputs := [] }
def jnzEntryR : BasicBlock := { label := "entry", instructions := [jnzInstR] }
def thenBB : BasicBlock := { label := "then", instructions := [stopInst] }
def elseBB : BasicBlock := { label := "else", instructions := [stopInst] }
def jnzStopFnR : IrFunction := { name := "main", blocks := [jnzEntryR, thenBB, elseBB] }

theorem hfsim_jnz_stop_example
    {fuel : Nat} {ctx : VenomContext} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState}
    (hcurbb : vs.currentBb = "entry") (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    match runBlocks fuel ctx jnzStopFnR vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm jnzProg.length ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as
                 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm jnzProg.length ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as
                 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm jnzProg.length ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as
                 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  set otp : AssocList Nat Nat := [(11, 6), (13, 8)] with hotp
  have hlen : jnzProg.length = 10 := rfl
  set s1 : AsmState := asmNext as with hs1
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  set cond : bytes32 := wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes 1).length) (0 : byte) ++ encodeNumBytes 1)) with hcond
  set s2 : AsmState := { asmNext s1 with stack := cond :: s1.stack } with hs2
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  set asMid : AsmState := { as with pc := 6 } with hasMid
  have hb0 : as.pc < jnzProg.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < jnzProg.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < jnzProg.length := by rw [p2, hlen]; decide
  have g0 : jnzProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : jnzProg.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 1) := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have p2pc1 : s2.pc + 1 < jnzProg.length := by rw [p2, hlen]; decide
  have hpush : jnzProg.get ⟨s2.pc, hb2⟩
      = resolveInst ([("then", 11), ("else", 13)] : AssocList String Nat) (AsmInst.AsmPushLabel "then") := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have hjumpi : jnzProg.get ⟨s2.pc + 1, p2pc1⟩ = AsmInst.AsmOp "JUMPI" := by
    have e : s2.pc + 1 = 3 := by rw [p2]
    conv_lhs => rw [show (⟨s2.pc + 1, p2pc1⟩ : Fin jnzProg.length) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext e]
    rfl
  have hct : cond.toNat = 1 := by rw [hcond]; exact pushed_offset_toNat 1 (by norm_num)
  have hcondne : cond ≠ EvmYul.UInt256.ofNat 0 := by
    intro h; rw [h, EvmYul.uint256_ofNat_toNat] at hct; simp at hct
  have hpushstep : asmStep otp jnzProg s1 = AsmResult.AsmOK s2 := by
    rw [asmStep_push_ok hb1 g1]; rfl
  have hjmpi2 : runAsm 2 otp jnzProg s2 = AsmResult.AsmOK { s2 with stack := s1.stack, pc := 6 } :=
    resolved_jumpi_taken_sim (offsets := ([("then", 11), ("else", 13)] : AssocList String Nat))
      (offsetToPc := otp) (prog := jnzProg) (s := s2) (ifNz := "then") (off := 11) (idx := 6)
      (stk := s1.stack) rfl hcondne hb2 hpush (by decide) (by decide) p2pc1 hjumpi (by decide)
  have hmideq : ({ s2 with stack := s1.stack, pc := 6 } : AsmState) = asMid := by
    simp only [hasMid, hs2, hs1, asmNext]
  have hentryAsm : runAsm 4 otp jnzProg as = AsmResult.AsmOK asMid := by
    rw [show (4 : Nat) = 1 + (1 + 2) from rfl,
        runAsm_add_ok (m := 1 + 2) (runAsm_succ_ok (n := 0) hb0 (asmStep_label_ok hb0 g0))]
    rw [runAsm_add_ok (m := 2) (runAsm_succ_ok (n := 0) hb1 hpushstep)]
    rw [hjmpi2, hmideq]
  have hpcMid : asMid.pc = 6 := rfl
  have hblockT : asmBlockAt jnzProg asMid.pc (executePlan [StackOp.SOLabel "then", StackOp.SOEmit "STOP"]) := by
    rw [hpcMid]
    refine ⟨by decide, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j <;> rfl
  have hrelMid : venomAsmRel lo (initPlanState 0) vs asMid := venomAsmRel_setPc hrel
  have hasm := hasm_stop (offsetToPc := otp) (budget := jnzProg.length - 4) hrelMid hblockT (by rw [hlen]; decide)
  have hstep_jnz : stepInstBase jnzInstR { vs with instIdx := 0 }
      = ExecResult.OK (jumpTo "then" { vs with instIdx := 0 }) := by
    simp [stepInstBase, jnzInstR, evalOperand]; intro h; exact absurd h (by decide)
  have hstep_stop : stepInstBase stopInst ({ jumpTo "then" { vs with instIdx := 0 } with instIdx := 0 })
      = ExecResult.Halt (haltState ({ jumpTo "then" { vs with instIdx := 0 } with instIdx := 0 })) := rfl
  refine hfsim_jmp_then_halt
    (entryBb := jnzEntryR) (termBb := thenBB) (n := 4)
    (efront := []) (eterm := jnzInstR) (ehd := jnzInstR) (etl := [])
    (esEnd := { vs with instIdx := 0 }) (sMid := jumpTo "then" { vs with instIdx := 0 })
    (tfront := []) (tterm := stopInst) (thd := stopInst) (ttl := [])
    (tsEnd := { jumpTo "then" { vs with instIdx := 0 } with instIdx := 0 })
    (tsEnd' := haltState { jumpTo "then" { vs with instIdx := 0 } with instIdx := 0 })
    ?_ rfl rfl (by decide) (by simp) rfl hstep_jnz (by decide) (by simp [jumpTo, hvshalt]) hentryAsm
    (by rw [hlen]; decide) ?_ rfl rfl (by decide) (by simp) rfl hstep_stop hasm
  · show lookupBlock vs.currentBb jnzStopFnR.blocks = some jnzEntryR
    rw [hcurbb]; rfl
  · show lookupBlock (jumpTo "then" { vs with instIdx := 0 }).currentBb jnzStopFnR.blocks = some thenBB
    rfl

/-! ## A data-mutating terminator: `entry: SELFDESTRUCT 0`

The first concrete block instance whose terminator carries an operand *and* mutates observable state
(`accounts`). The resolved program is `[JUMPDEST ; PUSH0 ; SELFDESTRUCT]` (single operand ⇒ no
reorder). The terminal relation only constrains `accounts/transient/returndata/logs`; the pushed
beneficiary (`0`) equals the Venom operand (`Lit 0`), so both sides apply the same `selfdestruct`
(`selfdestruct_accounts_congr`) — the account effect agrees. -/

def sdInst : Instruction :=
  { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] }
def sdBB : BasicBlock := { label := "entry", instructions := [sdInst] }
def sdFn : IrFunction := { name := "main", blocks := [sdBB] }

/-- Core: the resolved program `[JUMPDEST ; PUSH0 ; SELFDESTRUCT]` run from `as.pc = 0` halts
    (`AsmHalt`) with the account transfer matching the Venom `SELFDESTRUCT 0`. -/
theorem selfdestruct_runAsm_core
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    ∃ as', runAsm 3 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "SELFDESTRUCT"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (selfdestruct (UInt256.ofNat 0) { vs with instIdx := 0 })) as' := by
  set prog := [AsmInst.AsmLabel "entry", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "SELFDESTRUCT"]
    with hprogdef
  have hlen : prog.length = 3 := rfl
  set v := wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes 0).length) (0 : byte)
              ++ encodeNumBytes 0)) with hvdef
  have hv0 : v = UInt256.ofNat 0 := by
    have h : v.toNat = 0 := by rw [hvdef]; exact pushed_offset_toNat 0 (by norm_num)
    have hval : v.val = (UInt256.ofNat 0).val := Fin.ext (by
      show v.toNat = (UInt256.ofNat 0).toNat; rw [h, uint256_ofNat_toNat]; omega)
    exact congrArg UInt256.mk hval
  set s1 : AsmState := asmNext as with hs1
  set s2 : AsmState := { asmNext s1 with stack := v :: s1.stack } with hs2
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have hb0 : as.pc < prog.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < prog.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < prog.length := by rw [p2, hlen]; decide
  have g0 : prog.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : prog.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 0) := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmOp "SELFDESTRUCT" := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have e0 : asmStep offsetToPc prog as = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1]; rfl
  have e2 : asmStep offsetToPc prog s2
      = AsmResult.AsmHalt { asmNext s2 with stack := s1.stack, accounts := (selfdestruct v s2.toVenomState).accounts } := by
    rw [asmStep_selfdestruct_ok hb2 g2, asmSelfdestruct_ok (by rw [hs2])]
  obtain ⟨_, _, _, hAcc, hTrans, hRet, hLog, hCall, _, _, _, _⟩ := hrel
  refine ⟨{ asmNext s2 with stack := s1.stack, accounts := (selfdestruct v s2.toVenomState).accounts }, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + 1 + 1 from rfl, runAsm_succ_ok hb0 e0, runAsm_succ_ok hb1 e1]
    show runAsm 1 offsetToPc prog s2 = _
    unfold runAsm; rw [e2]
  · refine ⟨?_, hTrans, hRet, hLog⟩
    rw [hv0]
    exact selfdestruct_accounts_congr (UInt256.ofNat 0) hAcc hCall

/-- **Concrete non-vacuous block simulation with an operand-carrying, state-mutating terminator**:
    the generated + resolved program for `entry: SELFDESTRUCT 0` runs from `as.pc = 0` to `AsmHalt`,
    matching the Venom block step (which halts after the account transfer) under
    `venomAsmTerminalRel`. End-to-end through `generateBlockPlan → executePlan → asmResolve → runAsm`;
    no `sorry`. -/
theorem genBlockSimulation_selfdestruct_example
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    let prog := (asmResolve (executePlan (generateBlockPlan exLiveness DfgAnalysis.empty exCfg
                  sdFn sdBB (initPlanState 0)).get!.1)).1
    match runBlock 10 (default : VenomContext) sdBB vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
               venomAsmTerminalRel vs' as'
    | _ => True := by
  have hstep : stepInstBase { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } { vs with instIdx := 0 }
      = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { vs with instIdx := 0 })) :=
    stepInstBase_selfdestruct rfl rfl rfl
  have hrun : runBlock 10 (default : VenomContext) sdBB vs
      = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { vs with instIdx := 0 })) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, sdBB, sdInst, hstep]
  show match runBlock 10 (default : VenomContext) sdBB vs with
       | ExecResult.Halt vs' =>
           ∃ as', runAsm _ offsetToPc _ as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
       | _ => True
  rw [hrun]
  exact selfdestruct_runAsm_core hrel haspc

/-! ## Non-vacuous codegen correctness for a concrete function

`codegen_correct` is vacuously true (its `codegen … = some bytecode` hypothesis is unsatisfiable via
the `none`-stub `generateContextPlan`). Here is the *real* (fuel) pipeline `codegenFuel` applied to a
concrete single-block function `main: STOP`: it produces bytecode AND the codegen-correctness
conclusion genuinely holds — `runContext` halts, and the resolved whole-function program
`[JUMPDEST entry; STOP; JUMPDEST revert; PUSH0; DUP1; REVERT]` reaches `AsmHalt` (the `STOP` halts at
index 1, before the revert postamble) with the observable state in agreement. The first non-vacuous
codegen-correctness statement for a real function. -/

def stopCtx : VenomContext := { functions := [stopFn], entry := some "main" }
def stopFnEomMap : AssocList String Nat := AssocList.insert String Nat [] "main" 0
def stopProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP", AsmInst.AsmLabel "revert",
   AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "DUP1", AsmInst.AsmOp "REVERT"]

theorem codegenFuel_correct_stop_nonvacuous
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (∃ bytecode, codegenFuel 100 stopCtx stopFnEomMap [] = some bytecode) ∧
    (match runContext 100 stopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 2 offsetToPc stopProg as = AsmResult.AsmHalt as' ∧
            finalStateRel vs' as'
     | _ => True) := by
  obtain ⟨_, _, _, hAcc, hTrans, hRet, hLog, _⟩ := hrel
  refine ⟨⟨_, rfl⟩, ?_⟩
  have hrc : runContext 100 stopCtx vs
      = ExecResult.Halt (haltState { vs with prevBb := none, currentBb := "entry", instIdx := 0 }) := by
    simp [runContext, stopCtx, lookupFunction, runFunction, fnEntryLabel, stopFn, stopBB,
      runBlocks, lookupBlock, runBlock, execBlock, getInstruction, stopInst, stepInstBase,
      evalPhis, phiPrefixLength]
  rw [hrc]
  have hb0 : as.pc < stopProg.length := by rw [haspc]; decide
  have hb1 : (asmNext as).pc < stopProg.length := by show as.pc + 1 < _; rw [haspc]; decide
  have hget0 : stopProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext haspc]; rfl
  have hget1 : stopProg.get ⟨(asmNext as).pc, hb1⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨(asmNext as).pc, hb1⟩ : Fin _) = ⟨1, by decide⟩ from
          Fin.ext (by show as.pc + 1 = 1; rw [haspc])]; rfl
  refine ⟨asmNext (asmNext as), ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hb0 (asmStep_label_ok hb0 hget0)]
    show runAsm 1 offsetToPc stopProg (asmNext as) = AsmResult.AsmHalt (asmNext (asmNext as))
    unfold runAsm; rw [asmStep_stop_ok hb1 hget1]
  · exact ⟨hAcc, hTrans, hRet, hLog⟩

/-! ## The de-vacuified `codegen_correct`, instantiated with the *real* codegen program

`codegenFuel_correct_stop_nonvacuous` uses a hand-written `stopProg`. Here we instead instantiate the
now-real `codegen_correct` (CodegenCorrectness) with `prog` tied to the **actual** generator output
`(asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1`. `codegen_correct_singleBlockHalt` is a
reusable single-block, direct-halt wrapper: it peels `runContext` to the entry function's `runBlocks`,
runs `runBlocks_walk`, and discharges the per-block `hbsim` from the caller's Venom halt fact
(`hrunHalt`, fuel `k+1`), out-of-fuel fact (`hrun0`, fuel `0` ⇒ the trivial arm) and asm terminal sim
(`hasm`). Instantiated for `stopFn` (pure halt, → `[JUMPDEST ; STOP]`) and `sdFn` (SELFDESTRUCT — a
*state-mutating* halt, → `[JUMPDEST ; PUSH0 ; SELFDESTRUCT]`); the simulated program is the real codegen
output in both cases, closing the hand-written-`prog` gap. -/

/-- **Reusable single-block, direct-halt codegen correctness.** A context whose entry function is a
    single block that halts directly (STOP/SELFDESTRUCT/…) simulates the real codegen program, given
    the block's Venom halt behaviour (`hrunHalt`/`hrun0`) and its asm terminal sim (`hasm`). Peels
    `runContext` → the entry `runBlocks` and runs `runBlocks_walk`; the single-block `hbsim` is the
    caller's block facts. -/
theorem codegen_correct_singleBlockHalt
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {bb : BasicBlock}
    {lo : AssocList String Nat} {haltFn : VenomState → VenomState}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hblocks : fn.blocks = [bb])
    (hrunHalt : ∀ (k : Nat) (s : VenomState), runBlock (k+1) ctx bb s = ExecResult.Halt (haltFn s))
    (hrun0 : ∀ (s : VenomState), runBlock 0 ctx bb s = ExecResult.Error "out of fuel")
    (hasm : ∀ (s : VenomState) (asm : AsmState), venomAsmRel lo (initPlanState 0) s asm → asm.pc = 0 →
        ∃ asm', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel (haltFn s) asm')
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl)
    (Entry := fun s asm N => venomAsmRel lo (initPlanState 0) s asm ∧ asm.pc = 0 ∧
       N = (asmResolve (executePlan ops)).1.length)
    hplan hent hlk hlbl ?_ ⟨hrel, haspc, rfl⟩
  intro s asm N f' bb' hE hlk'
  obtain ⟨hvrel, hpc, hN⟩ := hE
  have hbb : bb' = bb := by
    rw [hblocks, lookupBlock] at hlk'
    simpa using List.mem_of_find?_eq_some hlk'
  subst hbb
  cases f' with
  | zero => simp only [hrun0 s]
  | succ k => rw [hrunHalt k s, hN]; exact hasm s asm hvrel hpc

/-- `codegen_correct` fired for `stopCtx` (`main: STOP`) over the real codegen output. -/
theorem codegen_correct_stop {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 stopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_singleBlockHalt (fuel := 10) (ctx := stopCtx) (fn := stopFn) (bb := stopBB)
    (entryName := "main") (entryLbl := "entry")
    (haltFn := fun s => haltState { s with instIdx := 0 })
    (ops := (generateFnPlan stopFn 0 0).get!.1) (psFinal := (generateFnPlan stopFn 0 0).get!.2)
    rfl rfl rfl rfl rfl ?_ ?_ ?_ hrel haspc
  · intro k s; simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
  · intro s; simp [runBlock, evalPhis, execBlock, stopBB, stopInst]
  · intro s asm hv hp; exact stop_runAsm_core hv hp

/-! ## Non-vacuous codegen correctness for a *state-mutating* function

Extends the STOP milestone to a function that carries an operand and changes observable state:
`main: SELFDESTRUCT 0`. The resolved program is `[JUMPDEST entry; PUSH0; SELFDESTRUCT; JUMPDEST revert;
PUSH0; DUP1; REVERT]` — the `SELFDESTRUCT` halts at index 2 (before the postamble), transferring the
contract's balance; both `runContext` and the asm apply the same `selfdestruct`, so `finalStateRel`'s
`accounts` match. The first non-vacuous codegen correctness for a contract that *does something*. -/

def sdCtx : VenomContext := { functions := [sdFn], entry := some "main" }
def sdFnEomMap : AssocList String Nat := AssocList.insert String Nat [] "main" 0
def sdProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "SELFDESTRUCT",
   AsmInst.AsmLabel "revert", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "DUP1",
   AsmInst.AsmOp "REVERT"]

theorem codegenFuel_correct_selfdestruct_nonvacuous
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (∃ bytecode, codegenFuel 100 sdCtx sdFnEomMap [] = some bytecode) ∧
    (match runContext 100 sdCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 3 offsetToPc sdProg as = AsmResult.AsmHalt as' ∧
            finalStateRel vs' as'
     | _ => True) := by
  obtain ⟨_, _, _, hAcc, hTrans, hRet, hLog, hCall, _, _, _, _⟩ := hrel
  refine ⟨⟨_, rfl⟩, ?_⟩
  have hstep : stepInstBase { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } { vs with prevBb := none, currentBb := "entry", instIdx := 0 }
      = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { vs with prevBb := none, currentBb := "entry", instIdx := 0 })) :=
    stepInstBase_selfdestruct rfl rfl rfl
  have hrc : runContext 100 sdCtx vs
      = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { vs with prevBb := none, currentBb := "entry", instIdx := 0 })) := by
    simp [runContext, sdCtx, lookupFunction, runFunction, fnEntryLabel, sdFn, sdBB, runBlocks,
      lookupBlock, runBlock, execBlock, getInstruction, sdInst, evalPhis, phiPrefixLength, hstep]
  rw [hrc]
  set v := wordOfBytes (List.toByteArray (List.replicate (32 - (encodeNumBytes 0).length) (0 : byte)
              ++ encodeNumBytes 0)) with hvdef
  have hv0 : v = UInt256.ofNat 0 := by
    have h : v.toNat = 0 := by rw [hvdef]; exact pushed_offset_toNat 0 (by norm_num)
    exact congrArg UInt256.mk (Fin.ext (by
      show v.toNat = (UInt256.ofNat 0).toNat; rw [h, uint256_ofNat_toNat]; omega))
  set s1 : AsmState := asmNext as with hs1
  set s2 : AsmState := { asmNext s1 with stack := v :: s1.stack } with hs2
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have hb0 : as.pc < sdProg.length := by rw [haspc]; decide
  have hb1 : s1.pc < sdProg.length := by rw [p1]; decide
  have hb2 : s2.pc < sdProg.length := by rw [p2]; decide
  have g0 : sdProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext haspc]; rfl
  have g1 : sdProg.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 0) := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext p1]; rfl
  have g2 : sdProg.get ⟨s2.pc, hb2⟩ = AsmInst.AsmOp "SELFDESTRUCT" := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext p2]; rfl
  have e0 : asmStep offsetToPc sdProg as = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
  have e1 : asmStep offsetToPc sdProg s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1]; rfl
  have e2 : asmStep offsetToPc sdProg s2
      = AsmResult.AsmHalt { asmNext s2 with stack := s1.stack, accounts := (selfdestruct v s2.toVenomState).accounts } := by
    rw [asmStep_selfdestruct_ok hb2 g2, asmSelfdestruct_ok (by rw [hs2])]
  refine ⟨{ asmNext s2 with stack := s1.stack, accounts := (selfdestruct v s2.toVenomState).accounts }, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + 1 + 1 from rfl, runAsm_succ_ok hb0 e0, runAsm_succ_ok hb1 e1]
    show runAsm 1 offsetToPc sdProg s2 = _
    unfold runAsm; rw [e2]
  · refine ⟨?_, hTrans, hRet, hLog⟩
    rw [hv0]
    exact selfdestruct_accounts_congr (UInt256.ofNat 0) hAcc hCall

/-- `codegen_correct` fired for `sdCtx` (`main: SELFDESTRUCT 0`, a *state-mutating* halt) over the real
    codegen output `[JUMPDEST entry ; PUSH0 ; SELFDESTRUCT]` — via the reusable
    `codegen_correct_singleBlockHalt`, demonstrating the de-vacuified `codegen_correct` across a
    non-trivial (account-mutating) terminator, not just STOP. -/
theorem codegen_correct_selfdestruct {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 sdCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_singleBlockHalt (fuel := 10) (ctx := sdCtx) (fn := sdFn) (bb := sdBB)
    (entryName := "main") (entryLbl := "entry")
    (haltFn := fun s => haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 }))
    (ops := (generateFnPlan sdFn 0 0).get!.1) (psFinal := (generateFnPlan sdFn 0 0).get!.2)
    rfl rfl rfl rfl rfl ?_ ?_ ?_ hrel haspc
  · intro k s
    have hstep : stepInstBase { id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } { s with instIdx := 0 } = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) := stepInstBase_selfdestruct rfl rfl rfl
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, sdBB, sdInst, hstep]
  · intro s; simp [runBlock, evalPhis, execBlock, sdBB, sdInst]
  · intro s asm hv hp; exact selfdestruct_runAsm_core hv hp

/-! ## The ABI return block: MSTORE-then-RETURN asm-core

The asm-side correctness of the ABI front-end's *return* block — the shape the
native `EvmYul.Venom.Abi.returnWord` lowers to. Where the native side
(`run_returnWord`) shows the Venom block halts with `returndata =
encodeUint256 (env v)`, and the codegen-acceptance witness
(`AbiCodegen.exFnRet_codegen_compiles`) shows this block *compiles* to concrete
EVM asm, this closes the loop at the asm level: the compiled program actually
recomputes the return value. The one worked block whose body both writes memory
and reads it back, exercising `asmMstore`/`asmReturnOp` + the spill roundtrip
(`asm_spill_roundtrip`) composed with the leading `JUMPDEST` and offset/size
pushes. -/

/-- **The ABI return block compiles to a correct EVM-asm program.** The resolved asm for
    the `returnWord` body — `LABEL body ; PUSH 0 ; MSTORE ; PUSH 32 ; PUSH 0 ; RETURN` —
    run from `s.pc = 0` with the return value `r` on top of the asm stack and 32 bytes of
    scratch memory, halts with `wordOfBytes as'.returndata = r`: it MSTOREs `r` at offset 0
    and RETURNs the 32-byte window, so the ABI-encoded return value is exactly `r`. The
    asm-level companion of the native `run_returnWord`, proved by composing the per-op
    `asmStep` lemmas (no `genBlockSimulation`, no `sorry`). The `hp*` hypotheses say the
    three pushed byte-strings decode to `0`/`32`/`0` (as `asmResolve` emits). -/
theorem retWord_runAsm_core {offsetToPc : AssocList Nat Nat} {s : AsmState} {r : bytes32}
    {stk : List bytes32} {b0 b32 b0' : List byte}
    (hstk : s.stack = r :: stk) (haspc : s.pc = 0) (hcov : 32 ≤ s.memory.size)
    (hp0  : wordOfBytes (List.toByteArray (List.replicate (32 - b0.length)  (0:byte) ++ b0))  = UInt256.ofNat 0)
    (hp32 : wordOfBytes (List.toByteArray (List.replicate (32 - b32.length) (0:byte) ++ b32)) = UInt256.ofNat 32)
    (hp0' : wordOfBytes (List.toByteArray (List.replicate (32 - b0'.length) (0:byte) ++ b0')) = UInt256.ofNat 0) :
    ∃ as' : AsmState, runAsm 6 offsetToPc
      [AsmInst.AsmLabel "body", AsmInst.AsmPush b0, AsmInst.AsmOp "MSTORE",
       AsmInst.AsmPush b32, AsmInst.AsmPush b0', AsmInst.AsmOp "RETURN"] s
      = AsmResult.AsmHalt as' ∧ wordOfBytes as'.returndata = r := by
  set prog := [AsmInst.AsmLabel "body", AsmInst.AsmPush b0, AsmInst.AsmOp "MSTORE",
       AsmInst.AsmPush b32, AsmInst.AsmPush b0', AsmInst.AsmOp "RETURN"] with hprog
  have hlen : prog.length = 6 := rfl
  have h0N  : (UInt256.ofNat 0).toNat = 0 := rfl
  have h32N : (UInt256.ofNat 32).toNat = 32 := rfl
  set mem' : ByteArray := (wordToBytes r).write 0 s.memory 0 32 with hmem'
  set s1 : AsmState := asmNext s with hs1
  set s2 : AsmState := { asmNext s1 with stack := UInt256.ofNat 0 :: s1.stack } with hs2
  set s3 : AsmState := { asmNext s2 with stack := stk, memory := mem' } with hs3
  set s4 : AsmState := { asmNext s3 with stack := UInt256.ofNat 32 :: s3.stack } with hs4
  set s5 : AsmState := { asmNext s4 with stack := UInt256.ofNat 0 :: s4.stack } with hs5
  -- pc values
  have p1 : s1.pc = 1 := by rw [hs1]; show s.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have p3 : s3.pc = 3 := by rw [hs3]; show s2.pc + 1 = 3; rw [p2]
  have p4 : s4.pc = 4 := by rw [hs4]; show s3.pc + 1 = 4; rw [p3]
  have p5 : s5.pc = 5 := by rw [hs5]; show s4.pc + 1 = 5; rw [p4]
  -- in-bounds
  have hb0 : s.pc  < prog.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < prog.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < prog.length := by rw [p2, hlen]; decide
  have hb3 : s3.pc < prog.length := by rw [p3, hlen]; decide
  have hb4 : s4.pc < prog.length := by rw [p4, hlen]; decide
  have hb5 : s5.pc < prog.length := by rw [p5, hlen]; decide
  -- fetched instructions
  have g0 : prog.get ⟨s.pc, hb0⟩ = AsmInst.AsmLabel "body" := by
    rw [show (⟨s.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : prog.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush b0 := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmOp "MSTORE" := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have g3 : prog.get ⟨s3.pc, hb3⟩ = AsmInst.AsmPush b32 := by
    rw [show (⟨s3.pc, hb3⟩ : Fin _) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext p3]; rfl
  have g4 : prog.get ⟨s4.pc, hb4⟩ = AsmInst.AsmPush b0' := by
    rw [show (⟨s4.pc, hb4⟩ : Fin _) = ⟨4, by rw [hlen]; decide⟩ from Fin.ext p4]; rfl
  have g5 : prog.get ⟨s5.pc, hb5⟩ = AsmInst.AsmOp "RETURN" := by
    rw [show (⟨s5.pc, hb5⟩ : Fin _) = ⟨5, by rw [hlen]; decide⟩ from Fin.ext p5]; rfl
  -- stack / memory bridges
  have hs1stk : s1.stack = r :: stk := by rw [hs1]; show s.stack = r :: stk; exact hstk
  have hs2mem : s2.memory = s.memory := by simp only [hs2, hs1, asmNext]
  have hs5mem : s5.memory = mem' := by
    rw [hs5]; show s4.memory = mem'; rw [hs4]; show s3.memory = mem'; rw [hs3]
  have hmemge : s.memory.size ≤ mem'.size := by
    rw [hmem', show (32:Nat) = (wordToBytes r).size from (length_wordToBytes r).symm]
    exact EvmYul.byteArray_write_size (wordToBytes r) s.memory 0
  have hmstore_stack : s2.stack = UInt256.ofNat 0 :: r :: stk := by
    rw [hs2]; show UInt256.ofNat 0 :: s1.stack = UInt256.ofNat 0 :: r :: stk; rw [hs1stk]
  have hmstore_cov : ((UInt256.ofNat 0).toNat + 32 + 31) / 32 * 32 ≤ s2.memory.size := by
    rw [hs2mem]; show (0 + 32 + 31) / 32 * 32 ≤ s.memory.size; omega
  have hs5stack : s5.stack = UInt256.ofNat 0 :: UInt256.ofNat 32 :: stk := by
    simp only [hs5, hs4, hs3]
  have hs5cov : ((UInt256.ofNat 0).toNat + (UInt256.ofNat 32).toNat + 31) / 32 * 32 ≤ s5.memory.size := by
    rw [hs5mem, h0N, h32N]; omega
  -- per-op steps
  have e0 : asmStep offsetToPc prog s = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1, hp0]; rfl
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK s3 := by
    rw [asmStep_mstore_ok hb2 g2, asmMstore_ok hmstore_stack hmstore_cov, h0N, hs3, hmem', hs2mem]
  have e3 : asmStep offsetToPc prog s3 = AsmResult.AsmOK s4 := by rw [asmStep_push_ok hb3 g3, hp32]; rfl
  have e4 : asmStep offsetToPc prog s4 = AsmResult.AsmOK s5 := by rw [asmStep_push_ok hb4 g4, hp0']; rfl
  set asRet : AsmState := { s5 with stack := stk, returndata := s5.memory.readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat, memory := s5.memory } with hasRet
  have e5 : asmStep offsetToPc prog s5 = AsmResult.AsmHalt asRet := by
    rw [asmStep_return_ok hb5 g5, hasRet]; exact asmReturnOp_ok hs5stack (Or.inr hs5cov)
  refine ⟨asRet, ?_, ?_⟩
  · rw [show (6:Nat) = 1+1+1+1+1+1 from rfl, runAsm_succ_ok hb0 e0, runAsm_succ_ok hb1 e1,
        runAsm_succ_ok hb2 e2, runAsm_succ_ok hb3 e3, runAsm_succ_ok hb4 e4]
    show runAsm 1 offsetToPc prog s5 = _
    unfold runAsm; rw [e5]
  · rw [hasRet]
    show wordOfBytes (s5.memory.readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) = r
    rw [hs5mem, h0N, h32N, hmem']
    exact asm_spill_roundtrip r s.memory 0 (Nat.zero_le _)

end EvmYul.Venom.Hol.Codegen.Example

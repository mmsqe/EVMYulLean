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

/-- **Asm core for a REVERT-terminated block** (`[JUMPDEST; PUSH off; PUSH sz; REVERT]`, `off=sz=0`).
    The `AsmRevert` companion of `stop_runAsm_core`: runs 4 steps from `as.pc = 0` to `AsmRevert` with
    empty returndata (`readWithPadding _ 0 = empty`). Composes `asmStep_label_ok` + two
    `asmStep_push_ok` + `runAsm_revert`. -/
theorem revert_runAsm_core
    {offsetToPc : AssocList Nat Nat}
    {as : AsmState} {b1 b2 : List byte}
    (haspc : as.pc = 0)
    (hsz : (wordOfBytes (List.toByteArray (List.replicate (32 - b1.length) (0 : byte) ++ b1))).toNat = 0) :
    ∃ as', runAsm 4 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmPush b1, AsmInst.AsmPush b2, AsmInst.AsmOp "REVERT"] as
             = AsmResult.AsmRevert as' := by
  set prog := [AsmInst.AsmLabel "entry", AsmInst.AsmPush b1, AsmInst.AsmPush b2, AsmInst.AsmOp "REVERT"]
    with hprogdef
  have hlen : prog.length = 4 := rfl
  set v1 := wordOfBytes (List.toByteArray (List.replicate (32 - b1.length) (0 : byte) ++ b1)) with hv1
  set v2 := wordOfBytes (List.toByteArray (List.replicate (32 - b2.length) (0 : byte) ++ b2)) with hv2
  set s1 : AsmState := asmNext as with hs1
  set s2 : AsmState := { asmNext s1 with stack := v1 :: s1.stack } with hs2
  set s3 : AsmState := { asmNext s2 with stack := v2 :: s2.stack } with hs3
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have p3 : s3.pc = 3 := by rw [hs3]; show s2.pc + 1 = 3; rw [p2]
  have hb0 : as.pc < prog.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < prog.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < prog.length := by rw [p2, hlen]; decide
  have hb3 : s3.pc < prog.length := by rw [p3, hlen]; decide
  have g0 : prog.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : prog.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush b1 := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have g2 : prog.get ⟨s2.pc, hb2⟩ = AsmInst.AsmPush b2 := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have g3 : prog.get ⟨s3.pc, hb3⟩ = AsmInst.AsmOp "REVERT" := by
    rw [show (⟨s3.pc, hb3⟩ : Fin _) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext p3]; rfl
  have e0 : asmStep offsetToPc prog as = AsmResult.AsmOK s1 := asmStep_label_ok hb0 g0
  have e1 : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2 := by rw [asmStep_push_ok hb1 g1]; rfl
  have e2 : asmStep offsetToPc prog s2 = AsmResult.AsmOK s3 := by rw [asmStep_push_ok hb2 g2]; rfl
  exact ⟨_, by
    rw [show (4 : Nat) = 1+1+1+1 from rfl, runAsm_succ_ok hb0 e0, runAsm_succ_ok hb1 e1,
        runAsm_succ_ok hb2 e2]
    exact runAsm_revert 0 hb3 g3 (by rw [hs3, hs2]) (Or.inl hsz)⟩


/-- **Asm-side INVALID block sim** (`AsmFault`). The `AsmFault` companion of
    `stop_runAsm_core` (AsmHalt) and `revert_runAsm_core` (AsmRevert), completing the
    trio of terminal asm results: `[JUMPDEST; INVALID]` runs 2 steps from `pc 0` to
    `AsmFault`. `INVALID` faults directly (`AsmFault (asmNext s)`), like `STOP` halts —
    so the run is `asmStep_label_ok` then the direct fault dispatch. Terminal relation
    is dropped (the Venom-side exceptional-halt reverts state, so the abort state's
    observable fields need the revert semantics — left as follow-up). -/
theorem invalid_runAsm_core
    {offsetToPc : AssocList Nat Nat} {as : AsmState}
    (haspc : as.pc = 0) :
    ∃ as', runAsm 2 offsetToPc [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"] as
             = AsmResult.AsmFault as' := by
  have hpc0 : as.pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"].length := by
    rw [haspc]; decide
  have hpc1 : (asmNext as).pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"].length := by
    show as.pc + 1 < _; rw [haspc]; decide
  have hget0 : [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"].get ⟨as.pc, hpc0⟩
      = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hpc0⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext haspc]; rfl
  have hget1 : [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"].get ⟨(asmNext as).pc, hpc1⟩
      = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨(asmNext as).pc, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from
          Fin.ext (by show as.pc + 1 = 1; rw [haspc])]; rfl
  have hstep1 : asmStep offsetToPc [AsmInst.AsmLabel "entry", AsmInst.AsmOp "INVALID"] (asmNext as)
      = AsmResult.AsmFault (asmNext (asmNext as)) := by
    unfold asmStep; rw [dif_pos hpc1, hget1]; rfl
  refine ⟨asmNext (asmNext as), ?_⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hpc0 (asmStep_label_ok hpc0 hget0)]
  show runAsm 1 offsetToPc _ (asmNext as) = AsmResult.AsmFault (asmNext (asmNext as))
  unfold runAsm; rw [hstep1]

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

/-! ## Var-reading store body: the first concrete `varentry` instance (SSTORE)

Every worked instance above (stop / addStop / jmp / jnz) either has an empty body or a *literal*-reading
body (`ADD 5 3`) — none exercises the `varentry` / `RegularStepG` var-reading layer, which had never been
instantiated concretely (all its wrappers were conditional). This is that de-vacuification: a block
`[SSTORE x y ; STOP]` whose body reads two *live vars* `x, y` off the stack. With `x, y` still live, the
generator keeps them (plan `[DUP1 ; DUP3 ; SSTORE]`), so the resolved program is
`[JUMPDEST ; DUP1 ; DUP3 ; SSTORE ; STOP]`. `runBlock` corresponds to `runAsm` from the var-stack asm
state, halting with the terminal relation — via `genBlockSimulation_regularGN_stop_varentry` fed the
constructed `RegularStepG` (SSTORE disjunct: dispatch to `execWrite2 sstore`, asm side `asmStep_sstore_ok`). -/

def sstoreInst : Instruction :=
  { id := 0, opcode := Opcode.SSTORE, operands := [Operand.Var "x", Operand.Var "y"], outputs := [] }
def sstoreProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3",
   AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"]
def sstoreBB : BasicBlock := { label := "entry", instructions := [sstoreInst, stopInst] }
def dummyFn : IrFunction := { name := "f", blocks := [] }

/-- The SSTORE var-reading body is a `RegularBodyG` with `S = [x, y]` (both live) — the SSTORE disjunct
    of `RegularStepG`, every conjunct discharged (dispatch to `execWrite2 sstore`; asm side
    `asmStep_sstore_ok`). -/
theorem sstore_regularBodyG {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyG lo ["x", "y"] offsetToPc sstoreProg [sstoreInst] ["x", "y"] := by
  refine ⟨?_, trivial⟩
  right; left
  refine ⟨"x", "y", ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · decide
  · rfl
  · intro v; rfl
  · rfl
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro s h hp; exact asmStep_sstore_ok h hp

/-- **First concrete `varentry` instance: a var-reading SSTORE body block sim.** For a block
    `[SSTORE x y ; STOP]` with `x, y` live vars on the stack (defined in `vs`), `runBlock` corresponds
    to `runAsm` on the resolved program `[JUMPDEST ; DUP1 ; DUP3 ; SSTORE ; STOP]` from the var-stack
    asm state, halting with the terminal relation. De-vacuifies
    `genBlockSimulation_regularGN_stop_varentry` (and the `RegularStepG` var-reading-body layer). -/
theorem genBlockSimulation_sstore_example
    {vs : VenomState} {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat} :
    (match runBlock 10 (default : VenomContext) sstoreBB vs with
     | ExecResult.OK vs' => ∃ as', runAsm sstoreProg.length offsetToPc sstoreProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets (initPlanState 0) vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm sstoreProg.length offsetToPc sstoreProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm sstoreProg.length offsetToPc sstoreProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm sstoreProg.length offsetToPc sstoreProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hxdef' : lookupVar "x" { vs with instIdx := 0 } = some vx := hxdef
  have hydef' : lookupVar "y" { vs with instIdx := 0 } = some vy := hydef
  set sEnd : VenomState := { sstore vx vy { vs with instIdx := 0 } with instIdx := 1 } with hsEnd
  have hthread : execBodyThread [sstoreInst] 0 { vs with instIdx := 0 } = some sEnd := by
    rw [hsEnd]; simp only [execBodyThread, sstoreInst, stepInstBase, execWrite2, evalOperand, hxdef', hydef']
  have hstepterm : stepInstBase stopInst sEnd = ExecResult.Halt (haltState sEnd) := by
    simp only [stepInstBase, stopInst]
  have hnonterm : ∀ inst ∈ [sstoreInst], isTerminator inst.opcode = false := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
  have hdef : ∀ z ∈ ["x","y"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · subst h; exact ⟨vx, hxdef⟩
    · subst h; exact ⟨vy, hydef⟩
  have hblock : asmBlockAt sstoreProg
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel "entry"] ++ (([sstoreInst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["x","y"] false true "entry" acc.2).1,
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["x","y"] false true "entry" acc.2).2))
          ([], { initPlanState 0 with stack := (["x","y"].map Operand.Var) })).1)) := by
    refine ⟨?_, fun j hj => ?_⟩
    · show (0:Nat) + 4 ≤ sstoreProg.length; decide
    · have hj' : j < 4 := hj
      interval_cases j <;> rfl
  have hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) }).pc + 4
        < sstoreProg.length := by show 0 + 4 < sstoreProg.length; decide
  have hget : sstoreProg.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["x","y"].map Operand.Var) }).pc + 4, hlt⟩
        = AsmInst.AsmOp "STOP" := by
    rw [show (⟨_, hlt⟩ : Fin sstoreProg.length) = ⟨4, by decide⟩ from Fin.ext (by rfl)]; rfl
  exact genBlockSimulation_regularGN_stop_varentry
    (labelOffsets := labelOffsets) (ps' := initPlanState 0) (offsetToPc := offsetToPc) (fnEom := 0)
    (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := dummyFn)
    (body := [sstoreInst]) (term := stopInst) (hd := sstoreInst) (tl := [stopInst])
    (l := "entry") (curBbLabel := "entry") (nextLiveness := ["x","y"]) (S := ["x","y"])
    (sEnd := sEnd) (bb := sstoreBB)
    (vs := vs) (bodyLen := 4) (prog := sstoreProg)
    sstore_regularBodyG rfl rfl (by decide) hnonterm (by decide)
    hdef (by decide) hthread hstepterm
    hblock rfl hlt hget


def addVarInst : Instruction :=
  { id := 0, opcode := Opcode.ADD, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["c"] }
def addVarProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3",
   AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"]
def addVarBB : BasicBlock := { label := "entry", instructions := [addVarInst, stopInst] }

/-- The ADD var-reading body is a `RegularBodyG` with `S = [a, b]` (both live), output `c` live — the
    commutative-binop sub-disjunct of `RegularStep` (first `RegularStepG` disjunct): dispatch to
    `execPure2 (·+·)`, asm side `asmStep_add_ok`. The 1-output var-binop analog of `sstore_regularBodyG`. -/
theorem addVar_regularBodyG {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyG lo ["a","b","c"] offsetToPc addVarProg [addVarInst] ["a","b"] := by
  refine ⟨?_, trivial⟩
  left
  refine ⟨"c", "ADD", ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · left
    refine ⟨"a", "b", (· + ·), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · intro v; rfl
    · rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · intro s h hp; exact asmStep_add_ok h hp

/-- **First concrete var-*binop* body block sim.** For a block `[c := ADD a b ; STOP]` with `a, b` live
    vars on the stack (defined in `vs`) and output `c` live, `runBlock` corresponds to `runAsm` on the
    resolved program `[JUMPDEST ; DUP1 ; DUP3 ; ADD ; STOP]` from the var-stack asm state, halting with
    the terminal relation. The 1-output binop analog of `genBlockSimulation_sstore_example` (SSTORE is
    0-output): exercises the commutative-binop var-reading path via
    `genBlockSimulation_regularGN_stop_varentry` fed `addVar_regularBodyG`. -/
theorem genBlockSimulation_addVar_example
    {vs : VenomState} {va vb : bytes32}
    (hadef : lookupVar "a" vs = some va) (hbdef : lookupVar "b" vs = some vb)
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat} :
    (match runBlock 10 (default : VenomContext) addVarBB vs with
     | ExecResult.OK vs' => ∃ as', runAsm addVarProg.length offsetToPc addVarProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets (initPlanState 0) vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm addVarProg.length offsetToPc addVarProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm addVarProg.length offsetToPc addVarProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm addVarProg.length offsetToPc addVarProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hadef' : lookupVar "a" { vs with instIdx := 0 } = some va := hadef
  have hbdef' : lookupVar "b" { vs with instIdx := 0 } = some vb := hbdef
  set sEnd : VenomState := { updateVar "c" (va + vb) { vs with instIdx := 0 } with instIdx := 1 } with hsEnd
  have hthread : execBodyThread [addVarInst] 0 { vs with instIdx := 0 } = some sEnd := by
    rw [hsEnd]; simp only [execBodyThread, addVarInst, stepInstBase, execPure2, evalOperand, hadef', hbdef']
  have hstepterm : stepInstBase stopInst sEnd = ExecResult.Halt (haltState sEnd) := by
    simp only [stepInstBase, stopInst]
  have hnonterm : ∀ inst ∈ [addVarInst], isTerminator inst.opcode = false := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
  have hdef : ∀ z ∈ ["a","b"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · subst h; exact ⟨va, hadef⟩
    · subst h; exact ⟨vb, hbdef⟩
  have hblock : asmBlockAt addVarProg
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel "entry"] ++ (([addVarInst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "entry" acc.2).1,
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "entry" acc.2).2))
          ([], { initPlanState 0 with stack := (["a","b"].map Operand.Var) })).1)) := by
    refine ⟨?_, fun j hj => ?_⟩
    · show (0:Nat) + 4 ≤ addVarProg.length; decide
    · have hj' : j < 4 := hj
      interval_cases j <;> rfl
  have hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) }).pc + 4
        < addVarProg.length := by show 0 + 4 < addVarProg.length; decide
  have hget : addVarProg.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b"].map Operand.Var) }).pc + 4, hlt⟩
        = AsmInst.AsmOp "STOP" := by
    rw [show (⟨_, hlt⟩ : Fin addVarProg.length) = ⟨4, by decide⟩ from Fin.ext (by rfl)]; rfl
  exact genBlockSimulation_regularGN_stop_varentry
    (labelOffsets := labelOffsets) (ps' := initPlanState 0) (offsetToPc := offsetToPc) (fnEom := 0)
    (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := dummyFn)
    (body := [addVarInst]) (term := stopInst) (hd := addVarInst) (tl := [stopInst])
    (l := "entry") (curBbLabel := "entry") (nextLiveness := ["a","b","c"]) (S := ["a","b"])
    (sEnd := sEnd) (bb := addVarBB)
    (vs := vs) (bodyLen := 4) (prog := addVarProg)
    addVar_regularBodyG rfl rfl (by decide) hnonterm (by decide)
    hdef (by decide) hthread hstepterm
    hblock rfl hlt hget


/-! ## Var-reading memory-copy body: the first concrete H-fold `varentry` instance (CALLDATACOPY)

Every `varentry` instance above (`SSTORE`, `ADD`) is a G-fold op — no memory precondition. This is the
H-fold counterpart: a block `[CALLDATACOPY a b c ; STOP]` reading three *live vars* `a, b, c` (dest
offset / calldata offset / size) off the stack. With all three live, the generator keeps them (plan
`[DUP1 ; DUP3 ; DUP5 ; CALLDATACOPY]`), so the resolved program is
`[JUMPDEST ; DUP1 ; DUP3 ; DUP5 ; CALLDATACOPY ; STOP]`. Unlike the G-fold cases, `CALLDATACOPY` touches
memory, so its `RegularStepH` disjunct carries a *memory-safety* conjunct (offset/size within the memory
and allocation bounds) that is genuinely a runtime precondition — not statically true for arbitrary live
values. It is therefore surfaced here as the one honest hypothesis `hmemsafe`; everything else (the
CALLDATACOPY semantics, the demand-threaded fold, the asm correspondence) is discharged. Via
`genBlockSimulation_regularHN_stop_varentry` fed the constructed `RegularStepH` — the H-fold twin of the
SSTORE instance, de-vacuifying the memory-copy var-reading path end-to-end. -/

def cdcInst : Instruction :=
  { id := 0, opcode := Opcode.CALLDATACOPY, operands := [Operand.Var "a", Operand.Var "b", Operand.Var "c"], outputs := [] }
def cdcProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp "DUP5",
   AsmInst.AsmOp "CALLDATACOPY", AsmInst.AsmOp "STOP"]
def cdcBB : BasicBlock := { label := "entry", instructions := [cdcInst, stopInst] }

/-- The CALLDATACOPY var-reading body is a `RegularBodyH` at demand `1` with `S = [a, b, c]` (all live) —
    the CALLDATACOPY disjunct of `RegularStepH`. The semantics conjunct is discharged by unfolding
    `stepInstBase`; the memory-safety conjunct is threaded through as `hmemsafe` (a genuine runtime
    precondition for a memory-touching op — the H-fold analog of the G-fold `sstore_regularBodyG`, which
    had none). -/
theorem cdc_regularBodyH {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel lo p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    RegularBodyH lo ["a","b","c"] offsetToPc cdcProg 1 [cdcInst] ["a","b","c"] := by
  refine ⟨?_, trivial⟩
  right; left
  refine ⟨"a", "b", "c", rfl, by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, hmemsafe, by decide⟩
  intro v wa wb wc ha hb hc
  simp only [stepInstBase, cdcInst, evalOperand, ha, hb, hc]

/-- **First concrete H-fold `varentry` instance: a var-reading CALLDATACOPY body block sim.** For a block
    `[CALLDATACOPY a b c ; STOP]` with `a, b, c` live vars on the stack (defined in `vs`) and the
    memory-safety precondition `hmemsafe`, `runBlock` corresponds to `runAsm` on the resolved program
    `[JUMPDEST ; DUP1 ; DUP3 ; DUP5 ; CALLDATACOPY ; STOP]` from the var-stack asm state, halting with the
    terminal relation. De-vacuifies `genBlockSimulation_regularHN_stop_varentry` (and the H-fold
    demand-threaded memory-copy var-reading path). The H-fold analog of
    `genBlockSimulation_sstore_example`. -/
theorem genBlockSimulation_calldatacopy_example
    {vs : VenomState} {va vb vc : bytes32}
    (hadef : lookupVar "a" vs = some va) (hbdef : lookupVar "b" vs = some vb)
    (hcdef : lookupVar "c" vs = some vc)
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel labelOffsets p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    (match runBlock 10 (default : VenomContext) cdcBB vs with
     | ExecResult.OK vs' => ∃ as', runAsm cdcProg.length offsetToPc cdcProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) })
            = AsmResult.AsmOK as' ∧ venomAsmRel labelOffsets (initPlanState 0) vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm cdcProg.length offsetToPc cdcProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) })
            = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm cdcProg.length offsetToPc cdcProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) })
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm cdcProg.length offsetToPc cdcProg
            ({ asmOfVenom { vs with instIdx := 0 } with
                stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) })
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  have hadef' : lookupVar "a" { vs with instIdx := 0 } = some va := hadef
  have hbdef' : lookupVar "b" { vs with instIdx := 0 } = some vb := hbdef
  have hcdef' : lookupVar "c" { vs with instIdx := 0 } = some vc := hcdef
  set sEnd : VenomState :=
    { writeMemoryWithExpansion va.toNat
        ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding vb.toNat vc.toNat)
        { vs with instIdx := 0 } with instIdx := 1 } with hsEnd
  have hthread : execBodyThread [cdcInst] 0 { vs with instIdx := 0 } = some sEnd := by
    rw [hsEnd]; simp only [execBodyThread, cdcInst, stepInstBase, evalOperand, hadef', hbdef', hcdef']
  have hstepterm : stepInstBase stopInst sEnd = ExecResult.Halt (haltState sEnd) := by
    simp only [stepInstBase, stopInst]
  have hnonterm : ∀ inst ∈ [cdcInst], isTerminator inst.opcode = false := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
  have hdef : ∀ z ∈ ["a","b","c"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · subst h; exact ⟨va, hadef⟩
    · subst h; exact ⟨vb, hbdef⟩
    · subst h; exact ⟨vc, hcdef⟩
  have hblock : asmBlockAt cdcProg
      ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) }).pc
      (executePlan ([StackOp.SOLabel "entry"] ++ (([cdcInst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "entry" acc.2).1,
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "entry" acc.2).2))
          ([], { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) })).1)) := by
    refine ⟨?_, fun j hj => ?_⟩
    · show (0:Nat) + 5 ≤ cdcProg.length; decide
    · have hj' : j < 5 := hj
      interval_cases j <;> rfl
  have hlt : ({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) }).pc + 5
        < cdcProg.length := by show 0 + 5 < cdcProg.length; decide
  have hget : cdcProg.get ⟨({ asmOfVenom { vs with instIdx := 0 } with
          stack := asmStackOf { vs with instIdx := 0 } labelOffsets (["a","b","c"].map Operand.Var) }).pc + 5, hlt⟩
        = AsmInst.AsmOp "STOP" := by
    rw [show (⟨_, hlt⟩ : Fin cdcProg.length) = ⟨5, by decide⟩ from Fin.ext (by rfl)]; rfl
  exact genBlockSimulation_regularHN_stop_varentry
    (labelOffsets := labelOffsets) (ps' := initPlanState 0) (offsetToPc := offsetToPc) (fnEom := 0)
    (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := dummyFn)
    (body := [cdcInst]) (term := stopInst) (hd := cdcInst) (tl := [stopInst])
    (l := "entry") (curBbLabel := "entry") (nextLiveness := ["a","b","c"]) (S := ["a","b","c"])
    (dem := 1) (sEnd := sEnd) (bb := cdcBB)
    (vs := vs) (bodyLen := 5) (prog := cdcProg)
    (cdc_regularBodyH hmemsafe) rfl rfl (by decide) hnonterm (by decide)
    hdef (by decide) hthread hstepterm
    hblock rfl hlt hget


/-! ## Non-entry var-reading function sim (de-vacuification)

The final piece: a whole 2-block function `main: entry: JMP next ; next: SSTORE x y ; STOP` where the
successor block reads *live vars* off the stack (the config a JMP predecessor leaves). Composes
`hentryAsm_bare_jmp` (entry JMP -> next's pc, relation preserved) with `hasm_regularStop` (the
residual-budget var-reading SSTORE block from the mid-state) via `hfsim_jmp_then_halt`. This
de-vacuifies the non-entry var-reading path end-to-end (Venom `runBlocks` + entry JMP + var-reading
block + terminal relation), the second route around the var-reading tension. -/

def sstoreNextBB : BasicBlock := { label := "next", instructions := [sstoreInst, stopInst] }
def jmpSstoreFn : IrFunction := { name := "main", blocks := [jmpEntryBB, sstoreNextBB] }
def jmpSstoreProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 5)),
   AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3",
   AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"]

/-- RegularBodyG for the SSTORE body over jmpSstoreProg. -/
theorem sstore_regularBodyG' {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyG lo ["x", "y"] offsetToPc jmpSstoreProg [sstoreInst] ["x", "y"] := by
  refine ⟨?_, trivial⟩
  right; left
  refine ⟨"x", "y", rfl, by decide, by decide, rfl, fun v => rfl, rfl, rfl, by decide, by decide,
    by decide, by decide, by decide, fun s h hp => asmStep_sstore_ok h hp⟩

/-- **Non-entry var-reading function sim (de-vacuification).** For `main: entry: JMP next ;
    next: SSTORE x y ; STOP`, with `x, y` live vars on the stack (the config a JMP predecessor leaves),
    `runBlocks` corresponds to `runAsm` on the resolved program, halting with the terminal relation.
    Composes `hentryAsm_bare_jmp` (entry JMP → next's pc, relation preserved) + `hasm_regularStop` (the
    residual-budget var-reading SSTORE block from the mid-state) via `hfsim_jmp_then_halt`. -/
theorem hfsim_jmp_sstore_example
    {fuel : Nat} {ctx : VenomContext} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {vx vy : bytes32}
    (hcurbb : vs.currentBb = "entry") (hvshalt : vs.halted = false)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := (["x","y"].map Operand.Var) } vs as)
    (haspc : as.pc = 0) :
    match runBlocks fuel ctx jmpSstoreFn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm jmpSstoreProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpSstoreProg as
                 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm jmpSstoreProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpSstoreProg as
                 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm jmpSstoreProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpSstoreProg as
                 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hlen : jmpSstoreProg.length = 8 := rfl
  -- entry JMP asm run  ->  asMid at next's pc (3), relation preserved
  have hbLabel : asmBlockAt jmpSstoreProg as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
  have hpc1 : as.pc + 1 < jmpSstoreProg.length := by rw [haspc, hlen]; decide
  have hpush : jmpSstoreProg.get ⟨as.pc + 1, hpc1⟩
      = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
    have e : as.pc + 1 = 1 := by omega
    simp only [e]; rfl
  have hpc2 : as.pc + 2 < jmpSstoreProg.length := by rw [haspc, hlen]; decide
  have hjump : jmpSstoreProg.get ⟨as.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
    have e : as.pc + 2 = 2 := by omega
    simp only [e]; rfl
  obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
    hentryAsm_bare_jmp (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
      (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (off := 5) (idx := 3)
      hrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
  -- SSTORE block asm run from asMid (pc 3) via hasm_regularStop
  have hdef : ∀ z ∈ ["x","y"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · subst h; exact ⟨vx, hxdef⟩
    · subst h; exact ⟨vy, hydef⟩
  have hblockN : asmBlockAt jmpSstoreProg asMid.pc
      (executePlan ([StackOp.SOLabel "next"] ++ (([sstoreInst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["x","y"] false true "next" acc.2).1,
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["x","y"] false true "next" acc.2).2))
          ([], { initPlanState 0 with stack := (["x","y"].map Operand.Var) })).1)) := by
    rw [hpcMid]
    refine ⟨by decide, fun j hj => ?_⟩
    have hj' : j < 4 := hj
    interval_cases j <;> rfl
  have hltN : asMid.pc + 4 < jmpSstoreProg.length := by rw [hpcMid, hlen]; decide
  have hgetN : jmpSstoreProg.get ⟨asMid.pc + 4, hltN⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨asMid.pc + 4, hltN⟩ : Fin _) = ⟨7, by rw [hlen]; decide⟩ from
      Fin.ext (show asMid.pc + 4 = 7 from by rw [hpcMid])]; rfl
  have hthreadN : execBodyThread [sstoreInst] 0 { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 }
      = some { sstore vx vy { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } with instIdx := 1 } := by
    have hxd : lookupVar "x" { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } = some vx := hxdef
    have hyd : lookupVar "y" { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } = some vy := hydef
    simp only [execBodyThread, sstoreInst, stepInstBase, execWrite2, evalOperand, hxd, hyd]
  have hasmN := hasm_regularStop
    (labelOffsets := lo) (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := dummyFn)
    (body := [sstoreInst]) (l := "next") (curBbLabel := "next") (nextLiveness := ["x","y"]) (S0 := ["x","y"])
    (ps0 := { initPlanState 0 with stack := (["x","y"].map Operand.Var) })
    (vs := jumpTo "next" { vs with instIdx := 0 }) (asm := asMid)
    (sEnd := { sstore vx vy { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } with instIdx := 1 })
    (bodyLen := 4) (budget := jmpSstoreProg.length - 3)
    sstore_regularBodyG'
    (stackDiscH_varStack (by decide) hdef) stackIsVars_varStack hrelMid hthreadN
    hblockN rfl hltN hgetN (by decide)
  -- assemble
  have hstep_jmp : stepInstBase jmpInst { vs with instIdx := 0 }
      = ExecResult.OK (jumpTo "next" { vs with instIdx := 0 }) := rfl
  refine hfsim_jmp_then_halt
    (entryBb := jmpEntryBB) (termBb := sstoreNextBB) (n := 3)
    (efront := []) (eterm := jmpInst) (ehd := jmpInst) (etl := [])
    (esEnd := { vs with instIdx := 0 }) (sMid := jumpTo "next" { vs with instIdx := 0 })
    (tfront := [sstoreInst]) (tterm := stopInst) (thd := sstoreInst) (ttl := [stopInst])
    (tsEnd := { sstore vx vy { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } with instIdx := 1 })
    (tsEnd' := haltState { sstore vx vy { (jumpTo "next" { vs with instIdx := 0 }) with instIdx := 0 } with instIdx := 1 })
    ?_ rfl rfl (by decide) (by simp) rfl hstep_jmp (by decide) (by simp [jumpTo, hvshalt]) hrunE
    (by rw [hlen]; decide) ?_ rfl rfl (by decide) (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    hthreadN (by simp only [stepInstBase, stopInst]) hasmN
  · show lookupBlock vs.currentBb jmpSstoreFn.blocks = some jmpEntryBB
    rw [hcurbb]; rfl
  · show lookupBlock (jumpTo "next" { vs with instIdx := 0 }).currentBb jmpSstoreFn.blocks = some sstoreNextBB
    rfl

/-! ## Non-entry var-reading memory-copy function sim (H-fold multi-block capstone)

The H-fold counterpart of `hfsim_jmp_sstore_example`: a whole 2-block function
`main: entry: JMP next ; next: CALLDATACOPY a b c ; STOP` where the successor block reads three *live
vars* off the stack (the config a JMP predecessor leaves) and copies calldata into memory. Composes
`hentryAsm_bare_jmp` (entry JMP → next's pc, relation preserved) with `hasm_regularHN_stop` (the
residual-budget demand-threaded CALLDATACOPY block from the mid-state) via `hfsim_jmp_then_halt`. This
de-vacuifies the non-entry *memory-copy* var-reading path end-to-end (Venom `runBlocks` + entry JMP +
demand-threaded copy block + terminal relation) — the multi-block analog of
`genBlockSimulation_calldatacopy_example`, carrying the same one honest hypothesis `hmemsafe` (the
runtime memory-safety precondition inherent to a memory-touching op). -/

def cdcNextBB : BasicBlock := { label := "next", instructions := [cdcInst, stopInst] }
def jmpCdcFn : IrFunction := { name := "main", blocks := [jmpEntryBB, cdcNextBB] }
def jmpCdcProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmPush (padBytes symbolSize (encodeNumBytes 5)),
   AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3",
   AsmInst.AsmOp "DUP5", AsmInst.AsmOp "CALLDATACOPY", AsmInst.AsmOp "STOP"]

/-- `RegularBodyH` for the CALLDATACOPY body over `jmpCdcProg` (memory-safety threaded as `hmemsafe`) —
    the `jmpCdcProg` re-instance of `cdc_regularBodyH`. -/
theorem cdc_regularBodyH' {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel lo p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    RegularBodyH lo ["a","b","c"] offsetToPc jmpCdcProg 1 [cdcInst] ["a","b","c"] := by
  refine ⟨?_, trivial⟩
  right; left
  refine ⟨"a", "b", "c", rfl, by decide, by decide, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, hmemsafe, by decide⟩
  intro v wa wb wc ha hb hc
  simp only [stepInstBase, cdcInst, evalOperand, ha, hb, hc]


/-- **Entry segment of a linear chain, fold-named.** The `eops1`/`eps1`-phrased packaging of
    `hasm_regularHN_jmp`: the entry block's H-fold body + resolved `push-label ; JUMP` runs to the
    successor's pc with the relation threaded at the *named* fold output `eps1` — the shared prelude
    of the generic chain-tail theorems. -/
theorem hasm_regularHN_jmp_named
    {vs esEnd : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {efront : List Instruction} {el curBbLabel1 target : String} {enl eS0 : List String}
    {eps0 eps1 : PlanState} {eops1 : List StackOp} {ebodyLen edem off idx : Nat}
    (hfold1 : (efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
        ([], eps0) = (eops1, eps1))
    (hebody : RegularBodyH labelOffsets enl offsetToPc prog edem efront eS0)
    (hesd0 : StackDiscH ((efront.zipIdx 0).map (fun _ => edem)).sum eps0 { vs with instIdx := 0 })
    (hesv0 : StackIsVars eS0 eps0)
    (herel0 : venomAsmRel labelOffsets eps0 { vs with instIdx := 0 } as)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm (ebodyLen + 2) offsetToPc prog as = AsmResult.AsmOK asMid ∧
             venomAsmRel labelOffsets eps1 esEnd asMid ∧ asMid.pc = idx := by
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ ((efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
          ([], eps0)).1)) := by rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ ((efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
          ([], eps0)).1)).length := by rw [hfold1]; exact hebodyLenEq
  obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
    hasm_regularHN_jmp (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (l := el) (curBbLabel := curBbLabel1) (target := target)
      hebody hesd0 hesv0 herel0 hethread heblockF hebodyLenEqF hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  refine ⟨asMid, hrunE, ?_, hpcMid⟩
  rw [hfold1] at hrelMid; exact hrelMid

/-- **Generic two-block linear-chain `hfsim`** (gap A): an entry block with any H-fold regular body
    ending in JMP, then a halting block with any H-fold regular body ending in STOP — the
    whole-function correspondence discharged generically, not per concrete function. Composes
    `hasm_regularHN_jmp` (entry run to the successor's pc, relation threaded) with
    `hasm_regularHN_stop` (residual-budget halting run) through `hfsim_jmp_then_halt` (Venom side
    already discharged). Linear chain = identity reconciliation: the successor block runs at the
    entry fold's output plan state `eps1` (`hfold1`), no reorder; `hrelTransport` moves the
    relation across the JMP's `currentBb`/`instIdx` bookkeeping (definitional when
    `sMid = jumpTo target esEnd`). -/
theorem hfsim_regularHN_jmp_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab curBbLabel1 curBbLabel2 target : String} {enl tnl eS0 tS0 : List String}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {ebodyLen tbodyLen edem tdem off idx : Nat}
    -- the two blocks' generated plans (folds named once)
    (hfold1 : (efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
        ([], eps0) = (eops1, eps1))
    (hfold2 : (tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
        ([], eps1) = (tops2, tps2))
    -- entry block: Venom structure (body threads to esEnd, JMP steps to sMid)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: asm side (H-fold readiness + resolved push-label/JUMP layout)
    (hebody : RegularBodyH labelOffsets enl offsetToPc prog edem efront eS0)
    (hesd0 : StackDiscH ((efront.zipIdx 0).map (fun _ => edem)).sum eps0 { vs with instIdx := 0 })
    (hesv0 : StackIsVars eS0 eps0)
    (herel0 : venomAsmRel labelOffsets eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure (body threads to tsEnd, STOP halts)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt (haltState tsEnd))
    -- halting block: asm side, at the THREADED plan state eps1 (linear-chain identity
    -- reconciliation) and the successor pc idx
    (htbody : RegularBodyH labelOffsets tnl offsetToPc prog tdem tfront tS0)
    (htsd0 : StackDiscH ((tfront.zipIdx 0).map (fun _ => tdem)).sum eps1 { sMid with instIdx := 0 })
    (htsv0 : StackIsVars tS0 eps1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel labelOffsets eps1 esEnd asm' →
        venomAsmRel labelOffsets eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idx + tbodyLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 2 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- entry-fold forms of the eops1-phrased hypotheses
  obtain ⟨asMid, hrunE, hrelMid1, hpcMid⟩ :=
    hasm_regularHN_jmp_named hfold1 hebody hesd0 hesv0 herel0 hethread heblock hebodyLenEq hpc1
      hpush hoff_lk hoff hpc2 hjump hidx_lk
  -- thread the relation to the successor's plan state eps1 and Venom state sMid
  -- stop block's asm facts at asMid (pc = idx)
  have htblock' : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)).length := by rw [hfold2]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen, htlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHN_stop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (l := tlab) (curBbLabel := curBbLabel2) (vs := sMid) (asm := asMid) (sEnd := tsEnd)
    (budget := prog.length - (ebodyLen + 2))
    htbody htsd0 htsv0 (hrelTransport asMid hrelMid1) htthread htblock' htbodyLenEqF htlt' htget'
    (by omega)
  exact hfsim_jmp_then_halt hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN


/-- **Generic two-block linear-chain `hfsim`, faulting tail** (gap A): as
    `hfsim_regularHN_jmp_stop` but the terminal block carries a G-fold regular body ending in
    INVALID (Venom fault clears returndata, hence `hrdEmpty`). Composes `hasm_regularHN_jmp` with
    `hasm_regularInvalid` through `hfsim_jmp_then_fault`. -/
theorem hfsim_regularHN_jmp_invalid
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab curBbLabel1 curBbLabel2 target : String} {enl tnl eS0 tS0 : List String}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {ebodyLen tbodyLen edem off idx : Nat}
    -- the two blocks' generated plans (folds named once)
    (hfold1 : (efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
        ([], eps0) = (eops1, eps1))
    (hfold2 : (tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
        ([], eps1) = (tops2, tps2))
    -- entry block: Venom structure (body threads to esEnd, JMP steps to sMid)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: asm side (H-fold readiness + resolved push-label/JUMP layout)
    (hebody : RegularBodyH labelOffsets enl offsetToPc prog edem efront eS0)
    (hesd0 : StackDiscH ((efront.zipIdx 0).map (fun _ => edem)).sum eps0 { vs with instIdx := 0 })
    (hesv0 : StackIsVars eS0 eps0)
    (herel0 : venomAsmRel labelOffsets eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure (body threads to tsEnd, STOP halts)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty tsEnd)))
    (hrdEmpty : tsEnd.returndata = ByteArray.empty)
    -- halting block: asm side, at the THREADED plan state eps1 (linear-chain identity
    -- reconciliation) and the successor pc idx
    (htbody : RegularBodyG labelOffsets tnl offsetToPc prog tfront tS0)
    (htsd0 : StackDiscH ((tfront.zipIdx 0).flatMap outsOf).length eps1 { sMid with instIdx := 0 })
    (htsv0 : StackIsVars tS0 eps1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel labelOffsets eps1 esEnd asm' →
        venomAsmRel labelOffsets eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idx + tbodyLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen, htlt⟩ = AsmInst.AsmOp "INVALID")
    (hbudget : ebodyLen + 2 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- entry-fold forms of the eops1-phrased hypotheses
  obtain ⟨asMid, hrunE, hrelMid1, hpcMid⟩ :=
    hasm_regularHN_jmp_named hfold1 hebody hesd0 hesv0 herel0 hethread heblock hebodyLenEq hpc1
      hpush hoff_lk hoff hpc2 hjump hidx_lk
  -- thread the relation to the successor's plan state eps1 and Venom state sMid
  -- stop block's asm facts at asMid (pc = idx)
  have htblock' : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)).length := by rw [hfold2]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen, htlt'⟩ = AsmInst.AsmOp "INVALID" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularInvalid (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (l := tlab) (curBbLabel := curBbLabel2) (vs := sMid) (asm := asMid) (sEnd := tsEnd)
    (budget := prog.length - (ebodyLen + 2))
    htbody htsd0 htsv0 (hrelTransport asMid hrelMid1) htthread hrdEmpty htblock' htbodyLenEqF htlt'
    htget' (by omega)
  exact hfsim_jmp_then_fault hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN


/-- **Generic two-block linear-chain `hfsim`, reverting tail** (gap A): as
    `hfsim_regularHN_jmp_stop` but the terminal block's H-fold regular body ends in a literal
    REVERT (`PUSH sz ; PUSH off ; REVERT`, `sz = 0` — the canonical compiled revert-block shape).
    Composes `hasm_regularHN_jmp` with `hasm_regularHN_revert_lit` through
    `hfsim_jmp_then_revert`. -/
theorem hfsim_regularHN_jmp_revert
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab curBbLabel1 curBbLabel2 target : String} {enl tnl eS0 tS0 : List String}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {ebodyLen tbodyLen edem tdem off idx : Nat} {b1 b2 : List byte} {roff rsz : bytes32}
    -- the two blocks' generated plans (folds named once)
    (hfold1 : (efront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 enl false true curBbLabel1 p) z acc.2).2))
        ([], eps0) = (eops1, eps1))
    (hfold2 : (tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
        ([], eps1) = (tops2, tps2))
    -- entry block: Venom structure (body threads to esEnd, JMP steps to sMid)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: asm side (H-fold readiness + resolved push-label/JUMP layout)
    (hebody : RegularBodyH labelOffsets enl offsetToPc prog edem efront eS0)
    (hesd0 : StackDiscH ((efront.zipIdx 0).map (fun _ => edem)).sum eps0 { vs with instIdx := 0 })
    (hesv0 : StackIsVars eS0 eps0)
    (herel0 : venomAsmRel labelOffsets eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst labelOffsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat labelOffsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure (body threads to tsEnd, STOP halts)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Abort AbortType.RevertAbort
      (revertState (setReturndata (readMemory roff.toNat rsz.toNat tsEnd) tsEnd)))
    -- halting block: asm side, at the THREADED plan state eps1 (linear-chain identity
    -- reconciliation) and the successor pc idx
    (htbody : RegularBodyH labelOffsets tnl offsetToPc prog tdem tfront tS0)
    (htsd0 : StackDiscH ((tfront.zipIdx 0).map (fun _ => tdem)).sum eps1 { sMid with instIdx := 0 })
    (htsv0 : StackIsVars tS0 eps1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel labelOffsets eps1 esEnd asm' →
        venomAsmRel labelOffsets eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htsafe : roff.toNat + rsz.toNat ≤ tps2.alloc.fnEom)
    (htlt1 : idx + tbodyLen < prog.length)
    (htget1 : prog.get ⟨idx + tbodyLen, htlt1⟩ = AsmInst.AsmPush b1)
    (htlt2 : idx + tbodyLen + 1 < prog.length)
    (htget2 : prog.get ⟨idx + tbodyLen + 1, htlt2⟩ = AsmInst.AsmPush b2)
    (htlt3 : idx + tbodyLen + 2 < prog.length)
    (htget3 : prog.get ⟨idx + tbodyLen + 2, htlt3⟩ = AsmInst.AsmOp "REVERT")
    (hv1 : wordOfBytes (List.toByteArray (List.replicate (32 - b1.length) (0 : byte) ++ b1)) = rsz)
    (hv2 : wordOfBytes (List.toByteArray (List.replicate (32 - b2.length) (0 : byte) ++ b2)) = roff)
    (hsz0 : rsz.toNat = 0)
    (hbudget : ebodyLen + 2 + (tbodyLen + 3) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- entry-fold forms of the eops1-phrased hypotheses
  obtain ⟨asMid, hrunE, hrelMid1, hpcMid⟩ :=
    hasm_regularHN_jmp_named hfold1 hebody hesd0 hesv0 herel0 hethread heblock hebodyLenEq hpc1
      hpush hoff_lk hoff hpc2 hjump hidx_lk
  -- thread the relation to the successor's plan state eps1 and Venom state sMid
  -- stop block's asm facts at asMid (pc = idx)
  have htblock' : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).1)).length := by rw [hfold2]; exact htbodyLenEq
  have htsafeF : roff.toNat + rsz.toNat ≤ ((tfront.zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 tnl false true curBbLabel2 p) z acc.2).2))
          ([], eps1)).2.alloc.fnEom := by rw [hfold2]; exact htsafe
  have htlt1' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt1
  have htget1' : prog.get ⟨asMid.pc + tbodyLen, htlt1'⟩ = AsmInst.AsmPush b1 :=
    prog_get_transfer (by rw [hpcMid]) htget1
  have htlt2' : asMid.pc + tbodyLen + 1 < prog.length := by rw [hpcMid]; exact htlt2
  have htget2' : prog.get ⟨asMid.pc + tbodyLen + 1, htlt2'⟩ = AsmInst.AsmPush b2 :=
    prog_get_transfer (by rw [hpcMid]) htget2
  have htlt3' : asMid.pc + tbodyLen + 2 < prog.length := by rw [hpcMid]; exact htlt3
  have htget3' : prog.get ⟨asMid.pc + tbodyLen + 2, htlt3'⟩ = AsmInst.AsmOp "REVERT" :=
    prog_get_transfer (by rw [hpcMid]) htget3
  have hasmN := hasm_regularHN_revert_lit (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (l := tlab) (curBbLabel := curBbLabel2) (vs := sMid) (asm := asMid) (sEnd := tsEnd)
    (budget := prog.length - (ebodyLen + 2))
    htbody htsd0 htsv0 (hrelTransport asMid hrelMid1) htthread htblock' htbodyLenEqF htsafeF
    htlt1' htget1' htlt2' htget2' htlt3' htget3' hv1 hv2 hsz0 (by omega)
  exact hfsim_jmp_then_revert hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN

/-- **Generic two-block linear-chain `hfsim`, spill-aware** (gap A × gap C): both blocks carry
    padded varying-growth (HSVP) bodies — so they may SPILL and RESTORE — and the whole-function
    `runBlocks`/`runAsm` correspondence is discharged generically. The fuel THREADS: the entry runs
    at padding `totalGain lg2 + P2`, and its exit invariant is exactly the successor's entry
    requirement; the plan state, stack shape, and exact spilled map thread likewise (linear chain =
    identity reconciliation). `hrelTransport`/`hsdTransport` move the relation and invariant across
    the JMP's `currentBb`/`instIdx` bookkeeping (definitional when `sMid = jumpTo target esEnd`). -/
theorem hfsim_regularHSVP_jmp_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gp2 : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab target : String} {eS0 : List String}
    {eM0 eM1 : AssocList Operand Nat}
    {lg1 lg2 : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {P2 ebodyLen tbodyLen off idx : Nat}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfold2 : lg2.foldl (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)
      = (tops2, tps2))
    -- entry block: Venom structure
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: spill-aware asm segment (fuel = successor requirement, threaded)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lg2 + P2) lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lg2 + P2)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt (haltState tsEnd))
    -- halting block: spill-aware asm segment at the THREADED state (fold output eps1,
    -- grown shape, exit map eM1)
    (hfront2 : lg2.map Prod.fst = tfront.zipIdx 0)
    (hready2 : BodyStepsReadyHSVP P2 lo offsetToPc prog gp2 lg2
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lg2 + P2) eps1 esEnd asm' →
        StackDiscHS (totalGain lg2 + P2) eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idx + tbodyLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 2 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  obtain ⟨asMid, hrunE, hrelMid, hpcMid, hsdMid, hsvMid⟩ :=
    hasm_regularHSVP_jmp (totalGain lg2 + P2) hfront1 hready1 hesd0 hesv0 hespM herel0 hethread
      heblockF hebodyLenEqF hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  rw [hfold1] at hrelMid hsdMid hsvMid
  have htblockF : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfold2]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen, htlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHSVP_stop P2 (budget := prog.length - (ebodyLen + 2))
    hfront2 hready2 (hsdTransport asMid hsdMid) hsvMid hspM1 (hrelTransport asMid hrelMid)
    htthread htblockF htbodyLenEqF htlt' htget' (by omega)
  exact hfsim_jmp_then_halt hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN


/-- **Two-block whole-function correspondence with an external CALL in the halting block** —
    the integration capstone: entry (HSVP body + `JMP`) → terminal block whose body is
    `tfront ++ [callInst]` ending in `STOP`. The Venom side threads through the driver-dispatched
    call (`hfsim_jmp_then_halt_extcall`); the asm side runs the entry segment then the
    CALL+STOP segment (`hasm_regularHSVP_call_stop`). Consumes every layer of the external-call
    program: producer sim, walk packaging, and the segment assembly. -/
theorem hfsim_regularHSVP_jmp_call_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fnG : IrFunction}
    {instC : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {gp1 gpT : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction}
    {tsEndT : VenomState}
    {el tlab target : String} {eS0 : List String}
    {eM0 eM1 MT : AssocList Operand Nat}
    {lg1 lgT : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tpsT : PlanState} {eops1 topsT : List StackOp}
    {ebodyLen tbodyLen tcallLen off idx : Nat}
    {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, tpsT))
    -- entry block: Venom structure
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: spill-aware asm segment (fuel = terminal requirement, threaded)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lgT + 7) lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lgT + 7)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- terminal block: Venom structure (body = tfront ++ [callInst], STOP terminator)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = (tfront ++ [instC] ++ []) ++ [tterm])
    (htcons : (tfront ++ [instC] ++ []) ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEndT)
    (htterm_step : stepInstBase tterm
        { (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) with
          instIdx := tfront.length + 1 }
      = ExecResult.Halt (haltState
        { (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) with
          instIdx := tfront.length + 1 }))
    -- terminal block: the CALL+STOP asm segment at the threaded state
    (hfrontT : lgT.map Prod.fst = tfront.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP 7 lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgT + 7) eps1 esEnd asm' →
        StackDiscHS (totalGain lgT + 7) eps1 { sMid with instIdx := 0 } asm')
    -- the CALL instruction facts at the terminal fold output / threaded state
    (hopcC : instC.opcode = Opcode.CALL)
    (hcomputeC : computeOperands instC = ovars.map Operand.Var)
    (houtsC : instC.outputs = [out])
    (hndC : ovars.Nodup)
    (hovarsS : ∀ v ∈ ovars, v ∈ (eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgT.flatMap (fun e => e.2))
    (hliveallC : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hliveC : nextLiveness.contains out = true)
    (hspMT : tpsT.spilled = MT)
    (hovMT : ∀ v ∈ ovars, alookup' MT (Operand.Var v) = none)
    (hevalC : evalOperands instC.operands tsEndT = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvalsC : List.map (operandVal tsEndT lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrevC : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargsC : aOff.toNat + aSz.toNat ≤ tpsT.alloc.fnEom)
    (haszltC : aSz.toNat < USize.size)
    (hro1C : rOff.toNat ≤ tsEndT.memory.size)
    (hretbelowC : rOff.toNat + rSz.toNat ≤ tpsT.alloc.fnEom)
    (hfnEomMono : ∀ asm' : AsmState, as.memory.size ≤ asm'.memory.size →
        tpsT.alloc.fnEom ≤ asm'.memory.size)
    (hfreshSC : ¬ Operand.Var out ∈ tpsT.stack)
    (houtovC : out ∉ ovars)
    (hspill_outC : AssocList.lookup Operand Nat MT (Operand.Var out) = none)
    (hspillRegC : ∀ op off', AssocList.lookup Operand Nat MT op = some off' →
        tpsT.alloc.fnEom ≤ off')
    (hcallC : evmCall subEvmFuel tsEndT.accounts tsEndT.callCtx.contract tsEndT.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (tsEndT.memory.readWithPadding aOff.toNat aSz.toNat).toList tsEndT.txCtx.gasprice 0
      (!tsEndT.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoopC : optimisticSwapPlan dfg instC nextLiveness nextIsTerminator
        { (emitInputPlan instC.opcode (computeOperands instC) nextLiveness tpsT).2 with
          stack := tpsT.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan instC.opcode (computeOperands instC) nextLiveness tpsT).2 with
              stack := tpsT.stack ++ [Operand.Var out] }))
    -- terminal block: layout
    (htblock : asmBlockAt prog idx (executePlan (([StackOp.SOLabel tlab] ++ topsT)
      ++ (generateRegularInstPlan liveness dfg cfg fnG instC nextLiveness false nextIsTerminator
          curBbLabel tpsT).1)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ topsT)).length)
    (htcallLenEq : tcallLen = (executePlan (generateRegularInstPlan liveness dfg cfg fnG instC
        nextLiveness false nextIsTerminator curBbLabel tpsT).1).length)
    (htlt : idx + tbodyLen + tcallLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen + tcallLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 2 + (tbodyLen + tcallLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  obtain ⟨asMid, hrunE, hrelMid, hpcMid, hsdMid, hsvMid⟩ :=
    hasm_regularHSVP_jmp (totalGain lgT + 7) hfront1 hready1 hesd0 hesv0 hespM herel0 hethread
      heblockF hebodyLenEqF hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  rw [hfold1] at hrelMid hsdMid hsvMid
  have hmonoE : as.memory.size ≤ asMid.memory.size := runAsm_memory_size_mono hrunE
  -- the CALL+STOP terminal segment at the threaded state
  have htblockF : asmBlockAt prog asMid.pc
      (executePlan (([StackOp.SOLabel tlab] ++ (lgT.foldl
          (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1)
        ++ (generateRegularInstPlan liveness dfg cfg fnG instC nextLiveness false nextIsTerminator
            curBbLabel (lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2))
              ([], eps1)).2).1)) := by
    rw [hfoldT, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ (lgT.foldl
      (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfoldT]; exact htbodyLenEq
  have htcallLenEqF : tcallLen = (executePlan (generateRegularInstPlan liveness dfg cfg fnG instC
      nextLiveness false nextIsTerminator curBbLabel (lgT.foldl
        (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).2).1).length := by
    rw [hfoldT]; exact htcallLenEq
  have htlt' : asMid.pc + tbodyLen + tcallLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen + tcallLen, htlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHSVP_call_stop (budget := prog.length - (ebodyLen + 2))
    (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fnG)
    hfrontT hreadyT (hsdTransport asMid hsdMid)
    hsvMid hspM1 (hrelTransport asMid hrelMid) htthread
    hopcC hcomputeC houtsC hndC hovarsS hliveallC hliveC
    (by rw [hfoldT]; exact hspMT) hovMT hevalC hvalsC hvalrevC
    (by rw [hfoldT]; exact hargsC) haszltC hro1C
    (by rw [hfoldT]; exact hretbelowC)
    (by rw [hfoldT]; exact hfnEomMono asMid hmonoE)
    (by rw [hfoldT]; exact hfreshSC) houtovC hspill_outC
    (by rw [hfoldT]; exact hspillRegC) hcallC
    (by rw [hfoldT]; exact hoptnoopC)
    htblockF htbodyLenEqF htcallLenEqF htlt' htget' (by omega)
  -- Venom-side call step at the threaded state
  have hcallV : evmCall subEvmFuel tsEndT.accounts tsEndT.callCtx.contract tsEndT.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (readMemory aOff.toNat aSz.toNat tsEndT).toList tsEndT.txCtx.gasprice 0
      (!tsEndT.callCtx.static)
      = (success, newAccs, ret) := by
    rw [readMemory]; exact hcallC
  have htstep : stepExternalCall subEvmFuel instC tsEndT
      = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) := by
    unfold stepExternalCall
    rw [hevalC]
    simp only [bind, Option.bind, hopcC, houtsC, hcallV]
  exact hfsim_jmp_then_halt_extcall hlk1 hebb hecons hephi henonterm hethread heterm_step
    heisterm henohalt hrunE (by omega) hlk2 htbb htcons htphi htnonterm (by intro i hi; cases hi)
    htthread (by rw [hopcC]; rfl) htstep rfl htterm_step hasmN

/-- **Two-block whole-function correspondence: call then RETURN the result** — the
    call-then-return sibling of `hfsim_regularHSVP_jmp_call_stop`: the terminal block runs
    `tfront ++ [CALL]` then RETURNs `memory[woff, woff+wsz)` from the writeback state (the asm
    side via `hasm_regularHSVP_call_return_var`, plan named `(cops, cps)`). -/
theorem hfsim_regularHSVP_jmp_call_return_var
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fnG : IrFunction}
    {instC : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {gp1 gpT : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction}
    {tsEndT : VenomState}
    {el tlab target : String} {eS0 : List String}
    {eM0 eM1 MT : AssocList Operand Nat}
    {lg1 lgT : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tpsT : PlanState} {eops1 topsT : List StackOp}
    {ebodyLen tbodyLen tcallLen temitLen off idx : Nat}
    {offv szv : String} {woff wsz : bytes32} {opc2 : Opcode}
    {cops : List StackOp} {cps : PlanState}
    {ovars : List String} {out : String}
    {gas addr value aOff aSz rOff rSz : bytes32} {vals : List bytes32}
    {success : bytes32} {newAccs : Accounts} {ret : List byte}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, tpsT))
    -- entry block: Venom structure
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- entry block: spill-aware asm segment (fuel = terminal requirement, threaded)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lgT + 7) lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lgT + 7)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- terminal block: Venom structure (body = tfront ++ [callInst], STOP terminator)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = (tfront ++ [instC] ++ []) ++ [tterm])
    (htcons : (tfront ++ [instC] ++ []) ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEndT)
    (htterm_step : stepInstBase tterm
        { (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) with
          instIdx := tfront.length + 1 }
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat
        { (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) with
          instIdx := tfront.length + 1 })
        { (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) with
          instIdx := tfront.length + 1 })))
    -- terminal block: the CALL+STOP asm segment at the threaded state
    (hfrontT : lgT.map Prod.fst = tfront.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP 7 lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgT + 7) eps1 esEnd asm' →
        StackDiscHS (totalGain lgT + 7) eps1 { sMid with instIdx := 0 } asm')
    -- the CALL instruction facts at the terminal fold output / threaded state
    (hopcC : instC.opcode = Opcode.CALL)
    (hcomputeC : computeOperands instC = ovars.map Operand.Var)
    (houtsC : instC.outputs = [out])
    (hndC : ovars.Nodup)
    (hovarsS : ∀ v ∈ ovars, v ∈ (eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgT.flatMap (fun e => e.2))
    (hliveallC : ∀ v ∈ ovars, nextLiveness.contains v = true)
    (hliveC : nextLiveness.contains out = true)
    (hspMT : tpsT.spilled = MT)
    (hovMT : ∀ v ∈ ovars, alookup' MT (Operand.Var v) = none)
    (hevalC : evalOperands instC.operands tsEndT = some [gas, addr, value, aOff, aSz, rOff, rSz])
    (hvalsC : List.map (operandVal tsEndT lo) (ovars.map Operand.Var) = List.map some vals)
    (hvalrevC : vals.reverse = [gas, addr, value, aOff, aSz, rOff, rSz])
    (hargsC : aOff.toNat + aSz.toNat ≤ tpsT.alloc.fnEom)
    (haszltC : aSz.toNat < USize.size)
    (hro1C : rOff.toNat ≤ tsEndT.memory.size)
    (hretbelowC : rOff.toNat + rSz.toNat ≤ tpsT.alloc.fnEom)
    (hfnEomMono : ∀ asm' : AsmState, as.memory.size ≤ asm'.memory.size →
        tpsT.alloc.fnEom ≤ asm'.memory.size)
    (hfreshSC : ¬ Operand.Var out ∈ tpsT.stack)
    (houtovC : out ∉ ovars)
    (hspill_outC : AssocList.lookup Operand Nat MT (Operand.Var out) = none)
    (hspillRegC : ∀ op off', AssocList.lookup Operand Nat MT op = some off' →
        tpsT.alloc.fnEom ≤ off')
    (hcallC : evmCall subEvmFuel tsEndT.accounts tsEndT.callCtx.contract tsEndT.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (tsEndT.memory.readWithPadding aOff.toNat aSz.toNat).toList tsEndT.txCtx.gasprice 0
      (!tsEndT.callCtx.static)
      = (success, newAccs, ret))
    (hoptnoopC : optimisticSwapPlan dfg instC nextLiveness nextIsTerminator
        { (emitInputPlan instC.opcode (computeOperands instC) nextLiveness tpsT).2 with
          stack := tpsT.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan instC.opcode (computeOperands instC) nextLiveness tpsT).2 with
              stack := tpsT.stack ++ [Operand.Var out] }))
    -- the CALL plan named + the RETURN operands
    (hcplanW : generateRegularInstPlan liveness dfg cfg fnG instC nextLiveness false
        nextIsTerminator curBbLabel tpsT = (cops, cps))
    (hoffCP : Operand.Var offv ∈ cps.stack)
    (hszCP : Operand.Var szv ∈ cps.stack)
    (hoffMC : alookup' cps.spilled (Operand.Var offv) = none)
    (hszMC : alookup' cps.spilled (Operand.Var szv) = none)
    (hliveoff : nextLiveness.contains offv = true) (hliveszv : nextLiveness.contains szv = true)
    (hvoffW : lookupVar offv (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) = some woff)
    (hvszW : lookupVar szv (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) = some wsz)
    (hcov0W : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hsafeR : woff.toNat + wsz.toNat ≤ cps.alloc.fnEom)
    (hlenR : wsz.toNat < USize.size)
    -- terminal block: layout
    (htblock : asmBlockAt prog idx (executePlan ((([StackOp.SOLabel tlab] ++ topsT) ++ cops)
      ++ (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ topsT)).length)
    (htcallLenEq : tcallLen = (executePlan cops).length)
    (htemitLenEq : temitLen = (executePlan
        (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1).length)
    (htlt : idx + tbodyLen + tcallLen + temitLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen + tcallLen + temitLen, htlt⟩ = AsmInst.AsmOp "RETURN")
    (hbudget : ebodyLen + 2 + (tbodyLen + tcallLen + temitLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  obtain ⟨asMid, hrunE, hrelMid, hpcMid, hsdMid, hsvMid⟩ :=
    hasm_regularHSVP_jmp (totalGain lgT + 7) hfront1 hready1 hesd0 hesv0 hespM herel0 hethread
      heblockF hebodyLenEqF hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  rw [hfold1] at hrelMid hsdMid hsvMid
  have hmonoE : as.memory.size ≤ asMid.memory.size := runAsm_memory_size_mono hrunE
  -- the CALL+STOP terminal segment at the threaded state
  have htblockF : asmBlockAt prog asMid.pc
      (executePlan ((([StackOp.SOLabel tlab] ++ (lgT.foldl
          (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1) ++ cops)
        ++ (emitInputPlan opc2 [Operand.Var szv, Operand.Var offv] nextLiveness cps).1)) := by
    rw [hfoldT, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ (lgT.foldl
      (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfoldT]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen + tcallLen + temitLen < prog.length := by
    rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen + tcallLen + temitLen, htlt'⟩
      = AsmInst.AsmOp "RETURN" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHSVP_call_return_var (budget := prog.length - (ebodyLen + 2))
    (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fnG)
    hfrontT hreadyT (hsdTransport asMid hsdMid)
    hsvMid hspM1 (hrelTransport asMid hrelMid) htthread
    hopcC hcomputeC houtsC hndC hovarsS hliveallC hliveC
    (by rw [hfoldT]; exact hspMT) hovMT hevalC hvalsC hvalrevC
    (by rw [hfoldT]; exact hargsC) haszltC hro1C
    (by rw [hfoldT]; exact hretbelowC)
    (by rw [hfoldT]; exact hfnEomMono asMid hmonoE)
    (by rw [hfoldT]; exact hfreshSC) houtovC hspill_outC
    (by rw [hfoldT]; exact hspillRegC) hcallC
    (by rw [hfoldT]; exact hoptnoopC)
    (by rw [hfoldT]; exact hcplanW)
    hoffCP hszCP hoffMC hszMC hliveoff hliveszv hvoffW hvszW
    (Or.imp_right (fun h => le_trans h hmonoE) hcov0W) hsafeR hlenR
    htblockF htbodyLenEqF htcallLenEq htemitLenEq htlt' htget' (by omega)
  -- Venom-side call step at the threaded state
  have hcallV : evmCall subEvmFuel tsEndT.accounts tsEndT.callCtx.contract tsEndT.txCtx.origin
      (AccountAddress.ofUInt256 addr) (AccountAddress.ofUInt256 addr) gas value value
      (readMemory aOff.toNat aSz.toNat tsEndT).toList tsEndT.txCtx.gasprice 0
      (!tsEndT.callCtx.static)
      = (success, newAccs, ret) := by
    rw [readMemory]; exact hcallC
  have htstep : stepExternalCall subEvmFuel instC tsEndT
      = some (callWriteback out rOff.toNat rSz.toNat success newAccs ret tsEndT) := by
    unfold stepExternalCall
    rw [hevalC]
    simp only [bind, Option.bind, hopcC, houtsC, hcallV]
  exact hfsim_jmp_then_halt_extcall hlk1 hebb hecons hephi henonterm hethread heterm_step
    heisterm henohalt hrunE (by omega) hlk2 htbb htcons htphi htnonterm (by intro i hi; cases hi)
    htthread (by rw [hopcC]; rfl) htstep rfl htterm_step hasmN

/-- **Generic two-block CONDITIONAL chain `hfsim`, spill-aware** (gap A beyond linear): the entry
    block carries a padded varying-growth (HSVP) body and ends in `JNZ c ifNz ifZ` with a non-zero
    condition — the branch is TAKEN and the whole-function `runBlocks`/`runAsm` correspondence is
    discharged generically, landing on the `ifNz` block (HSVP body + STOP). The condition variable
    sits at the fold-output top (the body's last computation); its asm tail is
    `DUP1 ; push-label ifNz ; JUMPI` (`hasm_regularHSVP_jnz_taken`), whose taken `JUMPI` restores
    the fold-exit stack so the invariants thread exactly as across a JMP. The Venom JNZ step is
    derived internally from the operands and the non-zero condition. -/
theorem hfsim_regularHSVP_jnz_taken_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gp2 : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab ifNz ifZ : String} {eS0 : List String}
    {eM0 eM1 : AssocList Operand Nat}
    {lg1 lg2 : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {P2 ebodyLen tbodyLen off idx : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfold2 : lg2.foldl (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)
      = (tops2, tps2))
    -- entry block: Venom structure, JNZ terminator (taken)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hnohaltE : esEnd.halted = false)
    (hsMid : sMid = jumpTo ifNz esEnd)
    -- entry block: spill-aware asm segment (fuel = successor requirement, threaded)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lg2 + P2) lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lg2 + P2)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    -- the condition at the fold-output top, and the resolved conditional tail
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt (haltState tsEnd))
    -- halting block: spill-aware asm segment at the THREADED state
    (hfront2 : lg2.map Prod.fst = tfront.zipIdx 0)
    (hready2 : BodyStepsReadyHSVP P2 lo offsetToPc prog gp2 lg2
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lg2 + P2) eps1 esEnd asm' →
        StackDiscHS (totalGain lg2 + P2) eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idx + tbodyLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 3 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- the Venom JNZ step: taken branch, OK (jumpTo ifNz)
  have heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid := by
    rw [hsMid]
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd = some cond from hcondv]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcond) h
  have heisterm : isTerminator eterm.opcode = true := by rw [hjopc]; decide
  have henohalt : sMid.halted = false := by rw [hsMid, jumpTo]; exact hnohaltE
  -- entry segment: HSVP body + DUP1 ; push-label ; JUMPI (taken)
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  have hstkF : (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).2.stack
      = base ++ [Operand.Var c] := by
    rw [hfold1]; exact hstk1
  have hcvalF : operandVal esEnd lo (Operand.Var c) = some cond := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv
  obtain ⟨asMid, hrunE, hrelMid, hpcMid, hsdMid, hsvMid⟩ :=
    hasm_regularHSVP_jnz_taken (totalGain lg2 + P2) hfront1 hready1 hesd0 hesv0 hespM herel0
      hethread heblockF hebodyLenEqF hstkF hcvalF hcond hpc1 hdup hpc2 hpush hoff_lk hoff
      hpc3 hjumpi hidx_lk
  rw [hfold1] at hrelMid hsdMid hsvMid
  -- terminal segment at the threaded state
  have htblockF : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfold2]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen, htlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHSVP_stop P2 (budget := prog.length - (ebodyLen + 3))
    hfront2 hready2 (hsdTransport asMid hsdMid) hsvMid hspM1 (hrelTransport asMid hrelMid)
    htthread htblockF htbodyLenEqF htlt' htget' (by omega)
  exact hfsim_jmp_then_halt hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN

/-- **Generic two-block conditional chain, branch NOT taken**: the zero-condition twin of
    `hfsim_regularHSVP_jnz_taken_stop` — the `JUMPI` falls through and the trailing
    `push-label ifZ ; JUMP` lands on the `ifZ` block (HSVP body + STOP). Together the pair covers
    both outcomes of a conditional two-block chain, spill-aware. -/
theorem hfsim_regularHSVP_jnz_nottaken_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gp2 : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb termBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction} {tsEnd : VenomState}
    {el tlab ifNz ifZ : String} {eS0 : List String}
    {eM0 eM1 : AssocList Operand Nat}
    {lg1 lg2 : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {P2 ebodyLen tbodyLen offNz offZ idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfold2 : lg2.foldl (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)
      = (tops2, tps2))
    -- entry block: Venom structure, JNZ terminator (taken)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hnohaltE : esEnd.halted = false)
    (hsMid : sMid = jumpTo ifZ esEnd)
    -- entry block: spill-aware asm segment (fuel = successor requirement, threaded)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lg2 + P2) lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lg2 + P2)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    -- the condition at the fold-output top, and the resolved conditional tail
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as.pc + ebodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as.pc + ebodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as.pc + ebodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    -- halting block: Venom structure
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt (haltState tsEnd))
    -- halting block: spill-aware asm segment at the THREADED state
    (hfront2 : lg2.map Prod.fst = tfront.zipIdx 0)
    (hready2 : BodyStepsReadyHSVP P2 lo offsetToPc prog gp2 lg2
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lg2 + P2) eps1 esEnd asm' →
        StackDiscHS (totalGain lg2 + P2) eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idxZ (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idxZ + tbodyLen < prog.length)
    (htget : prog.get ⟨idxZ + tbodyLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 5 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- the Venom JNZ step: zero condition, OK (jumpTo ifZ)
  have heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid := by
    rw [hsMid]
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd = some cond from hcondv]
    split
    · rename_i h; exact absurd h (by rw [hcond]; decide)
    · rfl
  have heisterm : isTerminator eterm.opcode = true := by rw [hjopc]; decide
  have henohalt : sMid.halted = false := by rw [hsMid, jumpTo]; exact hnohaltE
  -- entry segment: HSVP body + DUP1 ; push-label ; JUMPI (fall) ; push-label ; JUMP
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  have hstkF : (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).2.stack
      = base ++ [Operand.Var c] := by
    rw [hfold1]; exact hstk1
  have hcvalF : operandVal esEnd lo (Operand.Var c) = some cond := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv
  obtain ⟨asMid, hrunE, hrelMid, hpcMid, hsdMid, hsvMid⟩ :=
    hasm_regularHSVP_jnz_nottaken (totalGain lg2 + P2) hfront1 hready1 hesd0 hesv0 hespM herel0
      hethread heblockF hebodyLenEqF hstkF hcvalF hcond hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz
      hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  rw [hfold1] at hrelMid hsdMid hsvMid
  -- terminal segment at the threaded state
  have htblockF : asmBlockAt prog asMid.pc
      (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)) := by
    rw [hfold2, hpcMid]; exact htblock
  have htbodyLenEqF : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ (lg2.foldl
        (fun acc x => (acc.1 ++ (gp2 x.1 acc.2).1, (gp2 x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfold2]; exact htbodyLenEq
  have htlt' : asMid.pc + tbodyLen < prog.length := by rw [hpcMid]; exact htlt
  have htget' : prog.get ⟨asMid.pc + tbodyLen, htlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid]) htget
  have hasmN := hasm_regularHSVP_stop P2 (budget := prog.length - (ebodyLen + 5))
    hfront2 hready2 (hsdTransport asMid hsdMid) hsvMid hspM1 (hrelTransport asMid hrelMid)
    htthread htblockF htbodyLenEqF htlt' htget' (by omega)
  exact hfsim_jmp_then_halt hlk1 hebb hecons hephi henonterm hethread heterm_step heisterm henohalt
    hrunE (by omega) hlk2 htbb htcons htphi htnonterm htthread htterm_step hasmN

/-- **Generic THREE-block conditional `hfsim` — the branching chain** (gap A beyond linear,
    closed for the 2-successor diamond entry): entry block = HSVP body + `JNZ c ifNz ifZ`, with a
    halting HSVP block at EACH target. The whole-function correspondence holds for ANY runtime
    condition value — the proof dispatches on `cond = 0` into the taken/not-taken chain pair. The
    two successors may have different bodies/gains; the shared entry invariant runs at the common
    budget `P` and each leg's padding recovers it (`totalGain lgT + PT = P = totalGain lgZ + PZ`). -/
theorem hfsim_regularHSVP_jnz_branch_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gpT gpZ : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb thenBb elseBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfrontT : List Instruction} {ttermT thdT : Instruction} {ttlT : List Instruction} {tsEndT : VenomState}
    {tfrontZ : List Instruction} {ttermZ thdZ : Instruction} {ttlZ : List Instruction} {tsEndZ : VenomState}
    {el tlabT tlabZ ifNz ifZ : String} {eS0 : List String}
    {eM0 eM1 : AssocList Operand Nat}
    {lg1 lgT lgZ : List ((Instruction × Nat) × List String)}
    {eps0 eps1 tpsT tpsZ : PlanState} {eops1 topsT topsZ : List StackOp}
    {P PT PZ ebodyLen tbodyLenT tbodyLenZ offNz offZ idxNz idxZ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, tpsT))
    (hfoldZ : lgZ.foldl (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)
      = (topsZ, tpsZ))
    (hPT : totalGain lgT + PT = P) (hPZ : totalGain lgZ + PZ = P)
    -- entry block: Venom structure, JNZ terminator with an ARBITRARY condition value
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hnohaltE : esEnd.halted = false)
    -- entry block: spill-aware asm segment at the shared successor budget P
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP P lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + P) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    -- the condition at the fold-output top, and the resolved conditional tail
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as.pc + ebodyLen + 3 < prog.length)
    (hpushZ : prog.get ⟨as.pc + ebodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as.pc + ebodyLen + 4 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxNz_lk : AssocList.lookup Nat Nat offsetToPc offNz = some idxNz)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    -- shared boundary: the exit map
    (hspM1 : eps1.spilled = eM1)
    -- TAKEN leg: the ifNz block (HSVP body + STOP)
    (hlkT : lookupBlock (jumpTo ifNz esEnd).currentBb fn.blocks = some thenBb)
    (htbbT : thenBb.instructions = tfrontT ++ [ttermT])
    (htconsT : tfrontT ++ [ttermT] = thdT :: ttlT)
    (htphiT : thdT.opcode ≠ Opcode.PHI)
    (htnontermT : ∀ inst ∈ tfrontT, isTerminator inst.opcode = false)
    (htthreadT : execBodyThread tfrontT 0 { jumpTo ifNz esEnd with instIdx := 0 } = some tsEndT)
    (httermT : stepInstBase ttermT tsEndT = ExecResult.Halt (haltState tsEndT))
    (hfrontT : lgT.map Prod.fst = tfrontT.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP PT lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hrelTransportT : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (hsdTransportT : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (htblockT : asmBlockAt prog idxNz (executePlan ([StackOp.SOLabel tlabT] ++ topsT)))
    (htbodyLenEqT : tbodyLenT = (executePlan ([StackOp.SOLabel tlabT] ++ topsT)).length)
    (htltT : idxNz + tbodyLenT < prog.length)
    (htgetT : prog.get ⟨idxNz + tbodyLenT, htltT⟩ = AsmInst.AsmOp "STOP")
    (hbudgetT : ebodyLen + 3 + (tbodyLenT + 1) ≤ prog.length)
    -- NOT-TAKEN leg: the ifZ block (HSVP body + STOP)
    (hlkZ : lookupBlock (jumpTo ifZ esEnd).currentBb fn.blocks = some elseBb)
    (htbbZ : elseBb.instructions = tfrontZ ++ [ttermZ])
    (htconsZ : tfrontZ ++ [ttermZ] = thdZ :: ttlZ)
    (htphiZ : thdZ.opcode ≠ Opcode.PHI)
    (htnontermZ : ∀ inst ∈ tfrontZ, isTerminator inst.opcode = false)
    (htthreadZ : execBodyThread tfrontZ 0 { jumpTo ifZ esEnd with instIdx := 0 } = some tsEndZ)
    (httermZ : stepInstBase ttermZ tsEndZ = ExecResult.Halt (haltState tsEndZ))
    (hfrontZ : lgZ.map Prod.fst = tfrontZ.zipIdx 0)
    (hreadyZ : BodyStepsReadyHSVP PZ lo offsetToPc prog gpZ lgZ
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hrelTransportZ : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (hsdTransportZ : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (htblockZ : asmBlockAt prog idxZ (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)))
    (htbodyLenEqZ : tbodyLenZ = (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)).length)
    (htltZ : idxZ + tbodyLenZ < prog.length)
    (htgetZ : prog.get ⟨idxZ + tbodyLenZ, htltZ⟩ = AsmInst.AsmOp "STOP")
    (hbudgetZ : ebodyLen + 5 + (tbodyLenZ + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  by_cases hc : cond = EvmYul.UInt256.ofNat 0
  · -- condition zero: fall through to ifZ
    exact hfsim_regularHSVP_jnz_nottaken_stop hfold1 hfoldZ hlk1 hebb hecons hephi henonterm
      hethread hjopc hjops hcondv hc hnohaltE rfl hfront1
      (by rw [hPZ]; exact hready1) (by rw [hPZ]; exact hesd0) hesv0 hespM herel0 heblock
      hebodyLenEq hstk1 hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
      hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlkZ htbbZ htconsZ htphiZ htnontermZ htthreadZ httermZ
      hfrontZ hreadyZ hspM1 hrelTransportZ (by rw [hPZ]; exact hsdTransportZ) htblockZ
      htbodyLenEqZ htltZ htgetZ hbudgetZ
  · -- condition non-zero: branch taken to ifNz
    exact hfsim_regularHSVP_jnz_taken_stop hfold1 hfoldT hlk1 hebb hecons hephi henonterm
      hethread hjopc hjops hcondv hc hnohaltE rfl hfront1
      (by rw [hPT]; exact hready1) (by rw [hPT]; exact hesd0) hesv0 hespM herel0 heblock
      hebodyLenEq hstk1 hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hidxNz_lk
      hlkT htbbT htconsT htphiT htnontermT htthreadT httermT hfrontT hreadyT hspM1
      hrelTransportT (by rw [hPT]; exact hsdTransportT) htblockT htbodyLenEqT htltT htgetT
      (by omega)

/-- **A live spill crosses the JMP** — the cross-block-spill instantiation of the spill-aware
    chain. Two-block function: block 1 runs a both-live binop while the single-entry spilled map
    `[(w, offw)]` passes over it UNTOUCHED (`w` live in block 1's out-liveness), the JMP carries
    the map to block 2 (`eM1 = eM0`, the boundary is just `hspM1`), and block 2's TLOAD consumes
    the spilled `w` (restore, map → `[]`) before halting. Instantiates
    `hfsim_regularHSVP_jmp_stop` with the passover feeds — the first whole-function correspondence
    where a spill slot stays live across a block boundary. -/
theorem hfsim_spill_cross_jmp_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {vs sMid : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {entryBb termBb : BasicBlock}
    {i1 i2 eterm tterm : Instruction} {esEnd tsEnd : VenomState}
    {enl tnl : List String} {curBb1 curBb2 : String}
    {el tlab target : String} {eS0 : List String}
    {x1 y1 o1 w o2 name1 : String}
    {eps0 eps1 tps2 : PlanState} {eops1 tops2 : List StackOp}
    {P2 ebodyLen tbodyLen off offw idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hfold1 : [((i1, 0), [o1])].foldl (fun acc x =>
        (acc.1 ++ ((fun (w' : Instruction × Nat) (p : PlanState) =>
          generateRegularInstPlan liveness dfg cfg fn w'.1 enl false true curBb1 p) x.1 acc.2).1,
         ((fun (w' : Instruction × Nat) (p : PlanState) =>
          generateRegularInstPlan liveness dfg cfg fn w'.1 enl false true curBb1 p) x.1 acc.2).2))
        ([], eps0) = (eops1, eps1))
    (hfold2 : [((i2, 0), [w, o2])].foldl (fun acc x =>
        (acc.1 ++ ((fun (w' : Instruction × Nat) (p : PlanState) =>
          generateRegularInstPlan liveness dfg cfg fn w'.1 tnl false true curBb2 p) x.1 acc.2).1,
         ((fun (w' : Instruction × Nat) (p : PlanState) =>
          generateRegularInstPlan liveness dfg cfg fn w'.1 tnl false true curBb2 p) x.1 acc.2).2))
        ([], eps1) = (tops2, tps2))
    -- entry block: Venom structure
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = [i1] ++ [eterm])
    (hephi : i1.opcode ≠ Opcode.PHI)
    (hent1 : isTerminator i1.opcode = false)
    (hethread : execBodyThread [i1] 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    -- block 1 instruction: both-live binop, w untouched
    (hname1 : opcodeToEvmName i1.opcode = some name1)
    (hncomm1 : isCommutative i1.opcode = false)
    (hnjmp1 : i1.opcode ≠ Opcode.JMP)
    (hcompute1 : computeOperands i1 = i1.operands.reverse)
    (hdispatch1 : ∀ v, stepInstBase i1 v = execPure2 f i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1)
    (hx1S : x1 ∈ eS0) (hy1S : y1 ∈ eS0) (ho1S : o1 ∉ eS0)
    (hwx1 : w ≠ x1) (hwy1 : w ≠ y1) (hwo1 : w ≠ o1)
    (helive1 : enl.contains o1 = true)
    (helivex1 : enl.contains x1 = true) (helivey1 : enl.contains y1 = true)
    (helivew : enl.contains w = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name1 → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop1 : ∀ (p : PlanState), optimisticSwapPlan dfg i1 enl true
        { (emitInputPlan i1.opcode i1.operands.reverse enl p).2 with
          stack := p.stack ++ [Operand.Var o1] }
      = ([], { (emitInputPlan i1.opcode i1.operands.reverse enl p).2 with
              stack := p.stack ++ [Operand.Var o1] }))
    -- entry block: asm segment facts
    (hesd0 : StackDiscHS (totalGain [((i1, 0), [o1])]
        + (totalGain [((i2, 0), [w, o2])] + P2)) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0)
    (hespM : eps0.spilled = ([(Operand.Var w, offw)] : AssocList Operand Nat))
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hpush : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- halting block: Venom structure
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = [i2] ++ [tterm])
    (htphi : i2.opcode ≠ Opcode.PHI)
    (htnt1 : isTerminator i2.opcode = false)
    (htthread : execBodyThread [i2] 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt (haltState tsEnd))
    -- block 2 instruction: TLOAD consuming the spilled w
    (hname2 : opcodeToEvmName i2.opcode = some "TLOAD")
    (hnjmp2 : i2.opcode ≠ Opcode.JMP)
    (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execRead1 (fun key s => tload key s) i2 v)
    (hops2 : i2.operands = [Operand.Var w]) (houts2 : i2.outputs = [o2])
    (htlive2 : tnl.contains o2 = true) (htlivew : tnl.contains w = true)
    (ho2w : o2 ≠ w) (hwo2 : w ≠ o2) (ho2S : o2 ∉ eS0 ++ [o1])
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "TLOAD" →
          asmStep offsetToPc prog s = asmStateUnop (fun k s => tload k s.toVenomState) s)
    (hoptnoop2 : ∀ p : PlanState, optimisticSwapPlan dfg i2 tnl true
        { (emitInputPlan i2.opcode i2.operands.reverse tnl p).2 with
          stack := p.stack ++ [Operand.Var w, Operand.Var o2] }
      = ([], { (emitInputPlan i2.opcode i2.operands.reverse tnl p).2 with
              stack := p.stack ++ [Operand.Var w, Operand.Var o2] }))
    -- the boundary: the UNCHANGED single-entry map crosses the JMP
    (hspM1 : eps1.spilled = ([(Operand.Var w, offw)] : AssocList Operand Nat))
    (hrelTransport : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { sMid with instIdx := 0 } asm')
    (hsdTransport : ∀ (asm' : AsmState),
        StackDiscHS (totalGain [((i2, 0), [w, o2])] + P2) eps1 esEnd asm' →
        StackDiscHS (totalGain [((i2, 0), [w, o2])] + P2) eps1 { sMid with instIdx := 0 } asm')
    (htblock : asmBlockAt prog idx (executePlan ([StackOp.SOLabel tlab] ++ tops2)))
    (htbodyLenEq : tbodyLen = (executePlan ([StackOp.SOLabel tlab] ++ tops2)).length)
    (htlt : idx + tbodyLen < prog.length)
    (htget : prog.get ⟨idx + tbodyLen, htlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 2 + (tbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hready1 : BodyStepsReadyHSVP (totalGain [((i2, 0), [w, o2])] + P2) lo offsetToPc prog
      (fun w' p => generateRegularInstPlan liveness dfg cfg fn w'.1 enl false true curBb1 p)
      [((i1, 0), [o1])] eS0 ([(Operand.Var w, offw)] : AssocList Operand Nat) :=
    bodyStepsReadyHSVP_cons (M' := ([(Operand.Var w, offw)] : AssocList Operand Nat))
      (bodyStepHSVP_of_bodyStepHSV
        (bodyStepHSV_nonCommBinop_bothlive hname1 hncomm1 hnjmp1 hcompute1 hdispatch1 hops1
          houts1 hxy1 hx1S hy1S ho1S
          (alookup'_single_ne hwx1 offw) (alookup'_single_ne hwy1 offw)
          (alookup'_single_ne hwo1 offw)
          (fun q hq => releaseDeadSpills_spilled_of_live_single hq helivew)
          helive1 helivex1 helivey1 hdisp1 hoptnoop1))
      bodyStepsReadyHSVP_nil
  have hready2 : BodyStepsReadyHSVP P2 lo offsetToPc prog
      (fun w' p => generateRegularInstPlan liveness dfg cfg fn w'.1 tnl false true curBb2 p)
      [((i2, 0), [w, o2])] (eS0 ++ [((i1, 0), [o1])].flatMap (fun e => e.2))
      ([(Operand.Var w, offw)] : AssocList Operand Nat) :=
    bodyStepsReadyHSVP_cons (M' := ([] : AssocList Operand Nat))
      (bodyStepHSVP_of_bodyStepHSV
        (bodyStepHSV_tload_spilled hname2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 htlive2
          htlivew ho2w (by simpa using ho2S)
          (alookup'_single_self (Operand.Var w) offw) (alookup'_single_ne hwo2 offw)
          (fun q hq => releaseDeadSpills_spilled_of_nil (by rw [hq, aremove_single_self]))
          hdisp2 hoptnoop2))
      bodyStepsReadyHSVP_nil
  exact hfsim_regularHSVP_jmp_stop hfold1 hfold2 hlk1 hebb rfl hephi
    (by intro inst hmem; simp only [List.mem_singleton] at hmem; rw [hmem]; exact hent1)
    hethread heterm_step heisterm henohalt rfl hready1 hesd0 hesv0 hespM herel0 heblock
    hebodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk hlk2 htbb rfl htphi
    (by intro inst hmem; simp only [List.mem_singleton] at hmem; rw [hmem]; exact htnt1)
    htthread htterm_step rfl hready2 hspM1 hrelTransport hsdTransport htblock htbodyLenEq
    htlt htget hbudget
/-- **N-block linear chain from per-link runs.** Reduces `hfsim_jmp_chain`'s abstract link facts to
    what the segment lemmas actually produce: per-link Venom block structure (body threads, the
    terminator steps to the next state) and a plain per-link asm `OK`-run consuming the budget
    difference (`hasm_regularHN_jmp` / `hasm_regularHSVP_jmp` outputs). With this, an n-block
    linear-chain `hfsim` is a plug-in of K segment instances — no bespoke induction per function. -/
theorem hfsim_jmp_chain_of_runs {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    (K : Nat) (S : Nat → VenomState) (A : Nat → AsmState) (Nb : Nat → Nat) (B : Nat → BasicBlock)
    (hlink_lk : ∀ i, i < K → lookupBlock (S i).currentBb fn.blocks = some (B i))
    (hlink_struct : ∀ i, i < K →
        ∃ front term hd tl sEnd,
          (B i).instructions = front ++ [term] ∧
          front ++ [term] = hd :: tl ∧
          hd.opcode ≠ Opcode.PHI ∧
          (∀ inst ∈ front, isTerminator inst.opcode = false) ∧
          execBodyThread front 0 { S i with instIdx := 0 } = some sEnd ∧
          stepInstBase term sEnd = ExecResult.OK (S (i + 1)) ∧
          isTerminator term.opcode = true ∧
          (S (i + 1)).halted = false)
    (hNb : ∀ i, i < K → Nb (i + 1) ≤ Nb i)
    (hlink_run : ∀ i, i < K →
        runAsm (Nb i - Nb (i + 1)) offsetToPc prog (A i) = AsmResult.AsmOK (A (i + 1)))
    (hterm_lk : lookupBlock (S K).currentBb fn.blocks = some (B K))
    (hterm : ∀ f', match runBlock f' ctx (B K) (S K) with
        | ExecResult.OK s' =>
            s'.halted = true ∧ ∃ asm', runAsm (Nb K) offsetToPc prog (A K) = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm (Nb K) offsetToPc prog (A K) = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm (Nb K) offsetToPc prog (A K) = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm (Nb K) offsetToPc prog (A K) = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel s' asm'
        | _ => True) :
    match runBlocks fuel ctx fn (S 0) with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm (Nb 0) offsetToPc prog (A 0) = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm (Nb 0) offsetToPc prog (A 0) = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm (Nb 0) offsetToPc prog (A 0) = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_jmp_chain K S A Nb B hlink_lk
    (fun i hi => by
      obtain ⟨front, term, hd, tl, sEnd, hbb, hcons, hphi, hnonterm, hthread, hstep, histerm,
        hnohalt⟩ := hlink_struct i hi
      exact runBlock_jmp_arm ctx (B i) front term hd tl (S i) sEnd (S (i + 1))
        hbb hcons hphi hnonterm hthread hstep histerm hnohalt)
    (fun i hi => by
      have heq : Nb i = (Nb i - Nb (i + 1)) + Nb (i + 1) := by have := hNb i hi; omega
      rw [heq, runAsm_add_ok (hlink_run i hi)])
    hterm_lk hterm

/-- **Three-block spill-aware chain through a taken branch**: entry (HSVP body + `JNZ`, taken) →
    mid block (HSVP body + `JMP joinL`) → join block (HSVP body + STOP). The first instantiation
    of the K-indexed chain scaffold (`hfsim_jmp_chain_of_runs`, K = 2) with HSVP segments: the
    entry fuel `totalGain lg1 + (totalGain lgT + (totalGain lgJ + PJ))` threads through BOTH
    boundaries, and each link's asm run comes from its generic segment
    (`hasm_regularHSVP_jnz_taken` / `_jmp` / `_stop`). This is one arm of a diamond-with-rejoin:
    the join block's code (`topsJ` at `idxJ`) is stated against THIS path's entry plan state —
    the other arm must reconcile to the same code. -/
theorem hfsim_regularHSVP_jnz_taken_jmp_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gpT gpJ : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb thenBb joinBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfrontT : List Instruction} {ttermT thdT : Instruction} {ttlT : List Instruction} {tsEndT : VenomState}
    {jfront : List Instruction} {jterm jhd : Instruction} {jtl : List Instruction} {tsEndJ : VenomState}
    {el tlabT jlab ifNz ifZ joinL : String} {eS0 : List String}
    {eM0 eM1 eMT2 : AssocList Operand Nat}
    {lg1 lgT lgJ : List ((Instruction × Nat) × List String)}
    {eps0 eps1 epsT2 tpsJ : PlanState} {eops1 topsT topsJ : List StackOp}
    {PJ ebodyLen tbodyLenT jbodyLen offNz offJ idxT idxJ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, epsT2))
    (hfoldJ : lgJ.foldl (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsT2)
      = (topsJ, tpsJ))
    -- entry block: Venom structure, JNZ terminator (taken)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hnohaltE : esEnd.halted = false)
    -- entry block: asm segment (fuel threads through both boundaries)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lgT + (totalGain lgJ + PJ)) lo offsetToPc prog
      gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lgT + (totalGain lgJ + PJ)))
      eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hidxT_lk : AssocList.lookup Nat Nat offsetToPc offNz = some idxT)
    -- mid block (branch target): Venom structure, JMP joinL terminator
    (hlkT : lookupBlock (jumpTo ifNz esEnd).currentBb fn.blocks = some thenBb)
    (htbbT : thenBb.instructions = tfrontT ++ [ttermT])
    (htconsT : tfrontT ++ [ttermT] = thdT :: ttlT)
    (htphiT : thdT.opcode ≠ Opcode.PHI)
    (htnontermT : ∀ inst ∈ tfrontT, isTerminator inst.opcode = false)
    (htthreadT : execBodyThread tfrontT 0 { jumpTo ifNz esEnd with instIdx := 0 } = some tsEndT)
    (httermstepT : stepInstBase ttermT tsEndT = ExecResult.OK (jumpTo joinL tsEndT))
    (htistermT : isTerminator ttermT.opcode = true)
    (hnohaltT : tsEndT.halted = false)
    -- mid block: asm segment at the threaded state
    (hfrontT : lgT.map Prod.fst = tfrontT.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP (totalGain lgJ + PJ) lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport1 : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (hsdTransport1 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgT + (totalGain lgJ + PJ)) eps1 esEnd asm' →
        StackDiscHS (totalGain lgT + (totalGain lgJ + PJ)) eps1
          { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (htblockT : asmBlockAt prog idxT (executePlan ([StackOp.SOLabel tlabT] ++ topsT)))
    (htbodyLenEqT : tbodyLenT = (executePlan ([StackOp.SOLabel tlabT] ++ topsT)).length)
    (hpcJ1 : idxT + tbodyLenT < prog.length)
    (hpushJ : prog.get ⟨idxT + tbodyLenT, hpcJ1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hoffJ_lk : AssocList.lookup String Nat lo joinL = some offJ) (hoffJ : offJ < 2 ^ 256)
    (hpcJ2 : idxT + tbodyLenT + 1 < prog.length)
    (hjumpJ : prog.get ⟨idxT + tbodyLenT + 1, hpcJ2⟩ = AsmInst.AsmOp "JUMP")
    (hidxJ_lk : AssocList.lookup Nat Nat offsetToPc offJ = some idxJ)
    -- join block: Venom structure, STOP terminal
    (hlkJ : lookupBlock (jumpTo joinL tsEndT).currentBb fn.blocks = some joinBb)
    (hjbb : joinBb.instructions = jfront ++ [jterm])
    (hjcons : jfront ++ [jterm] = jhd :: jtl)
    (hjphi : jhd.opcode ≠ Opcode.PHI)
    (hjnonterm : ∀ inst ∈ jfront, isTerminator inst.opcode = false)
    (hjthread : execBodyThread jfront 0 { jumpTo joinL tsEndT with instIdx := 0 } = some tsEndJ)
    (hjterm : stepInstBase jterm tsEndJ = ExecResult.Halt (haltState tsEndJ))
    -- join block: asm segment at THIS path's threaded plan state
    (hfrontJ : lgJ.map Prod.fst = jfront.zipIdx 0)
    (hreadyJ : BodyStepsReadyHSVP PJ lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgT.flatMap (fun e => e.2)) eMT2)
    (hspMT2 : epsT2.spilled = eMT2)
    (hrelTransport2 : ∀ (asm' : AsmState), venomAsmRel lo epsT2 tsEndT asm' →
        venomAsmRel lo epsT2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (hsdTransport2 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJ) epsT2 tsEndT asm' →
        StackDiscHS (totalGain lgJ + PJ) epsT2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (htblockJ : asmBlockAt prog idxJ (executePlan ([StackOp.SOLabel jlab] ++ topsJ)))
    (hjbodyLenEq : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ topsJ)).length)
    (hjlt : idxJ + jbodyLen < prog.length)
    (hjget : prog.get ⟨idxJ + jbodyLen, hjlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 3 + (tbodyLenT + 2) + (jbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- the Venom JNZ step: taken branch
  have heterm_step : stepInstBase eterm esEnd = ExecResult.OK (jumpTo ifNz esEnd) := by
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd = some cond from hcondv]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcond) h
  have heisterm : isTerminator eterm.opcode = true := by rw [hjopc]; decide
  -- link 0: entry segment
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  have hstkF : (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).2.stack
      = base ++ [Operand.Var c] := by
    rw [hfold1]; exact hstk1
  have hcvalF : operandVal esEnd lo (Operand.Var c) = some cond := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv
  obtain ⟨asMid1, hrunE1, hrelMid1, hpcMid1, hsdMid1, hsvMid1⟩ :=
    hasm_regularHSVP_jnz_taken (totalGain lgT + (totalGain lgJ + PJ)) hfront1 hready1 hesd0 hesv0
      hespM herel0 hethread heblockF hebodyLenEqF hstkF hcvalF hcond hpc1 hdup hpc2 hpushNz
      hoffNz_lk hoffNz hpc3 hjumpi hidxT_lk
  rw [hfold1] at hrelMid1 hsdMid1 hsvMid1
  -- link 1: mid-block JMP segment at the threaded state
  have htblockT' : asmBlockAt prog asMid1.pc
      (executePlan ([StackOp.SOLabel tlabT] ++ (lgT.foldl
        (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1)) := by
    rw [hfoldT, hpcMid1]; exact htblockT
  have htbodyLenEqT' : tbodyLenT = (executePlan ([StackOp.SOLabel tlabT] ++ (lgT.foldl
        (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfoldT]; exact htbodyLenEqT
  have hpcJ1' : asMid1.pc + tbodyLenT < prog.length := by rw [hpcMid1]; exact hpcJ1
  have hpushJ' : prog.get ⟨asMid1.pc + tbodyLenT, hpcJ1'⟩
      = resolveInst lo (AsmInst.AsmPushLabel joinL) :=
    prog_get_transfer (by rw [hpcMid1]) hpushJ
  have hpcJ2' : asMid1.pc + tbodyLenT + 1 < prog.length := by rw [hpcMid1]; exact hpcJ2
  have hjumpJ' : prog.get ⟨asMid1.pc + tbodyLenT + 1, hpcJ2'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hpcMid1]) hjumpJ
  obtain ⟨asMid2, hrunT2, hrelT2, hpcMid2, hsdT2, hsvT2⟩ :=
    hasm_regularHSVP_jmp (totalGain lgJ + PJ) hfrontT hreadyT
      (hsdTransport1 asMid1 hsdMid1) hsvMid1 hspM1 (hrelTransport1 asMid1 hrelMid1)
      htthreadT htblockT' htbodyLenEqT' hpcJ1' hpushJ' hoffJ_lk hoffJ hpcJ2' hjumpJ' hidxJ_lk
  rw [hfoldT] at hrelT2 hsdT2 hsvT2
  -- terminal: join-block STOP segment
  have htblockJ' : asmBlockAt prog asMid2.pc
      (executePlan ([StackOp.SOLabel jlab] ++ (lgJ.foldl
        (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsT2)).1)) := by
    rw [hfoldJ, hpcMid2]; exact htblockJ
  have hjbodyLenEq' : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ (lgJ.foldl
        (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsT2)).1)).length := by
    rw [hfoldJ]; exact hjbodyLenEq
  have hjlt' : asMid2.pc + jbodyLen < prog.length := by rw [hpcMid2]; exact hjlt
  have hjget' : prog.get ⟨asMid2.pc + jbodyLen, hjlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid2]) hjget
  have hasmJ := hasm_regularHSVP_stop PJ
    (budget := prog.length - (ebodyLen + 3) - (tbodyLenT + 2))
    hfrontJ hreadyJ (hsdTransport2 asMid2 hsdT2) hsvT2 hspMT2 (hrelTransport2 asMid2 hrelT2)
    hjthread htblockJ' hjbodyLenEq' hjlt' hjget' (by omega)
  -- compose the two links + terminal via the K-indexed scaffold
  exact hfsim_jmp_chain_of_runs 2
    (fun i => match i with | 0 => vs | 1 => jumpTo ifNz esEnd | _ => jumpTo joinL tsEndT)
    (fun i => match i with | 0 => as | 1 => asMid1 | _ => asMid2)
    (fun i => match i with
      | 0 => prog.length
      | 1 => prog.length - (ebodyLen + 3)
      | _ => prog.length - (ebodyLen + 3) - (tbodyLenT + 2))
    (fun i => match i with | 0 => entryBb | 1 => thenBb | _ => joinBb)
    (by intro i hi
        interval_cases i
        · exact hlk1
        · exact hlkT)
    (by intro i hi
        interval_cases i
        · exact ⟨efront, eterm, ehd, etl, esEnd, hebb, hecons, hephi, henonterm, hethread,
            heterm_step, heisterm, hnohaltE⟩
        · exact ⟨tfrontT, ttermT, thdT, ttlT, tsEndT, htbbT, htconsT, htphiT, htnontermT,
            htthreadT, httermstepT, htistermT, hnohaltT⟩)
    (by intro i hi
        interval_cases i
        · show prog.length - (ebodyLen + 3) ≤ prog.length
          omega
        · show prog.length - (ebodyLen + 3) - (tbodyLenT + 2) ≤ prog.length - (ebodyLen + 3)
          omega)
    (by intro i hi
        interval_cases i
        · show runAsm (prog.length - (prog.length - (ebodyLen + 3))) offsetToPc prog as
            = AsmResult.AsmOK asMid1
          rw [show prog.length - (prog.length - (ebodyLen + 3)) = ebodyLen + 3 from by omega]
          exact hrunE1
        · show runAsm ((prog.length - (ebodyLen + 3))
              - (prog.length - (ebodyLen + 3) - (tbodyLenT + 2))) offsetToPc prog asMid1
            = AsmResult.AsmOK asMid2
          rw [show (prog.length - (ebodyLen + 3))
              - (prog.length - (ebodyLen + 3) - (tbodyLenT + 2)) = tbodyLenT + 2 from by omega]
          exact hrunT2)
    hlkJ
    (hterm_halt ctx joinBb jfront jterm jhd jtl (jumpTo joinL tsEndT) tsEndJ (haltState tsEndJ)
      hjbb hjcons hjphi hjnonterm hjthread hjterm hasmJ)

/-- **Three-block spill-aware chain through the fall-through branch**: the zero-condition twin
    of `hfsim_regularHSVP_jnz_taken_jmp_stop` — entry (HSVP body + `JNZ`, NOT taken) → the `ifZ`
    block (HSVP body + `JMP joinL`) → the SAME join block. The other arm of a diamond-with-rejoin:
    its join-code hypotheses are at the same `idxJ` as the taken arm's. -/
theorem hfsim_regularHSVP_jnz_nottaken_jmp_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gpZ gpJ : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb elseBb joinBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfrontZ : List Instruction} {ttermZ thdZ : Instruction} {ttlZ : List Instruction} {tsEndZ : VenomState}
    {jfront : List Instruction} {jterm jhd : Instruction} {jtl : List Instruction} {tsEndJ : VenomState}
    {el tlabZ jlab ifNz ifZ joinL : String} {eS0 : List String}
    {eM0 eM1 eMZ2 : AssocList Operand Nat}
    {lg1 lgZ lgJ : List ((Instruction × Nat) × List String)}
    {eps0 eps1 epsZ2 tpsJ : PlanState} {eops1 topsZ topsJ : List StackOp}
    {PJ ebodyLen tbodyLenZ jbodyLen offNz offZ offJ idxZ idxJ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldZ : lgZ.foldl (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)
      = (topsZ, epsZ2))
    (hfoldJ : lgJ.foldl (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsZ2)
      = (topsJ, tpsJ))
    -- entry block: Venom structure, JNZ terminator (taken)
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hnohaltE : esEnd.halted = false)
    -- entry block: asm segment (fuel threads through both boundaries)
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP (totalGain lgZ + (totalGain lgJ + PJ)) lo offsetToPc prog
      gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + (totalGain lgZ + (totalGain lgJ + PJ)))
      eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as.pc + ebodyLen + 3 < prog.length)
    (hpushZl : prog.get ⟨as.pc + ebodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as.pc + ebodyLen + 4 < prog.length)
    (hjumpZ : prog.get ⟨as.pc + ebodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    -- mid block (branch target): Venom structure, JMP joinL terminator
    (hlkZ2 : lookupBlock (jumpTo ifZ esEnd).currentBb fn.blocks = some elseBb)
    (htbbZ : elseBb.instructions = tfrontZ ++ [ttermZ])
    (htconsZ : tfrontZ ++ [ttermZ] = thdZ :: ttlZ)
    (htphiZ : thdZ.opcode ≠ Opcode.PHI)
    (htnontermZ : ∀ inst ∈ tfrontZ, isTerminator inst.opcode = false)
    (htthreadZ : execBodyThread tfrontZ 0 { jumpTo ifZ esEnd with instIdx := 0 } = some tsEndZ)
    (httermstepZ : stepInstBase ttermZ tsEndZ = ExecResult.OK (jumpTo joinL tsEndZ))
    (htistermZ : isTerminator ttermZ.opcode = true)
    (hnohaltZ : tsEndZ.halted = false)
    -- mid block: asm segment at the threaded state
    (hfrontZ : lgZ.map Prod.fst = tfrontZ.zipIdx 0)
    (hreadyZ : BodyStepsReadyHSVP (totalGain lgJ + PJ) lo offsetToPc prog gpZ lgZ
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransport1 : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (hsdTransport1 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgZ + (totalGain lgJ + PJ)) eps1 esEnd asm' →
        StackDiscHS (totalGain lgZ + (totalGain lgJ + PJ)) eps1
          { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (htblockZ : asmBlockAt prog idxZ (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)))
    (htbodyLenEqZ : tbodyLenZ = (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)).length)
    (hpcJ1 : idxZ + tbodyLenZ < prog.length)
    (hpushJ : prog.get ⟨idxZ + tbodyLenZ, hpcJ1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hoffJ_lk : AssocList.lookup String Nat lo joinL = some offJ) (hoffJ : offJ < 2 ^ 256)
    (hpcJ2 : idxZ + tbodyLenZ + 1 < prog.length)
    (hjumpJ : prog.get ⟨idxZ + tbodyLenZ + 1, hpcJ2⟩ = AsmInst.AsmOp "JUMP")
    (hidxJ_lk : AssocList.lookup Nat Nat offsetToPc offJ = some idxJ)
    -- join block: Venom structure, STOP terminal
    (hlkJ : lookupBlock (jumpTo joinL tsEndZ).currentBb fn.blocks = some joinBb)
    (hjbb : joinBb.instructions = jfront ++ [jterm])
    (hjcons : jfront ++ [jterm] = jhd :: jtl)
    (hjphi : jhd.opcode ≠ Opcode.PHI)
    (hjnonterm : ∀ inst ∈ jfront, isTerminator inst.opcode = false)
    (hjthread : execBodyThread jfront 0 { jumpTo joinL tsEndZ with instIdx := 0 } = some tsEndJ)
    (hjterm : stepInstBase jterm tsEndJ = ExecResult.Halt (haltState tsEndJ))
    -- join block: asm segment at THIS path's threaded plan state
    (hfrontJ : lgJ.map Prod.fst = jfront.zipIdx 0)
    (hreadyJ : BodyStepsReadyHSVP PJ lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgZ.flatMap (fun e => e.2)) eMZ2)
    (hspMZ2 : epsZ2.spilled = eMZ2)
    (hrelTransport2 : ∀ (asm' : AsmState), venomAsmRel lo epsZ2 tsEndZ asm' →
        venomAsmRel lo epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (hsdTransport2 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJ) epsZ2 tsEndZ asm' →
        StackDiscHS (totalGain lgJ + PJ) epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (htblockJ : asmBlockAt prog idxJ (executePlan ([StackOp.SOLabel jlab] ++ topsJ)))
    (hjbodyLenEq : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ topsJ)).length)
    (hjlt : idxJ + jbodyLen < prog.length)
    (hjget : prog.get ⟨idxJ + jbodyLen, hjlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : ebodyLen + 5 + (tbodyLenZ + 2) + (jbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  -- the Venom JNZ step: zero condition, fall through
  have heterm_step : stepInstBase eterm esEnd = ExecResult.OK (jumpTo ifZ esEnd) := by
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd = some cond from hcondv]
    split
    · rename_i h; exact absurd h (by rw [hcond]; decide)
    · rfl
  have heisterm : isTerminator eterm.opcode = true := by rw [hjopc]; decide
  -- link 0: entry segment
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfold1]; exact heblock
  have hebodyLenEqF : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfold1]; exact hebodyLenEq
  have hstkF : (lg1.foldl
        (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)).2.stack
      = base ++ [Operand.Var c] := by
    rw [hfold1]; exact hstk1
  have hcvalF : operandVal esEnd lo (Operand.Var c) = some cond := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv
  obtain ⟨asMid1, hrunE1, hrelMid1, hpcMid1, hsdMid1, hsvMid1⟩ :=
    hasm_regularHSVP_jnz_nottaken (totalGain lgZ + (totalGain lgJ + PJ)) hfront1 hready1 hesd0
      hesv0 hespM herel0 hethread heblockF hebodyLenEqF hstkF hcvalF hcond hpc1 hdup hpc2 hpushNz
      hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZl hoffZ_lk hoffZ hpc5 hjumpZ hidxZ_lk
  rw [hfold1] at hrelMid1 hsdMid1 hsvMid1
  -- link 1: mid-block JMP segment at the threaded state
  have htblockZ' : asmBlockAt prog asMid1.pc
      (executePlan ([StackOp.SOLabel tlabZ] ++ (lgZ.foldl
        (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)).1)) := by
    rw [hfoldZ, hpcMid1]; exact htblockZ
  have htbodyLenEqZ' : tbodyLenZ = (executePlan ([StackOp.SOLabel tlabZ] ++ (lgZ.foldl
        (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)).1)).length := by
    rw [hfoldZ]; exact htbodyLenEqZ
  have hpcJ1' : asMid1.pc + tbodyLenZ < prog.length := by rw [hpcMid1]; exact hpcJ1
  have hpushJ' : prog.get ⟨asMid1.pc + tbodyLenZ, hpcJ1'⟩
      = resolveInst lo (AsmInst.AsmPushLabel joinL) :=
    prog_get_transfer (by rw [hpcMid1]) hpushJ
  have hpcJ2' : asMid1.pc + tbodyLenZ + 1 < prog.length := by rw [hpcMid1]; exact hpcJ2
  have hjumpJ' : prog.get ⟨asMid1.pc + tbodyLenZ + 1, hpcJ2'⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hpcMid1]) hjumpJ
  obtain ⟨asMid2, hrunT2, hrelT2, hpcMid2, hsdT2, hsvT2⟩ :=
    hasm_regularHSVP_jmp (totalGain lgJ + PJ) hfrontZ hreadyZ
      (hsdTransport1 asMid1 hsdMid1) hsvMid1 hspM1 (hrelTransport1 asMid1 hrelMid1)
      htthreadZ htblockZ' htbodyLenEqZ' hpcJ1' hpushJ' hoffJ_lk hoffJ hpcJ2' hjumpJ' hidxJ_lk
  rw [hfoldZ] at hrelT2 hsdT2 hsvT2
  -- terminal: join-block STOP segment
  have htblockJ' : asmBlockAt prog asMid2.pc
      (executePlan ([StackOp.SOLabel jlab] ++ (lgJ.foldl
        (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsZ2)).1)) := by
    rw [hfoldJ, hpcMid2]; exact htblockJ
  have hjbodyLenEq' : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ (lgJ.foldl
        (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsZ2)).1)).length := by
    rw [hfoldJ]; exact hjbodyLenEq
  have hjlt' : asMid2.pc + jbodyLen < prog.length := by rw [hpcMid2]; exact hjlt
  have hjget' : prog.get ⟨asMid2.pc + jbodyLen, hjlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid2]) hjget
  have hasmJ := hasm_regularHSVP_stop PJ
    (budget := prog.length - (ebodyLen + 5) - (tbodyLenZ + 2))
    hfrontJ hreadyJ (hsdTransport2 asMid2 hsdT2) hsvT2 hspMZ2 (hrelTransport2 asMid2 hrelT2)
    hjthread htblockJ' hjbodyLenEq' hjlt' hjget' (by omega)
  -- compose the two links + terminal via the K-indexed scaffold
  exact hfsim_jmp_chain_of_runs 2
    (fun i => match i with | 0 => vs | 1 => jumpTo ifZ esEnd | _ => jumpTo joinL tsEndZ)
    (fun i => match i with | 0 => as | 1 => asMid1 | _ => asMid2)
    (fun i => match i with
      | 0 => prog.length
      | 1 => prog.length - (ebodyLen + 5)
      | _ => prog.length - (ebodyLen + 5) - (tbodyLenZ + 2))
    (fun i => match i with | 0 => entryBb | 1 => elseBb | _ => joinBb)
    (by intro i hi
        interval_cases i
        · exact hlk1
        · exact hlkZ2)
    (by intro i hi
        interval_cases i
        · exact ⟨efront, eterm, ehd, etl, esEnd, hebb, hecons, hephi, henonterm, hethread,
            heterm_step, heisterm, hnohaltE⟩
        · exact ⟨tfrontZ, ttermZ, thdZ, ttlZ, tsEndZ, htbbZ, htconsZ, htphiZ, htnontermZ,
            htthreadZ, httermstepZ, htistermZ, hnohaltZ⟩)
    (by intro i hi
        interval_cases i
        · show prog.length - (ebodyLen + 5) ≤ prog.length
          omega
        · show prog.length - (ebodyLen + 5) - (tbodyLenZ + 2) ≤ prog.length - (ebodyLen + 5)
          omega)
    (by intro i hi
        interval_cases i
        · show runAsm (prog.length - (prog.length - (ebodyLen + 5))) offsetToPc prog as
            = AsmResult.AsmOK asMid1
          rw [show prog.length - (prog.length - (ebodyLen + 5)) = ebodyLen + 5 from by omega]
          exact hrunE1
        · show runAsm ((prog.length - (ebodyLen + 5))
              - (prog.length - (ebodyLen + 5) - (tbodyLenZ + 2))) offsetToPc prog asMid1
            = AsmResult.AsmOK asMid2
          rw [show (prog.length - (ebodyLen + 5))
              - (prog.length - (ebodyLen + 5) - (tbodyLenZ + 2)) = tbodyLenZ + 2 from by omega]
          exact hrunT2)
    hlkJ
    (hterm_halt ctx joinBb jfront jterm jhd jtl (jumpTo joinL tsEndZ) tsEndJ (haltState tsEndJ)
      hjbb hjcons hjphi hjnonterm hjthread hjterm hasmJ)

/-- **Four-block DIAMOND with rejoin — the branching-CFG capstone**: entry (HSVP body + `JNZ`) →
    then/else arms (each HSVP body + `JMP joinL`) → ONE shared join block (HSVP body + STOP). The
    whole-function correspondence holds for ANY runtime condition value; the join block's code
    (`jlab`/`idxJ`) is fixed once, and each arm's hypotheses state its own fold (`topsJT`/`topsJZ`
    from its own threaded plan state) against that SAME code — the reconciliation obligation of a
    genuine join, surfaced explicitly (dischargeable when the arms' exits agree, or via the
    `reorderPlan_join_sim` reconciliation in the arms' tails). Entry budget `P` recovers each
    path's fuel via `totalGain lg_arm + (totalGain lgJ + PJ_arm) = P`. -/
theorem hfsim_regularHSVP_diamond_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gpT gpZ gpJ : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb thenBb elseBb joinBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfrontT : List Instruction} {ttermT thdT : Instruction} {ttlT : List Instruction} {tsEndT : VenomState}
    {tfrontZ : List Instruction} {ttermZ thdZ : Instruction} {ttlZ : List Instruction} {tsEndZ : VenomState}
    {jfront : List Instruction} {jterm jhd : Instruction} {jtl : List Instruction}
    {tsEndJT tsEndJZ : VenomState}
    {el tlabT tlabZ jlab ifNz ifZ joinL : String} {eS0 : List String}
    {eM0 eM1 eMT2 eMZ2 : AssocList Operand Nat}
    {lg1 lgT lgZ lgJ : List ((Instruction × Nat) × List String)}
    {eps0 eps1 epsT2 epsZ2 tpsJT tpsJZ : PlanState}
    {eops1 topsT topsZ topsJT topsJZ : List StackOp}
    {P PJT PJZ ebodyLen tbodyLenT tbodyLenZ jbodyLen offNz offZ offJ idxT idxZ idxJ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, epsT2))
    (hfoldZ : lgZ.foldl (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)
      = (topsZ, epsZ2))
    (hfoldJT : lgJ.foldl (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsT2)
      = (topsJT, tpsJT))
    (hfoldJZ : lgJ.foldl (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsZ2)
      = (topsJZ, tpsJZ))
    (hPT : totalGain lgT + (totalGain lgJ + PJT) = P)
    (hPZ : totalGain lgZ + (totalGain lgJ + PJZ) = P)
    -- entry block: Venom structure, JNZ with an ARBITRARY condition value
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hnohaltE : esEnd.halted = false)
    -- entry block: asm segment at the shared budget P
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP P lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + P) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as.pc + ebodyLen + 3 < prog.length)
    (hpushZl : prog.get ⟨as.pc + ebodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as.pc + ebodyLen + 4 < prog.length)
    (hjumpZ : prog.get ⟨as.pc + ebodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxT_lk : AssocList.lookup Nat Nat offsetToPc offNz = some idxT)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    -- THEN arm: Venom + asm
    (hlkT : lookupBlock (jumpTo ifNz esEnd).currentBb fn.blocks = some thenBb)
    (htbbT : thenBb.instructions = tfrontT ++ [ttermT])
    (htconsT : tfrontT ++ [ttermT] = thdT :: ttlT)
    (htphiT : thdT.opcode ≠ Opcode.PHI)
    (htnontermT : ∀ inst ∈ tfrontT, isTerminator inst.opcode = false)
    (htthreadT : execBodyThread tfrontT 0 { jumpTo ifNz esEnd with instIdx := 0 } = some tsEndT)
    (httermstepT : stepInstBase ttermT tsEndT = ExecResult.OK (jumpTo joinL tsEndT))
    (htistermT : isTerminator ttermT.opcode = true)
    (hnohaltT : tsEndT.halted = false)
    (hfrontT : lgT.map Prod.fst = tfrontT.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP (totalGain lgJ + PJT) lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransportT : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (hsdTransportT : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (htblockT : asmBlockAt prog idxT (executePlan ([StackOp.SOLabel tlabT] ++ topsT)))
    (htbodyLenEqT : tbodyLenT = (executePlan ([StackOp.SOLabel tlabT] ++ topsT)).length)
    (hpcJT1 : idxT + tbodyLenT < prog.length)
    (hpushJT : prog.get ⟨idxT + tbodyLenT, hpcJT1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hoffJ_lk : AssocList.lookup String Nat lo joinL = some offJ) (hoffJ : offJ < 2 ^ 256)
    (hpcJT2 : idxT + tbodyLenT + 1 < prog.length)
    (hjumpJT : prog.get ⟨idxT + tbodyLenT + 1, hpcJT2⟩ = AsmInst.AsmOp "JUMP")
    (hidxJ_lk : AssocList.lookup Nat Nat offsetToPc offJ = some idxJ)
    -- ELSE arm: Venom + asm
    (hlkZ2 : lookupBlock (jumpTo ifZ esEnd).currentBb fn.blocks = some elseBb)
    (htbbZ : elseBb.instructions = tfrontZ ++ [ttermZ])
    (htconsZ : tfrontZ ++ [ttermZ] = thdZ :: ttlZ)
    (htphiZ : thdZ.opcode ≠ Opcode.PHI)
    (htnontermZ : ∀ inst ∈ tfrontZ, isTerminator inst.opcode = false)
    (htthreadZ : execBodyThread tfrontZ 0 { jumpTo ifZ esEnd with instIdx := 0 } = some tsEndZ)
    (httermstepZ : stepInstBase ttermZ tsEndZ = ExecResult.OK (jumpTo joinL tsEndZ))
    (htistermZ : isTerminator ttermZ.opcode = true)
    (hnohaltZ : tsEndZ.halted = false)
    (hfrontZ : lgZ.map Prod.fst = tfrontZ.zipIdx 0)
    (hreadyZ : BodyStepsReadyHSVP (totalGain lgJ + PJZ) lo offsetToPc prog gpZ lgZ
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hrelTransportZ : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (hsdTransportZ : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (htblockZ : asmBlockAt prog idxZ (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)))
    (htbodyLenEqZ : tbodyLenZ = (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)).length)
    (hpcJZ1 : idxZ + tbodyLenZ < prog.length)
    (hpushJZ : prog.get ⟨idxZ + tbodyLenZ, hpcJZ1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hpcJZ2 : idxZ + tbodyLenZ + 1 < prog.length)
    (hjumpJZ : prog.get ⟨idxZ + tbodyLenZ + 1, hpcJZ2⟩ = AsmInst.AsmOp "JUMP")
    -- the SHARED join block: Venom structure per arm state, STOP terminal
    (hjbb : joinBb.instructions = jfront ++ [jterm])
    (hjcons : jfront ++ [jterm] = jhd :: jtl)
    (hjphi : jhd.opcode ≠ Opcode.PHI)
    (hjnonterm : ∀ inst ∈ jfront, isTerminator inst.opcode = false)
    (hlkJT : lookupBlock (jumpTo joinL tsEndT).currentBb fn.blocks = some joinBb)
    (hjthreadT : execBodyThread jfront 0 { jumpTo joinL tsEndT with instIdx := 0 } = some tsEndJT)
    (hjtermT : stepInstBase jterm tsEndJT = ExecResult.Halt (haltState tsEndJT))
    (hlkJZ : lookupBlock (jumpTo joinL tsEndZ).currentBb fn.blocks = some joinBb)
    (hjthreadZ : execBodyThread jfront 0 { jumpTo joinL tsEndZ with instIdx := 0 } = some tsEndJZ)
    (hjtermZ : stepInstBase jterm tsEndJZ = ExecResult.Halt (haltState tsEndJZ))
    -- the SHARED join code at idxJ, stated against EACH arm's threaded plan state
    (hfrontJ : lgJ.map Prod.fst = jfront.zipIdx 0)
    (hreadyJT : BodyStepsReadyHSVP PJT lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgT.flatMap (fun e => e.2)) eMT2)
    (hspMT2 : epsT2.spilled = eMT2)
    (hrelTransportJT : ∀ (asm' : AsmState), venomAsmRel lo epsT2 tsEndT asm' →
        venomAsmRel lo epsT2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (hsdTransportJT : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJT) epsT2 tsEndT asm' →
        StackDiscHS (totalGain lgJ + PJT) epsT2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (htblockJT : asmBlockAt prog idxJ (executePlan ([StackOp.SOLabel jlab] ++ topsJT)))
    (hjbodyLenEqT : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ topsJT)).length)
    (hreadyJZ : BodyStepsReadyHSVP PJZ lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgZ.flatMap (fun e => e.2)) eMZ2)
    (hspMZ2 : epsZ2.spilled = eMZ2)
    (hrelTransportJZ : ∀ (asm' : AsmState), venomAsmRel lo epsZ2 tsEndZ asm' →
        venomAsmRel lo epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (hsdTransportJZ : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJZ) epsZ2 tsEndZ asm' →
        StackDiscHS (totalGain lgJ + PJZ) epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (htblockJZ : asmBlockAt prog idxJ (executePlan ([StackOp.SOLabel jlab] ++ topsJZ)))
    (hjbodyLenEqZ : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ topsJZ)).length)
    (hjlt : idxJ + jbodyLen < prog.length)
    (hjget : prog.get ⟨idxJ + jbodyLen, hjlt⟩ = AsmInst.AsmOp "STOP")
    (hbudgetT : ebodyLen + 3 + (tbodyLenT + 2) + (jbodyLen + 1) ≤ prog.length)
    (hbudgetZ : ebodyLen + 5 + (tbodyLenZ + 2) + (jbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  by_cases hc : cond = EvmYul.UInt256.ofNat 0
  · exact hfsim_regularHSVP_jnz_nottaken_jmp_stop hfold1 hfoldZ hfoldJZ hlk1 hebb hecons hephi
      henonterm hethread hjopc hjops hcondv hc hnohaltE hfront1
      (by rw [hPZ]; exact hready1) (by rw [hPZ]; exact hesd0) hesv0 hespM herel0 heblock
      hebodyLenEq hstk1 hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZl
      hoffZ_lk hoffZ hpc5 hjumpZ hidxZ_lk hlkZ2 htbbZ htconsZ htphiZ htnontermZ htthreadZ
      httermstepZ htistermZ hnohaltZ hfrontZ hreadyZ hspM1 hrelTransportZ
      (by rw [hPZ]; exact hsdTransportZ) htblockZ htbodyLenEqZ hpcJZ1 hpushJZ hoffJ_lk hoffJ
      hpcJZ2 hjumpJZ hidxJ_lk hlkJZ hjbb hjcons hjphi hjnonterm hjthreadZ hjtermZ hfrontJ
      hreadyJZ hspMZ2 hrelTransportJZ hsdTransportJZ htblockJZ hjbodyLenEqZ hjlt hjget hbudgetZ
  · exact hfsim_regularHSVP_jnz_taken_jmp_stop hfold1 hfoldT hfoldJT hlk1 hebb hecons hephi
      henonterm hethread hjopc hjops hcondv hc hnohaltE hfront1
      (by rw [hPT]; exact hready1) (by rw [hPT]; exact hesd0) hesv0 hespM herel0 heblock
      hebodyLenEq hstk1 hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hidxT_lk
      hlkT htbbT htconsT htphiT htnontermT htthreadT httermstepT htistermT hnohaltT hfrontT
      hreadyT hspM1 hrelTransportT (by rw [hPT]; exact hsdTransportT) htblockT htbodyLenEqT
      hpcJT1 hpushJT hoffJ_lk hoffJ hpcJT2 hjumpJT hidxJ_lk hlkJT hjbb hjcons hjphi hjnonterm
      hjthreadT hjtermT hfrontJ hreadyJT hspMT2 hrelTransportJT hsdTransportJT htblockJT
      hjbodyLenEqT hjlt hjget hbudgetT

/-- **Generic discharge of the diamond join code-equality obligations**: when the two arms
    exit at the SAME plan state (`hexiteq`), plan-generator determinism makes the two join
    folds literally equal — the join code facts (`htblockJ*`, `hjbodyLenEq*`, `hspM*2`) are
    stated ONCE and the dual reconciliation obligations of `hfsim_regularHSVP_diamond_stop`
    collapse. The "dischargeable when the arms' exits agree" claim, landed. -/
theorem hfsim_regularHSVP_diamond_stop_eq_exits
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gp1 gpT gpZ gpJ : Instruction × Nat → PlanState → List StackOp × PlanState}
    {entryBb thenBb elseBb joinBb : BasicBlock}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    {tfrontT : List Instruction} {ttermT thdT : Instruction} {ttlT : List Instruction} {tsEndT : VenomState}
    {tfrontZ : List Instruction} {ttermZ thdZ : Instruction} {ttlZ : List Instruction} {tsEndZ : VenomState}
    {jfront : List Instruction} {jterm jhd : Instruction} {jtl : List Instruction}
    {tsEndJT tsEndJZ : VenomState}
    {el tlabT tlabZ jlab ifNz ifZ joinL : String} {eS0 : List String}
    {eM0 eM1 eMZ2 : AssocList Operand Nat}
    {lg1 lgT lgZ lgJ : List ((Instruction × Nat) × List String)}
    {eps0 eps1 epsT2 epsZ2 tpsJZ : PlanState}
    {eops1 topsT topsZ topsJZ : List StackOp}
    {P PJT PJZ ebodyLen tbodyLenT tbodyLenZ jbodyLen offNz offZ offJ idxT idxZ idxJ : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hfold1 : lg1.foldl (fun acc x => (acc.1 ++ (gp1 x.1 acc.2).1, (gp1 x.1 acc.2).2)) ([], eps0)
      = (eops1, eps1))
    (hfoldT : lgT.foldl (fun acc x => (acc.1 ++ (gpT x.1 acc.2).1, (gpT x.1 acc.2).2)) ([], eps1)
      = (topsT, epsT2))
    (hfoldZ : lgZ.foldl (fun acc x => (acc.1 ++ (gpZ x.1 acc.2).1, (gpZ x.1 acc.2).2)) ([], eps1)
      = (topsZ, epsZ2))
    (hexiteq : epsT2 = epsZ2)
    (hfoldJZ : lgJ.foldl (fun acc x => (acc.1 ++ (gpJ x.1 acc.2).1, (gpJ x.1 acc.2).2)) ([], epsZ2)
      = (topsJZ, tpsJZ))
    (hPT : totalGain lgT + (totalGain lgJ + PJT) = P)
    (hPZ : totalGain lgZ + (totalGain lgJ + PJZ) = P)
    -- entry block: Venom structure, JNZ with an ARBITRARY condition value
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (hjopc : eterm.opcode = Opcode.JNZ)
    (hjops : eterm.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : lookupVar c esEnd = some cond)
    (hnohaltE : esEnd.halted = false)
    -- entry block: asm segment at the shared budget P
    (hfront1 : lg1.map Prod.fst = efront.zipIdx 0)
    (hready1 : BodyStepsReadyHSVP P lo offsetToPc prog gp1 lg1 eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lg1 + P) eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (heblock : asmBlockAt prog as.pc (executePlan ([StackOp.SOLabel el] ++ eops1)))
    (hebodyLenEq : ebodyLen = (executePlan ([StackOp.SOLabel el] ++ eops1)).length)
    (hstk1 : eps1.stack = base ++ [Operand.Var c])
    (hpc1 : as.pc + ebodyLen < prog.length)
    (hdup : prog.get ⟨as.pc + ebodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : as.pc + ebodyLen + 1 < prog.length)
    (hpushNz : prog.get ⟨as.pc + ebodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel ifNz))
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hpc3 : as.pc + ebodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨as.pc + ebodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : as.pc + ebodyLen + 3 < prog.length)
    (hpushZl : prog.get ⟨as.pc + ebodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hpc5 : as.pc + ebodyLen + 4 < prog.length)
    (hjumpZ : prog.get ⟨as.pc + ebodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxT_lk : AssocList.lookup Nat Nat offsetToPc offNz = some idxT)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    -- THEN arm: Venom + asm
    (hlkT : lookupBlock (jumpTo ifNz esEnd).currentBb fn.blocks = some thenBb)
    (htbbT : thenBb.instructions = tfrontT ++ [ttermT])
    (htconsT : tfrontT ++ [ttermT] = thdT :: ttlT)
    (htphiT : thdT.opcode ≠ Opcode.PHI)
    (htnontermT : ∀ inst ∈ tfrontT, isTerminator inst.opcode = false)
    (htthreadT : execBodyThread tfrontT 0 { jumpTo ifNz esEnd with instIdx := 0 } = some tsEndT)
    (httermstepT : stepInstBase ttermT tsEndT = ExecResult.OK (jumpTo joinL tsEndT))
    (htistermT : isTerminator ttermT.opcode = true)
    (hnohaltT : tsEndT.halted = false)
    (hfrontT : lgT.map Prod.fst = tfrontT.zipIdx 0)
    (hreadyT : BodyStepsReadyHSVP (totalGain lgJ + PJT) lo offsetToPc prog gpT lgT
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hspM1 : eps1.spilled = eM1)
    (hrelTransportT : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (hsdTransportT : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifNz esEnd with instIdx := 0 } asm')
    (htblockT : asmBlockAt prog idxT (executePlan ([StackOp.SOLabel tlabT] ++ topsT)))
    (htbodyLenEqT : tbodyLenT = (executePlan ([StackOp.SOLabel tlabT] ++ topsT)).length)
    (hpcJT1 : idxT + tbodyLenT < prog.length)
    (hpushJT : prog.get ⟨idxT + tbodyLenT, hpcJT1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hoffJ_lk : AssocList.lookup String Nat lo joinL = some offJ) (hoffJ : offJ < 2 ^ 256)
    (hpcJT2 : idxT + tbodyLenT + 1 < prog.length)
    (hjumpJT : prog.get ⟨idxT + tbodyLenT + 1, hpcJT2⟩ = AsmInst.AsmOp "JUMP")
    (hidxJ_lk : AssocList.lookup Nat Nat offsetToPc offJ = some idxJ)
    -- ELSE arm: Venom + asm
    (hlkZ2 : lookupBlock (jumpTo ifZ esEnd).currentBb fn.blocks = some elseBb)
    (htbbZ : elseBb.instructions = tfrontZ ++ [ttermZ])
    (htconsZ : tfrontZ ++ [ttermZ] = thdZ :: ttlZ)
    (htphiZ : thdZ.opcode ≠ Opcode.PHI)
    (htnontermZ : ∀ inst ∈ tfrontZ, isTerminator inst.opcode = false)
    (htthreadZ : execBodyThread tfrontZ 0 { jumpTo ifZ esEnd with instIdx := 0 } = some tsEndZ)
    (httermstepZ : stepInstBase ttermZ tsEndZ = ExecResult.OK (jumpTo joinL tsEndZ))
    (htistermZ : isTerminator ttermZ.opcode = true)
    (hnohaltZ : tsEndZ.halted = false)
    (hfrontZ : lgZ.map Prod.fst = tfrontZ.zipIdx 0)
    (hreadyZ : BodyStepsReadyHSVP (totalGain lgJ + PJZ) lo offsetToPc prog gpZ lgZ
      (eS0 ++ lg1.flatMap (fun e => e.2)) eM1)
    (hrelTransportZ : ∀ (asm' : AsmState), venomAsmRel lo eps1 esEnd asm' →
        venomAsmRel lo eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (hsdTransportZ : ∀ (asm' : AsmState), StackDiscHS P eps1 esEnd asm' →
        StackDiscHS P eps1 { jumpTo ifZ esEnd with instIdx := 0 } asm')
    (htblockZ : asmBlockAt prog idxZ (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)))
    (htbodyLenEqZ : tbodyLenZ = (executePlan ([StackOp.SOLabel tlabZ] ++ topsZ)).length)
    (hpcJZ1 : idxZ + tbodyLenZ < prog.length)
    (hpushJZ : prog.get ⟨idxZ + tbodyLenZ, hpcJZ1⟩ = resolveInst lo (AsmInst.AsmPushLabel joinL))
    (hpcJZ2 : idxZ + tbodyLenZ + 1 < prog.length)
    (hjumpJZ : prog.get ⟨idxZ + tbodyLenZ + 1, hpcJZ2⟩ = AsmInst.AsmOp "JUMP")
    -- the SHARED join block: Venom structure per arm state, STOP terminal
    (hjbb : joinBb.instructions = jfront ++ [jterm])
    (hjcons : jfront ++ [jterm] = jhd :: jtl)
    (hjphi : jhd.opcode ≠ Opcode.PHI)
    (hjnonterm : ∀ inst ∈ jfront, isTerminator inst.opcode = false)
    (hlkJT : lookupBlock (jumpTo joinL tsEndT).currentBb fn.blocks = some joinBb)
    (hjthreadT : execBodyThread jfront 0 { jumpTo joinL tsEndT with instIdx := 0 } = some tsEndJT)
    (hjtermT : stepInstBase jterm tsEndJT = ExecResult.Halt (haltState tsEndJT))
    (hlkJZ : lookupBlock (jumpTo joinL tsEndZ).currentBb fn.blocks = some joinBb)
    (hjthreadZ : execBodyThread jfront 0 { jumpTo joinL tsEndZ with instIdx := 0 } = some tsEndJZ)
    (hjtermZ : stepInstBase jterm tsEndJZ = ExecResult.Halt (haltState tsEndJZ))
    -- the SHARED join code at idxJ, stated against EACH arm's threaded plan state
    (hfrontJ : lgJ.map Prod.fst = jfront.zipIdx 0)
    (hreadyJT : BodyStepsReadyHSVP PJT lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgT.flatMap (fun e => e.2)) eMZ2)
    (hrelTransportJT : ∀ (asm' : AsmState), venomAsmRel lo epsZ2 tsEndT asm' →
        venomAsmRel lo epsZ2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (hsdTransportJT : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJT) epsZ2 tsEndT asm' →
        StackDiscHS (totalGain lgJ + PJT) epsZ2 { jumpTo joinL tsEndT with instIdx := 0 } asm')
    (hreadyJZ : BodyStepsReadyHSVP PJZ lo offsetToPc prog gpJ lgJ
      ((eS0 ++ lg1.flatMap (fun e => e.2)) ++ lgZ.flatMap (fun e => e.2)) eMZ2)
    (hspMZ2 : epsZ2.spilled = eMZ2)
    (hrelTransportJZ : ∀ (asm' : AsmState), venomAsmRel lo epsZ2 tsEndZ asm' →
        venomAsmRel lo epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (hsdTransportJZ : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgJ + PJZ) epsZ2 tsEndZ asm' →
        StackDiscHS (totalGain lgJ + PJZ) epsZ2 { jumpTo joinL tsEndZ with instIdx := 0 } asm')
    (htblockJZ : asmBlockAt prog idxJ (executePlan ([StackOp.SOLabel jlab] ++ topsJZ)))
    (hjbodyLenEqZ : jbodyLen = (executePlan ([StackOp.SOLabel jlab] ++ topsJZ)).length)
    (hjlt : idxJ + jbodyLen < prog.length)
    (hjget : prog.get ⟨idxJ + jbodyLen, hjlt⟩ = AsmInst.AsmOp "STOP")
    (hbudgetT : ebodyLen + 3 + (tbodyLenT + 2) + (jbodyLen + 1) ≤ prog.length)
    (hbudgetZ : ebodyLen + 5 + (tbodyLenZ + 2) + (jbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  subst hexiteq
  exact hfsim_regularHSVP_diamond_stop hfold1 hfoldT hfoldZ hfoldJZ hfoldJZ hPT hPZ hlk1 hebb
    hecons hephi henonterm hethread hjopc hjops hcondv hnohaltE hfront1 hready1 hesd0 hesv0
    hespM herel0 heblock hebodyLenEq hstk1 hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi
    hpc4 hpushZl hoffZ_lk hoffZ hpc5 hjumpZ hidxT_lk hidxZ_lk hlkT htbbT htconsT htphiT
    htnontermT htthreadT httermstepT htistermT hnohaltT hfrontT hreadyT hspM1 hrelTransportT
    hsdTransportT htblockT htbodyLenEqT hpcJT1 hpushJT hoffJ_lk hoffJ hpcJT2 hjumpJT hidxJ_lk
    hlkZ2 htbbZ htconsZ htphiZ htnontermZ htthreadZ httermstepZ htistermZ hnohaltZ hfrontZ
    hreadyZ hrelTransportZ hsdTransportZ htblockZ htbodyLenEqZ hpcJZ1 hpushJZ hpcJZ2 hjumpJZ
    hjbb hjcons hjphi hjnonterm hlkJT hjthreadT hjtermT hlkJZ hjthreadZ hjtermZ hfrontJ
    hreadyJT hspMZ2 hrelTransportJT hsdTransportJT htblockJZ hjbodyLenEqZ hreadyJZ hspMZ2
    hrelTransportJZ hsdTransportJZ htblockJZ hjbodyLenEqZ hjlt hjget hbudgetT hbudgetZ

/-- **CYCLIC control flow: a loop body visited twice, then exit** — the first loop-shaped
    whole-function correspondence. One physical loop block (`loopL`, code at `idxL`, ending in
    `JNZ c loopL exitL`) appears TWICE in the chain: visit 1 takes the back-edge (`cond0 ≠ 0`,
    the `JUMPI` jumps back to `idxL` itself), visit 2 falls through (`cond1 = 0`) to the halting
    exit block. The K-indexed scaffold happily re-enters the same block (`B 0 = B 1 = loopBb`)
    at strictly decreasing asm budgets; the SAME physical `DUP1 ; push loopL ; JUMPI ;
    push exitL ; JUMP` tail serves both visits (taken uses the first three, fall-through all
    five). Per-visit plan folds (`lops1`/`lops2`) must emit same-length code (`lbodyLen`) — the
    loop-invariance obligation, explicit. -/
theorem hfsim_regularHSVP_loop_twice_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gpL gpE : Instruction × Nat → PlanState → List StackOp × PlanState}
    {loopBb exitBb : BasicBlock}
    {lfront : List Instruction} {lterm lhd : Instruction} {ltl : List Instruction}
    {esEnd0 esEnd1 : VenomState}
    {xfront : List Instruction} {xterm xhd : Instruction} {xtl : List Instruction} {tsEndX : VenomState}
    {llab xlab loopL exitL : String} {eS0 : List String}
    {eM0 eM1 eML2 : AssocList Operand Nat}
    {lgL lgE : List ((Instruction × Nat) × List String)}
    {eps0 epsL1 epsL2 xps : PlanState} {lops1 lops2 xops : List StackOp}
    {PE lbodyLen xbodyLen offL offE idxL idxE : Nat}
    {c : String} {cond0 cond1 : bytes32} {base1 base2 : List Operand}
    (hfoldL1 : lgL.foldl (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], eps0)
      = (lops1, epsL1))
    (hfoldL2 : lgL.foldl (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL1)
      = (lops2, epsL2))
    (hfoldE : lgE.foldl (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL2)
      = (xops, xps))
    -- the loop block: Venom structure (shared by both visits), JNZ back-edge terminator
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some loopBb)
    (hlbb : loopBb.instructions = lfront ++ [lterm])
    (hlcons : lfront ++ [lterm] = lhd :: ltl)
    (hlphi : lhd.opcode ≠ Opcode.PHI)
    (hlnonterm : ∀ inst ∈ lfront, isTerminator inst.opcode = false)
    (hjopc : lterm.opcode = Opcode.JNZ)
    (hjops : lterm.operands = [Operand.Var c, Operand.Label loopL, Operand.Label exitL])
    -- visit 1: body thread + non-zero condition (back-edge taken)
    (hethread0 : execBodyThread lfront 0 { vs with instIdx := 0 } = some esEnd0)
    (hcondv0 : lookupVar c esEnd0 = some cond0)
    (hcond0 : cond0 ≠ EvmYul.UInt256.ofNat 0)
    (hnohalt0 : esEnd0.halted = false)
    -- visit 2 (re-entry): body thread + zero condition (fall through to exit)
    (hlkL2 : lookupBlock (jumpTo loopL esEnd0).currentBb fn.blocks = some loopBb)
    (hethread1 : execBodyThread lfront 0 { jumpTo loopL esEnd0 with instIdx := 0 } = some esEnd1)
    (hcondv1 : lookupVar c esEnd1 = some cond1)
    (hcond1 : cond1 = EvmYul.UInt256.ofNat 0)
    (hnohalt1 : esEnd1.halted = false)
    -- the loop block: asm segment facts (ONE physical code section at idxL)
    (haspc : as.pc = idxL)
    (hfrontL : lgL.map Prod.fst = lfront.zipIdx 0)
    (hreadyL1 : BodyStepsReadyHSVP (totalGain lgL + (totalGain lgE + PE)) lo offsetToPc prog
      gpL lgL eS0 eM0)
    (hesd0 : StackDiscHS (totalGain lgL + (totalGain lgL + (totalGain lgE + PE)))
      eps0 { vs with instIdx := 0 } as)
    (hesv0 : StackPerm eS0 eps0) (hespM : eps0.spilled = eM0)
    (herel0 : venomAsmRel lo eps0 { vs with instIdx := 0 } as)
    (hlblock1 : asmBlockAt prog idxL (executePlan ([StackOp.SOLabel llab] ++ lops1)))
    (hlbodyLenEq1 : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ lops1)).length)
    (hstkL1 : epsL1.stack = base1 ++ [Operand.Var c])
    -- visit 2 segment facts at the SAME code section
    (hreadyL2 : BodyStepsReadyHSVP (totalGain lgE + PE) lo offsetToPc prog gpL lgL
      (eS0 ++ lgL.flatMap (fun e => e.2)) eM1)
    (hspM1 : epsL1.spilled = eM1)
    (hrelTransport1 : ∀ (asm' : AsmState), venomAsmRel lo epsL1 esEnd0 asm' →
        venomAsmRel lo epsL1 { jumpTo loopL esEnd0 with instIdx := 0 } asm')
    (hsdTransport1 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgL + (totalGain lgE + PE)) epsL1 esEnd0 asm' →
        StackDiscHS (totalGain lgL + (totalGain lgE + PE)) epsL1
          { jumpTo loopL esEnd0 with instIdx := 0 } asm')
    (hlblock2 : asmBlockAt prog idxL (executePlan ([StackOp.SOLabel llab] ++ lops2)))
    (hlbodyLenEq2 : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ lops2)).length)
    (hstkL2 : epsL2.stack = base2 ++ [Operand.Var c])
    -- the shared conditional tail (both visits run the same instructions)
    (hpc1 : idxL + lbodyLen < prog.length)
    (hdup : prog.get ⟨idxL + lbodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : idxL + lbodyLen + 1 < prog.length)
    (hpushL : prog.get ⟨idxL + lbodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel loopL))
    (hoffL_lk : AssocList.lookup String Nat lo loopL = some offL) (hoffL : offL < 2 ^ 256)
    (hpc3 : idxL + lbodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨idxL + lbodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : idxL + lbodyLen + 3 < prog.length)
    (hpushE : prog.get ⟨idxL + lbodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel exitL))
    (hoffE_lk : AssocList.lookup String Nat lo exitL = some offE) (hoffE : offE < 2 ^ 256)
    (hpc5 : idxL + lbodyLen + 4 < prog.length)
    (hjumpE : prog.get ⟨idxL + lbodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxL_lk : AssocList.lookup Nat Nat offsetToPc offL = some idxL)
    (hidxE_lk : AssocList.lookup Nat Nat offsetToPc offE = some idxE)
    -- the exit block: Venom structure, STOP terminal
    (hlkE : lookupBlock (jumpTo exitL esEnd1).currentBb fn.blocks = some exitBb)
    (hxbb : exitBb.instructions = xfront ++ [xterm])
    (hxcons : xfront ++ [xterm] = xhd :: xtl)
    (hxphi : xhd.opcode ≠ Opcode.PHI)
    (hxnonterm : ∀ inst ∈ xfront, isTerminator inst.opcode = false)
    (hxthread : execBodyThread xfront 0 { jumpTo exitL esEnd1 with instIdx := 0 } = some tsEndX)
    (hxterm : stepInstBase xterm tsEndX = ExecResult.Halt (haltState tsEndX))
    -- the exit block: asm segment
    (hfrontE : lgE.map Prod.fst = xfront.zipIdx 0)
    (hreadyE : BodyStepsReadyHSVP PE lo offsetToPc prog gpE lgE
      ((eS0 ++ lgL.flatMap (fun e => e.2)) ++ lgL.flatMap (fun e => e.2)) eML2)
    (hspML2 : epsL2.spilled = eML2)
    (hrelTransport2 : ∀ (asm' : AsmState), venomAsmRel lo epsL2 esEnd1 asm' →
        venomAsmRel lo epsL2 { jumpTo exitL esEnd1 with instIdx := 0 } asm')
    (hsdTransport2 : ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgE + PE) epsL2 esEnd1 asm' →
        StackDiscHS (totalGain lgE + PE) epsL2 { jumpTo exitL esEnd1 with instIdx := 0 } asm')
    (hxblock : asmBlockAt prog idxE (executePlan ([StackOp.SOLabel xlab] ++ xops)))
    (hxbodyLenEq : xbodyLen = (executePlan ([StackOp.SOLabel xlab] ++ xops)).length)
    (hxlt : idxE + xbodyLen < prog.length)
    (hxget : prog.get ⟨idxE + xbodyLen, hxlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : lbodyLen + 3 + (lbodyLen + 5) + (xbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hlisterm : isTerminator lterm.opcode = true := by rw [hjopc]; decide
  -- visit 1 Venom step: back-edge taken
  have hstep0 : stepInstBase lterm esEnd0 = ExecResult.OK (jumpTo loopL esEnd0) := by
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd0 = some cond0 from hcondv0]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcond0) h
  -- visit 2 Venom step: fall through to the exit
  have hstep1 : stepInstBase lterm esEnd1 = ExecResult.OK (jumpTo exitL esEnd1) := by
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) esEnd1 = some cond1 from hcondv1]
    split
    · rename_i h; exact absurd h (by rw [hcond1]; decide)
    · rfl
  -- visit 1: taken segment (jumps back to idxL)
  have heblockF : asmBlockAt prog as.pc
      (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], eps0)).1)) := by
    rw [hfoldL1, haspc]; exact hlblock1
  have hebodyLenEqF : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], eps0)).1)).length := by
    rw [hfoldL1]; exact hlbodyLenEq1
  have hstkF1 : (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], eps0)).2.stack
      = base1 ++ [Operand.Var c] := by
    rw [hfoldL1]; exact hstkL1
  have hcvalF0 : operandVal esEnd0 lo (Operand.Var c) = some cond0 := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv0
  have hpc1' : as.pc + lbodyLen < prog.length := by rw [haspc]; exact hpc1
  have hdup' : prog.get ⟨as.pc + lbodyLen, hpc1'⟩ = AsmInst.AsmOp "DUP1" :=
    prog_get_transfer (by rw [haspc]) hdup
  have hpc2' : as.pc + lbodyLen + 1 < prog.length := by rw [haspc]; exact hpc2
  have hpushL' : prog.get ⟨as.pc + lbodyLen + 1, hpc2'⟩
      = resolveInst lo (AsmInst.AsmPushLabel loopL) :=
    prog_get_transfer (by rw [haspc]) hpushL
  have hpc3' : as.pc + lbodyLen + 2 < prog.length := by rw [haspc]; exact hpc3
  have hjumpi' : prog.get ⟨as.pc + lbodyLen + 2, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [haspc]) hjumpi
  obtain ⟨asMid1, hrunE1, hrelMid1, hpcMid1, hsdMid1, hsvMid1⟩ :=
    hasm_regularHSVP_jnz_taken (totalGain lgL + (totalGain lgE + PE)) hfrontL hreadyL1 hesd0
      hesv0 hespM herel0 hethread0 heblockF hebodyLenEqF hstkF1 hcvalF0 hcond0 hpc1' hdup'
      hpc2' hpushL' hoffL_lk hoffL hpc3' hjumpi' hidxL_lk
  rw [hfoldL1] at hrelMid1 hsdMid1 hsvMid1
  -- visit 2: not-taken segment from the SAME code section (asMid1.pc = idxL again)
  have hlblock2' : asmBlockAt prog asMid1.pc
      (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL1)).1)) := by
    rw [hfoldL2, hpcMid1]; exact hlblock2
  have hlbodyLenEq2' : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL1)).1)).length := by
    rw [hfoldL2]; exact hlbodyLenEq2
  have hstkF2 : (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL1)).2.stack
      = base2 ++ [Operand.Var c] := by
    rw [hfoldL2]; exact hstkL2
  have hcvalF1 : operandVal esEnd1 lo (Operand.Var c) = some cond1 := by
    rw [operandVal_var_eq_lookupVar]; exact hcondv1
  have hpcV1 : asMid1.pc + lbodyLen < prog.length := by rw [hpcMid1]; exact hpc1
  have hdupV : prog.get ⟨asMid1.pc + lbodyLen, hpcV1⟩ = AsmInst.AsmOp "DUP1" :=
    prog_get_transfer (by rw [hpcMid1]) hdup
  have hpcV2 : asMid1.pc + lbodyLen + 1 < prog.length := by rw [hpcMid1]; exact hpc2
  have hpushLV : prog.get ⟨asMid1.pc + lbodyLen + 1, hpcV2⟩
      = resolveInst lo (AsmInst.AsmPushLabel loopL) :=
    prog_get_transfer (by rw [hpcMid1]) hpushL
  have hpcV3 : asMid1.pc + lbodyLen + 2 < prog.length := by rw [hpcMid1]; exact hpc3
  have hjumpiV : prog.get ⟨asMid1.pc + lbodyLen + 2, hpcV3⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hpcMid1]) hjumpi
  have hpcV4 : asMid1.pc + lbodyLen + 3 < prog.length := by rw [hpcMid1]; exact hpc4
  have hpushEV : prog.get ⟨asMid1.pc + lbodyLen + 3, hpcV4⟩
      = resolveInst lo (AsmInst.AsmPushLabel exitL) :=
    prog_get_transfer (by rw [hpcMid1]) hpushE
  have hpcV5 : asMid1.pc + lbodyLen + 4 < prog.length := by rw [hpcMid1]; exact hpc5
  have hjumpEV : prog.get ⟨asMid1.pc + lbodyLen + 4, hpcV5⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hpcMid1]) hjumpE
  obtain ⟨asMid2, hrunV2, hrelV2, hpcMid2, hsdV2, hsvV2⟩ :=
    hasm_regularHSVP_jnz_nottaken (totalGain lgE + PE) hfrontL hreadyL2
      (hsdTransport1 asMid1 hsdMid1) hsvMid1 hspM1 (hrelTransport1 asMid1 hrelMid1)
      hethread1 hlblock2' hlbodyLenEq2' hstkF2 hcvalF1 hcond1 hpcV1 hdupV hpcV2 hpushLV
      hoffL_lk hoffL hpcV3 hjumpiV hpcV4 hpushEV hoffE_lk hoffE hpcV5 hjumpEV hidxE_lk
  rw [hfoldL2] at hrelV2 hsdV2 hsvV2
  -- terminal: exit-block STOP segment
  have hxblock' : asmBlockAt prog asMid2.pc
      (executePlan ([StackOp.SOLabel xlab] ++ (lgE.foldl
        (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL2)).1)) := by
    rw [hfoldE, hpcMid2]; exact hxblock
  have hxbodyLenEq' : xbodyLen = (executePlan ([StackOp.SOLabel xlab] ++ (lgE.foldl
        (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL2)).1)).length := by
    rw [hfoldE]; exact hxbodyLenEq
  have hxlt' : asMid2.pc + xbodyLen < prog.length := by rw [hpcMid2]; exact hxlt
  have hxget' : prog.get ⟨asMid2.pc + xbodyLen, hxlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcMid2]) hxget
  have hasmX := hasm_regularHSVP_stop PE
    (budget := prog.length - (lbodyLen + 3) - (lbodyLen + 5))
    hfrontE hreadyE (hsdTransport2 asMid2 hsdV2) hsvV2 hspML2 (hrelTransport2 asMid2 hrelV2)
    hxthread hxblock' hxbodyLenEq' hxlt' hxget' (by omega)
  -- compose: the SAME block twice, then the exit — via the K-indexed scaffold
  exact hfsim_jmp_chain_of_runs 2
    (fun i => match i with | 0 => vs | 1 => jumpTo loopL esEnd0 | _ => jumpTo exitL esEnd1)
    (fun i => match i with | 0 => as | 1 => asMid1 | _ => asMid2)
    (fun i => match i with
      | 0 => prog.length
      | 1 => prog.length - (lbodyLen + 3)
      | _ => prog.length - (lbodyLen + 3) - (lbodyLen + 5))
    (fun i => match i with | 0 => loopBb | 1 => loopBb | _ => exitBb)
    (by intro i hi
        interval_cases i
        · exact hlk1
        · exact hlkL2)
    (by intro i hi
        interval_cases i
        · exact ⟨lfront, lterm, lhd, ltl, esEnd0, hlbb, hlcons, hlphi, hlnonterm, hethread0,
            hstep0, hlisterm, hnohalt0⟩
        · exact ⟨lfront, lterm, lhd, ltl, esEnd1, hlbb, hlcons, hlphi, hlnonterm, hethread1,
            hstep1, hlisterm, hnohalt1⟩)
    (by intro i hi
        interval_cases i
        · show prog.length - (lbodyLen + 3) ≤ prog.length
          omega
        · show prog.length - (lbodyLen + 3) - (lbodyLen + 5) ≤ prog.length - (lbodyLen + 3)
          omega)
    (by intro i hi
        interval_cases i
        · show runAsm (prog.length - (prog.length - (lbodyLen + 3))) offsetToPc prog as
            = AsmResult.AsmOK asMid1
          rw [show prog.length - (prog.length - (lbodyLen + 3)) = lbodyLen + 3 from by omega]
          exact hrunE1
        · show runAsm ((prog.length - (lbodyLen + 3))
              - (prog.length - (lbodyLen + 3) - (lbodyLen + 5))) offsetToPc prog asMid1
            = AsmResult.AsmOK asMid2
          rw [show (prog.length - (lbodyLen + 3))
              - (prog.length - (lbodyLen + 3) - (lbodyLen + 5)) = lbodyLen + 5 from by omega]
          exact hrunV2)
    hlkE
    (hterm_halt ctx exitBb xfront xterm xhd xtl (jumpTo exitL esEnd1) tsEndX (haltState tsEndX)
      hxbb hxcons hxphi hxnonterm hxthread hxterm hasmX)

set_option linter.unusedSimpArgs false in
/-- **K-iteration loop hfsim — cyclic control flow CLOSED for bounded iteration.** One physical
    loop block (`JNZ c loopL exitL`, code at `idxL`) is visited `K + 1` times: visits `0 … K-1`
    take the back-edge (`cond i ≠ 0`), visit `K` falls through to the halting exit block. The
    loop body's plan is a FOLD FIXED POINT (`hfix`: exit plan state = entry plan state, zero
    total gain, no residual gains) so ONE set of code facts serves every visit; the per-visit asm
    states are CONSTRUCTED by induction (each from the previous via the taken segment) and fed to
    the K-indexed scaffold. Venom-side per-visit data (`SEQ`/`E`/`cond`) enters as caller-supplied
    sequences. -/
theorem hfsim_regularHSVP_loop_K_stop
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {lo : AssocList String Nat}
    {gpL gpE : Instruction × Nat → PlanState → List StackOp × PlanState}
    {loopBb exitBb : BasicBlock}
    {lfront : List Instruction} {lterm lhd : Instruction} {ltl : List Instruction}
    {xfront : List Instruction} {xterm xhd : Instruction} {xtl : List Instruction} {tsEndX : VenomState}
    {llab xlab loopL exitL : String} {eS0 : List String}
    {eM0 : AssocList Operand Nat}
    {lgL lgE : List ((Instruction × Nat) × List String)}
    {epsL xps : PlanState} {lopsL xops : List StackOp}
    (K : Nat) (SEQ E : Nat → VenomState) (cond : Nat → bytes32)
    {PE lbodyLen xbodyLen offL offE idxL idxE : Nat}
    {c : String} {base : List Operand}
    -- the loop body plan: a fold FIXED POINT (loop invariance)
    (hfix : lgL.foldl (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)
      = (lopsL, epsL))
    (htot : totalGain lgL = 0)
    (hfoldE : lgE.foldl (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL)
      = (xops, xps))
    -- the loop block: Venom structure (shared by every visit)
    (hlbb : loopBb.instructions = lfront ++ [lterm])
    (hlcons : lfront ++ [lterm] = lhd :: ltl)
    (hlphi : lhd.opcode ≠ Opcode.PHI)
    (hlnonterm : ∀ inst ∈ lfront, isTerminator inst.opcode = false)
    (hjopc : lterm.opcode = Opcode.JNZ)
    (hjops : lterm.operands = [Operand.Var c, Operand.Label loopL, Operand.Label exitL])
    -- the per-visit Venom sequences
    (hSEQ0 : SEQ 0 = vs)
    (hSEQstep : ∀ i, i < K → SEQ (i + 1) = jumpTo loopL (E i))
    (hlks : ∀ i, i ≤ K → lookupBlock (SEQ i).currentBb fn.blocks = some loopBb)
    (hthreads : ∀ i, i ≤ K → execBodyThread lfront 0 { SEQ i with instIdx := 0 } = some (E i))
    (hconds : ∀ i, i ≤ K → lookupVar c (E i) = some (cond i))
    (htaken : ∀ i, i < K → cond i ≠ EvmYul.UInt256.ofNat 0)
    (hfall : cond K = EvmYul.UInt256.ofNat 0)
    (hnohalts : ∀ i, i ≤ K → (E i).halted = false)
    -- the loop block: ONE set of asm facts (constant across visits, by the fixed point)
    (haspc : as.pc = idxL)
    (hfrontL : lgL.map Prod.fst = lfront.zipIdx 0)
    (hreadyL : BodyStepsReadyHSVP (totalGain lgE + PE) lo offsetToPc prog gpL lgL eS0 eM0)
    (hsvL : StackPerm eS0 epsL) (hspM : epsL.spilled = eM0)
    (hrel0 : venomAsmRel lo epsL { vs with instIdx := 0 } as)
    (hsd0 : StackDiscHS (totalGain lgE + PE) epsL { vs with instIdx := 0 } as)
    (hlblock : asmBlockAt prog idxL (executePlan ([StackOp.SOLabel llab] ++ lopsL)))
    (hlbodyLenEq : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ lopsL)).length)
    (hstkL : epsL.stack = base ++ [Operand.Var c])
    (hpc1 : idxL + lbodyLen < prog.length)
    (hdup : prog.get ⟨idxL + lbodyLen, hpc1⟩ = AsmInst.AsmOp "DUP1")
    (hpc2 : idxL + lbodyLen + 1 < prog.length)
    (hpushL : prog.get ⟨idxL + lbodyLen + 1, hpc2⟩ = resolveInst lo (AsmInst.AsmPushLabel loopL))
    (hoffL_lk : AssocList.lookup String Nat lo loopL = some offL) (hoffL : offL < 2 ^ 256)
    (hpc3 : idxL + lbodyLen + 2 < prog.length)
    (hjumpi : prog.get ⟨idxL + lbodyLen + 2, hpc3⟩ = AsmInst.AsmOp "JUMPI")
    (hpc4 : idxL + lbodyLen + 3 < prog.length)
    (hpushE : prog.get ⟨idxL + lbodyLen + 3, hpc4⟩ = resolveInst lo (AsmInst.AsmPushLabel exitL))
    (hoffE_lk : AssocList.lookup String Nat lo exitL = some offE) (hoffE : offE < 2 ^ 256)
    (hpc5 : idxL + lbodyLen + 4 < prog.length)
    (hjumpE : prog.get ⟨idxL + lbodyLen + 4, hpc5⟩ = AsmInst.AsmOp "JUMP")
    (hidxL_lk : AssocList.lookup Nat Nat offsetToPc offL = some idxL)
    (hidxE_lk : AssocList.lookup Nat Nat offsetToPc offE = some idxE)
    -- boundary transports (definitional at jumpTo; per-visit)
    (hrelT : ∀ i, i < K → ∀ (asm' : AsmState), venomAsmRel lo epsL (E i) asm' →
        venomAsmRel lo epsL { jumpTo loopL (E i) with instIdx := 0 } asm')
    (hsdT : ∀ i, i < K → ∀ (asm' : AsmState),
        StackDiscHS (totalGain lgE + PE) epsL (E i) asm' →
        StackDiscHS (totalGain lgE + PE) epsL { jumpTo loopL (E i) with instIdx := 0 } asm')
    (hrelTX : ∀ (asm' : AsmState), venomAsmRel lo epsL (E K) asm' →
        venomAsmRel lo epsL { jumpTo exitL (E K) with instIdx := 0 } asm')
    (hsdTX : ∀ (asm' : AsmState), StackDiscHS (totalGain lgE + PE) epsL (E K) asm' →
        StackDiscHS (totalGain lgE + PE) epsL { jumpTo exitL (E K) with instIdx := 0 } asm')
    -- the exit block: Venom structure + asm segment
    (hlkE : lookupBlock (jumpTo exitL (E K)).currentBb fn.blocks = some exitBb)
    (hxbb : exitBb.instructions = xfront ++ [xterm])
    (hxcons : xfront ++ [xterm] = xhd :: xtl)
    (hxphi : xhd.opcode ≠ Opcode.PHI)
    (hxnonterm : ∀ inst ∈ xfront, isTerminator inst.opcode = false)
    (hxthread : execBodyThread xfront 0 { jumpTo exitL (E K) with instIdx := 0 } = some tsEndX)
    (hxterm : stepInstBase xterm tsEndX = ExecResult.Halt (haltState tsEndX))
    (hfrontE : lgE.map Prod.fst = xfront.zipIdx 0)
    (hreadyE : BodyStepsReadyHSVP PE lo offsetToPc prog gpE lgE eS0 eM0)
    (hxblock : asmBlockAt prog idxE (executePlan ([StackOp.SOLabel xlab] ++ xops)))
    (hxbodyLenEq : xbodyLen = (executePlan ([StackOp.SOLabel xlab] ++ xops)).length)
    (hxlt : idxE + xbodyLen < prog.length)
    (hxget : prog.get ⟨idxE + xbodyLen, hxlt⟩ = AsmInst.AsmOp "STOP")
    (hbudget : K * (lbodyLen + 3) + (lbodyLen + 5) + (xbodyLen + 1) ≤ prog.length) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hlisterm : isTerminator lterm.opcode = true := by rw [hjopc]; decide
  -- per-visit Venom steps
  have hstepTaken : ∀ i, i < K → stepInstBase lterm (E i) = ExecResult.OK (jumpTo loopL (E i)) := by
    intro i hi
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) (E i) = some (cond i) from hconds i (by omega)]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr (htaken i hi)) h
  have hstepFall : stepInstBase lterm (E K) = ExecResult.OK (jumpTo exitL (E K)) := by
    unfold stepInstBase
    rw [hjopc, hjops]
    simp only [show evalOperand (Operand.Var c) (E K) = some (cond K) from hconds K (Nat.le_refl K)]
    split
    · rename_i h; exact absurd h (by rw [hfall]; decide)
    · rfl
  -- construct the per-visit asm states by induction (each from the previous via the taken segment)
  have hchain : ∀ i, ∃ Ai : AsmState, i ≤ K →
      runAsm (i * (lbodyLen + 3)) offsetToPc prog as = AsmResult.AsmOK Ai ∧
      Ai.pc = idxL ∧
      venomAsmRel lo epsL { SEQ i with instIdx := 0 } Ai ∧
      StackDiscHS (totalGain lgE + PE) epsL { SEQ i with instIdx := 0 } Ai := by
    intro i
    induction i with
    | zero =>
      refine ⟨as, fun _ => ⟨?_, haspc, ?_, ?_⟩⟩
      · rw [Nat.zero_mul]; rfl
      · rw [hSEQ0]; exact hrel0
      · rw [hSEQ0]; exact hsd0
    | succ n ih =>
      obtain ⟨An, hAn⟩ := ih
      by_cases hle : n + 1 ≤ K
      · have hnK : n < K := by omega
        obtain ⟨hrunN, hpcN, hrelN, hsdN⟩ := hAn (by omega)
        -- the taken segment for visit n, from An (pc = idxL)
        have hblockN : asmBlockAt prog An.pc
            (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
              (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).1)) := by
          rw [hfix, hpcN]; exact hlblock
        have hbodyLenN : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
              (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).1)).length := by
          rw [hfix]; exact hlbodyLenEq
        have hstkFN : (lgL.foldl
              (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).2.stack
            = base ++ [Operand.Var c] := by
          rw [hfix]; exact hstkL
        have hcvalN : operandVal (E n) lo (Operand.Var c) = some (cond n) := by
          rw [operandVal_var_eq_lookupVar]; exact hconds n (by omega)
        have hpc1' : An.pc + lbodyLen < prog.length := by rw [hpcN]; exact hpc1
        have hdup' : prog.get ⟨An.pc + lbodyLen, hpc1'⟩ = AsmInst.AsmOp "DUP1" :=
          prog_get_transfer (by rw [hpcN]) hdup
        have hpc2' : An.pc + lbodyLen + 1 < prog.length := by rw [hpcN]; exact hpc2
        have hpushL' : prog.get ⟨An.pc + lbodyLen + 1, hpc2'⟩
            = resolveInst lo (AsmInst.AsmPushLabel loopL) :=
          prog_get_transfer (by rw [hpcN]) hpushL
        have hpc3' : An.pc + lbodyLen + 2 < prog.length := by rw [hpcN]; exact hpc3
        have hjumpi' : prog.get ⟨An.pc + lbodyLen + 2, hpc3'⟩ = AsmInst.AsmOp "JUMPI" :=
          prog_get_transfer (by rw [hpcN]) hjumpi
        obtain ⟨An1, hrunSeg, hrelSeg, hpcSeg, hsdSeg, _⟩ :=
          hasm_regularHSVP_jnz_taken (totalGain lgE + PE) hfrontL hreadyL
            (by simpa [htot] using hsdN) hsvL hspM hrelN (hthreads n (by omega))
            hblockN hbodyLenN hstkFN hcvalN (htaken n hnK) hpc1' hdup' hpc2' hpushL'
            hoffL_lk hoffL hpc3' hjumpi' hidxL_lk
        rw [hfix] at hrelSeg hsdSeg
        refine ⟨An1, fun _ => ⟨?_, hpcSeg, ?_, ?_⟩⟩
        · rw [Nat.succ_mul, runAsm_add_ok hrunN]
          exact hrunSeg
        · rw [hSEQstep n hnK]; exact hrelT n hnK An1 hrelSeg
        · rw [hSEQstep n hnK]; exact hsdT n hnK An1 hsdSeg
      · exact ⟨An, fun h => absurd h hle⟩
  choose A hA using hchain
  -- the final (fall-through) visit from A K
  obtain ⟨hrunK, hpcK, hrelK, hsdK⟩ := hA K (Nat.le_refl K)
  have hblockK : asmBlockAt prog (A K).pc
      (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).1)) := by
    rw [hfix, hpcK]; exact hlblock
  have hbodyLenK : lbodyLen = (executePlan ([StackOp.SOLabel llab] ++ (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).1)).length := by
    rw [hfix]; exact hlbodyLenEq
  have hstkFK : (lgL.foldl
        (fun acc x => (acc.1 ++ (gpL x.1 acc.2).1, (gpL x.1 acc.2).2)) ([], epsL)).2.stack
      = base ++ [Operand.Var c] := by
    rw [hfix]; exact hstkL
  have hcvalK : operandVal (E K) lo (Operand.Var c) = some (cond K) := by
    rw [operandVal_var_eq_lookupVar]; exact hconds K (Nat.le_refl K)
  have hpcK1 : (A K).pc + lbodyLen < prog.length := by rw [hpcK]; exact hpc1
  have hdupK : prog.get ⟨(A K).pc + lbodyLen, hpcK1⟩ = AsmInst.AsmOp "DUP1" :=
    prog_get_transfer (by rw [hpcK]) hdup
  have hpcK2 : (A K).pc + lbodyLen + 1 < prog.length := by rw [hpcK]; exact hpc2
  have hpushLK : prog.get ⟨(A K).pc + lbodyLen + 1, hpcK2⟩
      = resolveInst lo (AsmInst.AsmPushLabel loopL) :=
    prog_get_transfer (by rw [hpcK]) hpushL
  have hpcK3 : (A K).pc + lbodyLen + 2 < prog.length := by rw [hpcK]; exact hpc3
  have hjumpiK : prog.get ⟨(A K).pc + lbodyLen + 2, hpcK3⟩ = AsmInst.AsmOp "JUMPI" :=
    prog_get_transfer (by rw [hpcK]) hjumpi
  have hpcK4 : (A K).pc + lbodyLen + 3 < prog.length := by rw [hpcK]; exact hpc4
  have hpushEK : prog.get ⟨(A K).pc + lbodyLen + 3, hpcK4⟩
      = resolveInst lo (AsmInst.AsmPushLabel exitL) :=
    prog_get_transfer (by rw [hpcK]) hpushE
  have hpcK5 : (A K).pc + lbodyLen + 4 < prog.length := by rw [hpcK]; exact hpc5
  have hjumpEK : prog.get ⟨(A K).pc + lbodyLen + 4, hpcK5⟩ = AsmInst.AsmOp "JUMP" :=
    prog_get_transfer (by rw [hpcK]) hjumpE
  obtain ⟨asFinal, hrunFall, hrelFall, hpcFall, hsdFall, _⟩ :=
    hasm_regularHSVP_jnz_nottaken (totalGain lgE + PE) hfrontL hreadyL
      (by simpa [htot] using hsdK) hsvL hspM hrelK (hthreads K (Nat.le_refl K))
      hblockK hbodyLenK hstkFK hcvalK hfall hpcK1 hdupK hpcK2 hpushLK hoffL_lk hoffL
      hpcK3 hjumpiK hpcK4 hpushEK hoffE_lk hoffE hpcK5 hjumpEK hidxE_lk
  rw [hfix] at hrelFall hsdFall
  -- the exit STOP segment from asFinal
  have hxblock' : asmBlockAt prog asFinal.pc
      (executePlan ([StackOp.SOLabel xlab] ++ (lgE.foldl
        (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL)).1)) := by
    rw [hfoldE, hpcFall]; exact hxblock
  have hxbodyLenEq' : xbodyLen = (executePlan ([StackOp.SOLabel xlab] ++ (lgE.foldl
        (fun acc x => (acc.1 ++ (gpE x.1 acc.2).1, (gpE x.1 acc.2).2)) ([], epsL)).1)).length := by
    rw [hfoldE]; exact hxbodyLenEq
  have hxlt' : asFinal.pc + xbodyLen < prog.length := by rw [hpcFall]; exact hxlt
  have hxget' : prog.get ⟨asFinal.pc + xbodyLen, hxlt'⟩ = AsmInst.AsmOp "STOP" :=
    prog_get_transfer (by rw [hpcFall]) hxget
  have hmulK : K * (lbodyLen + 3) + (lbodyLen + 5) + (xbodyLen + 1) ≤ prog.length := hbudget
  have hasmX := hasm_regularHSVP_stop PE
    (budget := prog.length - K * (lbodyLen + 3) - (lbodyLen + 5))
    hfrontE hreadyE (hsdTX asFinal hsdFall) hsvL hspM (hrelTX asFinal hrelFall)
    hxthread hxblock' hxbodyLenEq' hxlt' hxget' (by omega)
  -- feed the K-indexed scaffold: K+1 links (K back-edges + the fall-through), then the exit
  have hA0eq : A 0 = as := by
    obtain ⟨h0, _, _, _⟩ := hA 0 (Nat.zero_le K)
    rw [Nat.zero_mul] at h0
    have h0' : AsmResult.AsmOK as = AsmResult.AsmOK (A 0) := h0
    injection h0' with h; exact h.symm
  have hmain := hfsim_jmp_chain_of_runs (fuel := fuel) (ctx := ctx) (fn := fn)
    (prog := prog) (offsetToPc := offsetToPc) (K + 1)
    (fun i => if i = K + 1 then jumpTo exitL (E K) else SEQ i)
    (fun i => if i = K + 1 then asFinal else A i)
    (fun i => if i = K + 1 then prog.length - K * (lbodyLen + 3) - (lbodyLen + 5)
              else prog.length - i * (lbodyLen + 3))
    (fun i => if i = K + 1 then exitBb else loopBb)
    (by intro i hi
        have hBi : (if i = K + 1 then exitBb else loopBb) = loopBb := if_neg (by omega)
        have hSi : (if i = K + 1 then jumpTo exitL (E K) else SEQ i) = SEQ i := if_neg (by omega)
        simp only [hBi, hSi]
        exact hlks i (by omega))
    (by intro i hi
        have hBi : (if i = K + 1 then exitBb else loopBb) = loopBb := if_neg (by omega)
        have hSi : (if i = K + 1 then jumpTo exitL (E K) else SEQ i) = SEQ i := if_neg (by omega)
        simp only [hBi, hSi]
        by_cases hik : i < K
        · have hSi1 : (if i + 1 = K + 1 then jumpTo exitL (E K) else SEQ (i + 1)) = SEQ (i + 1) :=
            if_neg (by omega)
          simp only [hSi1]
          refine ⟨lfront, lterm, lhd, ltl, E i, hlbb, hlcons, hlphi, hlnonterm,
            hthreads i (by omega), ?_, hlisterm, ?_⟩
          · rw [hSEQstep i hik]; exact hstepTaken i hik
          · rw [hSEQstep i hik]
            show (E i).halted = false
            exact hnohalts i (by omega)
        · have hiK : i = K := by omega
          have hSi1 : (if i + 1 = K + 1 then jumpTo exitL (E K) else SEQ (i + 1))
              = jumpTo exitL (E K) := if_pos (by omega)
          simp only [hSi1]
          rw [hiK]
          exact ⟨lfront, lterm, lhd, ltl, E K, hlbb, hlcons, hlphi, hlnonterm,
            hthreads K (Nat.le_refl K), hstepFall, hlisterm, hnohalts K (Nat.le_refl K)⟩)
    (by intro i hi
        by_cases hik : i < K
        · rw [if_neg (by omega), if_neg (by omega)]
          have h1 : (i + 1) * (lbodyLen + 3) ≤ K * (lbodyLen + 3) :=
            Nat.mul_le_mul_right _ (by omega)
          have h2 : i * (lbodyLen + 3) + (lbodyLen + 3) = (i + 1) * (lbodyLen + 3) :=
            (Nat.succ_mul i (lbodyLen + 3)).symm
          omega
        · have hiK : i = K := by omega
          rw [hiK, if_pos rfl, if_neg (by omega)]
          omega)
    (by intro i hi
        by_cases hik : i < K
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          obtain ⟨hrunI, _, _, _⟩ := hA i (by omega)
          obtain ⟨hrunI1, _, _, _⟩ := hA (i + 1) (by omega)
          have hsm : (i + 1) * (lbodyLen + 3) = i * (lbodyLen + 3) + (lbodyLen + 3) :=
            Nat.succ_mul i (lbodyLen + 3)
          rw [hsm, runAsm_add_ok hrunI] at hrunI1
          have h1 : (i + 1) * (lbodyLen + 3) ≤ K * (lbodyLen + 3) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [show prog.length - i * (lbodyLen + 3)
              - (prog.length - (i + 1) * (lbodyLen + 3)) = lbodyLen + 3 from by omega]
          exact hrunI1
        · have hiK : i = K := by omega
          rw [hiK, if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl]
          rw [show prog.length - K * (lbodyLen + 3)
              - (prog.length - K * (lbodyLen + 3) - (lbodyLen + 5)) = lbodyLen + 5 from by omega]
          exact hrunFall)
    (by have hS : (if K + 1 = K + 1 then jumpTo exitL (E K) else SEQ (K + 1))
          = jumpTo exitL (E K) := if_pos rfl
        have hB : (if K + 1 = K + 1 then exitBb else loopBb) = exitBb := if_pos rfl
        simp only [hS, hB]
        exact hlkE)
    (by have hS : (if K + 1 = K + 1 then jumpTo exitL (E K) else SEQ (K + 1))
          = jumpTo exitL (E K) := if_pos rfl
        have hB : (if K + 1 = K + 1 then exitBb else loopBb) = exitBb := if_pos rfl
        have hAf : (if K + 1 = K + 1 then asFinal else A (K + 1)) = asFinal := if_pos rfl
        have hNb : (if K + 1 = K + 1 then prog.length - K * (lbodyLen + 3) - (lbodyLen + 5)
              else prog.length - (K + 1) * (lbodyLen + 3))
          = prog.length - K * (lbodyLen + 3) - (lbodyLen + 5) := if_pos rfl
        simp only [hS, hB, hAf, hNb]
        exact hterm_halt ctx exitBb xfront xterm xhd xtl (jumpTo exitL (E K)) tsEndX
          (haltState tsEndX) hxbb hxcons hxphi hxnonterm hxthread hxterm hasmX)
  have hS0 : (if 0 = K + 1 then jumpTo exitL (E K) else SEQ 0) = vs := by
    rw [if_neg (by omega)]; exact hSEQ0
  have hA0 : (if 0 = K + 1 then asFinal else A 0) = as := by
    rw [if_neg (by omega)]; exact hA0eq
  have hNb0 : (if 0 = K + 1 then prog.length - K * (lbodyLen + 3) - (lbodyLen + 5)
        else prog.length - 0 * (lbodyLen + 3)) = prog.length := by
    rw [if_neg (by omega), Nat.zero_mul, Nat.sub_zero]
  simp only [hS0, hA0, hNb0] at hmain
  exact hmain

/-- **Non-entry var-reading memory-copy function sim (de-vacuification).** For `main: entry: JMP next ;
    next: CALLDATACOPY a b c ; STOP`, with `a, b, c` live vars on the stack (the config a JMP predecessor
    leaves) and the memory-safety precondition `hmemsafe`, `runBlocks` corresponds to `runAsm` on the
    resolved program, halting with the terminal relation. The H-fold twin of `hfsim_jmp_sstore_example`:
    composes `hentryAsm_bare_jmp` (entry JMP → next's pc, relation preserved) + `hasm_regularHN_stop`
    (the residual-budget demand-threaded CALLDATACOPY block from the mid-state) via
    `hfsim_jmp_then_halt`. -/
theorem hfsim_jmp_calldatacopy_example
    {fuel : Nat} {ctx : VenomContext} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {va vb vc : bytes32}
    (hcurbb : vs.currentBb = "entry") (hvshalt : vs.halted = false)
    (hadef : lookupVar "a" vs = some va) (hbdef : lookupVar "b" vs = some vb)
    (hcdef : lookupVar "c" vs = some vc)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) } vs as)
    (haspc : as.pc = 0)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel lo p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    match runBlocks fuel ctx jmpCdcFn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm jmpCdcProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpCdcProg as
                 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm jmpCdcProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpCdcProg as
                 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm jmpCdcProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpCdcProg as
                 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True := by
  have hlen : jmpCdcProg.length = 9 := rfl
  -- entry JMP asm run  ->  asMid at next's pc (3), relation preserved
  have hbLabel : asmBlockAt jmpCdcProg as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
  have hpc1 : as.pc + 1 < jmpCdcProg.length := by rw [haspc, hlen]; decide
  have hpush : jmpCdcProg.get ⟨as.pc + 1, hpc1⟩
      = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
    have e : as.pc + 1 = 1 := by omega
    simp only [e]; rfl
  have hpc2 : as.pc + 2 < jmpCdcProg.length := by rw [haspc, hlen]; decide
  have hjump : jmpCdcProg.get ⟨as.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
    have e : as.pc + 2 = 2 := by omega
    simp only [e]; rfl
  obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
    hentryAsm_bare_jmp (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
      (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (off := 5) (idx := 3)
      hrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
  -- CALLDATACOPY block asm run from asMid (pc 3) via hasm_regularHN_stop
  have hdef : ∀ z ∈ ["a","b","c"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · subst h; exact ⟨va, hadef⟩
    · subst h; exact ⟨vb, hbdef⟩
    · subst h; exact ⟨vc, hcdef⟩
  have hblockN : asmBlockAt jmpCdcProg asMid.pc
      (executePlan ([StackOp.SOLabel "next"] ++ (([cdcInst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "next" acc.2).1,
          (generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg dummyFn z.1 ["a","b","c"] false true "next" acc.2).2))
          ([], { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) })).1)) := by
    rw [hpcMid]
    refine ⟨by decide, fun j hj => ?_⟩
    have hj' : j < 5 := hj
    interval_cases j <;> rfl
  have hltN : asMid.pc + 5 < jmpCdcProg.length := by rw [hpcMid, hlen]; decide
  have hgetN : jmpCdcProg.get ⟨asMid.pc + 5, hltN⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨asMid.pc + 5, hltN⟩ : Fin _) = ⟨8, by rw [hlen]; decide⟩ from
      Fin.ext (show asMid.pc + 5 = 8 from by rw [hpcMid])]; rfl
  set smid : VenomState := jumpTo "next" { vs with instIdx := 0 } with hsmid
  set tsEnd : VenomState :=
    { writeMemoryWithExpansion va.toNat
        ((⟨smid.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding vb.toNat vc.toNat)
        { smid with instIdx := 0 } with instIdx := 1 } with htsEnd
  have hthreadN : execBodyThread [cdcInst] 0 { smid with instIdx := 0 } = some tsEnd := by
    have had : lookupVar "a" { smid with instIdx := 0 } = some va := hadef
    have hbd : lookupVar "b" { smid with instIdx := 0 } = some vb := hbdef
    have hcd : lookupVar "c" { smid with instIdx := 0 } = some vc := hcdef
    rw [htsEnd]; simp only [execBodyThread, cdcInst, stepInstBase, evalOperand, had, hbd, hcd]
  have hasmN := hasm_regularHN_stop
    (labelOffsets := lo) (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (fn := dummyFn)
    (body := [cdcInst]) (l := "next") (curBbLabel := "next") (nextLiveness := ["a","b","c"]) (S0 := ["a","b","c"])
    (ps0 := { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) }) (dem := 1)
    (vs := smid) (asm := asMid) (sEnd := tsEnd)
    (bodyLen := 5) (budget := jmpCdcProg.length - 3)
    (cdc_regularBodyH' hmemsafe)
    (stackDiscH_varStack (by decide) hdef) stackIsVars_varStack hrelMid hthreadN
    hblockN rfl hltN hgetN (by decide)
  -- assemble
  have hstep_jmp : stepInstBase jmpInst { vs with instIdx := 0 }
      = ExecResult.OK (jumpTo "next" { vs with instIdx := 0 }) := rfl
  refine hfsim_jmp_then_halt
    (entryBb := jmpEntryBB) (termBb := cdcNextBB) (n := 3)
    (efront := []) (eterm := jmpInst) (ehd := jmpInst) (etl := [])
    (esEnd := { vs with instIdx := 0 }) (sMid := smid)
    (tfront := [cdcInst]) (tterm := stopInst) (thd := cdcInst) (ttl := [stopInst])
    (tsEnd := tsEnd) (tsEnd' := haltState tsEnd)
    ?_ rfl rfl (by decide) (by simp) rfl hstep_jmp (by decide) (by simp [smid, jumpTo, hvshalt]) hrunE
    (by rw [hlen]; decide) ?_ rfl rfl (by decide) (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    hthreadN (by simp only [stepInstBase, stopInst]) hasmN
  · show lookupBlock vs.currentBb jmpCdcFn.blocks = some jmpEntryBB
    rw [hcurbb]; rfl
  · show lookupBlock smid.currentBb jmpCdcFn.blocks = some cdcNextBB
    rfl

/-- **Unconditional top-level `codegen_correct` conclusion for a body-carrying
function.** The CALLDATACOPY-carrying two-block function `jmpCdcFn`, run from the
context entry via `runContext`, corresponds to its resolved program `jmpCdcProg` —
`hbsim` fully discharged (no per-block hypothesis), extending the de-vacuified
top-level beyond the trivial STOP/JMP instances. Via the bridge
`runContext_correct_of_hfsim` applied to `hfsim_jmp_calldatacopy_example` at the
entry-reset state (the reset touches only control-flow fields, which `venomAsmRel`,
`lookupVar` and `halted` all ignore — so the example's hypotheses transport by
definitional equality). The only interface is the memory-safety side condition
(`hmemsafe`, a runtime precondition of the copy op) + the entry-lookup facts. -/
theorem runContext_calldatacopy_correct
    {fuel : Nat} {ctx : VenomContext} {lo : AssocList String Nat}
    {vs0 : VenomState} {as : AsmState} {va vb vc : bytes32} {entryName : String}
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some jmpCdcFn)
    (hlbl : fnEntryLabel jmpCdcFn = some "entry")
    (hvshalt : vs0.halted = false)
    (hadef : lookupVar "a" vs0 = some va) (hbdef : lookupVar "b" vs0 = some vb)
    (hcdef : lookupVar "c" vs0 = some vc)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := (["a","b","c"].map Operand.Var) } vs0 as)
    (haspc : as.pc = 0)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc,
        venomAsmRel lo p v s → lookupVar "a" v = some wa → lookupVar "c" v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    (match runContext fuel ctx vs0 with
     | ExecResult.Halt vs' => ∃ as', runAsm jmpCdcProg.length ([(5, 3), (0, 0)] : AssocList Nat Nat)
         jmpCdcProg as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm jmpCdcProg.length
         ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpCdcProg as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm jmpCdcProg.length
         ([(5, 3), (0, 0)] : AssocList Nat Nat) jmpCdcProg as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine runContext_correct_of_hfsim (entryLbl := "entry") hent hlk hlbl ?_
  exact hfsim_jmp_calldatacopy_example (ctx := ctx)
    (vs := { vs0 with prevBb := none, currentBb := "entry", instIdx := 0 })
    rfl hvshalt hadef hbdef hcdef hrel haspc hmemsafe

/-! ## Concrete genuine (non-identity) join reorder — a transposition

Every JMP example above (`hfsim_jmp_sstore_example`, `hfsim_jmp_calldatacopy_example`) is a *linear*
chain: the predecessor's exit layout already equals the successor's entry layout, so the join reorder is
the identity. This is the first example where the two differ — the predecessor leaves the live vars
`[b, a]` but the successor expects `[a, b]`, so the join emits a genuine `SWAP1`. It de-vacuifies the
bounded genuine-reorder join `reorderPlan_join_bounded` (the reorder runs on asm, `venomAsmRel`
preserved, plan stack landed at the target layout), whose per-`reorderOne` step is discharged internally
via the `foldl_ops_sim_inv` invariant (bounded, no-spill). -/

/-- **Concrete genuine (non-identity) join reorder — a transposition.** De-vacuifies
    `reorderPlan_join_bounded`: a JMP predecessor leaves the two live vars **swapped** (`[b, a]`) relative
    to the successor's entry layout `[a, b]`, so the join reorder is a genuine `SWAP1` (not a no-op). From
    the var-stack asm state (`venomAsmRel_varStack`), the reorder runs to `AsmOK`, landing the plan stack
    at `[a, b]` with `venomAsmRel` preserved — the first concrete genuine-reorder join. -/
theorem reorderPlan_join_swap_example
    {vs : VenomState} {va vb : bytes32} {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst}
    (hadef : lookupVar "a" vs = some va) (hbdef : lookupVar "b" vs = some vb)
    (hblock : asmBlockAt prog
        ({ asmOfVenom vs with stack := asmStackOf vs lo (["b","a"].map Operand.Var) }).pc
        [AsmInst.AsmOp "SWAP1"]) :
    ∃ as', runAsm 1 offsetToPc prog
             { asmOfVenom vs with stack := asmStackOf vs lo (["b","a"].map Operand.Var) }
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo { initPlanState 0 with stack := (["a","b"].map Operand.Var) } vs as' ∧
           as'.pc = ({ asmOfVenom vs with stack := asmStackOf vs lo (["b","a"].map Operand.Var) }).pc + 1 := by
  have hdef : ∀ z ∈ ["b","a"], ∃ w, lookupVar z vs = some w := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h
    · subst h; exact ⟨vb, hbdef⟩
    · subst h; exact ⟨va, hadef⟩
  have hreorder : reorderPlan [Operand.Var "a", Operand.Var "b"]
      { initPlanState 0 with stack := (["b","a"].map Operand.Var) }
      = ([StackOp.SOSwap 1], { initPlanState 0 with stack := [Operand.Var "a", Operand.Var "b"] }) := by
    have h := reorderPlan_swapped_pair_var [] "b" "a"
      { initPlanState 0 with stack := (["b","a"].map Operand.Var) } (by simp)
    simpa using h
  obtain ⟨as', hrun, hrel', hstk, hpc⟩ :=
    reorderPlan_join_bounded (targetOps := [Operand.Var "a", Operand.Var "b"]) (base := [])
      (perm := ["b","a"].map Operand.Var)
      (by simpa using List.Perm.swap (Operand.Var "a") (Operand.Var "b") [])
      (by simp) (by simp) (fun o => rfl) hreorder (venomAsmRel_varStack hdef) hblock
  exact ⟨as', hrun, hrel', hpc⟩

/-! ## Concrete schedule discharges by evaluation (the concrete-function path)

`pcOfLabel` / `resolvedJump_pcOf` — the whole-function pc-scheduling obligation — are computable on a
concrete resolved program, so they discharge by `decide`/`rfl` with no need for the general
value-lift induction. -/

/-- A concrete resolved program with two JUMPDEST labels. -/
def exStopProg : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP", AsmInst.AsmLabel "exit", AsmInst.AsmOp "STOP"]

/-- `pcOfLabel` computes each label's list index — by evaluation. -/
theorem pcOfLabel_exStopProg_exit : pcOfLabel exStopProg "exit" = 2 := by decide
theorem pcOfLabel_exStopProg_entry : pcOfLabel exStopProg "entry" = 0 := by decide

/-- **Concrete resolved-JMP lands at `pcOfLabel` — by evaluation.** The destination a resolved JUMP to
    `"exit"` computes (`offsetToPc.lookup (offsets.lookup "exit")`) is `some (pcOfLabel exStopProg "exit")`
    — the whole pc-scheduling obligation discharged concretely. -/
theorem resolvedJump_pcOf_exStopProg :
    AssocList.lookup Nat Nat (asmResolve exStopProg).2
      ((AssocList.lookup String Nat (computeLabelOffsets exStopProg).2 "exit").getD 0)
      = some (pcOfLabel exStopProg "exit") := by
  have h : exStopProg = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"]
      ++ AsmInst.AsmLabel "exit" :: [AsmInst.AsmOp "STOP"] := rfl
  rw [h]
  exact resolvedJump_pcOf [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"] "exit"
    [AsmInst.AsmOp "STOP"] (by simp) (by simp)

/-- **Suppliability witness for `codegen_correct_sched`** (the budget-ranked scheduling bridge): the
    STOP function instantiated through it. This is the crucial contrast with `codegen_correct_of_hstep`
    — whose `hstep` is unsuppliable (`runAsm 0 = AsmOK ≠ AsmHalt`). Here the rank `wOf ≡ 2` gives the
    `hstep` its budget lower bound `2 ≤ N`, so the halt clause is discharged for *every* such `N` by
    lifting `stop_runAsm_core` (`runAsm 2 = AsmHalt`) through `runAsm_le_of_ne_ok`. -/
theorem codegen_correct_stop_sched {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
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
  refine codegen_correct_sched (fuel := 10) (ctx := stopCtx) (fn := stopFn)
    (fnEom := 0) (lblCtr := 0) (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan stopFn 0 0).get!.1) (psFinal := (generateFnPlan stopFn 0 0).get!.2)
    (pcOf := fun _ => 0) (psOf := fun _ => initPlanState 0) (wOf := fun _ => 2)
    rfl rfl rfl rfl ?_ (bb0 := stopBB) rfl haspc (by decide) hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN _hnh
  have hbb : bb = stopBB := by
    rw [show stopFn.blocks = [stopBB] from rfl, lookupBlock] at hlk
    simpa using List.mem_of_find?_eq_some hlk
  subst hbb
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, stopBB, stopInst]
  | succ k =>
    have hrb : runBlock (k+1) stopCtx stopBB s
        = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
    rw [hrb]
    obtain ⟨as', hrun, hterm⟩ := stop_runAsm_core hvrel hpc
    exact ⟨as', runAsm_le_of_ne_ok (fun _ => by simp) hwN hrun, hterm⟩

/-- **Whole-function capstone via `codegen_correct_canonical` (single-block STOP).** The `codegen_correct`
    conclusion for `stopFn` (`main: entry: STOP`), discharged through the *canonical* scaffold: the
    schedule (`pcOfLabel`/`psOfFn`/rank) and all entry obligations come from `codegen_correct_canonical`
    (via `pcOfLabel_entry_zero` + `psOfFn_entry`); only the per-block `hstep` — here the STOP halt via
    `stop_runAsm_core` at the canonical budget — is supplied. End-to-end validation that the canonical
    stack (`codegen_correct_canonical` + `psOfFn` + `pcOfLabel_entry_zero`) composes into a real capstone. -/
theorem codegen_correct_canonical_stop {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
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
  have hfnready : ∀ bb ∈ stopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [stopFn, List.mem_singleton] at hbb; subst hbb
    simp only [stopBB, List.mem_singleton] at hinst; subst hinst
    unfold codegenReadyInst; decide
  have hgen : generateFnPlan stopFn 0 0
      = some ((generateFnPlan stopFn 0 0).get!.1, (generateFnPlan stopFn 0 0).get!.2) := rfl
  have hprog : (asmResolve (executePlan (generateFnPlan stopFn 0 0).get!.1)).1
      = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"] := rfl
  refine codegen_correct_canonical (fuel := 10) (ctx := stopCtx) (fn := stopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := (generateFnPlan stopFn 0 0).get!.1)
    (psFinal := (generateFnPlan stopFn 0 0).get!.2) (entry := stopBB)
    hgen rfl rfl rfl rfl rfl hfnready rfl (pcOfLabel_entry_zero rfl hfnready hgen) haspc ?_ hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN _hnh
  have hbb : bb = stopBB := by
    rw [show stopFn.blocks = [stopBB] from rfl, lookupBlock] at hlk
    simpa using List.mem_of_find?_eq_some hlk
  subst hbb
  have hpc0 : asm.pc = 0 := by rw [hpc, hprog]; decide
  have hps : psOfFn (fnPlanFuel stopFn) stopFn 0 0 stopBB.label = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  rw [hps] at hvrel
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, stopBB, stopInst]
  | succ k =>
    have hrb : runBlock (k+1) stopCtx stopBB s = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopBB, stopInst, stepInstBase]
    rw [hrb, hprog]
    obtain ⟨as', hrun, hterm⟩ := stop_runAsm_core hvrel hpc0
    refine ⟨as', runAsm_le_of_ne_ok (fun _ => by simp) ?_ hrun, hterm⟩
    have hpcl : pcOfLabel [AsmInst.AsmLabel "entry", AsmInst.AsmOp "STOP"] stopBB.label = 0 := by decide
    rw [hprog, hpcl] at hwN; simpa using hwN

/-- **Whole-function capstone via `codegen_correct_canonical` (2-block JMP→STOP).** `codegen_correct`
    for `jmpStopFn` through the canonical scaffold, exercising the reworked JMP arm
    `hstep_jmp_of_layout` (offsetToPc from the unresolved plan) and `blockSim_halt_of_body`. -/
theorem codegen_correct_canonical_jmpStop {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jmpStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ jmpStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [jmpStopFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [jmpEntryBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
    · simp only [stopNextBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan jmpStopFn 0 0
      = some ((generateFnPlan jmpStopFn 0 0).get!.1, (generateFnPlan jmpStopFn 0 0).get!.2) := rfl
  refine codegen_correct_canonical (fuel := 10) (ctx := jmpStopCtx) (fn := jmpStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := (generateFnPlan jmpStopFn 0 0).get!.1)
    (psFinal := (generateFnPlan jmpStopFn 0 0).get!.2) (entry := jmpEntryBB)
    hgen rfl rfl rfl rfl rfl hfnready rfl (pcOfLabel_entry_zero rfl hfnready hgen) haspc ?_ hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN hnh
  have hbb2 : bb = jmpEntryBB ∨ bb = stopNextBB := by
    rw [show jmpStopFn.blocks = [jmpEntryBB, stopNextBB] from rfl, lookupBlock] at hlk
    simpa using List.mem_of_find?_eq_some hlk
  rcases hbb2 with hbb | hbb
  · -- entry block: JMP via the reworked hstep_jmp_of_layout
    subst hbb
    have hpc0 : asm.pc = 0 := by rw [hpc]; decide
    have hpsN : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next" = initPlanState 0 := rfl
    have hpsE : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 jmpEntryBB.label = initPlanState 0 :=
      psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
    rw [hpsE] at hvrel
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, jmpEntryBB, jmpInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx jmpEntryBB s
          = ExecResult.OK (jumpTo "next" { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jmpEntryBB, jmpInst,
          stepInstBase, isTerminator, jumpTo, hnh]
      have hnothalt : (jumpTo "next" { s with instIdx := 0 }).halted = false := by simp [jumpTo, hnh]
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel "entry"]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hpc1 : asm.pc + 1 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc0]; decide
      have hpush : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨asm.pc + 1, hpc1⟩
          = resolveInst (computeLabelOffsets (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2 (AsmInst.AsmPushLabel "next") := by
        have e : asm.pc + 1 = 1 := by rw [hpc0]
        conv_lhs => rw [show (⟨asm.pc + 1, hpc1⟩ : Fin _) = ⟨1, by decide⟩ from Fin.ext e]
        rfl
      have hpc2 : asm.pc + 2 < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc0]; decide
      have hjump : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨asm.pc + 2, hpc2⟩
          = AsmInst.AsmOp "JUMP" := by
        have e : asm.pc + 2 = 2 := by rw [hpc0]
        conv_lhs => rw [show (⟨asm.pc + 2, hpc2⟩ : Fin _) = ⟨2, by decide⟩ from Fin.ext e]
        rfl
      obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
        hentryAsm_bare_jmp (offsetToPc := (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2)
          (off := 5) (idx := 3) hvrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
      have hwe : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 jmpEntryBB.label = 5 := by decide
      rw [hwe] at hwN
      refine hstep_jmp_of_layout (psOf := psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0)
        (wOf := fun l => (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 l)
        (bb' := stopNextBB)
        (pre := [AsmInst.AsmLabel "entry", AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP"])
        (suf := [AsmInst.AsmOp "STOP"]) (off := 5) (idx := 3)
        rfl
        (by intro inst hinst; simp only [List.mem_singleton] at hinst; subst hinst; simp [stopNextBB])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [stopNextBB])
        (by decide) (by decide) hrb hnothalt hrunE hrelMid
        (by simp [show stopNextBB.label = "next" from rfl, hpsN])
        (by simp [show stopNextBB.label = "next" from rfl, hpsN])
        (by simp [show stopNextBB.label = "next" from rfl, hpsN])
        (by simp [show stopNextBB.label = "next" from rfl, hpsN]) hpcMid (by omega)
        rfl (by decide)
  · -- next block: STOP via blockSim_halt_of_body
    subst hbb
    have hpc3 : asm.pc = 3 := by rw [hpc]; decide
    have hpsN : psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next" = initPlanState 0 := rfl
    rw [show stopNextBB.label = "next" from rfl, hpsN] at hvrel
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, stopNextBB, stopInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx stopNextBB s = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopNextBB, stopInst, stepInstBase]
      rw [hrb]
      have hbLabel : asmBlockAt (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm.pc
          (executePlan [StackOp.SOLabel "next"]) := by
        rw [hpc3]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1'⟩ :=
        soLabel_sim (offsetToPc := (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2) lo
          (psOfFn (fnPlanFuel jmpStopFn) jmpStopFn 0 0 "next") _ _ _ "next" (by rw [hpsN]; exact hvrel) hbLabel
      have hr1 : runAsm 1 (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
          (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 asm = AsmResult.AsmOK as1 := hrun1
      have hpc1'' : as1.pc = 4 := by rw [hpc1', hpc3]; decide
      have hlt4 : as1.pc < (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length := by
        rw [hpc1'']; decide
      have hstop : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.get ⟨as1.pc, hlt4⟩
          = AsmInst.AsmOp "STOP" := by
        conv_lhs => rw [show (⟨as1.pc, hlt4⟩ : Fin _) = ⟨4, by decide⟩ from Fin.ext hpc1'']
        rfl
      have hwn2 : (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 stopNextBB.label = 2 := by decide
      have hle2 : (1 : Nat) + 1 ≤ N := by omega
      obtain ⟨hhalt, hterm⟩ := blockSim_halt_of_body (bodyLen := 1) hr1 (by rw [hpsN] at hrel1; exact hrel1) hlt4 hstop hle2
      exact ⟨asmNext as1, hhalt, hterm⟩

def addStopCtx : VenomContext := { functions := [addStopFn], entry := some "main" }

/-- **Whole-function capstone via `codegen_correct_canonical` with a NON-TRIVIAL BODY (`entry: ADD; STOP`).**
    Unlike the bare STOP/JMP capstones, this exercises a body instruction (ADD, two literal pushes) through
    the canonical scaffold: the block sim is `addStop_runAsm_core` (`[JUMPDEST; PUSH; PUSH; ADD; STOP]` →
    AsmHalt) at the canonical budget `prog.length - pcOfLabel = 5 ≤ N`. -/
theorem codegen_correct_canonical_addStop {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 addStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ addStopFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [addStopFn, List.mem_singleton] at hbb; subst hbb
    simp only [addStopBB, List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan addStopFn 0 0
      = some ((generateFnPlan addStopFn 0 0).get!.1, (generateFnPlan addStopFn 0 0).get!.2) := rfl
  refine codegen_correct_canonical (fuel := 10) (ctx := addStopCtx) (fn := addStopFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := (generateFnPlan addStopFn 0 0).get!.1)
    (psFinal := (generateFnPlan addStopFn 0 0).get!.2) (entry := addStopBB)
    hgen rfl rfl rfl rfl rfl hfnready rfl (pcOfLabel_entry_zero rfl hfnready hgen) haspc ?_ hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN _hnh
  have hbb : bb = addStopBB := by
    rw [show addStopFn.blocks = [addStopBB] from rfl, lookupBlock] at hlk
    simpa using List.mem_of_find?_eq_some hlk
  subst hbb
  have hpc0 : asm.pc = 0 := by rw [hpc]; decide
  have hps : psOfFn (fnPlanFuel addStopFn) addStopFn 0 0 addStopBB.label = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  rw [hps] at hvrel
  -- the ADD;STOP body needs f' ≥ 2 (execBlock consumes 1 fuel for ADD, 1 for STOP)
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, addStopBB, addInst, stopInst]
  | succ k =>
    cases k with
    | zero => -- f' = 1: runBlock 1 = Error (ADD consumes the fuel), catch-all True
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, addStopBB, addInst,
            stopInst, stepInstBase, execPure2, evalOperand, isTerminator]
    | succ j => -- f' = j + 2: the block completes to Halt
      have hrb : runBlock (j+1+1) addStopCtx addStopBB s
          = ExecResult.Halt (haltState { updateVar "c" (UInt256.ofNat 5 + UInt256.ofNat 3)
              { s with instIdx := 0 } with instIdx := 1 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, addStopBB, addInst,
              stopInst, stepInstBase, execPure2, evalOperand, isTerminator]
      rw [hrb]
      obtain ⟨as', hrun, hterm⟩ := addStop_runAsm_core (lo := lo)
        (offsetToPc := (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).2) hvrel hpc0
      have hwe : (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1.length
          - pcOfLabel (asmResolve (executePlan (generateFnPlan addStopFn 0 0).get!.1)).1 addStopBB.label = 5 := by decide
      refine ⟨as', runAsm_le_of_ne_ok (fun _ => by simp) (by omega) hrun, hterm⟩

/-- **Whole-function capstone via `codegen_correct_canonical` (`entry: SELFDESTRUCT`).** A terminator
    other than STOP that also halts (with a `PUSH recipient` body from the plan): the block sim is
    `selfdestruct_runAsm_core` (`[JUMPDEST; PUSH 0; SELFDESTRUCT]` → AsmHalt) at the canonical budget
    `prog.length - pcOfLabel = 3 ≤ N`. -/
theorem codegen_correct_canonical_selfdestruct {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
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
  have hfnready : ∀ bb ∈ sdFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [sdFn, List.mem_singleton] at hbb; subst hbb
    simp only [sdBB, List.mem_singleton] at hinst; subst hinst; unfold codegenReadyInst; decide
  have hgen : generateFnPlan sdFn 0 0
      = some ((generateFnPlan sdFn 0 0).get!.1, (generateFnPlan sdFn 0 0).get!.2) := rfl
  refine codegen_correct_canonical (fuel := 10) (ctx := sdCtx) (fn := sdFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := (generateFnPlan sdFn 0 0).get!.1)
    (psFinal := (generateFnPlan sdFn 0 0).get!.2) (entry := sdBB)
    hgen rfl rfl rfl rfl rfl hfnready rfl (pcOfLabel_entry_zero rfl hfnready hgen) haspc ?_ hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN _hnh
  have hbb : bb = sdBB := by
    rw [show sdFn.blocks = [sdBB] from rfl, lookupBlock] at hlk
    simpa using List.mem_of_find?_eq_some hlk
  subst hbb
  have hpc0 : asm.pc = 0 := by rw [hpc]; decide
  have hps : psOfFn (fnPlanFuel sdFn) sdFn 0 0 sdBB.label = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  rw [hps] at hvrel
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, sdBB, sdInst]
  | succ k =>
    have hstep : stepInstBase ({ id := 0, opcode := Opcode.SELFDESTRUCT, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := [] } : Instruction) { s with instIdx := 0 }
        = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) :=
      stepInstBase_selfdestruct rfl rfl rfl
    have hrb : runBlock (k+1) sdCtx sdBB s
        = ExecResult.Halt (haltState (selfdestruct (UInt256.ofNat 0) { s with instIdx := 0 })) := by
      simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, sdBB, sdInst, hstep]
    rw [hrb]
    obtain ⟨as', hrun, hterm⟩ := selfdestruct_runAsm_core (lo := lo)
      (offsetToPc := (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).2) hvrel hpc0
    have hwe : (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1.length
        - pcOfLabel (asmResolve (executePlan (generateFnPlan sdFn 0 0).get!.1)).1 sdBB.label = 3 := by decide
    refine ⟨as', runAsm_le_of_ne_ok (fun _ => by simp) (by omega) hrun, hterm⟩






/-- **Multi-block suppliability witness for `codegen_correct_sched`.** The 2-block function
    `main: entry: JMP next / next: STOP` instantiated through the budget-ranked bridge. Unlike the
    single-block STOP witness, here the asm budget genuinely **decreases** across blocks: the rank
    `wOf` (entry ↦ 5, next ↦ 2) satisfies the decrease `wOf next + 3 ≤ wOf entry` consumed by the JMP,
    so the next block's STOP halt is discharged at the *reduced* budget `N - 3 ≥ 2`. The JMP-continue
    clause is `wellsched_jmp_sched_ok_continue` fed by `hentryAsm_bare_jmp`; the STOP halt is
    `hasm_stop` at budget `N`. Demonstrates the full budget-ranked scheduling assembly on a real CFG. -/
theorem codegen_correct_jmp_stop_sched {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 jmpStopCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1.length
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan jmpStopFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_sched (fuel := 10) (ctx := jmpStopCtx) (fn := jmpStopFn)
    (fnEom := 0) (lblCtr := 0) (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan jmpStopFn 0 0).get!.1) (psFinal := (generateFnPlan jmpStopFn 0 0).get!.2)
    (pcOf := fun l => if l = "next" then 3 else 0) (psOf := fun _ => initPlanState 0)
    (wOf := fun l => if l = "next" then 2 else 5)
    rfl rfl rfl rfl ?_ (bb0 := jmpEntryBB) rfl haspc (by decide) hvshalt hrel
  intro bb s asm N f' hlk hpc hvrel hwN hnh
  have hbb2 : bb = jmpEntryBB ∨ bb = stopNextBB := by
    rw [show jmpStopFn.blocks = [jmpEntryBB, stopNextBB] from rfl, lookupBlock] at hlk
    have h := List.mem_of_find?_eq_some hlk
    simpa using h
  rcases hbb2 with hbb | hbb
  · -- entry block: JMP
    subst hbb
    have hpc0 : asm.pc = 0 := hpc.trans (by rfl)
    have hwN5 : (5 : Nat) ≤ N := by
      have h5 : (if jmpEntryBB.label = "next" then (2 : Nat) else 5) = 5 := rfl
      omega
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, jmpEntryBB, jmpInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx jmpEntryBB s
          = ExecResult.OK (jumpTo "next" { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jmpEntryBB, jmpInst,
          stepInstBase, isTerminator, jumpTo, hnh]
      rw [hrb]
      have hnothalt : (jumpTo "next" { s with instIdx := 0 }).halted = false := by simp [jumpTo, hnh]
      simp only [hnothalt, Bool.false_eq_true, if_false]
      have hbLabel : asmBlockAt jmpProg asm.pc (executePlan [StackOp.SOLabel "entry"]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 1 := hj; interval_cases j; rfl
      have hpc1 : asm.pc + 1 < jmpProg.length := by rw [hpc0]; decide
      have hpush : jmpProg.get ⟨asm.pc + 1, hpc1⟩
          = resolveInst ([("entry", 0), ("next", 5)] : AssocList String Nat) (AsmInst.AsmPushLabel "next") := by
        have e : asm.pc + 1 = 1 := by rw [hpc0]
        conv_lhs => rw [show (⟨asm.pc + 1, hpc1⟩ : Fin jmpProg.length) = ⟨1, by decide⟩ from Fin.ext e]
        rfl
      have hpc2 : asm.pc + 2 < jmpProg.length := by rw [hpc0]; decide
      have hjump : jmpProg.get ⟨asm.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
        have e : asm.pc + 2 = 2 := by rw [hpc0]
        conv_lhs => rw [show (⟨asm.pc + 2, hpc2⟩ : Fin jmpProg.length) = ⟨2, by decide⟩ from Fin.ext e]
        rfl
      obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
        hentryAsm_bare_jmp (offsets := ([("entry", 0), ("next", 5)] : AssocList String Nat))
          (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat)) (off := 5) (idx := 3)
          hvrel hbLabel hpc1 hpush (by decide) (by decide) hpc2 hjump (by decide)
      exact wellsched_jmp_sched_ok_continue (fn := jmpStopFn)
        (pcOf := fun l => if l = "next" then 3 else 0) (psOf := fun _ => initPlanState 0)
        (wOf := fun l => if l = "next" then 2 else 5) (bb := jmpEntryBB) (bb' := stopNextBB)
        hrunE hrelMid hpcMid (by omega) (by rfl) rfl rfl (by rfl)
  · -- next block: STOP (at reduced budget)
    subst hbb
    have hpc3 : asm.pc = 3 := hpc.trans (by rfl)
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, stopNextBB, stopInst]
    | succ k =>
      have hrb : runBlock (k+1) jmpStopCtx stopNextBB s
          = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
        simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, stopNextBB, stopInst, stepInstBase]
      rw [hrb]
      have hblockT : asmBlockAt jmpProg asm.pc (executePlan [StackOp.SOLabel "next", StackOp.SOEmit "STOP"]) := by
        rw [hpc3]; refine ⟨by decide, fun j hj => ?_⟩; have hj' : j < 2 := hj; interval_cases j <;> rfl
      exact hasm_stop (offsetToPc := ([(5, 3), (0, 0)] : AssocList Nat Nat))
        (vs := { s with instIdx := 0 }) (budget := N) hvrel hblockT
        (by have h2 : (if stopNextBB.label = "next" then (2 : Nat) else 5) = 2 := rfl; omega)

def paramX : Instruction :=
  { id := 0, opcode := Opcode.PARAM, operands := [Operand.Lit (UInt256.ofNat 0)], outputs := ["x"] }
def paramY : Instruction :=
  { id := 1, opcode := Opcode.PARAM, operands := [Operand.Lit (UInt256.ofNat 1)], outputs := ["y"] }

/-- **Venom-side PARAM loading.** Threading the two-`PARAM` prefix loads `params[0]`/`params[1]` into
    the output variables `x`/`y` (advancing `instIdx` to 2) — the concrete instance of the Venom-side
    param layer that makes a var-reading body's inputs *defined*. -/
theorem execBodyThread_paramXY {s : VenomState}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    execBodyThread [paramX, paramY] 0 s
      = some { updateVar "y" (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
                 (updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s)
                 with instIdx := 2 } := by
  simp only [execBodyThread]
  rw [stepInstBase_param (inst := paramX) (vs := s) rfl rfl rfl hi0]
  show execBodyThread [paramY] 1
      { updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s with instIdx := 0 + 1 } = _
  simp only [execBodyThread]
  rw [stepInstBase_param (inst := paramY)
      (vs := { updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s with instIdx := 0 + 1 })
      rfl rfl rfl hi1]
  rfl


def paramSstoreBB : BasicBlock :=
  { label := "entry", instructions := [paramX, paramY, sstoreInst, stopInst] }

/-- **Venom-side param layer (whole block).** `runBlock` on a `PARAM`-prefixed var-reading block loads
    the params (`execBodyThread_paramXY`), then runs the body — the SSTORE reads the now-defined `x`/`y`
    (= `params[0]`/`params[1]`) and STOP halts. Shows a param entry's Venom execution makes its
    var-reading body's inputs defined, so the body reads the passed arguments. -/
theorem runBlock_paramSstore_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    runBlock (2 + (restFuel + 2)) ctx paramSstoreBB s
      = ExecResult.Halt (haltState
          { sstore (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩)
              (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
              { updateVar "y" (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
                  (updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s) with instIdx := 2 }
            with instIdx := 2 + 1 }) := by
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hsLidx : sL.instIdx = 2 := rfl
  have hstepS : stepInstBase sstoreInst sL = ExecResult.OK (sstore v0 v1 sL) := by
    refine stepInstBase_sstore rfl rfl ?_ ?_
    · show lookupVar "x" sL = some v0
      rw [hsL]
      show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 s)) = some v0
      rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
    · show lookupVar "y" sL = some v1
      rw [hsL]
      show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 s)) = some v1
      rw [lookupVar_updateVar_self]
  unfold runBlock
  rw [show paramSstoreBB.instructions = paramX :: [paramY, sstoreInst, stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 2)) ctx paramSstoreBB
      { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx paramSstoreBB (restFuel + 2) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  show execBlock ((restFuel + 1) + 1) ctx paramSstoreBB sL = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx paramSstoreBB sL (sstore v0 v1 sL) sstoreInst
        (by rw [hsLidx]; rfl) hstepS (by decide)]
  rw [execBlock_step_halt restFuel ctx paramSstoreBB
        { sstore v0 v1 sL with instIdx := sL.instIdx + 1 }
        (haltState { sstore v0 v1 sL with instIdx := sL.instIdx + 1 }) stopInst
        (by rw [hsLidx]; rfl) (by simp only [stepInstBase, stopInst])]


def paramSstoreFn : IrFunction := { name := "main", blocks := [paramSstoreBB] }
def paramSstoreCtx : VenomContext := { functions := [paramSstoreFn], entry := some "main" }

/-- **Whole-function real-codegen var-passing capstone** (joins the two param halves). For the *real*
    compiled `[PARAM x; PARAM y; SSTORE x y; STOP]`, `runContext` corresponds to `runAsm` on the actual
    resolved program `[JUMPDEST; SWAP1; SSTORE; STOP]`, halting with the final-state relation. The Venom
    side loads the params and stores `sstore params[0] params[1]` (`runBlock_paramSstore_venom`); the asm
    side runs the reorder+store to `sstore vx vy` (`asm_paramSstore_sim`); under caller-consistency
    `params[i] = vx/vy` the two stores agree, and loading preserves accounts/transient/returndata/logs so
    the terminal relations coincide (defeq). The first end-to-end var-passing sim over the *real* codegen. -/
theorem codegen_correct_paramSstore {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hp0 : vs.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ = vx)
    (hp1 : vs.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ = vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 paramSstoreCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 4
         (asmResolve (executePlan (generateFnPlan paramSstoreFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan paramSstoreFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hrc : runContext 10 paramSstoreCtx vs = runBlocks 10 paramSstoreCtx paramSstoreFn eS := by
    simp only [runContext, show paramSstoreCtx.entry = some "main" from rfl,
      show lookupFunction "main" paramSstoreCtx.functions = some paramSstoreFn from rfl,
      runFunction, show fnEntryLabel paramSstoreFn = some "entry" from rfl, heS]
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  have hpe0 : eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩ = vx := hp0
  have hpe1 : eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩ = vy := hp1
  set hltS : VenomState := haltState
    { sstore (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩) (eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩)
        { updateVar "y" (eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩)
            (updateVar "x" (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩) eS) with instIdx := 2 }
      with instIdx := 2 + 1 } with hHlt
  have hblkrun : runBlock 9 paramSstoreCtx paramSstoreBB eS = ExecResult.Halt hltS := by
    rw [hHlt]
    have h := runBlock_paramSstore_venom (ctx := paramSstoreCtx) (s := eS) (restFuel := 5) hi0' hi1'
    rwa [show (2 + (5 + 2) : Nat) = 9 from rfl] at h
  have hrbs : runBlocks 10 paramSstoreCtx paramSstoreFn eS = ExecResult.Halt hltS := by
    rw [runBlocks]
    simp only [show lookupBlock eS.currentBb paramSstoreFn.blocks = some paramSstoreBB from rfl, hblkrun]
  rw [hrc, hrbs]
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramSstore_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramSstoreFn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef) hrel haspc
  refine ⟨as', ?_, ?_⟩
  · rw [show (asmResolve (executePlan (generateFnPlan paramSstoreFn 0 0).get!.1)).1
        = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "SSTORE", AsmInst.AsmOp "STOP"]
        from rfl]
    exact hrunAsm
  · rw [hHlt, hpe0, hpe1]; exact hterm


/-- ADD consuming the two loaded params `x, y` (last use), producing `c`. Reuses `paramX`/`paramY`
    (which load `params[0]`/`params[1]` into `x`/`y`), so the whole Venom param-loading layer is shared
    with the SSTORE capstone; only the body op differs. -/
def addXYInst : Instruction :=
  { id := 2, opcode := Opcode.ADD, operands := [Operand.Var "x", Operand.Var "y"], outputs := ["c"] }
def paramAddBB : BasicBlock :=
  { label := "entry", instructions := [paramX, paramY, addXYInst, stopInst] }
def paramAddFn : IrFunction := { name := "main", blocks := [paramAddBB] }
def paramAddCtx : VenomContext := { functions := [paramAddFn], entry := some "main" }

/-- **Venom-side param+ADD block.** `runBlock` on `[PARAM x; PARAM y; ADD x y → c; STOP]` loads the
    params (`execBodyThread_paramXY`), then ADD reads the now-defined `x`/`y` (= `params[0]`/`params[1]`)
    into `c := params[0] + params[1]`, and STOP halts. The binop analog of `runBlock_paramSstore_venom`. -/
theorem runBlock_paramAdd_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    runBlock (2 + (restFuel + 2)) ctx paramAddBB s
      = ExecResult.Halt (haltState
          { updateVar "c" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩
              + s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
              { updateVar "y" (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
                  (updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s) with instIdx := 2 }
            with instIdx := 2 + 1 }) := by
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hsLidx : sL.instIdx = 2 := rfl
  have hxL : lookupVar "x" sL = some v0 := by
    rw [hsL]; show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 s)) = some v0
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hyL : lookupVar "y" sL = some v1 := by
    rw [hsL]; show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 s)) = some v1
    rw [lookupVar_updateVar_self]
  have hstepA : stepInstBase addXYInst sL = ExecResult.OK (updateVar "c" (v0 + v1) sL) := by
    simp only [stepInstBase, addXYInst, execPure2, evalOperand, hxL, hyL]
  unfold runBlock
  rw [show paramAddBB.instructions = paramX :: [paramY, addXYInst, stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 2)) ctx paramAddBB
      { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx paramAddBB (restFuel + 2) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  show execBlock ((restFuel + 1) + 1) ctx paramAddBB sL = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx paramAddBB sL (updateVar "c" (v0 + v1) sL) addXYInst
        (by rw [hsLidx]; rfl) hstepA (by decide)]
  rw [execBlock_step_halt restFuel ctx paramAddBB
        { updateVar "c" (v0 + v1) sL with instIdx := sL.instIdx + 1 }
        (haltState { updateVar "c" (v0 + v1) sL with instIdx := sL.instIdx + 1 }) stopInst
        (by rw [hsLidx]; rfl) (by simp only [stepInstBase, stopInst])]

/-- **Asm side of the param+ADD function.** The resolved program `[JUMPDEST; ADD; STOP]` runs from the
    entry var-layout state (args on the stack) to `AsmHalt`: JUMPDEST (`soLabel_sim`), then ADD pops the
    two args and pushes their sum (`emit_binop_sim`, commutative so no reorder), then STOP halts. ADD only
    writes a stack var, invisible to `venomAsmTerminalRel` (accounts/transient/returndata/logs), so the
    terminal relation follows from the post-ADD relation. -/
theorem asm_paramAdd_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 3 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (updateVar "c" (vy + vx) vs) as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  -- step 1: JUMPDEST at pc 0
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  -- step 2: ADD at pc 1 — extract as1.stack = vy :: vx :: rest (plan stack [x, y], TOS = y)
  have hstk1 : ∃ rest, as1.stack = vy :: vx :: rest :=
    asmStack_top2_of_planStackRel hrel1.1 (by rw [hpsE]; decide) rfl rfl hydef hxdef
  obtain ⟨rest, hstk1'⟩ := hstk1
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "ADD"]) := by
    rw [hpc1']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hfresh : ¬ (Operand.Var "c") ∈ psE.stack := by rw [hpsE]; decide
  have hspill : AssocList.lookup Operand Nat psE.spilled (Operand.Var "c") = none := by
    rw [hpsE]; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_binop_sim (offsetToPc := offsetToPc) (f := (· + ·)) hrel1 hstk1' hfresh hspill hblock1
      (fun h hg => asmStep_add_ok h hg)
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  -- step 3: STOP at pc 2
  have hlt2 : as2.pc < prog.length := by rw [hpc2']; decide
  have hget2 : prog.get ⟨as2.pc, hlt2⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as2.pc, hlt2⟩ : Fin prog.length) = ⟨2, by decide⟩ from Fin.ext hpc2']; rfl
  refine ⟨asmNext as2, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2]
    exact runAsm_stop 0 hlt2 hget2
  · have hterm := venomAsmRel_terminal lo _ _ _ hrel2
    -- as' = asmNext as2 preserves accounts/etc; venomAsmTerminalRel is pc-independent
    exact hterm


/-- **Single-block whole-function halt reduction.** For a one-block function `fn = [entry]` that is the
    context's entry, if the entry block `runBlock`s to `Halt hs` (from the param-entry state), then
    `runContext` halts with the same `hs`. The reusable runContext↔runBlock bridge: any single-block
    halting capstone `rw`s this, then only reasons about the asm side. -/
theorem runContext_singleBlock_halt
    {ctx : VenomContext} {fn : IrFunction} {entry : BasicBlock} {vs hs : VenomState}
    (hctx : ctx = ⟨[fn], some fn.name⟩)
    (hblocks : fn.blocks = [entry])
    (hrb : runBlock 9 ctx entry { vs with prevBb := none, currentBb := entry.label, instIdx := 0 }
        = ExecResult.Halt hs) :
    runContext 10 ctx vs = ExecResult.Halt hs := by
  set eS : VenomState := { vs with prevBb := none, currentBb := entry.label, instIdx := 0 } with heS
  have hlkf : lookupFunction fn.name [fn] = some fn := by simp [lookupFunction]
  have hlbl : fnEntryLabel fn = some entry.label := by rw [fnEntryLabel, hblocks]; rfl
  have hlkb : lookupBlock eS.currentBb fn.blocks = some entry := by
    rw [hblocks]; simp only [heS]; simp [lookupBlock]
  have hrc : runContext 10 ctx vs = runBlocks 10 ctx fn eS := by
    simp only [hctx, runContext, hlkf, runFunction, hlbl, heS]
  have hrbs : runBlocks 10 ctx fn eS = ExecResult.Halt hs := by
    rw [runBlocks]; simp only [hlkb, hrb]
  rw [hrc, hrbs]

/-- **Single-block whole-function halt capstone** (terminator/body-agnostic). Combines
    `runContext_singleBlock_halt` (Venom side) with the asm side reaching `AsmHalt` with matching
    terminal fields to conclude the whole-function `finalStateRel`. Any single-block halting capstone
    routes through this -- the caller supplies `hrb` and the asm sim. -/
theorem codegen_correct_singleBlock_halt
    {ctx : VenomContext} {fn : IrFunction} {entry : BasicBlock}
    {vs hs : VenomState} {as as' : AsmState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {N : Nat}
    (hctx : ctx = ⟨[fn], some fn.name⟩)
    (hblocks : fn.blocks = [entry])
    (hrb : runBlock 9 ctx entry { vs with prevBb := none, currentBb := entry.label, instIdx := 0 }
        = ExecResult.Halt hs)
    (hrun : runAsm N offsetToPc prog as = AsmResult.AsmHalt as')
    (hterm : venomAsmTerminalRel hs as') :
    (match runContext 10 ctx vs with
     | ExecResult.Halt vs' => ∃ a, runAsm N offsetToPc prog as = AsmResult.AsmHalt a ∧ finalStateRel vs' a
     | _ => True) := by
  rw [runContext_singleBlock_halt hctx hblocks hrb]
  exact ⟨as', hrun, hterm⟩

/-- **Whole-function var-passing binop capstone.** For the *real* compiled
    `[PARAM x; PARAM y; ADD x y → c; STOP]`, `runContext` corresponds to `runAsm` on the actual resolved
    program `[JUMPDEST; ADD; STOP]`, halting with the final-state relation. The Venom side loads the
    params and computes `c := params[0] + params[1]` (`runBlock_paramAdd_venom`); the asm side runs the
    commutative ADD (no reorder needed, `asm_paramAdd_sim`); ADD touches only a stack var, so the terminal
    relation (accounts/transient/returndata/logs) is preserved. The binop analog of
    `codegen_correct_paramSstore` — the first whole-function var-passing *binop* sim over the real codegen. -/
theorem codegen_correct_paramAdd {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 paramAddCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 3
         (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 }
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  set hltS : VenomState := haltState
    { updateVar "c" (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩
        + eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩)
        { updateVar "y" (eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩)
            (updateVar "x" (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩) eS) with instIdx := 2 }
      with instIdx := 2 + 1 } with hHlt
  have hblkrun : runBlock 9 paramAddCtx paramAddBB eS = ExecResult.Halt hltS := by
    rw [hHlt]
    have h := runBlock_paramAdd_venom (ctx := paramAddCtx) (s := eS) (restFuel := 5) hi0' hi1'
    rwa [show (2 + (5 + 2) : Nat) = 9 from rfl] at h
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramAdd_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef) hrel haspc
  -- lift the entry block's halt to the whole function via the reusable single-block bridge
  exact codegen_correct_singleBlock_halt (fn := paramAddFn) (entry := paramAddBB) (N := 3)
    (prog := (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).1)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).2)
    rfl rfl hblkrun
    (by rw [show (asmResolve (executePlan (generateFnPlan paramAddFn 0 0).get!.1)).1
          = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "STOP"] from rfl]; exact hrunAsm)
    (by rw [hHlt]; exact hterm)


/-! ## Whole-function environment-push capstone: `[CALLER c; STOP]`

The first whole-function `codegen_correct` over the real codegen for a **0-input environment opcode**
(the env-push analog of `codegen_correct_paramAdd`). Exercises the new `bodyStep_caller`/`emit_caller_sim`
env-push layer end-to-end: a genuine body instruction (CALLER) lowering correctly, threaded through the
same `codegen_correct_singleBlock_halt` bridge as the binop capstone. -/

def callerInst : Instruction :=
  { id := 0, opcode := Opcode.CALLER, operands := [], outputs := ["c"] }
def callerBB : BasicBlock := { label := "entry", instructions := [callerInst, stopInst] }
def callerFn : IrFunction := { name := "main", blocks := [callerBB] }
def callerCtx : VenomContext := { functions := [callerFn], entry := some "main" }

/-- **Venom side.** `runBlock` on `[CALLER c; STOP]` writes `c := caller` (`execRead0`, a non-terminator
    step) then STOP halts. The 0-input environment-opcode counterpart of `runBlock_paramAdd_venom`. -/
theorem runBlock_callerStop_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat} :
    runBlock (restFuel + 2) ctx callerBB s
      = ExecResult.Halt (haltState
          { updateVar "c" (addressToWord s.callCtx.caller) { s with instIdx := 0 }
            with instIdx := 1 }) := by
  set s0 : VenomState := { s with instIdx := 0 } with hs0
  set sC : VenomState := updateVar "c" (addressToWord s0.callCtx.caller) s0 with hsC
  have hidx0 : s0.instIdx = 0 := by rw [hs0]
  unfold runBlock
  rw [show callerBB.instructions = callerInst :: [stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s callerInst _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi callerInst _ (by decide)]
  show execBlock (restFuel + 2) ctx callerBB s0 = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx callerBB s0 sC callerInst
        (by rw [hidx0]; rfl) (by rw [hsC]; rfl) (by decide)]
  rw [execBlock_step_halt restFuel ctx callerBB
        { sC with instIdx := s0.instIdx + 1 }
        (haltState { sC with instIdx := s0.instIdx + 1 }) stopInst
        (by rw [hidx0]; rfl) (by simp only [stepInstBase, stopInst])]

/-- **Asm side.** The resolved `[JUMPDEST; CALLER; STOP]` runs from the entry (empty-stack) layout to
    `AsmHalt` — `soLabel_sim` + `emit_caller_sim` (the env-push emit) + `runAsm_stop` — terminal-related
    to the Venom state that wrote `c := caller` (CALLER touches only a stack var, invisible to the
    terminal relation). The env-push analog of `asm_paramAdd_sim`, one step shorter (no stack input). -/
theorem asm_callerStop_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat}
    (hrel : venomAsmRel lo (initPlanState 0) vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 3 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLER", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (updateVar "c" (addressToWord vs.callCtx.caller) vs) as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLER", AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := initPlanState 0 with hpsE
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALLER"]) := by
    rw [hpc1']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hfresh : ¬ (Operand.Var "c") ∈ psE.stack := by rw [hpsE]; decide
  have hspill : AssocList.lookup Operand Nat psE.spilled (Operand.Var "c") = none := by
    rw [hpsE]; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_caller_sim (offsetToPc := offsetToPc) hrel1 hfresh hspill hblock1
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  have hlt2 : as2.pc < prog.length := by rw [hpc2']; decide
  have hget2 : prog.get ⟨as2.pc, hlt2⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as2.pc, hlt2⟩ : Fin prog.length) = ⟨2, by decide⟩ from Fin.ext hpc2']; rfl
  refine ⟨asmNext as2, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2]
    exact runAsm_stop 0 hlt2 hget2
  · exact venomAsmRel_terminal lo _ _ _ hrel2

/-- **Whole-function environment-push capstone.** For the *real* compiled `[CALLER c; STOP]`,
    `runContext` corresponds to `runAsm` on the actual resolved program `[JUMPDEST; CALLER; STOP]`,
    halting with the final-state relation. The env-push analog of `codegen_correct_paramAdd`: the first
    whole-function sim over the real codegen for a 0-input environment opcode, exercising the new
    `emit_caller_sim`/`bodyStep_caller` layer. -/
theorem codegen_correct_caller {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hrel : venomAsmRel lo (initPlanState 0)
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 callerCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 3
         (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 }
  have hblkrun : runBlock 9 callerCtx callerBB eS
      = ExecResult.Halt (haltState
          { updateVar "c" (addressToWord eS.callCtx.caller) { eS with instIdx := 0 } with instIdx := 1 }) :=
    runBlock_callerStop_venom (ctx := callerCtx) (s := eS) (restFuel := 7)
  obtain ⟨as', hrunAsm, hterm⟩ := asm_callerStop_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).2) hrel haspc
  exact codegen_correct_singleBlock_halt (fn := callerFn) (entry := callerBB) (N := 3)
    (prog := (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).1)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).2)
    rfl rfl hblkrun
    (by rw [show (asmResolve (executePlan (generateFnPlan callerFn 0 0).get!.1)).1
          = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLER", AsmInst.AsmOp "STOP"] from rfl]
        exact hrunAsm)
    hterm


/-- **Venom-side param+commutative-binop block, opcode-generic.** Generalizes `runBlock_paramAdd_venom`
    from ADD to any binop whose step is `execPure2 f` with operands `[Var x, Var y]`, output `[c]`.
    `runBlock` on `[PARAM x; PARAM y; <binop> x y → c; STOP]` loads the params then computes
    `c := f params[0] params[1]` and halts. -/
theorem runBlock_paramBinop_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    {binopInst : Instruction} {f : bytes32 → bytes32 → bytes32}
    (hops : binopInst.operands = [Operand.Var "x", Operand.Var "y"])
    (houts : binopInst.outputs = ["c"])
    (hnonterm : isTerminator binopInst.opcode = false)
    (hstepf : ∀ v, stepInstBase binopInst v = execPure2 f binopInst v)
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    runBlock (2 + (restFuel + 2)) ctx
        { label := "entry", instructions := [paramX, paramY, binopInst, stopInst] } s
      = ExecResult.Halt (haltState
          { updateVar "c" (f (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩)
              (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩))
              { updateVar "y" (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
                  (updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s) with instIdx := 2 }
            with instIdx := 2 + 1 }) := by
  set bb : BasicBlock := { label := "entry", instructions := [paramX, paramY, binopInst, stopInst] } with hbb
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hsLidx : sL.instIdx = 2 := rfl
  have hxL : lookupVar "x" sL = some v0 := by
    rw [hsL]; show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 s)) = some v0
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hyL : lookupVar "y" sL = some v1 := by
    rw [hsL]; show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 s)) = some v1
    rw [lookupVar_updateVar_self]
  have hstepB : stepInstBase binopInst sL = ExecResult.OK (updateVar "c" (f v0 v1) sL) := by
    rw [hstepf sL]; simp only [execPure2, hops, houts, evalOperand, hxL, hyL]
  unfold runBlock
  rw [show bb.instructions = paramX :: [paramY, binopInst, stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 2)) ctx bb { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx bb (restFuel + 2) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  show execBlock ((restFuel + 1) + 1) ctx bb sL = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx bb sL (updateVar "c" (f v0 v1) sL) binopInst
        (by rw [hsLidx]; rfl) hstepB hnonterm]
  rw [execBlock_step_halt restFuel ctx bb
        { updateVar "c" (f v0 v1) sL with instIdx := sL.instIdx + 1 }
        (haltState { updateVar "c" (f v0 v1) sL with instIdx := sL.instIdx + 1 }) stopInst
        (by rw [hsLidx]; rfl) (by simp only [stepInstBase, stopInst])]

/-- **Asm side of a param+commutative-binop function, opcode-generic.** Generalizes `asm_paramAdd_sim`:
    the resolved program `[JUMPDEST; <name>; STOP]` runs from the entry var-layout to `AsmHalt` via
    `soLabel_sim` + `emit_binop_sim` (already opcode-parametric) + `runAsm_stop`; the binop writes only
    a stack var, invisible to the terminal relation. -/
theorem asm_paramBinop_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx vy : bytes32} {name : String} {f : bytes32 → bytes32 → bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0)
    (hasmdisp : ∀ (s : AsmState) (h : s.pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"].length),
        [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"].get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"] s = asmBinop f s) :
    ∃ as', runAsm 3 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (updateVar "c" (f vy vx) vs) as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  have hlen3 : prog.length = 3 := rfl
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]
    refine ⟨by rw [hlen3]; show (0:Nat) + 1 ≤ 3; omega, fun j hj => ?_⟩
    have hj1 : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  have hstk1 : ∃ rest, as1.stack = vy :: vx :: rest :=
    asmStack_top2_of_planStackRel hrel1.1 (by rw [hpsE]; decide) rfl rfl hydef hxdef
  obtain ⟨rest, hstk1'⟩ := hstk1
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit name]) := by
    rw [hpc1']
    refine ⟨by rw [hlen3]; show (1:Nat) + 1 ≤ 3; omega, fun j hj => ?_⟩
    have hj1 : j < 1 := hj; interval_cases j; rfl
  have hfresh : ¬ (Operand.Var "c") ∈ psE.stack := by rw [hpsE]; decide
  have hspill : AssocList.lookup Operand Nat psE.spilled (Operand.Var "c") = none := by
    rw [hpsE]; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_binop_sim (offsetToPc := offsetToPc) (f := f) hrel1 hstk1' hfresh hspill hblock1
      (fun h hg => hasmdisp as1 h hg)
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  have hlt2 : as2.pc < prog.length := by rw [hpc2', hlen3]; omega
  have hget2 : prog.get ⟨as2.pc, hlt2⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as2.pc, hlt2⟩ : Fin prog.length) = ⟨2, by rw [hlen3]; omega⟩ from Fin.ext hpc2']; rfl
  refine ⟨asmNext as2, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2]
    exact runAsm_stop 0 hlt2 hget2
  · exact venomAsmRel_terminal lo _ _ _ hrel2

/-- **Whole-function var-passing capstone, generic over the commutative binop.** For *any* commutative
    binop `main: [PARAM x; PARAM y; <binop> x y → c; STOP]` (operands `[Var x, Var y]`, output `[c]`,
    step `execPure2 f`, resolving to `[JUMPDEST; <name>; STOP]`), `runContext` corresponds to `runAsm`,
    halting with `finalStateRel`. Generalizes `codegen_correct_paramAdd` from ADD to the whole
    commutative-binop family (MUL, AND, OR, XOR, EQ, …). The caller discharges the resolved-program
    shape `hprog` and asm dispatch `hasmdisp` by `rfl`/the opcode's `asmStep_*_ok` lemma. -/
theorem codegen_correct_paramCommBinop
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {vx vy : bytes32}
    {binopInst : Instruction} {name : String} {f : bytes32 → bytes32 → bytes32}
    {fn : IrFunction} {ctx : VenomContext}
    (hfn : fn = ⟨"main", [⟨"entry", [paramX, paramY, binopInst, stopInst]⟩]⟩)
    (hctx : ctx = ⟨[fn], some "main"⟩)
    (hops : binopInst.operands = [Operand.Var "x", Operand.Var "y"])
    (houts : binopInst.outputs = ["c"])
    (hnonterm : isTerminator binopInst.opcode = false)
    (hstepf : ∀ v, stepInstBase binopInst v = execPure2 f binopInst v)
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0)
    (hprog : (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1
        = [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"])
    (hasmdisp : ∀ (s : AsmState)
        (h : s.pc < [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"].length),
        [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"].get ⟨s.pc, h⟩
          = AsmInst.AsmOp name →
        asmStep (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2
          [AsmInst.AsmLabel "entry", AsmInst.AsmOp name, AsmInst.AsmOp "STOP"] s = asmBinop f s) :
    (match runContext 10 ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 3
         (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set entryBlock : BasicBlock :=
    { label := "entry", instructions := [paramX, paramY, binopInst, stopInst] } with hEntry
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  set hltS : VenomState := haltState
    { updateVar "c" (f (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩)
        (eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩))
        { updateVar "y" (eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩)
            (updateVar "x" (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩) eS) with instIdx := 2 }
      with instIdx := 2 + 1 } with hHlt
  have hblkrun : runBlock 9 ctx entryBlock eS = ExecResult.Halt hltS := by
    rw [hHlt]
    have h := runBlock_paramBinop_venom (ctx := ctx) (s := eS) (restFuel := 5)
      hops houts hnonterm hstepf hi0' hi1'
    rw [show (2 + (5 + 2) : Nat) = 9 from rfl] at h
    exact h
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramBinop_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef)
    hrel haspc hasmdisp
  -- lift the entry block's halt to the whole function via the reusable single-block bridge
  exact codegen_correct_singleBlock_halt (fn := fn) (entry := entryBlock) (N := 3)
    (prog := (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2)
    (by rw [hctx, hfn]) (by rw [hfn]) hblkrun (by rw [hprog]; exact hrunAsm)
    (by rw [hHlt]; exact hterm)

/-- MUL body (a *different* commutative binop than ADD), to instantiate the generic capstone. -/
def mulXYInst : Instruction :=
  { id := 2, opcode := Opcode.MUL, operands := [Operand.Var "x", Operand.Var "y"], outputs := ["c"] }
def paramMulFn : IrFunction :=
  ⟨"main", [⟨"entry", [paramX, paramY, mulXYInst, stopInst]⟩]⟩

/-- **Concrete instantiation of the generic capstone at MUL.** Confirms `codegen_correct_paramCommBinop`
    is dischargeable at an opcode other than ADD: `hprog` by `rfl`, `hasmdisp` by `asmStep_mul_ok`. -/
theorem codegen_correct_paramMul {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 ⟨[paramMulFn], some "main"⟩ vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 3
         (asmResolve (executePlan (generateFnPlan paramMulFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan paramMulFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_paramCommBinop (binopInst := mulXYInst) (name := "MUL") (f := (· * ·))
    rfl rfl rfl rfl (by decide) (fun v => rfl) hi0 hi1 hxdef hydef hrel haspc
    rfl (fun s h hg => asmStep_mul_ok h hg)


/-- ADD then NOT: a two-instruction body with output→input dataflow (`c := ADD x y ; d := NOT c`),
    the first concrete *multi-instruction* body. Reuses `paramX`/`paramY`. -/
def addI2 : Instruction :=
  { id := 2, opcode := Opcode.ADD, operands := [Operand.Var "x", Operand.Var "y"], outputs := ["c"] }
def notI2 : Instruction :=
  { id := 3, opcode := Opcode.NOT, operands := [Operand.Var "c"], outputs := ["d"] }
def paramAddNotBB : BasicBlock :=
  { label := "entry", instructions := [paramX, paramY, addI2, notI2, stopInst] }
def paramAddNotFn : IrFunction := ⟨"main", [paramAddNotBB]⟩
def paramAddNotCtx : VenomContext := ⟨[paramAddNotFn], some "main"⟩

/-- **Venom side of the two-instruction body.** `runBlock` on `[PARAM x; PARAM y; c := ADD x y;
    d := NOT c; STOP]` loads the params, computes `c := params[0]+params[1]`, then `d := ~c`, and halts. -/
theorem runBlock_paramAddNot_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    runBlock (2 + (restFuel + 3)) ctx paramAddNotBB s
      = ExecResult.Halt (haltState
          (let v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩
           let v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩
           let sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 }
           { updateVar "d" (~~~ (v0 + v1)) { updateVar "c" (v0 + v1) sL with instIdx := 3 }
               with instIdx := 4 })) := by
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hsLidx : sL.instIdx = 2 := rfl
  have hxL : lookupVar "x" sL = some v0 := by
    rw [hsL]; show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 s)) = some v0
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hyL : lookupVar "y" sL = some v1 := by
    rw [hsL]; show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 s)) = some v1
    rw [lookupVar_updateVar_self]
  set sAdd : VenomState := { updateVar "c" (v0 + v1) sL with instIdx := 3 } with hsAdd
  have hcAdd : lookupVar "c" sAdd = some (v0 + v1) := by
    rw [hsAdd]; show lookupVar "c" (updateVar "c" (v0 + v1) sL) = some (v0 + v1)
    rw [lookupVar_updateVar_self]
  have hstepA : stepInstBase addI2 sL = ExecResult.OK (updateVar "c" (v0 + v1) sL) := by
    show execPure2 (· + ·) addI2 sL = _
    simp only [execPure2, addI2, evalOperand, hxL, hyL]
  have hstepN : stepInstBase notI2 sAdd = ExecResult.OK (updateVar "d" (~~~ (v0 + v1)) sAdd) := by
    show execPure1 (~~~ ·) notI2 sAdd = _
    simp only [execPure1, notI2, evalOperand, hcAdd]
  unfold runBlock
  rw [show paramAddNotBB.instructions = paramX :: [paramY, addI2, notI2, stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 3)) ctx paramAddNotBB { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx paramAddNotBB (restFuel + 3) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  show execBlock ((restFuel + 2) + 1) ctx paramAddNotBB sL = _
  rw [execBlock_step_nonterm (restFuel + 2) ctx paramAddNotBB sL (updateVar "c" (v0 + v1) sL) addI2
        (by rw [hsLidx]; rfl) hstepA (by decide)]
  show execBlock ((restFuel + 1) + 1) ctx paramAddNotBB sAdd = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx paramAddNotBB sAdd (updateVar "d" (~~~ (v0 + v1)) sAdd) notI2
        (by rw [hsAdd]; rfl) hstepN (by decide)]
  rw [execBlock_step_halt restFuel ctx paramAddNotBB
        { updateVar "d" (~~~ (v0 + v1)) sAdd with instIdx := sAdd.instIdx + 1 }
        (haltState { updateVar "d" (~~~ (v0 + v1)) sAdd with instIdx := sAdd.instIdx + 1 }) stopInst
        (by rw [hsAdd]; rfl) (by simp only [stepInstBase, stopInst])]

/-- **Top-1 asm-stack extraction from the plan-stack relation** (the 1-input companion of
    `asmStack_top2_of_planStackRel`). -/
theorem asmStack_top1_of_planStackRel {lo : AssocList String Nat} {vs : VenomState}
    {psStack : List Operand} {asmStack : List bytes32} {op : Operand} {v : bytes32}
    (hrel : planStackRel lo vs psStack asmStack)
    (hlen : 1 ≤ psStack.length)
    (h0 : stackPeek 0 psStack = op)
    (hv : operandVal vs lo op = some v) :
    ∃ rest, asmStack = v :: rest := by
  have hlenEq := hrel.1
  have e0 := planStackRel_peek hrel (dist := 0) (by omega)
  rw [h0, hv] at e0
  have hlenA : 1 ≤ asmStack.length := hlenEq ▸ hlen
  rcases asmStack with _ | ⟨a, t⟩
  · simp at hlenA
  · refine ⟨t, ?_⟩
    have ha : a = v := by simpa using e0.symm
    rw [ha]

/-- **Asm side of the two-instruction body.** `[JUMPDEST; ADD; NOT; STOP]` runs from the entry
    var-layout to `AsmHalt`: `soLabel_sim` + `emit_binop_sim` (ADD, pops 2) + `emit_unop_sim` (NOT,
    pops 1) + `runAsm_stop`; the outputs are stack vars, invisible to the terminal relation. -/
theorem asm_paramAddNot_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 4 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (updateVar "d" (~~~ (vy + vx)) (updateVar "c" (vy + vx) vs)) as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  have hlen4 : prog.length = 4 := rfl
  -- step 1: JUMPDEST
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  -- step 2: ADD (top two = vy, vx)
  have hstk1 : ∃ rest, as1.stack = vy :: vx :: rest :=
    asmStack_top2_of_planStackRel hrel1.1 (by rw [hpsE]; decide) rfl rfl hydef hxdef
  obtain ⟨rest, hstk1'⟩ := hstk1
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "ADD"]) := by
    rw [hpc1']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hfreshC : ¬ (Operand.Var "c") ∈ psE.stack := by rw [hpsE]; decide
  have hspillC : AssocList.lookup Operand Nat psE.spilled (Operand.Var "c") = none := by rw [hpsE]; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_binop_sim (offsetToPc := offsetToPc) (f := (· + ·)) hrel1 hstk1' hfreshC hspillC hblock1
      (fun h hg => asmStep_add_ok h hg)
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  -- step 3: NOT (plan stack after ADD is [Var c]; top = c = vy + vx)
  have hcval : operandVal (updateVar "c" (vy + vx) vs) lo (Operand.Var "c") = some (vy + vx) := by
    simp only [operandVal]; exact lookupVar_updateVar_self vs "c" (vy + vx)
  have hstk2 : ∃ rest2, as2.stack = (vy + vx) :: rest2 :=
    asmStack_top1_of_planStackRel hrel2.1 (by rw [hpsE]; decide) rfl hcval
  obtain ⟨rest2, hstk2'⟩ := hstk2
  have hblock2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "NOT"]) := by
    rw [hpc2']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hfreshD : ¬ (Operand.Var "d") ∈ ({ psE with stack := stackPush (Operand.Var "c") (stackPop 2 psE.stack) } : PlanState).stack := by
    rw [hpsE]; decide
  have hspillD : AssocList.lookup Operand Nat ({ psE with stack := stackPush (Operand.Var "c") (stackPop 2 psE.stack) } : PlanState).spilled (Operand.Var "d") = none := by
    rw [hpsE]; rfl
  obtain ⟨as3, hrun3, hrel3, hpc3⟩ :=
    emit_unop_sim (offsetToPc := offsetToPc) (f := (~~~ ·)) hrel2 hstk2' hfreshD hspillD hblock2
      (fun h hg => asmStep_not_ok h hg)
  have hpc3' : as3.pc = 3 := by rw [hpc3, hpc2']; rfl
  -- step 4: STOP
  have hlt3 : as3.pc < prog.length := by rw [hpc3', hlen4]; omega
  have hget3 : prog.get ⟨as3.pc, hlt3⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as3.pc, hlt3⟩ : Fin prog.length) = ⟨3, by rw [hlen4]; omega⟩ from Fin.ext hpc3']; rfl
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hr3 : runAsm 1 offsetToPc prog as2 = AsmResult.AsmOK as3 := hrun3
  refine ⟨asmNext as3, ?_, ?_⟩
  · rw [show (4 : Nat) = 1 + (1 + (1 + 1)) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2,
        runAsm_add_ok hr3]
    exact runAsm_stop 0 hlt3 hget3
  · exact venomAsmRel_terminal lo _ _ _ hrel3

/-- **Asm-side fold over a chain of same-unop instructions** (arbitrary length). A straight-line
    consumed body `[o₁ := f cur; o₂ := f o₁; …]` where each op consumes the single top-of-stack var and
    pushes its result. Runs `outs.length` asm steps to `AsmOK`, preserving a `venomAsmRel` whose plan
    stack keeps `psRest` and swaps the top var, and preserving the terminal-relation fields
    (accounts/transient/returndata/logs -- unops touch only stack vars). Chains `emit_unop_sim` by
    induction on `outs`, using `asmStack_top1_of_planStackRel` to expose the top for each step. -/
theorem asm_unopChain_sim {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {f : bytes32 → bytes32} {name : String}
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s) :
    ∀ (outs : List String) (psRest : List Operand) (spl : SpilledMap) (al : SpillAlloc) (lc : Nat)
      (curVar : String) (vc : bytes32) (vs : VenomState) (as : AsmState),
    (∀ o ∈ outs, Operand.Var o ∉ psRest) →
    (∀ o ∈ outs, AssocList.lookup Operand Nat spl (Operand.Var o) = none) →
    (curVar :: outs).Nodup →
    (∀ k, k < outs.length → asmBlockAt prog (as.pc + k) (executePlan [StackOp.SOEmit name])) →
    lookupVar curVar vs = some vc →
    venomAsmRel lo ⟨psRest ++ [Operand.Var curVar], spl, al, lc⟩ vs as →
    ∃ (lastVar : String) (vs' : VenomState) (as' : AsmState),
      runAsm outs.length offsetToPc prog as = AsmResult.AsmOK as' ∧
      venomAsmRel lo ⟨psRest ++ [Operand.Var lastVar], spl, al, lc⟩ vs' as' ∧
      as'.pc = as.pc + outs.length ∧
      as.accounts = as'.accounts ∧ as.transient = as'.transient ∧
      as.returndata = as'.returndata ∧ as.logs = as'.logs := by
  intro outs
  induction outs with
  | nil =>
    intro psRest spl al lc curVar vc vs as _ _ _ _ _ hrel
    exact ⟨curVar, vs, as, rfl, hrel, by simp, rfl, rfl, rfl, rfl⟩
  | cons o rest ih =>
    intro psRest spl al lc curVar vc vs as hfresh hspill hnodup hblocks hcur hrel
    -- expose the top value on the asm stack
    have hcval : operandVal vs lo (Operand.Var curVar) = some vc := by
      simp only [operandVal]; exact hcur
    have hstk : ∃ r, as.stack = vc :: r :=
      asmStack_top1_of_planStackRel hrel.1 (by simp) (by
        show stackPeek 0 (psRest ++ [Operand.Var curVar]) = Operand.Var curVar
        simp [stackPeek]) hcval
    obtain ⟨r, hstk'⟩ := hstk
    -- block for the head NOT at as.pc
    have hb0 : asmBlockAt prog as.pc (executePlan [StackOp.SOEmit name]) := by
      have := hblocks 0 (by simp); simpa using this
    have hfreshO : ¬ (Operand.Var o) ∈ (⟨psRest ++ [Operand.Var curVar], spl, al, lc⟩ : PlanState).stack := by
      show ¬ (Operand.Var o) ∈ psRest ++ [Operand.Var curVar]
      intro hmem
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hfresh o (by simp) h
      · have hne : o ≠ curVar := fun he => (List.nodup_cons.mp hnodup).1 (he ▸ List.mem_cons_self)
        exact hne (by injection h)
    have hspillO : AssocList.lookup Operand Nat (⟨psRest ++ [Operand.Var curVar], spl, al, lc⟩ : PlanState).spilled (Operand.Var o) = none :=
      hspill o (by simp)
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
      emit_unop_sim (offsetToPc := offsetToPc) (f := f) hrel hstk' hfreshO hspillO hb0
        (fun h hg => hdisp _ h hg)
    have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
    have hpc1' : as1.pc = as.pc + 1 := by rw [hpc1]; rfl
    -- post-step plan stack = psRest ++ [Var o]; new top var o is defined
    have hpsEq : stackPush (Operand.Var o) (stackPop 1 (psRest ++ [Operand.Var curVar]))
        = psRest ++ [Operand.Var o] := by
      simp [stackPush, stackPop]
    have hrel1' : venomAsmRel lo ⟨psRest ++ [Operand.Var o], spl, al, lc⟩ (updateVar o (f vc) vs) as1 := by
      have hpe : (⟨stackPush (Operand.Var o) (stackPop 1 (psRest ++ [Operand.Var curVar])), spl, al, lc⟩ : PlanState)
          = ⟨psRest ++ [Operand.Var o], spl, al, lc⟩ := by rw [hpsEq]
      rw [← hpe]; exact hrel1
    have hodef : lookupVar o (updateVar o (f vc) vs) = some (f vc) := lookupVar_updateVar_self vs o (f vc)
    -- recurse on `rest`
    have hfresh' : ∀ z ∈ rest, Operand.Var z ∉ psRest := fun z hz => hfresh z (by simp [hz])
    have hspill' : ∀ z ∈ rest, AssocList.lookup Operand Nat spl (Operand.Var z) = none :=
      fun z hz => hspill z (by simp [hz])
    have hnodup' : (o :: rest).Nodup := (List.nodup_cons.mp hnodup).2
    have hblocks' : ∀ k, k < rest.length → asmBlockAt prog (as1.pc + k) (executePlan [StackOp.SOEmit name]) := by
      intro k hk
      have hh := hblocks (k + 1) (by simp only [List.length_cons]; omega)
      rw [hpc1']
      have he : as.pc + 1 + k = as.pc + (k + 1) := by omega
      rw [he]; exact hh
    obtain ⟨lastVar, vs', as', hrunR, hrelR, hpcR, ha, ht, hrd, hlg⟩ :=
      ih psRest spl al lc o (f vc) (updateVar o (f vc) vs) as1 hfresh' hspill' hnodup' hblocks' hodef hrel1'
    have hT := venomAsmRel_terminal lo _ _ _ hrel
    have hacc : as1.accounts = vs.accounts := (venomAsmRel_terminal lo _ _ _ hrel1).1
    have htr : as1.transient = vs.transient := (venomAsmRel_terminal lo _ _ _ hrel1).2.1
    have hrdd : as1.returndata = vs.returndata := (venomAsmRel_terminal lo _ _ _ hrel1).2.2.1
    have hlgg : as1.logs = vs.logs := (venomAsmRel_terminal lo _ _ _ hrel1).2.2.2
    refine ⟨lastVar, vs', as', ?_, hrelR, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show (o :: rest).length = 1 + rest.length from by simp [Nat.add_comm], runAsm_add_ok hr1]
      exact hrunR
    · rw [hpcR, hpc1']; simp only [List.length_cons]; omega
    · rw [hT.1, ← hacc]; exact ha
    · rw [hT.2.1, ← htr]; exact ht
    · rw [hT.2.2.1, ← hrdd]; exact hrd
    · rw [hT.2.2.2, ← hlgg]; exact hlg


/-- **Whole-function capstone for a two-instruction body.** For the real compiled
    `main: [PARAM x; PARAM y; c := ADD x y; d := NOT c; STOP]`, `runContext` corresponds to `runAsm` on
    the actual resolved program `[JUMPDEST; ADD; NOT; STOP]`, halting with `finalStateRel`. The first
    whole-function capstone over a **multi-instruction** body (binop then unop, with output→input
    dataflow `c ↦ NOT`), routed through the reusable `codegen_correct_singleBlock_halt` lift. -/
theorem codegen_correct_paramAddNot {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 paramAddNotCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 4
         (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  have hblkrun := runBlock_paramAddNot_venom (ctx := paramAddNotCtx) (s := eS) (restFuel := 4) hi0' hi1'
  rw [show (2 + (4 + 3) : Nat) = 9 from rfl] at hblkrun
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramAddNot_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef) hrel haspc
  exact codegen_correct_singleBlock_halt (fn := paramAddNotFn) (entry := paramAddNotBB) (N := 4)
    (prog := (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).1)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).2)
    rfl rfl hblkrun
    (by rw [show (asmResolve (executePlan (generateFnPlan paramAddNotFn 0 0).get!.1)).1
          = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "STOP"]
          from rfl]; exact hrunAsm)
    hterm


/-- `NOT d → e`, the second link of the NOT chain (reuses `addI2`/`notI2` from the paramAddNot section). -/
def notI3 : Instruction :=
  { id := 4, opcode := Opcode.NOT, operands := [Operand.Var "d"], outputs := ["e"] }
def paramAddNotNotBB : BasicBlock :=
  { label := "entry", instructions := [paramX, paramY, addI2, notI2, notI3, stopInst] }
def paramAddNotNotFn : IrFunction := ⟨"main", [paramAddNotNotBB]⟩
def paramAddNotNotCtx : VenomContext := ⟨[paramAddNotNotFn], some "main"⟩

/-- **Venom side (ADD + two NOTs).** Loads params, `c := x+y`, `d := ~c`, `e := ~d`, halts. -/
theorem runBlock_paramAddNotNot_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length) :
    runBlock (2 + (restFuel + 4)) ctx paramAddNotNotBB s
      = ExecResult.Halt (haltState
          (let v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩
           let v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩
           let sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 }
           let sA : VenomState := { updateVar "c" (v0 + v1) sL with instIdx := 3 }
           let sD : VenomState := { updateVar "d" (~~~ (v0 + v1)) sA with instIdx := 4 }
           { updateVar "e" (~~~ (~~~ (v0 + v1))) sD with instIdx := 5 })) := by
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hxL : lookupVar "x" sL = some v0 := by
    rw [hsL]; show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 s)) = some v0
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hyL : lookupVar "y" sL = some v1 := by
    rw [hsL]; show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 s)) = some v1
    rw [lookupVar_updateVar_self]
  set sA : VenomState := { updateVar "c" (v0 + v1) sL with instIdx := 3 } with hsA
  have hcA : lookupVar "c" sA = some (v0 + v1) := by
    rw [hsA]; exact lookupVar_updateVar_self _ _ _
  set sD : VenomState := { updateVar "d" (~~~ (v0 + v1)) sA with instIdx := 4 } with hsD
  have hdD : lookupVar "d" sD = some (~~~ (v0 + v1)) := by
    rw [hsD]; exact lookupVar_updateVar_self _ _ _
  have hstepA : stepInstBase addI2 sL = ExecResult.OK (updateVar "c" (v0 + v1) sL) := by
    show execPure2 (· + ·) addI2 sL = _; simp only [execPure2, addI2, evalOperand, hxL, hyL]
  have hstepD : stepInstBase notI2 sA = ExecResult.OK (updateVar "d" (~~~ (v0 + v1)) sA) := by
    show execPure1 (~~~ ·) notI2 sA = _; simp only [execPure1, notI2, evalOperand, hcA]
  have hstepE : stepInstBase notI3 sD = ExecResult.OK (updateVar "e" (~~~ (~~~ (v0 + v1))) sD) := by
    show execPure1 (~~~ ·) notI3 sD = _; simp only [execPure1, notI3, evalOperand, hdD]
  unfold runBlock
  rw [show paramAddNotNotBB.instructions = paramX :: [paramY, addI2, notI2, notI3, stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 4)) ctx paramAddNotNotBB { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx paramAddNotNotBB (restFuel + 4) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  show execBlock ((restFuel + 3) + 1) ctx paramAddNotNotBB sL = _
  rw [execBlock_step_nonterm (restFuel + 3) ctx paramAddNotNotBB sL (updateVar "c" (v0 + v1) sL) addI2
        (by rfl) hstepA (by decide)]
  show execBlock ((restFuel + 2) + 1) ctx paramAddNotNotBB sA = _
  rw [execBlock_step_nonterm (restFuel + 2) ctx paramAddNotNotBB sA (updateVar "d" (~~~ (v0 + v1)) sA) notI2
        (by rfl) hstepD (by decide)]
  show execBlock ((restFuel + 1) + 1) ctx paramAddNotNotBB sD = _
  rw [execBlock_step_nonterm (restFuel + 1) ctx paramAddNotNotBB sD (updateVar "e" (~~~ (~~~ (v0 + v1))) sD) notI3
        (by rfl) hstepE (by decide)]
  rw [execBlock_step_halt restFuel ctx paramAddNotNotBB
        { updateVar "e" (~~~ (~~~ (v0 + v1))) sD with instIdx := sD.instIdx + 1 }
        (haltState { updateVar "e" (~~~ (~~~ (v0 + v1))) sD with instIdx := sD.instIdx + 1 }) stopInst
        (by rfl) (by simp only [stepInstBase, stopInst])]

/-- **Asm side (ADD then a NOT chain via the fold).** `[JUMPDEST; ADD; NOT; NOT; STOP]` runs to
    `AsmHalt`: `soLabel_sim` + `emit_binop_sim` (ADD) + **`asm_unopChain_sim` for the `[d,e]` NOT chain**
    + `runAsm_stop`. Wires the arbitrary-length unop-chain fold into a whole-function asm sim. -/
theorem asm_paramAddNotNot_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 5 offsetToPc
             [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "NOT",
              AsmInst.AsmOp "STOP"] as
             = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "NOT",
     AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } with hpsE
  have hlen5 : prog.length = 5 := rfl
  -- step 1: JUMPDEST
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  -- step 2: ADD
  have hstk1 : ∃ rest, as1.stack = vy :: vx :: rest :=
    asmStack_top2_of_planStackRel hrel1.1 (by rw [hpsE]; decide) rfl rfl hydef hxdef
  obtain ⟨rest, hstk1'⟩ := hstk1
  have hblock1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "ADD"]) := by
    rw [hpc1']; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hfreshC : ¬ (Operand.Var "c") ∈ psE.stack := by rw [hpsE]; decide
  have hspillC : AssocList.lookup Operand Nat psE.spilled (Operand.Var "c") = none := by rw [hpsE]; rfl
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
    emit_binop_sim (offsetToPc := offsetToPc) (f := (· + ·)) hrel1 hstk1' hfreshC hspillC hblock1
      (fun h hg => asmStep_add_ok h hg)
  have hr2 : runAsm 1 offsetToPc prog as1 = AsmResult.AsmOK as2 := hrun2
  have hpc2' : as2.pc = 2 := by rw [hpc2, hpc1']; rfl
  -- step 3-4: the [d, e] NOT chain via the fold
  have hrelC : venomAsmRel lo ⟨[] ++ [Operand.Var "c"], psE.spilled, psE.alloc, psE.labelCounter⟩
      (updateVar "c" (vy + vx) vs) as2 := by
    have he : (⟨[] ++ [Operand.Var "c"], psE.spilled, psE.alloc, psE.labelCounter⟩ : PlanState)
        = { psE with stack := stackPush (Operand.Var "c") (stackPop 2 psE.stack) } := by
      rw [hpsE]; simp [stackPush, stackPop]
    rw [he]; exact hrel2
  have hcdef : lookupVar "c" (updateVar "c" (vy + vx) vs) = some (vy + vx) :=
    lookupVar_updateVar_self _ _ _
  obtain ⟨lastVar, vs', as4, hrun4, hrel4, hpc4, ha, ht, hrd, hlg⟩ :=
    asm_unopChain_sim (offsetToPc := offsetToPc) (prog := prog) (f := (~~~ ·)) (name := "NOT")
      (fun s h hg => asmStep_not_ok h hg)
      ["d", "e"] [] psE.spilled psE.alloc psE.labelCounter "c" (vy + vx)
      (updateVar "c" (vy + vx) vs) as2
      (by intro o ho; simp) (by intro o _; rw [hpsE]; rfl)
      (by decide) (by
        intro k hk; rw [hpc2']
        have hk2 : k < 2 := hk
        interval_cases k
        · refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
        · refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl)
      hcdef hrelC
  have hpc4' : as4.pc = 4 := by rw [hpc4, hpc2']; rfl
  -- step 5: STOP
  have hlt4 : as4.pc < prog.length := by rw [hpc4', hlen5]; omega
  have hget4 : prog.get ⟨as4.pc, hlt4⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as4.pc, hlt4⟩ : Fin prog.length) = ⟨4, by rw [hlen5]; omega⟩ from Fin.ext hpc4']; rfl
  have hr4 : runAsm 2 offsetToPc prog as2 = AsmResult.AsmOK as4 := hrun4
  refine ⟨asmNext as4, ?_, ?_⟩
  · rw [show (5 : Nat) = 1 + (1 + (2 + 1)) from rfl, runAsm_add_ok hr1, runAsm_add_ok hr2,
        runAsm_add_ok hr4]
    exact runAsm_stop 0 hlt4 hget4
  · -- terminal rel: accounts/etc unchanged through label, ADD, the fold, and asmNext
    have hE := venomAsmRel_terminal lo _ _ _ hrel
    have h2 := venomAsmRel_terminal lo _ _ _ hrel2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show as4.accounts = vs.accounts; rw [← ha]; exact h2.1
    · show as4.transient = vs.transient; rw [← ht]; exact h2.2.1
    · show as4.returndata = vs.returndata; rw [← hrd]; exact h2.2.2.1
    · show as4.logs = vs.logs; rw [← hlg]; exact h2.2.2.2

/-- **Whole-function capstone wiring the unop-chain fold.** For the real compiled
    `main: [PARAM x; PARAM y; c := ADD x y; d := NOT c; e := NOT d; STOP]`, `runContext` corresponds to
    `runAsm` on `[JUMPDEST; ADD; NOT; NOT; STOP]`, halting with `finalStateRel`. The asm side runs the
    `[d,e]` NOT chain through `asm_unopChain_sim` -- the first whole-function capstone whose body-fold
    goes through the reusable arbitrary-length unop-chain fold. Routed through the single-block lift. -/
theorem codegen_correct_paramAddNotNot {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 paramAddNotNotCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 5
         (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 }
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  have hblkrun := runBlock_paramAddNotNot_venom (ctx := paramAddNotNotCtx) (s := eS) (restFuel := 3) hi0' hi1'
  rw [show (2 + (3 + 4) : Nat) = 9 from rfl] at hblkrun
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramAddNotNot_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef) hrel haspc
  exact codegen_correct_singleBlock_halt (fn := paramAddNotNotFn) (entry := paramAddNotNotBB) (N := 5)
    (prog := (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).1)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).2)
    rfl rfl hblkrun
    (by rw [show (asmResolve (executePlan (generateFnPlan paramAddNotNotFn 0 0).get!.1)).1
          = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "ADD", AsmInst.AsmOp "NOT", AsmInst.AsmOp "NOT",
             AsmInst.AsmOp "STOP"] from rfl]; exact hrunAsm)
    hterm


/-- A single `NOT cur → out` instruction. -/
def notInst (cur out : String) : Instruction :=
  { id := 0, opcode := Opcode.NOT, operands := [Operand.Var cur], outputs := [out] }

/-- Build a straight-line NOT chain `[NOT cur → o₁; NOT o₁ → o₂; …]` from the input var and the output
    var list. -/
def buildNotChain : String → List String → List Instruction
  | _, [] => []
  | cur, o :: rest => notInst cur o :: buildNotChain o rest

/-- **Venom-side chain fold** (mirror of `asm_unopChain_sim`). Threading a NOT chain from a defined input
    var produces a state whose terminal-relation fields (accounts/transient/returndata/logs) equal the
    starting state's -- unops touch only stack vars. Induction on `outs`. -/
theorem execBodyThread_notChain :
    ∀ (outs : List String) (cur : String) (start : Nat) (s : VenomState) (vc : bytes32),
    lookupVar cur s = some vc →
    ∃ s', execBodyThread (buildNotChain cur outs) start s = some s' ∧
          s'.accounts = s.accounts ∧ s'.transient = s.transient ∧
          s'.returndata = s.returndata ∧ s'.logs = s.logs := by
  intro outs
  induction outs with
  | nil => intro cur start s vc _; exact ⟨s, rfl, rfl, rfl, rfl, rfl⟩
  | cons o rest ih =>
    intro cur start s vc hcur
    have hstep : stepInstBase (notInst cur o) s = ExecResult.OK (updateVar o (~~~ vc) s) := by
      show execPure1 (~~~ ·) (notInst cur o) s = _
      simp only [execPure1, notInst, evalOperand, hcur]
    set s1 : VenomState := { updateVar o (~~~ vc) s with instIdx := start + 1 } with hs1
    have hodef : lookupVar o s1 = some (~~~ vc) := by
      rw [hs1]; show lookupVar o (updateVar o (~~~ vc) s) = some (~~~ vc)
      exact lookupVar_updateVar_self _ _ _
    obtain ⟨s', hthread', ha, ht, hrd, hlg⟩ := ih o (start + 1) s1 (~~~ vc) hodef
    refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
    · show execBodyThread (notInst cur o :: buildNotChain o rest) start s = some s'
      simp only [execBodyThread, hstep]
      rw [← hs1]; exact hthread'
    · rw [ha]; rfl
    · rw [ht]; rfl
    · rw [hrd]; rfl
    · rw [hlg]; rfl

/-- **Fuel-general single-block whole-function halt reduction.** `runContext (fuel+1)` reduces to the
    entry block's `runBlock fuel`; the arbitrary-fuel version of `runContext_singleBlock_halt`. -/
theorem runContext_singleBlock_halt_gen {fuel : Nat}
    {ctx : VenomContext} {fn : IrFunction} {entry : BasicBlock} {vs hs : VenomState}
    (hctx : ctx = ⟨[fn], some fn.name⟩)
    (hblocks : fn.blocks = [entry])
    (hrb : runBlock fuel ctx entry { vs with prevBb := none, currentBb := entry.label, instIdx := 0 }
        = ExecResult.Halt hs) :
    runContext (fuel + 1) ctx vs = ExecResult.Halt hs := by
  set eS : VenomState := { vs with prevBb := none, currentBb := entry.label, instIdx := 0 } with heS
  have hlkf : lookupFunction fn.name [fn] = some fn := by simp [lookupFunction]
  have hlbl : fnEntryLabel fn = some entry.label := by rw [fnEntryLabel, hblocks]; rfl
  have hlkb : lookupBlock eS.currentBb fn.blocks = some entry := by
    rw [hblocks]; simp only [heS]; simp [lookupBlock]
  have hrc : runContext (fuel + 1) ctx vs = runBlocks (fuel + 1) ctx fn eS := by
    simp only [hctx, runContext, hlkf, runFunction, hlbl, heS]
  have hrbs : runBlocks (fuel + 1) ctx fn eS = ExecResult.Halt hs := by
    rw [runBlocks]; simp only [hlkb, hrb]
  rw [hrc, hrbs]

/-- **Replicate-program layout.** In `[JUMPDEST] ++ replicate N NOT ++ [STOP]`, each of the `N` inner
    positions holds a `NOT` -- exactly the per-position `asmBlockAt` the unop-chain fold consumes. -/
theorem asmBlockAt_notChain (N : Nat) :
    ∀ k, k < N → asmBlockAt
      ([AsmInst.AsmLabel "entry"] ++ List.replicate N (AsmInst.AsmOp "NOT") ++ [AsmInst.AsmOp "STOP"])
      (1 + k) (executePlan [StackOp.SOEmit "NOT"]) := by
  intro k hk
  have hlen : ([AsmInst.AsmLabel "entry"] ++ List.replicate N (AsmInst.AsmOp "NOT")
      ++ [AsmInst.AsmOp "STOP"]).length = N + 2 := by
    simp [List.length_append, List.length_replicate]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [show (executePlan [StackOp.SOEmit "NOT"]).length = 1 from rfl, hlen]; omega
  · have hj0 : j = 0 := by have : j < 1 := hj; omega
    subst hj0
    rw [show (1 + k + 0) = (k + 1) from by omega,
        show (executePlan [StackOp.SOEmit "NOT"]) = [AsmInst.AsmOp "NOT"] from rfl]
    show (AsmInst.AsmLabel "entry" :: (List.replicate N (AsmInst.AsmOp "NOT") ++ [AsmInst.AsmOp "STOP"]))[k + 1]?
        = [AsmInst.AsmOp "NOT"][0]?
    rw [List.getElem?_cons_succ,
        List.getElem?_append_left (by rw [List.length_replicate]; exact hk),
        List.getElem?_replicate, if_pos hk]
    rfl

/-- **Asm side of the arbitrary-length NOT chain.** `[JUMPDEST] ++ replicate N NOT ++ [STOP]` runs from
    the entry var-layout to `AsmHalt`: `soLabel_sim` + `asm_unopChain_sim` (the whole `outs` chain) +
    `runAsm_stop`. -/
theorem asm_paramNotChain_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {vx : bytes32} {outs : List String}
    (hxdef : lookupVar "x" vs = some vx) (hnodup : ("x" :: outs).Nodup)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm (outs.length + 2) offsetToPc
             ([AsmInst.AsmLabel "entry"] ++ List.replicate outs.length (AsmInst.AsmOp "NOT")
                ++ [AsmInst.AsmOp "STOP"]) as
             = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs as' := by
  set prog : List AsmInst :=
    [AsmInst.AsmLabel "entry"] ++ List.replicate outs.length (AsmInst.AsmOp "NOT")
      ++ [AsmInst.AsmOp "STOP"] with hprog
  set psE : PlanState := { initPlanState 0 with stack := [Operand.Var "x"] } with hpsE
  have hlen : prog.length = outs.length + 2 := by
    rw [hprog]; simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  -- step 1: JUMPDEST
  have hblock0 : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hlen, show (executePlan [StackOp.SOLabel "entry"]).length = 1 from rfl]; omega
    · have : j = 0 := by have : j < 1 := hj; omega
      subst this; rw [hprog]; rfl
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := offsetToPc) lo psE vs as prog "entry" hrel hblock0
  have hr1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hrun1
  have hpc1' : as1.pc = 1 := by rw [hpc1, haspc]; rfl
  -- step 2: the NOT chain via the fold
  have hrelX : venomAsmRel lo ⟨[] ++ [Operand.Var "x"], psE.spilled, psE.alloc, psE.labelCounter⟩ vs as1 := by
    have he : (⟨[] ++ [Operand.Var "x"], psE.spilled, psE.alloc, psE.labelCounter⟩ : PlanState) = psE := by
      rw [hpsE]; rfl
    rw [he]; exact hrel1
  obtain ⟨lastVar, vs', asF, hrunF, hrelF, hpcF, ha, ht, hrd, hlg⟩ :=
    asm_unopChain_sim (offsetToPc := offsetToPc) (prog := prog) (f := (~~~ ·)) (name := "NOT")
      (fun s h hg => asmStep_not_ok h hg)
      outs [] psE.spilled psE.alloc psE.labelCounter "x" vx vs as1
      (by intro o _; simp) (by intro o _; rw [hpsE]; rfl) hnodup
      (by intro k hk; rw [hpc1', hprog]; exact asmBlockAt_notChain outs.length k hk)
      hxdef hrelX
  have hpcF' : asF.pc = 1 + outs.length := by rw [hpcF, hpc1']
  -- step 3: STOP at pc 1 + outs.length
  have hltF : asF.pc < prog.length := by rw [hpcF', hlen]; omega
  have hgetF : prog.get ⟨asF.pc, hltF⟩ = AsmInst.AsmOp "STOP" := by
    have hg : prog[asF.pc]? = some (AsmInst.AsmOp "STOP") := by
      rw [hpcF', hprog, show (1 + outs.length) = outs.length + 1 from by omega]
      show (AsmInst.AsmLabel "entry" :: (List.replicate outs.length (AsmInst.AsmOp "NOT")
              ++ [AsmInst.AsmOp "STOP"]))[outs.length + 1]? = some (AsmInst.AsmOp "STOP")
      rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp [List.length_replicate]),
          List.length_replicate, Nat.sub_self]
      rfl
    rw [List.get_eq_getElem]
    have h2 : some (prog[asF.pc]'hltF) = some (AsmInst.AsmOp "STOP") := by
      rw [← List.getElem?_eq_getElem hltF]; exact hg
    exact Option.some.inj h2
  have hr1' : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as1 := hr1
  refine ⟨asmNext asF, ?_, ?_⟩
  · rw [show (outs.length + 2) = 1 + (outs.length + 1) from by omega, runAsm_add_ok hr1',
        runAsm_add_ok hrunF]
    exact runAsm_stop 0 hltF hgetF
  · have hE := venomAsmRel_terminal lo _ _ _ hrel
    refine ⟨?_, ?_, ?_, ?_⟩
    · show asF.accounts = vs.accounts
      rw [← ha]; exact (venomAsmRel_terminal lo _ _ _ hrel1).1
    · show asF.transient = vs.transient
      rw [← ht]; exact (venomAsmRel_terminal lo _ _ _ hrel1).2.1
    · show asF.returndata = vs.returndata
      rw [← hrd]; exact (venomAsmRel_terminal lo _ _ _ hrel1).2.2.1
    · show asF.logs = vs.logs
      rw [← hlg]; exact (venomAsmRel_terminal lo _ _ _ hrel1).2.2.2

theorem buildNotChain_length (cur : String) (outs : List String) :
    (buildNotChain cur outs).length = outs.length := by
  induction outs generalizing cur with
  | nil => rfl
  | cons o rest ih => simp only [buildNotChain, List.length_cons, ih]

theorem buildNotChain_nonterm (cur : String) (outs : List String) :
    ∀ inst ∈ buildNotChain cur outs, isTerminator inst.opcode = false := by
  induction outs generalizing cur with
  | nil => intro inst h; simp [buildNotChain] at h
  | cons o rest ih =>
    intro inst h
    simp only [buildNotChain, List.mem_cons] at h
    rcases h with h | h
    · subst h; rfl
    · exact ih o inst h

/-- **Fully arbitrary-length whole-function capstone.** For the real compiled
    `main(x): [PARAM x; d₁ := NOT x; …; dₙ := NOT dₙ₋₁; STOP]` -- parametric over the output-var list
    `outs` -- `runContext` corresponds to `runAsm` on `[JUMPDEST; NOTⁿ; STOP]`, halting with
    `finalStateRel`, for *every* chain length `n = outs.length`. Composes the Venom-side chain fold
    (`execBodyThread_notChain`) via `runBlock_halt`, the asm-side chain fold (`asm_paramNotChain_sim` /
    `asm_unopChain_sim`), the replicate-program layout, and the fuel-general single-block lift. The
    caller discharges only `hprog` (the resolved program shape) and `hnodup` by `rfl`/`decide` for a
    concrete `n`. -/
theorem codegen_correct_paramNotChain {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx : bytes32} {outs : List String} {fn : IrFunction} {ctx : VenomContext}
    (hfn : fn = ⟨"main", [⟨"entry", [paramX] ++ buildNotChain "x" outs ++ [stopInst]⟩]⟩)
    (hctx : ctx = ⟨[fn], some "main"⟩)
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx)
    (hnodup : ("x" :: outs).Nodup)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0)
    (hprog : (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1
        = [AsmInst.AsmLabel "entry"] ++ List.replicate outs.length (AsmInst.AsmOp "NOT")
            ++ [AsmInst.AsmOp "STOP"]) :
    (match runContext (outs.length + 3) ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (outs.length + 2)
         (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  set entryBB : BasicBlock := ⟨"entry", [paramX] ++ buildNotChain "x" outs ++ [stopInst]⟩ with hentry
  -- Venom side: PARAM loads x, chain runs, STOP halts (runBlock_halt over the composed thread)
  set s0 : VenomState := updateVar "x" (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) eS with hs0
  set sP : VenomState := { s0 with instIdx := 1 } with hsP
  have hparam : execBodyThread [paramX] 0 { eS with instIdx := 0 } = some sP := by
    simp only [execBodyThread]
    rw [stepInstBase_param (inst := paramX) (vs := { eS with instIdx := 0 }) rfl rfl rfl (by simpa using hi0)]
  have hxP : lookupVar "x" sP = some (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) := by
    rw [hsP, hs0]; exact lookupVar_updateVar_self _ _ _
  obtain ⟨sEnd, hchain, hca, hct, hcrd, hclg⟩ :=
    execBodyThread_notChain outs "x" 1 sP (eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) hxP
  have hthread : execBodyThread ([paramX] ++ buildNotChain "x" outs) 0 { eS with instIdx := 0 } = some sEnd := by
    rw [execBodyThread_append [paramX] (buildNotChain "x" outs) 0 { eS with instIdx := 0 } sP hparam]
    simpa using hchain
  have hnonterm : ∀ inst ∈ [paramX] ++ buildNotChain "x" outs, isTerminator inst.opcode = false := by
    intro inst h; rw [List.mem_append] at h
    rcases h with h | h
    · simp only [List.mem_singleton] at h; subst h; rfl
    · exact buildNotChain_nonterm "x" outs inst h
  have hstepterm : stepInstBase stopInst sEnd = ExecResult.Halt (haltState sEnd) := by
    simp only [stepInstBase, stopInst]
  have hbb : entryBB.instructions = ([paramX] ++ buildNotChain "x" outs) ++ [stopInst] := by
    rw [hentry]
  have hrbh := runBlock_halt ctx entryBB 0 ([paramX] ++ buildNotChain "x" outs) stopInst
      paramX (buildNotChain "x" outs ++ [stopInst]) eS sEnd (haltState sEnd)
      hbb rfl (by decide) hnonterm hthread hstepterm
  -- fuel: front.length + 1 = outs.length + 2
  have hfl : ([paramX] ++ buildNotChain "x" outs).length + (0 + 1) = outs.length + 2 := by
    simp only [List.length_append, List.length_singleton, buildNotChain_length]; omega
  rw [hfl] at hrbh
  have hlift := runContext_singleBlock_halt_gen (fuel := outs.length + 2) (ctx := ctx) (fn := fn)
    (entry := entryBB) (vs := vs) (hs := haltState sEnd)
    (by rw [hctx, hfn]) (by rw [hfn]) hrbh
  rw [show (outs.length + 2 + 1) = outs.length + 3 from by omega] at hlift
  rw [hlift]
  -- asm side
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramNotChain_sim (lo := lo)
    (offsetToPc := (asmResolve (executePlan (generateFnPlan fn 0 0).get!.1)).2)
    (show lookupVar "x" eS = some vx from hxdef) hnodup hrel haspc
  refine ⟨as', ?_, ?_⟩
  · rw [hprog]; exact hrunAsm
  · -- finalStateRel (haltState sEnd) as' from venomAsmTerminalRel vs as' + sEnd fields = vs fields
    have hsa : sEnd.accounts = vs.accounts := by rw [hca, hsP, hs0]; rfl
    have hst : sEnd.transient = vs.transient := by rw [hct, hsP, hs0]; rfl
    have hsr : sEnd.returndata = vs.returndata := by rw [hcrd, hsP, hs0]; rfl
    have hsl : sEnd.logs = vs.logs := by rw [hclg, hsP, hs0]; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show as'.accounts = (haltState sEnd).accounts; rw [show (haltState sEnd).accounts = sEnd.accounts from rfl, hsa]; exact hterm.1
    · show as'.transient = (haltState sEnd).transient; rw [show (haltState sEnd).transient = sEnd.transient from rfl, hst]; exact hterm.2.1
    · show as'.returndata = (haltState sEnd).returndata; rw [show (haltState sEnd).returndata = sEnd.returndata from rfl, hsr]; exact hterm.2.2.1
    · show as'.logs = (haltState sEnd).logs; rw [show (haltState sEnd).logs = sEnd.logs from rfl, hsl]; exact hterm.2.2.2

/-- A concrete length-3 chain function, to instantiate the parametric capstone. -/
def chain3Fn : IrFunction :=
  ⟨"main", [⟨"entry", [paramX] ++ buildNotChain "x" ["d1", "d2", "d3"] ++ [stopInst]⟩]⟩

/-- **Concrete instantiation at length 3.** Confirms `codegen_correct_paramNotChain` is dischargeable:
    `hprog` by `rfl`, `hnodup` by `decide`. -/
theorem codegen_correct_chain3 {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {vx : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hxdef : lookupVar "x" vs = some vx)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext (["d1", "d2", "d3"].length + 3) ⟨[chain3Fn], some "main"⟩ vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (["d1", "d2", "d3"].length + 2)
         (asmResolve (executePlan (generateFnPlan chain3Fn 0 0).get!.1)).2
         (asmResolve (executePlan (generateFnPlan chain3Fn 0 0).get!.1)).1 as
         = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_paramNotChain (outs := ["d1", "d2", "d3"]) (fn := chain3Fn)
    (ctx := ⟨[chain3Fn], some "main"⟩) rfl rfl hi0 hxdef (by decide) hrel haspc rfl


def paramJmpBB : BasicBlock := { label := "entry", instructions := [paramX, paramY, jmpInst] }

/-- **Venom-side param+JMP entry.** `runBlock` on a `PARAM`-prefixed block ending in `JMP next` loads
    the params (`execBodyThread_paramXY`), then the `JMP` transitions to `next` carrying the loaded
    `x`/`y` — the entry-block Venom half of a multi-block var-passing param function. -/
theorem runBlock_paramJmp_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat}
    (hi0 : (UInt256.ofNat 0).toNat < s.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < s.params.length)
    (hhalt : s.halted = false) :
    runBlock (2 + (restFuel + 1)) ctx paramJmpBB s
      = ExecResult.OK (jumpTo "next"
          { updateVar "y" (s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩)
              (updateVar "x" (s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩) s) with instIdx := 2 }) := by
  set v0 := s.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ with hv0
  set v1 := s.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ with hv1
  set sL : VenomState := { updateVar "y" v1 (updateVar "x" v0 s) with instIdx := 2 } with hsL
  have hsLidx : sL.instIdx = 2 := rfl
  have hsLhalt : sL.halted = false := by rw [hsL]; exact hhalt
  have hstepJ : stepInstBase jmpInst sL = ExecResult.OK (jumpTo "next" sL) := by
    simp [stepInstBase, jmpInst]
  have hnh : (jumpTo "next" sL).halted = false := by rw [jumpTo]; exact hsLhalt
  unfold runBlock
  rw [show paramJmpBB.instructions = paramX :: [paramY, jmpInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s paramX _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi paramX _ (by decide)]
  show execBlock ([paramX, paramY].length + (restFuel + 1)) ctx paramJmpBB
      { s with instIdx := 0 } = _
  rw [execBlock_body_prefix ctx paramJmpBB (restFuel + 1) [paramX, paramY] 0
        { s with instIdx := 0 } sL rfl
        (by intro j hj; have : j < 2 := hj; interval_cases j <;> rfl)
        (by intro inst hinst; simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
            rcases hinst with h | h <;> subst h <;> decide)
        (by rw [hsL]; exact execBodyThread_paramXY (s := { s with instIdx := 0 }) hi0 hi1)]
  rw [execBlock_step_term_ok restFuel ctx paramJmpBB sL (jumpTo "next" sL) jmpInst
        (by rw [hsLidx]; rfl) hstepJ (by decide) hnh]


/-- **Venom-side var-reading SSTORE block** (no PARAM prefix). `runBlock` on `[SSTORE x y; STOP]` from a
    state with `x`/`y` already defined reads them and halts with `sstore vx vy`. The `next`-block Venom
    half of the multi-block var-passing function (its inputs were loaded by the entry block's PARAMs). -/
theorem runBlock_sstore_venom {ctx : VenomContext} {s : VenomState} {restFuel : Nat} {vx vy : bytes32}
    (hxdef : lookupVar "x" s = some vx) (hydef : lookupVar "y" s = some vy) :
    runBlock (1 + (restFuel + 1)) ctx sstoreNextBB s
      = ExecResult.Halt (haltState
          { sstore vx vy { s with instIdx := 0 } with instIdx := 0 + 1 }) := by
  have hxd0 : lookupVar "x" { s with instIdx := 0 } = some vx := hxdef
  have hyd0 : lookupVar "y" { s with instIdx := 0 } = some vy := hydef
  have hstepS : stepInstBase sstoreInst { s with instIdx := 0 }
      = ExecResult.OK (sstore vx vy { s with instIdx := 0 }) :=
    stepInstBase_sstore rfl rfl hxd0 hyd0
  unfold runBlock
  rw [show sstoreNextBB.instructions = sstoreInst :: [stopInst] from rfl,
      evalPhis_ok_of_hd_ne_phi s sstoreInst _ (by decide),
      phiPrefixLength_zero_of_hd_ne_phi sstoreInst _ (by decide)]
  show execBlock (1 + (restFuel + 1)) ctx sstoreNextBB { s with instIdx := 0 } = _
  rw [show (1 + (restFuel + 1) : Nat) = (restFuel + 1) + 1 from by omega,
      execBlock_step_nonterm (restFuel + 1) ctx sstoreNextBB { s with instIdx := 0 }
        (sstore vx vy { s with instIdx := 0 }) sstoreInst rfl hstepS (by decide)]
  rw [execBlock_step_halt restFuel ctx sstoreNextBB
        { sstore vx vy { s with instIdx := 0 } with instIdx := 0 + 1 }
        (haltState { sstore vx vy { s with instIdx := 0 } with instIdx := 0 + 1 }) stopInst
        rfl (by simp only [stepInstBase, stopInst])]

def paramJmpFn : IrFunction := { name := "main", blocks := [paramJmpBB, sstoreNextBB] }
abbrev pjInput := executePlan (generateFnPlan paramJmpFn 0 0).get!.1
abbrev pjProg := (asmResolve pjInput).1
abbrev pjOtp := (asmResolve pjInput).2
abbrev pjOffsets := (computeLabelOffsets pjInput).2

/-- **Asm side of the multi-block var-passing function.** The whole resolved program
    `[JUMPDEST entry; PUSH next; JUMP; JUMPDEST next; SWAP1; SSTORE; STOP]` runs from the entry
    var-layout to `AsmHalt` with the terminal relation: the entry JMP (`hentryAsm_bare_jmp`, 3 steps to
    `next`'s pc 3, relation preserved) then the `next` SSTORE block (`asm_paramSstore_block` at pc 3,
    4 steps to halt). -/
theorem asm_paramJmpSstore_sim {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] } vs as)
    (haspc : as.pc = 0) :
    ∃ as', runAsm 7 pjOtp pjProg as = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (sstore vx vy vs)) as' := by
  -- entry JMP: pc 0 -> next's pc 3
  have hbLabel : asmBlockAt pjProg as.pc (executePlan [StackOp.SOLabel "entry"]) := by
    rw [haspc]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hpc1 : as.pc + 1 < pjProg.length := by rw [haspc]; decide
  have hpush : pjProg.get ⟨as.pc + 1, hpc1⟩ = resolveInst pjOffsets (AsmInst.AsmPushLabel "next") := by
    have e : as.pc + 1 = 1 := by rw [haspc]
    conv_lhs => rw [show (⟨as.pc + 1, hpc1⟩ : Fin pjProg.length) = ⟨1, by decide⟩ from Fin.ext e]
    rfl
  have hpc2 : as.pc + 2 < pjProg.length := by rw [haspc]; decide
  have hjump : pjProg.get ⟨as.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP" := by
    have e : as.pc + 2 = 2 := by rw [haspc]
    conv_lhs => rw [show (⟨as.pc + 2, hpc2⟩ : Fin pjProg.length) = ⟨2, by decide⟩ from Fin.ext e]
    rfl
  obtain ⟨asMid, hrunE, hrelMid, hpcMid⟩ :=
    hentryAsm_bare_jmp (offsets := pjOffsets) (offsetToPc := pjOtp) (off := 5) (idx := 3)
      hrel hbLabel hpc1 hpush rfl (by decide) hpc2 hjump rfl
  -- next SSTORE block at pc 3
  have hb0 : asmBlockAt pjProg asMid.pc (executePlan [StackOp.SOLabel "next"]) := by
    rw [hpcMid]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hb1 : asmBlockAt pjProg (asMid.pc + 1) (executePlan [StackOp.SOSwap 1]) := by
    rw [hpcMid]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hb2 : asmBlockAt pjProg (asMid.pc + 2) (executePlan [StackOp.SOEmit "SSTORE"]) := by
    rw [hpcMid]; refine ⟨by decide, fun j hj => ?_⟩; have : j < 1 := hj; interval_cases j; rfl
  have hlt3 : asMid.pc + 3 < pjProg.length := by rw [hpcMid]; decide
  have hget3 : pjProg.get ⟨asMid.pc + 3, hlt3⟩ = AsmInst.AsmOp "STOP" := by
    have e : asMid.pc + 3 = 6 := by rw [hpcMid]
    conv_lhs => rw [show (⟨asMid.pc + 3, hlt3⟩ : Fin pjProg.length) = ⟨6, by decide⟩ from Fin.ext e]
    rfl
  obtain ⟨as', hrunN, htermN⟩ :=
    asm_paramSstore_block (offsetToPc := pjOtp) hxdef hydef hrelMid hb0 hb1 hb2 hlt3 hget3
  refine ⟨as', ?_, htermN⟩
  rw [show (7 : Nat) = 3 + 4 from rfl, runAsm_add_ok hrunE]; exact hrunN


def paramJmpCtx : VenomContext := { functions := [paramJmpFn], entry := some "main" }

/-- **Multi-block real-codegen var-passing capstone.** For the real compiled 2-block function
    `main: entry: PARAM x; PARAM y; JMP next / next: SSTORE x y; STOP`, `runContext` corresponds to
    `runAsm` on the actual resolved program, halting with the final-state relation. The Venom walk peels
    entry (loads params, JMPs — `runBlock_paramJmp_venom`) then next (stores — `runBlock_sstore_venom`);
    the asm runs the whole program (`asm_paramJmpSstore_sim`). The value carried across the JMP is
    `[Var x, Var y]` (uniform, so the entry JMP preserves the relation into next). Terminal relations
    coincide (defeq) since the param load / jump preserve accounts/transient/returndata/logs. -/
theorem codegen_correct_paramJmpSstore {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    {vx vy : bytes32}
    (hi0 : (UInt256.ofNat 0).toNat < vs.params.length)
    (hi1 : (UInt256.ofNat 1).toNat < vs.params.length)
    (hvshalt : vs.halted = false)
    (hxdef : lookupVar "x" vs = some vx) (hydef : lookupVar "y" vs = some vy)
    (hp0 : vs.params.get ⟨(UInt256.ofNat 0).toNat, hi0⟩ = vx)
    (hp1 : vs.params.get ⟨(UInt256.ofNat 1).toNat, hi1⟩ = vy)
    (hrel : venomAsmRel lo { initPlanState 0 with stack := [Operand.Var "x", Operand.Var "y"] }
        { vs with prevBb := none, currentBb := "entry", instIdx := 0 } as)
    (haspc : as.pc = 0) :
    (match runContext 10 paramJmpCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm 7 pjOtp pjProg as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | _ => True) := by
  set eS : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hi0' : (UInt256.ofNat 0).toNat < eS.params.length := hi0
  have hi1' : (UInt256.ofNat 1).toNat < eS.params.length := hi1
  set v0 := eS.params.get ⟨(UInt256.ofNat 0).toNat, hi0'⟩ with hv0
  set v1 := eS.params.get ⟨(UInt256.ofNat 1).toNat, hi1'⟩ with hv1
  have hpe0 : v0 = vx := hp0
  have hpe1 : v1 = vy := hp1
  set loaded : VenomState := { updateVar "y" v1 (updateVar "x" v0 eS) with instIdx := 2 } with hLd
  set jumped : VenomState := jumpTo "next" loaded with hJp
  -- entry block
  have hblkE : runBlock 9 paramJmpCtx paramJmpBB eS = ExecResult.OK jumped := by
    rw [hJp, hLd]
    have h := runBlock_paramJmp_venom (ctx := paramJmpCtx) (s := eS) (restFuel := 6) hi0' hi1'
      (by rw [heS]; exact hvshalt)
    rwa [show (2 + (6 + 1) : Nat) = 9 from rfl] at h
  -- next block: x,y still loaded in jumped
  have hxJ : lookupVar "x" jumped = some vx := by
    rw [hJp, jumpTo, hLd]
    show lookupVar "x" (updateVar "y" v1 (updateVar "x" v0 eS)) = some vx
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self, hpe0]
  have hyJ : lookupVar "y" jumped = some vy := by
    rw [hJp, jumpTo, hLd]
    show lookupVar "y" (updateVar "y" v1 (updateVar "x" v0 eS)) = some vy
    rw [lookupVar_updateVar_self, hpe1]
  set hltS : VenomState :=
    haltState { sstore vx vy { jumped with instIdx := 0 } with instIdx := 0 + 1 } with hHlt
  have hblkN : runBlock 8 paramJmpCtx sstoreNextBB jumped = ExecResult.Halt hltS := by
    rw [hHlt]
    have h := runBlock_sstore_venom (ctx := paramJmpCtx) (s := jumped) (restFuel := 6) hxJ hyJ
    rwa [show (1 + (6 + 1) : Nat) = 8 from rfl] at h
  -- runContext -> runBlocks (2 blocks) = Halt hltS
  have hrc : runContext 10 paramJmpCtx vs = runBlocks 10 paramJmpCtx paramJmpFn eS := by
    simp only [runContext, show paramJmpCtx.entry = some "main" from rfl,
      show lookupFunction "main" paramJmpCtx.functions = some paramJmpFn from rfl,
      runFunction, show fnEntryLabel paramJmpFn = some "entry" from rfl, heS]
  have hjhalt : jumped.halted = false := by rw [hJp, jumpTo, hLd]; exact hvshalt
  have hrbs : runBlocks 10 paramJmpCtx paramJmpFn eS = ExecResult.Halt hltS := by
    rw [runBlocks]
    simp only [show lookupBlock eS.currentBb paramJmpFn.blocks = some paramJmpBB from rfl, hblkE,
      hjhalt, Bool.false_eq_true, if_false]
    rw [runBlocks]
    simp only [show lookupBlock jumped.currentBb paramJmpFn.blocks = some sstoreNextBB from rfl, hblkN]
  rw [hrc, hrbs]
  obtain ⟨as', hrunAsm, hterm⟩ := asm_paramJmpSstore_sim (lo := lo)
    (show lookupVar "x" eS = some vx from hxdef) (show lookupVar "y" eS = some vy from hydef) hrel haspc
  exact ⟨as', hrunAsm, hterm⟩


end EvmYul.Venom.Hol.Codegen.Example


namespace EvmYul.Venom.Hol.Codegen

/-- **Function-level internal return.** A function whose blocks run to an `IntRet` (a `RET` terminator)
    returns those values -- `runFunction` just wraps `runBlocks`. The function-level rung of the
    internal-return chain (`runBlock_intret` -> `runBlocks_intret_of_block` -> here). -/
theorem runFunction_intret {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {s sEnd : VenomState}
    {lbl : String} {vals : List bytes32}
    (hlbl : fnEntryLabel fn = some lbl)
    (hrbs : runBlocks fuel ctx fn { s with currentBb := lbl, instIdx := 0 }
        = ExecResult.IntRet vals sEnd) :
    runFunction fuel ctx fn s = ExecResult.IntRet vals sEnd := by
  unfold runFunction; rw [hlbl]; exact hrbs

/-- **Context-level internal return.** The entry function returning `IntRet` makes `runContext` return
    those values -- the top of the internal-return chain. This is the Venom-side characterization of a
    callee that returns values (what an internal `CALL` would invoke; the semantics has `RET`/`IntRet`
    but no internal-call opcode that re-enters `runFunction`, so `IntRet` propagates to the top). -/
theorem runContext_intret {fuel : Nat} {ctx : VenomContext} {entryFn : IrFunction} {s sEnd : VenomState}
    {entryName : String} {vals : List bytes32}
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some entryFn)
    (hrf : runFunction fuel ctx entryFn { s with prevBb := none } = ExecResult.IntRet vals sEnd) :
    runContext fuel ctx s = ExecResult.IntRet vals sEnd := by
  simp only [runContext, hent, hlk]; exact hrf

/-! ## Concrete internal-return demonstration -/

def retInst : Instruction :=
  { id := 0, opcode := Opcode.RET, operands := [Operand.Lit (EvmYul.UInt256.ofNat 42)], outputs := [] }
def retBB : BasicBlock := { label := "entry", instructions := [retInst] }
def retFn : IrFunction := ⟨"main", [retBB]⟩
def retCtx : VenomContext := ⟨[retFn], some "main"⟩

/-- **First concrete internal-return instance.** For `main: [RET 42]`, `runContext` returns
    `IntRet [42]` from the entry state -- end to end through the whole Venom internal-return chain
    (`runBlock_intret` -> `runBlocks_intret_of_block` -> `runFunction_intret` -> `runContext_intret`).
    De-vacuifies the `IntRet` arm (previously only ever hit the `_ => True` catch-all). -/
theorem runContext_bareRet {s : VenomState} :
    runContext 3 retCtx s
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42]
          { s with prevBb := none, currentBb := "entry", instIdx := 0 } := by
  set eS : VenomState := { s with prevBb := none, currentBb := "entry", instIdx := 0 } with heS
  have hstep : stepInstBase retInst { eS with instIdx := 0 }
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } := rfl
  have hrb : runBlock 2 retCtx retBB eS
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } := by
    have h := runBlock_intret retCtx retBB 1 [] retInst retInst [] eS { eS with instIdx := 0 }
      { eS with instIdx := 0 } [EvmYul.UInt256.ofNat 42]
      (by rfl) rfl (by decide) (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstep
    simpa using h
  have hrbs : runBlocks 3 retCtx retFn eS
      = ExecResult.IntRet [EvmYul.UInt256.ofNat 42] { eS with instIdx := 0 } :=
    runBlocks_intret_of_block (by rfl) hrb
  refine runContext_intret (entryName := "main") (entryFn := retFn) rfl rfl ?_
  exact runFunction_intret (lbl := "entry") rfl hrbs

end EvmYul.Venom.Hol.Codegen

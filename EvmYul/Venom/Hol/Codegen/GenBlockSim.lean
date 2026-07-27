/-
Block / function Simulation Lemmas — THE key lemmas for codegen_correct

Port of vyper-hol/venom/codegen/proofs/genBlockSimScript.sml

States that a generated block (resp. function) plan, run on the asm interpreter,
simulates the Venom block (resp. function) execution, preserving `venomAsmRel`.

STATUS (stage 4b capstone — DISCHARGED, no `sorry`; conditional on the per-block / per-function asm
correspondence `hsim`/`hfsim`). These two lemmas are stated against the *real* stack-plan generator
(`generateBlockPlan` / `generateFnPlan`,
fully transcribed and proven total on codegen-ready input — see `CodegenGenProps`), AND against the
*resolved* asm: `prog := (asmResolve (executePlan ops)).1` runs label pushes as concrete value
pushes, and `JUMP`/`JUMPI` resolve through an `offsetToPc` map. `genFnSimulation` derives that map
from the whole function (`(asmResolve (executePlan ops)).2`, all block labels present);
`genBlockSimulation` takes it as a parameter (threaded by `genFnSimulation` — a single block's own
labels don't include its cross-block jump targets). This restatement makes the control-flow (OK)
case provable in principle (it was *unprovable* against the old raw `executePlan` + empty
`offsetToPc`, where `asmStep` errors on `AsmPushLabel`): see the `AsmResolveProofs` atoms
(`resolved_jump_sim` / `resolved_jumpi_*`, `asmResolve_fst_eq_of_no_label`).

Both are DISCHARGED (no `sorry`): `genBlockSimulation` via `genBlockSim_match`, `genFnSimulation` by
casing the CFG-walk result (`runBlocks_never_ok` + `hfsim`). They are *conditional* on the per-block
`hsim` / per-function `hfsim` asm correspondence — the outstanding correctness work is *supplying*
that unconditionally for a general function (composing the per-inst sims `GenInstSim` and control-flow
atoms over the resolved plan, threaded by the `runBlocks` CFG walk `runBlocks_walk`). `codegen_correct`
(CodegenCorrectness) is now real too (it feeds `runBlocks_walk` the same per-block correspondence);
the concrete `codegenFuel_correct_*` / `hfsim_*` / `genBlockSimulation_*_example` instances discharge
the correspondence end to end.

History: originally *vacuously* discharged (`generateBlockPlan`/`generateFnPlan` were `none` stubs);
transcribing the real generator made the premises satisfiable; restating against the resolved
program + `offsetToPc` (this revision) removed the label-resolution wall that made the OK case
unprovable.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Exec
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.PlanTypes
import EvmYul.Venom.Hol.Codegen.PlanOps
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.Hol.Codegen.AsmSem
import EvmYul.Venom.Hol.Codegen.CodegenRel
import EvmYul.Venom.Hol.Codegen.CodegenPipeline
import EvmYul.Venom.Hol.Codegen.SymbolResolve
import EvmYul.Venom.Hol.Codegen.GenBlockSimComp
import EvmYul.Venom.Hol.Codegen.CodegenCorrectness
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/- ============================================================
   KEY LEMMA: genBlockSimulation

   If a block plan is generated and the initial state satisfies
   venomAsmRel, then executing the plan on the asm interpreter
   preserves venomAsmRel through the Venom block step.

   In other words: the compiled block correctly simulates the
   Venom IR block execution.
   ============================================================ -/

-- The plan/rel/safety/WF hypotheses are the documented per-block interface; the discharge
-- consumes only the structural facts and `hsim`.
set_option linter.unusedVariables false in
theorem genBlockSimulation
  {fuel ctx fn bb ps ps' ops vs as labelOffsets}
  {offsetToPc : AssocList Nat Nat}
  {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
  (front : List Instruction) (term hd : Instruction) (tl : List Instruction) (sEnd : VenomState)
  (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (ops, ps'))
  (hrel  : venomAsmRel labelOffsets ps vs as)
  (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
           stepMemSafe ps.alloc vs1 vs2)
  (hready : codegenReadyFn fn)
  -- Block well-formedness (the `codegenReadyFn` well-formedness conjunct is currently a `True`
  -- stub, so the block structure is supplied explicitly): the block is `front ++ [term]` with a
  -- non-PHI head and non-terminator body, threading to `sEnd` over `execBodyThread`.
  (hbb : bb.instructions = front ++ [term])
  (hcons : front ++ [term] = hd :: tl)
  (hphi : hd.opcode ≠ Opcode.PHI)
  (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
  (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
  (histerm : isTerminator term.opcode = true)
  -- Per-block asm correspondence, keyed by the terminator's Venom effect (supplied by the body
  -- per-instruction sims composed with the terminator's own sim — `genBlockAsm_*_sim` over the
  -- resolved program). This is the per-instruction-correctness content the discharge consumes.
  (hsim : match stepInstBase term sEnd with
    | ExecResult.OK sEnd' =>
      sEnd'.halted = false ∧ ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
        venomAsmRel labelOffsets ps' sEnd' as'
    | ExecResult.Halt sEnd' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
        venomAsmTerminalRel sEnd' as'
    | ExecResult.Abort AbortType.RevertAbort sEnd' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
        venomAsmTerminalRel sEnd' as'
    | ExecResult.Abort AbortType.ExHaltAbort sEnd' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length offsetToPc
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
        venomAsmTerminalRel sEnd' as'
    | _ => True) :
  -- The compiled asm program is the *resolved* `executePlan ops`: `AsmResolve` turns each
  -- `AsmPushLabel`/`AsmPushOfst` into a concrete `AsmPush <byte offset>`, so `asmStep` no longer
  -- errors on unresolved label pushes. `offsetToPc` is the *whole-function* byte-offset → list-index
  -- map (threaded in by `genFnSimulation`), under which the block's `JUMP`/`JUMPI` resolve to their
  -- cross-block targets (a single block's own labels don't include the targets).
  let prog := (asmResolve (executePlan ops)).1
  -- Running the resolved asm program from `as` reaches an `as'` whose result constructor matches
  -- the Venom block step: OK (non-halting terminator, e.g. JMP) ↦ AsmOK preserving `venomAsmRel`;
  -- Halt/Abort ↦ AsmHalt/AsmRevert/AsmFault with the observable effects in agreement
  -- (`venomAsmTerminalRel`). The `∃`/result is *inside* each arm — the old form factored an
  -- `∃ as', runAsm … = AsmOK as'` outside the match, which is false for a halting block (`runAsm`
  -- can't be both `AsmOK` and `AsmHalt`).
  match runBlock fuel ctx bb vs with
  | ExecResult.OK vs' =>
    ∃ as', runAsm (prog.length) offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs' as'
  | ExecResult.Halt vs' =>
    ∃ as', runAsm (prog.length) offsetToPc prog as = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.RevertAbort vs' =>
    ∃ as', runAsm (prog.length) offsetToPc prog as = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
    ∃ as', runAsm (prog.length) offsetToPc prog as = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel vs' as'
  -- `Error` (insufficient fuel) / `IntRet` (call-level, never arises for `runBlock`): the
  -- simulation claims correspondence only when the Venom block step *succeeds*. Vacuous here, so
  -- the statement holds for any `fuel` (no fuel-sufficiency hypothesis needed); the dispatch
  -- supplies the asm result whenever `runBlock` actually reaches OK/Halt/Abort.
  | _ => True := by
  -- Stage-4b capstone: discharged via `genBlockSim_match` — case on the terminator's Venom effect
  -- (`stepInstBase term sEnd`), reduce `runBlock` (sufficient fuel) to the matching arm, and
  -- consume the per-block asm correspondence `hsim`. The well-formedness + per-instruction content
  -- is now explicit hypotheses (`hbb`/…/`hsim`), to be supplied by `genFnSimulation`/`codegen_correct`
  -- from `codegenReadyFn` + the per-instruction sims; no longer `sorry`-admitted.
  exact genBlockSim_match front term hd tl sEnd fuel hbb hcons hphi hnonterm hthread histerm hsim

/- ============================================================
   Function-level simulation: compose genBlockSimulation across
   all blocks in DFS order (via generateFnPlan).
   ============================================================ -/

-- The plan/rel/safety/WF hypotheses are the documented whole-function interface; the
-- modulo-`hbsim` discharge consumes only `hfsim`.
set_option linter.unusedVariables false in
theorem genFnSimulation
  {fuel ctx fn fnEom lblCtr ops psFinal vs as labelOffsets}
  (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
  (hrel  : venomAsmRel labelOffsets (initPlanState fnEom) vs as)
  (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
           stepMemSafe (initPlanState fnEom).alloc vs1 vs2)
  (hready : codegenReadyFn fn)
  -- Per-function asm correspondence keyed by the CFG-walk result `runBlocks fuel ctx fn vs`,
  -- supplied by composing `genBlockSimulation` across the DFS-ordered blocks (`runBlocks_unfold_*`),
  -- threading the whole-function `offsetToPc`. This is the inter-block (CFG) composition content;
  -- the discharge below adds the `runBlocks`-never-`OK` fact and the structural reduction.
  (hfsim : match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
      ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
        (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True) :
  -- The compiled asm program is the *resolved* whole-function `executePlan ops`, with its own
  -- byte-offset → list-index map derived by `AsmResolve`; cross-block `JUMP`/`JUMPI` resolve within
  -- it (all of the function's block labels are present). The block-level `genBlockSimulation` is
  -- composed across the DFS-ordered blocks (`runBlocks_unfold_*`), threading this `offsetToPc`.
  let prog := (asmResolve (executePlan ops)).1
  let offsetToPc := (asmResolve (executePlan ops)).2
  match runBlocks fuel ctx fn vs with
  | ExecResult.Halt vs' =>
    ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.RevertAbort vs' =>
    ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
    ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.OK _ => False
  | ExecResult.IntRet _ _ => True
  | ExecResult.Error _ => True := by
  -- Discharged: case on the CFG-walk result. `runBlocks` never returns `OK` (`runBlocks_never_ok`),
  -- so that arm is vacuous; `IntRet`/`Error` are `True`; the `Halt`/`Abort` arms are the per-function
  -- asm correspondence `hfsim` (the inter-block composition content, to be supplied by composing
  -- `genBlockSimulation` across blocks). No longer `sorry`-admitted.
  cases hrb : runBlocks fuel ctx fn vs with
  | OK vs' => exact runBlocks_never_ok hrb
  | Halt vs' => rw [hrb] at hfsim; exact hfsim
  | Abort a vs' => cases a <;> (rw [hrb] at hfsim; exact hfsim)
  | IntRet vals vs' => trivial
  | Error e => trivial

/-! ## CFG composition — single-block base cases (toward supplying `hfsim`)

`genFnSimulation` takes `hfsim` (the whole-function asm correspondence). For a function whose entry
block already produces the terminal (the common straight-line case: entry runs to STOP/RETURN/REVERT/
INVALID), `hfsim` follows from the block-level sim by two facts already in hand: the `runBlocks`
walk-peel (`runBlocks_{halt,abort}_of_block`) collapses the CFG walk to the entry block's outcome, and
the whole-program `runAsm prog.length` reaches the same terminal because the block's plan length
`n ≤ prog.length` and a terminal `AsmHalt`/`AsmRevert`/`AsmFault` is absorbing under extra fuel
(`runAsm_le_of_ne_ok`). The general multi-block case threads the per-block correspondence across JMP
boundaries (the remaining inter-block stack-layout work). -/

/-- Entry block halts ⇒ the function's `hfsim` Halt obligation. -/
theorem hfsim_halt_single {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {vs vs' : VenomState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as' : AsmState} {bb : BasicBlock}
    {n : Nat}
    (hlk : lookupBlock vs.currentBb fn.blocks = some bb)
    (hrb : runBlock fuel ctx bb vs = ExecResult.OK vs') (hh : vs'.halted = true)
    (hrun : runAsm n offsetToPc prog as = AsmResult.AsmHalt as') (hn : n ≤ prog.length)
    (hterm : venomAsmTerminalRel vs' as') :
    runBlocks (fuel + 1) ctx fn vs = ExecResult.Halt vs' ∧
    runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as' :=
  ⟨runBlocks_halt_of_block hlk hrb hh,
   runAsm_le_of_ne_ok (fun _ => by simp) hn hrun, hterm⟩

/-- Entry block halts **directly** (the terminator returns `Halt`, e.g. STOP/RETURN/SELFDESTRUCT) ⇒
    the function's `hfsim` Halt obligation. The direct-`Halt` companion of `hfsim_halt_single` (which
    handles the `OK`-then-halted case). The terminal-terminator blocks discharged by
    `genBlockSimulation_empty_body_halt` return `Halt` directly, so they feed this variant — lifting
    a single-block terminal function's block sim to the per-function `hfsim`. -/
theorem hfsim_haltDirect_single {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {vs vs' : VenomState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as' : AsmState} {bb : BasicBlock}
    {n : Nat}
    (hlk : lookupBlock vs.currentBb fn.blocks = some bb)
    (hrb : runBlock fuel ctx bb vs = ExecResult.Halt vs')
    (hrun : runAsm n offsetToPc prog as = AsmResult.AsmHalt as') (hn : n ≤ prog.length)
    (hterm : venomAsmTerminalRel vs' as') :
    runBlocks (fuel + 1) ctx fn vs = ExecResult.Halt vs' ∧
    runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as' :=
  ⟨runBlocks_haltDirect_of_block hlk hrb,
   runAsm_le_of_ne_ok (fun _ => by simp) hn hrun, hterm⟩

/-- Entry block reverts ⇒ the function's `hfsim` Revert obligation. -/
theorem hfsim_revert_single {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {vs vs' : VenomState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as' : AsmState} {bb : BasicBlock}
    {n : Nat}
    (hlk : lookupBlock vs.currentBb fn.blocks = some bb)
    (hrb : runBlock fuel ctx bb vs = ExecResult.Abort AbortType.RevertAbort vs')
    (hrun : runAsm n offsetToPc prog as = AsmResult.AsmRevert as') (hn : n ≤ prog.length)
    (hterm : venomAsmTerminalRel vs' as') :
    runBlocks (fuel + 1) ctx fn vs = ExecResult.Abort AbortType.RevertAbort vs' ∧
    runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as' :=
  ⟨runBlocks_abort_of_block hlk hrb,
   runAsm_le_of_ne_ok (fun _ => by simp) hn hrun, hterm⟩

/-- Entry block faults (INVALID) ⇒ the function's `hfsim` Fault obligation. -/
theorem hfsim_fault_single {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {vs vs' : VenomState}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as' : AsmState} {bb : BasicBlock}
    {n : Nat}
    (hlk : lookupBlock vs.currentBb fn.blocks = some bb)
    (hrb : runBlock fuel ctx bb vs = ExecResult.Abort AbortType.ExHaltAbort vs')
    (hrun : runAsm n offsetToPc prog as = AsmResult.AsmFault as') (hn : n ≤ prog.length)
    (hterm : venomAsmTerminalRel vs' as') :
    runBlocks (fuel + 1) ctx fn vs = ExecResult.Abort AbortType.ExHaltAbort vs' ∧
    runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as' :=
  ⟨runBlocks_abort_of_block hlk hrb,
   runAsm_le_of_ne_ok (fun _ => by simp) hn hrun, hterm⟩

/-- **Budget-step constructor for the `OK`-not-halted (JMP) arm of `runBlocks_walk`'s `hbsim`.** Given
    a block-local asm-JMP sim — running the block's own asm (`n` steps, `n ≤ N`) from its entry `asm`
    reaches `asm'` at the successor's entry pc (`runAsm n … asm = AsmOK asm'`) — plus the successor's
    `Entry s' asm' (N - n)`, produce the budget transition the engine consumes:
    `runAsm N … asm = runAsm (N - n) … asm'` (via `runAsm_append_ok`, splitting `N = n + (N - n)`).
    This isolates the engine-side budget mechanics; the remaining multi-block content is the
    block-local JMP sim (`runAsm n … asm = AsmOK asm'` landing at the successor's entry, with the
    reconciled stack layout) that supplies `hrun` and `hE'`. For an acyclic CFG with `N := prog.length`
    the block asm lengths sum to `prog.length`, so each `N - n` is the remaining budget. -/
theorem jmp_budget_step {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {Entry : VenomState → AsmState → Nat → Prop} {s' : VenomState} {asm asm' : AsmState} {n N : Nat}
    (hn : n ≤ N)
    (hrun : runAsm n offsetToPc prog asm = AsmResult.AsmOK asm')
    (hE' : Entry s' asm' (N - n)) :
    ∃ asm'' N', runAsm N offsetToPc prog asm = runAsm N' offsetToPc prog asm'' ∧ Entry s' asm'' N' := by
  refine ⟨asm', N - n, ?_, hE'⟩
  conv_lhs => rw [show N = n + (N - n) from by omega]
  exact runAsm_append_ok hrun

/-! ## Full `hfsim` via the CFG walk engine (acyclic `N := prog.length`)

`genFnSimulation` takes `hfsim` (the whole-function asm correspondence keyed by `runBlocks`). The
order-agnostic engine `runBlocks_walk` produces exactly that `match`-shape from a per-block sim plus an
`Entry` relation and an asm budget `N`; instantiating `N := prog.length` (the acyclic case — each
block's asm runs once, lengths summing to `prog.length`) discharges it. The lemma below is the base
case of that instantiation: a **single-block (entry-terminal) function**, where the singleton `Entry`
holds only for the initial `(vs, as, prog.length)` and the per-block sim is just the entry block's asm
correspondence. The general multi-block case threads the per-block correspondence across `JMP`
boundaries via the engine's `OK`-not-halted budget transition (`runAsm N = runAsm N' asm'`) — the
remaining inter-block stack-layout work. -/

/-- **Full `hfsim` for a single-block (entry-terminal) function, via `runBlocks_walk` at
    `N := prog.length`.** The per-block hypothesis `hbsim` is the entry block's asm correspondence
    (the shape `genBlockSimulation` produces, keyed by `runBlock`): a halting/aborting terminator
    yields the matching `AsmHalt`/`AsmRevert`/`AsmFault`; an `OK` outcome must be halting
    (`s'.halted = true`) — i.e. the block is terminal with no live successor. The conclusion is exactly
    `genFnSimulation`'s `hfsim`, so it plugs straight in. -/
theorem hfsim_single_via_walk {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {vs : VenomState}
    {as : AsmState} {ops : List StackOp}
    (hbsim : ∀ (f' : Nat) (bb : BasicBlock),
        lookupBlock vs.currentBb fn.blocks = some bb →
        match runBlock f' ctx bb vs with
        | ExecResult.OK s' =>
            s'.halted = true ∧ ∃ asm',
              runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
                (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
              (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
              (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
              (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel s' asm'
        | _ => True) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  runBlocks_walk
    (offsetToPc := (asmResolve (executePlan ops)).2) (prog := (asmResolve (executePlan ops)).1)
    (fun s asm N => s = vs ∧ asm = as ∧ N = (asmResolve (executePlan ops)).1.length)
    (by
      intro s asm N f' bb hE hlk
      obtain ⟨hs, ha, hNN⟩ := hE
      subst hs; subst ha; subst hNN
      have hb := hbsim f' bb hlk
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        obtain ⟨hh, hex⟩ := hb
        simp only [hh, if_true]; exact hex
      | Halt s' => rw [hrb] at hb; exact hb
      | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
      | IntRet vals s' => trivial
      | Error e => trivial)
    fuel vs as (asmResolve (executePlan ops)).1.length ⟨rfl, rfl, rfl⟩

/-- **Two-block `hfsim` (entry JMPs to a terminal block), assembled via the CFG walk engine.** The
    first genuine multi-block `hfsim`: the entry block continues (a non-halting JMP) to `sMid` at the
    successor `termBb`'s entry `asMid` (`hentry` / `hentryAsm`, the entry block's JMP-block sim — from
    `block_jmp_sim` + `genJmp_executePlan_eq`), and the terminal block halts/aborts (`hterm`, from the
    terminal block's `genBlockSimulation` arm at the residual budget `prog.length - n`). The engine
    threads a two-state `Entry` (initial `(vs, as, prog.length)` ∨ post-JMP `(sMid, asMid,
    prog.length - n)`); the JMP step is discharged by `jmp_budget_step`. The conclusion is exactly
    `genFnSimulation`'s `hfsim`. This shows the whole multi-block chain composes; the remaining work is
    *supplying* `hentryAsm`/`hentry`/`hterm` from the per-block body folds + the well-scheduling
    invariant. -/
theorem hfsim_jmp_then_terminal {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as asMid : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {entryBb termBb : BasicBlock} {n : Nat}
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hentry : ∀ f', match runBlock f' ctx entryBb vs with
        | ExecResult.OK s' => s' = sMid ∧ s'.halted = false
        | ExecResult.Halt _ => False
        | ExecResult.Abort _ _ => False
        | _ => True)
    (hentryAsm : runAsm n offsetToPc prog as = AsmResult.AsmOK asMid)
    (hn : n ≤ prog.length)
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (hterm : ∀ f', match runBlock f' ctx termBb sMid with
        | ExecResult.OK s' =>
            s'.halted = true ∧ ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel s' asm'
        | _ => True) :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  runBlocks_walk (offsetToPc := offsetToPc) (prog := prog)
    (fun s asm N => (s = vs ∧ asm = as ∧ N = prog.length) ∨
                    (s = sMid ∧ asm = asMid ∧ N = prog.length - n))
    (by
      intro s asm N f' bb hE hlk
      rcases hE with ⟨hs, ha, hN⟩ | ⟨hs, ha, hN⟩
      · subst hs; subst ha; subst hN
        rw [hlk1] at hlk; injection hlk with hbb; subst bb
        have hb := hentry f'
        cases hrb : runBlock f' ctx entryBb s with
        | OK s' =>
          rw [hrb] at hb; obtain ⟨hsmid, hnh⟩ := hb
          simp only [hnh, Bool.false_eq_true, if_false]
          refine ⟨asMid, prog.length - n, ?_, Or.inr ⟨hsmid, rfl, rfl⟩⟩
          conv_lhs => rw [show prog.length = n + (prog.length - n) from by omega]
          exact runAsm_append_ok hentryAsm
        | Halt s' => rw [hrb] at hb; exact hb.elim
        | Abort a s' => rw [hrb] at hb; exact hb.elim
        | IntRet vals s' => trivial
        | Error e => trivial
      · subst hs; subst ha; subst hN
        rw [hlk2] at hlk; injection hlk with hbb; subst bb
        have hb := hterm f'
        cases hrb : runBlock f' ctx termBb s with
        | OK s' =>
          rw [hrb] at hb; obtain ⟨hh, hex⟩ := hb
          simp only [hh, if_true]; exact hex
        | Halt s' => rw [hrb] at hb; exact hb
        | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
        | IntRet vals s' => trivial
        | Error e => trivial)
    fuel vs as prog.length (Or.inl ⟨rfl, rfl, rfl⟩)

/-- **Two-block `hfsim` with the Venom side fully discharged** (entry JMPs to a halting terminal
    block). Specialises `hfsim_jmp_then_terminal`, discharging `hentry` via `runBlock_jmp_arm` and
    `hterm` via `hterm_halt` from the two blocks' structure (`front ++ [term]`, non-PHI head,
    non-terminator body, threaded `execBodyThread`, terminator step). What remains are exactly the two
    **asm-side whole-program** facts: `hentryAsm` (the entry block's asm run from `as` to the
    successor's entry `asMid`, from the body fold + `block_jmp_sim`) and `hasm` (the terminal block's
    asm run from `asMid` to `AsmHalt`, at the residual budget). Everything else — Venom semantics,
    fuel, the CFG walk, the budget threading — is now proved. -/
theorem hfsim_jmp_then_halt
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as asMid : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {entryBb termBb : BasicBlock} {n : Nat}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    (hentryAsm : runAsm n offsetToPc prog as = AsmResult.AsmOK asMid)
    (hn : n ≤ prog.length)
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction}
    {tsEnd tsEnd' : VenomState}
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt tsEnd')
    (hasm : ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel tsEnd' asm') :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_jmp_then_terminal hlk1
    (runBlock_jmp_arm ctx entryBb efront eterm ehd etl vs esEnd sMid hebb hecons hephi henonterm
      hethread heterm_step heisterm henohalt)
    hentryAsm hn hlk2
    (hterm_halt ctx termBb tfront tterm thd ttl sMid tsEnd tsEnd' htbb htcons htphi htnonterm
      htthread htterm_step hasm)

/-- **Two-block `hfsim`, Venom side discharged, terminal block containing a mid-body external
    call**: the extcall sibling of `hfsim_jmp_then_halt` — `hterm` discharges via
    `hterm_halt_extcall` (prefix / driver-dispatched call / suffix threading), so the remaining
    inputs are exactly the two asm-side whole-program facts (`hentryAsm` and the extcall block's
    `hasm`, e.g. `hasm_regularHSVP_call_stop`). -/
theorem hfsim_jmp_then_halt_extcall
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as asMid : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {entryBb termBb : BasicBlock} {n : Nat}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    (hentryAsm : runAsm n offsetToPc prog as = AsmResult.AsmOK asMid)
    (hn : n ≤ prog.length)
    {tfront1 tfront2 : List Instruction} {callInst tterm thd : Instruction} {ttl : List Instruction}
    {tsMid twb tsEnd tsEnd' : VenomState}
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = (tfront1 ++ [callInst] ++ tfront2) ++ [tterm])
    (htcons : (tfront1 ++ [callInst] ++ tfront2) ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnt1 : ∀ inst ∈ tfront1, isTerminator inst.opcode = false)
    (htnt2 : ∀ inst ∈ tfront2, isTerminator inst.opcode = false)
    (htthread1 : execBodyThread tfront1 0 { sMid with instIdx := 0 } = some tsMid)
    (htcall : isExternalCall callInst.opcode = true)
    (htstep : stepExternalCall subEvmFuel callInst tsMid = some twb)
    (htthread2 : execBodyThread tfront2 (tfront1.length + 1)
        { twb with instIdx := tfront1.length + 1 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Halt tsEnd')
    (hasm : ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel tsEnd' asm') :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_jmp_then_terminal hlk1
    (runBlock_jmp_arm ctx entryBb efront eterm ehd etl vs esEnd sMid hebb hecons hephi henonterm
      hethread heterm_step heisterm henohalt)
    hentryAsm hn hlk2
    (hterm_halt_extcall ctx termBb tfront1 tfront2 callInst tterm thd ttl sMid tsMid twb tsEnd
      tsEnd' htbb htcons htphi htnt1 htnt2 htthread1 htcall htstep htthread2 htterm_step hasm)

/-- Two-block `hfsim`, Venom side discharged, for a **reverting** terminal block (REVERT). The
    Revert companion of `hfsim_jmp_then_halt`; the remaining inputs are `hentryAsm` and the
    `AsmRevert` `hasm`. -/
theorem hfsim_jmp_then_revert
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as asMid : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {entryBb termBb : BasicBlock} {n : Nat}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    (hentryAsm : runAsm n offsetToPc prog as = AsmResult.AsmOK asMid)
    (hn : n ≤ prog.length)
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction}
    {tsEnd tsEnd' : VenomState}
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Abort AbortType.RevertAbort tsEnd')
    (hasm : ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel tsEnd' asm') :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_jmp_then_terminal hlk1
    (runBlock_jmp_arm ctx entryBb efront eterm ehd etl vs esEnd sMid hebb hecons hephi henonterm
      hethread heterm_step heisterm henohalt)
    hentryAsm hn hlk2
    (hterm_revert ctx termBb tfront tterm thd ttl sMid tsEnd tsEnd' htbb htcons htphi htnonterm
      htthread htterm_step hasm)

/-- Two-block `hfsim`, Venom side discharged, for a **faulting** terminal block (INVALID). The
    Fault companion of `hfsim_jmp_then_halt`; the remaining inputs are `hentryAsm` and the
    `AsmFault` `hasm`. -/
theorem hfsim_jmp_then_fault
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs sMid : VenomState} {as asMid : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {entryBb termBb : BasicBlock} {n : Nat}
    {efront : List Instruction} {eterm ehd : Instruction} {etl : List Instruction} {esEnd : VenomState}
    (hlk1 : lookupBlock vs.currentBb fn.blocks = some entryBb)
    (hebb : entryBb.instructions = efront ++ [eterm])
    (hecons : efront ++ [eterm] = ehd :: etl)
    (hephi : ehd.opcode ≠ Opcode.PHI)
    (henonterm : ∀ inst ∈ efront, isTerminator inst.opcode = false)
    (hethread : execBodyThread efront 0 { vs with instIdx := 0 } = some esEnd)
    (heterm_step : stepInstBase eterm esEnd = ExecResult.OK sMid)
    (heisterm : isTerminator eterm.opcode = true)
    (henohalt : sMid.halted = false)
    (hentryAsm : runAsm n offsetToPc prog as = AsmResult.AsmOK asMid)
    (hn : n ≤ prog.length)
    {tfront : List Instruction} {tterm thd : Instruction} {ttl : List Instruction}
    {tsEnd tsEnd' : VenomState}
    (hlk2 : lookupBlock sMid.currentBb fn.blocks = some termBb)
    (htbb : termBb.instructions = tfront ++ [tterm])
    (htcons : tfront ++ [tterm] = thd :: ttl)
    (htphi : thd.opcode ≠ Opcode.PHI)
    (htnonterm : ∀ inst ∈ tfront, isTerminator inst.opcode = false)
    (htthread : execBodyThread tfront 0 { sMid with instIdx := 0 } = some tsEnd)
    (htterm_step : stepInstBase tterm tsEnd = ExecResult.Abort AbortType.ExHaltAbort tsEnd')
    (hasm : ∃ asm', runAsm (prog.length - n) offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel tsEnd' asm') :
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_jmp_then_terminal hlk1
    (runBlock_jmp_arm ctx entryBb efront eterm ehd etl vs esEnd sMid hebb hecons hephi henonterm
      hethread heterm_step heisterm henohalt)
    hentryAsm hn hlk2
    (hterm_fault ctx termBb tfront tterm thd ttl sMid tsEnd tsEnd' htbb htcons htphi htnonterm
      htthread htterm_step hasm)

/-- **Arbitrary-length JMP-chain `hfsim`.** Generalises `hfsim_jmp_then_terminal` (its 2-block case is
    `K = 1`) to a straight-line CFG of `K` non-halting JMP blocks feeding one terminal block (`K + 1`
    blocks total), for **any** `K`. The chain is given by index functions `S`/`A`/`Nb`/`B` (Venom
    state / asm state / residual asm budget / block, at each entry `i ≤ K`). Each link `i < K`
    OK-continues (non-halting JMP) to the next entry with a budget transition
    `runAsm (Nb i) … (A i) = runAsm (Nb (i+1)) … (A (i+1))`; the last block `K` is terminal, matching
    `A K` at budget `Nb K`. Discharged by the CFG-walk engine `runBlocks_walk` with the indexed `Entry`
    relation `∃ i ≤ K, s = S i ∧ asm = A i ∧ N = Nb i` — the arbitrary-block-count generalisation of the
    2-state `Entry` in `hfsim_jmp_then_terminal`. (Straight-line only: branching/merging CFGs need a
    non-linear `Entry`; the engine itself already supports them.) -/
theorem hfsim_jmp_chain {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    (K : Nat) (S : Nat → VenomState) (A : Nat → AsmState) (Nb : Nat → Nat) (B : Nat → BasicBlock)
    (hlink_lk : ∀ i, i < K → lookupBlock (S i).currentBb fn.blocks = some (B i))
    (hlink_vs : ∀ i, i < K → ∀ f', match runBlock f' ctx (B i) (S i) with
        | ExecResult.OK s' => s' = S (i + 1) ∧ s'.halted = false
        | ExecResult.Halt _ => False
        | ExecResult.Abort _ _ => False
        | _ => True)
    (hlink_asm : ∀ i, i < K →
        runAsm (Nb i) offsetToPc prog (A i) = runAsm (Nb (i + 1)) offsetToPc prog (A (i + 1)))
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
  runBlocks_walk (offsetToPc := offsetToPc) (prog := prog)
    (fun s asm N => ∃ i, i ≤ K ∧ s = S i ∧ asm = A i ∧ N = Nb i)
    (by
      intro s asm N f' bb hE hlk
      obtain ⟨i, hiK, hs, ha, hN⟩ := hE
      subst hs; subst ha; subst hN
      rcases Nat.lt_or_ge i K with hlt | hge
      · rw [hlink_lk i hlt] at hlk; injection hlk with hbb; subst bb
        have hb := hlink_vs i hlt f'
        cases hrb : runBlock f' ctx (B i) (S i) with
        | OK s' =>
          rw [hrb] at hb; obtain ⟨hnext, hnh⟩ := hb
          simp only [hnh, Bool.false_eq_true, if_false]
          exact ⟨A (i + 1), Nb (i + 1), hlink_asm i hlt, ⟨i + 1, by omega, hnext, rfl, rfl⟩⟩
        | Halt s' => rw [hrb] at hb; exact hb.elim
        | Abort a s' => rw [hrb] at hb; exact hb.elim
        | IntRet _ _ => trivial
        | Error _ => trivial
      · have hiK' : i = K := by omega
        subst hiK'
        rw [hterm_lk] at hlk; injection hlk with hbb; subst bb
        have hb := hterm f'
        cases hrb : runBlock f' ctx (B i) (S i) with
        | OK s' => rw [hrb] at hb; obtain ⟨hh, hex⟩ := hb; simp only [hh, if_true]; exact hex
        | Halt s' => rw [hrb] at hb; exact hb
        | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
        | IntRet _ _ => trivial
        | Error _ => trivial)
    fuel (S 0) (A 0) (Nb 0) ⟨0, by omega, rfl, rfl, rfl⟩

/-- **Arbitrary finite-CFG `hfsim` via a reachable-config set.** The most general finite-CFG shape,
    and the honest general form of frontier #2: a list `configs` of `(Venom state, asm state, residual
    asm budget)` triples, closed under the block step. For each config, its block either terminates
    (matching asm) or OK-continues to *some* config in the set with a budget transition
    `runAsm N … asm = runAsm N' … asm'`. Because the successor config is chosen per Venom outcome, this
    covers chains, **branches** (JNZ diamonds), merges, and bounded loops uniformly — a branch is just
    "the OK arm lands somewhere in the set." Subsumes `hfsim_jmp_chain` (whose linear index `S i` is one
    such set: `configs = (List.range (K+1)).map (fun i => (S i, A i, Nb i))`). Discharged by the CFG-walk
    engine `runBlocks_walk` with `Entry s asm N := (s, asm, N) ∈ configs`. The remaining honest content
    for a *specific* function is *supplying* this closed config set from `genBlockSimulation` per block
    (the well-scheduling invariant tying the asm layout to the block positions). -/
theorem hfsim_of_configs {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    (configs : List (VenomState × AsmState × Nat))
    (hstep : ∀ c ∈ configs, ∀ (f' : Nat) (bb : BasicBlock),
        lookupBlock c.1.currentBb fn.blocks = some bb →
        match runBlock f' ctx bb c.1 with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm c.2.2 offsetToPc prog c.2.1 = AsmResult.AsmHalt asm' ∧
                venomAsmTerminalRel s' asm'
            else
              ∃ c', c' ∈ configs ∧ s' = c'.1 ∧
                runAsm c.2.2 offsetToPc prog c.2.1 = runAsm c'.2.2 offsetToPc prog c'.2.1
        | ExecResult.Halt s' =>
            ∃ asm', runAsm c.2.2 offsetToPc prog c.2.1 = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm c.2.2 offsetToPc prog c.2.1 = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm c.2.2 offsetToPc prog c.2.1 = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel s' asm'
        | _ => True)
    (s0 : VenomState) (as0 : AsmState) (N0 : Nat) (hmem : (s0, as0, N0) ∈ configs) :
    match runBlocks fuel ctx fn s0 with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  runBlocks_walk (offsetToPc := offsetToPc) (prog := prog)
    (fun s asm N => (s, asm, N) ∈ configs)
    (by
      intro s asm N f' bb hE hlk
      have hb := hstep (s, asm, N) hE f' bb hlk
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        by_cases hh : s'.halted
        · simp only [hh, if_true] at hb ⊢; exact hb
        · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
          obtain ⟨c', hc'mem, hs'eq, hasmeq⟩ := hb
          exact ⟨c'.2.1, c'.2.2, hasmeq, by rw [hs'eq]; exact hc'mem⟩
      | Halt s' => rw [hrb] at hb; exact hb
      | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
      | IntRet _ _ => trivial
      | Error _ => trivial)
    fuel s0 as0 N0 hmem

/-- **Well-scheduling invariant → `hfsim` (relational; data-dependent CFGs).** The proper interface
    between `genBlockSimulation` (per-block) and the CFG-walk engine for functions whose control flow is
    data-dependent — so the reachable *states* are not a fixed finite list and `hfsim_of_configs` does
    not apply. A per-block predicate `P bb s asm N` — read as "the asm is *well-scheduled* for block
    `bb`: right entry pc, `venomAsmRel` holds, budget suffices" — is carried at each block entry. The
    per-block hypothesis is exactly `genBlockSimulation`'s shape: the block either terminates (matching
    asm) or OK-continues to its successor block `bb'`, where the asm budget threads
    (`runAsm N … asm = runAsm N' … asm'`) and `P bb'` holds again. Discharged by `runBlocks_walk` with
    the *relational* `Entry s asm N := ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧ P bb s asm N`
    (block matched by `s.currentBb`, state left free). This is the honest general interface; the deep
    remaining content is *instantiating* `P` with the concrete `venomAsmRel`-at-`labelOffset` invariant
    and discharging `hstep` from the whole-function asm layout (each block's plan sits at its label
    offset) — that is now cleanly a per-block obligation, not a whole-walk one. -/
theorem hfsim_of_blockInv {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    (P : BasicBlock → VenomState → AsmState → Nat → Prop)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb → P bb s asm N →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ asm' N' bb', runAsm N offsetToPc prog asm = runAsm N' offsetToPc prog asm' ∧
                lookupBlock s'.currentBb fn.blocks = some bb' ∧ P bb' s' asm' N'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (s0 : VenomState) (as0 : AsmState) (N0 : Nat) (bb0 : BasicBlock)
    (hlk0 : lookupBlock s0.currentBb fn.blocks = some bb0) (hP0 : P bb0 s0 as0 N0) :
    match runBlocks fuel ctx fn s0 with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  runBlocks_walk (offsetToPc := offsetToPc) (prog := prog)
    (fun s asm N => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧ P bb s asm N)
    (by
      intro s asm N f' bb hE hlk
      obtain ⟨bb', hlk', hP⟩ := hE
      rw [hlk] at hlk'; injection hlk' with hbbeq; subst hbbeq
      have hb := hstep bb s asm N f' hlk hP
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        by_cases hh : s'.halted
        · simp only [hh, if_true] at hb ⊢; exact hb
        · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
          obtain ⟨asm', N', bb'', hrun, hlk'', hP'⟩ := hb
          exact ⟨asm', N', hrun, bb'', hlk'', hP'⟩
      | Halt s' => rw [hrb] at hb; exact hb
      | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
      | IntRet _ _ => trivial
      | Error _ => trivial)
    fuel s0 as0 N0 ⟨bb0, hlk0, hP0⟩

/-- **Concrete `venomAsmRel`-at-`labelOffset` well-scheduling → `hfsim`** (flexible asm budget).
    Instantiates `hfsim_of_blockInv`'s abstract per-block predicate `P` with the concrete
    well-scheduling invariant `P bb s asm N := asm.pc = pcOf bb.label ∧ venomAsmRel labelOffsets
    (psOf bb.label) s asm` — at each block `bb` the asm sits at `bb`'s scheduled entry pc and
    `venomAsmRel` holds with `bb`'s scheduled entry plan state; the asm budget `N` threads freely. The
    per-block hypothesis `hstep` is in exactly the `genBlockSimulation` / `block_jmp_sim` output
    language: a terminal block matches asm at budget `N`; a continuing (JMP/JNZ) block runs `blockLen ≤
    N` asm steps to the successor's scheduled entry (`asm'.pc = pcOf bb'.label`), still `venomAsmRel`-
    related with the successor's entry plan state, and the budget threads as `N ↦ N - blockLen` (via
    `runAsm_append_ok`) — precisely `block_jmp_sim`'s `runAsm blockLen asm = AsmOK asm'` at the
    successor. (This flexible budget — not `prog.length - asm.pc` — is what makes the JMP transition
    clean for *any* jump target, not just fall-through.) The single deep remaining obligation is now
    isolated: the post-block plan state equals the successor's entry plan state `psOf bb'` — the
    join-point / cross-block plan-state threading of `generateFnPlan`. -/
theorem hfsim_venomAsmRelSched {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label → venomAsmRel labelOffsets (psOf bb.label) s asm →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel labelOffsets (psOf bb'.label) s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (s0 : VenomState) (as0 : AsmState) (N0 : Nat) (bb0 : BasicBlock)
    (hlk0 : lookupBlock s0.currentBb fn.blocks = some bb0)
    (hpc0 : as0.pc = pcOf bb0.label) (hrel0 : venomAsmRel labelOffsets (psOf bb0.label) s0 as0) :
    match runBlocks fuel ctx fn s0 with
    | ExecResult.Halt vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
        ∃ as', runAsm N0 offsetToPc prog as0 = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | _ => True :=
  hfsim_of_blockInv (offsetToPc := offsetToPc)
    (fun bb s asm _ => asm.pc = pcOf bb.label ∧ venomAsmRel labelOffsets (psOf bb.label) s asm)
    (by
      intro bb s asm N f' hlk ⟨hpc, hrel⟩
      have hb := hstep bb s asm N f' hlk hpc hrel
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        by_cases hh : s'.halted
        · simp only [hh, if_true] at hb ⊢; exact hb
        · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
          obtain ⟨bb', asm', blockLen, hlk', hrun, hle, hpc', hrel'⟩ := hb
          refine ⟨asm', N - blockLen, bb', ?_, hlk', hpc', hrel'⟩
          conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
          exact runAsm_append_ok hrun
      | Halt s' => rw [hrb] at hb; exact hb
      | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
      | IntRet _ _ => trivial
      | Error _ => trivial)
    s0 as0 N0 bb0 hlk0 ⟨hpc0, hrel0⟩

/-- **Well-scheduling JMP step from `block_jmp_sim`.** Produces `hfsim_venomAsmRelSched`'s per-block
    OK-continue clause for a JMP/JNZ block directly from `block_jmp_sim`'s output (the block's asm runs
    `blockLen` steps to the successor's entry `asm'` at index `idx`, still `venomAsmRel`-related with the
    post-block plan state `psPostBody`), given the two `generateFnPlan` scheduling facts: `idx = pcOf
    bb'.label` (the JMP target index is the successor's scheduled entry pc) and `psPostBody = psOf
    bb'.label` (the post-block plan state is the successor's entry plan state — the join-point / cross-
    block plan-state threading). With these two facts, the whole well-scheduling JMP transition is
    mechanical — the parallel of `asmStack_top2_of_planStackRel` for the RETURN operand coupling: both
    frontiers now bottom out at explicitly-stated `generateFnPlan` plan-state facts. -/
theorem wellsched_jmp_ok_continue {fn : IrFunction} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    {asm asm' : AsmState} {sPostBody : VenomState} {psPostBody : PlanState}
    {bb' : BasicBlock} {blockLen idx N : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody sPostBody asm')
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock sPostBody.currentBb fn.blocks = some bb')
    (hplan : psPostBody = psOf bb'.label) :
    ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
      lookupBlock sPostBody.currentBb fn.blocks = some bb'' ∧
      runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
      asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) sPostBody asm'' := by
  refine ⟨bb', asm', blockLen, hlk', hrun, hle, ?_, ?_⟩
  · rw [hpcidx, hidx]
  · rw [← hplan]; exact hrel

/-- **Concrete well-scheduling JMP step.** Assembles the full `hfsim_venomAsmRelSched` per-block
    OK-continue clause for a JMP block against the *concrete* schedule `pcOf := pcOfLabel prog`. From
    `block_jmp_sim` (the resolved `[push-label ; JUMP]` runs `bodyLen+2` steps to the successor's entry
    `asm'`, still `venomAsmRel`-related with the post-body plan state), the concrete pc bridge
    `resolvedJump_idx_eq_pcOfLabel` (`idx = pcOfLabel prog bb'.label`), and the plan-state fact
    (`psPostBody = psOf bb'.label`), `wellsched_jmp_ok_continue` yields the clause verbatim. Both
    scheduling obligations are now discharged concretely: pc via the label index, plan via the DFS/join
    threading. This is the JMP branch of the global assembly's per-block `hstep`, end to end. -/
theorem wellsched_jmp_step_pcOfLabel {fn : IrFunction} {labelOffsets : AssocList String Nat}
    {prog pre suf : List AsmInst} {asm asmPreJmp : AsmState} {bb' : BasicBlock}
    {off idx bodyLen N : Nat} {psOf : String → PlanState}
    {psPostBody : PlanState} {sPostBody : VenomState}
    (hprog : prog = pre ++ AsmInst.AsmLabel bb'.label :: suf)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel bb'.label ∧ inst ≠ AsmInst.AsmDataHeader bb'.label)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel bb'.label)
    (hbody : runAsm bodyLen (asmResolve prog).2 prog asm = AsmResult.AsmOK asmPreJmp)
    (hrel : venomAsmRel labelOffsets psPostBody sPostBody asmPreJmp)
    (hpc1 : asmPreJmp.pc < prog.length)
    (hpush : prog.get ⟨asmPreJmp.pc, hpc1⟩
      = resolveInst (computeLabelOffsets prog).2 (AsmInst.AsmPushLabel bb'.label))
    (hoff_lk : AssocList.lookup String Nat (computeLabelOffsets prog).2 bb'.label = some off)
    (hoff : off < 2 ^ 256)
    (hpc2 : asmPreJmp.pc + 1 < prog.length)
    (hjump : prog.get ⟨asmPreJmp.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat (asmResolve prog).2 off = some idx)
    (hle : bodyLen + 2 ≤ N)
    (hlk' : lookupBlock sPostBody.currentBb fn.blocks = some bb')
    (hplan : psPostBody = psOf bb'.label) :
    ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
      lookupBlock sPostBody.currentBb fn.blocks = some bb'' ∧
      runAsm blockLen' (asmResolve prog).2 prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
      asm''.pc = pcOfLabel prog bb''.label ∧
      venomAsmRel labelOffsets (psOf bb''.label) sPostBody asm'' := by
  obtain ⟨asm', hrun', hrel', hpcidx⟩ :=
    block_jmp_sim hbody hrel hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk
  have hidx : idx = pcOfLabel prog bb'.label := by
    rw [hprog] at hoff_lk hidx_lk ⊢
    exact resolvedJump_idx_eq_pcOfLabel pre suf bb'.label off idx hsuf hpre hoff_lk hidx_lk
  exact wellsched_jmp_ok_continue (pcOfLabel prog) psOf hrun' hrel' hpcidx hle hidx hlk' hplan

/-- **The whole-function bridge: per-block `hstep` ⇒ `genFnSimulation`'s conclusion.** This is the
    missing top-level wiring (`genFnSimulation ∘ hfsim_venomAsmRelSched`). `hfsim_venomAsmRelSched`
    *produces* the `runBlocks`-keyed asm correspondence from a per-block scheduled step obligation
    `hstep`; that produced correspondence is **definitionally** `genFnSimulation`'s `hfsim` hypothesis
    (same `runBlocks`/`runAsm (executePlan ops)` shape). So supplying `hstep` (the per-block simulation,
    the content built across this file) together with the entry setup — the entry block `bb0`, its pc
    `as.pc = pcOf bb0.label`, and its scheduled plan `psOf bb0.label = initPlanState fnEom` — discharges
    the whole-function `genFnSimulation` conclusion *unconditionally over the CFG walk*, with the
    `OK ⇒ False` arm coming from `genFnSimulation` (`runBlocks_never_ok`). -/
theorem genFnSim_of_hstep
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {labelOffsets : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hrel  : venomAsmRel labelOffsets (initPlanState fnEom) vs as)
    (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
             stepMemSafe (initPlanState fnEom).alloc vs1 vs2)
    (hready : codegenReadyFn fn)
    (pcOf : String → Nat) (psOf : String → PlanState)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel labelOffsets (psOf bb.label) s asm →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel labelOffsets (psOf bb'.label) s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock vs.currentBb fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hentryps : psOf bb0.label = initPlanState fnEom) :
    let prog := (asmResolve (executePlan ops)).1
    let offsetToPc := (asmResolve (executePlan ops)).2
    match runBlocks fuel ctx fn vs with
    | ExecResult.Halt vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.RevertAbort vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.Abort AbortType.ExHaltAbort vs' =>
      ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
    | ExecResult.OK _ => False
    | ExecResult.IntRet _ _ => True
    | ExecResult.Error _ => True := by
  refine genFnSimulation hplan hrel hsafe hready ?_
  exact hfsim_venomAsmRelSched (prog := (asmResolve (executePlan ops)).1)
    (offsetToPc := (asmResolve (executePlan ops)).2) (labelOffsets := labelOffsets)
    pcOf psOf hstep vs as (asmResolve (executePlan ops)).1.length bb0 hlk0 hpc0
    (by rw [hentryps]; exact hrel)

/-- **Whole-context codegen correctness via the scheduled per-block step (`genFnSimulation →
    codegen_correct`).** The top-level `runContext`-keyed statement, discharged through the *scheduling*
    driver rather than the abstract-`Entry` `runBlocks_walk`: `runContext` peels to the entry function's
    `runBlocks` (via `hent`/`hlk`/`hlbl`), then `genFnSim_of_hstep` supplies the whole-function
    correspondence from the per-block `hstep`. `finalStateRel` is definitionally `venomAsmTerminalRel`,
    so the produced relation matches; the walk's `OK` arm is impossible (`genFnSim_of_hstep` carries it
    as `False`), collapsing into the top statement's `_ => True`. This closes the last structural gap
    between the per-block simulation content and the top codegen-correctness theorem: no `hbsim`, only
    `hstep` + the entry setup. -/
theorem codegen_correct_of_hstep
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {labelOffsets : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
             stepMemSafe (initPlanState fnEom).alloc vs1 vs2)
    (hready : codegenReadyFn fn)
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel labelOffsets (psOf bb.label) s asm →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel labelOffsets (psOf bb'.label) s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hentryps : psOf bb0.label = initPlanState fnEom)
    (hrel : venomAsmRel labelOffsets (initPlanState fnEom)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hrc : runContext fuel ctx vs
      = runBlocks fuel ctx fn { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } := by
    simp only [runContext, hent, hlk, runFunction, hlbl]
  rw [hrc]
  have hg := genFnSim_of_hstep (fuel := fuel) hplan hrel hsafe hready pcOf psOf hstep bb0 hlk0 hpc0 hentryps
  cases hrb : runBlocks fuel ctx fn { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } with
  | Halt vs' => rw [hrb] at hg; exact hg
  | Abort a vs' => cases a <;> (rw [hrb] at hg; exact hg)
  | OK vs' => rw [hrb] at hg; exact hg.elim
  | IntRet _ _ => trivial
  | Error _ => trivial

/-- **Suppliable whole-context codegen correctness via a scheduled, budget-ranked per-block step.**
    Unlike the abstract `hfsim_venomAsmRelSched`/`codegen_correct_of_hstep` (whose `hstep` is quantified
    over *all* asm budgets `N` and is therefore unsuppliable — `runAsm 0 = AsmOK ≠ AsmHalt`), here the
    per-block `hstep` carries an **asm-work ranking** `wOf : String → Nat`: it may assume the budget is
    large enough (`wOf bb.label ≤ N`) and must show a continuing block *decreases* the rank past the
    step it consumes (`wOf bb'.label + blockLen ≤ wOf bb.label`). That single inequality threads the
    lower bound through the CFG walk (`N ↦ N - blockLen`), so the halt/continue clauses become provable
    at the budgets the walk actually uses. Built on the N-flexible `codegen_correct` driver (whose
    `Entry` is a free parameter), instantiated with the scheduling invariant + the rank bound. -/
theorem codegen_correct_sched
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel lo (psOf bb'.label) s' asm' ∧
                wOf bb'.label + blockLen ≤ wOf bb.label
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl)
    (Entry := fun s asm N => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
       asm.pc = pcOf bb.label ∧ venomAsmRel lo (psOf bb.label) s asm ∧ wOf bb.label ≤ N ∧
       s.halted = false)
    hplan hent hlk hlbl ?_ ⟨bb0, hlk0, hpc0, hrel, hw0, hvshalt⟩
  intro s asm N f' bb hE hlk'
  obtain ⟨bb', hlkbb, hpc, hvrel, hwN, hnh⟩ := hE
  rw [hlk'] at hlkbb; injection hlkbb with hbbeq; subst hbbeq
  have hb := hstep bb s asm N f' hlk' hpc hvrel hwN hnh
  cases hrb : runBlock f' ctx bb s with
  | OK s' =>
    rw [hrb] at hb
    by_cases hh : s'.halted
    · simp only [hh, if_true] at hb ⊢; exact hb
    · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
      obtain ⟨bb'', asm', blockLen, hlk'', hrun, hle, hpc', hvrel', hwdec⟩ := hb
      refine ⟨asm', N - blockLen, ?_, bb'', hlk'', hpc', hvrel', by omega, by simp⟩
      conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
      exact runAsm_append_ok hrun
  | Halt s' => rw [hrb] at hb; exact hb
  | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
  | IntRet _ _ => trivial
  | Error _ => trivial

/-- **Budget-ranked codegen correctness with the Entry invariant — `hstep` may assume reachability.**

    `codegen_correct_sched`'s `hstep` must hold at *every* block of `fn`, including blocks the walk can
    never enter. But the whole `_reach` hstep family (`hstep_regularHSVP_*_reach`) is stated for blocks
    that are `CfgReach`-able from the entry — that is the hypothesis that replaced `JmpChainTo` and made
    branch targets reachable at all. Without threading reachability through the driver's invariant,
    those hsteps could not be fed to the driver.

    This variant strengthens the `Entry` predicate with `CfgReach (cfgAnalyze fn) entryLbl s.currentBb`
    and hands it to `hstep` as an extra hypothesis. Preservation is `CfgReach_of_runBlock`: a block
    hands control only to a CFG successor, so a reachable block steps to a reachable block. The base
    case is `CfgReach.base` (the walk starts at the entry).

    Its two new side conditions are per-function and decidable: labels are distinct, and each block's only
    terminator is its last instruction.

    RETRACTION. This docstring used to list a third: "no block contains a `DJMP` (the one terminator that
    computes its target from a runtime selector rather than a label operand, and so could leave the static
    CFG)". That is false. A `DJMP`'s targets *are* label operands — the selector only picks among them —
    and `djmp_target_is_static_succ` proves the block it hands control to is always a static CFG successor.
    `CfgReach_of_runBlock`, which does the actual preservation, never carried a `DJMP` exclusion.

    The `_reach` hsteps no longer carry one either: their `hgood` has been replaced by
    `¬ IsFreshLabel bb.label`, a fact about naming. `DJMP` mints fresh trampoline labels, and the counting
    argument behind `hpreuniq` only ever asks about *block* labels — so all it needs is that the two do
    not collide. -/
theorem codegen_correct_sched_reach
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hwfblocks : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions,
      isTerminator inst.opcode = true → inst = b.instructions.getLast!)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        CfgReach (cfgAnalyze fn) entryLbl bb.label →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel lo (psOf bb'.label) s' asm' ∧
                wOf bb'.label + blockLen ≤ wOf bb.label
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  -- `lookupBlock` finds a block whose label *is* the one looked up
  have hlbl_of_lk : ∀ (l : String) (b : BasicBlock), lookupBlock l fn.blocks = some b → b.label = l := by
    intro l b hb
    have := List.find?_some hb
    simpa using this
  have hmem_of_lk : ∀ (l : String) (b : BasicBlock), lookupBlock l fn.blocks = some b → b ∈ fn.blocks :=
    fun l b hb => List.mem_of_find?_eq_some hb
  refine codegen_correct (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl)
    (Entry := fun s asm N => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
       asm.pc = pcOf bb.label ∧ venomAsmRel lo (psOf bb.label) s asm ∧ wOf bb.label ≤ N ∧
       s.halted = false ∧ CfgReach (cfgAnalyze fn) entryLbl bb.label)
    hplan hent hlk hlbl ?_
    ⟨bb0, hlk0, hpc0, hrel, hw0, hvshalt, by rw [hlbl_of_lk _ _ hlk0]; exact CfgReach.base⟩
  intro s asm N f' bb hE hlk'
  obtain ⟨bb', hlkbb, hpc, hvrel, hwN, hnh, hreach⟩ := hE
  rw [hlk'] at hlkbb; injection hlkbb with hbbeq; subst hbbeq
  have hb := hstep bb s asm N f' hlk' hpc hvrel hwN hnh hreach
  cases hrb : runBlock f' ctx bb s with
  | OK s' =>
    rw [hrb] at hb
    by_cases hh : s'.halted
    · simp only [hh, if_true] at hb ⊢; exact hb
    · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
      obtain ⟨bb'', asm', blockLen, hlk'', hrun, hle, hpc', hvrel', hwdec⟩ := hb
      -- the Entry invariant: a reachable block hands control only to a reachable block
      have hmem : bb ∈ fn.blocks := hmem_of_lk _ _ hlk'
      have hreach' : CfgReach (cfgAnalyze fn) entryLbl s'.currentBb :=
        CfgReach_of_runBlock hnd hmem (hwfblocks bb hmem) hreach hrb
      refine ⟨asm', N - blockLen, ?_, bb'', hlk'', hpc', hvrel', by omega, by simp,
        by rw [hlbl_of_lk _ _ hlk'']; exact hreach'⟩
      conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
      exact runAsm_append_ok hrun
  | Halt s' => rw [hrb] at hb; exact hb
  | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
  | IntRet _ _ => trivial
  | Error _ => trivial

/-- **Scheduled, loop-capable codegen correctness.** The counterpart of `codegen_correct_sched_reach`
    for cyclic CFGs: the same canonical schedule (`pcOf`/`psOf`) and the same reachability-carrying
    `Entry`, but the budget comes from `runBlocks_walk_fuel` rather than a program-position rank.

    Two things change in the per-block obligation, and both are *weakenings*:
      * the budget precondition is the uniform `B ≤ N` instead of `wOf bb.label ≤ N`;
      * the continuing block must show `blockLen ≤ B` instead of the strict rank decrease
        `wOf succ + blockLen ≤ wOf bb`.

    Nothing orders the labels, so a back-edge has nothing to violate — which is the whole point, since
    `ranked_walk_no_back_edge` shows a program-position rank *cannot exist* for a cyclic CFG. The asm
    budget is `fuel * B`; `prog.length` is always a legal `B` (a block's asm is a segment of `prog`),
    and a larger budget is not a weaker conclusion because a halted run stays halted. -/
theorem codegen_correct_fuel_sched
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat} (B : Nat)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hwfblocks : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions,
      isTerminator inst.opcode = true → inst = b.instructions.getLast!)
    (pcOf : String → Nat) (psOf : String → PlanState)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        B ≤ N →
        s.halted = false →
        CfgReach (cfgAnalyze fn) entryLbl bb.label →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ B ∧
                asm'.pc = pcOf bb'.label ∧ venomAsmRel lo (psOf bb'.label) s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (fuel * B)
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (fuel * B)
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (fuel * B)
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hlbl_of_lk : ∀ (l : String) (b : BasicBlock), lookupBlock l fn.blocks = some b → b.label = l := by
    intro l b hb
    have := List.find?_some hb
    simpa using this
  have hmem_of_lk : ∀ (l : String) (b : BasicBlock), lookupBlock l fn.blocks = some b → b ∈ fn.blocks :=
    fun l b hb => List.mem_of_find?_eq_some hb
  refine codegen_correct_fuel (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl) B
    (Entry := fun s asm => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
       asm.pc = pcOf bb.label ∧ venomAsmRel lo (psOf bb.label) s asm ∧
       s.halted = false ∧ CfgReach (cfgAnalyze fn) entryLbl bb.label)
    hplan hent hlk hlbl ?_
    ⟨bb0, hlk0, hpc0, hrel, hvshalt, by rw [hlbl_of_lk _ _ hlk0]; exact CfgReach.base⟩
  intro s asm N f' bb hE hlk' hBN
  obtain ⟨bb', hlkbb, hpc, hvrel, hnh, hreach⟩ := hE
  rw [hlk'] at hlkbb; injection hlkbb with hbbeq; subst hbbeq
  have hb := hstep bb s asm N f' hlk' hpc hvrel hBN hnh hreach
  cases hrb : runBlock f' ctx bb s with
  | OK s' =>
    rw [hrb] at hb
    by_cases hh : s'.halted
    · simp only [hh, if_true] at hb ⊢; exact hb
    · simp only [hh, Bool.false_eq_true, if_false] at hb ⊢
      obtain ⟨bb'', asm', blockLen, hlk'', hrun, hle, hpc', hvrel'⟩ := hb
      have hmem : bb ∈ fn.blocks := hmem_of_lk _ _ hlk'
      have hreach' : CfgReach (cfgAnalyze fn) entryLbl s'.currentBb :=
        CfgReach_of_runBlock hnd hmem (hwfblocks bb hmem) hreach hrb
      exact ⟨asm', blockLen, hrun, hle,
        bb'', hlk'', hpc', hvrel', by simp [hh],
        by rw [hlbl_of_lk _ _ hlk'']; exact hreach'⟩
  | Halt s' => rw [hrb] at hb; exact hb
  | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
  | IntRet _ _ => trivial
  | Error _ => trivial

/-- **JMP-continue clause for the budget-ranked `hstep` (`codegen_correct_sched`).** The rank-carrying
    analog of `wellsched_jmp_ok_continue`: from `block_jmp_sim`'s output (the block's asm runs `blockLen`
    steps to the successor entry `asm'` at index `idx`, still `venomAsmRel`-related with the post-block
    plan state `psPostBody`), the two scheduling facts (`idx = pcOf bb'.label`, `psPostBody = psOf
    bb'.label` — the value lift), and the **rank decrease** `wOf bb'.label + blockLen ≤ wOf bb.label`,
    produces `codegen_correct_sched`'s OK-continue clause verbatim (the extra `wOf` conjunct that threads
    the budget lower bound through the walk). Reduces a JMP block's whole `hstep` obligation to
    `block_jmp_sim` + the value lift (`hplan`) + one arithmetic rank fact. -/
theorem wellsched_jmp_sched_ok_continue {fn : IrFunction} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {asm asm' : AsmState} {sPostBody : VenomState} {psPostBody : PlanState}
    {bb' : BasicBlock} {blockLen idx N : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody sPostBody asm')
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock sPostBody.currentBb fn.blocks = some bb')
    (hplan : psPostBody = psOf bb'.label)
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
      lookupBlock sPostBody.currentBb fn.blocks = some bb'' ∧
      runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
      asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) sPostBody asm'' ∧
      wOf bb''.label + blockLen' ≤ wOf bb.label := by
  refine ⟨bb', asm', blockLen, hlk', hrun, hle, ?_, ?_, hwdec⟩
  · rw [hpcidx, hidx]
  · rw [← hplan]; exact hrel

/-- **`venomAsmRel`-based JMP-continue clause for the budget-ranked `hstep`.** A relaxation of
    `wellsched_jmp_sched_ok_continue` that decouples the value lift from *plan-state equality*: instead
    of `psPostBody = psOf bb'.label` (which for a phi-join is the wrong shape, and even phi-free carries
    traversal-dependent spill/alloc), it takes the **successor entry relation directly** —
    `venomAsmRel labelOffsets (psOf bb'.label) sPostBody asm'`. This is exactly what a phi-free CFG can
    supply from `block_jmp_sim`'s output via stack-uniformity (`jmp_exit_stack_liveness_no_phi`, the
    exit stack is the predecessor-independent `liveVarsAt`) together with `venomAsmRel_alloc_widen`
    (§6, the allocator only widens) — no on-the-nose plan-state match required. -/
theorem wellsched_jmp_sched_ok_continue' {fn : IrFunction} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {asm asm' : AsmState} {sPostBody : VenomState}
    {bb' : BasicBlock} {blockLen idx N : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hvrel' : venomAsmRel labelOffsets (psOf bb'.label) sPostBody asm')
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock sPostBody.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
      lookupBlock sPostBody.currentBb fn.blocks = some bb'' ∧
      runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
      asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) sPostBody asm'' ∧
      wOf bb''.label + blockLen' ≤ wOf bb.label := by
  exact ⟨bb', asm', blockLen, hlk', hrun, hle, by rw [hpcidx, hidx], hvrel', hwdec⟩

/-- **`venomAsmRel` transfers across plan states with equal stack/spilled and a widened allocator.**
    `venomAsmRel` reads a plan state only through its `stack` (`planStackRel`), `spilled`
    (`planSpillRel`), and `alloc` (`memoryRel`). So it transfers from `ps1` to `ps2` whenever their
    stacks and spill maps agree and `ps2`'s allocator merely widens `ps1`'s (same `fnEom`, `≥`
    `nextOffset` — `memoryRel_mono_alloc`). Combined with `jmp_exit_stack_liveness_no_phi` (phi-free
    exit stack = the predecessor-independent `liveVarsAt`), this is the transfer that supplies
    `wellsched_jmp_sched_ok_continue'`'s successor relation for a **phi-free** edge without any
    on-the-nose plan-state equality — closing the value lift's stack/alloc dimensions. -/
theorem venomAsmRel_congr_widen {lo : AssocList String Nat} {ps1 ps2 : PlanState}
    {vs : VenomState} {as : AsmState}
    (hstk : ps1.stack = ps2.stack) (hsp : ps1.spilled = ps2.spilled)
    (hfe : ps1.alloc.fnEom = ps2.alloc.fnEom) (hno : ps1.alloc.nextOffset ≤ ps2.alloc.nextOffset)
    (h : venomAsmRel lo ps1 vs as) : venomAsmRel lo ps2 vs as := by
  obtain ⟨hStk, hSp, hMem, hrest⟩ := h
  exact ⟨hstk ▸ hStk, hsp ▸ hSp, memoryRel_mono_alloc hfe hno hMem, hrest⟩

/-- **Phi-free JMP-block `hstep` continue clause with a canonical `psOf`.** The packaged phi-free value
    lift: from `block_jmp_sim`'s output (`hrun`/`hrel`/`hpcidx` — the block runs `blockLen` asm steps to
    the successor entry `asm'`, still `venomAsmRel`-related with the post-block plan `psPostBody`), the
    fact that `psPostBody` **agrees with the canonical `psOf bb'`** on stack (`jmp_exit_stack_liveness_no_phi`:
    the phi-free exit stack is the predecessor-independent `liveVarsAt`) and spilled (∅ for spill-free)
    with only a widened allocator, plus the scheduling facts, produces `codegen_correct_sched`'s
    OK-continue clause. Composes `venomAsmRel_congr_widen` (the transfer to the canonical relation, so no
    on-the-nose plan-state equality) with `wellsched_jmp_sched_ok_continue'`. This is the per-block JMP
    content of a universally-quantified phi-free + spill-free capstone. -/
theorem wellsched_jmp_canonical_continue {fn : IrFunction} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {asm asm' : AsmState} {sPostBody : VenomState} {psPostBody : PlanState}
    {bb' : BasicBlock} {blockLen idx N : Nat}
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody sPostBody asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock sPostBody.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
      lookupBlock sPostBody.currentBb fn.blocks = some bb'' ∧
      runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
      asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) sPostBody asm'' ∧
      wOf bb''.label + blockLen' ≤ wOf bb.label := by
  have hvrel' : venomAsmRel labelOffsets (psOf bb'.label) sPostBody asm' :=
    venomAsmRel_congr_widen hstk hsp hfe hno hrel
  exact wellsched_jmp_sched_ok_continue' pcOf psOf wOf hrun hvrel' hpcidx hle hidx hlk' hwdec

/-- **Full per-block `hstep` clause for a phi-free JMP block.** Wraps `wellsched_jmp_canonical_continue`
    into `codegen_correct_sched`'s complete `hstep` match: given that the block's Venom step is a
    (non-halting) JMP (`runBlock … = OK s'`, `s'.halted = false`) and its whole-program asm sim
    (`block_jmp_sim`'s output: `blockLen` steps to the successor entry `asm'`, `venomAsmRel psPostBody`),
    together with the canonical-`psOf` agreement facts (stack/spilled equal, alloc widen) and the
    scheduling facts, produces the `hstep` clause. The `OK` arm reduces (via `s'.halted = false`) to the
    OK-continue clause, discharged by `wellsched_jmp_canonical_continue`; the `Halt`/`Abort` arms are
    vacuous (`runBlock = OK`). The per-block JMP dispatch of the §5 assembly, complete. -/
theorem hstep_jmp_block {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen idx : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [hrb]
  simp only [hnh, Bool.false_eq_true, if_false]
  exact wellsched_jmp_canonical_continue pcOf psOf wOf hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk' hwdec


/-! ### Threading a join into the whole-function walk

The seven canonical `hstep`s carry an `hphi : hd.opcode ≠ Opcode.PHI`, which is why a join block could
not be handed to the walk. But that hypothesis lives in the theorems that *derive* an `hstep`'s inputs
from the compiler, not in the walk clause itself: `hstep_jmp_block` is parameterised entirely on
`hrb : runBlock … = OK s'` and `hrel`, and never asks what the block's head is. The walk was already
join-compatible; what was missing was a way to *supply* those two inputs for a block that starts with
phis — which is exactly what this arc's join lemmas produce. -/

/-- The walk's per-block obligation, as a predicate on the block's `ExecResult`. -/
def WalkStep (fn : IrFunction) (pcOf : String → Nat) (psOf : String → PlanState)
    (wOf : String → Nat) (labelOffsets : AssocList String Nat)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (bb : BasicBlock)
    (asm : AsmState) (N : Nat) : ExecResult → Prop
  | ExecResult.OK s' =>
      if s'.halted then
        ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      else
        ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
          lookupBlock s'.currentBb fn.blocks = some bb'' ∧
          runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
          asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
          wOf bb''.label + blockLen' ≤ wOf bb.label
  | ExecResult.Halt s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.RevertAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.ExHaltAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
  | _ => True

/-- **Every `hstep` is already join-aware.** -/
theorem WalkStep_join {fn ctx pcOf psOf wOf labelOffsets offsetToPc prog bb asm N f'}
    {s sPhi : VenomState}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions })) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) := by
  rw [runBlock_eq_execBlock_of_phis hev]
  exact hres

/-- **CORRESPONDENCE.** `WalkStep` is not a private mirror of the walk's obligation: it *is* that
obligation. `hstep_jmp_block`'s conclusion typechecks as a `WalkStep` on the nose, which is what makes
`WalkStep_join` a statement about the real walk rather than about a definition I wrote. -/
theorem hstep_jmp_block_ws {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen idx : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  hstep_jmp_block pcOf psOf wOf hrb hnh hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk' hwdec

/-- **The JMP `hstep`, for a block whose head is a `PHI`** — a join, threaded into the walk. Its two
real inputs are the post-phi body result (`hrb`, an `execBlock` from the phi-prologue's exit state) and
the post-phi relation (`hrel`, from `venomAsmRel_phi_join'`). Both are what the join lemmas of this arc
hand back, so a join block now produces the walk's per-block obligation like any other block. -/
theorem hstep_jmp_block_join {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s sPhi s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen idx : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hrb : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
             = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  hstep_jmp_block_ws pcOf psOf wOf
    (by rw [runBlock_eq_execBlock_of_phis hev]; exact hrb)
    hnh hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk' hwdec



/-- **Generic JNZ-taken per-block `hstep` clause.** A block ending in `JNZ cond ifNz ifZ` with `cond ≠ 0`
    steps (Venom) to `OK (jumpTo ifNz …)` -- exactly the `OK`-producing shape `hstep_jmp_block` already
    consumes (JNZ is a JMP-like OK step). Given the taken-branch asm run (`hrun`, from
    `resolved_jumpi_taken_sim`) to the `ifNz` successor entry and the scheduling facts, this produces the
    full per-block `hstep` match -- the conditional-branch counterpart of `hstep_jmp_block`, for a bare
    `[JNZ …]` block. Fuel is split: too little errors into the vacuous catch-all; enough runs the branch
    (`runBlock_ok`). -/
theorem hstep_jnz_taken {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen idx : Nat} {jnzInst : Instruction} {condOp : Operand} {ifNz ifZ : String}
    {cond : bytes32}
    (hbb : bb.instructions = [jnzInst])
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { s with instIdx := 0 } = some cond)
    (hcondne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hsnothalt : s.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody (jumpTo ifNz { s with instIdx := 0 }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  -- Venom JNZ step: OK (jumpTo ifNz)
  have hstepj : stepInstBase jnzInst { s with instIdx := 0 }
      = ExecResult.OK (jumpTo ifNz { s with instIdx := 0 }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcondne) h
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, hbb, hopc]
  | succ k =>
    have hrb : runBlock (k + 1) ctx bb s = ExecResult.OK (jumpTo ifNz { s with instIdx := 0 }) := by
      have h := runBlock_ok ctx bb k [] jnzInst jnzInst [] s { s with instIdx := 0 }
        (jumpTo ifNz { s with instIdx := 0 })
        (by simpa using hbb) rfl (by rw [hopc]; decide)
        (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepj
        (by rw [hopc]; decide) (by rw [jumpTo]; exact hsnothalt)
      simpa using h
    have hnh : (jumpTo ifNz { s with instIdx := 0 }).halted = false := by
      rw [jumpTo]; exact hsnothalt
    have hlk'' : lookupBlock (jumpTo ifNz { s with instIdx := 0 }).currentBb fn.blocks = some bb' := by
      rw [jumpTo]; exact hlk'
    exact hstep_jmp_block pcOf psOf wOf hrb hnh hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk'' hwdec

/-- **Generic JNZ-not-taken per-block `hstep` clause.** The `cond = 0` companion of `hstep_jnz_taken`:
    the Venom step is `OK (jumpTo ifZ …)` and the asm side (`hrun`, from `resolved_jumpi_nottaken_sim`
    then `resolved_jump_sim`) reaches the `ifZ` successor entry. Same packaging via `hstep_jmp_block`. -/
theorem hstep_jnz_nottaken {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen idx : Nat} {jnzInst : Instruction} {condOp : Operand} {ifNz ifZ : String}
    {cond : bytes32}
    (hbb : bb.instructions = [jnzInst])
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { s with instIdx := 0 } = some cond)
    (hcondeq : cond = EvmYul.UInt256.ofNat 0)
    (hsnothalt : s.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody (jumpTo ifZ { s with instIdx := 0 }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hstepj : stepInstBase jnzInst { s with instIdx := 0 }
      = ExecResult.OK (jumpTo ifZ { s with instIdx := 0 }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rename_i h; exact absurd h (by rw [hcondeq]; decide)
    · rfl
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, hbb, hopc]
  | succ k =>
    have hrb : runBlock (k + 1) ctx bb s = ExecResult.OK (jumpTo ifZ { s with instIdx := 0 }) := by
      have h := runBlock_ok ctx bb k [] jnzInst jnzInst [] s { s with instIdx := 0 }
        (jumpTo ifZ { s with instIdx := 0 })
        (by simpa using hbb) rfl (by rw [hopc]; decide)
        (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepj
        (by rw [hopc]; decide) (by rw [jumpTo]; exact hsnothalt)
      simpa using h
    have hnh : (jumpTo ifZ { s with instIdx := 0 }).halted = false := by
      rw [jumpTo]; exact hsnothalt
    have hlk'' : lookupBlock (jumpTo ifZ { s with instIdx := 0 }).currentBb fn.blocks = some bb' := by
      rw [jumpTo]; exact hlk'
    exact hstep_jmp_block pcOf psOf wOf hrb hnh hrun hrel hstk hsp hfe hno hpcidx hle hidx hlk'' hwdec


/-- **Single generic per-block `hstep` dispatcher.** One lemma covering *every* terminator kind: it
    takes a proof that the block falls into one of the four non-vacuous `runBlock` result-categories --
    Halt (STOP/RETURN/SELFDESTRUCT), Abort-Revert (REVERT), Abort-Fault (INVALID), or OK-continue
    (JMP/JNZ, to a successor block) -- each carrying that arm's asm witness, and produces the full
    `hstep` match. The per-terminator arms (`blockSim_halt_of_body`, `hstep_jmp_block`,
    `hstep_jnz_taken`/`_nottaken`, the revert/fault cores, …) each establish one disjunct; this
    dispatches on which. `Error`/`IntRet` (low fuel / internal return) are the vacuous `_ => True` arm
    and need no disjunct -- callers reach them by the fuel case split. This is the uniform block
    dispatch the arbitrary-CFG driver (`runBlocks_walk` via the canonical scaffold) consumes per block. -/
theorem hstep_dispatch {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {s : VenomState} {asm : AsmState} {N f' : Nat}
    (h :
      (∃ (s' : VenomState) (asm' : AsmState), runBlock f' ctx bb s = ExecResult.Halt s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (asm' : AsmState),
          runBlock f' ctx bb s = ExecResult.Abort AbortType.RevertAbort s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (asm' : AsmState),
          runBlock f' ctx bb s = ExecResult.Abort AbortType.ExHaltAbort s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (bb' : BasicBlock) (asm' : AsmState) (blockLen' : Nat),
          runBlock f' ctx bb s = ExecResult.OK s' ∧ s'.halted = false ∧
          lookupBlock s'.currentBb fn.blocks = some bb' ∧
          runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm' ∧ blockLen' ≤ N ∧
          asm'.pc = pcOf bb'.label ∧ venomAsmRel labelOffsets (psOf bb'.label) s' asm' ∧
          wOf bb'.label + blockLen' ≤ wOf bb.label)) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rcases h with ⟨s', asm', hrb, hrun, hterm⟩ | ⟨s', asm', hrb, hrun, hterm⟩ |
    ⟨s', asm', hrb, hrun, hterm⟩ | ⟨s', bb', asm', blockLen', hrb, hnh, hlk', hrun, hle, hpc, hrel, hwdec⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; simp only [hnh, Bool.false_eq_true, if_false]
    exact ⟨bb', asm', blockLen', hlk', hrun, hle, hpc, hrel, hwdec⟩


/-- **Fuel-shaped per-block `hstep` dispatcher.** The counterpart of `hstep_dispatch` for
    `codegen_correct_fuel_sched`: one lemma covering every terminator kind, taking a proof that the
    block falls into one of the four non-vacuous `runBlock` result-categories and producing the
    fuel-shaped `hstep` match.

    The three terminal categories (Halt / Abort-Revert / Abort-Fault) are *identical* in the ranked and
    fuel shapes — they never mention the budget discipline — so the four halting terminators convert for
    free. Only the OK-continue category differs: `blockLen ≤ B` (a uniform bound) replaces
    `blockLen ≤ N` plus the rank decrease `wOf succ + blockLen ≤ wOf bb`, which is precisely what a
    back-edge cannot satisfy. -/
theorem hstep_dispatch_fuel {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    {bb : BasicBlock} {s : VenomState} {asm : AsmState} {B N f' : Nat}
    (h :
      (∃ (s' : VenomState) (asm' : AsmState), runBlock f' ctx bb s = ExecResult.Halt s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (asm' : AsmState),
          runBlock f' ctx bb s = ExecResult.Abort AbortType.RevertAbort s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (asm' : AsmState),
          runBlock f' ctx bb s = ExecResult.Abort AbortType.ExHaltAbort s' ∧
          runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm') ∨
      (∃ (s' : VenomState) (bb' : BasicBlock) (asm' : AsmState) (blockLen' : Nat),
          runBlock f' ctx bb s = ExecResult.OK s' ∧ s'.halted = false ∧
          lookupBlock s'.currentBb fn.blocks = some bb' ∧
          runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm' ∧ blockLen' ≤ B ∧
          asm'.pc = pcOf bb'.label ∧ venomAsmRel labelOffsets (psOf bb'.label) s' asm')) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rcases h with ⟨s', asm', hrb, hrun, hterm⟩ | ⟨s', asm', hrb, hrun, hterm⟩ |
    ⟨s', asm', hrb, hrun, hterm⟩ | ⟨s', bb', asm', blockLen', hrb, hnh, hlk', hrun, hle, hpc, hrel⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; exact ⟨asm', hrun, hterm⟩
  · rw [hrb]; simp only [hnh, Bool.false_eq_true, if_false]
    exact ⟨bb', asm', blockLen', hlk', hrun, hle, hpc, hrel⟩

/-- **Fuel-shaped per-block `hstep` clause for a phi-free JMP block** — the loop-capable counterpart of
    `hstep_jmp_block`. Identical inputs except that the rank is gone: `blockLen ≤ B` (uniform) replaces
    `blockLen ≤ N` together with the rank decrease `wOf succ + blockLen ≤ wOf bb`. This is the only
    place a terminator's per-block clause genuinely differs between the two drivers — the halting
    terminators' clauses are the same in both (`hstep_dispatch_fuel`). -/
theorem hstep_jmp_block_fuel {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    {bb bb' : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {B N f' blockLen idx : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx)
    (hleB : blockLen ≤ B)
    (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) :=
  hstep_dispatch_fuel (fn := fn) (B := B) (N := N) pcOf psOf
    (Or.inr (Or.inr (Or.inr ⟨s', bb', asm', blockLen, hrb, hnh, hlk', hrun, hleB,
      hpcidx.trans hidx, venomAsmRel_congr_widen hstk hsp hfe hno hrel⟩)))

/-- **Terminator-structure dispatch for bare halting blocks (STOP / INVALID).** The final-glue shape:
    it dispatches on the *raw terminator opcode* of a bare block `[term]` -- computing the Venom
    result-category from the structure (STOP steps to `Halt`, INVALID to `Abort ExHaltAbort`, via
    `runBlock_halt` / `runBlock_abort`) -- and feeds the matching disjunct to `hstep_dispatch`. The
    caller supplies only the terminator's opcode tag and its asm witness (from the STOP/INVALID cores);
    the Venom step and result are derived here. Fuel too small errors into the vacuous catch-all. This
    is the structure→category→`hstep` pipeline for the operand-less terminators; the operand terminators
    (RETURN/REVERT/SELFDESTRUCT/JMP/JNZ) follow the same shape with their own `runBlock_*` + asm atom. -/
theorem hstep_bareTerm_halting {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {s : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hstep_result :
      (term.opcode = Opcode.STOP ∧ ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
          venomAsmTerminalRel (haltState { s with instIdx := 0 }) asm') ∨
      (term.opcode = Opcode.INVALID ∧ ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
          venomAsmTerminalRel
            (haltState (setReturndata ByteArray.empty { s with instIdx := 0 })) asm')) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rcases hstep_result with ⟨hstop, asm', hrun, hterm⟩ | ⟨hinv, asm', hrun, hterm⟩
  · -- STOP -> Halt
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, hbb, hstop]
    | succ k =>
      have hstepT : stepInstBase term { s with instIdx := 0 }
          = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
        unfold stepInstBase; rw [hstop]
      have hrb : runBlock (k + 1) ctx bb s = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
        have h := runBlock_halt ctx bb k [] term term [] s { s with instIdx := 0 }
          (haltState { s with instIdx := 0 }) (by simpa using hbb) rfl (by rw [hstop]; decide)
          (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepT
        simpa using h
      exact hstep_dispatch pcOf psOf wOf (Or.inl ⟨_, asm', hrb, hrun, hterm⟩)
  · -- INVALID -> Abort ExHaltAbort
    cases f' with
    | zero => simp [runBlock, evalPhis, execBlock, hbb, hinv]
    | succ k =>
      have hstepT : stepInstBase term { s with instIdx := 0 }
          = ExecResult.Abort AbortType.ExHaltAbort
              (haltState (setReturndata ByteArray.empty { s with instIdx := 0 })) := by
        unfold stepInstBase; rw [hinv]
      have hrb : runBlock (k + 1) ctx bb s
          = ExecResult.Abort AbortType.ExHaltAbort
              (haltState (setReturndata ByteArray.empty { s with instIdx := 0 })) := by
        have h := runBlock_abort ctx bb k [] term term [] s { s with instIdx := 0 }
          (haltState (setReturndata ByteArray.empty { s with instIdx := 0 })) AbortType.ExHaltAbort
          (by simpa using hbb) rfl (by rw [hinv]; decide)
          (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepT
        simpa using h
      exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hterm⟩)))

/-- **Generic halting-terminator per-block `hstep` clause.** The category-level core behind
    `hstep_bareTerm_halting`'s STOP arm, but freed from the opcode: for any bare block `[term]` whose
    Venom terminator step *halts* (`stepInstBase term {s with instIdx := 0} = Halt sEnd'`), the matching
    whole-program halt witness (`runAsm N … = AsmHalt asm'` + `venomAsmTerminalRel sEnd' asm'`) discharges
    the full per-block `hstep` match. STOP feeds it a trivial `hstepT`; RETURN / SELFDESTRUCT feed their
    own operand-derived `hstepT` (see `hstep_bareTerm_return`). Fuel too small (`f' = 0`) errors out of
    fuel into the vacuous catch-all. -/
theorem hstep_bareTerm_halt_gen {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {s sEnd' : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { s with instIdx := 0 } = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨asm', hrun, hterm⟩ := hasm
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, hbb, hphi]
  | succ k =>
    have hrb : runBlock (k + 1) ctx bb s = ExecResult.Halt sEnd' := by
      have h := runBlock_halt ctx bb k [] term term [] s { s with instIdx := 0 } sEnd'
        (by simpa using hbb) rfl hphi
        (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepT
      simpa using h
    exact hstep_dispatch pcOf psOf wOf (Or.inl ⟨_, asm', hrb, hrun, hterm⟩)

/-- **Generic revert-terminator per-block `hstep` clause.** The `RevertAbort` companion of
    `hstep_bareTerm_halt_gen`: a bare `[term]` whose step aborts with `RevertAbort` matches the
    whole-program `AsmRevert` witness. REVERT feeds its operand-derived `hstepT` (see
    `hstep_bareTerm_revert`). -/
theorem hstep_bareTerm_revert_gen {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {s sEnd' : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { s with instIdx := 0 } = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨asm', hrun, hterm⟩ := hasm
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, hbb, hphi]
  | succ k =>
    have hrb : runBlock (k + 1) ctx bb s = ExecResult.Abort AbortType.RevertAbort sEnd' := by
      have h := runBlock_abort ctx bb k [] term term [] s { s with instIdx := 0 } sEnd'
        AbortType.RevertAbort (by simpa using hbb) rfl hphi
        (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepT
      simpa using h
    exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hterm⟩))

/-- **Generic fault-terminator per-block `hstep` clause.** The `ExHaltAbort` companion: a bare `[term]`
    whose step aborts with `ExHaltAbort` matches the whole-program `AsmFault` witness. INVALID is the
    operand-less instance (subsumes `hstep_bareTerm_halting`'s INVALID arm). -/
theorem hstep_bareTerm_fault_gen {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {s sEnd' : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { s with instIdx := 0 } = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨asm', hrun, hterm⟩ := hasm
  cases f' with
  | zero => simp [runBlock, evalPhis, execBlock, hbb, hphi]
  | succ k =>
    have hrb : runBlock (k + 1) ctx bb s = ExecResult.Abort AbortType.ExHaltAbort sEnd' := by
      have h := runBlock_abort ctx bb k [] term term [] s { s with instIdx := 0 } sEnd'
        AbortType.ExHaltAbort (by simpa using hbb) rfl hphi
        (by intro inst hi; simp only [List.not_mem_nil] at hi) rfl hstepT
      simpa using h
    exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hterm⟩)))


/-! ### The rest of the hstep family, for join blocks

`WalkStep_join` is terminator-agnostic, but the five remaining canonical `hstep`s could not simply be
wrapped in it: each hard-codes `hbb : bb.instructions = [term]`, a *bare* terminator block. A join is
`phis ++ [term]`, so that hypothesis is false for it — which is why JMP alone went through above (it is
the one clause parameterised on the block's result rather than its syntax).

`runBlock_join_eq_execBlock_at` is the reduction they all need: a join block's `runBlock` is its
`execBlock` resumed at index `phis.length`, i.e. exactly at the terminator. From there the existing
`execBlock_step_*` lemmas fire unchanged, and the five clauses follow. -/

/-- **A join block's `runBlock` resumes at the terminator.** -/
theorem runBlock_join_eq_execBlock_at {ctx : VenomContext} {bb : BasicBlock} {fuel : Nat}
    {phis : List Instruction} {term : Instruction} {s sPhi : VenomState}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI) :
    runBlock fuel ctx bb s
      = execBlock fuel ctx bb { sPhi with instIdx := phis.length } := by
  have hlen : phiPrefixLength bb.instructions = phis.length := by
    rw [hbb]
    exact phiPrefixLength_append phis [term] hphis
      (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
  rw [runBlock_eq_execBlock_of_phis hev, hlen]

/-- **Halt-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_halt_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length } = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s = ExecResult.Halt sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_halt extraFuel ctx bb _ sEnd' term
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inl ⟨_, asm', hrb, hrun, hrel⟩)

/-- **Revert-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_revert_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length }
        = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s
      = ExecResult.Abort AbortType.RevertAbort sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_abort extraFuel ctx bb _ sEnd' term _
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hrel⟩))

/-- **Fault-terminator `hstep`, for a join block.** -/
theorem hstep_bareTerm_fault_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {phis : List Instruction} {term : Instruction}
    {s sPhi sEnd' : VenomState} {asm : AsmState} {N extraFuel : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [term])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hterm : term.opcode ≠ Opcode.PHI)
    (hstepT : stepInstBase term { sPhi with instIdx := phis.length }
        = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel sEnd' asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  obtain ⟨asm', hrun, hrel⟩ := hasm
  have hrb : runBlock (extraFuel + 1) ctx bb s
      = ExecResult.Abort AbortType.ExHaltAbort sEnd' := by
    rw [runBlock_join_eq_execBlock_at hev hbb hphis hterm]
    exact execBlock_step_abort extraFuel ctx bb _ sEnd' term _
      (by simpa using getInstruction_term bb phis term hbb) hstepT
  exact hstep_dispatch pcOf psOf wOf (Or.inr (Or.inr (Or.inl ⟨_, asm', hrb, hrun, hrel⟩)))


theorem hstep_jnz_taken_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {phis : List Instruction} {jnzInst : Instruction}
    {condOp : Operand} {ifNz ifZ : String} {cond : bytes32}
    {s sPhi : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [jnzInst])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { sPhi with instIdx := phis.length } = some cond)
    (hcondne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hsnothalt : sPhi.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo ifNz { sPhi with instIdx := phis.length }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  have hterm : jnzInst.opcode ≠ Opcode.PHI := by rw [hopc]; decide
  have hstepj : stepInstBase jnzInst { sPhi with instIdx := phis.length }
      = ExecResult.OK (jumpTo ifNz { sPhi with instIdx := phis.length }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rfl
    · rename_i h; exact absurd (bne_iff_ne.mpr hcondne) h
  have hnh : (jumpTo ifNz { sPhi with instIdx := phis.length }).halted = false := by
    rw [jumpTo]; exact hsnothalt
  have hrb : execBlock (extraFuel + 1) ctx bb
      { sPhi with instIdx := phiPrefixLength bb.instructions }
      = ExecResult.OK (jumpTo ifNz { sPhi with instIdx := phis.length }) := by
    have hlen : phiPrefixLength bb.instructions = phis.length := by
      rw [hbb]
      exact phiPrefixLength_append phis [jnzInst] hphis
        (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
    rw [hlen]
    exact execBlock_step_term_ok extraFuel ctx bb _ _ jnzInst
      (by simpa using getInstruction_term bb phis jnzInst hbb) hstepj
      (by rw [hopc]; decide) hnh
  have hlk'' : lookupBlock (jumpTo ifNz { sPhi with instIdx := phis.length }).currentBb
      fn.blocks = some bb' := by rw [jumpTo]; exact hlk'
  exact hstep_jmp_block_join pcOf psOf wOf hev hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk'' hwdec

theorem hstep_jnz_nottaken_join {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {phis : List Instruction} {jnzInst : Instruction}
    {condOp : Operand} {ifNz ifZ : String} {cond : bytes32}
    {s sPhi : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N extraFuel blockLen idx : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hbb : bb.instructions = phis ++ [jnzInst])
    (hphis : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hopc : jnzInst.opcode = Opcode.JNZ)
    (hops : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondeval : evalOperand condOp { sPhi with instIdx := phis.length } = some cond)
    (hcondeq : cond = EvmYul.UInt256.ofNat 0)
    (hsnothalt : sPhi.halted = false)
    (hrun : runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody
        (jumpTo ifZ { sPhi with instIdx := phis.length }) asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx) (hle : blockLen ≤ N) (hidx : idx = pcOf bb'.label)
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N
      (runBlock (extraFuel + 1) ctx bb s) := by
  have hterm : jnzInst.opcode ≠ Opcode.PHI := by rw [hopc]; decide
  have hstepj : stepInstBase jnzInst { sPhi with instIdx := phis.length }
      = ExecResult.OK (jumpTo ifZ { sPhi with instIdx := phis.length }) := by
    unfold stepInstBase
    rw [hopc, hops]
    simp only [hcondeval]
    split
    · rename_i h; exact absurd hcondeq (bne_iff_ne.mp h)
    · rfl
  have hnh : (jumpTo ifZ { sPhi with instIdx := phis.length }).halted = false := by
    rw [jumpTo]; exact hsnothalt
  have hrb : execBlock (extraFuel + 1) ctx bb
      { sPhi with instIdx := phiPrefixLength bb.instructions }
      = ExecResult.OK (jumpTo ifZ { sPhi with instIdx := phis.length }) := by
    have hlen : phiPrefixLength bb.instructions = phis.length := by
      rw [hbb]
      exact phiPrefixLength_append phis [jnzInst] hphis
        (by intro i hi; simp only [List.head?_cons, Option.some.injEq] at hi; subst hi; exact hterm)
    rw [hlen]
    exact execBlock_step_term_ok extraFuel ctx bb _ _ jnzInst
      (by simpa using getInstruction_term bb phis jnzInst hbb) hstepj
      (by rw [hopc]; decide) hnh
  have hlk'' : lookupBlock (jumpTo ifZ { sPhi with instIdx := phis.length }).currentBb
      fn.blocks = some bb' := by rw [jumpTo]; exact hlk'
  exact hstep_jmp_block_join pcOf psOf wOf hev hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk'' hwdec

/-- **RETURN per-block `hstep` clause.** The first *operand-bearing* terminator instance: for a bare
    `[term]` with `term.opcode = RETURN`, `term.operands = [offOp, szOp]` and both operands evaluating
    (`off`, `sz`), the Venom step halts with returndata `readMemory off.toNat sz.toNat …`. Given the
    matching whole-program halt witness, `hstep_bareTerm_halt_gen` discharges the full per-block match.
    The returndata effect *is* observable in `venomAsmTerminalRel`, so the caller's witness must produce
    matching returndata. -/
theorem hstep_bareTerm_return {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {offOp szOp : Operand} {off sz : UInt256}
    {s : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hret : term.opcode = Opcode.RETURN)
    (hops : term.operands = [offOp, szOp])
    (hoff : evalOperand offOp { s with instIdx := 0 } = some off)
    (hsz : evalOperand szOp { s with instIdx := 0 } = some sz)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel
          (haltState (setReturndata (readMemory off.toNat sz.toNat { s with instIdx := 0 })
            { s with instIdx := 0 })) asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  refine hstep_bareTerm_halt_gen pcOf psOf wOf hbb (by rw [hret]; decide) ?_ hasm
  unfold stepInstBase
  simp only [hret, hops, hoff, hsz]

/-- **REVERT per-block `hstep` clause.** The `RevertAbort` operand-bearing instance, mirroring
    `hstep_bareTerm_return`: a bare `[term]` with `term.opcode = REVERT` and both operands evaluating
    aborts with `RevertAbort` and returndata `readMemory off.toNat sz.toNat …`. Discharged via
    `hstep_bareTerm_revert_gen`. -/
theorem hstep_bareTerm_revert {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term : Instruction} {offOp szOp : Operand} {off sz : UInt256}
    {s : VenomState} {asm : AsmState} {N f' : Nat}
    (hbb : bb.instructions = [term])
    (hrev : term.opcode = Opcode.REVERT)
    (hops : term.operands = [offOp, szOp])
    (hoff : evalOperand offOp { s with instIdx := 0 } = some off)
    (hsz : evalOperand szOp { s with instIdx := 0 } = some sz)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel
          (revertState (setReturndata (readMemory off.toNat sz.toNat { s with instIdx := 0 })
            { s with instIdx := 0 })) asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  refine hstep_bareTerm_revert_gen pcOf psOf wOf hbb (by rw [hrev]; decide) ?_ hasm
  unfold stepInstBase
  simp only [hrev, hops, hoff, hsz]


/-- **Generic per-block `hstep` for a spilling JMP block** — the adapter wiring the
Step-1 spill-aware per-block sim (`genBlockSimulation_regularHSVP_jmp`) into the
codegen driver's per-block obligation (`hstep_jmp_block`, consumed by
`hstep_dispatch` → `codegen_correct_sched`). The block runs its HSVP body then
`JMP target`; the sim supplies the Venom `OK (jumpTo target sEnd)` and the asm run
to the successor pc with `venomAsmRel` at the post-body plan state, and this feeds
the driver's `hstep` match. The ONLY residual is the plan-state determinism
(`hstk`/`hsp`/`hfe`/`hno`: the post-body fold output equals the entry plan state the
schedule `psOf` assigns the successor) — the named Step-2/4 obligation, taken here
as a hypothesis. -/
theorem hstep_regularHSVP_jmp
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    -- Venom block structure + JMP terminator
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    -- HSVP body + JMP layout (as `genBlockSimulation_regularHSVP_jmp`)
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
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- the scheduling / plan-determinism residual (Step 2/4)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom
      = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset
      ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Per-block JMP `hstep` on the canonical schedule.** The whole-function assembly for an aligned-JMP
    forward edge: instantiates `hstep_regularHSVP_jmp` with `pcOf := pcOfLabel prog`, `psOf := psOfFn`,
    `wOf l := prog.length - pcOfLabel prog l`, discharging `hblock`/`hpush`/`hjump`/`hpc*` from the chain
    (`hstep_jmp_layout_canonical` + placement) and the scheduling residual `hstk`/`hsp`/`hfe`/`hno` from
    `adapter_lgfold_eq_psOfFn_succ_general` (`(lg.foldl gp).2 = psOfFn target`, projected). Body-sim
    (`hready`/`hsd0`/…), Venom facts (`hbb`/`hterm_step`/…), jump-target lookups (`hoff_lk`/`hidx_lk`/`hidxeq`),
    forward-edge ranking (`hle`/`hwdec`) and the open label-uniqueness (`hpreuniq`) are inputs. `bb` is a
    phi/param-free aligned-JMP block (`hbb`/`hnp` share `front`). -/
theorem hstep_regularHSVP_jmp_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen off idx : Nat} {target : String} {succRest : List String}
    {succBB : BasicBlock} {result : List String × AssocList String PlanState × PlanState}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = target :: succRest)
    (hsfind : fn.blocks.find? (·.label == target) = some succBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ target) (hsne : target ≠ bb.label)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = target)
    (hidxeq : idx = pcOfLabel prog bb'.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hh1, hpush0, hh2, hjump0⟩ := hstep_jmp_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  have hres := adapter_lgfold_eq_psOfFn_succ_general (fnEom := fnEom) (lblCtr := lblCtr)
    hentry hpathhead hfuel hfn hchain hpsucc hsfind hsfresh hsne hsome hpfind hentry0 hmulti hnp
    hterm_jmp hterm_ops hterm_outs hjoin hreg hnospill hfront hgp
  exact hstep_regularHSVP_jmp (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Per-block JMP `hstep` on the canonical schedule, for *any reachable* block.** The chain-free
    counterpart of `hstep_regularHSVP_jmp_canonical`. That one routes its layout fact through
    `chain_segment_gbp`, hence `JmpChainTo`, hence "every block between the entry and `bb` has exactly
    one successor" — so it can never fire on a block behind a `JNZ`. Here the layout comes from
    `reach_segment_gbp_fn` instead: plain `CfgReach` from the entry, plus the decidable `DfsClosed` /
    entry-visited facts. Every reachable block qualifies, branch targets and joins included.

    The scheduling residual (`hres`: the block's gp-fold lands on the successor's canonical entry state)
    is taken as a hypothesis rather than derived from the chain. Both of its sides *compute*, so it is
    decidable per function; deriving it in general is the DFS tree-edge/join theory, which is what the
    remaining `psOfFn_succ_*_general` family does for chains. Everything else — body-sim, Venom facts,
    jump-target lookups, ranking — is unchanged from the canonical version. -/
theorem hstep_regularHSVP_jmp_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen off idx : Nat} {target : String}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr target)
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = target)
    (hidxeq : idx = pcOfLabel prog bb'.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hle : bodyLen + 2 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 2) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  -- `hpreuniq` is *derived*, not assumed: the block's plan heads with its own label
  -- (`generateBlockPlan_head_label`), and the DFS emits each label at most once (`hpreuniq_generic`).
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hh1, hpush0, hh2, hjump0⟩ := hstep_jmp_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_jmp (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Generic per-block `hstep` for a spilling JNZ-taken block** — the conditional
counterpart of `hstep_regularHSVP_jmp`: feeds `genBlockSimulation_regularHSVP_jnz_taken`
into `hstep_jmp_block` (terminator-agnostic — JNZ-taken produces `OK (jumpTo ifNz)`).
Residual: the same plan-state determinism. -/
theorem hstep_regularHSVP_jnz_taken
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hle : bodyLen + 3 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 3) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Generic per-block `hstep` for a spilling JNZ-not-taken block** — the `cond = 0`
fall-through twin, feeding `genBlockSimulation_regularHSVP_jnz_nottaken` into
`hstep_jmp_block`. Same plan-state-determinism residual. -/
theorem hstep_regularHSVP_jnz_nottaken
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idxZ = pcOf bb'.label)
    (hle : bodyLen + 5 ≤ N)
    (hwdec : wOf bb'.label + (bodyLen + 5) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block pcOf psOf wOf hrb hnohalt hrun hrel hstk hsp hfe hno hpcMid hle hidxeq hlk' hwdec

/-- **Per-block JNZ-taken `hstep` on the canonical schedule.** Dual-successor analogue of
    `hstep_regularHSVP_jmp_canonical` for the condition-≠0 branch: discharges the layout
    (`hblock`/`hdup`/`hpush`/`hjumpi` — the first three of the 5-op tail) from the chain via
    `hstep_jnz_layout_canonical` + placement (`pcOfLabel_aligned_jnz_block`), then applies the generic
    `hstep_regularHSVP_jnz_taken`. The scheduling residual (`hstk`/`hsp`/`hfe`/`hno` for `ifNz`) is an INPUT
    here — JNZ's term-step is not PlanState-identity (DUP+POP+emit), so the JMP residual machinery
    (`adapter_lgfold_eq_psOfFn_succ_general`) does not transfer directly; a JNZ successor-recording is future
    work. Condition (`hstkF`/`hcval`/`hcond`), jump-target, body-sim, Venom and forward-edge are inputs. -/
theorem hstep_regularHSVP_jnz_taken_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P off idx : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifNzBB ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 4 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifNz)
    -- NOTE the successor ORDER: `bbSuccs` is `(getSuccessors …).reverse`, so a JNZ's CFG successors
    -- come out as `ifZ :: ifNz` — the fall-through is the FIRST successor and the taken target the
    -- SECOND. Hence the taken branch needs the second-successor RELATION, not an equality.
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: ifNz :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfind2 : fn.blocks.find? (·.label == ifNz) = some ifNzBB)
    (hsfresh1 : ∀ b ∈ path, b.label ≠ ifZ) (hsne1 : ifZ ≠ bb.label)
    (hsfresh2 : ∀ b ∈ path, b.label ≠ ifNz) (hsne2 : ifNz ≠ bb.label)
    (hnr : ¬ CfgReach (cfgAnalyze fn) ifZ ifNz)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idx = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ :=
    chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpush⟩, ⟨hpc3, hjumpi⟩, _, _⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- discharge the scheduling residual from the chain (taken branch; ifNz = SECOND successor)
  obtain ⟨hstk, hsp, hfe, hno⟩ := adapter_lgfold_rel_psOfFn_succ2_jnz_general hentry hpathhead hfuel hfn
    hchain hpsucc hsfind1 hsfind2 hsfresh1 hsne1 hsfresh2 hsne2 hnr hsome hpfind hentry0 hmulti hnp
    hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS hreg hnospill hfront hgp
  exact hstep_regularHSVP_jnz_taken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hle hwdec

/-- **Per-block JNZ-not-taken `hstep` on the canonical schedule.** Dual-successor analogue of
    `hstep_regularHSVP_jmp_canonical` for the condition-=0 (fall-through) branch: discharges the layout
    (`hblock`/`hdup`/`hpush`/`hjumpi` — all five of the 5-op tail) from the chain via
    `hstep_jnz_layout_canonical` + placement (`pcOfLabel_aligned_jnz_block`), then applies the generic
    `hstep_regularHSVP_jnz_nottaken`. The scheduling residual (`hstk`/`hsp`/`hfe`/`hno` for `ifZ`) is
    DISCHARGED from the chain by `adapter_lgfold_rel_psOfFn_succ2_jnz_general`: `ifZ` is the *second*
    successor, so its recorded entry agrees with the block's body-fold on stack/spilled but carries the
    allocator threaded through `ifNz`'s whole subtree — hence a relation (`fnEom` fixed, `nextOffset`
    non-decreasing, via `dfsEntries_alloc_inv`) rather than the taken branch's whole-state equality.
    The tree-edge side condition is now a plain CFG fact — `hnr : ¬ CfgReach (cfgAnalyze fn) ifNz ifZ`
    (via `dfsEntriesAux_not_reach_fresh` / `dfsEntries_visited_reach`) — as are
    the condition (`hstkF`/`hcval`/`hcond`), jump-target, body-sim, Venom and forward-edge facts. -/
theorem hstep_regularHSVP_jnz_nottaken_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P offNz offZ idxZ : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 3 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifZ)
    -- `bbSuccs` reverses the terminator's labels, so the FALL-THROUGH `ifZ` is the FIRST CFG
    -- successor: its recorded entry is the block's exit exactly (a whole-PlanState equality).
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: succRest)
    (hsfind : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfresh : ∀ b ∈ path, b.label ≠ ifZ) (hsne : ifZ ≠ bb.label)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idxZ = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ :=
    chain_segment_gbp hentry hpathhead (by omega) hfn hchain hgen hpfind
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpushNz⟩, ⟨hpc3, hjumpi⟩, ⟨hpc4, hpushZ⟩, ⟨hpc5, hjump⟩⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- discharge the scheduling residual from the chain (not-taken branch; ifZ = FIRST successor)
  have hres := adapter_lgfold_eq_psOfFn_succ_jnz_general hentry hpathhead hfuel hfn hchain hpsucc hsfind
    hsfresh hsne hsome hpfind hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit hreorderS
    hreg hnospill hfront hgp
  exact hstep_regularHSVP_jnz_nottaken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec

/-- **Generic per-block `hstep` for a spilling STOP block** — the terminal
counterpart of the continue-arm adapters. A block `front ++ [STOP]` with an HSVP
body: the Venom side halts (`runBlock_halt` → `Halt (haltState sEnd)`), the asm side
runs body + STOP to `AsmHalt` with the terminal relation (`hasm_regularHSVP_stop`,
stretched to the driver budget `N`), and `hstep_halt_block` packages the two into the
driver's per-block `hstep` match. No plan-state-determinism residual (a terminal block
has no successor). The spilling terminal `hstep` clause, generic. -/
theorem hstep_regularHSVP_stop
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState sEnd) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd (haltState sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_stop (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
      hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Generic per-block `hstep` for a spilling INVALID block** — the fault-terminal counterpart
of `hstep_regularHSVP_stop`. A block `front ++ [INVALID]` with an HSVP body: Venom aborts to
`Abort ExHaltAbort (haltState (setReturndata empty sEnd))` (`runBlock_abort`, via the INVALID step
supplied as `hterm_step`), the asm runs body + INVALID to `AsmFault` with the terminal relation
(`hasm_regularHSVP_invalid`, budget = driver `N`), and `rw [hrb]` discharges the driver match's
ExHaltAbort arm. The terminal returndata match is unconditional (both sides clear returndata on the
fault), so — unlike the pre-fix INVALID chain — there is no returndata-empty hypothesis. No
plan-state-determinism residual. -/
theorem hstep_regularHSVP_invalid
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
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
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata ByteArray.empty sEnd)) AbortType.ExHaltAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_invalid (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread hblock
      hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block STOP `hstep` on the canonical schedule.** Terminal analogue of
    `hstep_regularHSVP_jmp_canonical` for a STOP block: discharges the layout (`hblock`/`hlt`/`hget` = `AsmOp
    "STOP"`) from the chain via `hstep_bareHalt_layout_canonical` + placement, then applies the generic
    `hstep_regularHSVP_stop`. No scheduling residual / jump-target / forward-edge (STOP halts, the
    OK-not-halted branch is vacuous so `pcOf`/`psOf`/`wOf` stay abstract). Body-sim, Venom and `hN` are
    inputs; `bb` is a phi/param-free STOP block. -/
theorem hstep_regularHSVP_stop_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "STOP")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "STOP" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_stop P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN

/-- **Per-block INVALID `hstep` on the canonical schedule.** Fault-terminal analogue of
    `hstep_regularHSVP_stop_canonical`: same bare-halting layout from the chain (`AsmOp "INVALID"`), Venom
    faults to `Abort ExHaltAbort (haltState (setReturndata empty sEnd))`, applies `hstep_regularHSVP_invalid`.
    `pcOf`/`psOf`/`wOf` abstract (vacuous branch). -/
theorem hstep_regularHSVP_invalid_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "INVALID")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "INVALID" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_invalid P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN


/-- **Generic per-block `hstep` for a spilling RETURN block** — the operand-terminal
counterpart of `hstep_regularHSVP_stop`. A block `front ++ [RETURN off sz]` with an
HSVP body: Venom halts to `Halt (haltState (setReturndata (memory[woff,wsz]) sEnd))`
(`runBlock_halt`, via the RETURN step supplied as `hterm_step`), the asm runs body +
the two-operand emission + RETURN to `AsmHalt` with the terminal relation
(`hasm_regularHSVP_return_var`, budget = driver `N`), and `rw [hrb]` discharges the
driver match's Halt arm. No plan-state-determinism residual. -/
theorem hstep_regularHSVP_return
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    (hN : bodyLen + emitLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd))
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_return_var (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block RETURN `hstep` on the canonical schedule.** Operand-terminal analogue of
    `hstep_regularHSVP_stop_canonical`: discharges the 3-segment layout (`hblock` for label+body+emit, `hget`
    = `AsmOp "RETURN"` at `bodyLen+emitLen`) from the chain via `hstep_return_layout_canonical` + placement,
    then applies the generic `hstep_regularHSVP_return`. The memory-safety (`hcov0`/`hsafe`/`hlen`),
    operand-membership/liveness/lookup (`hoffS`/…/`hvsz`) and body-sim/Venom facts are inputs. `pcOf`/`psOf`/
    `wOf` abstract (RETURN halts). `bb` a phi/param-free RETURN block; `nl` = `liveVarsAt … instructions.length`. -/
theorem hstep_regularHSVP_return_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "RETURN")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "RETURN" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_return pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN

/-- **Generic per-block `hstep` for a spilling REVERT block** — the operand-terminal
counterpart of `hstep_regularHSVP_stop`. A block `front ++ [REVERT off sz]` with an
HSVP body: Venom aborts to `Abort RevertAbort (revertState (setReturndata (memory[woff,wsz]) sEnd))`
(`runBlock_abort`, via the REVERT step supplied as `hterm_step`), the asm runs body +
the two-operand emission + RETURN to `AsmHalt` with the terminal relation
(`hasm_regularHSVP_revert_var`, budget = driver `N`), and `rw [hrb]` discharges the
driver match's Halt arm. No plan-state-determinism residual. -/
theorem hstep_regularHSVP_revert
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
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
    (hN : bodyLen + emitLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) AbortType.RevertAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_revert_var (budget := N) P hfront hready hsd0 hsv0 hspM hrel0 hthread
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-- **Per-block REVERT `hstep` on the canonical schedule.** Revert-terminal analogue of
    `hstep_regularHSVP_return_canonical`: discharges the 3-segment layout (`hblock` for label+body+emit, `hget`
    = `AsmOp "REVERT"` at `bodyLen+emitLen`) from the chain via `hstep_return_layout_canonical` + placement,
    then applies the generic `hstep_regularHSVP_revert`. The memory-safety (`hcov0`/`hsafe`/`hlen`),
    operand-membership/liveness/lookup (`hoffS`/…/`hvsz`) and body-sim/Venom facts are inputs. `pcOf`/`psOf`/
    `wOf` abstract (REVERT aborts). `bb` a phi/param-free REVERT block; `nl` = `liveVarsAt … instructions.length`. -/
theorem hstep_regularHSVP_revert_canonical
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {path : List BasicBlock} {blockOps : List StackOp} {ps' : PlanState}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hpathhead : (path.head?.map (·.label)).getD bb.label = entry.label)
    (hfuel : 2 * path.length + 1 ≤ fuel)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hchain : JmpChainTo (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn) (cfgAnalyze fn) fn
      bb.label blockOps ps' path [] { initPlanState fnEom with labelCounter := lblCtr })
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "REVERT")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hpreuniq : ∀ preOps tailOps, ops = preOps ++ blockOps ++ tailOps →
      ∀ a ∈ executePlan preOps, a ≠ AsmInst.AsmLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, tailOps, hseg, hgbp0⟩ := chain_segment_gbp hentry hpathhead hfuel hfn hchain hgen hpfind
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "REVERT" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_revert pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN

/-- **Full per-block `hstep` clause for a terminal (halting) block.** For a block whose Venom step halts
    (`runBlock … = Halt s'`), the whole-program halt sim (`runAsm N … = AsmHalt asm'` +
    `venomAsmTerminalRel s' asm'`) *is* the `hstep`'s `Halt` arm; the other arms are vacuous. The
    per-block terminal dispatch of the §5 assembly (STOP/RETURN/… blocks). -/
theorem hstep_halt_block {ctx : VenomContext} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {bb : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {N f' : Nat}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt s')
    (hsim : runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm') :
    (match runBlock f' ctx bb s with
     | ExecResult.OK _ => True
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  rw [hrb]; exact ⟨asm', hsim⟩


/-- **Reworked JMP `hstep` arm (offsetToPc from the *unresolved* plan).** Fixes the double-resolution:
    the walk's `offsetToPc`/`prog` come from `asmResolve origAsm` (the unresolved plan `executePlan ops`),
    so the arm takes `origAsm = pre ++ AsmLabel bb'.label :: suf` and uses `(asmResolve origAsm).2` /
    `(asmResolve origAsm).1` throughout — matching `codegen_correct_sched`'s `hstep`. `hidx : idx =
    pcOfLabel prog bb'.label` is discharged via `resolvedJump_idx_eq_pcOfLabel` (over `origAsm`) +
    `pcOfLabel_asmResolve` (label positions survive resolution). -/
theorem hstep_jmp_of_layout {fn : IrFunction} {ctx : VenomContext}
    {origAsm pre suf : List AsmInst} {labelOffsets : AssocList String Nat}
    (psOf : String → PlanState) (wOf : String → Nat)
    {bb bb' : BasicBlock} {s s' : VenomState} {asm asm' : AsmState} {psPostBody : PlanState}
    {N f' blockLen off idx : Nat}
    (horig : origAsm = pre ++ AsmInst.AsmLabel bb'.label :: suf)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel bb'.label ∧ inst ≠ AsmInst.AsmDataHeader bb'.label)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel bb'.label)
    (hoff_lk : AssocList.lookup String Nat (computeLabelOffsets origAsm).2 bb'.label = some off)
    (hidx_lk : AssocList.lookup Nat Nat (asmResolve origAsm).2 off = some idx)
    (hrb : runBlock f' ctx bb s = ExecResult.OK s')
    (hnh : s'.halted = false)
    (hrun : runAsm blockLen (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmOK asm')
    (hrel : venomAsmRel labelOffsets psPostBody s' asm')
    (hstk : psPostBody.stack = (psOf bb'.label).stack)
    (hsp : psPostBody.spilled = (psOf bb'.label).spilled)
    (hfe : psPostBody.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : psPostBody.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hpcidx : asm'.pc = idx)
    (hle : blockLen ≤ N)
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hwdec : wOf bb'.label + blockLen ≤ wOf bb.label) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOfLabel (asmResolve origAsm).1 bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N (asmResolve origAsm).2 (asmResolve origAsm).1 asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hidx : idx = pcOfLabel (asmResolve origAsm).1 bb'.label := by
    rw [pcOfLabel_asmResolve, horig]
    exact resolvedJump_idx_eq_pcOfLabel pre suf bb'.label off idx hsuf hpre (horig ▸ hoff_lk) (horig ▸ hidx_lk)
  exact hstep_jmp_block (pcOf := pcOfLabel (asmResolve origAsm).1) psOf wOf hrb hnh hrun hrel hstk hsp hfe hno
    hpcidx hle hidx hlk' hwdec


/-- **Canonical-scheduling scaffold for `codegen_correct_sched`.** Instantiates the budget-ranked bridge
    with the *canonical* schedule — `pcOf := pcOfLabel prog`, `psOf := psOfFn`, and the rank
    `wOf l := prog.length - pcOfLabel prog l` (which decreases by exactly a block's asm length across
    each JMP) — and discharges the three entry obligations automatically: `hpc0` from the entry's
    JUMPDEST being at pc 0 (`hpc0zero`), `hw0` from the rank being ≤ `prog.length`, and the entry
    relation from `psOfFn_entry` (`psOfFn entry = init`). Reduces a whole-function capstone to just the
    per-block `hstep` for the canonical schedule. -/
theorem codegen_correct_canonical {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat} {entry : BasicBlock}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hentryblk : entryBlock fn = some entry)
    (hentrylbl : entryLbl = entry.label)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hlk0 : lookupBlock entryLbl fn.blocks = some entry)
    (hpc0zero : pcOfLabel (asmResolve (executePlan ops)).1 entry.label = 0)
    (haspc : as.pc = 0)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOfLabel (asmResolve (executePlan ops)).1 bb.label →
        venomAsmRel lo (psOfFn (fnPlanFuel fn) fn fnEom lblCtr bb.label) s asm →
        (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb.label ≤ N →
        s.halted = false →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (bb' : BasicBlock) (asm' : AsmState) (blockLen : Nat),
                lookupBlock s'.currentBb fn.blocks = some bb' ∧
                runAsm blockLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                  = AsmResult.AsmOK asm' ∧ blockLen ≤ N ∧
                asm'.pc = pcOfLabel (asmResolve (executePlan ops)).1 bb'.label ∧
                venomAsmRel lo (psOfFn (fnPlanFuel fn) fn fnEom lblCtr bb'.label) s' asm' ∧
                ((asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb'.label) + blockLen
                  ≤ (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 bb.label
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
              = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo { initPlanState fnEom with labelCounter := lblCtr }
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfuelpos : 0 < fnPlanFuel fn := by simp only [fnPlanFuel]; omega
  have hpsofentry : psOfFn (fnPlanFuel fn) fn fnEom lblCtr entry.label
      = { initPlanState fnEom with labelCounter := lblCtr } := psOfFn_entry hentryblk hfn hfuelpos
  refine codegen_correct_sched (fuel := fuel) hplan hent hlk hlbl
    (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel fn) fn fnEom lblCtr)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    hstep (bb0 := entry) hlk0 ?_ ?_ hvshalt ?_
  · rw [haspc]; exact hpc0zero.symm
  · omega
  · rw [hpsofentry, hentrylbl]; exact hrel

/-- **Per-block STOP `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_stop_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_stop_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "STOP")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "STOP" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_stop P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN


/-- **Per-block INVALID `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_invalid_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_invalid_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen : Nat}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "INVALID")
    (hterm_ops : term.operands = []) (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_bareHalt_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "INVALID" hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_bareHalt_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hterm_ops hterm_outs hterm_reg hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_invalid P pcOf psOf wOf hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hlt hget hN



/-- **Per-block RETURN `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_return_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_return_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "RETURN")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "RETURN" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_return pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN


/-- **Per-block REVERT `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_revert_canonical`: the layout fact comes from
    `reach_segment_gbp_fn` (plain `CfgReach` + the decidable `DfsClosed`/entry-visited facts) instead of
    `chain_segment_gbp`/`JmpChainTo`, which structurally could not reach a block behind a `JNZ`.

    A halting terminator has no successor, so — unlike the JMP/JNZ case — there is **no scheduling
    residual and no ranking obligation** to carry. This variant is therefore *fully* generic: every
    hypothesis it adds is either decidable per function or plain CFG reachability, and `hpreuniq` is
    derived (`generateBlockPlan_head_label` + `hpreuniq_generic`) rather than assumed. -/
theorem hstep_regularHSVP_revert_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P : Nat} {offv szv : String} {woff wsz : bytes32} {M1 : AssocList Operand Nat}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hname : opcodeToEvmName term.opcode = some "REVERT")
    (hncomm : isCommutative term.opcode = false) (hnjmp : term.opcode ≠ Opcode.JMP)
    (hco : computeOperands term = [Operand.Var szv, Operand.Var offv])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hreorderNil : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var szv, Operand.Var offv]
        (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [])
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains offv = true)
    (hliveszv : (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length).contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hN : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length
      + (executePlan (emitInputPlan term.opcode [Operand.Var szv, Operand.Var offv]
          (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
            ([], psOfFn fuel fn fnEom lblCtr bb.label)).2).1).length + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_return_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term "REVERT" offv szv hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg
      hreorderNil hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hlt, hget⟩ := hstep_return_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hname hncomm hnjmp hco hterm_outs hterm_reg hreorderNil hgbp0
    hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_revert pcOf psOf wOf P hbb hcons hphi hnonterm hterm_step hfront hready
    hsd0 hsv0 hspM hrel0 hthread hvs0 hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0
    hsafe hlen hblk rfl rfl hlt hget hN


/-- **Per-block JNZ-taken `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_jnz_taken_canonical`: layout from `reach_segment_gbp_fn` (plain
    `CfgReach` + the decidable `DfsClosed`/entry-visited facts) rather than `JmpChainTo`.

    The taken branch targets `ifNz`, which is the CFG's *second* successor (`bbSuccs` reverses the
    terminator's labels, so a JNZ's successors are `ifZ :: ifNz` — fall-through first). The DFS
    therefore records it from a widened allocator, and the scheduling residual is a four-part
    *relation* (stack/spilled/fnEom equal, nextOffset only `≤`), not an equation. It is taken as the
    input `hres2` here, exactly the shape `adapter_lgfold_rel_psOfFn_succ2_jnz_general` derives from a
    chain. `hpreuniq` is derived, not assumed. -/
theorem hstep_regularHSVP_jnz_taken_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P off idx : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifNzBB ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres2 : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = (psOfFn fuel fn fnEom lblCtr ifNz).stack ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = (psOfFn fuel fn fnEom lblCtr ifNz).spilled ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom = (psOfFn fuel fn fnEom lblCtr ifNz).alloc.fnEom ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.nextOffset ≤ (psOfFn fuel fn fnEom lblCtr ifNz).alloc.nextOffset)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifNz)
    -- NOTE the successor ORDER: `bbSuccs` is `(getSuccessors …).reverse`, so a JNZ's CFG successors
    -- come out as `ifZ :: ifNz` — the fall-through is the FIRST successor and the taken target the
    -- SECOND. Hence the taken branch needs the second-successor RELATION, not an equality.
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: ifNz :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfind2 : fn.blocks.find? (·.label == ifNz) = some ifNzBB)
    (hnr : ¬ CfgReach (cfgAnalyze fn) ifZ ifNz)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idx = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpush⟩, ⟨hpc3, hjumpi⟩, _, _⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- the scheduling residual is supplied directly (`hres2`), not derived from a chain
  obtain ⟨hstk, hsp, hfe, hno⟩ := hres2
  exact hstep_regularHSVP_jnz_taken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hle hwdec


/-- **Per-block JNZ-not-taken `hstep` on the canonical schedule, for *any reachable* block.** Chain-free
    counterpart of `hstep_regularHSVP_jnz_nottaken_canonical`: layout from `reach_segment_gbp_fn` (plain
    `CfgReach` + the decidable `DfsClosed`/entry-visited facts) rather than `JmpChainTo`.

    The not-taken branch targets `ifZ`, the CFG's *first* successor, so its residual is a plain
    plan-state equation (`hres`) like the JMP case — taken as an input here, exactly the shape
    `adapter_lgfold_eq_psOfFn_succ_jnz_general` derives from a chain. `hpreuniq` is derived. -/
theorem hstep_regularHSVP_jnz_nottaken_reach
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P offNz offZ idxZ : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hwOf : wOf = fun l => prog.length - pcOfLabel prog l)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr ifZ)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifZ)
    -- `bbSuccs` reverses the terminator's labels, so the FALL-THROUGH `ifZ` is the FIRST CFG
    -- successor: its recorded entry is the block's exit exactly (a whole-PlanState equality).
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: succRest)
    (hsfind : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idxZ = pcOf bb'.label)
    (hle : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5 ≤ N)
    (hwdec : wOf bb'.label + ((executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5) ≤ wOf bb.label) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hwOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  -- the layout lemmas read the `.1`-only emit/reorder; derive them from the full-pair forms
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpushNz⟩, ⟨hpc3, hjumpi⟩, ⟨hpc4, hpushZ⟩, ⟨hpc5, hjump⟩⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  -- the scheduling residual is supplied directly (`hres`), not derived from a chain
  exact hstep_regularHSVP_jnz_nottaken (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr)
    (fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hle hwdec



/-- **Mid-layer JMP `hstep`, fuel-shaped.** Same block simulation as `hstep_regularHSVP_jmp` — the
    underlying `genBlockSimulation_regularHSVP_jmp` never mentioned a rank — but it hands off to
    `hstep_jmp_block_fuel`, so the block owes only the uniform bound `blockLen ≤ B` instead of a
    strict rank decrease. This is the whole difference between the two drivers at the block level. -/
theorem hstep_regularHSVP_jmp_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    -- Venom block structure + JMP terminator
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    -- HSVP body + JMP layout (as `genBlockSimulation_regularHSVP_jmp`)
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
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    -- the scheduling / plan-determinism residual (Step 2/4)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
      = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom
      = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset
      ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 2 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hblock hbodyLenEq hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Per-block JMP `hstep`: chain-free *and* loop-capable.** The composition of this session's two
    generalizations — the layout comes from `reach_segment_gbp_fn` (plain `CfgReach`, so a block behind
    a `JNZ` qualifies) and the budget discipline is the uniform `blockLen ≤ B` of the fuel-ranked driver
    (so a back-edge has nothing to violate). This is the hstep `codegen_correct_fuel_sched` consumes.

    Everything else is unchanged from `hstep_regularHSVP_jmp_reach`: the block simulation underneath
    never mentioned a rank, so dropping it costs nothing. -/
theorem hstep_regularHSVP_jmp_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P bodyLen off idx : Nat} {target : String}
    {lg : List ((Instruction × Nat) × List String)} {S0 : List String} {M0 : AssocList Operand Nat}
    {vs0 sEnd : VenomState} {as0 : AsmState}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jmp : term.opcode = Opcode.JMP) (hterm_ops : term.operands = [Operand.Label target])
    (hterm_outs : term.outputs = [])
    (hjoin : ∀ targetBb, fn.blocks.find? (·.label == target) = some targetBb →
              inputVarsFrom bb.label targetBb.instructions
                (liveVarsAt (livenessAnalyzeFuel fuel fn) target 0) = [])
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr target)
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = target)
    (hidxeq : idx = pcOfLabel prog bb'.label)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length)
    (hleB : bodyLen + 2 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog hbodyLenEq
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jmp_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term target hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
      (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, hh1, hpush0, hh2, hjump0⟩ := hstep_jmp_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jmp hterm_ops hterm_outs hjoin hgbp0 hseg hnospill
    hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_jmp_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0
    hblk rfl hh1 hpush0 hoff_lk hoff hh2 hjump0 hidx_lk hlk'
    (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hleB


/-- **Every terminating block's `hstep` converts from the ranked driver to the fuel driver for free.**

    The ranked and fuel `hstep` matches differ *only* in the OK-continue arm (`blockLen ≤ N` + rank
    decrease vs. the uniform `blockLen ≤ B`). Their Halt / Abort-Revert / Abort-Fault arms are literally
    the same proposition — neither mentions the budget discipline.

    So for a block whose `runBlock` never yields a non-halted `OK` — every one of STOP, INVALID, RETURN,
    REVERT — the ranked hstep *is* the fuel hstep: `rw [hrb]` lands both in the same arm. All four
    halting terminators therefore get their loop-capable `hstep` from the existing
    `hstep_regularHSVP_*_reach` theorems with no new proof, at any `wOf` the caller likes (the arm that
    mentions it is unreachable). Only JMP and JNZ need genuinely new work, which is
    `hstep_regularHSVP_jmp_reach_fuel` and its JNZ siblings. -/
theorem hstep_fuel_of_sched_terminal {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {s : VenomState} {as0 : AsmState} {B N f' : Nat}
    (hterm : ∀ s', runBlock f' ctx bb s ≠ ExecResult.OK s')
    (h :
      (match runBlock f' ctx bb s with
       | ExecResult.OK s' =>
           if s'.halted then
             ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
           else
             ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
               lookupBlock s'.currentBb fn.blocks = some bb'' ∧
               runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
               asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
               wOf bb''.label + blockLen' ≤ wOf bb.label
       | ExecResult.Halt s' =>
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
       | ExecResult.Abort AbortType.RevertAbort s' =>
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
       | ExecResult.Abort AbortType.ExHaltAbort s' =>
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
       | _ => True)) :
    (match runBlock f' ctx bb s with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  cases hrb : runBlock f' ctx bb s with
  | OK s' => exact absurd hrb (hterm s')
  | Halt s' => rw [hrb] at h; exact h
  | Abort a s' => rw [hrb] at h; cases a <;> exact h
  | IntRet _ _ => trivial
  | Error _ => trivial



/-- **Mid-layer JNZ-taken `hstep`, fuel-shaped.** As `hstep_regularHSVP_jnz_taken`, but handing off to
    `hstep_jmp_block_fuel`: the block owes the uniform `blockLen ≤ B` rather than a rank decrease, so a
    taken branch may target a block laid out *before* it — i.e. a loop back-edge. -/
theorem hstep_regularHSVP_jnz_taken_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 3 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Mid-layer JNZ-not-taken `hstep`, fuel-shaped.** The fall-through counterpart of
    `hstep_regularHSVP_jnz_taken_fuel`; same swap of the rank decrease for the uniform bound. -/
theorem hstep_regularHSVP_jnz_nottaken_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = base ++ [Operand.Var c])
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
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idxZ = pcOf bb'.label)
    (hleB : bodyLen + 5 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0
      hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- **Per-block JNZ-taken `hstep`: chain-free *and* loop-capable.** Both generalizations composed —
    layout from `CfgReach` (so this fires behind a JNZ), budget from the fuel rank (so the taken branch
    may jump *backwards*, which is exactly a loop back-edge). -/
theorem hstep_regularHSVP_jnz_taken_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P off idx : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifNzBB ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres2 : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = (psOfFn fuel fn fnEom lblCtr ifNz).stack ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.spilled = (psOfFn fuel fn fnEom lblCtr ifNz).spilled ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.fnEom = (psOfFn fuel fn fnEom lblCtr ifNz).alloc.fnEom ∧
      (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.alloc.nextOffset ≤ (psOfFn fuel fn fnEom lblCtr ifNz).alloc.nextOffset)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifNz sEnd))
    (hnohalt : (jumpTo ifNz sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hoff_lk : AssocList.lookup String Nat lo ifNz = some off) (hoff : off < 2 ^ 256)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifNz)
    -- NOTE the successor ORDER: `bbSuccs` is `(getSuccessors …).reverse`, so a JNZ's CFG successors
    -- come out as `ifZ :: ifNz` — the fall-through is the FIRST successor and the taken target the
    -- SECOND. Hence the taken branch needs the second-successor RELATION, not an equality.
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: ifNz :: succRest)
    (hsfind1 : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsfind2 : fn.blocks.find? (·.label == ifNz) = some ifNzBB)
    (hnr : ¬ CfgReach (cfgAnalyze fn) ifZ ifNz)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 3 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpush⟩, ⟨hpc3, hjumpi⟩, _, _⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  obtain ⟨hstk, hsp, hfe, hno⟩ := hres2
  exact hstep_regularHSVP_jnz_taken_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpush hoff_lk hoff hpc3 hjumpi hidx_lk hlk'
    (by rw [hbb'lbl]; exact hstk) (by rw [hbb'lbl]; exact hsp)
    (by rw [hbb'lbl]; exact hfe) (by rw [hbb'lbl]; exact hno) hidxeq hleB


/-- **Per-block JNZ-not-taken `hstep`: chain-free *and* loop-capable.** The fall-through counterpart;
    same composition. -/
theorem hstep_regularHSVP_jnz_nottaken_reach_fuel
    {fuel fnEom lblCtr : Nat} {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {entry bb bb' : BasicBlock} {term hd : Instruction} {tl front : List Instruction}
    {ops : List StackOp} {ps : PlanState}
    {extraFuel N P offNz offZ idxZ : Nat} {c ifNz ifZ : String} {cond : bytes32} {base : List Operand}
    {S0 : List String} {M0 : AssocList Operand Nat} {vs0 sEnd : VenomState} {as0 : AsmState}
    {lg : List ((Instruction × Nat) × List String)}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {succRest : List String} {ifZBB : BasicBlock}
    {result : List String × AssocList String PlanState × PlanState}
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoffsetToPc : offsetToPc = (asmResolve (executePlan ops)).2)
    (hlo : lo = (computeLabelOffsets (executePlan ops)).2)
    (hpcOf : pcOf = pcOfLabel prog)
    (hpsOf : psOf = psOfFn fuel fn fnEom lblCtr)
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ b ∈ fn.blocks, ∀ inst ∈ b.instructions, codegenReadyInst inst)
    (hclosed : DfsClosed fuel fn fnEom lblCtr)
    (hent : (dfsVisited fuel fn fnEom lblCtr).contains entry.label = true)
    (hreach : CfgReach (cfgAnalyze fn) entry.label bb.label)
    (hbbnf : ¬ IsFreshLabel bb.label)
    (hres : (lg.foldl (fun (acc : List StackOp × PlanState) (x : ((Instruction × Nat) × List String)) =>
        (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).2 = psOfFn fuel fn fnEom lblCtr ifZ)
    (hgen : generateFnPlanFuel fuel fn fnEom lblCtr = some (ops, ps))
    (hpfind : fn.blocks.find? (·.label == bb.label) = some bb)
    (hentry0 : ∀ e, fn.blocks.head? = some e → getParams e.instructions = [])
    (hmulti : CleanTrivial (livenessAnalyzeFuel fuel fn) (cfgAnalyze fn) fn bb)
    (hnp : nonParamInsts bb = front ++ [term])
    (hterm_jnz : term.opcode = Opcode.JNZ)
    (hterm_ops : term.operands = [Operand.Var c, Operand.Label ifNz, Operand.Label ifZ])
    (hterm_outs : term.outputs = [])
    (hterm_reg : ¬ isPreCodegenOpcode term.opcode ∧ term.opcode ≠ Opcode.PHI ∧
      term.opcode ≠ Opcode.OFFSET ∧ term.opcode ≠ Opcode.PARAM ∧ term.opcode ≠ Opcode.NOP)
    (hemit : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body
        = ([StackOp.SODup 1], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hreorderS : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      reorderPlan [Operand.Var c] { ps_body with stack := stackDup 0 ps_body.stack }
        = ([], { ps_body with stack := stackDup 0 ps_body.stack }))
    (hnospill : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
        ps_body.spilled = ([] : AssocList Operand Nat))
    (hlblfree : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (∀ a ∈ executePlan ([StackOp.SOLabel bb.label] ++ bodyOps), (∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
        ∧ (∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d)))
    (hgp : gp = fun (y : Instruction × Nat) (ps : PlanState) =>
        generateRegularInstPlan (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
          (cfgAnalyze fn) fn y.1
          (if y.2 + 1 < (nonParamInsts bb).length then
              liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label (y.2 + (getParams bb.instructions).length + 1)
            else liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length)
          (bbIsHalting bb)
          (if y.2 + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[y.2 + 1]!.opcode else false)
          bb.label ps)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hreg : ∀ x ∈ front.zipIdx 0, ¬ isPreCodegenOpcode x.1.opcode ∧ x.1.opcode ≠ Opcode.PHI ∧
      x.1.opcode ≠ Opcode.OFFSET ∧ x.1.opcode ≠ Opcode.PARAM ∧ x.1.opcode ≠ Opcode.NOP)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo ifZ sEnd))
    (hnohalt : (jumpTo ifZ sEnd).halted = false)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (hsv0 : StackPerm S0 (psOfFn fuel fn fnEom lblCtr bb.label))
    (hspM : (psOfFn fuel fn fnEom lblCtr bb.label).spilled = M0)
    (hrel0 : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr bb.label) vs0 as0)
    (has0 : as0.pc = pcOfLabel prog bb.label)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], psOfFn fuel fn fnEom lblCtr bb.label)).2.stack = base ++ [Operand.Var c])
    (hcval : operandVal sEnd lo (Operand.Var c) = some cond)
    (hcond : cond = EvmYul.UInt256.ofNat 0)
    (hoffNz_lk : AssocList.lookup String Nat lo ifNz = some offNz) (hoffNz : offNz < 2 ^ 256)
    (hoffZ_lk : AssocList.lookup String Nat lo ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hbb'lbl : bb'.label = ifZ)
    -- `bbSuccs` reverses the terminator's labels, so the FALL-THROUGH `ifZ` is the FIRST CFG
    -- successor: its recorded entry is the block's exit exactly (a whole-PlanState equality).
    (hpsucc : (cfgAnalyze fn).succsOf bb.label = ifZ :: succRest)
    (hsfind : fn.blocks.find? (·.label == ifZ) = some ifZBB)
    (hsome : dfsEntriesAux fuel (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn [entry.label] [] [] { initPlanState fnEom with labelCounter := lblCtr } = some result)
    (hidxeq : idxZ = pcOf bb'.label)
    (hleB : (executePlan ([StackOp.SOLabel bb.label] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], psOfFn fuel fn fnEom lblCtr bb.label)).1)).length + 5 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  subst hpsOf hpcOf hlo hoffsetToPc hprog
  obtain ⟨preOps, blockOps, tailOps, ps', hseg, hgbp0⟩ :=
    reach_segment_gbp_fn hfn hentry hgen hclosed hent hreach hpfind
  obtain ⟨restOps, hblkhd⟩ := generateBlockPlan_head_label _ _ _ _ _ _ hgbp0
  have hpreuniq := hpreuniq_fresh (bb := bb) hbbnf hgen hblkhd
  have hemit_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).1
        = [StackOp.SODup 1] := fun bo pb h => by rw [hemit bo pb h]
  have hreorder_lay : ∀ bodyOps ps_body,
      (front.zipIdx 0).foldl (instFoldF (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
        (cfgAnalyze fn) fn bb) (some ([], psOfFn fuel fn fnEom lblCtr bb.label)) = some (bodyOps, ps_body) →
      (reorderPlan [Operand.Var c] (emitInputPlan Opcode.JNZ [Operand.Var c]
        (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) ps_body).2).1 = [] :=
    fun bo pb h => by
      rw [show (emitInputPlan Opcode.JNZ [Operand.Var c]
            (liveVarsAt (livenessAnalyzeFuel fuel fn) bb.label bb.instructions.length) pb).2
          = { pb with stack := stackDup 0 pb.stack } from congrArg Prod.snd (hemit bo pb h),
        hreorderS bo pb h]
  have hpcpre : pcOfLabel (asmResolve (executePlan ops)).1 bb.label = (executePlan preOps).length :=
    pcOfLabel_aligned_jnz_block (livenessAnalyzeFuel fuel fn) (DfgAnalysis.buildFunction fn)
      (cfgAnalyze fn) fn bb (psOfFn fuel fn fnEom lblCtr bb.label) ops preOps tailOps blockOps ps'
      front term c ifNz ifZ hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay
      hreorder_lay hgbp0 hseg (hpreuniq preOps tailOps hseg)
  have has0pre : as0.pc = (executePlan preOps).length := has0.trans hpcpre
  obtain ⟨hblk, ⟨hpc1, hdup⟩, ⟨hpc2, hpushNz⟩, ⟨hpc3, hjumpi⟩, ⟨hpc4, hpushZ⟩, ⟨hpc5, hjump⟩⟩ := hstep_jnz_layout_canonical
    (as0pc := as0.pc) hentry0 hmulti hnp hterm_jnz hterm_ops hterm_outs hterm_reg hemit_lay hreorder_lay
    hgbp0 hseg hlblfree has0pre hgp hfront hreg
  exact hstep_regularHSVP_jnz_nottaken_fuel (pcOfLabel (asmResolve (executePlan ops)).1)
    (psOfFn fuel fn fnEom lblCtr) B
    P hbb hcons hphi hnonterm histerm hfront hready hsd0 hsv0 hspM hrel0 hthread hvs0 hblk rfl hstkF
    hcval hcond hterm_step hnohalt hpc1 hdup hpc2 hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ
    hoffZ_lk hoffZ hpc5 hjump hidxZ_lk hlk' (by rw [hbb'lbl, hres]) (by rw [hbb'lbl, hres])
    (by rw [hbb'lbl, hres]) (le_of_eq (by rw [hbb'lbl, hres])) hidxeq hleB


/-- **Mid-layer JMP `hstep` through a clean-stack prologue, fuel-shaped** — the composition of *all
    three* of this session's generalizations at the block level:

      * the block may carry a non-empty clean-stack prologue (`toPop ≠ []`, a join that drops values),
        via `genBlockSimulation_regularHSVP_jmp_clean`;
      * it owes only the uniform bound `blockLen ≤ B`, so it may branch *backwards* — a loop back-edge;
      * (with `reach_segment_gbp_fn` supplying its layout) it may sit anywhere CFG-reachable, including
        behind a `JNZ`.

    The pc arithmetic the prologue forces is absorbed entirely into `bodyLen`, which is *defined* as the
    length of the prologue-and-body asm — so the terminator still lands at `as0.pc + bodyLen` and no
    jump-target lemma changes. The residual (`hstk`/`hsp`/`hfe`/`hno`) is now about the fold from the
    post-pop state `ps2`, which is where the body actually starts. -/
theorem hstep_regularHSVP_jmp_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l target : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen off idx : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo target sEnd))
    (hnohalt : (jumpTo target sEnd).halted = false)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst lo (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat lo target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo target sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack
      = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled
      = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom
      = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset
      ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 2 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jmp_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront
      hready hsd2 hsv2 hspM2 hrel0 hthread hpop hshallow hlenPop hblock hbodyLenEq hpc1 hpush hoff_lk
      hoff hpc2 hjump hidx_lk hvs0
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'



/-- Per-block STOP `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_stop`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_stop_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "STOP")
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState sEnd) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd (haltState sEnd)
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_stop_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop
      hshallow hlenPop hblock hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block INVALID `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_invalid`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_invalid_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hlt : as0.pc + bodyLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen, hlt⟩ = AsmInst.AsmOp "INVALID")
    (hN : bodyLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata ByteArray.empty sEnd)) AbortType.ExHaltAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_invalid_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread hpop
      hshallow hlenPop hblock hbodyLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block RETURN `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_return`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_return_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "RETURN")
    (hN : bodyLen + emitLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd))
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_return_var_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread
      hpop hshallowPS hlenPop
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block REVERT `hstep` through a clean-stack prologue — the `toPop ≠ []` counterpart of
    `hstep_regularHSVP_revert`. Same Venom side (the prologue only discards dead variables); the body fold
    runs from the post-pop state and `bodyLen` absorbs the pops. Converts to the loop-capable driver
    for free via `hstep_fuel_of_sched_terminal` — a halting block's two match shapes agree. -/
theorem hstep_regularHSVP_revert_clean
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {offv szv : String} {woff wsz : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallowPS : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hoffS : offv ∈ S0 ++ lg.flatMap (fun e => e.2)) (hszS : szv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = M1)
    (hoffM : alookup' M1 (Operand.Var offv) = none) (hszM : alookup' M1 (Operand.Var szv) = none)
    (hliveoff : nl.contains offv = true) (hliveszv : nl.contains szv = true)
    (hvoff : lookupVar offv sEnd = some woff) (hvsz : lookupVar szv sEnd = some wsz)
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as0.memory.size)
    (hsafe : woff.toNat + wsz.toNat ≤
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom)
    (hlen : wsz.toNat < USize.size)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)
        ++ (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var szv, Operand.Var offv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "REVERT")
    (hN : bodyLen + emitLen + 1 ≤ N) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm'' ∧
             wOf bb''.label + blockLen' ≤ wOf bb.label
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) :=
    runBlock_abort ctx bb extraFuel front term hd tl vs0 sEnd
      (revertState (setReturndata (readMemory woff.toNat wsz.toNat sEnd) sEnd)) AbortType.RevertAbort
      hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_revert_var_clean (budget := N) P hfront hready hsd2 hsv2 hspM2 hrel0 hthread
      hpop hshallowPS hlenPop
      hoffS hszS hspMF hoffM hszM hliveoff hliveszv hvoff hvsz hcov0 hsafe hlen hblock hbodyLenEq
      hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩


/-- Per-block JNZ-taken `hstep` through a clean-stack prologue, fuel-shaped — the full composition:
    dropping join + loop-capable budget. -/
theorem hstep_regularHSVP_jnz_taken_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = base ++ [Operand.Var c])
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
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx)
    (hlk' : lookupBlock (jumpTo ifNz sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idx = pcOf bb'.label)
    (hleB : bodyLen + 3 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_taken_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd2 hsv2
      hspM2 hrel0 hthread hpop hshallow hlenPop hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpush hoff_lk hoff hpc3 hjumpi hidx_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-- Per-block JNZ-not-taken `hstep` through a clean-stack prologue, fuel-shaped. -/
theorem hstep_regularHSVP_jnz_nottaken_clean_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState)
    (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {toPop : List Operand} {cleanOps : List StackOp}
    {ps0 ps2 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {c : String} {cond : bytes32} {base : List Operand}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd2 : StackDiscHS (totalGain lg + P) ps2 vs0 as0)
    (hsv2 : StackPerm S0 ps2) (hspM2 : ps2.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hshallow : ps0.stack.length ≤ 17)
    (hlenPop : toPop.length < ps0.stack.length)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ cleanOps ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).1)).length)
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = base ++ [Operand.Var c])
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
    (hidxZ_lk : AssocList.lookup Nat Nat offsetToPc offZ = some idxZ)
    (hlk' : lookupBlock (jumpTo ifZ sEnd).currentBb fn.blocks = some bb')
    (hstk : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps2)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : idxZ = pcOf bb'.label)
    (hleB : bodyLen + 5 ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel, _, _⟩ :=
    genBlockSimulation_regularHSVP_jnz_nottaken_clean (ctx := ctx) (bb := bb) (term := term) (hd := hd)
      (tl := tl) (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hfront hready hsd2 hsv2
      hspM2 hrel0 hthread hpop hshallow hlenPop hvs0 hblock hbodyLenEq hstkF hcval hcond hterm_step hnohalt hpc1 hdup hpc2
      hpushNz hoffNz_lk hoffNz hpc3 hjumpi hpc4 hpushZ hoffZ_lk hoffZ hpc5 hjump hidxZ_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


set_option maxHeartbeats 1000000 in
/-- **Per-block DJMP `hstep`, fuel-shaped.** The seventh-and-last terminator. `hstep_jmp_block_fuel` is
    terminator-agnostic — it only wants "the Venom block stepped to a non-halting `OK` and the asm ran to
    the successor's entry, still related" — and `genBlockSimulation_regularHSVP_djmp` supplies exactly
    that. The plan side ends at the body's output with the selector popped, so the scheduling residual
    (`hstk`/`hsp`/`hfe`/`hno`) is stated against `stackPop 1` of the fold output.

    Loop-capable by construction: the obligation is the uniform `blockLen ≤ B`, so a DJMP may select a
    block laid out *before* it. That is sound precisely because DJMP cannot leave the static CFG
    (`stepInstBase_term_currentBb_mem_succs`), so the walk's reachability invariant survives it. -/
theorem hstep_regularHSVP_djmp_fuel
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (B : Nat)
    {bb bb' : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat}
    (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState} {bodyLen : Nat}
    {selVar : String} {selVal : bytes32} {base : List Operand} {tgtLbl : String}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK (jumpTo tgtLbl sEnd))
    (hnohalt : (jumpTo tgtLbl sEnd).halted = false)
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
    (hstkF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.stack = base ++ [Operand.Var selVar])
    (hselval : operandVal sEnd lo (Operand.Var selVar) = some selVal)
    (pre : List (List byte × String × Nat))
    (hpre : ∀ (k : Nat) (hk : k < pre.length),
        djmpEntryHere lo prog (as0.pc + bodyLen + 5 * k) (pre.get ⟨k, hk⟩).1
          (pre.get ⟨k, hk⟩).2.1 (pre.get ⟨k, hk⟩).2.2 ∧
        selVal ≠ djmpVal (pre.get ⟨k, hk⟩).1)
    {matb : List byte} {tName : String} {matoff idxTramp : Nat}
    (hmatch : djmpEntryHere lo prog (as0.pc + bodyLen + 5 * pre.length) matb tName matoff)
    (hsel : selVal = djmpVal matb)
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc matoff = some idxTramp)
    {lName : String} {loff target : Nat}
    (ht0 : ∃ h : idxTramp < prog.length, prog.get ⟨idxTramp, h⟩ = AsmInst.AsmLabel tName)
    (ht1 : ∃ h : idxTramp + 1 < prog.length, prog.get ⟨idxTramp + 1, h⟩ = AsmInst.AsmOp "POP")
    (ht2 : ∃ h : idxTramp + 2 < prog.length,
        prog.get ⟨idxTramp + 2, h⟩ = resolveInst lo (AsmInst.AsmPushLabel lName))
    (hl_lk : AssocList.lookup String Nat lo lName = some loff) (hloff : loff < 2 ^ 256)
    (ht3 : ∃ h : idxTramp + 3 < prog.length, prog.get ⟨idxTramp + 3, h⟩ = AsmInst.AsmOp "JUMP")
    (htarget_lk : AssocList.lookup Nat Nat offsetToPc loff = some target)
    -- the walk's successor + the scheduling residual (the plan side popped the selector)
    (hlk' : lookupBlock (jumpTo tgtLbl sEnd).currentBb fn.blocks = some bb')
    (hstk : stackPop 1 (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.stack = (psOf bb'.label).stack)
    (hsp : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.spilled = (psOf bb'.label).spilled)
    (hfe : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.fnEom = (psOf bb'.label).alloc.fnEom)
    (hno : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
        ([], ps0)).2.alloc.nextOffset ≤ (psOf bb'.label).alloc.nextOffset)
    (hidxeq : target = pcOf bb'.label)
    (hleB : bodyLen + (5 * pre.length + 5 + 4) ≤ B) :
    (match runBlock (front.length + (extraFuel + 1)) ctx bb vs0 with
     | ExecResult.OK s' =>
         if s'.halted then
           ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         else
           ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
             lookupBlock s'.currentBb fn.blocks = some bb'' ∧
             runAsm blockLen' offsetToPc prog as0 = AsmResult.AsmOK asm'' ∧ blockLen' ≤ B ∧
             asm''.pc = pcOf bb''.label ∧ venomAsmRel lo (psOf bb''.label) s' asm''
     | ExecResult.Halt s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.RevertAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
     | ExecResult.Abort AbortType.ExHaltAbort s' =>
         ∃ asm', runAsm N offsetToPc prog as0 = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
     | _ => True) := by
  obtain ⟨hrb, asMid, hrun, hpcMid, hrel⟩ :=
    genBlockSimulation_regularHSVP_djmp (ctx := ctx) (bb := bb) (term := term) (hd := hd) (tl := tl)
      (extraFuel := extraFuel) P hbb hcons hphi hnonterm histerm hterm_step hnohalt hfront hready
      hsd0 hsv0 hspM hrel0 hthread hvs0 hblock hbodyLenEq hstkF hselval pre hpre hmatch hsel hidx_lk
      ht0 ht1 ht2 hl_lk hloff ht3 htarget_lk
  exact hstep_jmp_block_fuel (B := B) (N := N) pcOf psOf hrb hnohalt hrun hrel hstk hsp hfe hno
    hpcMid hleB hidxeq hlk'


/-! ### The shallow-stack bound is not a restriction

`popmanyPlan_sim_closed` and the block prologue require `stack.length ≤ 17`, which is what keeps every
`doSwap` inside `SWAP16` and out of the temp spill region. I had recorded that as an honest restriction
to be lifted later — by threading `doSwap_big_sim`'s spill side conditions into the fold invariant.

It needs no lifting. `StackDiscHS.shallow` already caps the plan stack at **15**, and `StackDiscHS` is the
invariant the entire body-simulation machinery threads through every block. So any state the development
governs at all already satisfies the bound, with room to spare: the clean-stack prologue's shallow
requirement costs nothing beyond what its surroundings already demand, and the big-swap spill path is
simply never reached. -/

/-- `StackDiscHS` already caps the plan stack at 15. -/
theorem StackDiscHS.stack_le_15 {k p v s} (h : StackDiscHS k p v s) : p.stack.length ≤ 15 := by
  have := h.shallow; omega

/-- Hence the shallow-stack side condition of `popmanyPlan_sim_closed` costs nothing: any state the
    body-sim machinery governs already satisfies it. -/
theorem StackDiscHS.shallow17 {k p v s} (h : StackDiscHS k p v s) : p.stack.length ≤ 17 := by
  have := h.shallow; omega

/-- `popmanyPlan` simulates, with the shallow bound supplied by the invariant the development already
    threads rather than assumed outright. -/
theorem popmanyPlan_sim_of_sd {toPop : List Operand} {ps ps' : PlanState} {ops : List StackOp}
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst} {k : Nat}
    {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS k ps vs as)
    (hpop : popmanyPlan toPop ps = (ops, ps'))
    (hrel : venomAsmRel lo ps vs as)
    (hlen : toPop.length < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length :=
  popmanyPlan_sim_closed hpop hrel hsd.shallow17 hlen hblock

/-- The block prologue, likewise. -/
theorem blockPrologue_prefix_sim_of_sd {lo : AssocList String Nat} {vs : VenomState}
    {prog : List AsmInst} {ps0 ps2 : PlanState} {cleanOps : List StackOp} {toPop : List Operand}
    {as0 : AsmState} {l : String} {k : Nat} {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS k ps0 vs as0)
    (hrel : venomAsmRel lo ps0 vs as0)
    (hpop : popmanyPlan toPop ps0 = (cleanOps, ps2))
    (hlen : toPop.length < ps0.stack.length)
    (hblock : asmBlockAt prog as0.pc (executePlan ([StackOp.SOLabel l] ++ cleanOps))) :
    ∃ asMid, runAsm (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length offsetToPc prog as0
               = AsmResult.AsmOK asMid ∧
             venomAsmRel lo ps2 vs asMid ∧
             asMid.pc = as0.pc + (executePlan ([StackOp.SOLabel l] ++ cleanOps)).length :=
  blockPrologue_prefix_sim hrel hpop hsd.shallow17 hlen hblock


/-! ### Where ④ actually still stands: the scheduler's join-agreement invariant

With items 1-4 closed and both DFS side conditions discharged, exactly one thing is left, and it is worth
naming precisely rather than leaving as "generic `hres`".

`hres` says a block's post-body plan state equals its successor's *recorded* entry state. Along a DFS
tree edge that holds by construction — the successor is recorded *with* the predecessor's exit. At a join
reached from a second predecessor it is not automatic. And the compiler emits nothing to fix it up:
`cleanStackPlan` fires only at a block with exactly one predecessor, so a genuine (≥2-predecessor) join
gets no stack reconciliation at all (below).

So the residual is not a gap in the *simulation* — it is a property of the **plan generator**: every
predecessor of a block must exit with the plan state that block was recorded with. That is the stack
scheduler's join-agreement invariant, and it is the honest remaining content of ④. -/

/-- **A genuine join gets no reconciliation.** `cleanStackPlan` fires only at a block with *exactly one*
    predecessor (a JNZ branch target). At a block with two or more predecessors it emits nothing —
    `cleanTrivial_of_multi` — so the compiler performs no stack fix-up there at all.

    This pins what generic `hres` actually asks for. `hres` says a block's post-body plan state equals its
    successor's *recorded* entry state. That holds by construction along DFS tree edges (the successor is
    recorded *with* the predecessor's exit). At a join reached from a second predecessor it is not
    automatic — and, because nothing is emitted to fix it up, it must already be true. So the residual is
    not a simulation gap but a property of the **plan generator**: every predecessor of a block must exit
    with the plan state that block was recorded with. That is the stack scheduler's join-agreement
    invariant, and it is the honest remaining content of ④. -/
theorem no_reconciliation_at_join
    {L : DfState (List String)} {C : CfgAnalysis} {fn : IrFunction} {bb : BasicBlock} {ps : PlanState}
    (hmulti : 2 ≤ (C.predsOf bb.label).length) :
    cleanStackPlan L C fn bb ps = ([], ps) :=
  cleanTrivial_of_multi (by omega) ps



/-- **`BlockSim` really is the conclusion `genBlockSimulation` proves.**

`BlockSim` is a definition written in this development to name that conclusion so it can be moved
between results. If it did not actually match, `BlockSim_join` could not consume `genBlockSimulation`
and the whole transfer would be decorative. It matches — definitionally. -/
theorem BlockSim_eq_genBlockSim_concl
    (labelOffsets : AssocList String Nat) (ps' : PlanState) (offsetToPc : AssocList Nat Nat)
    (ops : List StackOp) (as : AsmState) (r : ExecResult) :
    BlockSim labelOffsets ps' offsetToPc (asmResolve (executePlan ops)).1 as r
      = (match r with
        | ExecResult.OK vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
        | ExecResult.Halt vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
        | ExecResult.Abort AbortType.RevertAbort vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
            venomAsmTerminalRel vs' as'
        | ExecResult.Abort AbortType.ExHaltAbort vs' =>
          ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
            (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
            venomAsmTerminalRel vs' as'
        | _ => True) := by
  cases r with
  | OK _ => rfl
  | Halt _ => rfl
  | Abort t _ => cases t <;> rfl
  | IntRet _ _ => rfl
  | Error _ => rfl



/-- **`genBlockSimulation`, for a genuine join.**

The family proper cannot be instantiated here — its `hphi` hypothesis demands a non-phi head, and a
join's head is a phi. This is the drop-in: give it a simulation for the block's *phi-free residual*, and
it yields the same conclusion for the join.

**But note what `hres` must be a simulation of.** It is about running the residual — the instructions
after the phis — against a program that assembles to the same thing the join's plan does. It is **not**
about `generateBlockPlan` applied to a synthetic residual `BasicBlock`: the generator looks liveness up
*by position within the block*, so dropping the phis shifts every later index and it emits different code
(`residual_block_compiles_differently` pins this, and the difference is real: 4 instructions against 5).
The program to use is the join's own — its body plan with the phi prologue in front, which assembles to
exactly the body plan alone (`executePlan_join_eq_residual`), because a phi prologue emits nothing.

On any incoming edge, the phis are discharged, the asm does not move, and the two runs agree up to the
instruction index — which neither `venomAsmRel` nor `venomAsmTerminalRel` can see. -/
theorem genBlockSimulation_join
    {fuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock} {phis : List Instruction}
    {vs vs' : VenomState} {ps' : PlanState} {ops resOps : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hbb : bb.instructions = phis ++ bb'.instructions)
    (hphi : ∀ i ∈ phis, i.opcode = Opcode.PHI)
    (hnext : ∀ i, bb'.instructions.head? = some i → i.opcode ≠ Opcode.PHI)
    (hno : ∀ inst ∈ bb'.instructions, inst.opcode ≠ Opcode.INVOKE)
    (hnx : ∀ inst ∈ bb'.instructions, isExternalCall inst.opcode = false)
    (hstep : ∀ inst ∈ bb'.instructions, ∀ t1 t2, sameUpToIdx t1 t2 →
        ResSameUpToIdx (stepInstBase inst t1) (stepInstBase inst t2))
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    -- the join's plan and the residual's differ by the phi prologue, which assembles to nothing
    -- (`executePlan_join_eq_residual`) — so they produce the same program, which is all the
    -- simulation sees. Without this the reuse of the program below would be an assumption.
    (hops : executePlan ops = executePlan resOps)
    (hres : match runBlock fuel ctx bb' vs' with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan resOps)).1.length) offsetToPc
          (asmResolve (executePlan resOps)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True) :
    match runBlock fuel ctx bb vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True := by
  rw [hops]
  exact BlockSim_join hbb hphi hnext hno hnx hstep hev hres


/-- `genBlockSimulation` for a join, stated on the join's own block and plan — no residual block. -/
theorem genBlockSimulation_join_self {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {vs vs' : VenomState} {ps' : PlanState} {ops : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    (hres : match execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions } with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True) :
    match runBlock fuel ctx bb vs with
      | ExecResult.OK w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' w as'
      | ExecResult.Halt w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.RevertAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel w as'
      | ExecResult.Abort AbortType.ExHaltAbort w =>
        ∃ as', runAsm ((asmResolve (executePlan ops)).1.length) offsetToPc
          (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel w as'
      | _ => True :=
  BlockSim_join_self hev hres


/-! ### From the per-block simulation to the walk, for a join

`genBlockSimulation_join_self` hands back a join's `BlockSim`. The walk wants a `WalkStep`. These are
*not* the same proposition, and the difference is easy to miss: `BlockSim`'s terminal arms run the asm
with `prog.length` fuel, `WalkStep`'s run it with the walk's budget `N`. They line up only when
`N = prog.length`, which is why `hN` is a hypothesis below rather than an omission. (I expected these
three arms to be definitionally equal and they were not — the probe said so before the prose did.)

With that, both halves of the `hphi` barrier are gone: the per-block simulation accepts a PHI-headed
block, and so does the walk clause it feeds. -/

/-- Terminal arms: `BlockSim` and `WalkStep` are the same proposition. -/
theorem WalkStep_of_BlockSim_terminal {fn ctx pcOf psOf wOf labelOffsets offsetToPc prog bb as N f'}
    {s : VenomState} {ps' : PlanState}
    (hN : N = prog.length)
    (hterm : (∀ w, runBlock f' ctx bb s ≠ ExecResult.OK w))
    (hbs : BlockSim labelOffsets ps' offsetToPc prog as (runBlock f' ctx bb s)) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb as N
      (runBlock f' ctx bb s) := by
  subst hN
  cases hr : runBlock f' ctx bb s with
  | OK w => exact absurd hr (hterm w)
  | Halt w => rw [hr] at hbs; exact hbs
  | Abort a w => cases a <;> (rw [hr] at hbs; exact hbs)
  | IntRet _ _ => trivial
  | Error _ => trivial

/-! ### REMOVED: `WalkStep_of_BlockSim_ok`

It carried the block's asm run at `prog.length` fuel. With `prog` the whole function's program — which is
what the walk needs — that arm is *false* for any block that continues: a continuing block does not stop at
its own boundary, it runs on into its successor. See `dia_blockSim_ok_false_at_whole_prog` for the
refutation and `WalkStep_of_BlockSimAt` for the replacement, which takes the block's asm length as a
parameter instead of reading it off the program. -/

/-- **A general join's walk obligation, straight from the compiler.** `genBlockSimulation_join_self`
gives the join's `BlockSim`; this turns it into the walk's `WalkStep`. The `hphi` barrier is gone on
both halves now: the per-block sim accepts a PHI-headed block, and so does the walk. -/
theorem WalkStep_join_of_genBlockSim_terminal {fuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {fn : IrFunction} {vs vs' : VenomState} {ps' : PlanState} {ops : List StackOp} {as : AsmState}
    {labelOffsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {N : Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hN : N = (asmResolve (executePlan ops)).1.length)
    (hterm : ∀ w, runBlock fuel ctx bb vs ≠ ExecResult.OK w)
    (hev : evalPhis vs bb.instructions = ExecResult.OK vs')
    (hres : BlockSim labelOffsets ps' offsetToPc (asmResolve (executePlan ops)).1 as
      (execBlock fuel ctx bb { vs' with instIdx := phiPrefixLength bb.instructions })) :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc (asmResolve (executePlan ops)).1 bb as N
      (runBlock fuel ctx bb vs) :=
  WalkStep_of_BlockSim_terminal hN hterm (genBlockSimulation_join_self hev hres)


/-- **The driver accepts `WalkStep`s — so it accepts joins.**

`codegen_correct_sched` is the real whole-function driver, and its `hstep` hypothesis is spelled out
inline. This restates that hypothesis as a `WalkStep` and closes the theorem by handing over
`codegen_correct_sched` itself: it typechecks by `exact`, so the two are *definitionally* the same
obligation. That is what makes the join work of this arc load-bearing rather than decorative —
`hstep_jmp_block_join`, `hstep_bareTerm_{halt,revert,fault}_join` and `hstep_jnz_{taken,nottaken}_join`
all produce `WalkStep`s, so they can be fed to this driver directly, with no adapter.

(Stating the driver's obligation as my own predicate and *not* proving the correspondence is exactly
the trap this branch has now walked into six times. Hence the `exact`.) -/
theorem codegen_correct_sched_ws
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        WalkStep fn pcOf psOf wOf lo (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 bb asm N (runBlock f' ctx bb s))
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_sched hplan hent hlk hlbl pcOf psOf wOf hstep bb0 hlk0 hpc0 hw0 hvshalt hrel


/-! ### Joins with a body

The bare-terminator join hsteps above take a block `phis ++ [term]` and derive its `execBlock` from that
syntax. That was more machinery than the job needs. `WalkStep_join` already transfers the walk obligation
across the phi prologue for an *arbitrary* block, so a join with any body at all — a join whose body reads
the phi's own output, say — needs only its post-phi `execBlock` result and the asm witness. Each of these
is one line, and each is strictly more general than its bare-terminator counterpart.

(The bare-terminator forms are kept: they are the convenient entry point when the block's syntax is what
you have. But the general primitive is here, and it is what a join with a body needs.) -/

/-- **Halting join, ANY body.** -/
theorem hstep_join_halt {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Halt sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)

/-- **Reverting join, ANY body.** -/
theorem hstep_join_revert {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Abort AbortType.RevertAbort sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)

/-- **Faulting join, ANY body.** -/
theorem hstep_join_fault {fn : IrFunction} {ctx : VenomContext}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {bb : BasicBlock} {s sPhi sEnd : VenomState} {asm : AsmState} {N f' : Nat}
    (hev : evalPhis s bb.instructions = ExecResult.OK sPhi)
    (hres : execBlock f' ctx bb { sPhi with instIdx := phiPrefixLength bb.instructions }
        = ExecResult.Abort AbortType.ExHaltAbort sEnd)
    (hasm : ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧
        venomAsmTerminalRel sEnd asm') :
    WalkStep fn pcOf psOf wOf labelOffsets offsetToPc prog bb asm N (runBlock f' ctx bb s) :=
  WalkStep_join hev (by rw [hres]; exact hasm)


/-! ### The driver's `Entry` is too weak for a phi join

`codegen_correct_sched`'s `Entry` carries a block, a pc, a `venomAsmRel`, a rank bound and `halted =
false`. That is everything a phi-free block needs and *not* everything a join needs.

A join's `evalPhis` reads its sources out of `vars`, so discharging it requires knowing which predecessor
the walk arrived from and that that predecessor's variable is bound. `venomAsmRel` says nothing about
`vars` — and it cannot be made to, because the compiler is entitled to drop a variable the EVM no longer
needs (a phi does not *use* its sources, so it pops them). The witness for `evalPhis` is exactly the
information the stack no longer carries.

`codegen_correct`, underneath, takes `Entry` as a free parameter. So the fix is not to weaken the join but
to thread an invariant: `codegen_correct_sched_inv` hands `Inv s` to each `hstep` and requires it back at
the successor, which is the standard way to carry a fact the relation deliberately forgets. -/
/-- The walk's per-block obligation, carrying a user invariant `Inv` to the successor. -/
def WalkStepInv (Inv : VenomState → Prop) (fn : IrFunction) (pcOf : String → Nat)
    (psOf : String → PlanState) (wOf : String → Nat) (labelOffsets : AssocList String Nat)
    (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (bb : BasicBlock)
    (asm : AsmState) (N : Nat) : ExecResult → Prop
  | ExecResult.OK s' =>
      if s'.halted then
        ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      else
        ∃ (bb'' : BasicBlock) (asm'' : AsmState) (blockLen' : Nat),
          lookupBlock s'.currentBb fn.blocks = some bb'' ∧
          runAsm blockLen' offsetToPc prog asm = AsmResult.AsmOK asm'' ∧ blockLen' ≤ N ∧
          asm''.pc = pcOf bb''.label ∧ venomAsmRel labelOffsets (psOf bb''.label) s' asm'' ∧
          wOf bb''.label + blockLen' ≤ wOf bb.label ∧ Inv s'
  | ExecResult.Halt s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.RevertAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
  | ExecResult.Abort AbortType.ExHaltAbort s' =>
      ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
  | _ => True

/-- **The budget-ranked driver, with a user invariant threaded through the walk.** -/
theorem codegen_correct_sched_inv
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    (Inv : VenomState → Prop)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    (hstep : ∀ (bb : BasicBlock) (s : VenomState) (asm : AsmState) (N f' : Nat),
        lookupBlock s.currentBb fn.blocks = some bb →
        asm.pc = pcOf bb.label →
        venomAsmRel lo (psOf bb.label) s asm →
        wOf bb.label ≤ N →
        s.halted = false →
        Inv s →
        WalkStepInv Inv fn pcOf psOf wOf lo (asmResolve (executePlan ops)).2
          (asmResolve (executePlan ops)).1 bb asm N (runBlock f' ctx bb s))
    (bb0 : BasicBlock)
    (hlk0 : lookupBlock entryLbl fn.blocks = some bb0)
    (hpc0 : as.pc = pcOf bb0.label)
    (hw0 : wOf bb0.label ≤ (asmResolve (executePlan ops)).1.length)
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (psOf bb0.label)
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as)
    (hInv0 : Inv { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 }) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct (fuel := fuel) (ctx := ctx) (fn := fn) (fnEom := fnEom) (lblCtr := lblCtr)
    (ops := ops) (psFinal := psFinal) (entryName := entryName) (entryLbl := entryLbl)
    (Entry := fun s asm N => ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
       asm.pc = pcOf bb.label ∧ venomAsmRel lo (psOf bb.label) s asm ∧ wOf bb.label ≤ N ∧
       s.halted = false ∧ Inv s)
    hplan hent hlk hlbl ?_ ⟨bb0, hlk0, hpc0, hrel, hw0, hvshalt, hInv0⟩
  intro s asm N f' bb hE hlk'
  obtain ⟨bb', hlkbb, hpc, hvrel, hwN, hnh, hinv⟩ := hE
  rw [hlk'] at hlkbb; injection hlkbb with hbbeq; subst hbbeq
  have hb := hstep bb s asm N f' hlk' hpc hvrel hwN hnh hinv
  cases hrb : runBlock f' ctx bb s with
  | OK s' =>
    rw [hrb] at hb
    by_cases hh : s'.halted
    · simp only [WalkStepInv, hh, if_true] at hb ⊢; exact hb
    · simp only [WalkStepInv, hh, Bool.false_eq_true, if_false] at hb ⊢
      obtain ⟨bb'', asm', blockLen, hlk'', hrun, hle, hpc', hvrel', hwdec, hinv'⟩ := hb
      refine ⟨asm', N - blockLen, ?_, bb'', hlk'', hpc', hvrel', by omega, by simp, hinv'⟩
      conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
      exact runAsm_append_ok hrun
  | Halt s' => rw [hrb] at hb; exact hb
  | Abort a s' => rw [hrb] at hb; cases a <;> exact hb
  | IntRet _ _ => trivial
  | Error _ => trivial


/-! ## Loops: the drivers already exist, and I duplicated them

RETRACTION. I claimed here that loops were kept out of the top-level theorem by one hard-coded numeral —
`codegen_correct`'s initial asm budget of `prog.length` — and added `codegen_correct_budget` to
parameterise it. **The claim is false and the theorem was redundant.**

`codegen_correct_fuel` (in `CodegenCorrectness`) is already the loop-admitting top-level driver: its asm
budget is `fuel * B`, Venom's own fuel times a per-block bound, and its per-block obligation is the
uniform `blockLen ≤ B` rather than a strictly decreasing per-label rank. Nothing orders the blocks, so a
back-edge has nothing to violate. `codegen_correct_fuel_sched` is the scheduled counterpart. Both were
here the whole time, and both are strictly better than what I added — the budget is *derived* rather than
supplied.

Worse: `loopFn_ranked_walk_impossible`'s docstring, which I read while forming the claim, says in as many
words that this "is exactly what `codegen_correct_fuel` sidesteps". I read the sentence naming the
solution and did not follow it.

The real open item was never the statement. It is that **no loop has been driven end to end through
`codegen_correct_fuel_sched`** — the per-block obligations for a cyclic function at a loop-admitting
budget. That is the work, and it was the work before this detour.

**2026-07-17: done.** `codegen_correct_loopVFn_fuel` (`GenBlockSimExample`) drives
`entry: %a = CALLVALUE ; JNZ %a entry exit` / `exit: STOP` — a real back-edge
(`loopVFn_back_edge`) — end to end through this driver, both JNZ arms, on the real generated
program, at budget `fuel * 8`. -/

end EvmYul.Venom.Hol.Codegen

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

end EvmYul.Venom.Hol.Codegen

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

end EvmYul.Venom.Hol.Codegen

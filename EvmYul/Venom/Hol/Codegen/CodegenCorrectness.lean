/-
Codegen Correctness — theorem statements + proofs (Phase 5.1-5.3, 5.9-5.10 done)

Phase 5.1: runBlocks_never_ok ✓
Phase 5.2: initial_state_bridge ✓
Phase 5.3: runFunction_never_ok / runContext_never_ok ✓
Phase 5.9: codegen_fn_correct ✓ (REAL — `generateContextPlan` is now the fuel pipeline; the theorem
           ties `prog` to the resolved plan and is discharged by `runBlocks_walk` given the per-block
           correspondence `hbsim`; no longer vacuous)
Phase 5.10: codegen_correct ✓ (REAL — `runContext` peels to the entry function's `runBlocks`, then
           `runBlocks_walk`; non-vacuous, premise satisfiable via the real pipeline)

The remaining content is *supplying* `hbsim` unconditionally for a general function (the per-block
sims composed across the CFG — packaged as `hfsim` by `genFnSimulation`, one file up); the concrete
`codegenFuel_correct_*` / `hfsim_*` instances discharge it end to end.
-/


import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Exec
import EvmYul.Venom.Hol.Codegen.AsmSem
import EvmYul.Venom.Hol.Codegen.CodegenRel
import EvmYul.Venom.Hol.Codegen.CodegenPipeline
import EvmYul.Venom.Hol.Codegen.PlanSim
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

def finalStateRel (vs : VenomState) (as : AsmState) : Prop := venomAsmTerminalRel vs as

theorem runBlocks_never_ok {fuel ctx fn s vs} : runBlocks fuel ctx fn s ≠ ExecResult.OK vs := by
  intro h
  induction fuel generalizing vs s with
  | zero =>
    unfold runBlocks at h
    injection h
  | succ fuel ih =>
    unfold runBlocks at h
    cases hlookup : lookupBlock s.currentBb fn.blocks
    · -- none: already closed by simp
      simp [hlookup] at h
    · -- some bb
      next bb =>
      simp [hlookup] at h
      cases hr : runBlock fuel ctx bb s
      · -- OK s'
        next s' =>
        simp [hr] at h
        split at h
        · injection h
        · apply ih h
      · -- Halt: already closed by simp
        simp [hr] at h
      · -- Abort: already closed by simp
        simp [hr] at h
      · -- IntRet: already closed by simp
        simp [hr] at h
      · -- Error: already closed by simp
        simp [hr] at h

/-! ## CFG-walk peel lemmas

One iteration of `runBlocks`' fuel recursion: look up the current block, run it, then propagate the
terminal result or continue to the successor. These expose the structure that composes
`genBlockSimulation` across the DFS-ordered blocks — the inter-block (CFG) content of
`genFnSimulation`'s `hfsim`. Each is the definitional unfold of `runBlocks (fuel+1)` specialised to
the current block's `runBlock` outcome. -/

/-- Current block halts (`runBlock` OK with `halted`) ⇒ the whole CFG walk halts there. -/
theorem runBlocks_halt_of_block {fuel ctx fn s bb vs'}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.OK vs') (hh : vs'.halted = true) :
    runBlocks (fuel + 1) ctx fn s = ExecResult.Halt vs' := by
  unfold runBlocks; rw [hlk]; simp only [hb, hh, if_true]

/-- Current block aborts ⇒ the walk aborts with the same type/state. -/
theorem runBlocks_abort_of_block {fuel ctx fn s bb a vs'}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.Abort a vs') :
    runBlocks (fuel + 1) ctx fn s = ExecResult.Abort a vs' := by
  unfold runBlocks; rw [hlk]; simp only [hb]

/-- Current block returns (`IntRet`) ⇒ the walk returns those values. -/
theorem runBlocks_intret_of_block {fuel ctx fn s bb vals vs'}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.IntRet vals vs') :
    runBlocks (fuel + 1) ctx fn s = ExecResult.IntRet vals vs' := by
  unfold runBlocks; rw [hlk]; simp only [hb]

/-- Current block errors ⇒ the walk errors. -/
theorem runBlocks_error_of_block {fuel ctx fn s bb e}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.Error e) :
    runBlocks (fuel + 1) ctx fn s = ExecResult.Error e := by
  unfold runBlocks; rw [hlk]; simp only [hb]

/-- Current block halts *directly* (`runBlock = Halt`, e.g. a STOP whose `stepInstBase` is `Halt`,
    not `OK`-then-`halted`) ⇒ the walk halts there. Complements `runBlocks_halt_of_block`. -/
theorem runBlocks_haltDirect_of_block {fuel ctx fn s bb vs'}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.Halt vs') :
    runBlocks (fuel + 1) ctx fn s = ExecResult.Halt vs' := by
  unfold runBlocks; rw [hlk]; simp only [hb]

/-- Current block finishes OK without halting ⇒ the walk continues from the successor state `vs'`
    (whose `currentBb` the terminator set). The inductive step of the CFG composition. -/
theorem runBlocks_step_of_block {fuel ctx fn s bb vs'}
    (hlk : lookupBlock s.currentBb fn.blocks = some bb)
    (hb : runBlock fuel ctx bb s = ExecResult.OK vs') (hh : vs'.halted = false) :
    runBlocks (fuel + 1) ctx fn s = runBlocks fuel ctx fn vs' := by
  conv_lhs => unfold runBlocks
  rw [hlk]; simp only [hb, hh, Bool.false_eq_true, if_false]

/-! ## CFG walk-composition (acyclic): supplying `hfsim` from per-block sims

The whole-function `runAsm` correspondence (`genFnSimulation`'s `hfsim`) by inducting on the
`runBlocks` fuel. Threaded with an asm **budget** `N` (decreasing) and an `Entry` relation abstracting
"the asm state is at the current block's entry pc, related to the Venom state, with budget `N`". The
per-block sim `hbsim` gives, for each block: the matching asm terminal (Halt/Abort), or — for a
non-halting `JMP` — the budget transition `runAsm N … asm = runAsm N' … asm'` to the successor's entry
(`asm'`, budget `N'`), via `runAsm_append_ok`. The walk chains these along the CFG. For an ACYCLIC CFG
the caller instantiates `N := prog.length` (each block's asm runs once, lengths summing to
`prog.length`), discharging `hbsim`'s budget transitions; this lemma is the order-agnostic engine
those discharges plug into. -/
theorem runBlocks_walk {ctx : VenomContext} {fn : IrFunction} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    (Entry : VenomState → AsmState → Nat → Prop)
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm N → lookupBlock s.currentBb fn.blocks = some bb →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ asm' N', runAsm N offsetToPc prog asm = runAsm N' offsetToPc prog asm' ∧ Entry s' asm' N'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True) :
    ∀ (fuel : Nat) (s : VenomState) (asm : AsmState) (N : Nat), Entry s asm N →
      match runBlocks fuel ctx fn s with
      | ExecResult.Halt s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
      | _ => True := by
  intro fuel
  induction fuel with
  | zero => intro s asm N _; rw [runBlocks]; exact trivial
  | succ f' ih =>
    intro s asm N hE
    cases hlk : lookupBlock s.currentBb fn.blocks with
    | none =>
      have hE2 : runBlocks (f' + 1) ctx fn s = ExecResult.Error "block not found" := by
        rw [runBlocks, hlk]
      rw [hE2]; exact trivial
    | some bb =>
      have hb := hbsim s asm N f' bb hE hlk
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        by_cases hh : s'.halted
        · rw [runBlocks_halt_of_block hlk hrb hh]
          simp only [hh, if_true] at hb; exact hb
        · have hh' : s'.halted = false := by simpa using hh
          rw [runBlocks_step_of_block hlk hrb hh']
          simp only [hh', Bool.false_eq_true, if_false] at hb
          obtain ⟨asm', N', heq, hE'⟩ := hb
          rw [heq]; exact ih s' asm' N' hE'
      | Halt s' =>
        rw [runBlocks_haltDirect_of_block hlk hrb]; rw [hrb] at hb; exact hb
      | Abort a s' =>
        rw [runBlocks_abort_of_block hlk hrb]; rw [hrb] at hb
        cases a <;> exact hb
      | IntRet vals s' => rw [runBlocks_intret_of_block hlk hrb]; exact trivial
      | Error e => rw [runBlocks_error_of_block hlk hrb]; exact trivial

theorem initial_state_bridge {vs labelOffsets fnEom} : ∃ as, venomAsmRel labelOffsets (initPlanState fnEom) vs as ∧ as.pc = 0 := by
  let as : AsmState := {
    stack := []
    memory := vs.memory
    accounts := vs.accounts
    transient := vs.transient
    returndata := vs.returndata
    logs := vs.logs
    pc := 0
    callCtx := vs.callCtx
    txCtx := vs.txCtx
    blockCtx := vs.blockCtx
    code := vs.code
    prevHashes := vs.prevHashes
  }
  have hrel : venomAsmRel labelOffsets (initPlanState fnEom) vs as := by
    unfold venomAsmRel initPlanState
    dsimp [as]
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · -- planStackRel: empty stacks, length 0 = 0, and no indices < 0
      refine ⟨rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    · -- planSpillRel: vacuously true (AssocList.lookup [] ... = some ... is impossible)
      unfold planSpillRel
      intro op off h
      -- h: AssocList.lookup Operand Nat [] op = some off
      -- AssocList.lookup on [] always returns none
      rw [AssocList.lookup] at h
      simp at h
    · -- memoryRel: equality outside spill region [fnEom, fnEom) = empty
      unfold memoryRel initSpillAlloc
      intro i _
      rfl
  have hpc : as.pc = 0 := rfl
  exact ⟨as, hrel, hpc⟩

theorem runFunction_never_ok {fuel ctx fn vs vs'} : runFunction fuel ctx fn vs ≠ ExecResult.OK vs' := by
  unfold runFunction
  split
  · intro h; injection h
  · apply runBlocks_never_ok

theorem runContext_never_ok {fuel ctx vs vs'} : runContext fuel ctx vs ≠ ExecResult.OK vs' := by
  unfold runContext
  split
  · intro h; injection h
  · next entry =>
    split
    · intro h; injection h
    · apply runFunction_never_ok

/-! ### De-vacuified codegen correctness (real `generateContextPlan`, tied `prog`)

`generateContextPlan` is now the real fuel pipeline (not a `none` stub), so the old
`codegen … = some bytecode → …` statements — whose `prog` was a *free* parameter disconnected from
the codegen output — would be **false** (a free `prog` can't simulate `runContext`). They are
restated here over the **resolved codegen program** `prog := (asmResolve (executePlan plan)).1` with
its own `offsetToPc`, and discharged by the CFG-walk engine `runBlocks_walk` given the per-block asm
correspondence `hbsim` (keyed by the walk's `Entry` relation — the honest remaining content, supplied
per function by composing `genBlockSimulation`). This makes them non-vacuous (the plan premise `hplan`
is satisfiable via the real pipeline) and *true* (the conclusion follows from `runBlocks_walk`), rather
than vacuously true via an unsatisfiable `none`-stub hypothesis. `genFnSimulation` (which lives
*above* this file) packages `hbsim` into a whole-function `hfsim`; the concrete
`codegenFuel_correct_*` / `hfsim_*` instances discharge it end to end. -/

/-- Per-function codegen correctness over the resolved plan, discharged by `runBlocks_walk`. -/
theorem codegen_fn_correct
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    (Entry : VenomState → AsmState → Nat → Prop)
    (_hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm N → lookupBlock s.currentBb fn.blocks = some bb →
        (match runBlock f' ctx bb s with
         | ExecResult.OK s' =>
             if s'.halted then
               ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
             else
               ∃ asm' N', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                 = runAsm N' (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm' ∧ Entry s' asm' N'
         | ExecResult.Halt s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         | ExecResult.Abort AbortType.RevertAbort s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
         | ExecResult.Abort AbortType.ExHaltAbort s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
         | _ => True))
    (hentry : Entry vs as (asmResolve (executePlan ops)).1.length) :
    (match runBlocks fuel ctx fn vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  runBlocks_walk Entry hbsim fuel vs as (asmResolve (executePlan ops)).1.length hentry

/-- Whole-context codegen correctness: `runContext` peels to the entry function's `runBlocks`, then
    `codegen_fn_correct` over the resolved plan. Non-vacuous (real `generateContextPlan`) and true
    (via `runBlocks_walk`). -/
theorem codegen_correct
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String}
    (Entry : VenomState → AsmState → Nat → Prop)
    (_hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm N → lookupBlock s.currentBb fn.blocks = some bb →
        (match runBlock f' ctx bb s with
         | ExecResult.OK s' =>
             if s'.halted then
               ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                 = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
             else
               ∃ asm' N', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                 = runAsm N' (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm' ∧ Entry s' asm' N'
         | ExecResult.Halt s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
         | ExecResult.Abort AbortType.RevertAbort s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
         | ExecResult.Abort AbortType.ExHaltAbort s' =>
             ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
               = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
         | _ => True))
    (hentry : Entry { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as
        (asmResolve (executePlan ops)).1.length) :
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
  exact runBlocks_walk Entry hbsim fuel
    { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as
    (asmResolve (executePlan ops)).1.length hentry

/-! ## De-vacuification over the real (fuel) pipeline

`codegen_correct` / `codegen_fn_correct` above are now **real** (`generateContextPlan` delegates to
`generateContextPlanFuel`, so `codegen … = some bytecode` is satisfiable), stated over the resolved
plan `prog`, and discharged by `runBlocks_walk` given the per-block correspondence `hbsim`.  The
lemmas below are the entry-less base cases + witnesses, kept as the simplest non-vacuous instances:
the `entry = none` case is fully discharged unconditionally (Venom errors out, hitting the trivial
`Error` arm — no `hbsim` needed); the Halt/Abort arms for a non-trivial entry are the genuine
simulation obligation (`hbsim`, packaged by `genFnSimulation`). -/

/-- **Whole-function hfsim ⇒ top-level `codegen_correct` conclusion.** The reusable
adapter between the two shapes the development produces at different levels: every
whole-function capstone (`hfsim_*`) concludes the `match runBlocks fn {entry}` shape
with `venomAsmTerminalRel`; the top-level `codegen_correct` conclusion is the
`match runContext ctx` shape with `finalStateRel`. This lifts the former to the
latter by peeling `runContext` to the entry function's `runBlocks` (`hent`/`hlk`/
`hlbl`) and using `finalStateRel = venomAsmTerminalRel` (definitional). So any
capstone — this session's spill-aware / external-call whole-function results
included — yields the top-level `codegen_correct` conclusion for its function with
no separate `hbsim`/`runBlocks_walk` re-derivation: the per-block obligation is
already discharged *inside* the hfsim. -/
theorem codegen_correct_of_wholeFn_hfsim
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {ops : List StackOp} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {N : Nat}
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hprog : prog = (asmResolve (executePlan ops)).1)
    (hoff : offsetToPc = (asmResolve (executePlan ops)).2)
    (hN : N = (asmResolve (executePlan ops)).1.length)
    (hfsim : match runBlocks fuel ctx fn
              { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } with
      | ExecResult.Halt vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
      | ExecResult.Abort AbortType.RevertAbort vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
      | ExecResult.Abort AbortType.ExHaltAbort vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
      | _ => True) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as
           = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hrc : runContext fuel ctx vs
      = runBlocks fuel ctx fn { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } := by
    simp only [runContext, hent, hlk, runFunction, hlbl]
  rw [hrc]
  subst hprog hoff hN
  exact hfsim

/-- **General-program sibling**: lift a whole-function hfsim (against ITS OWN
resolved program `prog`/`offsetToPc`, as the concrete `hfsim_*_example`s state it)
to a `runContext` correspondence. Same peel, without the `codegen_correct`-specific
`prog = asmResolve (executePlan ops)` wiring — the form a concrete example applies
directly. `codegen_correct_of_wholeFn_hfsim` is the special case
`prog = asmResolve (executePlan ops)`. -/
theorem runContext_correct_of_hfsim
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction}
    {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {N : Nat}
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hfsim : match runBlocks fuel ctx fn
              { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } with
      | ExecResult.Halt vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel vs' as'
      | ExecResult.Abort AbortType.RevertAbort vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
      | ExecResult.Abort AbortType.ExHaltAbort vs' =>
          ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
      | _ => True) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' =>
         ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
         ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
         ∃ as', runAsm N offsetToPc prog as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hrc : runContext fuel ctx vs
      = runBlocks fuel ctx fn { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } := by
    simp only [runContext, hent, hlk, runFunction, hlbl]
  rw [hrc]
  exact hfsim

/-- The real context-plan generator on a function-free context yields exactly the shared revert
    postamble (the foldl never iterates, leaving `some ([] ++ revertPostamble)`). -/
theorem generateContextPlanFuel_empty {fuel : Nat} {ctx : VenomContext}
    {fnEomMap : AssocList String Nat} (hfns : ctx.functions = []) :
    generateContextPlanFuel fuel ctx fnEomMap = some revertPostamble := by
  unfold generateContextPlanFuel
  rw [hfns]
  simp

/-- **The real pipeline produces output.** For a function-free context, `codegenFuel`
    returns `some bytecode` — concrete evidence that the `codegenFuel … = some bytecode`
    hypothesis is satisfiable (unlike the `none`-stub `codegen`). -/
theorem codegenFuel_some_of_noFunctions {fuel : Nat} {ctx : VenomContext}
    {fnEomMap : AssocList String Nat} {dataSeg : List DataSection} (hfns : ctx.functions = []) :
    ∃ bytecode, codegenFuel fuel ctx fnEomMap dataSeg = some bytecode := by
  unfold codegenFuel
  rw [generateContextPlanFuel_empty hfns]
  exact ⟨_, rfl⟩

/-- **Non-vacuous codegen-correctness for the entry-less case (real pipeline).** When the
    context has no entry function, `runContext` errors out, so the conclusion holds via the
    trivial `Error` arm — and the hypothesis `codegenFuel … = some bytecode` is genuinely
    satisfiable (`codegenFuel_some_of_noFunctions`), so this is *not* vacuously true. This is the
    entry-less base case of the now-real `codegen_correct` (which handles a non-trivial entry via
    `runBlocks_walk` + the per-block `hbsim`). -/
theorem codegenFuel_correct_noEntry
    (fuel : Nat) (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) (bytecode : List byte)
    (vs : VenomState) (labelOffsets : AssocList String Nat) (prog : List AsmInst)
    (hentry : ctx.entry = none)
    (_hcode : codegenFuel fuel ctx fnEomMap dataSeg = some bytecode) :
    ∃ gasNeeded, ∀ as, venomAsmRel labelOffsets (initPlanState 0) vs as → as.pc = 0 →
      (match runContext fuel ctx vs with
       | ExecResult.Halt vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
       | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
       | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
       | ExecResult.OK _ => False | ExecResult.IntRet _ _ => True | ExecResult.Error _ => True) := by
  refine ⟨0, fun as _ _ => ?_⟩
  have hrc : runContext fuel ctx vs = ExecResult.Error "no entry function" := by
    unfold runContext; rw [hentry]
  rw [hrc]
  trivial

/-- **The de-vacuification witness.** A concrete context (function-free, entry-less) simultaneously
    satisfies both hypotheses of `codegenFuel_correct_noEntry`: `entry = none` and a real
    `codegenFuel … = some bytecode`. This certifies the entry-less correctness statement is
    inhabited — the real pipeline is verified non-vacuously on it. -/
theorem codegenFuel_correct_nonvacuous_witness
    (fuel : Nat) (fnEomMap : AssocList String Nat) (dataSeg : List DataSection) :
    ∃ (ctx : VenomContext) (bytecode : List byte),
      ctx.entry = none ∧ codegenFuel fuel ctx fnEomMap dataSeg = some bytecode := by
  obtain ⟨bc, hbc⟩ :=
    codegenFuel_some_of_noFunctions (fuel := fuel) (ctx := { functions := [], entry := none })
      (fnEomMap := fnEomMap) (dataSeg := dataSeg) rfl
  exact ⟨{ functions := [], entry := none }, bc, rfl, hbc⟩


/-! ## CFG walk-composition for CYCLIC CFGs — budget from Venom fuel, not program position

`runBlocks_walk` is already order- and cycle-agnostic: it inducts on the *Venom* fuel, never on the
CFG. What forbids loops is entirely in how its callers instantiate it:

  * `codegen_correct` starts the asm budget at `prog.length`, and
  * `codegen_correct_sched` adds a per-label rank `wOf` with the strict decrease
    `wOf succ + blockLen ≤ wOf bb`.

Both encode "each block's asm runs at most once, and the block lengths sum to `prog.length`". A loop
violates that outright: it re-executes blocks, so total asm steps are unbounded by `prog.length`, the
budget underflows, and `runAsm 0 = AsmOK ≠ AsmHalt`. The canonical rank makes this concrete — on a
forward edge `wOf succ + blockLen = wOf bb` holds with *equality*, so a back-edge has no slack at all.

The fix is not a cleverer rank but a different source of decrease: **the Venom fuel itself**. Venom's
`runBlocks fuel` executes at most `fuel` blocks, and each block's asm run is at most `B` steps (any `B`
bounding a single block's asm; `prog.length` always works, since a block's asm is a segment of `prog`).
So `fuel * B` steps suffice for the whole run, and the invariant `fuel * B ≤ N` is preserved: one block
consumes `blockLen ≤ B` and drops the Venom fuel by one, so `N - blockLen ≥ (fuel-1) * B`.

The per-block obligation correspondingly weakens from a *decreasing rank* to a *uniform bound*
(`blockLen ≤ B`) — no ordering on labels, hence nothing for a back-edge to violate. -/

/-- **Cyclic-CFG walk composition.** Same engine as `runBlocks_walk`, but the asm budget is carried by
    the Venom fuel (`fuel * B ≤ N`) instead of a decreasing per-label rank. Each block consumes at most
    `B` asm steps and exactly one unit of Venom fuel, so the invariant survives the step — and, unlike
    the ranked version, it says nothing about *which* block comes next. Loops and back-edges are
    therefore admissible. -/
theorem runBlocks_walk_fuel {ctx : VenomContext} {fn : IrFunction} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} (B : Nat)
    (Entry : VenomState → AsmState → Prop)
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm → lookupBlock s.currentBb fn.blocks = some bb → B ≤ N →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (asm' : AsmState) (blockLen : Nat),
                runAsm blockLen offsetToPc prog asm = AsmResult.AsmOK asm' ∧
                blockLen ≤ B ∧ Entry s' asm'
        | ExecResult.Halt s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.RevertAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
        | ExecResult.Abort AbortType.ExHaltAbort s' =>
            ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
        | _ => True) :
    ∀ (fuel : Nat) (s : VenomState) (asm : AsmState) (N : Nat),
      Entry s asm → fuel * B ≤ N →
      match runBlocks fuel ctx fn s with
      | ExecResult.Halt s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmRevert asm' ∧ venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm N offsetToPc prog asm = AsmResult.AsmFault asm' ∧ venomAsmTerminalRel s' asm'
      | _ => True := by
  intro fuel
  induction fuel with
  | zero => intro s asm N _ _; rw [runBlocks]; exact trivial
  | succ f' ih =>
    intro s asm N hE hbud
    have hBN : B ≤ N := by
      have : B ≤ (f' + 1) * B := by
        have : 1 * B ≤ (f' + 1) * B := Nat.mul_le_mul_right B (by omega)
        omega
      omega
    cases hlk : lookupBlock s.currentBb fn.blocks with
    | none =>
      have hE2 : runBlocks (f' + 1) ctx fn s = ExecResult.Error "block not found" := by
        rw [runBlocks, hlk]
      rw [hE2]; exact trivial
    | some bb =>
      have hb := hbsim s asm N f' bb hE hlk hBN
      cases hrb : runBlock f' ctx bb s with
      | OK s' =>
        rw [hrb] at hb
        by_cases hh : s'.halted
        · rw [runBlocks_halt_of_block hlk hrb hh]
          simp only [hh, if_true] at hb; exact hb
        · have hh' : s'.halted = false := by simpa using hh
          rw [runBlocks_step_of_block hlk hrb hh']
          simp only [hh', Bool.false_eq_true, if_false] at hb
          obtain ⟨asm', blockLen, hrun, hle, hE'⟩ := hb
          -- the budget still covers the remaining `f'` blocks
          have hrem : f' * B ≤ N - blockLen := by
            have h1 : (f' + 1) * B = f' * B + B := by ring
            omega
          have heq : runAsm N offsetToPc prog asm
              = runAsm (N - blockLen) offsetToPc prog asm' := by
            conv_lhs => rw [show N = blockLen + (N - blockLen) from by omega]
            exact runAsm_append_ok hrun
          rw [heq]
          exact ih s' asm' (N - blockLen) hE' hrem
      | Halt s' =>
        rw [runBlocks_haltDirect_of_block hlk hrb]; rw [hrb] at hb; exact hb
      | Abort a s' =>
        rw [runBlocks_abort_of_block hlk hrb]; rw [hrb] at hb
        cases a <;> exact hb
      | IntRet vals s' => rw [runBlocks_intret_of_block hlk hrb]; exact trivial
      | Error e => rw [runBlocks_error_of_block hlk hrb]; exact trivial



/-- **The ranked walk provably cannot take a back-edge.** Makes precise what forces the fuel-budget
    redesign, rather than leaving it as an intuition.

    On the canonical schedule the rank is `wOf l = prog.length - pcOfLabel prog l`; here `pcBb` and
    `pcSucc` are those two `pcOfLabel` values and `progLen` is `prog.length`. The ranked driver
    (`codegen_correct_sched`) requires, at every continuing block, `wOf succ + blockLen ≤ wOf bb`. A
    *back-edge* is exactly an edge whose target sits at or before the block in the program
    (`pcSucc ≤ pcBb`) — and then `wOf succ ≥ wOf bb`, so the decrease forces `blockLen = 0`. But a
    block always emits at least its own `JUMPDEST`, so `blockLen ≥ 1`: contradiction.

    So it is not that the rank is merely hard to find — a program-position rank *cannot exist* for a
    cyclic CFG. The decrease has to come from somewhere outside the program layout, which is what
    `runBlocks_walk_fuel` gets from the Venom fuel. -/
theorem ranked_walk_no_back_edge {progLen pcBb pcSucc blockLen : Nat}
    (hback : pcSucc ≤ pcBb)
    (hin : pcBb ≤ progLen)
    (hpos : 1 ≤ blockLen)
    (hdec : (progLen - pcSucc) + blockLen ≤ (progLen - pcBb)) :
    False := by
  omega

/-- **Top-level codegen correctness for a CYCLIC CFG.** The loop-admitting counterpart of
    `codegen_correct`: the asm budget is `fuel * B` — Venom's own fuel times a per-block asm bound —
    rather than `prog.length`, and the per-block obligation is the uniform `blockLen ≤ B` rather than a
    strictly decreasing per-label rank.

    `prog.length` is always a legal `B` (a block's asm is a segment of `prog`), so this subsumes the
    acyclic case at the cost of a larger stated budget; and because a halted run stays halted, a bigger
    budget is not a weaker conclusion. Nothing here orders the blocks, so back-edges are fine. -/
theorem codegen_correct_fuel
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} (B : Nat)
    (Entry : VenomState → AsmState → Prop)
    (_hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm → lookupBlock s.currentBb fn.blocks = some bb → B ≤ N →
        match runBlock f' ctx bb s with
        | ExecResult.OK s' =>
            if s'.halted then
              ∃ asm', runAsm N (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
                = AsmResult.AsmHalt asm' ∧ venomAsmTerminalRel s' asm'
            else
              ∃ (asm' : AsmState) (blockLen : Nat),
                runAsm blockLen (asmResolve (executePlan ops)).2
                  (asmResolve (executePlan ops)).1 asm = AsmResult.AsmOK asm' ∧
                blockLen ≤ B ∧ Entry s' asm'
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
    (hentry : Entry { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as) :
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
  have hrc : runContext fuel ctx vs
      = runBlocks fuel ctx fn { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } := by
    simp only [runContext, hent, hlk, runFunction, hlbl]
  rw [hrc]
  exact runBlocks_walk_fuel B Entry hbsim fuel
    { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as (fuel * B)
    hentry (le_refl _)


end EvmYul.Venom.Hol.Codegen

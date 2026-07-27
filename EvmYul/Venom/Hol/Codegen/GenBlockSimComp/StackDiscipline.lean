/-
GenBlockSimComp / Phase 1 — body simulation & stack discipline

Split part of `GenBlockSimComp`; see that module's header for the full roadmap.
This part continues the single `EvmYul.Venom.Hol.Codegen` namespace and imports
the previous part, so the whole was cut horizontally with no change in meaning.
-/

import EvmYul.Venom.Hol.Codegen.GenInstSim
import EvmYul.Venom.Hol.Codegen.AsmResolveProofs
import EvmYul.Venom.Hol.Codegen.CodegenGenProps

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol EvmYul

/-- **Asm-side loop budget** (cyclic CFG). If one loop iteration runs `step` asm instructions and
    re-enters the loop header — `runAsm step prog (iter i) = AsmOK (iter (i+1))`, where the back-edge
    means `iter (i+1)` may sit at the *same or an earlier* pc than `iter i` — then `K` iterations run
    `K * step` instructions, landing at `iter K`.

    This is the budget revision a cyclic CFG needs. The acyclic walk uses `N = prog.length` (each
    block runs once, lengths summing to `prog.length`); a loop body executed `K` times instead needs
    `N = K * step`, which can far exceed `prog.length`. `runBlocks_walk` (CodegenCorrectness) is
    *already* loop-general — its statement has no acyclicity assumption; it inducts on the Venom fuel
    and threads an abstract budget `N` through the per-block `hbsim`, so a loop block simply re-establishes
    its `Entry` (the loop invariant) at the header with a smaller `N` each iteration. This lemma is the
    matching asm-side step count: it composes the per-iteration runs with `runAsm_compose`, so the
    caller can discharge `runBlocks_walk`'s back-edge budget transition `runAsm N … = runAsm N' …` with
    `N - N' = step` per iteration. Together they handle cyclic CFGs (the exit iteration — the JNZ that
    falls through instead of re-entering — is composed on top via `runAsm_add_ok`). -/
theorem runAsm_loop_iterate {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {step : Nat}
    (iter : Nat → AsmState)
    (hstep : ∀ i, runAsm step offsetToPc prog (iter i) = AsmResult.AsmOK (iter (i + 1))) :
    ∀ K, runAsm (K * step) offsetToPc prog (iter 0) = AsmResult.AsmOK (iter K) := by
  intro K
  induction K with
  | zero => simp [runAsm]
  | succ k ih =>
    have hcompose : runAsm (k * step + step) offsetToPc prog (iter 0) = AsmResult.AsmOK (iter (k + 1)) :=
      runAsm_compose ih (hstep k)
    rw [show (k + 1) * step = k * step + step from by ring]; exact hcompose

/-- `runAsm` decomposition: a successful `n`-step prefix lets the run continue from the reached
    state. The `AsmOK`-prefix companion of `runAsm_compose` — unlike it, the suffix run need not be
    `AsmOK` (so it composes an OK body with a *terminal* suffix). -/
theorem runAsm_add_ok {n m offsetToPc prog s s'}
    (h : runAsm n offsetToPc prog s = AsmResult.AsmOK s') :
    runAsm (n + m) offsetToPc prog s = runAsm m offsetToPc prog s' := by
  induction n generalizing s with
  | zero => simp only [runAsm] at h; injection h with he; subst he; rw [Nat.zero_add]
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by omega, runAsm]
    rw [runAsm] at h
    cases hstep : asmStep offsetToPc prog s with
    | AsmOK s'' => rw [hstep] at h; exact ih h
    | AsmHalt s'' => rw [hstep] at h; simp at h
    | AsmRevert s'' => rw [hstep] at h; simp at h
    | AsmFault s'' => rw [hstep] at h; simp at h
    | AsmError msg => rw [hstep] at h; simp at h

/-- Attach a halting terminal step after an OK body run: if the first `n` steps reach `AsmOK s'` and
    `asmStep` at `s'` halts, the whole `n+1`-step run halts. (`genBlockSimulation`'s `Halt` arm: a
    block body followed by `STOP`.) -/
theorem runAsm_seq_halt {n offsetToPc prog s s' s''}
    (h : runAsm n offsetToPc prog s = AsmResult.AsmOK s')
    (hstep : asmStep offsetToPc prog s' = AsmResult.AsmHalt s'') :
    runAsm (n + 1) offsetToPc prog s = AsmResult.AsmHalt s'' := by
  rw [runAsm_add_ok (m := 1) h]; show runAsm 1 offsetToPc prog s' = _
  unfold runAsm; rw [hstep]

/-- Attach a reverting terminal step after an OK body run. (`genBlockSimulation`'s `RevertAbort`
    arm: a block body followed by `REVERT`.) -/
theorem runAsm_seq_revert {n offsetToPc prog s s' s''}
    (h : runAsm n offsetToPc prog s = AsmResult.AsmOK s')
    (hstep : asmStep offsetToPc prog s' = AsmResult.AsmRevert s'') :
    runAsm (n + 1) offsetToPc prog s = AsmResult.AsmRevert s'' := by
  rw [runAsm_add_ok (m := 1) h]; show runAsm 1 offsetToPc prog s' = _
  unfold runAsm; rw [hstep]

/-- Attach a faulting terminal step after an OK body run. (`genBlockSimulation`'s `ExHaltAbort`
    arm: a block body followed by `INVALID`.) -/
theorem runAsm_seq_fault {n offsetToPc prog s s' s''}
    (h : runAsm n offsetToPc prog s = AsmResult.AsmOK s')
    (hstep : asmStep offsetToPc prog s' = AsmResult.AsmFault s'') :
    runAsm (n + 1) offsetToPc prog s = AsmResult.AsmFault s'' := by
  rw [runAsm_add_ok (m := 1) h]; show runAsm 1 offsetToPc prog s' = _
  unfold runAsm; rw [hstep]

/-! ## De-Option bridge: the generator's `instOps` fold collapses to a plain fold

`generateBlockPlan`'s instruction fold is `Option`-wrapped (`generateInstPlan` may fail on a
pre-codegen opcode). On a codegen-ready block every step succeeds, so the fold equals the plain
`(ops, ps)` fold of the de-Optioned step `gp` — the shape the body-fold simulation (`foldl_inst_sim`)
consumes. -/

/-- If every per-step `g a p` succeeds (with de-Optioned value `gp a p`), the option-fold equals the
    plain `(ops, ps)` fold of `gp`. -/
theorem optFold_eq_plain {α} {g : α → PlanState → Option (List StackOp × PlanState)}
    {gp : α → PlanState → List StackOp × PlanState}
    (l : List α) (ops0 : List StackOp) (ps0 : PlanState) (res : List StackOp × PlanState)
    (hg : ∀ a ∈ l, ∀ p, g a p = some (gp a p))
    (h : l.foldl (optFoldStep g) (some (ops0, ps0)) = some res) :
    res = l.foldl (fun (acc : List StackOp × PlanState) (a : α) =>
                    (acc.1 ++ (gp a acc.2).1, (gp a acc.2).2)) (ops0, ps0) := by
  induction l generalizing ops0 ps0 with
  | nil => simp only [List.foldl_nil] at h; exact (Option.some.inj h).symm
  | cons x xs ih =>
    obtain ⟨so, psn, hgx, htail⟩ := foldl_optFold_cons_some g x xs ops0 ps0 res h
    rw [hg x List.mem_cons_self ps0] at hgx
    obtain ⟨hso, hpsn⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgx
    subst hso; subst hpsn
    rw [List.foldl_cons]
    exact ih (ops0 ++ (gp x ps0).1) (gp x ps0).2 (fun a ha p => hg a (List.mem_cons_of_mem _ ha) p) htail

/-- The `(ops, ps)` part of `foldl_inst_sim`'s combined `(ops, ps, vs)` fold (with the plan-gen `gp`
    and the Venom step `gv` split) equals the plain `(ops, ps)` fold of `gp` — the plan generation
    doesn't consult `vs`. Bridges `optFold_eq_plain`'s plain fold to the combined fold
    `foldl_inst_sim` runs over. -/
theorem foldl_inst_proj {α} (gp : α → PlanState → List StackOp × PlanState)
    (gv : α → VenomState → VenomState) (l : List α) :
    ∀ (ops0 : List StackOp) (ps0 : PlanState) (vs0 : VenomState),
      (l.foldl (fun (acc : List StackOp × PlanState × VenomState) (x : α) =>
          (acc.1 ++ (gp x acc.2.1).1, (gp x acc.2.1).2, gv x acc.2.2)) (ops0, ps0, vs0)).1
        = (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
            (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) (ops0, ps0)).1
    ∧ (l.foldl (fun (acc : List StackOp × PlanState × VenomState) (x : α) =>
          (acc.1 ++ (gp x acc.2.1).1, (gp x acc.2.1).2, gv x acc.2.2)) (ops0, ps0, vs0)).2.1
        = (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
            (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) (ops0, ps0)).2 := by
  induction l with
  | nil => intro ops0 ps0 vs0; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro ops0 ps0 vs0
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (ops0 ++ (gp x ps0).1) (gp x ps0).2 (gv x vs0)

/-- The `vs` part of `foldl_inst_sim`'s combined fold is the plain left-fold of the Venom step
    `gv` — independent of `ops`/`ps`. -/
theorem foldl_inst_proj_vs {α} (gp : α → PlanState → List StackOp × PlanState)
    (gv : α → VenomState → VenomState) (l : List α) :
    ∀ (ops0 : List StackOp) (ps0 : PlanState) (vs0 : VenomState),
      (l.foldl (fun (acc : List StackOp × PlanState × VenomState) (x : α) =>
          (acc.1 ++ (gp x acc.2.1).1, (gp x acc.2.1).2, gv x acc.2.2)) (ops0, ps0, vs0)).2.2
        = l.foldl (fun (v : VenomState) (x : α) => gv x v) vs0 := by
  induction l with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro ops0 ps0 vs0; rw [List.foldl_cons, List.foldl_cons]; exact ih _ _ _

/-! ## Block body simulation (modulo `execBlock`)

Composing the per-instruction sims (`hstep`) over the block's plain instruction fold: running the
generated body simulates, threading the plan via `gp` and the Venom state via the `gv` left-fold.
This is `foldl_inst_sim` instantiated with the (plan-gen, Venom-step) split `g` and re-expressed on
the plain `(ops, ps)` fold (via `foldl_inst_proj`/`_vs`). To plug into `genBlockSimulation` it
remains to (1) take `gp = generateInstPlan` (so the plain fold = `generateBlockPlan`'s `instOps` via
`optFold_eq_plain`) and (2) identify the `gv` left-fold with `execBlock`'s `vs`. -/

theorem foldPlain_sim {α} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : α → PlanState → List StackOp × PlanState)
    (gv : α → VenomState → VenomState)
    (hstep : ∀ (x : α) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gv x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (l : List α) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
        (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
              (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length offsetToPc prog as0
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo
             (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
               (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
             (l.foldl (fun (v : VenomState) (x : α) => gv x v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (l.foldl (fun (acc : List StackOp × PlanState) (x : α) =>
              (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length := by
  obtain ⟨hops, hps⟩ := foldl_inst_proj gp gv l [] ps0 vs0
  have hvs := foldl_inst_proj_vs gp gv l [] ps0 vs0
  rw [← hops, ← hps, ← hvs]
  rw [← hops] at hblock
  exact foldl_inst_sim lo offsetToPc prog (fun p v x => ((gp x p).1, (gp x p).2, gv x v))
    hstep l ps0 vs0 as0 hrel0 hblock

/-! ## `generateInstPlan` connection: instOps is the plain `generateRegularInstPlan` fold

For a block whose body instructions are all "regular" (not pre-codegen / PHI / OFFSET / PARAM /
NOP), `generateInstPlan` is `generateRegularInstPlan` (`generateInstPlan_regular_eq`), so
`generateBlockPlan`'s `Option`-wrapped `instOps` fold collapses (via `optFold_eq_plain`) to the plain
`generateRegularInstPlan` fold — the `gp` that `foldPlain_sim` consumes. -/

theorem genInstOps_eq_plain
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    (bb : BasicBlock) (ps2 : PlanState) (instOps : List StackOp) (ps3 : PlanState)
    (hreg : ∀ inst ∈ nonParamInsts bb, ¬ isPreCodegenOpcode inst.opcode ∧
      inst.opcode ≠ Opcode.PHI ∧ inst.opcode ≠ Opcode.OFFSET ∧
      inst.opcode ≠ Opcode.PARAM ∧ inst.opcode ≠ Opcode.NOP)
    (hf : ((nonParamInsts bb).zipIdx.foldl
        (fun (acc : Option (List StackOp × PlanState)) (instI : Instruction × Nat) =>
          match acc with
          | none => none
          | some (ops, psc) =>
            let (inst, i) := instI
            let nextLive :=
              if i + 1 < (nonParamInsts bb).length then
                liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
              else liveVarsAt liveness bb.label bb.instructions.length
            let nextIsTerm :=
              if i + 1 < (nonParamInsts bb).length then
                isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
            match generateInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb) nextIsTerm
                    bb.label psc with
            | none => none
            | some (stepOps, psn) => some (ops ++ stepOps, psn))
        (some ([], ps2))) = some (instOps, ps3)) :
    (instOps, ps3) = (nonParamInsts bb).zipIdx.foldl
        (fun (acc : List StackOp × PlanState) (instI : Instruction × Nat) =>
          let (inst, i) := instI
          let nextLive :=
            if i + 1 < (nonParamInsts bb).length then
              liveVarsAt liveness bb.label (i + (getParams bb.instructions).length + 1)
            else liveVarsAt liveness bb.label bb.instructions.length
          let nextIsTerm :=
            if i + 1 < (nonParamInsts bb).length then
              isTerminator (nonParamInsts bb)[i + 1]!.opcode else false
          (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).1,
           (generateRegularInstPlan liveness dfg cfg fn inst nextLive (bbIsHalting bb)
                      nextIsTerm bb.label acc.2).2))
        ([], ps2) := by
  refine optFold_eq_plain (nonParamInsts bb).zipIdx [] ps2 (instOps, ps3) ?_ hf
  intro instI hmem psc
  obtain ⟨inst, i⟩ := instI
  have hmem' : inst ∈ nonParamInsts bb := by
    simpa using List.mem_map_of_mem (f := Prod.fst) hmem
  obtain ⟨h0, hphi, hoff, hparam, hnop⟩ := hreg inst hmem'
  simpa using generateInstPlan_regular_eq h0 hphi hoff hparam hnop

/-! ## execBlock body peeling (the Venom-side recursion alignment)

`execBlock` walks `bb.instructions` by `instIdx`, threading `stepInstBase` OK states. For a block
whose first `body.length` instructions (from `instIdx = start`) are non-terminators that all step to
`OK`, `execBlock` peels them off one by one and continues on the terminator from the threaded end
state. `execBodyThread` is the pure list-fold that threads those OK states (with `instIdx`
advancing exactly as `execBlock` advances it), and `execBlock_body_prefix` proves `execBlock`
follows it — isolating the fuel/`instIdx` recursion from the asm side entirely. -/

/-- Threads `stepInstBase` over a non-terminator body, advancing `instIdx` exactly as `execBlock`
    does (`{s' with instIdx := start + 1}`); `none` if any step fails to return `OK`. -/
def execBodyThread : List Instruction → Nat → VenomState → Option VenomState
  | [], _, s => some s
  | inst :: rest, start, s =>
    match stepInstBase inst s with
    | ExecResult.OK s' => execBodyThread rest (start + 1) { s' with instIdx := start + 1 }
    | _ => none

theorem execBlock_body_prefix (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat) :
    ∀ (body : List Instruction) (start : Nat) (s sEnd : VenomState),
    s.instIdx = start →
    (∀ (j : Nat) (hj : j < body.length), getInstruction bb (start + j) = some body[j]) →
    (∀ inst ∈ body, isTerminator inst.opcode = false) →
    execBodyThread body start s = some sEnd →
    execBlock (body.length + restFuel) ctx bb s = execBlock restFuel ctx bb sEnd := by
  intro body
  induction body with
  | nil =>
    intro start s sEnd _ _ _ hthread
    simp only [execBodyThread] at hthread
    obtain rfl := Option.some.inj hthread
    simp
  | cons inst rest ih =>
    intro start s sEnd hidx hsplit hnonterm hthread
    have hget : getInstruction bb s.instIdx = some inst := by
      rw [hidx]; have := hsplit 0 (by simp); simpa using this
    have hterm : isTerminator inst.opcode = false := hnonterm inst (by simp)
    simp only [execBodyThread] at hthread
    cases hstep : stepInstBase inst s with
    | OK s' =>
      rw [hstep] at hthread
      have hlen : (inst :: rest).length + restFuel = (rest.length + restFuel) + 1 := by
        simp [List.length_cons]; omega
      rw [hlen, execBlock_step_nonterm (rest.length + restFuel) ctx bb s s' inst hget hstep hterm,
          hidx]
      refine ih (start + 1) { s' with instIdx := start + 1 } sEnd rfl ?_ ?_ hthread
      · intro j hj
        rw [show start + 1 + j = start + (j + 1) by omega]
        have := hsplit (j + 1) (by simp [List.length_cons]; omega)
        simpa using this
      · intro i hi; exact hnonterm i (List.mem_cons_of_mem _ hi)
    | IntRet _ _ => rw [hstep] at hthread; simp at hthread
    | Halt _ => rw [hstep] at hthread; simp at hthread
    | Abort _ _ => rw [hstep] at hthread; simp at hthread
    | Error _ => rw [hstep] at hthread; simp at hthread

/-- Out-of-fuel companion of `execBlock_body_prefix`: with `fuel ≤ body.length`, `execBlock` runs
    out before reaching the terminator and returns `Error` (the body steps all `OK`, but there is
    not enough fuel to finish). The discharge's insufficient-fuel arm uses this to land in
    `genBlockSimulation`'s vacuous `_ => True` branch. -/
theorem execBlock_oof (ctx : VenomContext) (bb : BasicBlock) :
    ∀ (body : List Instruction) (start fuel : Nat) (s sEnd : VenomState),
    s.instIdx = start →
    (∀ (j : Nat) (hj : j < body.length), getInstruction bb (start + j) = some body[j]) →
    (∀ inst ∈ body, isTerminator inst.opcode = false) →
    execBodyThread body start s = some sEnd →
    fuel ≤ body.length →
    ∃ e, execBlock fuel ctx bb s = ExecResult.Error e := by
  intro body
  induction body with
  | nil =>
    intro start fuel s sEnd _ _ _ _ hfuel
    obtain rfl : fuel = 0 := Nat.le_zero.mp (by simpa using hfuel)
    exact ⟨"out of fuel", by rw [execBlock]⟩
  | cons inst rest ih =>
    intro start fuel s sEnd hidx hsplit hnonterm hthread hfuel
    cases fuel with
    | zero => exact ⟨"out of fuel", by rw [execBlock]⟩
    | succ k =>
      have hk : k ≤ rest.length := by simp only [List.length_cons] at hfuel; omega
      have hget : getInstruction bb s.instIdx = some inst := by
        rw [hidx]; have := hsplit 0 (by simp); simpa using this
      have hterm : isTerminator inst.opcode = false := hnonterm inst (by simp)
      simp only [execBodyThread] at hthread
      cases hstep : stepInstBase inst s with
      | OK s' =>
        rw [hstep] at hthread
        rw [execBlock_step_nonterm k ctx bb s s' inst hget hstep hterm, hidx]
        refine ih (start + 1) k { s' with instIdx := start + 1 } sEnd rfl ?_ ?_ hthread hk
        · intro j hj
          rw [show start + 1 + j = start + (j + 1) by omega]
          have := hsplit (j + 1) (by simp [List.length_cons]; omega)
          simpa using this
        · intro i hi; exact hnonterm i (List.mem_cons_of_mem _ hi)
      | IntRet _ _ => rw [hstep] at hthread; simp at hthread
      | Halt _ => rw [hstep] at hthread; simp at hthread
      | Abort _ _ => rw [hstep] at hthread; simp at hthread
      | Error _ => rw [hstep] at hthread; simp at hthread

/-- The Venom step `gv` for the body fold: take `stepInstBase`'s OK state and set `instIdx` to
    `i + 1` exactly as `execBlock`/`execBodyThread` advance it (on a non-OK step it is irrelevant —
    `execBodyThread` would have failed). `instIdx` is invisible to `venomAsmRel`, so the
    per-instruction sims that `foldPlain_sim` consumes are unaffected by the `instIdx` setting. -/
def gvBodyStep (x : Instruction × Nat) (v : VenomState) : VenomState :=
  match stepInstBase x.1 v with
  | ExecResult.OK s' => { s' with instIdx := x.2 + 1 }
  | _ => v

/-- `venomAsmRel` does not read `instIdx`, so setting it is invisible to the relation. This lets a
    per-instruction sim (which concludes on `stepInstBase`'s raw OK state) feed `foldPlain_sim`'s
    `gvBodyStep` (which sets `instIdx`) unchanged. -/
@[simp] theorem venomAsmRel_instIdx (lo : AssocList String Nat) (ps : PlanState) (v : VenomState)
    (as : AsmState) (n : Nat) :
    venomAsmRel lo ps { v with instIdx := n } as = venomAsmRel lo ps v as := rfl

/-- The `gv`-fold of `foldPlain_sim` (over `body.zipIdx start` with `gvBodyStep`) is exactly
    `execBodyThread`'s threaded end state — `gvBodyStep` tracks `instIdx` identically, so the fold
    and the thread stay state-for-state equal. This closes the gap between `foldPlain_sim`'s `vs`
    and `execBlock_body_prefix`. -/
theorem execBodyThread_eq_gvFold (body : List Instruction) :
    ∀ (start : Nat) (s sEnd : VenomState),
    execBodyThread body start s = some sEnd →
    (body.zipIdx start).foldl (fun v x => gvBodyStep x v) s = sEnd := by
  induction body with
  | nil =>
    intro start s sEnd hthread
    simp only [execBodyThread] at hthread
    obtain rfl := Option.some.inj hthread
    rfl
  | cons inst rest ih =>
    intro start s sEnd hthread
    simp only [execBodyThread] at hthread
    cases hstep : stepInstBase inst s with
    | OK s' =>
      rw [hstep] at hthread
      rw [show (inst :: rest).zipIdx start = (inst, start) :: rest.zipIdx (start + 1) from rfl,
          List.foldl_cons]
      have hgv : gvBodyStep (inst, start) s = { s' with instIdx := start + 1 } := by
        simp only [gvBodyStep, hstep]
      rw [hgv]
      exact ih (start + 1) { s' with instIdx := start + 1 } sEnd hthread
    | IntRet _ _ => rw [hstep] at hthread; simp at hthread
    | Halt _ => rw [hstep] at hthread; simp at hthread
    | Abort _ _ => rw [hstep] at hthread; simp at hthread
    | Error _ => rw [hstep] at hthread; simp at hthread

/-! ## Cohesive body simulation (the assembly's body step)

Composing the round's pillars into the single statement `genBlockSimulation` consumes for a block's
non-terminator body `front`: given per-instruction sims (`hstep`, with the body Venom step
`gvBodyStep`) and that `execBodyThread` threads `front` to `sEnd`, running the generated body asm
from `as0` reaches an `as'` simulating the plan after the body, with the Venom side at exactly
`sEnd` — `execBlock`'s peeled prefix (`execBlock_body_prefix`). Chains `foldPlain_sim` (asm
composition) with `execBodyThread_eq_gvFold` (the `gv`-fold *is* `sEnd`). -/

theorem genBlockBody_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (start : Nat)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front start vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ((front.zipIdx start).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan ((front.zipIdx start).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ((front.zipIdx start).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd as' ∧
           as'.pc = as0.pc + (executePlan ((front.zipIdx start).foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length := by
  have hfold := foldPlain_sim gp gvBodyStep hstep (front.zipIdx start) ps0 vs0 as0 hrel0 hblock
  rw [execBodyThread_eq_gvFold front start vs0 sEnd hthread] at hfold
  exact hfold

/-! ## Lifting per-instruction sims to body steps (`gvBodyStep` form)

The per-instruction asm sims (`genRegularInstPlan_commBinopVar_sim`, … in `GenInstSim`) conclude on
the *raw* Venom step `updateVar out w v`. `genBlockBody_sim`'s `hstep` instead wants the body step
`gvBodyStep (inst, idx) v`, which is that raw `stepInstBase` OK-state with `instIdx` set. Since
`venomAsmRel` ignores `instIdx` (`venomAsmRel_instIdx`), the two coincide once `stepInstBase inst v
= OK (updateVar out w v)` is supplied (via `stepInstBase_binopVar` for binops). This lemma performs
that lift opcode-agnostically — it converts any `updateVar`-shaped per-instruction sim into the
`gvBodyStep` shape the fold consumes, decoupled from the per-opcode hypothesis list. -/
theorem gvBodyStep_of_updateVar {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {inst : Instruction} {idx : Nat} {ps' : PlanState}
    {v : VenomState} {as : AsmState} {plan : List StackOp} {out : String} {w : bytes32}
    (hstepEq : stepInstBase inst v = ExecResult.OK (updateVar out w v))
    (hsim : ∃ s', runAsm (executePlan plan).length offsetToPc prog as = AsmResult.AsmOK s' ∧
             venomAsmRel lo ps' (updateVar out w v) s' ∧
             s'.pc = as.pc + (executePlan plan).length) :
    ∃ s', runAsm (executePlan plan).length offsetToPc prog as = AsmResult.AsmOK s' ∧
          venomAsmRel lo ps' (gvBodyStep (inst, idx) v) s' ∧
          s'.pc = as.pc + (executePlan plan).length := by
  obtain ⟨s', hrun, hrel, hpc⟩ := hsim
  refine ⟨s', hrun, ?_, hpc⟩
  have hgv : gvBodyStep (inst, idx) v = { updateVar out w v with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  rw [hgv, venomAsmRel_instIdx]
  exact hrel

/-- General `gvBodyStep` bridge — any `OK` state, not only `updateVar`. Needed for stores/other ops
    whose `stepInstBase` OK result isn't an `updateVar` form. -/
theorem gvBodyStep_of_ok {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {inst : Instruction} {idx : Nat} {ps' : PlanState}
    {v : VenomState} {as : AsmState} {plan : List StackOp} {sv : VenomState}
    (hstepEq : stepInstBase inst v = ExecResult.OK sv)
    (hsim : ∃ s', runAsm (executePlan plan).length offsetToPc prog as = AsmResult.AsmOK s' ∧
             venomAsmRel lo ps' sv s' ∧
             s'.pc = as.pc + (executePlan plan).length) :
    ∃ s', runAsm (executePlan plan).length offsetToPc prog as = AsmResult.AsmOK s' ∧
          venomAsmRel lo ps' (gvBodyStep (inst, idx) v) s' ∧
          s'.pc = as.pc + (executePlan plan).length := by
  obtain ⟨s', hrun, hrel, hpc⟩ := hsim
  refine ⟨s', hrun, ?_, hpc⟩
  have hgv : gvBodyStep (inst, idx) v = { sv with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  rw [hgv, venomAsmRel_instIdx]
  exact hrel

/-! ## Stack-discipline invariant (per-block hsim builder)

A per-instruction invariant the codegen maintains in the non-spilling regime: no spills, a shallow
plan stack (`≤ 15`, so every var is DUP-reachable within DUP16 even after one operand grows it), and
every stacked var has a value in the Venom state. It discharges exactly the per-instruction side
conditions (`hnospill`/`hspill`/`hdepth`/`hlen`/`hvx`) that `venomAsmRel` alone cannot — turning a
per-instruction asm sim into a body step usable by `genBlockBody_sim`. (`venomAsmRel` stays
untouched; this is threaded *alongside* it.) -/
structure StackDisc (p : PlanState) (v : VenomState) : Prop where
  /-- No operand is spilled (the non-spilling regime). -/
  noSpill : ∀ op, alookup' p.spilled op = none
  /-- The plan stack is shallow enough that both operands of a binop stay DUP-reachable. -/
  shallow : p.stack.length ≤ 15
  /-- Every var on the plan stack has a value in the Venom state. -/
  defined : ∀ z, Operand.Var z ∈ p.stack → ∃ w, lookupVar z v = some w

/-- **Body step from the invariant — commutative var binop.** Under `StackDisc`, a commutative binop
    with two distinct live var operands both present on the stack and a fresh live output yields the
    body step `genBlockBody_sim` consumes (the `gvBodyStep` form). Every side condition of
    `genRegularInstPlan_commBinopVar_sim` is *derived* from the invariant: depths + bounds from
    membership and shallowness (`stackGetDepth_of_mem`, `stackGetDepth_append_ne`), operand values
    from `defined`, spill-freedom from `noSpill`, output distinctness from freshness. The Venom step
    is lifted to `gvBodyStep` via `stepInstBase_binopVar` + `gvBodyStep_of_updateVar`. This is the
    atom the per-block body fold will iterate (the remaining work being to prove `StackDisc` is
    preserved across the step). -/
theorem stackDisc_commBinopVar_bodyStep
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y out : String} {name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDisc ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by
    unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by have := hsd.shallow; omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hsim := genRegularInstPlan_commBinopVar_sim (d_x' := d_x + 1)
    hname hcomm hops houts hxy hox hoy rfl hlive hfresh (hsd.noSpill _)
    (hsd.noSpill _) hlivey hdepth_y hsmall_y hleny (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx'
    hwx hwy hdisp hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  exact gvBodyStep_of_updateVar (idx := idx) hstepEq hsim

/-! ## Headroom invariant + preservation (toward the body fold)

A binop is net `+1` on the plan stack (DUP×2 − pop2 + push), so the fixed `≤ 15` bound of
`StackDisc` is NOT preserved. `StackDiscH k` carries a *headroom* `k` (`length + k ≤ 15`): each
stack-growing instruction consumes one unit, so the bound stays true while the stack grows. The body
fold threads `k` from the body length down to `0`; `toStackDisc` recovers the fixed bound the
per-instruction step needs. -/
structure StackDiscH (k : Nat) (p : PlanState) (v : VenomState) : Prop where
  noSpill : ∀ op, alookup' p.spilled op = none
  shallow : p.stack.length + k ≤ 15
  defined : ∀ z, Operand.Var z ∈ p.stack → ∃ w, lookupVar z v = some w

/-- Headroom implies the fixed `≤ 15` bound (`length ≤ length + k ≤ 15`), so a `StackDiscH` state
    satisfies `StackDisc` — what the per-instruction body step consumes. -/
theorem StackDiscH.toStackDisc {k : Nat} {p : PlanState} {v : VenomState}
    (h : StackDiscH k p v) : StackDisc p v where
  noSpill := h.noSpill
  shallow := by have := h.shallow; omega
  defined := h.defined

/-! ### Spill-aware stack discipline (`StackDiscHS`)

The spilling counterpart of `StackDiscH`. Where the whole-function fold currently runs in the
non-spilling regime (`StackDiscH.noSpill` structurally forbids spilled operands), `StackDiscHS`
*permits* spills and instead carries their well-formedness (`spillWf`) — exactly the precondition the
restore path consumes. This is the foundation for lifting the body fold out of the no-spill regime:
`of_stackDiscH` bridges every existing (no-spill) state in; `stackDiscHS_emitInput_single_spilled`
demonstrates the invariant driving a spilled input through the real `emitInputPlan`. -/

/-- **Spill-aware stack discipline.** Instead of forbidding spills (`noSpill`), carries their
    well-formedness (`spillWf` — 32-aligned, in-bounds against the asm memory, `< 2^256`), exactly the
    precondition the restore path (`doRestore_sim`, `emitInputPlan_single_var_sim_spilled`) consumes.
    `shallow`/`defined` are unchanged. Depends on the asm state `s` for the memory bound. -/
structure StackDiscHS (k : Nat) (p : PlanState) (v : VenomState) (s : AsmState) : Prop where
  spillWf : ∀ o off, alookup' p.spilled o = some off → 32 ∣ off ∧ off + 32 ≤ s.memory.size ∧ off < 2 ^ 256
  shallow : p.stack.length + k ≤ 15
  defined : ∀ z, Operand.Var z ∈ p.stack → ∃ w, lookupVar z v = some w

/-- Every no-spill state (`StackDiscH`) is spill-aware for any asm state (`spillWf` vacuous). The
    bridge from the existing no-spill world into the spill-aware invariant. -/
theorem StackDiscHS.of_stackDiscH {k p v s} (h : StackDiscH k p v) : StackDiscHS k p v s where
  spillWf o off hlook := by rw [h.noSpill o] at hlook; simp at hlook
  shallow := h.shallow
  defined := h.defined

/-- Monotone in headroom (`b ≤ a`). -/
theorem StackDiscHS.mono {a b p v s} (h : StackDiscHS a p v s) (hab : b ≤ a) : StackDiscHS b p v s where
  spillWf := h.spillWf
  shallow := by have := h.shallow; omega
  defined := h.defined

/-- Recover `StackDiscH` when the state happens to have no spills. -/
theorem StackDiscHS.toStackDiscH {k p v s} (h : StackDiscHS k p v s)
    (hns : ∀ op, alookup' p.spilled op = none) : StackDiscH k p v where
  noSpill := hns
  shallow := h.shallow
  defined := h.defined


/-- Read a spill fact off the threaded exact map: `p.spilled = M` transports any `M`-lookup. -/
theorem alookup_of_spilled_eq {p : PlanState} {M : AssocList Operand Nat} {o : Operand}
    {v : Option Nat} (h : p.spilled = M) (hl : alookup' M o = v) : alookup' p.spilled o = v := by
  rw [h]; exact hl

/-- Transfer a program fetch across a pc equality (collapses the recurring
    `conv_lhs => rw [show Fin … from Fin.ext …]` blocks). -/
theorem prog_get_transfer {prog : List AsmInst} {a b : Nat} {i : AsmInst} {hb : b < prog.length}
    (e : a = b) (h : prog.get ⟨b, hb⟩ = i) {ha : a < prog.length} :
    prog.get ⟨a, ha⟩ = i := by subst e; exact h

/-- A spilled operand is valued in the Venom state (via `planSpillRel`, the 2nd `venomAsmRel` conjunct). -/
theorem venomAsmRel_spilled_defined {lo ps vs as v off}
    (hrel : venomAsmRel lo ps vs as) (hspill : alookup' ps.spilled (Operand.Var v) = some off) :
    ∃ w, lookupVar v vs = some w := by
  obtain ⟨val, hov, _⟩ := hrel.2.1 (Operand.Var v) off hspill
  rw [operandVal_var_eq_lookupVar] at hov
  exact ⟨val, hov⟩


/-- **Rebuild the spill-aware invariant after a step.** The post-state's spilled map is a sub-map of
    the pre-state's (unchanged, or shrunk by `aremove`) and memory only grew, so `spillWf` lifts;
    the caller supplies the new `shallow`/`defined`. Collapses the three-field re-establishment
    shared by every `stackDiscHS_*_preserve`. -/
theorem StackDiscHS.rebuild {k k' : Nat} {p p' : PlanState} {v v' : VenomState} {s s' : AsmState}
    (h : StackDiscHS k p v s)
    (hmem : s.memory.size ≤ s'.memory.size)
    (hsub : ∀ o off, alookup' p'.spilled o = some off → alookup' p.spilled o = some off)
    (hshallow : p'.stack.length + k' ≤ 15)
    (hdefined : ∀ z, Operand.Var z ∈ p'.stack → ∃ w, lookupVar z v' = some w) :
    StackDiscHS k' p' v' s' where
  spillWf o off hlook := by
    obtain ⟨ha, hc, h2⟩ := h.spillWf o off (hsub o off hlook)
    exact ⟨ha, by omega, h2⟩
  shallow := hshallow
  defined := hdefined

/-- **Attach the spill-aware invariant to a body-step simulation.** Given the sim's existential and
    a preservation fact valid for any memory-non-shrinking post state (discharged via
    `runAsm_memory_size_mono`), produce the four-conjunct `step_S` conclusion. Collapses the
    obtain/mono/refine tail shared by every `stackDiscHS_*_step_S`. -/
theorem bodyStepS_of_sim {n : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {as : AsmState} {lo : AssocList String Nat} {ps' : PlanState} {vs' : VenomState} {k : Nat}
    (hsim : ∃ as', runAsm n offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel lo ps' vs' as' ∧ as'.pc = as.pc + n)
    (hpres : ∀ as', as.memory.size ≤ as'.memory.size → StackDiscHS k ps' vs' as') :
    ∃ as', runAsm n offsetToPc prog as = AsmResult.AsmOK as' ∧ venomAsmRel lo ps' vs' as' ∧
           as'.pc = as.pc + n ∧ StackDiscHS k ps' vs' as' := by
  obtain ⟨as', hrun, hrel, hpc⟩ := hsim
  exact ⟨as', hrun, hrel, hpc, hpres as' (runAsm_memory_size_mono hrun)⟩

/-- Shallow-only binop DUP-depth chain: the 2-operand analogue of `ternopVar_depths_of_shallow` —
    both operands' DUP depths from just the headroom bound, no `noSpill` needed (the state may
    carry unrelated spills). -/
theorem binopVar_depths_of_shallow {ps : PlanState} {x y : String}
    (hshallow : ps.stack.length ≤ 15)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack) :
    ∃ d_y d_x',
      stackGetDepth (Operand.Var y) ps.stack = some d_y ∧ d_y ≤ 15 ∧ d_y < ps.stack.length ∧
      stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x' ∧ d_x' ≤ 15 ∧
        d_x' < (stackDup d_y ps.stack).length := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hxdup : Operand.Var x ∈ stackDup d_y ps.stack := by
    rw [hdupY]; exact List.mem_append.mpr (Or.inl hxmem)
  obtain ⟨d_x', hdepth_x', hlenx'⟩ := stackGetDepth_of_mem hxdup
  have hlen : (stackDup d_y ps.stack).length = ps.stack.length + 1 := by rw [hdupY]; simp
  exact ⟨d_y, d_x', hdepth_y, by omega, hleny, hdepth_x', by omega, hlenx'⟩

/-- **`StackDiscHS` preserved across a single spilled-operand emission** — pure invariant algebra.
    Given the pre-state discipline `StackDiscHS (k+2)`, the post-state (`emitOneInput_var_spilled_eq`
    shape: `v` restored+dupped atop, its spill entry gone), the fact that the run did not shrink memory
    (`hmemmono`), and that the restored var is valued (`hdef_v`), the spill-aware invariant holds at
    headroom `k` (stack grew by 2). -/
theorem stackDiscHS_spilled_preserve {k ps vs as as' v off}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hdef_v : ∃ w, lookupVar v vs = some w) :
    StackDiscHS k
      { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                spilled := aremove ps.spilled (Operand.Var v),
                alloc := freeSpillSlot off ps.alloc } vs as' := by
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some ps.spilled (Operand.Var v) o off' hlook
  · show (ps.stack ++ [Operand.Var v, Operand.Var v]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz
    · exact hsd.defined z hz
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_v

/-- **Spill-aware body-input step (single spilled operand).** `StackDiscHS` supplies exactly the
    `spillWf` the restore path needs, so a spilled live input threads through the real `emitInputPlan`
    with `venomAsmRel` preserved **and** the spill-aware invariant unconditionally re-established at
    headroom `k` — the memory-monotonicity side-fact is discharged by `runAsm_memory_size_mono`.
    Concrete demonstration that the invariant carries what unlocks spilling — the role
    `StackDiscH.noSpill` structurally excluded, now fully self-contained. -/
theorem stackDiscHS_emitInput_single_spilled {opc nl v ps lo vs as prog off k}
    {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS (k + 2) ps vs as)
    (hspill : alookup' ps.spilled (Operand.Var v) = some off)
    (hlive : nl.contains v = true)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v] nl ps).1).length ∧
           StackDiscHS k (emitInputPlan opc [Operand.Var v] nl ps).2 vs as' := by
  refine bodyStepS_of_sim
    (emitInputPlan_single_var_sim_spilled (offsetToPc := offsetToPc) hspill hlive hrel hsd.spillWf hblock)
    (fun as' hmemmono => ?_)
  have hshape : emitInputPlan opc [Operand.Var v] nl ps
      = ([StackOp.SORestore off, StackOp.SODup 1],
         { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                   spilled := aremove ps.spilled (Operand.Var v),
                   alloc := freeSpillSlot off ps.alloc }) := by
    have hone : emitInputPlan opc [Operand.Var v] nl ps = emitOneInput opc nl (Operand.Var v) ps := by
      unfold emitInputPlan
      simp only [List.foldl_cons, List.foldl_nil, List.nil_append, Prod.mk.eta]
    rw [hone, emitOneInput_var_spilled_eq hspill hlive]
  rw [hshape]
  exact stackDiscHS_spilled_preserve hsd hmemmono (venomAsmRel_spilled_defined hrel hspill)

/-- **`StackDiscHS` preservation across a both-restore of a spilled pair.** Emitting two spilled
    operands grows the stack by four (`[v,v] ++ [w,w]`) and frees both slots; the spill-aware invariant
    is re-established at four-lower headroom. The pair analogue of `stackDiscHS_spilled_preserve`. -/
theorem stackDiscHS_pair_both_spilled_preserve {k ps vs as as'} {v w : String} {offv offw : Nat}
    (hsd : StackDiscHS (k + 4) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hdef_v : ∃ x, lookupVar v vs = some x) (hdef_w : ∃ x, lookupVar w vs = some x) :
    StackDiscHS k
      { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v] ++ [Operand.Var w, Operand.Var w],
                spilled := aremove (aremove ps.spilled (Operand.Var v)) (Operand.Var w),
                alloc := freeSpillSlot offw (freeSpillSlot offv ps.alloc) } vs as' := by
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some _ (Operand.Var v) o off'
          (aremove_lookup_some _ (Operand.Var w) o off' hlook)
  · show (ps.stack ++ [Operand.Var v, Operand.Var v] ++ [Operand.Var w, Operand.Var w]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (hz | hz | hz) | hz | hz
    · exact hsd.defined z hz
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_w
    · injection hz with hz'; subst hz'; exact hdef_w

/-- **Spill-aware body-input step (both operands spilled).** `StackDiscHS` drives a two-spilled-operand
    `emitInputPlan` (both restored from their slots), preserving `venomAsmRel` and re-establishing the
    spill-aware invariant at headroom `k`. The pair analogue of `stackDiscHS_emitInput_single_spilled`;
    a building block for rerouting a 2-operand body producer off `StackDiscH.noSpill`. -/
theorem stackDiscHS_emitInput_pair_both_spilled {opc nl v w ps lo vs as prog offv offw k}
    {offsetToPc : AssocList Nat Nat}
    (hvw : v ≠ w)
    (hsd : StackDiscHS (k + 4) ps vs as)
    (hspillv : alookup' ps.spilled (Operand.Var v) = some offv)
    (hspillw : alookup' ps.spilled (Operand.Var w) = some offw)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length ∧
           StackDiscHS k (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' := by
  refine bodyStepS_of_sim
    (emitInputPlan_pair_both_spilled_sim (offsetToPc := offsetToPc) hvw hspillv hspillw hlivev hlivew hrel
        hsd.spillWf hblock)
    (fun as' hmemmono => ?_)
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                    spilled := aremove ps.spilled (Operand.Var v),
                                    alloc := freeSpillSlot offv ps.alloc } with hps1def
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore offv, StackOp.SODup 1], ps1) :=
    emitOneInput_var_spilled_eq hspillv hlivev
  have hspillw1 : alookup' ps1.spilled (Operand.Var w) = some offw := by
    rw [hps1def]
    show alookup' (aremove ps.spilled (Operand.Var v)) (Operand.Var w) = some offw
    unfold alookup'
    rw [aremove_lookup_ne ps.spilled (Operand.Var v) (Operand.Var w)
      (by intro h; injection h with h'; exact hvw h'.symm)]
    exact hspillw
  set ps2 : PlanState := { ps1 with stack := ps1.stack ++ [Operand.Var w, Operand.Var w],
                                     spilled := aremove ps1.spilled (Operand.Var w),
                                     alloc := freeSpillSlot offw ps1.alloc } with hps2def
  have htail : emitOneInput opc nl (Operand.Var w) ps1 = ([StackOp.SORestore offw, StackOp.SODup 1], ps2) :=
    emitOneInput_var_spilled_eq hspillw1 hlivew
  have hfold : (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 = ps2 := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hfold, hps2def, hps1def]
  exact stackDiscHS_pair_both_spilled_preserve hsd hmemmono
    (venomAsmRel_spilled_defined hrel hspillv) (venomAsmRel_spilled_defined hrel hspillw)

/-- `StackDiscHS` preservation across a `[spilled, live]` mixed emit (`[v,v]++[w]`, +3 headroom). -/
theorem stackDiscHS_pair_first_spilled_preserve {k ps vs as as'} {v w : String} {offv : Nat}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hdef_v : ∃ x, lookupVar v vs = some x) (hdef_w : ∃ x, lookupVar w vs = some x) :
    StackDiscHS k
      { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v] ++ [Operand.Var w],
                spilled := aremove ps.spilled (Operand.Var v),
                alloc := freeSpillSlot offv ps.alloc } vs as' := by
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some _ (Operand.Var v) o off' hlook
  · show (ps.stack ++ [Operand.Var v, Operand.Var v] ++ [Operand.Var w]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (hz | hz | hz) | hz
    · exact hsd.defined z hz
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_w

/-- **Spill-aware body-input step (`[spilled v, live w]`).** `StackDiscHS` drives a mixed pair emit
    (restore `v`, DUP the live `w`), preserving `venomAsmRel` and re-establishing `StackDiscHS k`. The
    `SL` case of the 2-var spill invariant matrix. -/
theorem stackDiscHS_emitInput_pair_first_spilled {opc nl v w ps lo vs as prog offv k}
    {offsetToPc : AssocList Nat Nat}
    (hvw : v ≠ w)
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hspillv : alookup' ps.spilled (Operand.Var v) = some offv)
    (hnospillw : alookup' ps.spilled (Operand.Var w) = none)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hwmem : Operand.Var w ∈ ps.stack)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length ∧
           StackDiscHS k (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' := by
  obtain ⟨d, hdepthw, hlenw⟩ := stackGetDepth_of_mem hwmem
  have hsmall : d + 2 ≤ 15 := by have := hsd.shallow; omega
  refine bodyStepS_of_sim
    (emitInputPlan_pair_spill_first_sim (offsetToPc := offsetToPc) hvw hspillv hlivev hlivew hnospillw
        hdepthw hsmall hlenw hrel hsd.spillWf hblock)
    (fun as' hmemmono => ?_)
  set ps1 : PlanState := { ps with stack := ps.stack ++ [Operand.Var v, Operand.Var v],
                                    spilled := aremove ps.spilled (Operand.Var v),
                                    alloc := freeSpillSlot offv ps.alloc } with hps1def
  have hps1stack : ps1.stack = ps.stack ++ [Operand.Var v, Operand.Var v] := by rw [hps1def]
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SORestore offv, StackOp.SODup 1], ps1) :=
    emitOneInput_var_spilled_eq hspillv hlivev
  have hdepthw1 : stackGetDepth (Operand.Var w) ps1.stack = some (d + 2) := by
    rw [hps1stack,
        show ps.stack ++ [Operand.Var v, Operand.Var v]
          = (ps.stack ++ [Operand.Var v]) ++ [Operand.Var v] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var v]) (Ne.symm hvw),
        stackGetDepth_append_ne ps.stack (Ne.symm hvw), hdepthw]; rfl
  have hnospillw1 : alookup' ps1.spilled (Operand.Var w) = none := by
    rw [hps1def]; exact aremove_lookup_none ps.spilled (Operand.Var v) (Operand.Var w) hnospillw
  have hddred : doDup (d + 2) ps1 = ([StackOp.SODup (d + 2 + 1)], { ps1 with stack := stackDup (d + 2) ps1.stack }) := by
    unfold doDup; rw [if_pos hsmall]
  have htail : emitOneInput opc nl (Operand.Var w) ps1 = ([StackOp.SODup (d + 2 + 1)], { ps1 with stack := stackDup (d + 2) ps1.stack }) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillw1, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivew, if_true, hdepthw1, hddred, List.nil_append]
  have hfold : (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 = { ps1 with stack := stackDup (d + 2) ps1.stack } := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  have hpeekw : stackPeek (d + 2) ps1.stack = Operand.Var w := stackGetDepth_peek hdepthw1
  have hdupw : stackDup (d + 2) ps1.stack = ps1.stack ++ [Operand.Var w] := by unfold stackDup; rw [hpeekw]
  rw [hfold, hdupw, hps1stack, hps1def]
  exact stackDiscHS_pair_first_spilled_preserve hsd hmemmono
    (venomAsmRel_spilled_defined hrel hspillv) (hsd.defined w hwmem)

/-- `StackDiscHS` preservation across a `[live, spilled]` mixed emit (`[v]++[w,w]`, +3 headroom). -/
theorem stackDiscHS_pair_second_spilled_preserve {k ps vs as as'} {v w : String} {offw : Nat}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hmemmono : as.memory.size ≤ as'.memory.size)
    (hdef_v : ∃ x, lookupVar v vs = some x) (hdef_w : ∃ x, lookupVar w vs = some x) :
    StackDiscHS k
      { ps with stack := ps.stack ++ [Operand.Var v] ++ [Operand.Var w, Operand.Var w],
                spilled := aremove ps.spilled (Operand.Var w),
                alloc := freeSpillSlot offw ps.alloc } vs as' := by
  refine hsd.rebuild hmemmono ?_ ?_ ?_
  · intro o off' hlook
    exact aremove_lookup_some _ (Operand.Var w) o off' hlook
  · show (ps.stack ++ [Operand.Var v] ++ [Operand.Var w, Operand.Var w]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (hz | hz) | hz | hz
    · exact hsd.defined z hz
    · injection hz with hz'; subst hz'; exact hdef_v
    · injection hz with hz'; subst hz'; exact hdef_w
    · injection hz with hz'; subst hz'; exact hdef_w

/-- **Spill-aware body-input step (`[live v, spilled w]`).** `StackDiscHS` drives a mixed pair emit
    (DUP the live `v`, restore `w`), preserving `venomAsmRel` and re-establishing `StackDiscHS k`. The
    `LS` case; completes the 2-var spill invariant matrix (with `SL`, `SS`, and `of_stackDiscH` for
    `LL`). -/
theorem stackDiscHS_emitInput_pair_second_spilled {opc nl v w ps lo vs as prog offw k}
    {offsetToPc : AssocList Nat Nat}
    (hsd : StackDiscHS (k + 3) ps vs as)
    (hnospillv : alookup' ps.spilled (Operand.Var v) = none)
    (hspillw : alookup' ps.spilled (Operand.Var w) = some offw)
    (hlivev : nl.contains v = true) (hlivew : nl.contains w = true)
    (hvmem : Operand.Var v ∈ ps.stack)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1)) :
    ∃ as', runAsm (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' ∧
           as'.pc = as.pc + (executePlan (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).1).length ∧
           StackDiscHS k (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 vs as' := by
  obtain ⟨d, hdepthv, hlenv⟩ := stackGetDepth_of_mem hvmem
  have hsmall : d ≤ 15 := by have := hsd.shallow; omega
  refine bodyStepS_of_sim
    (emitInputPlan_pair_spill_second_sim (offsetToPc := offsetToPc) hnospillv hlivev hlivew hdepthv hsmall
        hlenv hspillw hrel hsd.spillWf hblock)
    (fun as' hmemmono => ?_)
  have hpeekv : stackPeek d ps.stack = Operand.Var v := stackGetDepth_peek hdepthv
  have hdupv : stackDup d ps.stack = ps.stack ++ [Operand.Var v] := by unfold stackDup; rw [hpeekv]
  set ps1 : PlanState := { ps with stack := stackDup d ps.stack } with hps1def
  have hps1stack : ps1.stack = ps.stack ++ [Operand.Var v] := by rw [hps1def, hdupv]
  have hdd : doDup d ps = ([StackOp.SODup (d + 1)], ps1) := by rw [hps1def]; unfold doDup; rw [if_pos hsmall]
  have hhead : emitOneInput opc nl (Operand.Var v) ps = ([StackOp.SODup (d + 1)], ps1) := by
    unfold emitOneInput
    simp only [isVarOperand, hnospillv, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
      if_false, hlivev, if_true, hdepthv, hdd, List.nil_append]
  have hspillw1 : alookup' ps1.spilled (Operand.Var w) = some offw := by rw [hps1def]; exact hspillw
  set ps2 : PlanState := { ps1 with stack := ps1.stack ++ [Operand.Var w, Operand.Var w],
                                     spilled := aremove ps1.spilled (Operand.Var w),
                                     alloc := freeSpillSlot offw ps1.alloc } with hps2def
  have htail : emitOneInput opc nl (Operand.Var w) ps1 = ([StackOp.SORestore offw, StackOp.SODup 1], ps2) :=
    emitOneInput_var_spilled_eq hspillw1 hlivew
  have hfold : (emitInputPlan opc [Operand.Var v, Operand.Var w] nl ps).2 = ps2 := by
    unfold emitInputPlan
    simp only [List.foldl_cons, List.foldl_nil, hhead, htail, List.nil_append]
  rw [hfold, hps2def, hps1stack, hps1def]
  exact stackDiscHS_pair_second_spilled_preserve hsd hmemmono
    (hsd.defined v hvmem) (venomAsmRel_spilled_defined hrel hspillw)

/-- **Invariant preservation — commutative var binop.** A binop consumes one unit of headroom:
    `StackDiscH (k+1)` before ⇒ `StackDiscH k` after. The output stack is `ps.stack ++ [Var out]`
    (operands DUP'd then popped, output pushed; the live inputs stay), so length grows by one and the
    headroom drops by one (`length + (k+1) = (length+1) + k`). `noSpill` is preserved
    (`releaseDeadSpills` only removes spills; input emission only DUPs); `defined` is preserved (the
    new var `out` is valued `f wx wy`; the old vars keep their values since `out` is fresh). -/
theorem stackDisc_commBinopVar_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {vs : VenomState} {x y out : String} {wx wy : bytes32} {name : String}
    {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hwx : lookupVar x vs = some wx)
    (hwy : lookupVar y vs = some wy)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps).2
      (gvBodyStep (inst, idx) vs) := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hshallow15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hps1eq := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x'
  -- the output plan state collapses to `releaseDeadSpills nl { ps1 with stack := ps.stack ++ [out] }`
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x']
    simp only [hoptnoop]
  -- input emission preserves `spilled` (only DUPs, no restore in the no-spill regime)
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by rw [hrev, hps1eq]
  -- the body Venom step in updateVar form
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
      stepInstBase_binopVar hdispatch hops houts hwx hwy
    simp only [gvBodyStep, hstepEq]
  refine ⟨?_, ?_, ?_⟩
  · -- noSpill
    rw [hstateEq]
    apply releaseDeadSpills_noSpill
    intro op
    show alookup' (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled op = none
    rw [hps1spill]; exact hsd.noSpill op
  · -- shallow: length grows by 1, headroom drops by 1
    rw [hstateEq, releaseDeadSpills_stack]
    show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · -- defined
    rw [hstateEq, releaseDeadSpills_stack]
    intro z hz
    rw [hgv]
    show ∃ w, lookupVar z (updateVar out (f wx wy) vs) = some w
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · have hzout : z ≠ out := by rintro rfl; exact hfresh hz
      rw [lookupVar_updateVar_ne vs out z (f wx wy) hzout]
      exact hsd.defined z hz
    · injection hz with hz'
      rw [hz']
      exact ⟨f wx wy, lookupVar_updateVar_self vs out (f wx wy)⟩

/-- **Per-instruction body atom under the headroom invariant — commutative var binop.** Bundles the
    asm body step (`stackDisc_commBinopVar_bodyStep`, via `toStackDisc`) and the invariant
    preservation (`stackDisc_commBinopVar_preserve`) into the single statement an invariant-threading
    body fold iterates: from `StackDiscH (k+1)` it both simulates the asm to a `gvBodyStep`-related
    state AND re-establishes `StackDiscH k`. (`wx`/`wy` are derived once from the invariant's
    `defined`; both halves conclude on the same fixed `gvBodyStep (inst, idx) vs`.) -/
theorem stackDisc_commBinopVar_step
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs) := by
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  exact ⟨stackDisc_commBinopVar_bodyStep hsd.toStackDisc hname hcomm hdispatch hops houts hxy
           hxmem hymem hfresh hlive hlivex hlivey hdisp hoptnoop hrel hblock,
         stackDisc_commBinopVar_preserve hsd hname hcomm hdispatch hops houts hxy hxmem hymem
           hfresh hlive hlivex hlivey hwx hwy hoptnoop⟩

/-! ## Stack-as-var-list (closing the operand-membership gap)

The per-instruction step needs `Operand.Var x ∈ ps.stack` for its operands. For the fold's `∀ p`
`hstep`, that must come from the invariant. `StackIsVars S p` pins the plan stack to a concrete var
list `S` (`p.stack = S.map Var`), so operand membership reduces to `x ∈ S` — a static per-block fact
(in the no-pop regime `S` is the block inputs followed by the outputs emitted so far, so an operand is
in `S` iff it is defined earlier, i.e. SSA def-before-use). A binop appends its output: `S ↦ S ++
[out]`. -/
def StackIsVars (S : List String) (p : PlanState) : Prop :=
  p.stack = S.map Operand.Var

/-- A var in the tracked list is on the stack. -/
theorem stackIsVars_mem {S : List String} {p : PlanState} {a : String}
    (h : StackIsVars S p) (ha : a ∈ S) : Operand.Var a ∈ p.stack := by
  rw [h, List.mem_map]; exact ⟨a, ha, rfl⟩

/-- A var NOT in the tracked list is absent from the stack (operand freshness from `out ∉ S`). -/
theorem stackIsVars_not_mem {S : List String} {p : PlanState} {a : String}
    (h : StackIsVars S p) (ha : a ∉ S) : ¬ Operand.Var a ∈ p.stack := by
  rw [h, List.mem_map]; rintro ⟨b, hb, hba⟩; injection hba with hba'; exact ha (hba' ▸ hb)

/-- The tracked list's length is the stack depth (so `StackDiscH`'s `shallow` is `S.length + k ≤ 15`). -/
theorem stackIsVars_length {S : List String} {p : PlanState} (h : StackIsVars S p) :
    p.stack.length = S.length := by rw [h, List.length_map]

/-- **The well-scheduling bridge** (non-trivial stack layouts). Connects the body fold's output layout
    (`StackIsVars S ps`, where `S = S0 ++ block outputs` for the no-swap fold) to the JMP terminator
    codegen (`generateRegularInstPlan_jmp_eq`), via the **well-scheduling equality** `hsched`: the
    body's output layout `S` equals the JMP target's expected entry layout
    `inputVarsFrom curBbLabel targetBb (liveVarsAt …)`. Under it, the JMP join reorder is a no-op
    (`reorderPlan_vars_nil`) and the plan collapses to `[SOPushLabel target, SOEmit "JUMP"]`, leaving
    the plan stack at the target layout. `hsched` is the scheduler-correctness obligation (a
    `perm_reaches`-level fact) — this lemma isolates it as the *single* remaining input for a
    non-trivial (non-empty-layout) JMP block, the bare-layout case being `hsched : [] = []`. -/
theorem generateRegularInstPlan_jmp_eq_of_stackIsVars
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock} {S : List String}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hsv : StackIsVars S ps)
    (hnd : S.Nodup)
    (hsched : S = inputVarsFrom curBbLabel targetBb.instructions (liveVarsAt liveness target 0)) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], releaseDeadSpills nextLiveness ps) := by
  refine generateRegularInstPlan_jmp_eq hjmp hops houts htgt ?_ ?_
  · rw [show ps.stack = S.map Operand.Var from hsv, hsched]
  · rw [← hsched]; exact hnd

/-- **Well-scheduling bridge for a phi-free target** (the common case): when the JMP target has no
    `PHI` instructions, the scheduling equality `hsched` simplifies (`inputVarsFrom_no_phi`) to
    `S = liveVarsAt liveness target 0` — the body's output layout must equal the target's live vars at
    entry, with no phi remapping. Reduces the non-trivial JMP block's scheduler obligation to a plain
    liveness equality. -/
theorem generateRegularInstPlan_jmp_eq_of_stackIsVars_no_phi
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {target : String} {targetBb : BasicBlock} {S : List String}
    (hjmp : inst.opcode = Opcode.JMP)
    (hops : inst.operands = [Operand.Label target])
    (houts : inst.outputs = [])
    (htgt : fn.blocks.find? (·.label == target) = some targetBb)
    (hsv : StackIsVars S ps)
    (hnd : S.Nodup)
    (hnophi : collectPhis targetBb.instructions = [])
    (hsched : S = liveVarsAt liveness target 0) :
    generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps
      = ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], releaseDeadSpills nextLiveness ps) := by
  refine generateRegularInstPlan_jmp_eq_of_stackIsVars hjmp hops houts htgt hsv hnd ?_
  rw [inputVarsFrom_no_phi curBbLabel targetBb.instructions (liveVarsAt liveness target 0) hnophi]
  exact hsched

/-- The output stack of a commutative var binop (under the invariant-derivable side conditions) is
    `ps.stack ++ [Var out]` — operands DUP'd then popped, live inputs kept, output pushed. Extracted
    from the preservation reasoning so the `StackIsVars` update `S ↦ S ++ [out]` can be read off. -/
theorem genRegularInstPlan_commBinopVar_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {vs : VenomState}
    {x y out : String} {name : String}
    (hsd : StackDisc ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hshallow15 : ps.stack.length ≤ 15 := hsd.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x']
    simp only [hoptnoop]
  rw [hstateEq, releaseDeadSpills_stack]

/-- **Body step + invariant + stack-shape, all from the invariant.** The `StackIsVars`-aware step:
    operand membership (`hxmem`/`hymem`) and freshness (`hfresh`) are derived from `x, y ∈ S` and
    `out ∉ S`, and the output's `StackIsVars (S ++ [out])` is produced — so this is dischargeable
    purely from the per-block static facts (`x, y ∈ S`, `out ∉ S`) plus the headroom invariant, with
    no stateful side conditions assumed. -/
theorem stackDisc_commBinopVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨hstep, hsd'⟩ := stackDisc_commBinopVar_step hsd hname hcomm hdispatch hops houts hxy
    hxmem hymem hfresh hlive hlivex hlivey hdisp hoptnoop hrel hblock
  refine ⟨hstep, hsd', ?_⟩
  have hout := genRegularInstPlan_commBinopVar_outStack (liveness := liveness) (dfg := dfg)
    (cfg := cfg) (fn := fn) (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
    hsd.toStackDisc hname hcomm hops houts hxy hxmem hymem hlive hlivex hlivey hoptnoop
  show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
    curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
  rw [hout, hsv, List.map_append]; rfl

/-- `stepInstBase` on a binop with operands `[Var x, Lit b]`: one lookup, the literal direct.
    The mixed sibling of `stepInstBase_binopVar` / `stepInstBase_binopLit`. -/
theorem stepInstBase_binopVarLit {inst : Instruction} {vs : VenomState}
    {f : bytes32 → bytes32 → bytes32} {x : String} {b wx : bytes32} {out : String}
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hvx : lookupVar x vs = some wx) :
    stepInstBase inst vs = ExecResult.OK (updateVar out (f wx b) vs) := by
  rw [hdispatch]
  simp [execPure2, hops, houts, evalOperand, hvx]

/-- `stepInstBase` on a binop with operands `[Lit a, Var y]` — the mirror of
    `stepInstBase_binopVarLit`. -/
theorem stepInstBase_binopLitVar {inst : Instruction} {vs : VenomState}
    {f : bytes32 → bytes32 → bytes32} {y : String} {a wy : bytes32} {out : String}
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [out])
    (hvy : lookupVar y vs = some wy) :
    stepInstBase inst vs = ExecResult.OK (updateVar out (f a wy) vs) := by
  rw [hdispatch]
  simp [execPure2, hops, houts, evalOperand, hvy]

/-- `stepInstBase` on a commutative binop whose operands are BOTH literals: no lookups, the
    result is direct. The Lit sibling of `stepInstBase_binopVar`. -/
theorem stepInstBase_binopLit {inst : Instruction} {vs : VenomState}
    {f : bytes32 → bytes32 → bytes32} {a b : bytes32} {out : String}
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b])
    (houts : inst.outputs = [out]) :
    stepInstBase inst vs = ExecResult.OK (updateVar out (f a b) vs) := by
  rw [hdispatch]
  simp [execPure2, hops, houts, evalOperand]

/-- **The shared assembly of every `stackDisc_commBinop*_step_S`.** All four arms (both-literal,
    mixed `[Var,Lit]`, mixed `[Lit,Var]`, and the consuming dead-operand one) end in the same ~27
    lines: rewrite the Venom step, transport `noSpill` through `releaseDeadSpills`, bound the
    headroom, re-establish `defined`, and read off the output layout. Nothing there depends on the
    operand classes or on whether the stack grew or shrank — only on `base` (what sits below the
    output), `S'` (the layout that names it) and `w` (the value written).

    Stating it once makes the arms their genuinely distinct parts: how the operands are emitted, and
    which `stepInstBase` lemma gives the Venom step. -/
theorem stackDisc_commBinop_assemble
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as as' : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {base : List Operand} {S' : List String} {out : String} {k idx : Nat} {w : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hbaselen : base.length ≤ ps.stack.length)
    (hbasemem : ∀ o, o ∈ base → o ∈ ps.stack)
    (hbaseS : base ++ [Operand.Var out] = S'.map Operand.Var)
    (hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := base ++ [Operand.Var out] })
    (hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled)
    (hgv : gvBodyStep (inst, idx) vs = { updateVar out w vs with instIdx := idx + 1 })
    (hrun : runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (updateVar out w vs) as')
    (hpc : as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length) :
    (∃ as'', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as'' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as'' ∧
            as''.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S'
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  refine ⟨⟨as', hrun, ?_, hpc⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hgv, venomAsmRel_instIdx]; exact hrel'
  · rw [hstateEq]
    apply releaseDeadSpills_noSpill
    intro op
    show alookup' (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled op
      = none
    rw [hps1spill]; exact hsd.noSpill op
  · rw [hstateEq, releaseDeadSpills_stack]
    show (base ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · rw [hstateEq, releaseDeadSpills_stack]
    intro z hz
    rw [hgv]
    show ∃ u, lookupVar z (updateVar out w vs) = some u
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · have hzmem : Operand.Var z ∈ ps.stack := hbasemem _ hz
      have hzout : z ≠ out := by rintro rfl; exact hfresh hzmem
      rw [lookupVar_updateVar_ne vs out z w hzout]
      exact hsd.defined z hzmem
    · injection hz with hz'
      rw [hz']
      exact ⟨w, lookupVar_updateVar_self vs out w⟩
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S'.map Operand.Var
    rw [hstateEq, releaseDeadSpills_stack]; exact hbaseS

/-- **Body step + invariant + stack-shape — commutative binop, both operands LITERAL.** The Lit
    sibling of `stackDisc_commBinopVar_step_S`, and the first literal-operand member of the
    `stackDisc_*_step` family (everything before it bound `Operand.Var` only). The plan is
    `PUSH b ; PUSH a ; OP`: no DUPs, no stack-var interaction, so the operands need NO `∈ S`
    membership and NO liveness side conditions — only the output's freshness (`out ∉ S`) and
    liveness matter. The asm sim is the already-existing `genRegularInstPlan_commBinopLit_sim`;
    what this adds is the `StackDiscH` threading (headroom `k+1 → k`: the plan stack grows by
    exactly the one `Var out`) and the `StackIsVars (S ++ [out])` output the body fold
    iterates on. -/
theorem stackDisc_commBinopLit_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {a b : bytes32} {out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Lit a, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hab : a ≠ b)
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := by
    have := hsd.noSpill (Operand.Var out); simpa [alookup'] using this
  have hrev : inst.operands.reverse = [Operand.Lit b, Operand.Lit a] := by rw [hops]; rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopLit_eq hname hcomm hops houts hab rfl hlive]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by rw [hrev, emitInputPlan_pair_lit_eq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f a b) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, stepInstBase_binopLit hdispatch hops houts]
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopLit_sim hname hcomm hops houts hab
    rfl hlive hfresh hspill hdisp hoptnoop hrel hblock
  exact stackDisc_commBinop_assemble hsd hfresh le_rfl (fun _ h => h)
    (by rw [show ps.stack = S.map Operand.Var from hsv, List.map_append]; rfl)
    hstateEq hps1spill hgv hrun hrel' hpc

/-- **Body step + invariant + stack-shape — commutative binop, MIXED `[Var x, Lit b]` operands**
    (`OP %x, b`). The mixed sibling of `stackDisc_commBinopVar_step_S` (both operands vars) and
    `stackDisc_commBinopLit_step_S` (both literals), completing the commutative binop's operand
    classes at the fold's per-instruction layer.

    The plan is `PUSH b ; DUP(d+1) ; OP`. The one genuinely new obligation versus either sibling is
    the **depth shift across the `PUSH`**: `x`'s depth is needed in `ps.stack ++ [Lit b]`, not in
    `ps.stack`, and it is derived here from `x ∈ S` via `stackGetDepth_append_lit`. Everything else
    is the shared skeleton: operand membership and output freshness come from `x ∈ S` / `out ∉ S`,
    the headroom invariant supplies `d + 1 ≤ 15`, and the output extends `S ↦ S ++ [out]`. -/
theorem stackDisc_commBinopVarLit_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x : String} {b : bytes32} {out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Lit b])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := by
    have := hsd.noSpill (Operand.Var out); simpa [alookup'] using this
  obtain ⟨d, hdepth0, hlen0⟩ := stackGetDepth_of_mem hxmem
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  -- the depth shift across the `PUSH b` — the mixed case's one new obligation
  have hdepth : stackGetDepth (Operand.Var x) (ps.stack ++ [Operand.Lit b]) = some (d + 1) := by
    rw [stackGetDepth_append_lit ps.stack b, hdepth0]; rfl
  have hsmall : d + 1 ≤ 15 := by have := hsd.shallow; omega
  have hlen : d + 1 < (ps.stack ++ [Operand.Lit b]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hrev : inst.operands.reverse = [Operand.Lit b, Operand.Var x] := by rw [hops]; rfl
  have hemitstack :
      (emitInputPlan inst.opcode [Operand.Lit b, Operand.Var x] nextLiveness ps).2.stack
        = ps.stack ++ [Operand.Lit b, Operand.Var x] := by
    rw [emitInputPlan_pair_litVar_eq (hsd.noSpill _) hlivex hdepth hsmall]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopPair_eq hname hcomm hops houts (by simp) hlive hemitstack]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by
    rw [hrev, emitInputPlan_pair_litVar_eq (hsd.noSpill _) hlivex hdepth hsmall]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx b) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, stepInstBase_binopVarLit hdispatch hops houts hwx]
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopVarLit_sim hname hcomm hops houts
    hox rfl hlive hfresh hspill (hsd.noSpill _) hlivex hdepth hsmall hlen hwx hdisp hoptnoop
    hrel hblock
  exact stackDisc_commBinop_assemble hsd hfresh le_rfl (fun _ h => h)
    (by rw [show ps.stack = S.map Operand.Var from hsv, List.map_append]; rfl)
    hstateEq hps1spill hgv hrun hrel' hpc

/-- **Body step + invariant + stack-shape — commutative binop, both operands DEAD (consuming).**

    Every `stackDisc_*_step_S` above is in the **duplicating** regime: the operands stay live, the
    generator DUPs them, and the stack grows by one (`S ↦ S ++ [out]`). This is the **consuming**
    regime — both operands' last use is this instruction, so nothing is emitted for them and the
    opcode eats them off the stack: `S = base ++ [y, x] ↦ base ++ [out]`, one **shorter**.

    That shrink is why this cannot yet feed `BodyStep`, whose conclusion hardcodes
    `StackIsVars (S ++ [outOf x])`; lifting the fold's S-threading is the next step. Everything
    below it composes unchanged — the plan/sim layer is `genRegularInstPlan_commBinopDead_sim`,
    itself a thin instance of the operand-class-agnostic `..._commBinopPair_sim`.

    Headroom is free and slack: from `StackDiscH (k+1)` the shorter stack satisfies `StackDiscH k`
    immediately, so the arm keeps the same `(k+1) → k` shape the fold uses. -/
theorem stackDisc_commBinopDead_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {base : List String} {x y out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars (base ++ [y, x]) ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (houtS : out ∉ base ++ [y, x])
    (hlive : nextLiveness.contains out = true)
    (hdead_x : nextLiveness.contains x = false)
    (hdead_y : nextLiveness.contains y = false)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base.map Operand.Var ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base.map Operand.Var ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (base ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hstack : ps.stack = base.map Operand.Var ++ [Operand.Var y, Operand.Var x] := by
    rw [show ps.stack = (base ++ [y, x]).map Operand.Var from hsv, List.map_append]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := by rw [hstack]; simp
  have hymem : Operand.Var y ∈ ps.stack := by rw [hstack]; simp
  have hfreshS : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hfresh : ¬ (Operand.Var out) ∈ base.map Operand.Var := by
    intro h; exact hfreshS (by rw [hstack]; exact List.mem_append_left _ h)
  have hox : out ≠ x := by rintro rfl; exact hfreshS hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfreshS hymem
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := by
    have := hsd.noSpill (Operand.Var out); simpa [alookup'] using this
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hemit := emitInputPlan_pair_dead_eq (opc := inst.opcode) (nl := nextLiveness)
    (hsd.noSpill _) hdead_y (hsd.noSpill _) hdead_x
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := base.map Operand.Var ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopPair_eq hname hcomm hops houts
          (fun h => hxy (Operand.Var.inj h)) hlive (by rw [hemit]; exact hstack)]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by rw [hrev, hemit]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, stepInstBase_binopVar hdispatch hops houts hwx hwy]
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopDead_sim hname hcomm hops houts
    hxy hox hoy hstack hlive hfresh hspill (hsd.noSpill _) hdead_y (hsd.noSpill _) hdead_x
    hwx hwy hdisp hoptnoop hrel hblock
  refine stackDisc_commBinop_assemble hsd hfreshS ?_ ?_ (by simp [List.map_append]) hstateEq
    hps1spill hgv hrun hrel' hpc
  · have hlen : ps.stack.length = base.length + 2 := by rw [hstack]; simp
    simp only [List.length_map]; omega
  · intro o ho; rw [hstack]; exact List.mem_append_left _ ho

/-- **Body step — commutative binop, both operands DEAD, in the MIRROR order** (`base ++ [x, y]`,
    `y` on top). This is the order the generator emits bare for a consuming op (`deadTopFn`), so it
    is the arm a whole-function consuming capstone actually needs. The asm computes `f wy wx` where
    Venom computes `f wx wy`, bridged by `hfcomm` — commutativity of `f` *as a function*, which is
    why this is its own arm rather than an instance of `stackDisc_commBinopDead_step_S`. -/
theorem stackDisc_commBinopDeadMirror_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {base : List String} {x y out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars (base ++ [x, y]) ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hfcomm : ∀ (a b : bytes32), f a b = f b a)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (houtS : out ∉ base ++ [x, y])
    (hlive : nextLiveness.contains out = true)
    (hdead_x : nextLiveness.contains x = false)
    (hdead_y : nextLiveness.contains y = false)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := base.map Operand.Var ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := base.map Operand.Var ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (base ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hstack : ps.stack = base.map Operand.Var ++ [Operand.Var x, Operand.Var y] := by
    rw [show ps.stack = (base ++ [x, y]).map Operand.Var from hsv, List.map_append]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := by rw [hstack]; simp
  have hymem : Operand.Var y ∈ ps.stack := by rw [hstack]; simp
  have hfreshS : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hfresh : ¬ (Operand.Var out) ∈ base.map Operand.Var := by
    intro h; exact hfreshS (by rw [hstack]; exact List.mem_append_left _ h)
  have hox : out ≠ x := by rintro rfl; exact hfreshS hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfreshS hymem
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := by
    have := hsd.noSpill (Operand.Var out); simpa [alookup'] using this
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hemit := emitInputPlan_pair_dead_eq (opc := inst.opcode) (nl := nextLiveness)
    (hsd.noSpill _) hdead_y (hsd.noSpill _) hdead_x
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := base.map Operand.Var ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopPairMirror_eq hname hcomm hops houts
          (fun h => hxy (Operand.Var.inj h)) hlive (by rw [hemit]; exact hstack)]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by rw [hrev, hemit]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, stepInstBase_binopVar hdispatch hops houts hwx hwy]
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopDeadMirror_sim hname hcomm hops houts
    hxy hox hoy (hfcomm wx wy) hstack hlive hfresh hspill (hsd.noSpill _) hdead_y (hsd.noSpill _)
    hdead_x hwx hwy hdisp hoptnoop hrel hblock
  refine stackDisc_commBinop_assemble hsd hfreshS ?_ ?_ (by simp [List.map_append]) hstateEq
    hps1spill hgv hrun hrel' hpc
  · have hlen : ps.stack.length = base.length + 2 := by rw [hstack]; simp
    simp only [List.length_map]; omega
  · intro o ho; rw [hstack]; exact List.mem_append_left _ ho

/-- **Body step + invariant + stack-shape — commutative binop, MIXED `[Lit a, Var y]` operands**
    (`OP a, %y`) — the mirror of `stackDisc_commBinopVarLit_step_S`. The plan is
    `DUP(d+1) ; PUSH a ; OP`: the var is emitted first, so its depth is read off `ps.stack`
    directly and no depth shift is needed. -/
theorem stackDisc_commBinopLitVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {y : String} {a : bytes32} {out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [out])
    (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := by
    have := hsd.noSpill (Operand.Var out); simpa [alookup'] using this
  obtain ⟨d, hdepth, hlen⟩ := stackGetDepth_of_mem hymem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hsmall : d ≤ 15 := by have := hsd.shallow; omega
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Lit a] := by rw [hops]; rfl
  have hemitstack :
      (emitInputPlan inst.opcode [Operand.Var y, Operand.Lit a] nextLiveness ps).2.stack
        = ps.stack ++ [Operand.Var y, Operand.Lit a] := by
    rw [emitInputPlan_pair_varLit_eq (hsd.noSpill _) hlivey hdepth hsmall]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_commBinopPair_eq hname hcomm hops houts (by simp) hlive hemitstack]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by
    rw [hrev, emitInputPlan_pair_varLit_eq (hsd.noSpill _) hlivey hdepth hsmall]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f a wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, stepInstBase_binopLitVar hdispatch hops houts hwy]
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopLitVar_sim hname hcomm hops houts
    hoy rfl hlive hfresh hspill (hsd.noSpill _) hlivey hdepth hsmall hlen hwy hdisp hoptnoop
    hrel hblock
  exact stackDisc_commBinop_assemble hsd hfresh le_rfl (fun _ h => h)
    (by rw [show ps.stack = S.map Operand.Var from hsv, List.map_append]; rfl)
    hstateEq hps1spill hgv hrun hrel' hpc


/-! ## Non-commutative var-binop body atoms (SUB/DIV/MOD/LT/GT/SHL/…)

The non-commutative counterparts of the commutative var-binop body atoms. A non-comm binop has the
same plan shape (two DUPs, pop 2, push 1 — net `+1`), so the headroom accounting and depth bounds are
identical to the commutative case; the only difference is the generator takes the
`computeOperands = reverse` path with no cheaper-order dispatch (`isCommutative = false`), threaded by
`hncomm`/`hnjmp`/`hcompute`. This covers SUB, DIV, MOD, SDIV, SMOD, EXP, LT, GT, SLT, SGT, SHL, SHR,
SAR — the majority of arithmetic/comparison opcodes. -/

/-- **Body step from the invariant — non-commutative var binop.** The non-comm counterpart of
    `stackDisc_commBinopVar_bodyStep` (uses `genRegularInstPlan_nonCommBinopVar_sim`). -/
theorem stackDisc_nonCommBinopVar_bodyStep
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y out : String} {name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDisc ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by
    unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by have := hsd.shallow; omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hsim := genRegularInstPlan_nonCommBinopVar_sim (d_x' := d_x + 1)
    hname hncomm hnjmp hcompute hops houts hxy hox hoy rfl hlive hfresh (hsd.noSpill _)
    (hsd.noSpill _) hlivey hdepth_y hsmall_y hleny (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx'
    hwx hwy hdisp hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  exact gvBodyStep_of_updateVar (idx := idx) hstepEq hsim

/-- The output stack of a non-commutative var binop is `ps.stack ++ [Var out]`. The non-comm
    counterpart of `genRegularInstPlan_commBinopVar_outStack`. -/
theorem genRegularInstPlan_nonCommBinopVar_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {vs : VenomState}
    {x y out : String} {name : String}
    (hsd : StackDisc ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hsmall_y : d_y ≤ 15 := by have := hsd.shallow; omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by have := hsd.shallow; omega
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x']
    simp only [hoptnoop]
  rw [hstateEq, releaseDeadSpills_stack]

/-- **Value-generic 2-input/1-output headroom preserve.** Freed from the binop `f`: the pushed value
    `val` is abstract (from `hstepEq`), so both the non-commutative binops (`val = f wx wy`) and SHA3
    (`val = keccak` of a memory slice) reuse it. -/
theorem stackDisc_binop2_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {vs : VenomState} {x y out : String} {name : String}
    {k idx : Nat} {val : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out val vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps).2
      (gvBodyStep (inst, idx) vs) := by
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hshallow15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hps1eq := emitInputPlan_pair_var_eq (opc := inst.opcode) (nl := nextLiveness)
    (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x'
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x']
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by rw [hrev, hps1eq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out val vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hstateEq]
    apply releaseDeadSpills_noSpill
    intro op
    show alookup' (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled op = none
    rw [hps1spill]; exact hsd.noSpill op
  · rw [hstateEq, releaseDeadSpills_stack]
    show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · rw [hstateEq, releaseDeadSpills_stack]
    intro z hz
    rw [hgv]
    show ∃ w, lookupVar z (updateVar out val vs) = some w
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · have hzout : z ≠ out := by rintro rfl; exact hfresh hz
      rw [lookupVar_updateVar_ne vs out z val hzout]
      exact hsd.defined z hz
    · injection hz with hz'
      rw [hz']
      exact ⟨val, lookupVar_updateVar_self vs out val⟩

/-- **Body step + invariant + stack-shape, all from the invariant — non-commutative var binop.** The
    `StackIsVars`-aware step for SUB/DIV/MOD/LT/GT/SHL/…; the non-comm counterpart of
    `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_nonCommBinopVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  refine ⟨stackDisc_nonCommBinopVar_bodyStep hsd.toStackDisc hname hncomm hnjmp hcompute hdispatch
            hops houts hxy hxmem hymem hfresh hlive hlivex hlivey hdisp hoptnoop hrel hblock,
          stackDisc_binop2_preserve hsd hname hncomm hnjmp hcompute hops houts hxy
            hxmem hymem hfresh hlive hlivex hlivey hstepEq hoptnoop, ?_⟩
  have hout := genRegularInstPlan_nonCommBinopVar_outStack (liveness := liveness) (dfg := dfg)
    (cfg := cfg) (fn := fn) (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
    hsd.toStackDisc hname hncomm hnjmp hcompute hops houts hxy hxmem hymem hlive hlivex hlivey hoptnoop
  show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
    curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
  rw [hout, hsv, List.map_append]; rfl

/-! ## Ternary var-opcode body atoms (ADDMOD/MULMOD)

The 3-input counterparts of the commutative var-binop body atoms. A ternary op is also net `+1` on
the plan stack (three DUPs, pop 3, push 1), so the headroom accounting `StackDiscH (k+1) ⇒
StackDiscH k` is identical. The one difference: the third (deepest) input DUP reaches depth `d_x + 2`
(vs the binop's `d_x + 1`), so the body step needs `StackDiscH 1` (length ≤ 14) rather than plain
`StackDisc` (length ≤ 15) — and `StackDiscH (k+1)` (k ≥ 0) always supplies that. -/

/-- Build the `emitDepthsOk` chain for distinct live vars over any `base` from a length bound: each
    `eᵢ` sits at depth `orig(eᵢ) + i` on the stack grown by the prior DUPs, so with
    `base.length + es.length ≤ 17` every depth stays `≤ 15`. The arbitrary-arity generalisation of the
    depth-shift chain inside `stackDisc_ternopVar_depths`. -/
theorem emitDepthsOk_of_bounds {nl : List String} :
    ∀ (es : List String) (base : List Operand),
      base.length + es.length ≤ 17 →
      es.Nodup →
      (∀ v ∈ es, Operand.Var v ∈ base) →
      (∀ v ∈ es, nl.contains v = true) →
      ∃ dists, emitDepthsOk nl es dists base := by
  intro es
  induction es with
  | nil => intro base _ _ _ _; exact ⟨[], trivial⟩
  | cons e es' ih =>
    intro base hbound hnd hmem hlive
    obtain ⟨d_e, hdepth_e, hlen_e⟩ := stackGetDepth_of_mem (hmem e List.mem_cons_self)
    have hd_e15 : d_e ≤ 15 := by
      simp only [List.length_cons] at hbound; omega
    obtain ⟨dists', hrec⟩ := ih (base ++ [Operand.Var e])
      (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
      (List.nodup_cons.mp hnd).2
      (fun v hv => List.mem_append_left _ (hmem v (List.mem_cons_of_mem _ hv)))
      (fun v hv => hlive v (List.mem_cons_of_mem _ hv))
    exact ⟨d_e :: dists', hlive e List.mem_cons_self, hdepth_e, hd_e15, hrec⟩

/-- **The `emitDepthsOk` chain from `StackDiscH`** for an N-input all-variable op: distinct live vars,
    all present, with headroom `StackDiscH (es.length - 2)` (for LOG with `n` topics, that is
    `StackDiscH n`). The arbitrary-arity generalisation of `stackDisc_ternopVar_depths`, feeding the
    N-input emission lemmas. -/
theorem stackDisc_nVar_depths {ps : PlanState} {vs : VenomState} {nl : List String} (es : List String)
    (hsd : StackDiscH (es.length - 2) ps vs)
    (hnd : es.Nodup)
    (hmem : ∀ v ∈ es, Operand.Var v ∈ ps.stack)
    (hlive : ∀ v ∈ es, nl.contains v = true) :
    ∃ dists, emitDepthsOk nl es dists ps.stack := by
  apply emitDepthsOk_of_bounds es ps.stack _ hnd hmem hlive
  have := hsd.shallow
  omega

/-- The three input depths of a ternary var op, computed from membership + headroom, with the
    chained depth-shift facts the input plan (`emitInputPlan_triple_var_eq`) consumes. Shared by the
    body step, preservation and out-stack lemmas. -/
theorem stackDisc_ternopVar_depths {ps : PlanState} {vs : VenomState} {x y z : String}
    (hsd : StackDiscH 1 ps vs)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxmem : Operand.Var x ∈ ps.stack) (hymem : Operand.Var y ∈ ps.stack)
    (hzmem : Operand.Var z ∈ ps.stack) :
    ∃ d_z d_y d_x,
      stackGetDepth (Operand.Var z) ps.stack = some d_z ∧ d_z ≤ 15 ∧ d_z < ps.stack.length ∧
      stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some (d_y + 1) ∧ d_y + 1 ≤ 15 ∧
        d_y + 1 < (stackDup d_z ps.stack).length ∧
      stackGetDepth (Operand.Var x) (stackDup (d_y + 1) (stackDup d_z ps.stack)) = some (d_x + 2) ∧
        d_x + 2 ≤ 15 ∧ d_x + 2 < (stackDup (d_y + 1) (stackDup d_z ps.stack)).length := by
  have hshallow : ps.stack.length ≤ 14 := by have := hsd.shallow; omega
  obtain ⟨d_z, hdepth_z, hlenz⟩ := stackGetDepth_of_mem hzmem
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have hpeekZ : stackPeek d_z ps.stack = Operand.Var z := stackGetDepth_peek hdepth_z
  have hdupZ : stackDup d_z ps.stack = ps.stack ++ [Operand.Var z] := by unfold stackDup; rw [hpeekZ]
  have hdepth_y' : stackGetDepth (Operand.Var y) (stackDup d_z ps.stack) = some (d_y + 1) := by
    rw [hdupZ, stackGetDepth_append_ne ps.stack hyz, hdepth_y]; rfl
  have hsy : stackDup (d_y + 1) (stackDup d_z ps.stack)
      = ps.stack ++ [Operand.Var z, Operand.Var y] := by
    rw [hdupZ]
    have hpy : stackPeek (d_y + 1) (ps.stack ++ [Operand.Var z]) = Operand.Var y := by
      rw [← hdupZ]; exact stackGetDepth_peek hdepth_y'
    unfold stackDup; rw [hpy]; simp
  have hdepth_x'' : stackGetDepth (Operand.Var x) (stackDup (d_y + 1) (stackDup d_z ps.stack))
      = some (d_x + 2) := by
    rw [hsy, show ps.stack ++ [Operand.Var z, Operand.Var y]
          = (ps.stack ++ [Operand.Var z]) ++ [Operand.Var y] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var z]) hxy,
        stackGetDepth_append_ne ps.stack hxz, hdepth_x]; rfl
  refine ⟨d_z, d_y, d_x, hdepth_z, by omega, hlenz, hdepth_y', by omega, ?_, hdepth_x'', by omega, ?_⟩
  · rw [hdupZ]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [hsy]; simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **4-input depth derivation.** The quad counterpart of `stackDisc_ternopVar_depths`; derives the four
    DUP depths (on the growing dup-chain) from `StackDiscH 2` — the deepest input (`a`, first operand,
    emitted last) reaches `original_depth + 3`, so headroom 2 (`length ≤ 13`) is needed. -/
theorem stackDisc_quadVar_depths {ps : PlanState} {vs : VenomState} {a b c d : String}
    (hsd : StackDiscH 2 ps vs)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hamem : Operand.Var a ∈ ps.stack) (hbmem : Operand.Var b ∈ ps.stack)
    (hcmem : Operand.Var c ∈ ps.stack) (hdmem : Operand.Var d ∈ ps.stack) :
    ∃ d_d d_c d_b d_a,
      stackGetDepth (Operand.Var d) ps.stack = some d_d ∧ d_d ≤ 15 ∧ d_d < ps.stack.length ∧
      stackGetDepth (Operand.Var c) (stackDup d_d ps.stack) = some (d_c + 1) ∧ d_c + 1 ≤ 15 ∧
        d_c + 1 < (stackDup d_d ps.stack).length ∧
      stackGetDepth (Operand.Var b) (stackDup (d_c + 1) (stackDup d_d ps.stack)) = some (d_b + 2) ∧
        d_b + 2 ≤ 15 ∧ d_b + 2 < (stackDup (d_c + 1) (stackDup d_d ps.stack)).length ∧
      stackGetDepth (Operand.Var a) (stackDup (d_b + 2) (stackDup (d_c + 1) (stackDup d_d ps.stack))) = some (d_a + 3) ∧
        d_a + 3 ≤ 15 ∧ d_a + 3 < (stackDup (d_b + 2) (stackDup (d_c + 1) (stackDup d_d ps.stack))).length := by
  have hshallow : ps.stack.length ≤ 13 := by have := hsd.shallow; omega
  obtain ⟨d_d, hdepth_d, hlend⟩ := stackGetDepth_of_mem hdmem
  obtain ⟨d_c, hdepth_c, hlenc⟩ := stackGetDepth_of_mem hcmem
  obtain ⟨d_b, hdepth_b, hlenb⟩ := stackGetDepth_of_mem hbmem
  obtain ⟨d_a, hdepth_a, hlena⟩ := stackGetDepth_of_mem hamem
  have hpeekD : stackPeek d_d ps.stack = Operand.Var d := stackGetDepth_peek hdepth_d
  have hdupD : stackDup d_d ps.stack = ps.stack ++ [Operand.Var d] := by unfold stackDup; rw [hpeekD]
  have hdepth_c' : stackGetDepth (Operand.Var c) (stackDup d_d ps.stack) = some (d_c + 1) := by
    rw [hdupD, stackGetDepth_append_ne ps.stack hcd, hdepth_c]; rfl
  have hsy : stackDup (d_c + 1) (stackDup d_d ps.stack)
      = ps.stack ++ [Operand.Var d, Operand.Var c] := by
    rw [hdupD]
    have hpc : stackPeek (d_c + 1) (ps.stack ++ [Operand.Var d]) = Operand.Var c := by
      rw [← hdupD]; exact stackGetDepth_peek hdepth_c'
    unfold stackDup; rw [hpc]; simp
  have hdepth_b'' : stackGetDepth (Operand.Var b) (stackDup (d_c + 1) (stackDup d_d ps.stack))
      = some (d_b + 2) := by
    rw [hsy, show ps.stack ++ [Operand.Var d, Operand.Var c]
          = (ps.stack ++ [Operand.Var d]) ++ [Operand.Var c] from by simp,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var d]) hbc,
        stackGetDepth_append_ne ps.stack hbd, hdepth_b]; rfl
  have hsz : stackDup (d_b + 2) (stackDup (d_c + 1) (stackDup d_d ps.stack))
      = ps.stack ++ [Operand.Var d, Operand.Var c, Operand.Var b] := by
    rw [hsy]
    have hpb : stackPeek (d_b + 2) (ps.stack ++ [Operand.Var d, Operand.Var c]) = Operand.Var b := by
      rw [← hsy]; exact stackGetDepth_peek hdepth_b''
    unfold stackDup; rw [hpb]; simp
  have hdepth_a''' : stackGetDepth (Operand.Var a)
      (stackDup (d_b + 2) (stackDup (d_c + 1) (stackDup d_d ps.stack))) = some (d_a + 3) := by
    rw [hsz, show ps.stack ++ [Operand.Var d, Operand.Var c, Operand.Var b]
          = ((ps.stack ++ [Operand.Var d]) ++ [Operand.Var c]) ++ [Operand.Var b] from by simp,
        stackGetDepth_append_ne ((ps.stack ++ [Operand.Var d]) ++ [Operand.Var c]) hab,
        stackGetDepth_append_ne (ps.stack ++ [Operand.Var d]) hac,
        stackGetDepth_append_ne ps.stack had, hdepth_a]; rfl
  refine ⟨d_d, d_c, d_b, d_a,
    hdepth_d, by omega, hlend,
    hdepth_c', by omega, ?_,
    hdepth_b'', by omega, ?_,
    hdepth_a''', by omega, ?_⟩
  · rw [hdupD]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [hsy]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [hsz]; simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **Body step from the invariant — ternary var opcode.** The 3-input counterpart of
    `stackDisc_commBinopVar_bodyStep`; needs `StackDiscH 1` (length ≤ 14) for the deepest input DUP. -/
theorem stackDisc_ternopVar_bodyStep
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {x y z out : String} {name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH 1 ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hzmem : Operand.Var z ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'',
    hsmall_x, hlenx''⟩ := stackDisc_ternopVar_depths hsd hxy hyz hxz hxmem hymem hzmem
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wz, hwz⟩ := hsd.defined z hzmem
  have hox : out ≠ x := by rintro rfl; exact hfresh hxmem
  have hoy : out ≠ y := by rintro rfl; exact hfresh hymem
  have hoz : out ≠ z := by rintro rfl; exact hfresh hzmem
  have hsim := genRegularInstPlan_ternopVar_sim (d_z := d_z) (d_y' := d_y + 1) (d_x'' := d_x + 2)
    hname hncomm hnjmp hcompute hops houts hxy hyz hxz hox hoy hoz rfl hlive hfresh (hsd.noSpill _)
    (hsd.noSpill _) hlivez hdepth_z hsmall_z hlenz (hsd.noSpill _) hlivey hdepth_y' hsmall_y hleny'
    (hsd.noSpill _) hlivex hdepth_x'' hsmall_x hlenx'' hwx hwy hwz hdisp hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) :=
    stepInstBase_3opVar hdispatch hops houts hwx hwy hwz
  exact gvBodyStep_of_updateVar (idx := idx) hstepEq hsim

/-- The output stack of a ternary var op is `ps.stack ++ [Var out]` (operands DUP'd then popped,
    live inputs kept, output pushed). The 3-input counterpart of
    `genRegularInstPlan_commBinopVar_outStack`. -/
theorem genRegularInstPlan_ternopVar_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {vs : VenomState}
    {x y z out : String} {name : String}
    (hsd : StackDiscH 1 ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hzmem : Operand.Var z ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'',
    hsmall_x, hlenx''⟩ := stackDisc_ternopVar_depths hsd hxy hyz hxz hxmem hymem hzmem
  rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz rfl hlive
      (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey hdepth_y' hsmall_y
      (hsd.noSpill _) hlivex hdepth_x'' hsmall_x,
    hoptnoop]
  rw [releaseDeadSpills_stack]

/-- **Invariant preservation — ternary var opcode.** `StackDiscH (k+1)` before ⇒ `StackDiscH k`
    after. Same `+1`-net headroom drop as the binop; the 3-input counterpart of
    `stackDisc_commBinopVar_preserve`. -/
theorem stackDisc_ternopVar_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {vs : VenomState} {x y z out : String} {wx wy wz : bytes32} {name : String}
    {k idx : Nat} {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxmem : Operand.Var x ∈ ps.stack)
    (hymem : Operand.Var y ∈ ps.stack)
    (hzmem : Operand.Var z ∈ ps.stack)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hwx : lookupVar x vs = some wx)
    (hwy : lookupVar y vs = some wy)
    (hwz : lookupVar z vs = some wz)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k
      (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
        curBbLabel ps).2
      (gvBodyStep (inst, idx) vs) := by
  have hsd1 : StackDiscH 1 ps vs := ⟨hsd.noSpill, by have := hsd.shallow; omega, hsd.defined⟩
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'',
    hsmall_x, hlenx''⟩ := stackDisc_ternopVar_depths hsd1 hxy hyz hxz hxmem hymem hzmem
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz rfl hlive
        (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey hdepth_y' hsmall_y
        (hsd.noSpill _) hlivex hdepth_x'' hsmall_x]
    simp only [hoptnoop]
  have hps1spill : (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled
      = ps.spilled := by
    rw [hrev, emitInputPlan_triple_var_eq (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _)
      hlivey hdepth_y' hsmall_y (hsd.noSpill _) hlivex hdepth_x'' hsmall_x]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy wz) vs with instIdx := idx + 1 } := by
    have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) :=
      stepInstBase_3opVar hdispatch hops houts hwx hwy hwz
    simp only [gvBodyStep, hstepEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hstateEq]
    apply releaseDeadSpills_noSpill
    intro op
    show alookup' (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled op = none
    rw [hps1spill]; exact hsd.noSpill op
  · rw [hstateEq, releaseDeadSpills_stack]
    show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · rw [hstateEq, releaseDeadSpills_stack]
    intro w hw
    rw [hgv]
    show ∃ ww, lookupVar w (updateVar out (f wx wy wz) vs) = some ww
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · have hwout : w ≠ out := by rintro rfl; exact hfresh hw
      rw [lookupVar_updateVar_ne vs out w (f wx wy wz) hwout]
      exact hsd.defined w hw
    · injection hw with hw'
      rw [hw']
      exact ⟨f wx wy wz, lookupVar_updateVar_self vs out (f wx wy wz)⟩

/-- **Body step + invariant + stack-shape, all from the invariant — ternary var opcode.** The
    `StackIsVars`-aware step for ADDMOD/MULMOD: operand membership/freshness come from `x,y,z ∈ S`
    and `out ∉ S`, and `StackIsVars (S ++ [out])` is produced. The 3-input counterpart of
    `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_ternopVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y z out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
              = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2
        (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hzmem : Operand.Var z ∈ ps.stack := stackIsVars_mem hsv hzS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hsd1 : StackDiscH 1 ps vs := ⟨hsd.noSpill, by have := hsd.shallow; omega, hsd.defined⟩
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  obtain ⟨wz, hwz⟩ := hsd.defined z hzmem
  refine ⟨stackDisc_ternopVar_bodyStep hsd1 hname hncomm hnjmp hcompute hdispatch hops houts hxy hyz
            hxz hxmem hymem hzmem hfresh hlive hlivex hlivey hlivez hdisp hoptnoop hrel hblock,
          stackDisc_ternopVar_preserve hsd hname hncomm hnjmp hcompute hdispatch hops houts hxy hyz
            hxz hxmem hymem hzmem hfresh hlive hlivex hlivey hlivez hwx hwy hwz hoptnoop, ?_⟩
  have hout := genRegularInstPlan_ternopVar_outStack (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
    hsd1 hname hncomm hnjmp hcompute hops houts hxy hyz hxz hxmem hymem hzmem hlive hlivex hlivey
    hlivez hoptnoop
  show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
    curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
  rw [hout, hsv, List.map_append]; rfl

end EvmYul.Venom.Hol.Codegen

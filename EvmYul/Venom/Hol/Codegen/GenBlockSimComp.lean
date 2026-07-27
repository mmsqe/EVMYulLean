/-
Block simulation composition — the assembly layer toward `genBlockSimulation`

`genBlockSimulation` runs the resolved block plan `JUMPDEST :: cleanOps ++ instOps` and must match
the Venom `runBlock`. Its proof composes, over the resolved program:

    leading JUMPDEST (soLabel_sim)  →  body fold (per-inst sims via foldl_inst_sim)  →  terminator

This file builds the reusable *sequencing layer* that glues those segments together at the `runAsm`
level: `runAsm_add_ok` continues a run past a successful prefix, and `runAsm_seq_{halt,revert,fault}`
attach a terminal step (STOP / REVERT / INVALID — the three non-OK `genBlockSimulation` arms) after
an OK body run. The general body-fold composition (`foldl_inst_sim` over `generateBlockPlan`'s
`instOps`, threaded against `execBlock`) is the remaining core and will land here on top of these.

These were validated end-to-end in `GenBlockSimExample` (STOP / ADD;STOP / cross-block JMP).
-/

import EvmYul.Venom.Hol.Codegen.GenInstSim
import EvmYul.Venom.Hol.Codegen.AsmResolveProofs

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
    exact ⟨"out of fuel", rfl⟩
  | cons inst rest ih =>
    intro start fuel s sEnd hidx hsplit hnonterm hthread hfuel
    cases fuel with
    | zero => exact ⟨"out of fuel", rfl⟩
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

/-- **Invariant preservation — non-commutative var binop.** `StackDiscH (k+1)` ⇒ `StackDiscH k`. The
    non-comm counterpart of `stackDisc_commBinopVar_preserve`. -/
theorem stackDisc_nonCommBinopVar_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    {vs : VenomState} {x y out : String} {wx wy : bytes32} {name : String}
    {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
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
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
      stepInstBase_binopVar hdispatch hops houts hwx hwy
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
    show ∃ w, lookupVar z (updateVar out (f wx wy) vs) = some w
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · have hzout : z ≠ out := by rintro rfl; exact hfresh hz
      rw [lookupVar_updateVar_ne vs out z (f wx wy) hzout]
      exact hsd.defined z hz
    · injection hz with hz'
      rw [hz']
      exact ⟨f wx wy, lookupVar_updateVar_self vs out (f wx wy)⟩

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
  refine ⟨stackDisc_nonCommBinopVar_bodyStep hsd.toStackDisc hname hncomm hnjmp hcompute hdispatch
            hops houts hxy hxmem hymem hfresh hlive hlivex hlivey hdisp hoptnoop hrel hblock,
          stackDisc_nonCommBinopVar_preserve hsd hname hncomm hnjmp hcompute hdispatch hops houts hxy
            hxmem hymem hfresh hlive hlivex hlivey hwx hwy hoptnoop, ?_⟩
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

/-! ## Invariant-threading body fold

The body-fold counterpart of `genBlockBody_sim` that THREADS the `StackDiscH` invariant. Given a
per-instruction step that, from `StackDiscH (j+1)`, both simulates the asm AND re-establishes
`StackDiscH j` (exactly `stackDisc_commBinopVar_step`'s shape), folding over a body of length `n`
with initial headroom `n` runs the whole body's asm and lands at `StackDiscH 0`. Unlike
`genBlockBody_sim`'s *uniform* `hstep` (which only sees `venomAsmRel`), here the per-instruction side
conditions are carried by the invariant, whose headroom drops one unit per (stack-growing)
instruction — so a depth bound that a single instruction would break stays true across the body. -/
theorem genBlockBody_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length)
        ∧ StackDiscH j (gp x p).2 (gvBodyStep x v))
    (l : List (Instruction × Nat)) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState)
    (hsd0 : StackDiscH l.length ps0 vs0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (l.foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (l.foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
             (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (l.foldl
             (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0
             (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
             (l.foldl (fun v x => gvBodyStep x v) vs0) := by
  induction l generalizing ps0 vs0 as0 with
  | nil =>
    refine ⟨as0, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
  | cons x xs ih =>
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1⟩ := hstep x ps0 vs0 as0 xs.length hsd0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd'⟩ :=
      ih (gp x ps0).2 (gvBodyStep x vs0) as1 hsd1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd'⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega

/-! ## S-threading body fold (no-swap regime)

`genBlockBody_sim_inv`'s `hstep` is `∀ x p`, so it can't supply each instruction's operand membership
(`x, y ∈ stack`). This version threads the stack-var list `S` too, via a per-instruction readiness
predicate `BodyStepsReady` that *pins* `S` at each position — so the SSA fact "operands ∈ S_i" is a
fixed fact the caller discharges (via `stackDisc_commBinopVar_step_S`). The pinned-`S` entry is still
`∀ p` (any plan state with `StackIsVars S p`), which is exactly what `step_S` proves given the static
binop facts + the no-op optimistic swap (the no-swap regime, where the schedule needs no reorder). -/

/-- The output var an instruction appends to the stack-var list. -/
def outOf (x : Instruction × Nat) : String := x.1.outputs.headD ""

/-- Per-instruction readiness threading the stack-var list `S`: each instruction's body step holds
    for any state with `StackIsVars S` (S pinned to its position), and the tail is ready relative to
    `S ++ [outOf x]`. Proven per-block by `stackDisc_commBinopVar_step_S` (its `x,y ∈ S`/`out ∉ S`
    obligations become fixed SSA facts once `S` is pinned). -/
def BodyStepsReady (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S =>
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → StackIsVars S p → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
        StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
        StackIsVars (S ++ [outOf x]) (gp x p).2)
      ∧ BodyStepsReady lo offsetToPc prog gp xs (S ++ [outOf x])

/-- **S-threading body fold.** Given `BodyStepsReady` (per-instruction steps with `S` pinned) and the
    initial headroom (`StackDiscH l.length`) + stack shape (`StackIsVars S0`), folding the body runs
    its whole asm and ends at `StackDiscH 0` with the stack now `S0 ++ l.map outOf`. The fold consumes
    the readiness predicate one entry per instruction, threading both invariants. -/
theorem genBlockBody_sim_inv_S {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReady lo offsetToPc prog gp l S0 →
      StackDiscH l.length ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
             StackDiscH 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) ∧
             StackIsVars (S0 ++ l.map outOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨hstepx, hready_xs⟩ := hready
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv, List.map_cons] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ := hstepx ps0 vs0 as0 xs.length hsd0 hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ [outOf x]) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'

/-- **Single-binop `BodyStepsReady` constructor.** Packages one commutative var-binop body
    instruction (immediately preceding the block terminator) into a one-element `BodyStepsReady`,
    ready to feed `genBlockBody_sim_inv_S` / `genBlockPrefixBody_sim_inv`. The key simplification is
    `nextIsTerminator = true`: the optimistic-swap obligation of `stackDisc_commBinopVar_step_S`
    collapses to `([], ps)` (the first branch of `optimisticSwapPlan`), so it holds for *every* plan
    state with no per-state reasoning — exactly the no-swap regime the body fold needs. The remaining
    obligations are static SSA facts about `inst`/`S` (operands `∈ S`, output fresh, both live) and the
    program's opcode dispatch. This is the missing adapter between the per-instruction body atom and the
    body-fold engine. -/
theorem bodyStepsReady_single_commBinop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s) :
    BodyStepsReady lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      [(inst, idx)] S := by
  refine ⟨?_, trivial⟩
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopVar_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ## Permutation-aware invariant (handling an active optimistic swap)

The optimistic swap reorders the stack to match the next instruction's operand order, breaking the
exact-order `StackIsVars`. But everything the per-instruction step actually needs — operand
membership, stack length, output freshness — is order-INDEPENDENT. So the right generalization tracks
the stack *up to permutation*: `StackPerm S p` says the plan stack is a permutation of `S.map Var`. It
generalizes `StackIsVars` (equality ⇒ permutation) and supports the same membership/length/freshness
derivations, now stable under the swap's reordering. (The exact-order `StackIsVars` is the no-swap
special case; `StackPerm` is what an active-swap fold threads.) -/
def StackPerm (S : List String) (p : PlanState) : Prop :=
  List.Perm p.stack (S.map Operand.Var)

/-- The exact-order invariant implies the permutation invariant. -/
theorem stackIsVars_perm {S : List String} {p : PlanState} (h : StackIsVars S p) : StackPerm S p := by
  have hp : p.stack = S.map Operand.Var := h
  rw [StackPerm, hp]

/-- Operand membership from the permutation invariant (order-independent). -/
theorem stackPerm_mem {S : List String} {p : PlanState} {z : String}
    (h : StackPerm S p) (hz : z ∈ S) : Operand.Var z ∈ p.stack :=
  h.mem_iff.mpr (List.mem_map_of_mem hz)

/-- A var not in `S` is absent from the stack (freshness), order-independent. -/
theorem stackPerm_not_mem {S : List String} {p : PlanState} {z : String}
    (h : StackPerm S p) (hz : z ∉ S) : ¬ Operand.Var z ∈ p.stack := by
  intro hc
  rw [h.mem_iff, List.mem_map] at hc
  obtain ⟨a, ha, hav⟩ := hc
  injection hav with hav'
  exact hz (hav' ▸ ha)

/-- The stack depth equals `S.length` (for the `shallow` bound), order-independent. -/
theorem stackPerm_length {S : List String} {p : PlanState} (h : StackPerm S p) :
    p.stack.length = S.length := by rw [h.length_eq, List.length_map]

/-- `StackPerm` is preserved by appending the output (the no-swap output stack `ps.stack ++ [Var out]`
    permutes `(S ++ [out]).map Var`); under an active swap, a stack *permutation* of this still
    satisfies `StackPerm (S ++ [out])` by transitivity — which is exactly why the permutation form is
    the right invariant for the swap. -/
theorem stackPerm_append_out {S : List String} {p : PlanState} {out : String}
    (h : StackPerm S p) :
    StackPerm (S ++ [out]) { p with stack := p.stack ++ [Operand.Var out] } := by
  show List.Perm (p.stack ++ [Operand.Var out]) ((S ++ [out]).map Operand.Var)
  rw [List.map_append]
  exact h.append_right _

open List in
/-- **`stackSwap` is a permutation of its input.** The optimistic swap reorders the stack via a
    single `stackSwap` (a transposition of the top with an earlier element), so its output is a
    *permutation* of the input. Proved structurally (BEq-free): decompose `s = mid ++ [last]`, reduce
    the two `set`s to `(mid.set k last) ++ [mid[k]]`, then chain `set_perm_cons_eraseIdx` +
    `getElem_cons_eraseIdx_perm` + `perm_append_comm`. (`dist < s.length` holds at every call site
    via `doSwap`'s bound; `dist = 0` is the identity case.) -/
theorem stackSwap_perm (dist : Nat) (s : List Operand) (hd : dist < s.length) :
    List.Perm (stackSwap dist s) s := by
  rcases Nat.eq_zero_or_pos dist with h0 | hpos
  · subst h0
    have ht : s.length - 1 < s.length := by omega
    simp only [stackSwap, Nat.sub_zero, List.set_set]
    rw [getElem!_pos s _ ht, List.set_getElem_self]
  · obtain ⟨mid, last, hs⟩ : ∃ mid last, s = mid ++ [last] := by
      rcases List.eq_nil_or_concat s with h | ⟨mid, last, h⟩
      · subst h; simp at hd
      · exact ⟨mid, last, by rw [h, List.concat_eq_append]⟩
    subst hs
    have hkmid : mid.length - dist < mid.length := by simp at hd; omega
    have hlenq : (mid ++ [last]).length = mid.length + 1 := by simp
    have hidx_t : (mid ++ [last]).length - 1 = mid.length := by simp
    have hv : (mid ++ [last])[mid.length - dist]! = mid[mid.length - dist]'hkmid := by
      rw [getElem!_pos _ _ (by rw [hlenq]; omega),
          List.getElem_append_left hkmid]
    have hw : (mid ++ [last])[mid.length]! = last := by
      rw [getElem!_pos _ _ (by rw [hlenq]; omega),
          List.getElem_append_right (by omega)]; simp
    have hstk : stackSwap dist (mid ++ [last])
        = (mid.set (mid.length - dist) last) ++ [mid[mid.length - dist]'hkmid] := by
      simp only [stackSwap, hidx_t, hv, hw]
      rw [List.set_append, if_neg (by omega)]
      simp only [Nat.sub_self, List.set_cons_zero]
      rw [List.set_append, if_pos (by omega)]
    rw [hstk]
    have hperm1 : (mid.set (mid.length - dist) last) ~ last :: mid.eraseIdx (mid.length - dist) :=
      List.set_perm_cons_eraseIdx hkmid last
    calc (mid.set (mid.length - dist) last) ++ [mid[mid.length - dist]'hkmid]
        ~ (last :: mid.eraseIdx (mid.length - dist)) ++ [mid[mid.length - dist]'hkmid] :=
          hperm1.append_right _
      _ = last :: (mid.eraseIdx (mid.length - dist) ++ [mid[mid.length - dist]'hkmid]) := by simp
      _ ~ last :: (mid[mid.length - dist]'hkmid :: mid.eraseIdx (mid.length - dist)) :=
          List.Perm.cons _ (List.perm_append_comm.trans (by simp))
      _ ~ last :: mid := List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hkmid)
      _ ~ mid ++ [last] := by
          have := List.perm_append_comm (l₁ := [last]) (l₂ := mid); simpa using this

/-- **The active swap preserves `StackPerm`.** Since `stackSwap` permutes the stack and `StackPerm`
    tracks the stack only up to permutation, applying the optimistic swap keeps `StackPerm S` — the
    payoff of choosing the permutation form: an active swap (which would break exact-order
    `StackIsVars`) leaves the invariant intact. -/
theorem stackPerm_swap {S : List String} {p : PlanState} {dist : Nat}
    (h : StackPerm S p) (hd : dist < p.stack.length) :
    StackPerm S { p with stack := stackSwap dist p.stack } :=
  (stackSwap_perm dist p.stack hd).trans h

/-- **The whole optimistic swap preserves `StackPerm`** — the invariant-side companion of
    `optimisticSwapPlan_sim` (the asm side). `optimisticSwapPlan` is either a no-op or a single
    `doSwap`; under the same in-range bound `optimisticSwapPlan_sim` assumes (`dist ≤ 16 ∧ dist <
    length`), `doSwap`'s stack effect is exactly `stackSwap` (or identity for `dist = 0`), so
    `StackPerm S` survives. This is the invariant-threading fact an active-swap binop step needs. -/
theorem optimisticSwapPlan_stackPerm {dfg : DfgAnalysis} {inst : Instruction}
    {nextLiveness : List String} {nIT : Bool} {ps : PlanState} {S : List String}
    (h : StackPerm S ps)
    (hbound : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist →
              optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps →
              dist ≤ 16 ∧ dist < ps.stack.length) :
    StackPerm S (optimisticSwapPlan dfg inst nextLiveness nIT ps).2 := by
  rcases optimisticSwapPlan_cases dfg inst nextLiveness nIT ps with hnoop | ⟨dist, hd, heq⟩
  · rw [hnoop]; exact h
  · rw [heq]
    obtain ⟨hle, hlt⟩ := hbound dist hd heq
    rcases Nat.eq_zero_or_pos dist with h0 | hpos
    · subst h0; rw [doSwap_zero]; exact h
    · unfold doSwap
      rw [if_neg (by omega), if_pos hle]
      exact stackPerm_swap h hlt

/-- The active swap preserves `StackDiscH` too: it permutes the stack, so length and the var set are
    unchanged (`shallow`/`defined` survive via `stackSwap_perm`), and `spilled` is untouched. -/
theorem stackDiscH_swap {k : Nat} {p : PlanState} {v : VenomState} {dist : Nat}
    (h : StackDiscH k p v) (hd : dist < p.stack.length) :
    StackDiscH k { p with stack := stackSwap dist p.stack } v where
  noSpill := h.noSpill
  shallow := by
    show (stackSwap dist p.stack).length + k ≤ 15
    rw [(stackSwap_perm dist p.stack hd).length_eq]; exact h.shallow
  defined := fun z hz =>
    h.defined z ((stackSwap_perm dist p.stack hd).mem_iff.mp hz)

/-- `optimisticSwapPlan` preserves `StackDiscH` (the `StackDiscH` companion of
    `optimisticSwapPlan_stackPerm`): no-op or a single in-range `doSwap`, both `StackDiscH`-preserving. -/
theorem optimisticSwapPlan_stackDiscH {dfg : DfgAnalysis} {inst : Instruction}
    {nextLiveness : List String} {nIT : Bool} {ps : PlanState} {vs : VenomState} {k : Nat}
    (h : StackDiscH k ps vs)
    (hbound : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!) ps.stack = some dist →
              optimisticSwapPlan dfg inst nextLiveness nIT ps = doSwap dist ps →
              dist ≤ 16 ∧ dist < ps.stack.length) :
    StackDiscH k (optimisticSwapPlan dfg inst nextLiveness nIT ps).2 vs := by
  rcases optimisticSwapPlan_cases dfg inst nextLiveness nIT ps with hnoop | ⟨dist, hd, heq⟩
  · rw [hnoop]; exact h
  · rw [heq]
    obtain ⟨hle, hlt⟩ := hbound dist hd heq
    rcases Nat.eq_zero_or_pos dist with h0 | hpos
    · subst h0; rw [doSwap_zero]; exact h
    · unfold doSwap
      rw [if_neg (by omega), if_pos hle]
      exact stackDiscH_swap h hlt

/-- `releaseDeadSpills` preserves `StackDiscH`: it never touches the stack
    (`releaseDeadSpills_stack`, so `shallow`/`defined` survive) and only removes spills
    (`releaseDeadSpills_noSpill`). -/
theorem releaseDeadSpills_stackDiscH {nextLiveness : List String} {k : Nat} {ps : PlanState}
    {vs : VenomState} (h : StackDiscH k ps vs) :
    StackDiscH k (releaseDeadSpills nextLiveness ps) vs where
  noSpill := releaseDeadSpills_noSpill nextLiveness ps h.noSpill
  shallow := by rw [releaseDeadSpills_stack]; exact h.shallow
  defined := fun z hz => h.defined z (by rw [releaseDeadSpills_stack] at hz; exact hz)

/-- `releaseDeadSpills` preserves `StackPerm` (it never touches the stack). -/
theorem releaseDeadSpills_stackPerm {nextLiveness : List String} {S : List String} {ps : PlanState}
    (h : StackPerm S ps) : StackPerm S (releaseDeadSpills nextLiveness ps) := by
  show List.Perm (releaseDeadSpills nextLiveness ps).stack (S.map Operand.Var)
  rw [releaseDeadSpills_stack]; exact h

/-- `StackPerm` for a state whose stack is `ps.stack ++ [Var out]` and `StackPerm S ps`: it permutes
    `(S ++ [out]).map Var`. (Generalises `stackPerm_append_out` to any state with that stack — used
    for the post-emit state, whose non-stack fields come from the input-emission output, not `ps`.) -/
theorem stackPerm_of_stack_append {S : List String} {ps q : PlanState} {out : String}
    (h : StackPerm S ps) (hq : q.stack = ps.stack ++ [Operand.Var out]) :
    StackPerm (S ++ [out]) q := by
  show List.Perm q.stack ((S ++ [out]).map Operand.Var)
  rw [hq, List.map_append]
  exact h.append_right _

/-- **Active-swap body step under the invariant** — discharges a `BodyStepsReadyP` entry for a
    commutative var binop. From `StackDiscH (k+1)` + `StackPerm S` it derives the binop sim's side
    conditions (membership/depths/values; freshness from `out ∉ S`), runs the active-swap sim
    (`genRegularInstPlan_commBinopVar_sim_swap`), and re-establishes both invariants on the output:
    `StackDiscH k` (post-emit `StackDiscH` + `optimisticSwapPlan_stackDiscH` + `releaseDeadSpills_stackDiscH`)
    and `StackPerm (S ++ [out])` (post-emit `StackPerm` via `stackPerm_of_stack_append` +
    `optimisticSwapPlan_stackPerm` + `releaseDeadSpills_stackPerm`). The active-swap counterpart of
    `stackDisc_commBinopVar_step_S`; this is what `genBlockBody_sim_inv_P` folds. -/
theorem stackDisc_commBinopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
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
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  -- the asm step (active swap)
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_commBinopVar_sim_swap hname hcomm hops houts
    hxy hox hoy rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivey hdepth_y hsmall_y hleny
    (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx' hwx hwy hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  -- the output state is `releaseDeadSpills (optimisticSwapPlan … psE).2`, psE the post-emit state
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_commBinopVar_eq hname hcomm hops houts hxy rfl hlive (hsd.noSpill _)
      hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x', hrev]
  -- post-emit StackDiscH on psE
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_pair_var_eq (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex
      hdepth_x' hsmall_x']
  -- `lookupVar` is invisible to `gvBodyStep`'s `instIdx` (it only sets that field)
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs)
      = lookupVar z (updateVar out (f wx wy) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w, hw⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w, by rw [hlv z, lookupVar_updateVar_ne vs out z (f wx wy) hzout]; exact hw⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f wx wy, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · -- StackDiscH k (output) (gvBodyStep …)
    rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · -- StackPerm (S ++ [out]) (output)
    rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Active-swap body step under the invariant — non-commutative var binop.** Discharges a
    `BodyStepsReadyP` entry for SUB/DIV/MOD/LT/GT/SHL/…; the non-comm counterpart of
    `stackDisc_commBinopVar_step_swap_P` (uses `genRegularInstPlan_nonCommBinopVar_sim_swap`). -/
theorem stackDisc_nonCommBinopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure2 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hox : out ≠ x) (hoy : out ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmBinop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
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
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  obtain ⟨d_x, hdepth_x, hlenx⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some (d_x + 1) := by
    rw [hdupY, stackGetDepth_append_ne ps.stack hxy, hdepth_x]; rfl
  have hsmall_x' : d_x + 1 ≤ 15 := by omega
  have hlenx' : d_x + 1 < (stackDup d_y ps.stack).length := by
    rw [hdupY]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_nonCommBinopVar_sim_swap hname hncomm hnjmp
    hcompute hops houts hxy hox hoy rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivey hdepth_y
    hsmall_y hleny (hsd.noSpill _) hlivex hdepth_x' hsmall_x' hlenx' hwx hwy hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy) vs) :=
    stepInstBase_binopVar hdispatch hops houts hwx hwy
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_nonCommBinopVar_eq hname hncomm hnjmp hcompute hops houts hxy rfl hlive
      (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex hdepth_x' hsmall_x', hrev]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_pair_var_eq (hsd.noSpill _) hlivey hdepth_y hsmall_y (hsd.noSpill _) hlivex
      hdepth_x' hsmall_x']
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs)
      = lookupVar z (updateVar out (f wx wy) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w, hw⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w, by rw [hlv z, lookupVar_updateVar_ne vs out z (f wx wy) hzout]; exact hw⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f wx wy, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Active-swap body step under the invariant — ternary var opcode.** Discharges a
    `BodyStepsReadyP` entry for ADDMOD/MULMOD: derives the sim's side conditions from
    `StackDiscH (k+1)` + `StackPerm S` (depths via `stackDisc_ternopVar_depths`), runs the active-swap
    sim (`genRegularInstPlan_ternopVar_sim_swap`), and re-establishes `StackDiscH k` + `StackPerm
    (S ++ [out])`. The 3-input counterpart of `stackDisc_commBinopVar_step_swap_P`. -/
theorem stackDisc_ternopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y z out : String} {name : String} {k idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure3 f inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hox : out ≠ x) (hoy : out ≠ y) (hoz : out ≠ z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmTernop f s)
    (hswap : ∀ dist, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                   nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } : PlanState).stack
                 = some dist →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] }
            = doSwap dist
              { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
                  nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } →
            dist ≤ 16 ∧ dist < (ps.stack ++ [Operand.Var out]).length)
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
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var z, Operand.Var y, Operand.Var x] := by
    rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackPerm_mem hsv hyS
  have hzmem : Operand.Var z ∈ ps.stack := stackPerm_mem hsv hzS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  have hsd1 : StackDiscH 1 ps vs := ⟨hsd.noSpill, by have := hsd.shallow; omega, hsd.defined⟩
  obtain ⟨d_z, d_y, d_x, hdepth_z, hsmall_z, hlenz, hdepth_y', hsmall_y, hleny', hdepth_x'',
    hsmall_x, hlenx''⟩ := stackDisc_ternopVar_depths hsd1 hxy hyz hxz hxmem hymem hzmem
  obtain ⟨wx, hwx⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.toStackDisc.defined y hymem
  obtain ⟨wz, hwz⟩ := hsd.toStackDisc.defined z hzmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_ternopVar_sim_swap hname hncomm hnjmp hcompute
    hops houts hxy hyz hxz hox hoy hoz rfl hlive hfresh (hsd.noSpill _) (hsd.noSpill _) hlivez
    hdepth_z hsmall_z hlenz (hsd.noSpill _) hlivey hdepth_y' hsmall_y hleny' (hsd.noSpill _) hlivex
    hdepth_x'' hsmall_x hlenx'' hwx hwy hwz hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f wx wy wz) vs) :=
    stepInstBase_3opVar hdispatch hops houts hwx hwy hwz
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f wx wy wz) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_ternopVar_eq hname hncomm hnjmp hcompute hops houts hxy hyz hxz rfl hlive
      (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey hdepth_y' hsmall_y
      (hsd.noSpill _) hlivex hdepth_x'' hsmall_x, hrev]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x]
        nextLiveness ps).2 with stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled
      = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2.spilled
      = ps.spilled
    rw [emitInputPlan_triple_var_eq (hsd.noSpill _) hlivez hdepth_z hsmall_z (hsd.noSpill _) hlivey
      hdepth_y' hsmall_y (hsd.noSpill _) hlivex hdepth_x'' hsmall_x]
  have hlv : ∀ w, lookupVar w (gvBodyStep (inst, idx) vs)
      = lookupVar w (updateVar out (f wx wy wz) vs) :=
    fun w => (congrArg (lookupVar w) hgv).trans rfl
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var z, Operand.Var y, Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro w hw
      have hw' : Operand.Var w ∈ ps.stack ++ [Operand.Var out] := hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with hw' | hw'
      · have hwout : w ≠ out := by rintro rfl; exact hfresh hw'
        obtain ⟨ww, hww⟩ := hsd.toStackDisc.defined w hw'
        exact ⟨ww, by rw [hlv w, lookupVar_updateVar_ne vs out w (f wx wy wz) hwout]; exact hww⟩
      · injection hw' with hw''; rw [hw'']
        exact ⟨f wx wy wz, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f wx wy wz)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-- **Body step from the invariant — unary var op (no-swap).** The unary counterpart of
    `stackDisc_commBinopVar_step_S`: a single-operand op (ISZERO/NOT/…) discharges a `BodyStepsReady`
    entry. Membership/depth/value/freshness are derived from `StackDiscH`+`StackIsVars`; the asm runs
    via `genRegularInstPlan_unopVar_sim`; `StackDiscH k` (post-emit `StackDiscH` +
    `releaseDeadSpills_stackDiscH`, the `optimisticSwap` is a no-op via `hoptnoop`) and
    `StackIsVars (S ++ [out])` are re-established. -/
theorem stackDisc_unopVar_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure1 f inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
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
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hrev : inst.operands.reverse = [Operand.Var x] := by rw [hops]; rfl
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hsmall : dist ≤ 15 := by have := hsd.toStackDisc.shallow; omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_unopVar_sim hname hnjmp hcompute hops houts
    rfl hlive (hsd.noSpill _) hlivex hdepth hsmall hpeek hlen hxmem hw hfresh (hsd.noSpill _) hdisp
    hoptnoop hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) :=
    stepInstBase_unopVar hdispatch hops houts hw
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f w) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs) = lookupVar z (updateVar out (f w) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness
          { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] } := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive (hsd.noSpill _)
      hlivex hdepth hsmall hpeek]
    simp only [hoptnoop]
  have hpsE_spill : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2.spilled = ps.spilled
    rw [hrev, emitInputPlan_single_var_eq (hsd.noSpill _) hlivex hdepth hsmall hpeek]
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w', hw'⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w', by rw [hlv z, lookupVar_updateVar_ne vs out z (f w) hzout]; exact hw'⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f w, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f w)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]; exact releaseDeadSpills_stackDiscH hsdE
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [hstateEq, releaseDeadSpills_stack, hsv, List.map_append]; rfl

/-- **Active-swap body step under the invariant — unary var op.** The unary counterpart of
    `stackDisc_commBinopVar_step_swap_P`: discharges a `BodyStepsReadyP` entry for a unary var op,
    running the active-swap unary sim and re-establishing `StackDiscH k` + `StackPerm (S ++ [out])`. -/
theorem stackDisc_unopVar_step_swap_P
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis}
    {fn : IrFunction} {inst : Instruction} {nextLiveness : List String}
    {nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState} {lo : AssocList String Nat}
    {vs : VenomState} {as : AsmState} {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {name : String} {k idx : Nat} {f : bytes32 → bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackPerm S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execPure1 f inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name →
        asmStep offsetToPc prog s = asmUnop f s)
    (hswap : ∀ d, stackGetDepth (Operand.Var nextLiveness.getLast!)
              ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                 stack := ps.stack ++ [Operand.Var out] } : PlanState).stack = some d →
            optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] }
            = doSwap d
              { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
                stack := ps.stack ++ [Operand.Var out] } →
            d ≤ 16 ∧ d < (ps.stack ++ [Operand.Var out]).length)
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
          curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackPerm (S ++ [out])
        (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
          curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackPerm_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackPerm_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have h15 : ps.stack.length ≤ 15 := hsd.toStackDisc.shallow
  have hsmall : dist ≤ 15 := by omega
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  obtain ⟨w, hw⟩ := hsd.toStackDisc.defined x hxmem
  obtain ⟨as', hrun, hrel', hpc⟩ := genRegularInstPlan_unopVar_sim_swap hname hnjmp hcompute hops
    houts rfl hlive (hsd.noSpill _) hlivex hdepth hsmall hpeek hlen hxmem hw hfresh (hsd.noSpill _)
    hdisp hswap hrel hblock
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (f w) vs) :=
    stepInstBase_unopVar hdispatch hops houts hw
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (f w) vs with instIdx := idx + 1 } := by
    simp only [gvBodyStep, hstepEq]
  have hlv : ∀ z, lookupVar z (gvBodyStep (inst, idx) vs) = lookupVar z (updateVar out (f w) vs) :=
    fun z => (congrArg (lookupVar z) hgv).trans rfl
  have hstateEq : (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2
      = releaseDeadSpills nextLiveness (optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
          { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
            stack := ps.stack ++ [Operand.Var out] }).2 := by
    rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive (hsd.noSpill _)
      hlivex hdepth hsmall hpeek,
      show inst.operands.reverse = [Operand.Var x] from by rw [hops]; rfl]
  have hpsE_spill : ({ (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState).spilled = ps.spilled := by
    show (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2.spilled = ps.spilled
    rw [emitInputPlan_single_var_eq (hsd.noSpill _) hlivex hdepth hsmall hpeek]
  have hsdE : StackDiscH k
      { (emitInputPlan inst.opcode [Operand.Var x] nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } (gvBodyStep (inst, idx) vs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro op; rw [hpsE_spill]; exact hsd.noSpill op
    · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hsd.shallow; omega
    · intro z hz
      have hz' : Operand.Var z ∈ ps.stack ++ [Operand.Var out] := hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with hz' | hz'
      · have hzout : z ≠ out := by rintro rfl; exact hfresh hz'
        obtain ⟨w', hw'⟩ := hsd.toStackDisc.defined z hz'
        exact ⟨w', by rw [hlv z, lookupVar_updateVar_ne vs out z (f w) hzout]; exact hw'⟩
      · injection hz' with hz''; rw [hz'']
        exact ⟨f w, by rw [hlv out]; exact lookupVar_updateVar_self vs out (f w)⟩
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq ⟨as', hrun, hrel', hpc⟩, ?_, ?_⟩
  · rw [hstateEq]
    exact releaseDeadSpills_stackDiscH (optimisticSwapPlan_stackDiscH hsdE hswap)
  · rw [hstateEq]
    refine releaseDeadSpills_stackPerm (optimisticSwapPlan_stackPerm ?_ hswap)
    exact stackPerm_of_stack_append hsv rfl

/-! ## Body-fold composition kit (chain per-instruction `BodyStep`s into `BodyStepsReady`)

`BodyStepsReady` is cons-structured (`x :: xs` = head-step ∧ ready-tail), and `genBlockBody_sim_inv_S`
folds it into a whole-body sim. What was missing was the *builder* side: a way to assemble
`BodyStepsReady` for an N-instruction body from per-instruction facts. This kit supplies it:

  - `BodyStep` names the head-step (the first conjunct of the cons case) so it can be produced once
    per instruction shape;
  - `bodyStepsReady_nil` / `bodyStepsReady_cons` are the list combinators (`cons` threads `S` by
    `outOf x`, exactly matching the fold's induction);
  - `bodyStep_commBinop` / `bodyStep_unopVar` / `bodyStep_nonCommBinopVar` factor the existing
    `stackDisc_*_step_S` per-instruction steps into `BodyStep` producers.

Chaining `bodyStepsReady_cons` over these producers, then feeding `genBlockBody_sim_inv_S`, gives a
multi-instruction body sim (see `bodyStepsReady_two_commBinop`). The remaining generality gap: the
`gp` is one function for the whole body, so heterogeneous *per-instruction* liveness/`nextIsTerminator`
must be encoded through `gp`'s instruction argument — the producers already take those as parameters,
so a `gp` that dispatches on the index composes; a concrete real-liveness N-instruction block is the
next step. -/

/-- The per-instruction **head-step** — exactly the first conjunct of `BodyStepsReady`'s cons case,
    named so it can be produced once per instruction shape and chained by `bodyStepsReady_cons`. -/
def BodyStep (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + 1) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ [outOf x]) (gp x p).2

/-- Empty body is trivially ready. -/
theorem bodyStepsReady_nil {lo offsetToPc prog gp S} :
    BodyStepsReady lo offsetToPc prog gp ([] : List (Instruction × Nat)) S := trivial

/-- **The body-fold composition step.** Prepend one ready instruction (`BodyStep` at `S`) to a ready
    tail (starting at `S ++ [outOf x]`) to get a ready `x :: xs`. Turns per-instruction `BodyStep`s
    into an N-instruction `BodyStepsReady`, which `genBlockBody_sim_inv_S` then folds. -/
theorem bodyStepsReady_cons {lo offsetToPc prog gp x xs S}
    (hhead : BodyStep lo offsetToPc prog gp x S)
    (htail : BodyStepsReady lo offsetToPc prog gp xs (S ++ [outOf x])) :
    BodyStepsReady lo offsetToPc prog gp (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **`BodyStep` for a commutative var-binop** (immediately before the terminator, `nextIsTerminator =
    true`, so the optimistic swap collapses to a no-op), factored from `bodyStepsReady_single_commBinop`. -/
theorem bodyStep_commBinop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hopt : optimisticSwapPlan dfg inst nextLiveness true
      { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
        stack := p.stack ++ [Operand.Var out] }
    = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
            stack := p.stack ++ [Operand.Var out] }) := by
    simp [optimisticSwapPlan]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_commBinopVar_step_S (idx := idx) hsd hsv hname hcomm
    (hdispatch v) hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp hopt hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **`BodyStep` for a var-unop** (ISZERO/NOT), factored from `stackDisc_unopVar_step_S`. The
    optimistic-swap no-op is hypothesised per plan state (`hoptnoop : ∀ p, …`). -/
theorem bodyStep_unopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out name : String} {idx : Nat} {f : bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure1 f inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmUnop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_unopVar_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **`BodyStep` for a non-commutative var-binop** (SUB/DIV/SHL/…), factored from
    `stackDisc_nonCommBinopVar_step_S`. -/
theorem bodyStep_nonCommBinopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y out name : String} {idx : Nat} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_nonCommBinopVar_step_S (idx := idx) hsd hsv hname hncomm hnjmp
    hcompute (hdispatch v) hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **A 2-instruction body composes.** Two commutative var-binops (both in the collapsed-swap regime)
    chain via `bodyStepsReady_cons`: the first ready at `S`, the second at `S ++ [out₁]` (the
    S-thread), giving `BodyStepsReady [i₁, i₂]` — feedable to `genBlockBody_sim_inv_S` for a whole
    2-instruction-body sim. Validates that the kit scales past one instruction. -/
theorem bodyStepsReady_two_commBinop
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 o2 n1 n2 : String} {idx1 idx2 : Nat}
    {f1 f2 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some n2) (hcomm2 : isCommutative i2.opcode = true)
    (hdisp2' : ∀ v, stepInstBase i2 v = execPure2 f2 i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1]) (ho2S : o2 ∉ S ++ [o1])
    (hlive2 : nextLiveness.contains o2 = true) (hlivex2 : nextLiveness.contains x2 = true)
    (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n2 → asmStep offsetToPc prog s = asmBinop f2 s) :
    BodyStepsReady lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      [(i1, idx1), (i2, idx2)] S := by
  have hstep1 := bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
    (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
  have hstep2 := bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
    (curBbLabel := curBbLabel) (S := S ++ [o1]) hname2 hcomm2 hdisp2' hops2 houts2 hxy2 hx2S hy2S ho2S hlive2 hlivex2 hlivey2 hdisp2
  have hout1 : outOf (i1, idx1) = o1 := by simp [outOf, houts1]
  refine bodyStepsReady_cons hstep1 ?_
  rw [hout1]
  exact bodyStepsReady_cons hstep2 bodyStepsReady_nil

/-- **`BodyStep` for a var-ternop** (ADDMOD/MULMOD), factored from `stackDisc_ternopVar_step_S`. -/
theorem bodyStep_ternopVar
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y z out name : String} {idx : Nat}
    {f : bytes32 → bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execPure3 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y, Operand.Var z])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hlivez : nextLiveness.contains z = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmTernop f s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_ternopVar_step_S (idx := idx) hsd hsv hname hncomm hnjmp
    hcompute (hdispatch v) hops houts hxy hyz hxz hxS hyS hzS houtS hlive hlivex hlivey hlivez hdisp
    (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ### `BodyStep` producer for 0-input context pushes (wiring a non-arithmetic atom into the fold)

The first body-fold producer for an op that is *not* an arithmetic var-op: a 0-input context push
(`CALLVALUE`, `CALLER`, `CODESIZE`, …), built on `genRegularInstPlan_read0_eq`/`_sim`. The output
stack (`genRegularInstPlan_read0_outStack`) and headroom (`stackDisc_read0_preserve`) mirror the
arithmetic producers; the wrinkle is that the pushed value is a *state field* (`fV v` on the Venom
side, `fA s` on the asm side, equal under the relation), threaded through `hfield`. -/

/-- Output stack of a 0-input push: `ps.stack ++ [Var out]` (the 0-operand analog of
    `genRegularInstPlan_commBinopVar_outStack`). -/
theorem genRegularInstPlan_read0_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {out name : String}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive]
  simp only [hoptnoop]
  rw [releaseDeadSpills_stack]

/-- Headroom preservation for a 0-input push: `StackDiscH (k+1)` before ⇒ `StackDiscH k` after (one
    output pushed). The 0-operand analog of `stackDisc_commBinopVar_preserve`. -/
theorem stackDisc_read0_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {out name : String} {idx k : Nat} {v : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out v vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_read0_eq hname hnjmp hcompute hops houts hlive]
  simp only [hoptnoop]
  apply releaseDeadSpills_stackDiscH
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out v vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    show ∃ w, lookupVar z (updateVar out v vs) = some w
    rw [List.mem_append] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨w, hw⟩ := hsd.defined z h
      exact ⟨w, by rw [lookupVar_updateVar_ne vs out z v hzout]; exact hw⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      exact ⟨v, by rw [h']; exact lookupVar_updateVar_self vs out v⟩

/-- The `StackIsVars`-aware body step for a 0-input push: the sim (via `gvBodyStep_of_updateVar`), the
    headroom drop, and the output shape `StackIsVars (S ++ [out])`. The 0-operand analog of
    `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_read0_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {out name : String} {k idx : Nat} {v : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out v vs))
    (hdisp : ∀ (h : as.pc < prog.length),
        prog.get ⟨as.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog as = asmPushVal v as)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { ps with stack := ps.stack ++ [Operand.Var out] }
      = ([], { ps with stack := ps.stack ++ [Operand.Var out] }))
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  have hsim := genRegularInstPlan_read0_sim hname hnjmp hcompute hops houts hlive
    hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_read0_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_read0_outStack hname hnjmp hcompute hops houts hlive hoptnoop, hsv,
      List.map_append]; rfl

/-- **`BodyStep` for a 0-input context-push op** (CALLVALUE / CALLER / CODESIZE / …). The pushed value
    is a state field: `fV v` on the Venom side (`hstepEq`), `fA s` on the asm side (`hdispAsm`), equal
    under the relation (`hfield`, from the equated `venomAsmRel` conjunct for that field). The first
    non-arithmetic body-fold producer — lets context pushes chain via `bodyStepsReady_cons` alongside
    the arithmetic ops. -/
theorem bodyStep_read0
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {out name : String} {idx : Nat}
    {fV : VenomState → bytes32} {fA : AsmState → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [])
    (houts : inst.outputs = [out])
    (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hstepEq : ∀ v, stepInstBase inst v = ExecResult.OK (updateVar out (fV v) v))
    (hdispAsm : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fA s) s)
    (hfield : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { p with stack := p.stack ++ [Operand.Var out] }
      = ([], { p with stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  have hdisp : ∀ (h : s.pc < prog.length),
      prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmPushVal (fV v) s := by
    intro h hg; rw [hdispAsm s h hg, hfield p v s hrel]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_read0_step_S (idx := idx) (v := fV v) hsd hsv hname hnjmp
    hcompute hops houts houtS hlive (hstepEq v) hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-! ### `BodyStep` producer for SLOAD (a 1-input storage load)

The load counterpart of the read0 producer. It has a stack *input* (the key), so — unlike read0 — the
input's stack depth is derived from `StackIsVars S` inside `stackDisc_sload_step_S` (as the arithmetic
producers do), and the plan state carries the input-emission bridge (`sload_emit2_eq`). No field bridge
is needed: `emit_sload_sim` reconciles `sload key as.toVenomState` with `sload key vs` internally. -/

/-- Reduce `(emitInputPlan opc (reverse = [Var x]) nl ps).2` to `{ps with stack := stackDup dist ps.stack}`
    — the single-var input emission is a `doDup`. -/
private theorem sload_emit2_eq {inst : Instruction} {nextLiveness : List String} {ps : PlanState}
    {x : String} {dist : Nat}
    (hops : inst.operands = [Operand.Var x])
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15) :
    (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2
      = { ps with stack := stackDup dist ps.stack } := by
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
  rw [hrev, hemiteq, hdo]

/-- Output stack of an SLOAD: `ps.stack ++ [Var out]` (unopVar shape). -/
theorem genRegularInstPlan_sload_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {x out : String} {dist : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack ++ [Operand.Var out] := by
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
      hdepth hsmall hpeek]
  simp only [hoptnoop]
  rw [releaseDeadSpills_stack]

/-- Headroom preservation for an SLOAD: `StackDiscH (k+1)` before ⇒ `StackDiscH k` after. -/
theorem stackDisc_sload_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x out : String} {idx k dist : Nat} {w : bytes32}
    (hsd : StackDiscH (k + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hlive : nextLiveness.contains out = true)
    (hnospill : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth : stackGetDepth (Operand.Var x) ps.stack = some dist)
    (hsmall : dist ≤ 15)
    (hpeek : stackPeek dist ps.stack = Operand.Var x)
    (hfresh : ¬ Operand.Var out ∈ ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (sload w vs) vs))
    (hoptnoop : optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
          stack := ps.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
              stack := ps.stack ++ [Operand.Var out] })) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_unopVar_eq hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
      hdepth hsmall hpeek]
  simp only [hoptnoop]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with
        stack := ps.stack ++ [Operand.Var out] } : PlanState)
      = { ps with stack := ps.stack ++ [Operand.Var out] } := by
    rw [sload_emit2_eq hops hnospill hlivex hdepth hsmall]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { updateVar out (sload w vs) vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show (ps.stack ++ [Operand.Var out]).length + k ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    have := hsd.shallow; omega
  · intro z hz
    show ∃ ww, lookupVar z (updateVar out (sload w vs) vs) = some ww
    rw [List.mem_append] at hz
    rcases hz with h | h
    · have hzout : z ≠ out := by rintro rfl; exact hfresh h
      obtain ⟨ww, hww⟩ := hsd.defined z h
      exact ⟨ww, by rw [lookupVar_updateVar_ne vs out z (sload w vs) hzout]; exact hww⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      injection h with h'
      exact ⟨sload w vs, by rw [h']; exact lookupVar_updateVar_self vs out (sload w vs)⟩

/-- The `StackIsVars`-aware body step for SLOAD: derives the input depth from `StackIsVars S`, runs the
    sim (`genRegularInstPlan_sload_sim` via `gvBodyStep_of_updateVar`), and threads the headroom /
    output shape. The storage-load analog of `stackDisc_commBinopVar_step_S`. -/
theorem stackDisc_sload_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x out : String} {k idx : Nat}
    (hsd : StackDiscH (k + 1) ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execRead1 (fun key s => sload key s) inst vs)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
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
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars (S ++ [out]) (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hfresh : ¬ Operand.Var out ∈ ps.stack := stackIsVars_not_mem hsv houtS
  obtain ⟨dist, hdepth, hlen⟩ := stackGetDepth_of_mem hxmem
  have hpeek : stackPeek dist ps.stack = Operand.Var x := stackGetDepth_peek hdepth
  have hsmall : dist ≤ 15 := by have := hsd.shallow; omega
  have hnospill : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  have hspill : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hsd.noSpill _
  obtain ⟨w, hw⟩ := hsd.defined x hxmem
  have hval : operandVal vs lo (Operand.Var x) = some w := hw
  have hstepEq : stepInstBase inst vs = ExecResult.OK (updateVar out (sload w vs) vs) := by
    rw [hdispatch]; unfold execRead1; rw [hops, houts]; simp only [evalOperand, hw]
  have hsim := genRegularInstPlan_sload_sim hname hnjmp hcompute hops houts rfl hlive hnospill hlivex
    hdepth hsmall hpeek hlen hxmem hval hfresh hspill hdisp hoptnoop hrel hblock
  refine ⟨gvBodyStep_of_updateVar (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_sload_preserve (idx := idx) hsd hname hnjmp hcompute hops houts hlive hnospill
      hlivex hdepth hsmall hpeek hfresh hstepEq hoptnoop
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = (S ++ [out]).map Operand.Var
    rw [genRegularInstPlan_sload_outStack hname hnjmp hcompute hops houts hlive hnospill hlivex
      hdepth hsmall hpeek hoptnoop, hsv, List.map_append]; rfl

/-- **`BodyStep` for SLOAD.** The storage-load body-fold producer. Unlike `bodyStep_read0`, no field
    bridge is needed (`emit_sload_sim` reconciles the asm/Venom reads internally via the
    `accounts`/`callCtx` conjuncts); the input depth is derived from `StackIsVars S` inside
    `stackDisc_sload_step_S`. -/
theorem bodyStep_sload
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x out : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SLOAD")
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execRead1 (fun key s => sload key s) inst v)
    (hops : inst.operands = [Operand.Var x])
    (houts : inst.outputs = [out])
    (hxS : x ∈ S) (houtS : out ∉ S)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SLOAD" → asmStep offsetToPc prog s = asmSload s)
    (hoptnoop : ∀ p : PlanState, optimisticSwapPlan dfg inst nextLiveness nextIsTerminator
        { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
          stack := p.stack ++ [Operand.Var out] }
      = ([], { (emitInputPlan inst.opcode inst.operands.reverse nextLiveness p).2 with
              stack := p.stack ++ [Operand.Var out] })) :
    BodyStep lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have hout : outOf (inst, idx) = out := by simp [outOf, houts]
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_sload_step_S (idx := idx) hsd hsv hname hnjmp hcompute
    (hdispatch v) hops houts hxS houtS hlive hlivex hdisp (hoptnoop p) hrel hblock
  exact ⟨hsim, hsd', by rw [hout]; exact hsv'⟩

/-- **End-to-end 2-instruction body sim.** Chains two commutative var-binops via the composition kit
    (`bodyStepsReady_two_commBinop`) and folds them through `genBlockBody_sim_inv_S`: running the whole
    2-instruction body's asm from a disciplined, `S`-shaped, related state ends OK, still related, with
    the discipline at 0 and the stack now `S ++ [o₁, o₂]`. The concrete payoff of the body-fold kit —
    it composes the builder (kit) with the fold into a genuine multi-instruction body simulation. -/
theorem genBlockBody_two_commBinop_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 o2 n1 n2 : String} {idx1 idx2 : Nat}
    {f1 f2 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some n2) (hcomm2 : isCommutative i2.opcode = true)
    (hdisp2' : ∀ v, stepInstBase i2 v = execPure2 f2 i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [o2])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1]) (ho2S : o2 ∉ S ++ [o1])
    (hlive2 : nextLiveness.contains o2 = true) (hlivex2 : nextLiveness.contains x2 = true)
    (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n2 → asmStep offsetToPc prog s = asmBinop f2 s)
    (hsd0 : StackDiscH 2 ps0 vs0) (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].map outOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReady_two_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (curBbLabel := curBbLabel) (idx1 := idx1) (idx2 := idx2)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S
    hlive1 hlivex1 hlivey1 hdisp1 hname2 hcomm2 hdisp2' hops2 houts2 hxy2 hx2S hy2S ho2S hlive2 hlivex2 hlivey2 hdisp2
  exact genBlockBody_sim_inv_S
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ## General body fold — 0- and 1-output ops (`outsOf`/`BodyStepG`/`genBlockBodyG_sim_inv`)

`BodyStep`/`BodyStepsReady`/`genBlockBody_sim_inv_S` assume exactly one output per instruction (they
thread `S ++ [outOf x]` and count `l.length` units of headroom). That excludes no-output observable-
effect ops (stores, LOG). This generalisation replaces the single output `outOf x : String` with the
full list `outsOf x = x.1.outputs : List String`: a 0-output op contributes `[]` (stack and headroom
unchanged), a 1-output op contributes `[out]` (the old behaviour). `bodyStepG_of_bodyStep` bridges
every existing 1-output producer into the general fold, so 0- and 1-output ops mix freely in one body. -/

/-- The full output list of a body instruction (0 or 1 element in practice). Generalises `outOf`
    (a single `String`) so a *0-output* op contributes `[]` — the stack stays `S`. -/
def outsOf (x : Instruction × Nat) : List String := x.1.outputs

/-- The per-instruction head-step, generalised to an arbitrary output list: an op with
    `(outsOf x).length` outputs consumes that many units of headroom (`StackDiscH (j+n) → StackDiscH j`)
    and grows the stack by `outsOf x` (`S → S ++ outsOf x`). For a 1-output op this is `BodyStep`; for
    a 0-output op (store/LOG) it keeps `S` and the headroom. -/
def BodyStepG (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + (outsOf x).length) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ outsOf x) (gp x p).2

/-- Readiness for a general body (mixing 0- and 1-output ops). -/
def BodyStepsReadyG (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepG lo offsetToPc prog gp x S ∧ BodyStepsReadyG lo offsetToPc prog gp xs (S ++ outsOf x)

theorem bodyStepsReadyG_nil {lo offsetToPc prog gp S} :
    BodyStepsReadyG lo offsetToPc prog gp ([] : List (Instruction × Nat)) S := trivial

theorem bodyStepsReadyG_cons {lo offsetToPc prog gp x xs S}
    (hhead : BodyStepG lo offsetToPc prog gp x S)
    (htail : BodyStepsReadyG lo offsetToPc prog gp xs (S ++ outsOf x)) :
    BodyStepsReadyG lo offsetToPc prog gp (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Bridge: a 1-output `BodyStep` is a `BodyStepG`.** So every existing producer (`bodyStep_commBinop`,
    `bodyStep_read0`, `bodyStep_sload`, …) feeds the general fold unchanged: for a 1-output op
    `outsOf x = [out]`, so the headroom delta is `1` and `S ++ outsOf x = S ++ [outOf x]`. -/
theorem bodyStepG_of_bodyStep {lo offsetToPc prog gp x S out}
    (houts : x.1.outputs = [out]) (h : BodyStep lo offsetToPc prog gp x S) :
    BodyStepG lo offsetToPc prog gp x S := by
  intro p v s j hsd hsv hrel hblock
  have hlen : (outsOf x).length = 1 := by rw [outsOf, houts]; rfl
  rw [hlen] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := h p v s j hsd hsv hrel hblock
  have houtOf : outsOf x = [outOf x] := by rw [outsOf, outOf, houts]; rfl
  exact ⟨hsim, hsd', by rw [houtOf]; exact hsv'⟩

/-- **The general S-threading body fold** (0- and 1-output). Same shape as `genBlockBody_sim_inv_S`, but
    the headroom is `(l.flatMap outsOf).length` (Σ outputs, not #instructions) and the stack grows by
    `l.flatMap outsOf` — so a 0-output op consumes 0 headroom and leaves the stack unchanged. -/
theorem genBlockBodyG_sim_inv {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyG lo offsetToPc prog gp l S0 →
      StackDiscH (l.flatMap outsOf).length ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
             StackDiscH 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) ∧
             StackIsVars (S0 ++ l.flatMap outsOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨hstepx, hready_xs⟩ := hready
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscH ((xs.flatMap outsOf).length + (outsOf x).length) ps0 vs0 := by
      have he : ((x :: xs).flatMap outsOf).length = (xs.flatMap outsOf).length + (outsOf x).length := by
        rw [List.flatMap_cons, List.length_append]; omega
      rwa [he] at hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ :=
      hstepx ps0 vs0 as0 (xs.flatMap outsOf).length hsd0' hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ outsOf x) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · rw [List.flatMap_cons, ← List.append_assoc]; exact hsv'

/-! ### Demand-decoupled body fold (headroom demand ≠ output count, for N-input 0-output ops)

The copies (3-input, 0-output) don't fit the output-count headroom of `genBlockBodyG_sim_inv`: the 3rd
DUP reaches `original_depth + 2`, needing `StackDiscH 1` even though `outsOf = []`. This generalisation
threads a per-instruction *demand* `dem` (≥ the output count) for the headroom, decoupled from the
stack delta `outsOf`. `genBlockBodyG_sim_inv` is the `dem = outsOf.length` special case; the copies use
`dem = inputs.length - 2`. `bodyStepH_of_bodyStepG` feeds every existing producer in via monotonicity. -/

/-- `StackDiscH` is antitone in the headroom index: more reserved headroom is a stronger claim. -/
theorem StackDiscH.mono {a b : Nat} {p : PlanState} {v : VenomState}
    (h : StackDiscH a p v) (hab : b ≤ a) : StackDiscH b p v where
  noSpill := h.noSpill
  shallow := by have := h.shallow; omega
  defined := h.defined

/-- The per-instruction head-step with an explicit *headroom demand* `dem` — decoupled from the output
    count `outsOf`. An op reserves `dem` units of headroom (`StackDiscH (j + dem) → StackDiscH j`) — for
    an N-input op `dem ≥ N - 2` covers the deepest DUP's reach even when the output count is smaller
    (e.g. a 3-input 0-output copy needs `dem = 1` though `outsOf = []`). The stack still grows by
    `outsOf x` only. -/
def BodyStepH (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Nat) (x : Instruction × Nat) (S : List String) : Prop :=
  ∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
    StackDiscH (j + dem) p v → StackIsVars S p → venomAsmRel lo p v s →
    asmBlockAt prog s.pc (executePlan (gp x p).1) →
    (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
           venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
           s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
    StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
    StackIsVars (S ++ outsOf x) (gp x p).2

/-- Readiness with a per-instruction demand function `dem`. -/
def BodyStepsReadyH (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst)
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S => BodyStepH lo offsetToPc prog gp (dem x) x S ∧ BodyStepsReadyH lo offsetToPc prog gp dem xs (S ++ outsOf x)

theorem bodyStepsReadyH_nil {lo offsetToPc prog gp dem S} :
    BodyStepsReadyH lo offsetToPc prog gp dem ([] : List (Instruction × Nat)) S := trivial

theorem bodyStepsReadyH_cons {lo offsetToPc prog gp dem x xs S}
    (hhead : BodyStepH lo offsetToPc prog gp (dem x) x S)
    (htail : BodyStepsReadyH lo offsetToPc prog gp dem xs (S ++ outsOf x)) :
    BodyStepsReadyH lo offsetToPc prog gp dem (x :: xs) S :=
  ⟨hhead, htail⟩

/-- **Bridge: `BodyStepG` (output-count demand) is a `BodyStepH` at any demand `≥ outsOf.length`.** So
    every 0- and 1-output producer feeds the demand-threading fold; ops whose reach demand exceeds
    their output count (the copies) use a larger `dem`. -/
theorem bodyStepH_of_bodyStepG {lo offsetToPc prog gp dem x S}
    (hdem : (outsOf x).length ≤ dem) (h : BodyStepG lo offsetToPc prog gp x S) :
    BodyStepH lo offsetToPc prog gp dem x S := by
  intro p v s j hsd hsv hrel hblock
  exact h p v s j (StackDiscH.mono hsd (by omega)) hsv hrel hblock

/-- **The demand-threading body fold.** Generalises `genBlockBodyG_sim_inv`: headroom is `Σ dem`
    (a per-instruction reach demand) instead of `Σ outsOf.length`, so N-input 0-output ops (copies) —
    whose reach demand exceeds their output count — compose too. Stack still grows by `l.flatMap outsOf`. -/
theorem genBlockBodyH_sim_inv {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (dem : Instruction × Nat → Nat)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyH lo offsetToPc prog gp dem l S0 →
      StackDiscH (l.map dem).sum ps0 vs0 → StackIsVars S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
             StackDiscH 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) ∧
             StackIsVars (S0 ++ l.flatMap outsOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨hstepx, hready_xs⟩ := hready
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    have hsd0' : StackDiscH ((xs.map dem).sum + dem x) ps0 vs0 := by
      have he : ((x :: xs).map dem).sum = (xs.map dem).sum + dem x := by
        rw [List.map_cons, List.sum_cons]; omega
      rwa [he] at hsd0
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ :=
      hstepx ps0 vs0 as0 (xs.map dem).sum hsd0' hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ outsOf x) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · rw [List.flatMap_cons, ← List.append_assoc]; exact hsv'

/-! ### `BodyStepG` producer for SSTORE (the first 0-output producer)

Exercises the general fold: SSTORE has no output, so `outsOf = []` — the headroom delta is 0 and the
stack is unchanged. Built on `genRegularInstPlan_sstore_eq`/`_sim`, with the general `gvBodyStep_of_ok`
bridge (the venom step is `sstore wx wy`, not an `updateVar`). -/

/-- `{(emitInputPlan (reverse=[Var y,Var x]) nl ps).2 with stack := base} = {ps with stack := base}`. -/
private theorem sstore_state_eq {inst : Instruction} {nextLiveness : List String} {ps : PlanState}
    {x y : String} {base : List Operand} {d_y d_x' : Nat}
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hlivey : nextLiveness.contains y = true)
    (hdepth_y : stackGetDepth (Operand.Var y) ps.stack = some d_y)
    (hsmall_y : d_y ≤ 15)
    (hnospill_x : alookup' ps.spilled (Operand.Var x) = none)
    (hlivex : nextLiveness.contains x = true)
    (hdepth_x' : stackGetDepth (Operand.Var x) (stackDup d_y ps.stack) = some d_x')
    (hsmall_x' : d_x' ≤ 15) :
    ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
  rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']

/-- Output stack of an SSTORE: `ps.stack` (unchanged — no output). -/
theorem genRegularInstPlan_sstore_outStack
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
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [releaseDeadSpills_stack]
  show base = ps.stack
  exact hstack0.symm

/-- Headroom preservation for an SSTORE: `StackDiscH j` unchanged (no output, stack back to `base`). -/
theorem stackDisc_sstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
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
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { sstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for SSTORE: derives the two input depths from `StackIsVars S`,
    runs the sim (`gvBodyStep_of_ok`), and threads the (unchanged) headroom / stack. The no-output
    (delta-0) analog of `stackDisc_nonCommBinopVar_step_S`. -/
theorem stackDisc_sstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => sstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hxdup : Operand.Var x ∈ stackDup d_y ps.stack := by
    rw [hdupY]; exact List.mem_append.mpr (Or.inl hxmem)
  obtain ⟨d_x', hdepth_x', hlenx'⟩ := stackGetDepth_of_mem hxdup
  have hsmall_x' : d_x' ≤ 15 := by
    rw [hdupY, List.length_append, List.length_cons, List.length_nil] at hlenx'; omega
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (sstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_sstore_sim hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
    hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx' hvx hvy hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_sstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`BodyStepG` for SSTORE** — the first *0-output* body-fold producer. Exercises the general fold:
    with `outsOf (inst,idx) = []` the headroom delta is 0 (`StackDiscH j → StackDiscH j`) and the
    stack is unchanged (`S ++ [] = S`). Stores now chain via `bodyStepsReadyG_cons`. -/
theorem bodyStepG_sstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "SSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun key val s => sstore key val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_sstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for TSTORE (transient-store twin of SSTORE)

The transient-storage twin of the SSTORE producer — `tstore` preserves `vars` just like `sstore`, so
the headroom / stack reasoning is identical; only the emit sim (`genRegularInstPlan_tstore_sim`) and
venom step (`tstore`) differ. Reuses the generic `genRegularInstPlan_sstore_eq`/`_outStack`. -/

theorem stackDisc_tstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
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
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (tstore wx wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { tstore wx wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for TSTORE (transient twin of `stackDisc_sstore_step_S`). -/
theorem stackDisc_tstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "TSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun key val s => tstore key val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hxdup : Operand.Var x ∈ stackDup d_y ps.stack := by
    rw [hdupY]; exact List.mem_append.mpr (Or.inl hxmem)
  obtain ⟨d_x', hdepth_x', hlenx'⟩ := stackGetDepth_of_mem hxdup
  have hsmall_x' : d_x' ≤ 15 := by
    rw [hdupY, List.length_append, List.length_cons, List.length_nil] at hlenx'; omega
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hstepEq : stepInstBase inst vs = ExecResult.OK (tstore wx wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_tstore_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_tstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`BodyStepG` for TSTORE** — a 0-output producer (transient-store twin of `bodyStepG_sstore`). -/
theorem bodyStepG_tstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "TSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun key val s => tstore key val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_tstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for MSTORE (a 0-output *memory* store)

Unlike the shared-state stores, MSTORE's emit step is a memory write, so it carries a per-state
memory-safety precondition (`hmemsafe`: the write window is covered and below the spill region) — the
invariant the codegen guarantees but that lives outside `StackDiscH`. Everything else mirrors the
shared-state stores (`mstore` preserves `vars`; `hspillReg` is vacuous under `noSpill`). -/

theorem stackDisc_mstore_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
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
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (mstore wx.toNat wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  rw [sstore_state_eq hops hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  have hgv : gvBodyStep (inst, idx) vs = { mstore wx.toNat wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

/-- The `StackIsVars`-aware body step for MSTORE: derives depths + the offset value, pulls the memory-
    safety facts from `hmemsafe`, discharges `hspillReg` vacuously from `noSpill`, runs the sim. -/
theorem stackDisc_mstore_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun addr val s => mstore addr.toNat val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ w, lookupVar x vs = some w →
        w.toNat ≤ vs.memory.size ∧ ((w.toNat + 32 + 31) / 32) * 32 ≤ as.memory.size ∧
        w.toNat + 32 ≤ ps.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hxdup : Operand.Var x ∈ stackDup d_y ps.stack := by
    rw [hdupY]; exact List.mem_append.mpr (Or.inl hxmem)
  obtain ⟨d_x', hdepth_x', hlenx'⟩ := stackGetDepth_of_mem hxdup
  have hsmall_x' : d_x' ≤ 15 := by
    rw [hdupY, List.length_append, List.length_cons, List.length_nil] at hlenx'; omega
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  obtain ⟨hcovV, hcovA, hsafe⟩ := hmemsafe wx hwx
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (mstore wx.toNat wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_mstore_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hcovV hcovA hsafe hspillReg hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_mstore_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

/-- **`BodyStepG` for MSTORE** — a 0-output producer for a *memory* store, carrying the per-state
    memory-safety precondition `hmemsafe` (write window covered + below the spill region), the
    invariant the codegen guarantees but that lives outside `StackDiscH`. -/
theorem bodyStepG_mstore
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore addr.toNat val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 32 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 32 ≤ p.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE" → asmStep offsetToPc prog s = asmMstore s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mstore_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey (fun w hw => hmemsafe p v s w hrel hw) hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepG` producer for MSTORE8 (single-byte memory store)

The single-byte twin of the MSTORE producer (`+1` write window instead of `+32`). Same shape;
only `emit_mstore8_sim`/`mstore8` and the `+1` memory-safety bound differ. -/

/-- Headroom preservation for an MSTORE8 (single-byte twin of `stackDisc_mstore_preserve`). -/
theorem stackDisc_mstore8_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {x y : String} {base : List Operand} {name : String}
    {idx j d_y d_x' : Nat} {wx wy : bytes32}
    (hsd : StackDiscH j ps vs)
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
    (hsmall_x' : d_x' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 wx.toNat wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_sstore_eq hname hncomm hnjmp hcompute hops houts hxy hstack0 hnospill_y hlivey
      hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
    have hrev : inst.operands.reverse = [Operand.Var y, Operand.Var x] := by rw [hops]; rfl
    rw [hrev, emitInputPlan_pair_var_eq hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { mstore8 wx.toNat wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    rw [← hstack0]; exact hsd.shallow
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact hz)

theorem stackDisc_mstore8_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {S : List String} {x y : String} {j idx : Nat}
    (hsd : StackDiscH j ps vs)
    (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst vs)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ w, lookupVar x vs = some w →
        w.toNat ≤ vs.memory.size ∧ ((w.toNat + 1 + 31) / 32) * 32 ≤ as.memory.size ∧
        w.toNat + 1 ≤ ps.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
              nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
              nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hxmem : Operand.Var x ∈ ps.stack := stackIsVars_mem hsv hxS
  have hymem : Operand.Var y ∈ ps.stack := stackIsVars_mem hsv hyS
  have hshallow : ps.stack.length ≤ 15 := by have := hsd.shallow; omega
  obtain ⟨d_y, hdepth_y, hleny⟩ := stackGetDepth_of_mem hymem
  have hsmall_y : d_y ≤ 15 := by omega
  have hpeekY : stackPeek d_y ps.stack = Operand.Var y := stackGetDepth_peek hdepth_y
  have hdupY : stackDup d_y ps.stack = ps.stack ++ [Operand.Var y] := by unfold stackDup; rw [hpeekY]
  have hxdup : Operand.Var x ∈ stackDup d_y ps.stack := by
    rw [hdupY]; exact List.mem_append.mpr (Or.inl hxmem)
  obtain ⟨d_x', hdepth_x', hlenx'⟩ := stackGetDepth_of_mem hxdup
  have hsmall_x' : d_x' ≤ 15 := by
    rw [hdupY, List.length_append, List.length_cons, List.length_nil] at hlenx'; omega
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  have hnospill_x : alookup' ps.spilled (Operand.Var x) = none := hsd.noSpill _
  obtain ⟨wx, hwx⟩ := hsd.defined x hxmem
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvx : operandVal vs lo (Operand.Var x) = some wx := hwx
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  obtain ⟨hcovV, hcovA, hsafe⟩ := hmemsafe wx hwx
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 wx.toNat wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwx, hwy]
  have hsim := genRegularInstPlan_mstore8_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute hops
    houts hxy rfl hnospill_y hlivey hdepth_y hsmall_y hleny hnospill_x hlivex hdepth_x' hsmall_x' hlenx'
    hvx hvy hcovV hcovA hsafe hspillReg hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_mstore8_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts hxy rfl
      hnospill_y hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x' hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_sstore_outStack hname hncomm hnjmp hcompute hops houts hxy rfl hnospill_y
      hlivey hdepth_y hsmall_y hnospill_x hlivex hdepth_x' hsmall_x']
    exact hsv

theorem bodyStepG_mstore8
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {x y : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [])
    (hxy : x ≠ y)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hlivex : nextLiveness.contains x = true)
    (hlivey : nextLiveness.contains y = true)
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) (w : bytes32),
        venomAsmRel lo p v s → lookupVar x v = some w →
        w.toNat ≤ v.memory.size ∧ ((w.toNat + 1 + 31) / 32) * 32 ≤ s.memory.size ∧
        w.toNat + 1 ≤ p.alloc.fnEom)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s) :
    BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  have houts0 : (outsOf (inst, idx)).length = 0 := by rw [outsOf, houts]; rfl
  rw [houts0, Nat.add_zero] at hsd
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mstore8_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    (hdispatch v) hops houts hxy hxS hyS hlivex hlivey (fun w hw => hmemsafe p v s w hrel hw) hdisp hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### `BodyStepH` producer for CALLDATACOPY (the first 3-input 0-output producer)

Exercises the demand-decoupled fold at `dem = 1`: a 3-input 0-output op whose 3rd DUP reaches
`original_depth + 2` needs `StackDiscH 1` even though `outsOf = []`. The `dem = 1` input supplies it;
the (net-0) headroom is weakened `StackDiscH (j+1) → StackDiscH j` on the way out. -/

/-- Output stack of a copy: `ps.stack` (unchanged — no output). -/
theorem genRegularInstPlan_copy_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {a b c : String} {base : List Operand} {name : String} {d_z d_y' d_x'' : Nat}
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z) (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y') (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_a : d_x'' ≤ 15) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  rw [releaseDeadSpills_stack]; show base = ps.stack; exact hstack0.symm

/-- Headroom preservation for a copy: `StackDiscH k` unchanged (no output; the memory write preserves vars). -/
theorem stackDisc_copy_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {a b c : String} {base : List Operand} {name : String}
    {idx k d_z d_y' d_x'' : Nat} {bytes : ByteArray} {wa : bytes32}
    (hsd : StackDiscH k ps vs)
    (hname : opcodeToEvmName inst.opcode = some name) (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hstack0 : ps.stack = base)
    (hnospill_c : alookup' ps.spilled (Operand.Var c) = none) (hlivec : nextLiveness.contains c = true)
    (hdepth_c : stackGetDepth (Operand.Var c) ps.stack = some d_z) (hsmall_c : d_z ≤ 15)
    (hnospill_b : alookup' ps.spilled (Operand.Var b) = none) (hliveb : nextLiveness.contains b = true)
    (hdepth_b : stackGetDepth (Operand.Var b) (stackDup d_z ps.stack) = some d_y') (hsmall_b : d_y' ≤ 15)
    (hnospill_a : alookup' ps.spilled (Operand.Var a) = none) (hlivea : nextLiveness.contains a = true)
    (hdepth_a : stackGetDepth (Operand.Var a) (stackDup d_y' (stackDup d_z ps.stack)) = some d_x'') (hsmall_a : d_x'' ≤ 15)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat bytes vs)) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_copy_eq hname hncomm hnjmp hcompute hops houts hab hbc hac hstack0 hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } := by
    have hrev : inst.operands.reverse = [Operand.Var c, Operand.Var b, Operand.Var a] := by rw [hops]; rfl
    rw [hrev, emitInputPlan_triple_var_eq hnospill_c hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { writeMemoryWithExpansion wa.toNat bytes vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + k ≤ 15; rw [← hstack0]; exact hsd.shallow
  · intro z' hz'; show ∃ w, lookupVar z' vs = some w; exact hsd.defined z' (by rw [hstack0]; exact hz')

/-- The `StackIsVars`-aware body step for CALLDATACOPY at demand 1: derives the 3 input depths from
    `StackDiscH 1`, pulls the memory-safety facts from `hmemsafe`, runs the sim, and weakens the
    (unchanged) headroom `StackDiscH (j+1) → StackDiscH j`. -/
theorem stackDisc_calldatacopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_calldatacopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := (⟨vs.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for CALLDATACOPY at demand 1** — the first 3-input 0-output producer, exercising the
    demand-decoupled fold. Carries the CALLDATACOPY semantics (`hstepEqFn`) and per-state memory safety
    (`hmemsafe`) as hypotheses; `dem = 1` supplies the 3rd DUP's reach. -/
theorem bodyStepH_calldatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CALLDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_calldatacopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for CODECOPY at demand 1 — the CODECOPY twin of
    `stackDisc_calldatacopy_step_S` (source `vs.code`, sim `genRegularInstPlan_codecopy_sim`). -/
theorem stackDisc_codecopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "CODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_codecopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := (⟨vs.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for CODECOPY at demand 1** — the CODECOPY twin of `bodyStepH_calldatacopy`; a second
    3-input 0-output producer through the demand-decoupled fold, with source `code`. -/
theorem bodyStepH_codecopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "CODECOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.code.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_codecopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for RETURNDATACOPY at demand 1 — the twin of
    `stackDisc_codecopy_step_S`, with source `vs.returndata` and the extra OOB-safety `hnooobFn`
    (`srcOff + sz ≤ returndata.size`) threaded into the in-bounds sim. -/
theorem stackDisc_returndatacopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "RETURNDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.returndata.readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hnooobFn : ∀ wb wc, lookupVar b vs = some wb → lookupVar c vs = some wc → wb.toNat + wc.toNat ≤ vs.returndata.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  have hnooob : wb.toNat + wc.toNat ≤ vs.returndata.size := hnooobFn wb wc hwb hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.returndata.readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_returndatacopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hsafe hnooob hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := vs.returndata.readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for RETURNDATACOPY at demand 1** — the first copy-family producer with a fault
    branch. The demand-decoupled fold still applies on the in-bounds path: `hnooobFn` (per-state
    `srcOff + sz ≤ returndata.size`) selects the OK case, aligned with Venom (both fault OOB identically). -/
theorem bodyStepH_returndatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "RETURNDATACOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.returndata.readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hnooobFn : ∀ (v : VenomState) wb wc, lookupVar b v = some wb → lookupVar c v = some wc → wb.toNat + wc.toNat ≤ v.returndata.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_returndatacopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc)
    (fun wb wc hb hc => hnooobFn v wb wc hb hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- The `StackIsVars`-aware body step for MCOPY at demand 1 — the memory→memory copy. Twin of
    `stackDisc_returndatacopy_step_S`, but the source is `vs.memory` (bridged via `memoryRel`) and the
    extra facts are source-safety + source-coverage (`hsrcsafeFn`), threaded into the sim. -/
theorem stackDisc_mcopy_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S : List String} {a b c : String} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs) (hsv : StackIsVars S ps)
    (hname : opcodeToEvmName inst.opcode = some "MCOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ wa wb wc, lookupVar a vs = some wa → lookupVar b vs = some wb → lookupVar c vs = some wc →
        stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.memory.readWithPadding wb.toNat wc.toNat) vs))
    (hmemsafe : ∀ wa wc, lookupVar a vs = some wa → lookupVar c vs = some wc →
        wa.toNat ≤ vs.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size ∧
        wa.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsrcsafeFn : ∀ wb wc, lookupVar b vs = some wb → lookupVar c vs = some wc →
        wb.toNat + wc.toNat ≤ ps.alloc.fnEom ∧ ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hsd1 : StackDiscH 1 ps vs := StackDiscH.mono hsd (by omega)
  have hamem : Operand.Var a ∈ ps.stack := stackIsVars_mem hsv haS
  have hbmem : Operand.Var b ∈ ps.stack := stackIsVars_mem hsv hbS
  have hcmem : Operand.Var c ∈ ps.stack := stackIsVars_mem hsv hcS
  obtain ⟨d_z, d_y, d_x, hdepth_c, hsmall_c, hlenc, hdepth_b, hsmall_b, hlenb, hdepth_a, hsmall_a, hlena⟩ :=
    stackDisc_ternopVar_depths (x := a) (y := b) (z := c) hsd1 hab hbc hac hamem hbmem hcmem
  have hnospill_a : alookup' ps.spilled (Operand.Var a) = none := hsd.noSpill _
  have hnospill_b : alookup' ps.spilled (Operand.Var b) = none := hsd.noSpill _
  have hnospill_c : alookup' ps.spilled (Operand.Var c) = none := hsd.noSpill _
  obtain ⟨wa, hwa⟩ := hsd.defined a hamem
  obtain ⟨wb, hwb⟩ := hsd.defined b hbmem
  obtain ⟨wc, hwc⟩ := hsd.defined c hcmem
  have hva : operandVal vs lo (Operand.Var a) = some wa := hwa
  have hvb : operandVal vs lo (Operand.Var b) = some wb := hwb
  have hvc : operandVal vs lo (Operand.Var c) = some wc := hwc
  obtain ⟨hcovV, hcovA, hsafe, hpos, hsize⟩ := hmemsafe wa wc hwa hwc
  obtain ⟨hsrcsafe, hcovS⟩ := hsrcsafeFn wb wc hwb hwc
  have hspillReg : ∀ op off', AssocList.lookup Operand Nat ps.spilled op = some off' → ps.alloc.fnEom ≤ off' := by
    intro op off' h
    have hn : AssocList.lookup Operand Nat ps.spilled op = none := hsd.noSpill op
    rw [hn] at h; exact absurd h (by simp)
  have hstepEq : stepInstBase inst vs = ExecResult.OK (writeMemoryWithExpansion wa.toNat (vs.memory.readWithPadding wb.toNat wc.toNat) vs) :=
    hstepEqFn wa wb wc hwa hwb hwc
  have hsim := genRegularInstPlan_mcopy_sim (offsetToPc := offsetToPc) hname hncomm hnjmp hcompute
    hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c hlenc hnospill_b hliveb hdepth_b hsmall_b
    hlenb hnospill_a hlivea hdepth_a hsmall_a hlena hva hvb hvc hcovV hcovA hcovS hsafe hsrcsafe hpos hsize hspillReg hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_copy_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
      (idx := idx) (bytes := vs.memory.readWithPadding wb.toNat wc.toNat)
      hsd hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c hlivec hdepth_c hsmall_c
      hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_copy_outStack hname hncomm hnjmp hcompute hops houts hab hbc hac rfl hnospill_c
      hlivec hdepth_c hsmall_c hnospill_b hliveb hdepth_b hsmall_b hnospill_a hlivea hdepth_a hsmall_a]
    exact hsv

/-- **`BodyStepH` for MCOPY at demand 1** — the memory→memory copy producer, the last of the copy
    family. The demand-decoupled fold applies with the source read bridged through `memoryRel`
    (source-safety `srcOff + sz ≤ fnEom`) rather than an equality conjunct. -/
theorem bodyStepH_mcopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S : List String} {a b c : String} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MCOPY") (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP) (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Var a, Operand.Var b, Operand.Var c]) (houts : inst.outputs = [])
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hlivea : nextLiveness.contains a = true) (hliveb : nextLiveness.contains b = true) (hlivec : nextLiveness.contains c = true)
    (hstepEqFn : ∀ (v : VenomState) wa wb wc, lookupVar a v = some wa → lookupVar b v = some wb → lookupVar c v = some wc →
        stepInstBase inst v = ExecResult.OK (writeMemoryWithExpansion wa.toNat (v.memory.readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a v = some wa → lookupVar c v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsrcsafeFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wb wc, venomAsmRel lo p v s → lookupVar b v = some wb → lookupVar c v = some wc →
        wb.toNat + wc.toNat ≤ p.alloc.fnEom ∧ ((wb.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      1 (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_mcopy_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute
    hops houts hab hbc hac haS hbS hcS hlivea hliveb hlivec
    (fun wa wb wc ha hb hc => hstepEqFn v wa wb wc ha hb hc)
    (fun wa wc ha hc => hmemsafe p v s wa wc hrel ha hc)
    (fun wb wc hb hc => hsrcsafeFn p v s wb wc hrel hb hc) hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-- LOG output stack = input stack (no outputs, dead-spill release doesn't touch stack). -/
theorem genRegularInstPlan_log_outStack
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {es : List String} {dists : List Nat} {tc : bytes32}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack) :
    (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = ps.stack := by
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths, releaseDeadSpills_stack]

/-- LOG headroom preservation: `StackDiscH k` unchanged (no output; appending a log doesn't touch the
    var environment). LOG analog of `stackDisc_copy_preserve`. -/
theorem stackDisc_log_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {es : List String} {dists : List Nat} {tc : bytes32}
    {k idx : Nat} {L : List Event}
    (hsd : StackDiscH k ps vs)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hnospill : ∀ v ∈ es, alookup' ps.spilled (Operand.Var v) = none)
    (hdepths : emitDepthsOk nextLiveness es dists ps.stack)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := L }) :
    StackDiscH k (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_log_eq hopc hhead hcompute houts rfl hnd hnospill hdepths]
  apply releaseDeadSpills_stackDiscH
  have hstateEq : ({ (emitInputPlan inst.opcode (computeOperands inst) nextLiveness ps).2 with stack := ps.stack } : PlanState)
      = { ps with stack := ps.stack } := by
    rw [hcompute, emitInputPlan_allVars_eq inst.opcode nextLiveness es dists ps hnospill hdepths]
  rw [hstateEq]
  have hgv : gvBodyStep (inst, idx) vs = { ({ vs with logs := L }) with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · exact hsd.shallow
  · intro z' hz'; show ∃ w, lookupVar z' vs = some w; exact hsd.defined z' hz'

/-- The `StackIsVars`-aware LOG body step at demand `n`: derives the emit-depth chain from
    `StackDiscH (j + n)` (`stackDisc_nVar_depths`), runs the sim, weakens the (unchanged) headroom
    `StackDiscH (j + n) → StackDiscH j`. -/
theorem stackDisc_log_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat} {S es : List String} {tc : bytes32} {n j idx : Nat}
    {offset size : bytes32} {topics : List bytes32}
    (hsd : StackDiscH (j + n) ps vs) (hsv : StackIsVars S ps)
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S) (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (htlen : topics.length = n)
    (hvals : (es.map Operand.Var).reverse.map (fun o => operandVal vs lo o) = (offset :: size :: topics).map some)
    (hcov : ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ as.memory.size)
    (hbelow : offset.toNat + size.toNat ≤ ps.alloc.fnEom)
    (hsize : size.toNat < USize.size)
    (hstepEq : stepInstBase inst vs = ExecResult.OK { vs with logs := vs.logs ++ [({ logger := vs.callCtx.contract, topics := topics, data := (vs.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] })
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1)) :
    (∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) as' ∧
            as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).1).length)
    ∧ StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs)
    ∧ StackIsVars S (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2 := by
  have hmemes : ∀ w ∈ es, Operand.Var w ∈ ps.stack := fun w hw => stackIsVars_mem hsv (hesS w hw)
  have hnospill : ∀ w ∈ es, alookup' ps.spilled (Operand.Var w) = none := fun w _ => hsd.noSpill _
  have hsdn : StackDiscH (es.length - 2) ps vs := by
    rw [hlenes]; exact StackDiscH.mono hsd (by omega)
  obtain ⟨dists, hdepths⟩ := stackDisc_nVar_depths es hsdn hnd hmemes hlive
  have hsim := genRegularInstPlan_log_sim (offsetToPc := offsetToPc) hopc hhead hcompute houts rfl hnd
    hnospill hdepths hlenes htc htlen hvals hcov hbelow hsize hn hrel hblock
  refine ⟨gvBodyStep_of_ok hstepEq hsim, ?_, ?_⟩
  · have hpres := stackDisc_log_preserve (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
      (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel) (idx := idx)
      hsd hopc hhead hcompute houts hnd hnospill hdepths hstepEq
    exact StackDiscH.mono hpres (by omega)
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator curBbLabel ps).2.stack = S.map Operand.Var
    rw [genRegularInstPlan_log_outStack hopc hhead hcompute houts hnd hnospill hdepths]
    exact hsv

/-- **`BodyStepH` for LOG at demand `n`** — the first variable-arity producer through the demand fold.
    The demand `n` (= topic count = `es.length - 2`) supplies the reach of the deepest input DUP. A
    per-state `hlogFn` provides the operand values, memory safety, and LOG semantics for each Venom
    state (the LOG analog of the copies' `hstepEqFn`/`hmemsafe`). -/
theorem bodyStepH_log
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {S es : List String} {tc : bytes32} {n idx : Nat}
    (hopc : inst.opcode = Opcode.LOG) (hhead : inst.operands.head! = Operand.Lit tc)
    (hcompute : computeOperands inst = es.map Operand.Var) (houts : inst.outputs = [])
    (hnd : es.Nodup) (hesS : ∀ v ∈ es, v ∈ S) (hlive : ∀ v ∈ es, nextLiveness.contains v = true)
    (hlenes : es.length = n + 2) (htc : tc.toNat = n) (hn : n ≤ 4)
    (hlogFn : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s →
        ∃ offset size topics,
          topics.length = n ∧
          (es.map Operand.Var).reverse.map (fun o => operandVal v lo o) = (offset :: size :: topics).map some ∧
          ((offset.toNat + size.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
          offset.toNat + size.toNat ≤ p.alloc.fnEom ∧
          size.toNat < USize.size ∧
          stepInstBase inst v = ExecResult.OK { v with logs := v.logs ++ [({ logger := v.callCtx.contract, topics := topics, data := (v.memory.readWithPadding offset.toNat size.toNat).toList } : Event)] }) :
    BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false nextIsTerminator curBbLabel p)
      n (inst, idx) S := by
  intro p v s j hsd hsv hrel hblock
  obtain ⟨offset, size, topics, htlen, hvals, hcov, hbelow, hsize, hstepEq⟩ := hlogFn p v s hrel
  obtain ⟨hsim, hsd', hsv'⟩ := stackDisc_log_step_S (idx := idx) hsd hsv hopc hhead hcompute houts
    hnd hesS hlive hlenes htc hn htlen hvals hcov hbelow hsize hstepEq hrel hblock
  have houtsnil : outsOf (inst, idx) = [] := by rw [outsOf, houts]
  exact ⟨hsim, hsd', by rw [houtsnil, List.append_nil]; exact hsv'⟩

/-! ### Mixed-arity demonstration (0- and 1-output ops in one body)

The payoff of the general fold: a 1-output binop (bridged via `bodyStepG_of_bodyStep`) and a 0-output
store chain via `bodyStepsReadyG_cons`, then fold through `genBlockBodyG_sim_inv` into a whole
2-instruction body sim — proving 0- and 1-output ops genuinely compose in one body. -/

/-- A commutative var-binop (1 output `o1`) then an SSTORE (0 outputs) chain via `bodyStepsReadyG_cons`:
    the binop ready at `S`, the store ready at `S ++ [o1]` (its `outsOf = []` keeps `S ++ [o1]`). -/
theorem bodyStepsReadyG_binop_store
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 n1 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "SSTORE") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execWrite2 (fun key val s => sstore key val s) i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1])
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s) :
    BodyStepsReadyG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      [(i1, idx1), (i2, idx2)] S := by
  have hstep1 : BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (i1, idx1) S :=
    bodyStepG_of_bodyStep houts1
      (bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
        (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
        (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1)
  have hstep2 : BodyStepG lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (i2, idx2) (S ++ [o1]) :=
    bodyStepG_sstore (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
      (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
      (nextIsTerminator := true) (curBbLabel := curBbLabel)
      hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S hlivex2 hlivey2 hdisp2
  have hout1 : outsOf (i1, idx1) = [o1] := by rw [outsOf, houts1]
  refine bodyStepsReadyG_cons hstep1 ?_
  rw [hout1]
  exact bodyStepsReadyG_cons hstep2 bodyStepsReadyG_nil

/-- **End-to-end mixed-arity body sim.** Feeds `bodyStepsReadyG_binop_store` through
    `genBlockBodyG_sim_inv`: a binop (1 output) then a store (0 outputs) run as one body, ending OK,
    still related, discipline at 0, stack now `S ++ [o1]` (the store added nothing). Headroom is 1 —
    `(l.flatMap outsOf).length = ([o1] ++ []).length`. The concrete demonstration that 0- and 1-output
    ops compose end-to-end in the general fold. -/
theorem genBlockBodyG_binop_store_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 x2 y2 n1 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "SSTORE") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hdispatch2 : ∀ v, stepInstBase i2 v = execWrite2 (fun key val s => sstore key val s) i2 v)
    (hops2 : i2.operands = [Operand.Var x2, Operand.Var y2]) (houts2 : i2.outputs = [])
    (hxy2 : x2 ≠ y2) (hx2S : x2 ∈ S ++ [o1]) (hy2S : y2 ∈ S ++ [o1])
    (hlivex2 : nextLiveness.contains x2 = true) (hlivey2 : nextLiveness.contains y2 = true)
    (hdisp2 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "SSTORE" → asmStep offsetToPc prog s = asmSstore s)
    (hsd0 : StackDiscH (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).flatMap outsOf).length ps0 vs0)
    (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].flatMap outsOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyG_binop_store (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx1 := idx1) (idx2 := idx2) (curBbLabel := curBbLabel)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
    hname2 hncomm2 hnjmp2 hcompute2 hdispatch2 hops2 houts2 hxy2 hx2S hy2S hlivex2 hlivey2 hdisp2
  exact genBlockBodyG_sim_inv
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ### Demand-fold mixed-arity demonstration (1-output binop then a 3-input 0-output copy)

The demand-fold (`genBlockBodyH_sim_inv`) analog of `genBlockBodyG_binop_store_sim`. The store demo
runs through the output-count fold, which structurally cannot carry a copy (a 3-input 0-output op needs
more headroom than its output count grants). This threads a commutative binop (1 output) then a
CALLDATACOPY (3 inputs, 0 outputs) through the *demand* fold with `dem = fun _ => 1` — so the required
headroom is `Σ dem = 2`, one more than the output count `(l.flatMap outsOf).length = 1`. That extra
unit is exactly the reach the copy's deepest DUP needs and the output count does not pay for. -/
theorem bodyStepsReadyH_binop_calldatacopy
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 n1 a2 b2 c2 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "CALLDATACOPY") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hops2 : i2.operands = [Operand.Var a2, Operand.Var b2, Operand.Var c2]) (houts2 : i2.outputs = [])
    (hab2 : a2 ≠ b2) (hbc2 : b2 ≠ c2) (hac2 : a2 ≠ c2)
    (ha2S : a2 ∈ S ++ [o1]) (hb2S : b2 ∈ S ++ [o1]) (hc2S : c2 ∈ S ++ [o1])
    (hlivea2 : nextLiveness.contains a2 = true) (hliveb2 : nextLiveness.contains b2 = true) (hlivec2 : nextLiveness.contains c2 = true)
    (hstepEqFn2 : ∀ (v : VenomState) wa wb wc, lookupVar a2 v = some wa → lookupVar b2 v = some wb → lookupVar c2 v = some wc →
        stepInstBase i2 v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe2 : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a2 v = some wa → lookupVar c2 v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size) :
    BodyStepsReadyH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      (fun _ => 1) [(i1, idx1), (i2, idx2)] S := by
  have hstep1 : BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      1 (i1, idx1) S :=
    bodyStepH_of_bodyStepG (by simp [outsOf, houts1])
      (bodyStepG_of_bodyStep houts1
        (bodyStep_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
          (offsetToPc := offsetToPc) (prog := prog) (idx := idx1) (nextLiveness := nextLiveness)
          (curBbLabel := curBbLabel) hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1))
  have hstep2 : BodyStepH lo offsetToPc prog
      (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      1 (i2, idx2) (S ++ [o1]) :=
    bodyStepH_calldatacopy (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn) (lo := lo)
      (offsetToPc := offsetToPc) (prog := prog) (idx := idx2) (nextLiveness := nextLiveness)
      (nextIsTerminator := true) (curBbLabel := curBbLabel)
      hname2 hncomm2 hnjmp2 hcompute2 hops2 houts2 hab2 hbc2 hac2 ha2S hb2S hc2S hlivea2 hliveb2 hlivec2 hstepEqFn2 hmemsafe2
  refine bodyStepsReadyH_cons hstep1 ?_
  have hout1 : outsOf (i1, idx1) = [o1] := by rw [outsOf, houts1]
  rw [hout1]
  exact bodyStepsReadyH_cons hstep2 bodyStepsReadyH_nil

/-- **End-to-end demand-fold mixed-arity body sim.** Feeds `bodyStepsReadyH_binop_calldatacopy` through
    `genBlockBodyH_sim_inv`: a binop (1 output) then a CALLDATACOPY (3 inputs, 0 outputs) run as one
    body, ending OK, still related, discipline at 0, stack now `S ++ [o1]` (the copy added nothing).
    Headroom is `Σ dem = 2` — strictly more than the output count 1 — the concrete witness that the
    demand-decoupled fold composes a 3-input 0-output copy that the output-count fold cannot. -/
theorem genBlockBodyH_binop_calldatacopy_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {i1 i2 : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {S : List String} {x1 y1 o1 n1 a2 b2 c2 : String} {idx1 idx2 : Nat}
    {f1 : bytes32 → bytes32 → bytes32}
    {ps0 : PlanState} {vs0 : VenomState} {as0 : AsmState}
    (hname1 : opcodeToEvmName i1.opcode = some n1) (hcomm1 : isCommutative i1.opcode = true)
    (hdisp1' : ∀ v, stepInstBase i1 v = execPure2 f1 i1 v)
    (hops1 : i1.operands = [Operand.Var x1, Operand.Var y1]) (houts1 : i1.outputs = [o1])
    (hxy1 : x1 ≠ y1) (hx1S : x1 ∈ S) (hy1S : y1 ∈ S) (ho1S : o1 ∉ S)
    (hlive1 : nextLiveness.contains o1 = true) (hlivex1 : nextLiveness.contains x1 = true)
    (hlivey1 : nextLiveness.contains y1 = true)
    (hdisp1 : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp n1 → asmStep offsetToPc prog s = asmBinop f1 s)
    (hname2 : opcodeToEvmName i2.opcode = some "CALLDATACOPY") (hncomm2 : isCommutative i2.opcode = false)
    (hnjmp2 : i2.opcode ≠ Opcode.JMP) (hcompute2 : computeOperands i2 = i2.operands.reverse)
    (hops2 : i2.operands = [Operand.Var a2, Operand.Var b2, Operand.Var c2]) (houts2 : i2.outputs = [])
    (hab2 : a2 ≠ b2) (hbc2 : b2 ≠ c2) (hac2 : a2 ≠ c2)
    (ha2S : a2 ∈ S ++ [o1]) (hb2S : b2 ∈ S ++ [o1]) (hc2S : c2 ∈ S ++ [o1])
    (hlivea2 : nextLiveness.contains a2 = true) (hliveb2 : nextLiveness.contains b2 = true) (hlivec2 : nextLiveness.contains c2 = true)
    (hstepEqFn2 : ∀ (v : VenomState) wa wb wc, lookupVar a2 v = some wa → lookupVar b2 v = some wb → lookupVar c2 v = some wc →
        stepInstBase i2 v = ExecResult.OK (writeMemoryWithExpansion wa.toNat ((⟨v.callCtx.calldata.toArray⟩ : ByteArray).readWithPadding wb.toNat wc.toNat) v))
    (hmemsafe2 : ∀ (p : PlanState) (v : VenomState) (s : AsmState) wa wc, venomAsmRel lo p v s → lookupVar a2 v = some wa → lookupVar c2 v = some wc →
        wa.toNat ≤ v.memory.size ∧ ((wa.toNat + wc.toNat + 31) / 32) * 32 ≤ s.memory.size ∧
        wa.toNat + wc.toNat ≤ p.alloc.fnEom ∧ 0 < wc.toNat ∧ wc.toNat < USize.size)
    (hsd0 : StackDiscH 2 ps0 vs0)
    (hsv0 : StackIsVars S ps0) (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
        (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                       (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1)) :
    ∃ as', runAsm (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) as' ∧
           as'.pc = as0.pc + (executePlan (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).1).length ∧
           StackDiscH 0 (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2
             (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl (fun v w => gvBodyStep w v) vs0) ∧
           StackIsVars (S ++ [(i1, idx1), (i2, idx2)].flatMap outsOf) (([(i1, idx1), (i2, idx2)] : List (Instruction × Nat)).foldl
              (fun acc w => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).1,
                             (generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel acc.2).2)) ([], ps0)).2 := by
  have hready := bodyStepsReadyH_binop_calldatacopy (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (lo := lo) (offsetToPc := offsetToPc) (prog := prog) (idx1 := idx1) (idx2 := idx2) (curBbLabel := curBbLabel)
    hname1 hcomm1 hdisp1' hops1 houts1 hxy1 hx1S hy1S ho1S hlive1 hlivex1 hlivey1 hdisp1
    hname2 hncomm2 hnjmp2 hcompute2 hops2 houts2 hab2 hbc2 hac2 ha2S hb2S hc2S hlivea2 hliveb2 hlivec2 hstepEqFn2 hmemsafe2
  exact genBlockBodyH_sim_inv
    (fun w p => generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
    (fun _ => 1) [(i1, idx1), (i2, idx2)] S ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock

/-! ## Permutation-threading body fold (active-swap regime)

The active-swap counterpart of `genBlockBody_sim_inv_S`: threads `StackPerm` (up to permutation)
instead of the exact-order `StackIsVars`, so it admits per-instruction steps that *reorder* the stack
(the active optimistic swap). Identical fold structure — the per-instruction readiness predicate
`BodyStepsReadyP` pins `S` per position and concludes `StackPerm (S ++ [outOf x])`; the active-swap
step `genRegularInstPlan_commBinopVar_sim_swap` (+ `optimisticSwapPlan_stackPerm`) discharges each
entry. -/
def BodyStepsReadyP (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst) (gp : Instruction × Nat → PlanState → List StackOp × PlanState) :
    List (Instruction × Nat) → List String → Prop
  | [], _ => True
  | x :: xs, S =>
      (∀ (p : PlanState) (v : VenomState) (s : AsmState) (j : Nat),
        StackDiscH (j + 1) p v → StackPerm S p → venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        (∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
               venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
               s'.pc = s.pc + (executePlan (gp x p).1).length) ∧
        StackDiscH j (gp x p).2 (gvBodyStep x v) ∧
        StackPerm (S ++ [outOf x]) (gp x p).2)
      ∧ BodyStepsReadyP lo offsetToPc prog gp xs (S ++ [outOf x])

/-- **Permutation-threading body fold.** As `genBlockBody_sim_inv_S` but with `StackPerm` (so it
    covers blocks whose instructions reorder the stack via the optimistic swap). Folds
    `BodyStepsReadyP` one entry per instruction, threading `StackDiscH` (`l.length → 0`) and
    `StackPerm` (`S0 → S0 ++ l.map outOf`). -/
theorem genBlockBody_sim_inv_P {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (l : List (Instruction × Nat)) :
    ∀ (S0 : List String) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState),
      BodyStepsReadyP lo offsetToPc prog gp l S0 →
      StackDiscH l.length ps0 vs0 → StackPerm S0 ps0 → venomAsmRel lo ps0 vs0 as0 →
      asmBlockAt prog as0.pc
        (executePlan (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) →
      ∃ as', runAsm (executePlan (l.foldl
                (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length
               offsetToPc prog as0 = AsmResult.AsmOK as' ∧
             venomAsmRel lo (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) as' ∧
             as'.pc = as0.pc + (executePlan (l.foldl
               (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length ∧
             StackDiscH 0
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2
               (l.foldl (fun v x => gvBodyStep x v) vs0) ∧
             StackPerm (S0 ++ l.map outOf)
               (l.foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 := by
  induction l with
  | nil =>
    intro S0 ps0 vs0 as0 _ hsd0 hsv0 hrel0 _
    refine ⟨as0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
    · simpa using hsd0
    · simpa using hsv0
  | cons x xs ih =>
    intro S0 ps0 vs0 as0 hready hsd0 hsv0 hrel0 hblock
    obtain ⟨hstepx, hready_xs⟩ := hready
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2)) ([], ps0)
        = ((gp x ps0).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
              ([], (gp x ps0).2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_ops_acc (fun p y => gp y p) xs (gp x ps0).1 (gp x ps0).2
    have keyv : (x :: xs).foldl (fun v y => gvBodyStep y v) vs0
        = xs.foldl (fun v y => gvBodyStep y v) (gvBodyStep x vs0) := by
      simp only [List.foldl_cons]
    simp only [key, keyv, List.map_cons] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨⟨as1, hrun1, hrel1, hpc1⟩, hsd1, hsv1⟩ := hstepx ps0 vs0 as0 xs.length hsd0 hsv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (gp y acc.2).1, (gp y acc.2).2))
          ([], (gp x ps0).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc', hsd', hsv'⟩ :=
      ih (S0 ++ [outOf x]) (gp x ps0).2 (gvBodyStep x vs0) as1 hready_xs hsd1 hsv1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_, hsd', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append, hpc', hpc1]; omega
    · simpa [List.append_assoc] using hsv'

/-! ## Terminator split of the plan body fold

`generateBlockPlan`'s `instOps` runs over `nonParamInsts bb = front ++ [term]`. The fold splits into
the front (non-terminator) fold followed by one terminator step at index `front.length` — the asm
runs the body via `genBlockBody_sim` and the terminator separately (`resolved_jump_sim` etc.), and
`execBlock` peels the front (`execBlock_body_prefix`) then steps the terminator
(`execBlock_step_term`). This is the plan-side split feeding that dispatch. -/

theorem instOps_fold_split (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (term : Instruction) (ps2 : PlanState) :
    (front ++ [term]).zipIdx.foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)
      = (((front.zipIdx).foldl
            (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).1
          ++ (gp (term, front.length)
                ((front.zipIdx).foldl
                  (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).2).1,
         (gp (term, front.length)
                ((front.zipIdx).foldl
                  (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps2)).2).2) := by
  rw [List.zipIdx_append]
  simp only [Nat.zero_add, List.foldl_append, List.zipIdx_cons, List.zipIdx_nil,
    List.foldl_cons, List.foldl_nil]

/-! ## Generic-`offsetToPc` plan sequencing

`plan_seq_sim` (PlanSim) is stated for the empty `offsetToPc`; the assembly threads the whole-
function `offsetToPc` (so cross-block `JUMP`/`JUMPI` resolve), and every body lemma here is already
`offsetToPc`-generic. `plan_seq_sim'` is the same sequencing under a generic `offsetToPc` — chains
two consecutive `AsmOK` plan segments (prefix→body, body→terminator) via the generic
`runAsm_compose`. -/

theorem plan_seq_sim' {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} {vs : VenomState} {ps2 : PlanState} {as as1 as2 : AsmState}
    {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h1pc : as1.pc = as.pc + (executePlan ops1).length)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmOK as2)
    (h2rel : venomAsmRel lo ps2 vs as2)
    (h2pc : as2.pc = as1.pc + (executePlan ops2).length) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmOK as2 ∧
    venomAsmRel lo ps2 vs as2 ∧
    as2.pc = as.pc + (executePlan (ops1 ++ ops2)).length := by
  rw [executePlan_append, List.length_append]
  exact ⟨runAsm_compose h1run h2run, h2rel, by rw [h2pc, h1pc]; omega⟩

/-- Sequencing into a halting terminator: the body plan `ops1` runs to `AsmOK as1`, then the
    terminator plan `ops2` halts. The whole `ops1 ++ ops2` halts at the same state. The arm-carrying
    counterpart of `plan_seq_sim'` for the `Halt` branch (`genInstPlan_sim_stop`), via the generic
    `runAsm_add_ok`. -/
theorem asm_seq_halt {prog : List AsmInst} {offsetToPc : AssocList Nat Nat} {as as1 as2 : AsmState}
    {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmHalt as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmHalt as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a reverting terminator (`Abort RevertAbort` ↦ `AsmRevert`). -/
theorem asm_seq_revert {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmRevert as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmRevert as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a faulting terminator (`Abort ExHaltAbort` / INVALID ↦ `AsmFault`). -/
theorem asm_seq_fault {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmFault as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmFault as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-- Sequencing into a non-halting (`OK`) terminator (e.g. `JUMP`). Unlike `plan_seq_sim'` this
    needs no `pc` constraint — a jumping terminator's `pc` is not sequential — so it is the right
    glue for the *final* segment. -/
theorem asm_seq_ok {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {as as1 as2 : AsmState} {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as = AsmResult.AsmOK as1)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1 = AsmResult.AsmOK as2) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as = AsmResult.AsmOK as2 := by
  rw [executePlan_append, List.length_append, runAsm_add_ok h1run]; exact h2run

/-! ## Prefix + body composition (`[SOLabel] ++ body`)

The first two segments of a block's plan: the `JUMPDEST` prefix (`soLabel_sim`) sequenced with the
non-terminator body (`genBlockBody_sim`) via `plan_seq_sim'`, splitting the program coverage with
`asmBlockAt_append`. Running `[SOLabel l] ++ body` from `as0` simulates the plan after the body,
with the Venom side at `execBodyThread`'s end state `sEnd`. The remaining segment is the
terminator (handled by `instOps_fold_split` + the terminator's own sim). -/

theorem genBlockPrefixBody_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
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
  obtain ⟨as', h2run, h2rel, h2pc⟩ :=
    genBlockBody_sim gp front 0 ps0 vs0 sEnd as1 hstep h1rel hthread hbody'
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Invariant-threading prefix-body sim** — the body half of the per-block `hsim` builder. As
    `genBlockPrefixBody_sim` but driven by `BodyStepsReady` (the per-instruction steps discharged
    from `StackDiscH`+`StackIsVars`, e.g. via `stackDisc_commBinopVar_step_S`/`stackDisc_unopVar_step_S`)
    instead of a uniform `venomAsmRel`-only `hstep`. Runs the block's `SOLabel` prefix then the body
    via `genBlockBody_sim_inv_S`, landing the asm at `sEnd` (the `gvBodyStep` fold is `sEnd` by
    `execBodyThread_eq_gvFold`). The terminator is composed on top by the caller via the
    `genBlockAsm_*_sim` lemmas to produce the full `hsim`. -/
theorem genBlockPrefixBody_sim_inv {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState)
    (hready : BodyStepsReady lo offsetToPc prog gp (front.zipIdx 0) S0)
    (hsd0 : StackDiscH (front.zipIdx 0).length ps0 vs0)
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
    genBlockBody_sim_inv_S gp (front.zipIdx 0) S0 ps0 vs0 as1 hready hsd0 hsv0 h1rel hbody'
  rw [execBodyThread_eq_gvFold front 0 vs0 sEnd hthread] at h2rel
  exact ⟨as', plan_seq_sim' h1run h1pc h2run h2rel h2pc⟩

/-- **Body block ending in a JMP** — the OK-terminator (non-halting) counterpart of the
    `genBlockSimulation_body_{halt,revert,fault}` family. Runs the block's `SOLabel` prefix + body
    (via `genBlockPrefixBody_sim_inv`) then the resolved `[push-label target ; JUMP]` (via
    `block_jmp_sim`), landing at the successor block's entry index `idx` (`AsmOK`, pc = `idx`) still
    related to the post-body Venom/plan state. This is exactly `hfsim_jmp_then_*`'s `hentryAsm`
    (the entry-block arm) for an entry block that *does work before jumping* — `block_jmp_sim` already
    accepts a prefix run of any length, so the body fold composes onto it directly. The Venom JMP
    step (`OK (jumpTo target …)`) is supplied by the caller via `hfsim_jmp_then_*`'s `heterm_step`;
    `venomAsmRel` is currentBb-independent so it carries through the jump. -/
theorem genBlockPrefixBody_then_jmp_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} {offsets : AssocList String Nat}
    (l target : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (S0 : List String)
    (ps0 : PlanState) (vs0 sEnd : VenomState) (as0 : AsmState) (off idx : Nat)
    (hready : BodyStepsReady lo offsetToPc prog gp (front.zipIdx 0) S0)
    (hsd0 : StackDiscH (front.zipIdx 0).length ps0 vs0)
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)).length)
    (hpc1 : as0.pc + bodyLen < prog.length)
    (hpush : prog.get ⟨as0.pc + bodyLen, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as0.pc + bodyLen + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + bodyLen + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asm', runAsm (bodyLen + 2) offsetToPc prog as0 = AsmResult.AsmOK asm' ∧
            venomAsmRel lo ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd asm' ∧
            asm'.pc = idx := by
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBody_sim_inv l gp front S0 ps0 vs0 sEnd as0 hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  have hpc1' : asMid.pc < prog.length := by rw [hbpc]; exact hpc1
  have hpush' : prog.get ⟨asMid.pc, hpc1'⟩ = resolveInst offsets (AsmInst.AsmPushLabel target) := by
    have he : (⟨asMid.pc, hpc1'⟩ : Fin prog.length) = ⟨as0.pc + bodyLen, hpc1⟩ := Fin.ext hbpc
    rw [he]; exact hpush
  have hpc2' : asMid.pc + 1 < prog.length := by rw [hbpc]; exact hpc2
  have hjump' : prog.get ⟨asMid.pc + 1, hpc2'⟩ = AsmInst.AsmOp "JUMP" := by
    have he : (⟨asMid.pc + 1, hpc2'⟩ : Fin prog.length) = ⟨as0.pc + bodyLen + 1, hpc2⟩ :=
      Fin.ext (congrArg (· + 1) hbpc)
    rw [he]; exact hjump
  exact block_jmp_sim hbrun hbrel hpc1' hpush' hoff_lk hoff hpc2' hjump' hidx_lk

/-! ## Venom side: runBlock reduces to execBlock at the terminator

The Venom counterpart of `genBlockPrefixBody_sim`. For a phi-free block whose instructions are the
non-terminator body `front` followed by the terminator `term`, `runBlock` (no phi prefix, so just
`execBlock` from `instIdx 0` — `runBlock_no_phi`) peels `front` (`execBlock_body_prefix`) and lands
on `execBlock` of the terminator at the threaded end state `sEnd`. The caller then applies
`execBlock_step_term_*` to dispatch the terminator into its `Halt`/`OK`/`Abort` arm. -/

/-- `execBodyThread` leaves `instIdx` at `start + body.length` (each step sets it to the next
    index), so after the body the terminator sits at `getInstruction bb (start + body.length)`. -/
theorem execBodyThread_instIdx (body : List Instruction) :
    ∀ (start : Nat) (s sEnd : VenomState), s.instIdx = start →
    execBodyThread body start s = some sEnd → sEnd.instIdx = start + body.length := by
  induction body with
  | nil =>
    intro start s sEnd hidx hthread
    simp only [execBodyThread] at hthread
    obtain rfl := Option.some.inj hthread
    simpa using hidx
  | cons inst rest ih =>
    intro start s sEnd _ hthread
    simp only [execBodyThread] at hthread
    cases hstep : stepInstBase inst s with
    | OK s' =>
      rw [hstep] at hthread
      have := ih (start + 1) { s' with instIdx := start + 1 } sEnd rfl hthread
      rw [this, List.length_cons]; omega
    | IntRet _ _ => rw [hstep] at hthread; simp at hthread
    | Halt _ => rw [hstep] at hthread; simp at hthread
    | Abort _ _ => rw [hstep] at hthread; simp at hthread
    | Error _ => rw [hstep] at hthread; simp at hthread

/-- One `execBlock` step on an instruction whose Venom step *directly* halts (STOP/RETURN/SINK —
    `stepInstBase = Halt`, not `OK`-then-`halted`). The existing `execBlock_step_term_*` lemmas only
    cover the `OK` branch; this is the `Halt` match arm. -/
theorem execBlock_step_halt (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Halt s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Halt s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step on an instruction whose Venom step *directly* aborts (REVERT ↦
    `RevertAbort`, faulting opcodes ↦ `ExHaltAbort` — `stepInstBase = Abort`). The `Abort` match
    arm. -/
theorem execBlock_step_abort (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction) (a : AbortType)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Abort a s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Abort a s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step whose Venom step internally returns (`stepInstBase = IntRet` — RET). -/
theorem execBlock_step_intret (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s s' : VenomState) (inst : Instruction) (vals : List bytes32)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.IntRet vals s') :
    execBlock (fuel' + 1) ctx bb s = ExecResult.IntRet vals s' := by
  simp only [execBlock, hget, hstep]

/-- One `execBlock` step whose Venom step errors (`stepInstBase = Error`). -/
theorem execBlock_step_error (fuel' : Nat) (ctx : VenomContext) (bb : BasicBlock)
    (s : VenomState) (inst : Instruction) (e : String)
    (hget : getInstruction bb s.instIdx = some inst)
    (hstep : stepInstBase inst s = ExecResult.Error e) :
    execBlock (fuel' + 1) ctx bb s = ExecResult.Error e := by
  simp only [execBlock, hget, hstep]

theorem runBlock_to_term (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + restFuel) ctx bb s = execBlock restFuel ctx bb sEnd := by
  rw [runBlock_no_phi (front.length + restFuel) ctx bb s hd tl (hbb.trans hcons) hphi]
  refine execBlock_body_prefix ctx bb restFuel front 0 { s with instIdx := 0 } sEnd rfl ?_ hnonterm
    hthread
  intro j hj
  rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]

/-- `getInstruction` of the terminator: `bb.instructions = front ++ [term]` puts `term` at index
    `front.length`, which is exactly where `execBodyThread` leaves `instIdx`. -/
theorem getInstruction_term (bb : BasicBlock) (front : List Instruction) (term : Instruction)
    (hbb : bb.instructions = front ++ [term]) :
    getInstruction bb front.length = some term := by
  rw [getInstruction_eq, hbb, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Venom-side `Halt` arm: a phi-free block `front ++ [term]` whose terminator halts directly
    (`stepInstBase term sEnd = Halt sEnd'` — STOP/RETURN/SINK) returns `Halt sEnd'`, given enough
    fuel. Combines `runBlock_to_term` (peel the body) with `execBlock_step_halt` (step the
    terminator), locating it via `execBodyThread_instIdx`. -/
theorem runBlock_halt (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Halt sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_halt extraFuel ctx bb sEnd sEnd' term hget hterm_step

/-- Venom-side `Abort` arm (REVERT ↦ `RevertAbort`, faulting opcodes ↦ `ExHaltAbort`): same as
    `runBlock_halt` with `execBlock_step_abort`. -/
theorem runBlock_abort (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState) (a : AbortType)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort a sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Abort a sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_abort extraFuel ctx bb sEnd sEnd' term a hget hterm_step

/-- Venom-side `OK` arm: a non-halting terminator (`stepInstBase = OK`, not halted — e.g. JMP, which
    sets `currentBb`) leaves `runBlock = OK sEnd'`, given enough fuel. Combines `runBlock_to_term`
    with `execBlock_step_term_ok`. -/
theorem runBlock_ok (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false) :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.OK sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_term_ok extraFuel ctx bb sEnd sEnd' term hget hterm_step hterm_isterm hnohalt

/-- Venom-side `IntRet` arm: a terminator that internally returns (`stepInstBase = IntRet` — RET)
    leaves `runBlock = IntRet`, given enough fuel. -/
theorem runBlock_intret (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState) (vals : List bytes32)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.IntRet vals sEnd') :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.IntRet vals sEnd' := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_intret extraFuel ctx bb sEnd sEnd' term vals hget hterm_step

/-- Venom-side `Error` arm: a terminator that errors leaves `runBlock = Error`, given enough fuel. -/
theorem runBlock_error (ctx : VenomContext) (bb : BasicBlock) (extraFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (e : String)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Error e) :
    runBlock (front.length + (extraFuel + 1)) ctx bb s = ExecResult.Error e := by
  rw [runBlock_to_term ctx bb (extraFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    simpa using execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
  have hget : getInstruction bb sEnd.instIdx = some term := by
    rw [hidx]; exact getInstruction_term bb front term hbb
  exact execBlock_step_error extraFuel ctx bb sEnd term e hget hterm_step

/-- Venom-side insufficient-fuel arm: `fuel ≤ front.length` means `runBlock` runs out before the
    terminator, returning `Error`. Lands the discharge in `genBlockSimulation`'s vacuous `_ => True`
    branch. Completes the `runBlock` fuel characterization (`runBlock_halt`/`abort` for sufficient
    fuel, this for insufficient). -/
theorem runBlock_oof (ctx : VenomContext) (bb : BasicBlock) (fuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hfuel : fuel ≤ front.length) :
    ∃ e, runBlock fuel ctx bb s = ExecResult.Error e := by
  rw [runBlock_no_phi fuel ctx bb s hd tl (hbb.trans hcons) hphi]
  refine execBlock_oof ctx bb front 0 fuel { s with instIdx := 0 } sEnd rfl ?_ hnonterm hthread hfuel
  intro j hj
  rw [Nat.zero_add, getInstruction_eq, hbb, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]

/-! ## Venom-side block-arm packaging (the `∀ f'` outcome for the CFG walk)

`hfsim_jmp_then_terminal` (and the CFG walk's `hbsim`) want the per-block `runBlock` outcome quantified
over *all* fuel `f'`: the real outcome when fuel suffices, and the vacuous `Error` (insufficient fuel)
arm otherwise. These package the `runBlock_*` decomposition + `runBlock_oof` into that `∀ f'` form. -/

/-- **The `∀ f'` outcome of a JMP (non-halting terminator) block** — exactly
    `hfsim_jmp_then_terminal`'s `hentry`. For sufficient fuel the block runs to `sEnd'` (`runBlock_ok`,
    `halted = false`); for insufficient fuel it runs out (`runBlock_oof` ⇒ `Error` ⇒ the vacuous arm).
    Pure Venom semantics — no codegen. -/
theorem runBlock_jmp_arm (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false) :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' => s' = sEnd' ∧ s'.halted = false
      | ExecResult.Halt _ => False
      | ExecResult.Abort _ _ => False
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_ok ctx bb extra front term hd tl s sEnd sEnd' hbb hcons hphi hnonterm hthread
      hterm_step hterm_isterm hnohalt]
    exact ⟨rfl, hnohalt⟩

/-- **The `∀ f'` outcome of a halting terminal block** (`stepInstBase term sEnd = Halt sEnd'` —
    STOP/RETURN/SINK) — `hfsim_jmp_then_terminal`'s `hterm` for the `Halt` case. Factors `hterm` into
    the Venom-side `runBlock_halt` (sufficient fuel ⇒ `Halt sEnd'`; insufficient ⇒ `Error` ⇒ vacuous)
    and the asm correspondence `hasm` (the terminal block's asm running from `asMid` to `AsmHalt`, at
    the residual budget). The `OK`/`Abort` match arms are never reached (a Halt-terminator block's
    `runBlock` is only `Halt` or `Error`), so they need no proof. The remaining input is `hasm` — the
    terminal block's whole-program asm sim. -/
theorem hterm_halt {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_halt ctx bb extra front term hd tl s sEnd sEnd' hbb hcons hphi hnonterm hthread
      hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a reverting terminal block** (`stepInstBase term sEnd = Abort RevertAbort
    sEnd'` — REVERT) — `hfsim_jmp_then_terminal`'s `hterm` for the `Revert` case. The Revert-case
    companion of `hterm_halt` (via `runBlock_abort`); only the `Abort RevertAbort` arm is reached. -/
theorem hterm_revert {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb extra front term hd tl s sEnd sEnd' AbortType.RevertAbort hbb hcons
      hphi hnonterm hthread hterm_step]
    exact hasm

/-- **The `∀ f'` outcome of a faulting terminal block** (`stepInstBase term sEnd = Abort ExHaltAbort
    sEnd'` — INVALID) — `hfsim_jmp_then_terminal`'s `hterm` for the `Fault` case. The Fault-case
    companion of `hterm_halt`; only the `Abort ExHaltAbort` arm is reached. -/
theorem hterm_fault {budget : Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {asMid : AsmState} (ctx : VenomContext) (bb : BasicBlock)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd sEnd' : VenomState)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
              venomAsmTerminalRel sEnd' asm') :
    ∀ f', match runBlock f' ctx bb s with
      | ExecResult.OK s' =>
          s'.halted = true ∧ ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Halt s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmHalt asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.RevertAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmRevert asm' ∧
            venomAsmTerminalRel s' asm'
      | ExecResult.Abort AbortType.ExHaltAbort s' =>
          ∃ asm', runAsm budget offsetToPc prog asMid = AsmResult.AsmFault asm' ∧
            venomAsmTerminalRel s' asm'
      | _ => True := by
  intro f'
  by_cases hf : f' ≤ front.length
  · obtain ⟨e, he⟩ :=
      runBlock_oof ctx bb f' front term hd tl s sEnd hbb hcons hphi hnonterm hthread hf
    simp only [he]
  · obtain ⟨extra, rfl⟩ : ∃ e, f' = front.length + (e + 1) := ⟨f' - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb extra front term hd tl s sEnd sEnd' AbortType.ExHaltAbort hbb hcons
      hphi hnonterm hthread hterm_step]
    exact hasm

/-! ## Asm-side full-block sim (halting terminator)

The asm side of a block's `Halt` arm: prefix + body (`genBlockPrefixBody_sim`) sequenced with a
terminator whose sim halts (`asm_seq_halt`). The terminator is abstracted as `htermsim` — the caller
plugs `genInstPlan_sim_stop` (STOP) or any `[term-ops] → AsmHalt` sim. Running
`[SOLabel l] ++ body ++ termOps` from `as0` halts at `as''`, with observable effects agreeing
(`venomAsmTerminalRel`) at the terminator's Venom result `vsTerm`. The `Revert`/`Fault`/`OK` arms
are the same shape with `asm_seq_revert`/`asm_seq_fault`/`plan_seq_sim'`. -/

theorem genBlockAsm_halt_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmHalt s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmHalt as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_halt h1run h2run, h2rel⟩

/-- Asm side of a block's `Revert` arm (terminator `Abort RevertAbort`). -/
theorem genBlockAsm_revert_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmRevert s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmRevert as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_revert h1run h2run, h2rel⟩

/-- Asm side of a block's `Fault` arm (terminator `Abort ExHaltAbort` / INVALID). -/
theorem genBlockAsm_fault_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmFault s' ∧
              venomAsmTerminalRel vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmFault as'' ∧
           venomAsmTerminalRel vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_fault h1run h2run, h2rel⟩

/-- Asm side of a block's `OK` arm (non-halting terminator, e.g. `JUMP`): the terminator's
    `venomAsmRel` (not terminal) carries forward to the next block. -/
theorem genBlockAsm_ok_sim {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat}
    (l : String) (gp : Instruction × Nat → PlanState → List StackOp × PlanState)
    (front : List Instruction) (termOps : List StackOp) (psTerm : PlanState)
    (ps0 : PlanState) (vs0 sEnd vsTerm : VenomState) (as0 : AsmState)
    (hstep : ∀ (x : Instruction × Nat) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (gp x p).1) →
        ∃ s', runAsm (executePlan (gp x p).1).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo (gp x p).2 (gvBodyStep x v) s' ∧
              s'.pc = s.pc + (executePlan (gp x p).1).length)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (htermsim : ∀ (s : AsmState),
        venomAsmRel lo ((front.zipIdx 0).foldl
          (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd s →
        asmBlockAt prog s.pc (executePlan termOps) →
        ∃ s', runAsm (executePlan termOps).length offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel lo psTerm vsTerm s')
    (hblock : asmBlockAt prog as0.pc
      (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps))) :
    ∃ as'', runAsm (executePlan ([StackOp.SOLabel l] ++ ((front.zipIdx 0).foldl
              (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1 ++ termOps)).length
             offsetToPc prog as0 = AsmResult.AsmOK as'' ∧
           venomAsmRel lo psTerm vsTerm as'' := by
  rw [executePlan_append] at hblock
  obtain ⟨hpreBody, htermBlock⟩ := asmBlockAt_append hblock
  obtain ⟨as', h1run, h1rel, h1pc⟩ :=
    genBlockPrefixBody_sim l gp front ps0 vs0 sEnd as0 hstep hrel0 hthread hpreBody
  have htermBlock' : asmBlockAt prog as'.pc (executePlan termOps) := by rw [h1pc]; exact htermBlock
  obtain ⟨as'', h2run, h2rel⟩ := htermsim as' h1rel htermBlock'
  exact ⟨as'', asm_seq_ok h1run h2run, h2rel⟩

/-! ## Discharge logic — the halting arm

The core `genBlockSimulation` discharge for a halting block (terminator `stepInstBase = Halt` —
STOP/RETURN/SINK), in the exact `match runBlock`-shape `genBlockSimulation` uses. Cases on fuel:
with enough fuel `runBlock = Halt (haltState sEnd)` (`runBlock_halt`), so the match reduces to the
`Halt` arm, discharged by the asm result `hasm` (which `genBlockAsm_halt_sim` supplies); with too
little fuel `runBlock = Error` (`runBlock_oof`), landing in the vacuous `_ => True` arm. The OK /
Abort arms are unreachable for a halting block (their hypotheses are never selected). This isolates
the fuel case-split + match handling — the asm side is the `hasm` hypothesis. -/

theorem genBlockSim_match_halt {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_halt : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_halt ctx bb e front term hd tl vs sEnd sEnd' hbb hcons hphi hnonterm
        hthread hterm_halt]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-- Discharge logic for the `Revert` arm (terminator `stepInstBase = Abort RevertAbort` — REVERT).
    Same shape as `genBlockSim_match_halt` with `runBlock_abort`. -/
theorem genBlockSim_match_revert {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb e front term hd tl vs sEnd sEnd' AbortType.RevertAbort hbb hcons hphi
        hnonterm hthread hterm_abort]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-- Discharge logic for the `Fault` arm (terminator `stepInstBase = Abort ExHaltAbort` — INVALID and
    the faulting opcodes). Same shape with `runBlock_abort`. -/
theorem genBlockSim_match_fault {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
                   venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_abort ctx bb e front term hd tl vs sEnd sEnd' AbortType.ExHaltAbort hbb hcons hphi
        hnonterm hthread hterm_abort]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-! ## Plan-structure connection

For a non-single-predecessor block (so `generateBlockPlan_decompose`'s `cleanOps` is empty) with an
entry that has no params and a body of regular instructions, the generated plan is exactly
`SOLabel :: (the plain generateRegularInstPlan fold over nonParamInsts)`. Chains
`generateBlockPlan_decompose` (peel the `SOLabel` / `cleanOps`) with `genInstOps_eq_plain` (the
`Option` instOps fold collapses to the plain regular fold). The body fold can then be split at the
terminator by `instOps_fold_split` to match the `genBlockAsm_*_sim` shape. -/

theorem genBlockPlan_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {bb : BasicBlock} {ps : PlanState} {blockOps : List StackOp} {ps' : PlanState}
    (hentry : ∀ entry, fn.blocks.head? = some entry → getParams entry.instructions = [])
    (hnotsingle : (cfg.predsOf bb.label).length ≠ 1)
    (hreg : ∀ inst ∈ nonParamInsts bb, ¬ isPreCodegenOpcode inst.opcode ∧
      inst.opcode ≠ Opcode.PHI ∧ inst.opcode ≠ Opcode.OFFSET ∧
      inst.opcode ≠ Opcode.PARAM ∧ inst.opcode ≠ Opcode.NOP)
    (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (blockOps, ps')) :
    blockOps = StackOp.SOLabel bb.label :: ((nonParamInsts bb).zipIdx.foldl
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
        ([], ps)).1 := by
  obtain ⟨cleanOps, ps2, instOps, hclean, hf, hblk⟩ :=
    generateBlockPlan_decompose liveness dfg cfg fn bb ps blockOps ps' hentry hplan
  obtain ⟨hco, hps2⟩ : cleanOps = [] ∧ ps2 = ps := by
    rcases hclean with ⟨hc, _⟩ | ⟨_, hco, hps2⟩
    · exact absurd hc hnotsingle
    · exact ⟨hco, hps2⟩
  subst hco; subst ps2
  have hio : instOps = _ := congrArg Prod.fst (genInstOps_eq_plain bb ps instOps ps' hreg hf)
  rw [hblk, hio]; simp

/-- A program contains itself at pc 0 — `asmBlockAt prog 0 prog`. Used to feed `genBlockAsm_*_sim`
    when the block's compiled program *is* `prog` and execution starts at the top (`as.pc = 0`). -/
theorem asmBlockAt_self (prog : List AsmInst) : asmBlockAt prog 0 prog := by
  refine ⟨by omega, ?_⟩
  intro j hj; simp

/-! ## asmResolve identity on a label-free plan

For a block whose plan emits no label/offset pushes (no `SOPushLabel`/`SOPushOfst`/`SOPush (Label)` —
i.e. a non-control-flow block: arithmetic body + STOP/RETURN/REVERT/INVALID terminator),
`executePlan ops` contains no `AsmPushLabel`/`AsmPushOfst`, so `asmResolve` is the identity on it and
the capstone's `prog = (asmResolve (executePlan ops)).1` *is* `executePlan ops`. This reduces the
whole-plan no-label condition to a per-`StackOp` one via `executePlan = ops >>= execStackOp`. -/

theorem asmResolve_executePlan_id (ops : List StackOp)
    (hL : ∀ op ∈ ops, ∀ a ∈ execStackOp op, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (hO : ∀ op ∈ ops, ∀ a ∈ execStackOp op, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    (asmResolve (executePlan ops)).1 = executePlan ops := by
  apply asmResolve_fst_eq_of_no_label
  · intro a ha lbl
    have ha2 : a ∈ ops.flatMap execStackOp := ha
    rw [List.mem_flatMap] at ha2
    obtain ⟨op, hop, ha'⟩ := ha2
    exact hL op hop a ha' lbl
  · intro a ha lbl d
    have ha2 : a ∈ ops.flatMap execStackOp := ha
    rw [List.mem_flatMap] at ha2
    obtain ⟨op, hop, ha'⟩ := ha2
    exact hO op hop a ha' lbl d

/-- Discharge logic for the `OK` arm (non-halting terminator, e.g. JMP): the match reduces (via
    `runBlock_ok`) to the `OK` arm, carrying `venomAsmRel` forward to the next block. The asm side
    `hasm` is supplied by `genBlockAsm_ok_sim` (whose control-flow terminator resolves through
    `offsetToPc`). -/
theorem genBlockSim_match_ok {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_step : stepInstBase term sEnd = ExecResult.OK sEnd')
    (hterm_isterm : isTerminator term.opcode = true)
    (hnohalt : sEnd'.halted = false)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
                   venomAsmRel labelOffsets ps' sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  by_cases hf : front.length < fuel
  · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) :=
      ⟨fuel - front.length - 1, by omega⟩
    rw [runBlock_ok ctx bb e front term hd tl vs sEnd sEnd' hbb hcons hphi hnonterm hthread
        hterm_step hterm_isterm hnohalt]
    exact hasm
  · obtain ⟨err, herr⟩ :=
      runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
    rw [herr]; trivial

/-! ## Full halting-block discharge

The `genBlockSimulation`-shaped conclusion (with the *resolved* program
`prog = (asmResolve (executePlan blockOps)).1`) for a halting block. Bridges the `asmResolve`
identity (`hresolve`, from `asmResolve_executePlan_id` on a label-free plan) to
`genBlockSim_match_halt`: rewriting `prog` to `executePlan blockOps` reduces the goal to the latter,
whose `hasm` is supplied by `genBlockAsm_halt_sim` (run from `as.pc = 0` via `asmBlockAt_self`, with
`blockOps = SOLabel :: front-fold ++ termOps` from `genBlockPlan_regular` + `instOps_fold_split`).
The first end-to-end assembly of the discharge components into the capstone shape. -/

theorem genBlockSimulation_halting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_halt : stepInstBase term sEnd = ExecResult.Halt (haltState sEnd))
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmHalt as' ∧ venomAsmTerminalRel (haltState sEnd) as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_halt front term hd tl sEnd (haltState sEnd) fuel hbb hcons hphi hnonterm
    hthread hterm_halt hasm

/-- Full reverting-block discharge (terminator `Abort RevertAbort` — REVERT). Variant of
    `genBlockSimulation_halting` via `genBlockSim_match_revert`. -/
theorem genBlockSimulation_reverting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_revert front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
    hterm_abort hasm

/-- Full faulting-block discharge (terminator `Abort ExHaltAbort` — INVALID / faulting opcodes).
    Variant of `genBlockSimulation_halting` via `genBlockSim_match_fault`. -/
theorem genBlockSimulation_faulting {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {blockOps : List StackOp}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (hterm_abort : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hresolve : (asmResolve (executePlan blockOps)).1 = executePlan blockOps)
    (hasm : ∃ as', runAsm (executePlan blockOps).length offsetToPc (executePlan blockOps) as
                     = AsmResult.AsmFault as' ∧ venomAsmTerminalRel sEnd' as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm (asmResolve (executePlan blockOps)).1.length offsetToPc
                (asmResolve (executePlan blockOps)).1 as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  rw [hresolve]
  exact genBlockSim_match_fault front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
    hterm_abort hasm

/-! ## General block-simulation discharge (all terminator arms)

The unified `genBlockSimulation`-shaped discharge for an arbitrary phi-free block
`front ++ [term]`, given the asm-side result `hsim` keyed by the terminator's effect
`stepInstBase term sEnd`. Cases on that effect and dispatches to the matching per-arm lemma
(`genBlockSim_match_{ok,halt,revert,fault}`); for an internally-returning (RET) or erroring
terminator, `runBlock` is `IntRet`/`Error` (via `runBlock_intret`/`runBlock_error`, or `runBlock_oof`
on low fuel), landing in the vacuous `_ => True` arm. The whole asm side is the `hsim` hypothesis
(supplied by the body per-inst sims + the terminator's own sim through `genBlockAsm_*_sim`); this
lemma is purely the terminator case-split + `runBlock` reduction. -/

theorem genBlockSim_match {ctx : VenomContext} {bb : BasicBlock} {vs as : _}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {labelOffsets : AssocList String Nat} {ps' : PlanState}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd : VenomState) (fuel : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hsim : match stepInstBase term sEnd with
      | ExecResult.OK sEnd' =>
        sEnd'.halted = false ∧ ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
          venomAsmRel labelOffsets ps' sEnd' as'
      | ExecResult.Halt sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
          venomAsmTerminalRel sEnd' as'
      | ExecResult.Abort AbortType.RevertAbort sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
          venomAsmTerminalRel sEnd' as'
      | ExecResult.Abort AbortType.ExHaltAbort sEnd' =>
        ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
          venomAsmTerminalRel sEnd' as'
      | _ => True) :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' =>
       ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vs' as'
     | _ => True) := by
  cases hstep_term : stepInstBase term sEnd with
  | OK sEnd' =>
    simp only [hstep_term] at hsim
    obtain ⟨hnohalt, hasm⟩ := hsim
    exact genBlockSim_match_ok front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
      hstep_term histerm hnohalt hasm
  | Halt sEnd' =>
    simp only [hstep_term] at hsim
    exact genBlockSim_match_halt front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm hthread
      hstep_term hsim
  | Abort a sEnd' =>
    cases a with
    | RevertAbort =>
      simp only [hstep_term] at hsim
      exact genBlockSim_match_revert front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm
        hthread hstep_term hsim
    | ExHaltAbort =>
      simp only [hstep_term] at hsim
      exact genBlockSim_match_fault front term hd tl sEnd sEnd' fuel hbb hcons hphi hnonterm
        hthread hstep_term hsim
  | IntRet vals sEnd' =>
    by_cases hf : front.length < fuel
    · obtain ⟨e, rfl⟩ : ∃ e, fuel = front.length + (e + 1) := ⟨fuel - front.length - 1, by omega⟩
      rw [runBlock_intret ctx bb e front term hd tl vs sEnd sEnd' vals hbb hcons hphi hnonterm
        hthread hstep_term]; trivial
    · obtain ⟨err, herr⟩ :=
        runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
      rw [herr]; trivial
  | Error e =>
    by_cases hf : front.length < fuel
    · obtain ⟨e2, rfl⟩ : ∃ e2, fuel = front.length + (e2 + 1) := ⟨fuel - front.length - 1, by omega⟩
      rw [runBlock_error ctx bb e2 front term hd tl vs sEnd e hbb hcons hphi hnonterm
        hthread hstep_term]; trivial
    · obtain ⟨err, herr⟩ :=
        runBlock_oof ctx bb fuel front term hd tl vs sEnd hbb hcons hphi hnonterm hthread (by omega)
      rw [herr]; trivial

/-! ## Empty-body terminal blocks: reusable `genBlockSimulation` discharge

For a block `[term]` (no body) whose terminator halts/reverts/faults, there is no body fold (hence no
well-scheduling obligation), and `genBlockSimulation`'s `hsim` collapses to the terminator's own sim.
These wrappers feed `genBlockSim_match` the empty-body structure, leaving only the Venom terminator
step (`hstep`) and the runnable asm sim (`hasm`) — supplied by the per-instruction terminal sims
(`emit_{return,revert,selfdestruct}_sim`, `asmStep_{stop,invalid}_ok`, …) over the resolved program
(`asmResolve` is the identity on a label-push-free terminal block). The first *general*
(non-example) `genBlockSimulation` discharge for the terminal-terminator class. -/

/-- Empty-body **Halt**-terminated block (STOP / RETURN / SELFDESTRUCT). -/
theorem genBlockSimulation_empty_body_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Halt vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-- Empty-body **Revert**-terminated block (REVERT). -/
theorem genBlockSimulation_empty_body_revert
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Abort AbortType.RevertAbort vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmRevert as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-- Empty-body **Fault**-terminated block (INVALID). -/
theorem genBlockSimulation_empty_body_fault
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {as : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {term : Instruction} {fuel : Nat} {vsTerm : VenomState}
    (hbb : bb.instructions = [term])
    (hphi : term.opcode ≠ Opcode.PHI)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term { vs with instIdx := 0 } = ExecResult.Abort AbortType.ExHaltAbort vsTerm)
    (hasm : ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmFault as' ∧
              venomAsmTerminalRel vsTerm as') :
    (match runBlock fuel ctx bb vs with
     | ExecResult.OK vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmOK as' ∧
            venomAsmRel labelOffsets ps' vs' as'
     | ExecResult.Halt vs' => ∃ as', runAsm prog.length offsetToPc prog as = AsmResult.AsmHalt as' ∧
            venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmRevert as' ∧ venomAsmTerminalRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm prog.length offsetToPc prog as
            = AsmResult.AsmFault as' ∧ venomAsmTerminalRel vs' as'
     | _ => True) := by
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') [] term term []
    { vs with instIdx := 0 } fuel hbb rfl hphi (by simp)
    rfl histerm ?_
  rw [hstep]; exact hasm

/-! ## Non-empty-body terminal blocks: body fold ∘ terminator

The reusable discharge for a block with a *non-empty* straight-line body `front` followed by a
terminal terminator.  The body's asm runs `bodyLen` steps to `AsmOK as_mid` (supplied by
`genBlockPrefixBody_sim_inv` over a `BodyStepsReady` — the well-scheduled body fold), and the
terminator's asm then runs the remaining `prog.length - bodyLen` steps from `as_mid` to its terminal
result (supplied by the per-instruction terminal sims).  `runAsm_append_ok` glues the two into the
single whole-program `runAsm prog.length` that `genBlockSim_match`'s `hsim` demands.  This is what
lets a block with body instructions — not just a bare terminator — be discharged. -/

/-- Non-empty-body **Halt**-terminated block: body OK to `as_mid`, terminator Halt from `as_mid`. -/
theorem genBlockSimulation_body_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Halt sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmHalt asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
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
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmHalt asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- Non-empty-body **Revert**-terminated block (REVERT terminator). -/
theorem genBlockSimulation_body_revert
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Abort AbortType.RevertAbort sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmRevert asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
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
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmRevert asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- Non-empty-body **Fault**-terminated block (INVALID terminator). -/
theorem genBlockSimulation_body_fault
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (sEnd sEnd' : VenomState) (asMid asFin : AsmState) (bodyLen : Nat)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { vs with instIdx := 0 } = some sEnd)
    (histerm : isTerminator term.opcode = true)
    (hstep : stepInstBase term sEnd = ExecResult.Abort AbortType.ExHaltAbort sEnd')
    (hbodyrun : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asMid)
    (htermrun : runAsm (prog.length - bodyLen) offsetToPc prog asMid = AsmResult.AsmFault asFin)
    (hlen : bodyLen ≤ prog.length)
    (htermrel : venomAsmTerminalRel sEnd' asFin) :
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
  refine genBlockSim_match (labelOffsets := labelOffsets) (ps' := ps') front term hd tl sEnd fuel
    hbb hcons hphi hnonterm hthread histerm ?_
  rw [hstep]
  refine ⟨asFin, ?_, htermrel⟩
  have hc : runAsm (bodyLen + (prog.length - bodyLen)) offsetToPc prog asm = AsmResult.AsmFault asFin := by
    rw [runAsm_append_ok hbodyrun]; exact htermrun
  rwa [Nat.add_sub_cancel' hlen] at hc

/-- **Fully-wired single-binop-body block sim (Halt terminator).** End-to-end composition of the
    non-empty-body fold for a block `[c := <comm var binop> x y ; <Halt terminator>]`: the single
    binop atom is packaged into a `BodyStepsReady` (`bodyStepsReady_single_commBinop`, free
    optimistic-swap since `nextIsTerminator`), folded to its post-body asm state by
    `genBlockPrefixBody_sim_inv`, and glued to the terminator by `genBlockSimulation_body_halt`. The
    only example-specific inputs are the resolved program's layout/dispatch (`hblock`, `hdisp`) and
    the terminator's own asm sim (`htermrun`) — the body fold itself is fully discharged here. The
    first per-block simulation with a non-empty instruction body. -/
theorem genBlockSimulation_single_commBinop_halt
    {ctx : VenomContext} {bb : BasicBlock} {vs : VenomState} {asm : AsmState}
    {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {labelOffsets : AssocList String Nat}
    {ps' : PlanState} {fuel : Nat}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst term : Instruction} {l curBbLabel : String} {nextLiveness S0 : List String}
    {ps0 : PlanState} {sEnd sEndTerm : VenomState} {asFin : AsmState}
    {x y out name : String} {f : bytes32 → bytes32 → bytes32}
    (hname : opcodeToEvmName inst.opcode = some name)
    (hcomm : isCommutative inst.opcode = true)
    (hdispatch : ∀ v, stepInstBase inst v = execPure2 f inst v)
    (hops : inst.operands = [Operand.Var x, Operand.Var y])
    (houts : inst.outputs = [out])
    (hxy : x ≠ y) (hxS : x ∈ S0) (hyS : y ∈ S0) (houtS : out ∉ S0)
    (hlive : nextLiveness.contains out = true)
    (hlivex : nextLiveness.contains x = true) (hlivey : nextLiveness.contains y = true)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp name → asmStep offsetToPc prog s = asmBinop f s)
    (hbb : bb.instructions = [inst] ++ [term])
    (hinstphi : inst.opcode ≠ Opcode.PHI)
    (hinstnonterm : isTerminator inst.opcode = false)
    (histerm : isTerminator term.opcode = true)
    (hsd0 : StackDiscH ([inst].zipIdx 0).length ps0 { vs with instIdx := 0 })
    (hsv0 : StackIsVars S0 ps0)
    (hrel0 : venomAsmRel labelOffsets ps0 { vs with instIdx := 0 } asm)
    (hthread : execBodyThread [inst] 0 { vs with instIdx := 0 } = some sEnd)
    (hstepterm : stepInstBase term sEnd = ExecResult.Halt sEndTerm)
    (hblock : asmBlockAt prog asm.pc
      (executePlan ([StackOp.SOLabel l] ++ (([inst].zipIdx 0).foldl
        (fun acc z => (acc.1 ++
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).1,
          ((fun (w : Instruction × Nat) (p : PlanState) =>
            generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p) z acc.2).2))
          ([], ps0)).1)))
    (bodyLen : Nat)
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (([inst].zipIdx 0).foldl
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
  have hready := bodyStepsReady_single_commBinop (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (curBbLabel := curBbLabel) (idx := 0) (lo := labelOffsets) (offsetToPc := offsetToPc)
    (prog := prog) hname hcomm hdispatch hops houts hxy hxS hyS houtS hlive hlivex hlivey hdisp
  obtain ⟨asMid, hbrun, hbrel, hbpc⟩ :=
    genBlockPrefixBody_sim_inv l
      (fun (w : Instruction × Nat) (p : PlanState) =>
        generateRegularInstPlan liveness dfg cfg fn w.1 nextLiveness false true curBbLabel p)
      [inst] S0 ps0 { vs with instIdx := 0 } sEnd asm hready hsd0 hsv0 hrel0 hthread hblock
  rw [← hbodyLenEq] at hbrun hbpc
  exact genBlockSimulation_body_halt (labelOffsets := labelOffsets) (ps' := ps')
    [inst] term inst [term] sEnd sEndTerm asMid asFin bodyLen
    hbb rfl hinstphi (by intro i hi; simp at hi; subst hi; exact hinstnonterm) hthread histerm
    hstepterm hbrun (htermrun asMid hbpc) hlen htermrel

end EvmYul.Venom.Hol.Codegen

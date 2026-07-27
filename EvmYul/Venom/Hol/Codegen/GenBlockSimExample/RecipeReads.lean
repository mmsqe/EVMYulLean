/-
GenBlockSimExample / read capstones (TLOAD, 0-input env reads, account reads)

Split from RecipeFinal for readability; layout only, meaning unchanged. Wrapped in
`namespace …Codegen.Example` and imports the previous part.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeFinal

namespace EvmYul.Venom.Hol.Codegen

namespace Example

/-! ### ✅ A 1-input READ (TLOAD) via the recipe route — `codegen_correct_tldFn_recipeW`

The transient-storage read `TLOAD`, twin of the `CALLDATALOAD` capstone (same shape, `RegularStepG`'s
TLOAD arm, `asmStep_tload_ok`):

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = TLOAD %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                               -- MUL consumes the TOP two (b,c)
```

`TLOAD %a` is a 1-input read (`RegularStepG`'s TLOAD arm, emitted `DUP2 ; TLOAD`), leaving `[a, b, c]`
with `c = tldVal s` (the transient word at key `callvalue` — context-dependent, generally NON-zero, so
`c` cannot itself be a RETURN operand). In `next` the consuming `MUL %b %c` eats the top two (`b, c`);
since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`, regardless of `c`), emptying the return window.
`a` (bottom) is never buried — no f1a reorder. `entry` via `hsupplyW_regularJmp`, `next` via
`hsupplyW_regularReturnTo` fed the consuming `MUL` (`tldNext_ready`). -/

def tldCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def tldCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def tldLoad : Instruction :=
  { id := 2, opcode := Opcode.TLOAD, operands := [Operand.Var "a"], outputs := ["c"] }
def tldJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def tldMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def tldRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def tldEntry : BasicBlock := { label := "entry", instructions := [tldCvA, tldCvB, tldLoad, tldJmp] }
def tldNext : BasicBlock := { label := "next", instructions := [tldMul, tldRet] }
def tldFn : IrFunction := { name := "main", blocks := [tldEntry, tldNext] }
def tldCtx : VenomContext := { functions := [tldFn], entry := some "main" }

theorem tld_unresolved_asm : executePlan (generateFnPlan tldFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "TLOAD", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- The transient-storage word TLOAD reads at key `a` (= the call value); context-dependent, generally NON-zero. -/
abbrev tldVal (s : VenomState) : bytes32 := tload s.callCtx.callvalue s

/-- entry's body `[CV a; CV b; TLOAD %a]` as a `RegularBodyH`: two `cv_step`s then the
    TLOAD read via `RegularStepG`'s TLOAD arm (`asmStep_tload_ok`), output live. -/
theorem tldEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 1 [tldCvA, tldCvB, tldLoad] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, by decide⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨"a", "c", rfl, by decide, rfl, fun _ => rfl, rfl, rfl,
     by decide, by decide, by decide, by decide, fun _ h hg => asmStep_tload_ok h hg⟩)))))))

/-- Body-end state of `tldEntry`: `a,b := callvalue`, `c := tldVal s` (the transient read at key `a`). -/
abbrev tldEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (tldVal s)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem tldEntry_thread (s : VenomState) :
    execBodyThread [tldCvA, tldCvB, tldLoad] 0 { s with instIdx := 0 } = some (tldEntrySEnd s) := by
  have hla : lookupVar "a" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "b" s.callCtx.callvalue
      (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = some s.callCtx.callvalue
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue :=
    lookupVar_updateVar_self _ _ _
  have hsub : stepInstBase tldLoad ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = ExecResult.OK (updateVar "c" (tldVal s)
        ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 })) := by
    have he : evalOperand (Operand.Var "a") ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := hla
    simp only [tldLoad, stepInstBase, execRead1, he]
    rfl
  have h1 : stepInstBase tldCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase tldCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase tldCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [tldCvB, tldLoad] 1 { s' with instIdx := 1 }
        | _ => none) = some (tldEntrySEnd s)
  rw [h1]
  show (match stepInstBase tldCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [tldLoad] 2 { s' with instIdx := 2 }
        | _ => none) = some (tldEntrySEnd s)
  rw [h2]
  show (match stepInstBase tldLoad ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (tldEntrySEnd s)
  rw [hsub]
  rfl

/-- `tldEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem tldEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) tldCtx tldEntry s = ExecResult.OK (jumpTo "next" (tldEntrySEnd s)) :=
  runBlock_body_jmp tldCtx tldEntry j [tldCvA, tldCvB, tldLoad] tldJmp tldCvA [tldCvB, tldLoad, tldJmp] s
    (tldEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (tldEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem tldNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg tldFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([tldMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := tldFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev tldNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem tldNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (tldNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (tldNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem tldNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [tldMul] 0 { s with instIdx := 0 } = some (tldNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase tldMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := tldMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase tldMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem tldMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase tldMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [tldMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem tldMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase tldMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [tldMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem tldNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) tldCtx tldNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (tldNextSEnd s wb wc))
        (tldNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := tldNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return tldCtx tldNext j [tldMul] tldRet tldMul [tldRet] s (tldNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (tldNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem tldNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) tldCtx tldNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := tldNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term tldCtx tldNext j [tldMul] tldRet tldMul [tldRet] s (tldNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (tldNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : tldNext.instructions = [tldMul] ++ [tldRet])
    (tldNext_thread s wb wc hb hc), tldRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `tldEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem tldEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (tldEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (tldEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (tldEntrySEnd s) = some (tldVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (tldVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (tldVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (tldVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def tldInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (tldVal s))

theorem tldInv_pres : ∀ bb ∈ tldFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    tldInv s → runBlock f' tldCtx bb s = ExecResult.OK s' → tldInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [tldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (tldEntrySEnd s)`
    have hnt : ∀ inst ∈ [tldCvA, tldCvB, tldLoad], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldEntry 0 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
             [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldEntry 1 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
             [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldEntry 2 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
             [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldEntry 3 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
             [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, tldEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := tldEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (tldEntrySEnd s)) = lookupVar "c" (tldEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 tldCtx tldNext s tldMul [tldRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error tldCtx tldNext tldMul [tldRet] s "undefined operand" j rfl
          (by decide) (tldMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 tldCtx tldNext s tldMul [tldRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error tldCtx tldNext tldMul [tldRet] s "undefined operand" j rfl
            (by decide) (tldMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 tldCtx tldNext s tldMul [tldRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldNext 1 [tldMul] tldRet tldMul [tldRet] s
                   (tldNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (tldNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, tldNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 tldCtx tldNext s tldMul [tldRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof tldCtx tldNext 1 [tldMul] tldRet tldMul [tldRet] s
                   (tldNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (tldNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, tldNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 tldCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem tldFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 tldCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 tldCtx vs
      = runBlocks 10 tldCtx tldFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, tldCtx, tldFn, lookupFunction, fnEntryLabel, tldEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (tldEntrySEnd s0) with hs1
  have hentry : runBlock 9 tldCtx tldEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact tldEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb tldFn.blocks = some tldEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 tldCtx tldFn s0 = runBlocks 9 tldCtx tldFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := tldEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (tldVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (tldEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb tldFn.blocks = some tldNext := rfl
  have hhalt := tldNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (tldVal s0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **A 1-input READ (TLOAD) capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=TLOAD %a ; JMP next` /
    `next: %e=MUL %b %c ; RETURN %e, %a`. `entry`'s TLOAD exercises the 1-input transient-read arm
    (`RegularStepG`'s TLOAD disjunct, `asmStep_tload_ok`), emitted `DUP2 ; TLOAD`, leaving `c = tldVal s`
    (context-dependent). `next`'s MUL consumes the top two `[b, c]` (so `a` is never buried — no f1a
    reorder); `b = 0` ⇒ `e = 0` (`uint256_zero_mul`) empties the return window. `next` ends in a
    body-then-RETURN handled by `hsupplyW_regularReturnTo`; `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_tldFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 tldCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ tldFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [tldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [tldEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [tldNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan tldFn 0 0
      = some ((generateFnPlan tldFn 0 0).get!.1, (generateFnPlan tldFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel tldFn) tldFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv tldInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel tldFn) tldFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan tldFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := tldCtx) (fn := tldFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan tldFn 0 0).get!.1) (psFinal := (generateFnPlan tldFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ tldInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [tldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, tldEntry, tldCvA]
    · simp [runBlock, evalPhis, execBlock, tldNext, tldMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [tldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [tldCvA, tldCvB, tldLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof tldCtx tldEntry 1 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
               [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof tldCtx tldEntry 2 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
               [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof tldCtx tldEntry 3 [tldCvA, tldCvB, tldLoad] tldJmp tldCvA
               [tldCvB, tldLoad, tldJmp] s (tldEntrySEnd s) rfl rfl (by decide) hnt (tldEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([tldCvA, tldCvB, tldLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [tldCvA, tldCvB, tldLoad]) (jmpInst := tldJmp) (hd := tldCvA) (tl := [tldCvB, tldLoad, tldJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := tldNext) (sEnd := tldEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := tldEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := tldEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 4 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- next: the CONSUMING ADD + body-then-RETURN
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof tldCtx tldNext 1 [tldMul] tldRet tldMul [tldRet] s
               (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (tldNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([tldMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [tldMul]) (retInst := tldRet) (hd := tldMul) (tl := [tldRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel tldFn) tldFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := tldNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s))
            = lookupVar "e" (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) from rfl,
            (tldNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (tldVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s))
            = lookupVar "a" (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) from rfl,
            (tldNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (tldVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) from rfl,
            (tldNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (tldVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (tldNextSEnd s (EvmYul.UInt256.ofNat 0) (tldVal s)) from rfl,
            (tldNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (tldVal s)).2]; exact ha0)
        (hready := tldNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel tldFn) tldFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc7]; decide) (hret := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨tldEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel tldFn) tldFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan tldFn 0 0).get!.1)).1.length
      omega



/-! ### ✅ GENERIC 0-input READ driver — `codegen_correct_r0` (deduplicates the read family)

The whole-function `codegen_correct` for every 0-input environment read (CALLER, ADDRESS, …)
is one shape parametrized by the opcode `op`, its EVM name `nm`, and the read value `fV`/`fA`.
`codegen_correct_r0` proves it once over an abstract `op`; the opcode-specific facts
(`op ≠ JMP`, the `asmStep` sim lemma, the resolved-program `hexec`, …) are hypotheses each
instantiation discharges by `rfl`/`decide`. See `codegen_correct_r0_caller` for the pattern:
a ~15-line instantiation replacing a ~475-line bespoke proof. -/

def r0CvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def r0CvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def r0Load (op : Opcode) : Instruction := { id := 2, opcode := op, operands := [], outputs := ["c"] }
def r0Jmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def r0Mul : Instruction := { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def r0Ret : Instruction := { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def r0Entry (op : Opcode) : BasicBlock := { label := "entry", instructions := [r0CvA, r0CvB, r0Load op, r0Jmp] }
def r0Next : BasicBlock := { label := "next", instructions := [r0Mul, r0Ret] }
def r0Fn (op : Opcode) : IrFunction := { name := "main", blocks := [r0Entry op, r0Next] }
def r0Ctx (op : Opcode) : VenomContext := { functions := [r0Fn op], entry := some "main" }

abbrev r0EntrySEnd (fV : VenomState → bytes32) (s : VenomState) : VenomState :=
  { updateVar "c" (fV s) { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem r0Entry_thread (op : Opcode) (fV : VenomState → bytes32)
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hpure : ∀ (s' : VenomState) (out : String) (v : bytes32), fV (updateVar out v s') = fV s')
    (hpureI : ∀ (s' : VenomState) (i : Nat), fV { s' with instIdx := i } = fV s')
    (s : VenomState) :
    execBodyThread [r0CvA, r0CvB, r0Load op] 0 { s with instIdx := 0 } = some (r0EntrySEnd fV s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hfv : fV S2 = fV s := by rw [hS2, hpureI, hpure, hpureI, hpure, hpureI]
  have hsub : stepInstBase (r0Load op) S2 = ExecResult.OK (updateVar "c" (fV s) S2) := by rw [hstep S2, hfv]
  have h1 : stepInstBase r0CvA { s with instIdx := 0 } = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase r0CvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [r0CvB, r0Load op] 1 { s' with instIdx := 1 } | _ => none) = some (r0EntrySEnd fV s)
  rw [h1]
  show (match stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [r0Load op] 2 { s' with instIdx := 2 } | _ => none) = some (r0EntrySEnd fV s)
  rw [h2]
  show (match stepInstBase (r0Load op) S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none) = some (r0EntrySEnd fV s)
  rw [hsub]; rfl

theorem r0Entry_body (op : Opcode) (nm : String) (fV : VenomState → bytes32) (fA : AsmState → bytes32)
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP)
    (hcompute : computeOperands (r0Load op) = (r0Load op).operands.reverse)
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmPushVal (fA s) s)
    (hfeq : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v) :
    RegularBodyH lo ["a", "b", "c"] offsetToPc prog 1 [r0CvA, r0CvB, r0Load op] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, Nat.le_refl 1⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨"c", nm, fV, fA, hname, hnjmp, hcompute, rfl, rfl, by decide, by decide, hstep,
     (fun s h hg => hasm offsetToPc prog s h hg), hfeq⟩)))))

theorem r0Entry_runBlock (op : Opcode) (fV : VenomState → bytes32)
    (hnterm : isTerminator op = false)
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hpure : ∀ (s' : VenomState) (out : String) (v : bytes32), fV (updateVar out v s') = fV s')
    (hpureI : ∀ (s' : VenomState) (i : Nat), fV { s' with instIdx := i } = fV s')
    (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) (r0Ctx op) (r0Entry op) s = ExecResult.OK (jumpTo "next" (r0EntrySEnd fV s)) :=
  runBlock_body_jmp (r0Ctx op) (r0Entry op) j [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA [r0CvB, r0Load op, r0Jmp] s
    (r0EntrySEnd fV s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm)
    (r0Entry_thread op fV hstep hpure hpureI s) (by simpa [updateVar] using hnh)

theorem r0EntrySEnd_lookup (fV : VenomState → bytes32) (s : VenomState) :
    lookupVar "a" (r0EntrySEnd fV s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (r0EntrySEnd fV s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (r0EntrySEnd fV s) = some (fV s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (fV s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (fV s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (fV s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]
-- Stage 2: next block (op-independent venom lemmas; r0Next_ready needs the program via hexec)
abbrev r0NextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem r0NextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (r0NextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (r0NextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem r0Next_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [r0Mul] 0 { s with instIdx := 0 } = some (r0NextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase r0Mul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := r0Mul) (f := fun a b => a * b) (x := "b") (y := "c") (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase r0Mul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

theorem r0Mul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase r0Mul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [r0Mul, stepInstBase, execPure2, evalOperand, hb']

theorem r0Mul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase r0Mul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [r0Mul, stepInstBase, execPure2, evalOperand, hb', hc']

theorem r0Next_halts (op : Opcode) (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) (r0Ctx op) r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return (r0Ctx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem r0Next_error_a (op : Opcode) (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) (r0Ctx op) r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term (r0Ctx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

-- Stage 3: invariant, inv_pres, fn_halts (parametrized by fV; purity hyps for the c-clause)
def r0Inv (fV : VenomState → bytes32) (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (fV s))

theorem r0Inv_pres (op : Opcode) (fV : VenomState → bytes32)
    (hnterm : isTerminator op = false)
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hpure : ∀ (s' : VenomState) (out : String) (v : bytes32), fV (updateVar out v s') = fV s')
    (hpureI : ∀ (s' : VenomState) (i : Nat), fV { s' with instIdx := i } = fV s')
    (hpureJ : ∀ (s' : VenomState) (lbl : String), fV (jumpTo lbl s') = fV s') :
    ∀ bb ∈ (r0Fn op).blocks, ∀ (s s' : VenomState) (f' : Nat),
      r0Inv fV s → runBlock f' (r0Ctx op) bb s = ExecResult.OK s' → r0Inv fV s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [r0Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [r0CvA, r0CvB, r0Load op], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · decide
      · decide
      · exact hnterm
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) (r0Entry op) 0 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
             [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) (r0Entry op) 1 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
             [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) (r0Entry op) 2 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
             [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) (r0Entry op) 3 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
             [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega] at hrun
      rw [r0Entry_runBlock op fV hnterm hstep hpure hpureI s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := r0EntrySEnd_lookup fV s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (r0EntrySEnd fV s)) = lookupVar "c" (r0EntrySEnd fV s) from rfl, hc0]
      have hpres : fV (r0EntrySEnd fV s) = fV s := by simp only [r0EntrySEnd, hpure, hpureI]
      rw [hpureJ, hpres]
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 (r0Ctx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error (r0Ctx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 (r0Ctx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error (r0Ctx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (r0Ctx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, r0Next_error_a op s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (r0Ctx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (r0Ctx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, r0Next_halts op s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem r0Fn_halts (op : Opcode) (fV : VenomState → bytes32)
    (hnterm : isTerminator op = false)
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hpure : ∀ (s' : VenomState) (out : String) (v : bytes32), fV (updateVar out v s') = fV s')
    (hpureI : ∀ (s' : VenomState) (i : Nat), fV { s' with instIdx := i } = fV s')
    (hpureJ : ∀ (s' : VenomState) (lbl : String), fV (jumpTo lbl s') = fV s')
    (vs : VenomState) (hnh : vs.halted = false) (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 (r0Ctx op) vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 (r0Ctx op) vs
      = runBlocks 10 (r0Ctx op) (r0Fn op) { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, r0Ctx, r0Fn, lookupFunction, fnEntryLabel, r0Entry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (r0EntrySEnd fV s0) with hs1
  have hentry : runBlock 9 (r0Ctx op) (r0Entry op) s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact r0Entry_runBlock op fV hnterm hstep hpure hpureI s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb (r0Fn op).blocks = some (r0Entry op) := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 (r0Ctx op) (r0Fn op) s0 = runBlocks 9 (r0Ctx op) (r0Fn op) s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := r0EntrySEnd_lookup fV s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (fV s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (r0EntrySEnd fV s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb (r0Fn op).blocks = some r0Next := rfl
  have hhalt := r0Next_halts op s1 6 (EvmYul.UInt256.ofNat 0) (fV s0) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

abbrev R0UNRES (nm : String) : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp nm,
   AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"]

theorem r0Next_ready (op : Opcode) (nm : String) {lo : AssocList String Nat}
    (ops : List StackOp) (hexec : executePlan ops = R0UNRES nm) :
    BodyStepsReadyHTo lo (asmResolve (executePlan ops)).2
      (asmResolve (executePlan ops)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg (r0Fn op) z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] := by
  rw [hexec]
  exact bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := r0Fn op) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

-- Stage 4: the GENERIC driver — ops/psFinal are params (executePlan ops stays a stuck
-- variable ⇒ no whnf timeout); hexec concretizes it uniformly.
theorem codegen_correct_r0 (op : Opcode) (nm : String) (fV : VenomState → bytes32) (fA : AsmState → bytes32)
    {lo : AssocList String Nat}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP) (hnterm : isTerminator op = false)
    (hcompute : computeOperands (r0Load op) = (r0Load op).operands.reverse)
    (hrdy : codegenReadyInst (r0Load op))
    (hstep : ∀ s' : VenomState, stepInstBase (r0Load op) s' = ExecResult.OK (updateVar "c" (fV s') s'))
    (hpure : ∀ (s' : VenomState) (out : String) (v : bytes32), fV (updateVar out v s') = fV s')
    (hpureI : ∀ (s' : VenomState) (i : Nat), fV { s' with instIdx := i } = fV s')
    (hpureJ : ∀ (s' : VenomState) (lbl : String), fV (jumpTo lbl s') = fV s')
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmPushVal (fA s) s)
    (hfeq : ∀ (p : PlanState) (v : VenomState) (s : AsmState), venomAsmRel lo p v s → fA s = fV v)
    (ops : List StackOp) (psFinal : PlanState)
    (hplan : generateFnPlan (r0Fn op) 0 0 = some (ops, psFinal))
    (hexec : executePlan ops = R0UNRES nm)
    (hbodyE : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (r0Fn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, r0Load op] (initPlanState 0)).1
      = [AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp nm])
    (hbodyN : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (r0Fn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next")).1
      = [AsmInst.AsmOp "MUL"])
    (hpsN : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (r0Fn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, r0Load op] (initPlanState 0)).2
      = psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next")
    (hpsStack : (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next").stack
      = [Operand.Var "a", Operand.Var "b", Operand.Var "c"])
    (hpsSpill : ∀ op', alookup' (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next").spilled op' = none)
    (hpsVars : StackIsVars ["a", "b", "c"] (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next"))
    (hpsNstack : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (r0Fn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next")).2.stack
      = [Operand.Var "a", Operand.Var "e"])
    {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx op) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hprog : asmResolve (executePlan ops) = asmResolve (R0UNRES nm) := by rw [hexec]
  have hoffs : (computeLabelOffsets (executePlan ops)).2 = (computeLabelOffsets (R0UNRES nm)).2 := by rw [hexec]
  have hlen9 : (asmResolve (R0UNRES nm)).1.length = 9 := rfl
  have hpcN : pcOfLabel (asmResolve (R0UNRES nm)).1 "next" = 6 := rfl
  have hpcE0 : pcOfLabel (asmResolve (R0UNRES nm)).1 "entry" = 0 := rfl
  have hlabE : (executePlan [StackOp.SOLabel (r0Entry op).label]).length = 1 := rfl
  have hlabN : (executePlan [StackOp.SOLabel r0Next.label]).length = 1 := rfl
  have hfnready : ∀ bb ∈ (r0Fn op).blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [r0Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [r0Entry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl
      · unfold codegenReadyInst; decide
      · unfold codegenReadyInst; decide
      · exact hrdy
      · unfold codegenReadyInst; decide
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hpsE : psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv (r0Inv fV)
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    (offsets := (computeLabelOffsets (executePlan ops)).2)
    (fuel := 10) (ctx := r0Ctx op) (fn := r0Fn op) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := ops) (psFinal := psFinal)
    hplan rfl rfl rfl ?_ ?_ (r0Inv_pres op fV hnterm hstep hpure hpureI hpureJ) ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [r0Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, r0Entry, r0CvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [r0Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hplan
      have hnt : ∀ inst ∈ [r0CvA, r0CvB, r0Load op], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm
      match k with
      | 0 => exact Or.inl (runBlock_oof (r0Ctx op) (r0Entry op) 1 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
               [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 1 => exact Or.inl (runBlock_oof (r0Ctx op) (r0Entry op) 2 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
               [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 2 => exact Or.inl (runBlock_oof (r0Ctx op) (r0Entry op) 3 [r0CvA, r0CvB, r0Load op] r0Jmp r0CvA
               [r0CvB, r0Load op, r0Jmp] s (r0EntrySEnd fV s) rfl rfl (by decide) hnt (r0Entry_thread op fV hstep hpure hpureI s) (by simp only [List.length_cons, List.length_nil]; omega))
      | (j+3) =>
      rw [show j+3+1 = ([r0CvA, r0CvB, r0Load op] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0CvA, r0CvB, r0Load op]) (jmpInst := r0Jmp) (hd := r0CvA) (tl := [r0CvB, r0Load op, r0Jmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 8) (bb' := r0Next) (sEnd := r0EntrySEnd fV s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := r0Entry_thread op fV hstep hpure hpureI s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := r0Entry_body op nm fV fA hname hnjmp hcompute hstep hasm hfeq)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0, hprog]
                       refine ⟨by simp only [hlabE, hlen9]; omega, fun j hj => ?_⟩
                       simp only [hlabE] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc0, hprog, hbodyE]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen9]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j <;> rfl)
        (hps := hpsN)
        (hpc := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen9]; omega)
        (hpush := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hoff_lk := by rw [hoffs]; rfl)
        (hoff := by decide)
        (hpc2 := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen9]; omega)
        (hjump := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hidx_lk := by rw [hprog]; rfl) (hlk' := rfl)
        (hw := by rw [hprog, hbodyE]; simp only [r0Entry, List.length_cons, List.length_nil, hlen9, hpcN, hpcE0]; omega))
    · have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc6 : asm.pc = 6 := by rw [hpc_asm, hprog]; rfl
      match k with
      | 0 => exact Or.inl (runBlock_oof (r0Ctx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (r0Next_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([r0Mul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0Mul]) (retInst := r0Ret) (hd := r0Mul) (tl := [r0Ret])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fV s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fV s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fV s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fV s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fV s)).2]; exact ha0)
        (hready := r0Next_ready op nm ops hexec)
        (hsd := ⟨hpsSpill, by rw [hpsStack]; decide, by
          intro z hz
          rw [hpsStack] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := hpsVars)
        (hrel := hvrel)
        (hbLabel := by rw [hpc6, hprog]
                       refine ⟨by simp only [hlabN, hlen9]; omega, fun j hj => ?_⟩
                       simp only [hlabN] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc6, hprog, hbodyN]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen9]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j; rfl)
        (hps'stack := by rw [List.nil_append, hpsNstack])
        (hpc := by rw [hpc6, hprog, hbodyN]; simp only [List.length_cons, List.length_nil, hlen9]; omega)
        (hret := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                    simp only [hexec, hpc6, hbodyN, List.length_cons, List.length_nil]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat])
        (hw := by rw [hprog, hbodyN]; simp only [r0Next, List.length_cons, List.length_nil, hlen9, hpcN]; omega))
  case _ =>
    refine ⟨⟨r0Entry op, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel (r0Fn op)) (r0Fn op) 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan ops)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hplan).symm
    · show (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 "entry" ≤ (asmResolve (executePlan ops)).1.length
      omega
-- END-TO-END VALIDATION: instantiate the generic driver at CALLER (all hyps by rfl/decide)
theorem codegen_correct_r0_caller {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.CALLER) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLER) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.CALLER "CALLER" (fun s => addressToWord s.callCtx.caller)
    (fun s => addressToWord s.callCtx.caller)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_caller_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,hcc,_,_,_,_⟩ := hr; rw [hcc])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_pvrFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.PREVRANDAO) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.PREVRANDAO) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.PREVRANDAO "PREVRANDAO" (fun s => s.blockCtx.prevrandao) (fun s => s.blockCtx.prevrandao)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_prevrandao_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_bbfFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.BLOBBASEFEE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BLOBBASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.BLOBBASEFEE "BLOBBASEFEE" (fun s => s.blockCtx.blobbasefee) (fun s => s.blockCtx.blobbasefee)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_blobbasefee_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

/-! ### ✅ The ACCOUNT-READ family via the generic `codegen_correct_racc` driver

BALANCE / EXTCODESIZE / EXTCODEHASH share one driver, parametrized by the opcode `op`, its EVM
name, and the read function `fRead : bytes32 → Accounts → bytes32`. Same recipe as the 0-input
`codegen_correct_r0` driver, but with a 1-input load (`DUP2 ; op`, the account-read `RegularStepG`
arm dispatching via `asmStateUnop`). Reuses r0's `next` block (`r0Next` / `r0Mul` / `r0Ret`)
verbatim. Each read is a ~10-line instantiation discharging the opcode facts by `rfl`/`decide`. -/

-- account-read family (BALANCE/EXTCODESIZE/EXTCODEHASH): 1-input load, account-read arm.
-- Reuses r0's next block (r0Next / r0Mul / r0Ret and their lemmas) verbatim.
def raccLoad (op : Opcode) : Instruction := { id := 2, opcode := op, operands := [Operand.Var "a"], outputs := ["c"] }
def raccEntry (op : Opcode) : BasicBlock := { label := "entry", instructions := [r0CvA, r0CvB, raccLoad op, r0Jmp] }
def raccFn (op : Opcode) : IrFunction := { name := "main", blocks := [raccEntry op, r0Next] }
def raccCtx (op : Opcode) : VenomContext := { functions := [raccFn op], entry := some "main" }

abbrev raccEntrySEnd (fRead : bytes32 → Accounts → bytes32) (s : VenomState) : VenomState :=
  { updateVar "c" (fRead s.callCtx.callvalue s.accounts) { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem raccEntry_thread (op : Opcode) (fRead : bytes32 → Accounts → bytes32)
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v)
    (s : VenomState) :
    execBodyThread [r0CvA, r0CvB, raccLoad op] 0 { s with instIdx := 0 } = some (raccEntrySEnd fRead s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hla : lookupVar "a" S2 = some s.callCtx.callvalue := by
    rw [hS2]; show lookupVar "a" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have haccts : S2.accounts = s.accounts := by rw [hS2]; rfl
  have hsub : stepInstBase (raccLoad op) S2 = ExecResult.OK (updateVar "c" (fRead s.callCtx.callvalue s.accounts) S2) := by
    rw [hsem S2]
    have he : evalOperand (Operand.Var "a") S2 = some s.callCtx.callvalue := hla
    simp only [raccLoad, execRead1, he, haccts]
  have h1 : stepInstBase r0CvA { s with instIdx := 0 } = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase r0CvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [r0CvB, raccLoad op] 1 { s' with instIdx := 1 } | _ => none) = some (raccEntrySEnd fRead s)
  rw [h1]
  show (match stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [raccLoad op] 2 { s' with instIdx := 2 } | _ => none) = some (raccEntrySEnd fRead s)
  rw [h2]
  show (match stepInstBase (raccLoad op) S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none) = some (raccEntrySEnd fRead s)
  rw [hsub]; rfl

theorem raccEntry_body (op : Opcode) (nm : String) (fRead : bytes32 → Accounts → bytes32)
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP)
    (hcompute : computeOperands (raccLoad op) = (raccLoad op).operands.reverse)
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s) :
    RegularBodyH lo ["a", "b", "c"] offsetToPc prog 1 [r0CvA, r0CvB, raccLoad op] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, Nat.le_refl 1⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨"a", "c", nm, fRead, hname, hnjmp, hcompute, hsem, rfl, rfl, by decide, by decide, by decide, by decide,
     (fun s h hg => hasm offsetToPc prog s h hg)⟩))))))
theorem raccEntry_runBlock (op : Opcode) (fRead : bytes32 → Accounts → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v)
    (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) (raccCtx op) (raccEntry op) s = ExecResult.OK (jumpTo "next" (raccEntrySEnd fRead s)) :=
  runBlock_body_jmp (raccCtx op) (raccEntry op) j [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA [r0CvB, raccLoad op, r0Jmp] s
    (raccEntrySEnd fRead s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm)
    (raccEntry_thread op fRead hsem s) (by simpa [updateVar] using hnh)

theorem raccEntrySEnd_lookup (fRead : bytes32 → Accounts → bytes32) (s : VenomState) :
    lookupVar "a" (raccEntrySEnd fRead s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (raccEntrySEnd fRead s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (raccEntrySEnd fRead s) = some (fRead s.callCtx.callvalue s.accounts) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

theorem raccNext_halts (op : Opcode) (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) (raccCtx op) r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return (raccCtx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem raccNext_error_a (op : Opcode) (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) (raccCtx op) r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term (raccCtx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

def raccInv (fRead : bytes32 → Accounts → bytes32) (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (fRead s.callCtx.callvalue s.accounts))

theorem raccInv_pres (op : Opcode) (fRead : bytes32 → Accounts → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v) :
    ∀ bb ∈ (raccFn op).blocks, ∀ (s s' : VenomState) (f' : Nat),
      raccInv fRead s → runBlock f' (raccCtx op) bb s = ExecResult.OK s' → raccInv fRead s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [raccFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [r0CvA, r0CvB, raccLoad op], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · decide
      · decide
      · exact hnterm
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) (raccEntry op) 0 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
             [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) (raccEntry op) 1 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
             [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) (raccEntry op) 2 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
             [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) (raccEntry op) 3 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
             [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega] at hrun
      rw [raccEntry_runBlock op fRead hnterm hsem s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := raccEntrySEnd_lookup fRead s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (raccEntrySEnd fRead s)) = lookupVar "c" (raccEntrySEnd fRead s) from rfl, hc0]
      rfl
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 (raccCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error (raccCtx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 (raccCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error (raccCtx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (raccCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, raccNext_error_a op s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (raccCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (raccCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, raccNext_halts op s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem raccFn_halts (op : Opcode) (fRead : bytes32 → Accounts → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v)
    (vs : VenomState) (hnh : vs.halted = false) (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 (raccCtx op) vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 (raccCtx op) vs
      = runBlocks 10 (raccCtx op) (raccFn op) { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, raccCtx, raccFn, lookupFunction, fnEntryLabel, raccEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (raccEntrySEnd fRead s0) with hs1
  have hentry : runBlock 9 (raccCtx op) (raccEntry op) s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact raccEntry_runBlock op fRead hnterm hsem s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb (raccFn op).blocks = some (raccEntry op) := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 (raccCtx op) (raccFn op) s0 = runBlocks 9 (raccCtx op) (raccFn op) s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := raccEntrySEnd_lookup fRead s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (fRead s0.callCtx.callvalue s0.accounts) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (raccEntrySEnd fRead s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb (raccFn op).blocks = some r0Next := rfl
  have hhalt := raccNext_halts op s1 6 (EvmYul.UInt256.ofNat 0) (fRead s0.callCtx.callvalue s0.accounts) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩
abbrev RACCUNRES (nm : String) : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP2",
   AsmInst.AsmOp nm, AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next",
   AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"]

theorem raccNext_ready (op : Opcode) (nm : String) {lo : AssocList String Nat}
    (ops : List StackOp) (hexec : executePlan ops = RACCUNRES nm) :
    BodyStepsReadyHTo lo (asmResolve (executePlan ops)).2
      (asmResolve (executePlan ops)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg (raccFn op) z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] := by
  rw [hexec]
  exact bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := raccFn op) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))
theorem codegen_correct_racc (op : Opcode) (nm : String) (fRead : bytes32 → Accounts → bytes32)
    {lo : AssocList String Nat}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP) (hnterm : isTerminator op = false)
    (hcompute : computeOperands (raccLoad op) = (raccLoad op).operands.reverse)
    (hrdy : codegenReadyInst (raccLoad op))
    (hsem : ∀ v : VenomState, stepInstBase (raccLoad op) v = execRead1 (fun addr s => fRead addr s.accounts) (raccLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmStateUnop (fun addr s => fRead addr s.toVenomState.accounts) s)
    (ops : List StackOp) (psFinal : PlanState)
    (hplan : generateFnPlan (raccFn op) 0 0 = some (ops, psFinal))
    (hexec : executePlan ops = RACCUNRES nm)
    (hbodyE : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (raccFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, raccLoad op] (initPlanState 0)).1
      = [AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP2", AsmInst.AsmOp nm])
    (hbodyN : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (raccFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next")).1
      = [AsmInst.AsmOp "MUL"])
    (hpsN : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (raccFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, raccLoad op] (initPlanState 0)).2
      = psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next")
    (hpsStack : (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next").stack
      = [Operand.Var "a", Operand.Var "b", Operand.Var "c"])
    (hpsSpill : ∀ op', alookup' (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next").spilled op' = none)
    (hpsVars : StackIsVars ["a", "b", "c"] (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next"))
    (hpsNstack : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (raccFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next")).2.stack
      = [Operand.Var "a", Operand.Var "e"])
    {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (raccCtx op) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hprog : asmResolve (executePlan ops) = asmResolve (RACCUNRES nm) := by rw [hexec]
  have hoffs : (computeLabelOffsets (executePlan ops)).2 = (computeLabelOffsets (RACCUNRES nm)).2 := by rw [hexec]
  have hlen10 : (asmResolve (RACCUNRES nm)).1.length = 10 := rfl
  have hpcN : pcOfLabel (asmResolve (RACCUNRES nm)).1 "next" = 7 := rfl
  have hpcE0 : pcOfLabel (asmResolve (RACCUNRES nm)).1 "entry" = 0 := rfl
  have hlabE : (executePlan [StackOp.SOLabel (raccEntry op).label]).length = 1 := rfl
  have hlabN : (executePlan [StackOp.SOLabel r0Next.label]).length = 1 := rfl
  have hfnready : ∀ bb ∈ (raccFn op).blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [raccFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [raccEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl
      · unfold codegenReadyInst; decide
      · unfold codegenReadyInst; decide
      · exact hrdy
      · unfold codegenReadyInst; decide
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hpsE : psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv (raccInv fRead)
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    (offsets := (computeLabelOffsets (executePlan ops)).2)
    (fuel := 10) (ctx := raccCtx op) (fn := raccFn op) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := ops) (psFinal := psFinal)
    hplan rfl rfl rfl ?_ ?_ (raccInv_pres op fRead hnterm hsem) ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [raccFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, raccEntry, r0CvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [raccFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hplan
      have hnt : ∀ inst ∈ [r0CvA, r0CvB, raccLoad op], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm
      match k with
      | 0 => exact Or.inl (runBlock_oof (raccCtx op) (raccEntry op) 1 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
               [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 1 => exact Or.inl (runBlock_oof (raccCtx op) (raccEntry op) 2 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
               [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 2 => exact Or.inl (runBlock_oof (raccCtx op) (raccEntry op) 3 [r0CvA, r0CvB, raccLoad op] r0Jmp r0CvA
               [r0CvB, raccLoad op, r0Jmp] s (raccEntrySEnd fRead s) rfl rfl (by decide) hnt (raccEntry_thread op fRead hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | (j+3) =>
      rw [show j+3+1 = ([r0CvA, r0CvB, raccLoad op] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0CvA, r0CvB, raccLoad op]) (jmpInst := r0Jmp) (hd := r0CvA) (tl := [r0CvB, raccLoad op, r0Jmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := r0Next) (sEnd := raccEntrySEnd fRead s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := raccEntry_thread op fRead hsem s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := raccEntry_body op nm fRead hname hnjmp hcompute hsem hasm)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0, hprog]
                       refine ⟨by simp only [hlabE, hlen10]; omega, fun j hj => ?_⟩
                       simp only [hlabE] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc0, hprog, hbodyE]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen10]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j <;> rfl)
        (hps := hpsN)
        (hpc := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen10]; omega)
        (hpush := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hoff_lk := by rw [hoffs]; rfl)
        (hoff := by decide)
        (hpc2 := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen10]; omega)
        (hjump := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hidx_lk := by rw [hprog]; rfl) (hlk' := rfl)
        (hw := by rw [hprog, hbodyE]; simp only [raccEntry, List.length_cons, List.length_nil, hlen10, hpcN, hpcE0]; omega))
    · have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc7 : asm.pc = 7 := by rw [hpc_asm, hprog]; rfl
      match k with
      | 0 => exact Or.inl (runBlock_oof (raccCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (r0Next_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([r0Mul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0Mul]) (retInst := r0Ret) (hd := r0Mul) (tl := [r0Ret])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (fRead s.callCtx.callvalue s.accounts)).2]; exact ha0)
        (hready := raccNext_ready op nm ops hexec)
        (hsd := ⟨hpsSpill, by rw [hpsStack]; decide, by
          intro z hz
          rw [hpsStack] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := hpsVars)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7, hprog]
                       refine ⟨by simp only [hlabN, hlen10]; omega, fun j hj => ?_⟩
                       simp only [hlabN] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc7, hprog, hbodyN]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen10]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j; rfl)
        (hps'stack := by rw [List.nil_append, hpsNstack])
        (hpc := by rw [hpc7, hprog, hbodyN]; simp only [List.length_cons, List.length_nil, hlen10]; omega)
        (hret := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                    simp only [hexec, hpc7, hbodyN, List.length_cons, List.length_nil]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat])
        (hw := by rw [hprog, hbodyN]; simp only [r0Next, List.length_cons, List.length_nil, hlen10, hpcN]; omega))
  case _ =>
    refine ⟨⟨raccEntry op, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel (raccFn op)) (raccFn op) 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan ops)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hplan).symm
    · show (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 "entry" ≤ (asmResolve (executePlan ops)).1.length
      omega
theorem codegen_correct_balFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (raccCtx Opcode.BALANCE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.BALANCE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_racc Opcode.BALANCE "BALANCE" (fun addr accts => EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) accts).balance)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_balance_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_ecsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (raccCtx Opcode.EXTCODESIZE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_racc Opcode.EXTCODESIZE "EXTCODESIZE" (fun addr accts => EvmYul.UInt256.ofNat (lookupAccount (AccountAddress.ofUInt256 addr) accts).code.length)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_extcodesize_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_echFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (raccCtx Opcode.EXTCODEHASH) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (raccFn Opcode.EXTCODEHASH) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_racc Opcode.EXTCODEHASH "EXTCODEHASH" (fun addr accts => let acct := lookupAccount (AccountAddress.ofUInt256 addr) accts;
      if accountEmpty acct then (⟨0⟩ : bytes32) else keccak256 (⟨acct.code.toArray⟩ : ByteArray))
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_extcodehash_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc


/-! ### ✅ The 0-input READ family via the generic `codegen_correct_r0` driver

Each opcode below is a ~15-line instantiation of `codegen_correct_r0` (see the generic driver
above). What was ~475 bespoke lines per read is now the opcode, its name, the read value, its
`asmStep` sim lemma, and the one `venomAsmRel` conjunct feeding `hfeq`. -/

theorem codegen_correct_adrFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.ADDRESS) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ADDRESS) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.ADDRESS "ADDRESS" (fun s => addressToWord s.callCtx.contract) (fun s => addressToWord s.callCtx.contract)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_address_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,h,_,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_orgFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.ORIGIN) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.ORIGIN) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.ORIGIN "ORIGIN" (fun s => addressToWord s.txCtx.origin) (fun s => addressToWord s.txCtx.origin)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_origin_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,h,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_tspFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.TIMESTAMP) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.TIMESTAMP) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.TIMESTAMP "TIMESTAMP" (fun s => s.blockCtx.timestamp) (fun s => s.blockCtx.timestamp)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_timestamp_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_numFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.NUMBER) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.NUMBER) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.NUMBER "NUMBER" (fun s => s.blockCtx.number) (fun s => s.blockCtx.number)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_number_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_chdFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.CHAINID) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CHAINID) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.CHAINID "CHAINID" (fun s => s.txCtx.chainid) (fun s => s.txCtx.chainid)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_chainid_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,h,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_cbsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.COINBASE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.COINBASE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.COINBASE "COINBASE" (fun s => addressToWord s.blockCtx.coinbase) (fun s => addressToWord s.blockCtx.coinbase)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_coinbase_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_gprFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.GASPRICE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASPRICE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.GASPRICE "GASPRICE" (fun s => s.txCtx.gasprice) (fun s => s.txCtx.gasprice)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_gasprice_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,h,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_glmFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.GASLIMIT) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GASLIMIT) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.GASLIMIT "GASLIMIT" (fun s => s.blockCtx.gaslimit) (fun s => s.blockCtx.gaslimit)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_gaslimit_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_cdsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.CALLDATASIZE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CALLDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.CALLDATASIZE "CALLDATASIZE" (fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length) (fun s => EvmYul.UInt256.ofNat s.callCtx.calldata.length)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_calldatasize_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,h,_,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_gsrFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.GAS) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.GAS) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.GAS "GAS" (fun s => EvmYul.UInt256.ofNat s.callCtx.gas) (fun s => EvmYul.UInt256.ofNat s.callCtx.gas)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_gas_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,h,_,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_bfeFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.BASEFEE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.BASEFEE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.BASEFEE "BASEFEE" (fun s => s.blockCtx.basefee) (fun s => s.blockCtx.basefee)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_basefee_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,h,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_cszFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.CODESIZE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.CODESIZE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.CODESIZE "CODESIZE" (fun s => EvmYul.UInt256.ofNat s.code.length) (fun s => EvmYul.UInt256.ofNat s.code.length)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_codesize_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,_,_,_,_,_,h,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_rdsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.RETURNDATASIZE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.RETURNDATASIZE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.RETURNDATASIZE "RETURNDATASIZE" (fun s => EvmYul.UInt256.ofNat s.returndata.size) (fun s => EvmYul.UInt256.ofNat s.returndata.size)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_returndatasize_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,_,_,h,_,_,_,_,_,_⟩ := hr; rw [h])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_sblFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (r0Ctx Opcode.SELFBALANCE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (r0Fn Opcode.SELFBALANCE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_r0 Opcode.SELFBALANCE "SELFBALANCE" (fun s => EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance) (fun s => EvmYul.UInt256.ofNat (lookupAccount s.callCtx.contract s.accounts).balance)
    rfl (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _o2pc _prg _s h hg => asmStep_selfbalance_ok h hg)
    (fun _ v s hr => by obtain ⟨_,_,_,ha,_,_,_,h,_,_,_,_⟩ := hr; rw [h, ha])
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

end Example

end EvmYul.Venom.Hol.Codegen

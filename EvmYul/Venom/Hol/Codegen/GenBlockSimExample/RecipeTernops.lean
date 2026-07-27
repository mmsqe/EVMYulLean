/-
GenBlockSimExample / ternop capstones (ADDMOD, MULMOD)

Split from RecipeFinal for readability; layout only, meaning unchanged. Wrapped in
`namespace …Codegen.Example` and imports the previous part (the read/binop capstone chain).
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeBinops

namespace EvmYul.Venom.Hol.Codegen

namespace Example

/-! ### ✅ A TERNOP (ADDMOD) reaches codegen_correct — `codegen_correct_admFn_recipeW` (3-block)

The ternop arm needs all 3 operands live ⇒ `entry` delivers `[a,b,c,d]`; two cleanup MULs, each in its
OWN block (so its output is live at that block's exit — the same 3-block shape as `csFn`):
```
entry: %a,%b,%c=CV; %d=ADDMOD %a %b %c; JMP work   -- [a,b,c,d]   (ternop, DUP1;DUP3;DUP5;ADDMOD)
work:  %e=MUL %c %d; JMP done                       -- [a,b,e]     (consumes c,d)
done:  %f=MUL %b %e; RETURN %f, %a                  -- [a,f]       (consumes b,e; f=0=e; empty window)
```
-/

def admCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def admCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def admCvC : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }
def admAddmod : Instruction :=
  { id := 3, opcode := Opcode.ADDMOD, operands := [Operand.Var "a", Operand.Var "b", Operand.Var "c"], outputs := ["d"] }
def admJWork : Instruction := { id := 4, opcode := Opcode.JMP, operands := [Operand.Label "work"], outputs := [] }
def admMul1 : Instruction :=
  { id := 5, opcode := Opcode.MUL, operands := [Operand.Var "c", Operand.Var "d"], outputs := ["e"] }
def admJDone : Instruction := { id := 6, opcode := Opcode.JMP, operands := [Operand.Label "done"], outputs := [] }
def admMul2 : Instruction :=
  { id := 7, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "e"], outputs := ["f"] }
def admRet : Instruction :=
  { id := 8, opcode := Opcode.RETURN, operands := [Operand.Var "f", Operand.Var "a"], outputs := [] }
def admEntry : BasicBlock := { label := "entry", instructions := [admCvA, admCvB, admCvC, admAddmod, admJWork] }
def admWork : BasicBlock := { label := "work", instructions := [admMul1, admJDone] }
def admDone : BasicBlock := { label := "done", instructions := [admMul2, admRet] }
def admFn : IrFunction := { name := "main", blocks := [admEntry, admWork, admDone] }
def admCtx : VenomContext := { functions := [admFn], entry := some "main" }

theorem adm_unresolved_asm : executePlan (generateFnPlan admFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp "DUP5", AsmInst.AsmOp "ADDMOD",
     AsmInst.AsmPushLabel "work", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "work",
     AsmInst.AsmOp "MUL", AsmInst.AsmPushLabel "done", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "done",
     AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

abbrev admVal (s : VenomState) : bytes32 :=
  addmod s.callCtx.callvalue s.callCtx.callvalue s.callCtx.callvalue

theorem admEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c", "d"] offsetToPc
      (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 1 [admCvA, admCvB, admCvC, admAddmod] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide),
          cv_step (out := "c") (S := ["a", "b"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"d", "ADDMOD", rfl, rfl, by decide, by decide,
    Or.inr (Or.inr (Or.inr (Or.inl
      ⟨"a", "b", "c", addmod, by decide, by decide, rfl, fun _ => rfl, rfl,
       by decide, by decide, by decide, by decide, by decide, by decide,
       by decide, by decide, by decide, fun _ h hg => asmStep_addmod_ok h hg⟩)))⟩

abbrev admEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "d" (admVal s)
      { updateVar "c" s.callCtx.callvalue
          { updateVar "b" s.callCtx.callvalue
              { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
            with instIdx := 2 }
        with instIdx := 3 }
    with instIdx := 4 }

theorem admEntry_thread (s : VenomState) :
    execBodyThread [admCvA, admCvB, admCvC, admAddmod] 0 { s with instIdx := 0 } = some (admEntrySEnd s) := by
  set S3 : VenomState :=
    { updateVar "c" s.callCtx.callvalue
        { updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }
      with instIdx := 3 } with hS3
  have hla : evalOperand (Operand.Var "a") S3 = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  have hlb : evalOperand (Operand.Var "b") S3 = some s.callCtx.callvalue := by
    show lookupVar "b" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlc : evalOperand (Operand.Var "c") S3 = some s.callCtx.callvalue := by
    show lookupVar "c" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]
  have hsub : stepInstBase admAddmod S3 = ExecResult.OK (updateVar "d" (admVal s) S3) := by
    simp only [admAddmod, stepInstBase, execPure3, hla, hlb, hlc]
  have h1 : stepInstBase admCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase admCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  have h3 : stepInstBase admCvC ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } : VenomState)
      = ExecResult.OK (updateVar "c" s.callCtx.callvalue
          ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 })) := rfl
  show (match stepInstBase admCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [admCvB, admCvC, admAddmod] 1 { s' with instIdx := 1 }
        | _ => none) = some (admEntrySEnd s)
  rw [h1]
  show (match stepInstBase admCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [admCvC, admAddmod] 2 { s' with instIdx := 2 }
        | _ => none) = some (admEntrySEnd s)
  rw [h2]
  show (match stepInstBase admCvC ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [admAddmod] 3 { s' with instIdx := 3 }
        | _ => none) = some (admEntrySEnd s)
  rw [h3]
  show (match stepInstBase admAddmod S3 with
        | ExecResult.OK s' => execBodyThread [] 4 { s' with instIdx := 4 }
        | _ => none) = some (admEntrySEnd s)
  rw [hsub]
  rfl

theorem admEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (admEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (admEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (admEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "d" (admEntrySEnd s) = some (admVal s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "d" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_self]

theorem admEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (4 + (j + 1)) admCtx admEntry s = ExecResult.OK (jumpTo "work" (admEntrySEnd s)) :=
  runBlock_body_jmp admCtx admEntry j [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
    [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) "work" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    (admEntry_thread s) (by simpa [updateVar] using hnh)

/-- `work`'s consuming `MUL %c %d` (mirror, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    eats `[c,d]` off `[a,b,c,d]`, leaving `[a,b,e]`. -/
theorem admWork_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg admFn z.1
        ["a", "b", "e"] false true "work" p)
      (fun _ => 1) ([admMul1].zipIdx 0) ["a", "b", "c", "d"] ["a", "b", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := admFn) (curBbLabel := "work") (base := ["a", "b"]) (x := "c") (y := "d")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev admWorkSEnd (s : VenomState) (wc wd : bytes32) : VenomState :=
  { updateVar "e" (wc * wd) { s with instIdx := 0 } with instIdx := 1 }

theorem admWorkSEnd_lookup (s : VenomState) (wc wd : bytes32) :
    lookupVar "e" (admWorkSEnd s wc wd) = some (wc * wd)
    ∧ lookupVar "a" (admWorkSEnd s wc wd) = lookupVar "a" s
    ∧ lookupVar "b" (admWorkSEnd s wc wd) = lookupVar "b" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_, ?_⟩
  · show lookupVar "a" (updateVar "e" (wc * wd) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
  · show lookupVar "b" (updateVar "e" (wc * wd) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem admWork_thread (s : VenomState) (wc wd : bytes32)
    (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = some wd) :
    execBodyThread [admMul1] 0 { s with instIdx := 0 } = some (admWorkSEnd s wc wd) := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hd' : lookupVar "d" { s with instIdx := 0 } = some wd := hd
  have hstep : stepInstBase admMul1 { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wc * wd) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := admMul1) (f := fun a b => a * b) (x := "c") (y := "d")
      (out := "e") rfl rfl rfl hc' hd'
  show (match stepInstBase admMul1 { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

theorem admMul1_error_c (s : VenomState) (hc : lookupVar "c" s = none) :
    stepInstBase admMul1 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [admMul1, stepInstBase, execPure2, evalOperand, hc']

theorem admMul1_error_d (s : VenomState) (wc : bytes32)
    (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = none) :
    stepInstBase admMul1 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hd' : lookupVar "d" { s with instIdx := 0 } = none := hd
  simp [admMul1, stepInstBase, execPure2, evalOperand, hc', hd']

theorem admWork_runBlock (s : VenomState) (j : Nat) (wc wd : bytes32)
    (hnh : s.halted = false) (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = some wd) :
    runBlock (1 + (j + 1)) admCtx admWork s = ExecResult.OK (jumpTo "done" (admWorkSEnd s wc wd)) :=
  runBlock_body_jmp admCtx admWork j [admMul1] admJDone admMul1 [admJDone] s
    (admWorkSEnd s wc wd) "done" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (admWork_thread s wc wd hc hd) (by simpa [updateVar] using hnh)

/-- `done`'s consuming `MUL %b %e` (mirror) as a `BodyStepsReadyHTo`: eats `[b,e]` off `[a,b,e]`,
    leaving `[a,f]`. -/
theorem admDone_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg admFn z.1
        ["f", "a"] false true "done" p)
      (fun _ => 1) ([admMul2].zipIdx 0) ["a", "b", "e"] ["a", "f"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := admFn) (curBbLabel := "done") (base := ["a"]) (x := "b") (y := "e")
      (out := "f") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev admDoneSEnd (s : VenomState) (wb we : bytes32) : VenomState :=
  { updateVar "f" (wb * we) { s with instIdx := 0 } with instIdx := 1 }

theorem admDoneSEnd_lookup (s : VenomState) (wb we : bytes32) :
    lookupVar "f" (admDoneSEnd s wb we) = some (wb * we)
    ∧ lookupVar "a" (admDoneSEnd s wb we) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "f" (wb * we) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem admDone_thread (s : VenomState) (wb we : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we) :
    execBodyThread [admMul2] 0 { s with instIdx := 0 } = some (admDoneSEnd s wb we) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have he' : lookupVar "e" { s with instIdx := 0 } = some we := he
  have hstep : stepInstBase admMul2 { s with instIdx := 0 }
      = ExecResult.OK (updateVar "f" (wb * we) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := admMul2) (f := fun a b => a * b) (x := "b") (y := "e")
      (out := "f") rfl rfl rfl hb' he'
  show (match stepInstBase admMul2 { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

theorem admMul2_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase admMul2 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [admMul2, stepInstBase, execPure2, evalOperand, hb']

theorem admMul2_error_e (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = none) :
    stepInstBase admMul2 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have he' : lookupVar "e" { s with instIdx := 0 } = none := he
  simp [admMul2, stepInstBase, execPure2, evalOperand, hb', he']

theorem admDone_halts (s : VenomState) (j : Nat) (wb we wa : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) admCtx admDone s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * we).toNat wa.toNat (admDoneSEnd s wb we))
        (admDoneSEnd s wb we))) := by
  obtain ⟨hf, haa⟩ := admDoneSEnd_lookup s wb we
  rw [ha] at haa
  exact runBlock_body_return admCtx admDone j [admMul2] admRet admMul2 [admRet] s (admDoneSEnd s wb we)
    (Operand.Var "f") (Operand.Var "a") (wb * we) wa rfl rfl rfl hf haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (admDone_thread s wb we hb he)

theorem admDone_error_a (s : VenomState) (j : Nat) (wb we : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) admCtx admDone s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨hf, haa⟩ := admDoneSEnd_lookup s wb we
  rw [ha] at haa
  refine runBlock_body_term admCtx admDone j [admMul2] admRet admMul2 [admRet] s (admDoneSEnd s wb we)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (admDone_thread s wb we hb he) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : admDone.instructions = [admMul2] ++ [admRet])
    (admDone_thread s wb we hb he), admRet, stepInstBase, evalOperand, hf, haa, isExternalCall]


theorem admVal_zero (s : VenomState) (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    admVal s = EvmYul.UInt256.ofNat 0 := by
  show addmod s.callCtx.callvalue s.callCtx.callvalue s.callCtx.callvalue = _
  rw [hcv]; decide

abbrev admZ (s : VenomState) (v : String) : Prop :=
  lookupVar v s = none ∨ lookupVar v s = some (EvmYul.UInt256.ofNat 0)

def admInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  admZ s "a" ∧ admZ s "b" ∧ admZ s "c" ∧ admZ s "d" ∧ admZ s "e" ∧ admZ s "f" ∧
  (lookupVar "c" s = some (EvmYul.UInt256.ofNat 0) →
     lookupVar "a" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "work" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "done" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "e" s = some (EvmYul.UInt256.ofNat 0))

theorem admInv_pres : ∀ bb ∈ admFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    admInv s → runBlock f' admCtx bb s = ExecResult.OK s' → admInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, hZa, hZb, hZc, hZd, hZe, hZf, hlink, _, _⟩ := hinv
  simp only [admFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · -- entry: fuel ≥ 5 → jumpTo "work" (admEntrySEnd s)
    have hnt : ∀ inst ∈ [admCvA, admCvB, admCvC, admAddmod], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof admCtx admEntry 0 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
             [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof admCtx admEntry 1 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
             [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof admCtx admEntry 2 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
             [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof admCtx admEntry 3 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
             [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 4 => obtain ⟨e, he⟩ := runBlock_oof admCtx admEntry 4 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
             [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+5) =>
      rw [show j+5 = 4+(j+1) from by omega, admEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0, hd0⟩ := admEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      rw [admVal_zero s hcv] at hd0
      have ha : lookupVar "a" (jumpTo "work" (admEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := ha0
      have hb : lookupVar "b" (jumpTo "work" (admEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hb0
      have hc : lookupVar "c" (jumpTo "work" (admEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hc0
      have hd : lookupVar "d" (jumpTo "work" (admEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hd0
      have hEe : lookupVar "e" (jumpTo "work" (admEntrySEnd s)) = lookupVar "e" s := by
        show lookupVar "e" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
          (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
          lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
      have hEf : lookupVar "f" (jumpTo "work" (admEntrySEnd s)) = lookupVar "f" s := by
        show lookupVar "f" (updateVar "d" (admVal s) (updateVar "c" s.callCtx.callvalue
          (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
          lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
      exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        Or.inr ha, Or.inr hb, Or.inr hc, Or.inr hd,
        (hZe.imp hEe.trans hEe.trans), (hZf.imp hEf.trans hEf.trans),
        fun _ => ⟨ha, hb, hd⟩, fun _ => ⟨ha, hb, hc, hd⟩, fun hdn => by simp [jumpTo] at hdn⟩
  · -- work: reads c,d. Undefined ⇒ head_error. Defined ⇒ csZ 0, link, MUL e=c*d=0.
    rcases hlc : lookupVar "c" s with _ | wc
    · match f' with
      | 0 => rw [runBlock_no_phi 0 admCtx admWork s admMul1 [admJDone] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error admCtx admWork admMul1 [admJDone] s "undefined operand" j rfl
          (by decide) (admMul1_error_c s hlc) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hld : lookupVar "d" s with _ | wd
      · match f' with
        | 0 => rw [runBlock_no_phi 0 admCtx admWork s admMul1 [admJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error admCtx admWork admMul1 [admJDone] s "undefined operand" j rfl
            (by decide) (admMul1_error_d s wc hlc hld) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · have hc0 : wc = EvmYul.UInt256.ofNat 0 := by
          rcases hZc with h | h <;> rw [hlc] at h <;> simp_all
        subst hc0
        obtain ⟨haD, hbD, _⟩ := hlink hlc
        match f' with
        | 0 => rw [runBlock_no_phi 0 admCtx admWork s admMul1 [admJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | 1 =>
          rw [runBlock_no_phi 1 admCtx admWork s admMul1 [admJDone] rfl (by decide)] at hrun
          have hc' : lookupVar "c" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := hlc
          have hd' : lookupVar "d" { s with instIdx := 0 } = some wd := hld
          simp [execBlock, getInstruction, admWork, admMul1, stepInstBase, execPure2, evalOperand,
            isTerminator, hc', hd'] at hrun
        | (j+2) =>
          rw [show j+2 = 1+(j+1) from by omega,
              admWork_runBlock s j (EvmYul.UInt256.ofNat 0) wd hnh hlc hld] at hrun
          injection hrun with h; subst h
          obtain ⟨heD, haaD, hbbD⟩ := admWorkSEnd_lookup s (EvmYul.UInt256.ofNat 0) wd
          have hez : (EvmYul.UInt256.ofNat 0) * wd = EvmYul.UInt256.ofNat 0 := uint256_zero_mul wd
          rw [hez] at heD
          have haE : lookupVar "a" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "a" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "a" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, haaD]; exact haD
          have hbE : lookupVar "b" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "b" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "b" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, hbbD]; exact hbD
          have heE : lookupVar "e" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "e" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "e" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, heD]
          have hcE : lookupVar "c" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "c" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "c" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl,
              show lookupVar "c" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) = lookupVar "c"
                { s with instIdx := 0 } from by
                show lookupVar "c" (updateVar "e" _ { s with instIdx := 0 }) = _
                rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]]; exact hlc
          have hdE : lookupVar "d" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "d" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "d" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl,
              show lookupVar "d" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) = lookupVar "d"
                { s with instIdx := 0 } from by
                show lookupVar "d" (updateVar "e" _ { s with instIdx := 0 }) = _
                rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]]
            exact (hlink hlc).2.2
          have hfE : lookupVar "f" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "f" s := by
            rw [show lookupVar "f" (jumpTo "done" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "f" (admWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl]
            show lookupVar "f" (updateVar "e" _ { s with instIdx := 0 }) = _
            rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
          exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
            Or.inr haE, Or.inr hbE, Or.inr hcE, Or.inr hdE, Or.inr heE, (hZf.imp hfE.trans hfE.trans),
            fun _ => ⟨haE, hbE, hdE⟩, fun hw => by simp [jumpTo] at hw, fun _ => ⟨haE, hbE, heE⟩⟩
  · -- done: MUL then RETURN — never yields OK
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 admCtx admDone s admMul2 [admRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error admCtx admDone admMul2 [admRet] s "undefined operand" j rfl
          (by decide) (admMul2_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hle : lookupVar "e" s with _ | we
      · match f' with
        | 0 => rw [runBlock_no_phi 0 admCtx admDone s admMul2 [admRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error admCtx admDone admMul2 [admRet] s "undefined operand" j rfl
            (by decide) (admMul2_error_e s wb hlb hle) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 admCtx admDone s admMul2 [admRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof admCtx admDone 1 [admMul2] admRet admMul2 [admRet] s
                   (admDoneSEnd s wb we) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (admDone_thread s wb we hlb hle) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, admDone_error_a s j wb we hlb hle hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 admCtx admDone s admMul2 [admRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof admCtx admDone 1 [admMul2] admRet admMul2 [admRet] s
                   (admDoneSEnd s wb we) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (admDone_thread s wb we hlb hle) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, admDone_halts s j wb we wa hlb hle hla] at hrun
            exact absurd hrun (by simp)

theorem admFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 admCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 admCtx vs
      = runBlocks 10 admCtx admFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, admCtx, admFn, lookupFunction, fnEntryLabel, admEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "work" (admEntrySEnd s0) with hs1
  have hentry : runBlock 9 admCtx admEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 4 + (4 + 1) from by omega]; exact admEntry_runBlock s0 4 hnh0
  have hlk0 : lookupBlock s0.currentBb admFn.blocks = some admEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 admCtx admFn s0 = runBlocks 9 admCtx admFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1, hd1⟩ := admEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  rw [admVal_zero s0 hcv0] at hd1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 0) := hc1
  have hd1' : lookupVar "d" s1 = some (EvmYul.UInt256.ofNat 0) := hd1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  set s2 : VenomState := jumpTo "done" (admWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0)) with hs2
  have hwork : runBlock 8 admCtx admWork s1 = ExecResult.OK s2 := by
    rw [show (8 : Nat) = 1 + (6 + 1) from by omega]
    exact admWork_runBlock s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) hnh1 hc1' hd1'
  have hlk1 : lookupBlock s1.currentBb admFn.blocks = some admWork := rfl
  have hnh2 : s2.halted = false := by rw [hs2]; simpa [jumpTo, updateVar] using hnh1
  have hstep1 : runBlocks 9 admCtx admFn s1 = runBlocks 8 admCtx admFn s2 :=
    runBlocks_step_of_block (fuel := 8) hlk1 hwork hnh2
  obtain ⟨he2, ha2, hb2⟩ := admWorkSEnd_lookup s1 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
  have hez : (EvmYul.UInt256.ofNat 0) * (EvmYul.UInt256.ofNat 0) = EvmYul.UInt256.ofNat 0 :=
    uint256_zero_mul _
  rw [hez] at he2
  have he2' : lookupVar "e" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "e" s2 = lookupVar "e" (admWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, he2]
  have hb2' : lookupVar "b" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "b" s2 = lookupVar "b" (admWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, hb2]; exact hb1'
  have ha2' : lookupVar "a" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "a" s2 = lookupVar "a" (admWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, ha2]; exact ha1'
  have hlk2 : lookupBlock s2.currentBb admFn.blocks = some admDone := rfl
  have hhalt := admDone_halts s2 5 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0) hb2' he2' ha2'
  rw [show (1 : Nat) + (5 + 1) = 7 from by omega] at hhalt
  rw [h0, hstep0, hstep1]
  exact ⟨_, runBlocks_haltDirect_of_block hlk2 hhalt⟩


set_option maxHeartbeats 4000000 in
/-- **A TERNOP (ADDMOD) capstone.** `codegen_correct` for the 3-block function
    `entry: %a,%b,%c=CV; %d=ADDMOD %a %b %c; JMP work` / `work: %e=MUL %c %d; JMP done` /
    `done: %f=MUL %b %e; RETURN %f %a`. `entry`'s ADDMOD is the `RegularStep` ternop sub-arm
    (`asmStep_addmod_ok`, DUP1;DUP3;DUP5;ADDMOD); each cleanup MUL lives in its own block so its output
    is live at that block's exit (the 3-block shape `csFn` established). All-zero ⇒ `e=f=0`
    (`uint256_zero_mul`), size `a=0` ⇒ empty return window. `entry` via `hsupplyW_regularJmp`, `work`
    via `hsupplyW_regularJmpTo` (`admWork_ready`), `done` via `hsupplyW_regularReturnTo` (`admDone_ready`). -/
theorem codegen_correct_admFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hclean : lookupVar "a" vs = none ∧ lookupVar "b" vs = none ∧ lookupVar "c" vs = none
      ∧ lookupVar "d" vs = none ∧ lookupVar "e" vs = none ∧ lookupVar "f" vs = none)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 admCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ admFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [admFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [admEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [admWork, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [admDone, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan admFn 0 0
      = some ((generateFnPlan admFn 0 0).get!.1, (generateFnPlan admFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel admFn) admFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv admInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel admFn) admFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan admFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := admCtx) (fn := admFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan admFn 0 0).get!.1) (psFinal := (generateFnPlan admFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ admInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero,
      Or.inl hclean.1, Or.inl hclean.2.1, Or.inl hclean.2.2.1, Or.inl hclean.2.2.2.1,
      Or.inl hclean.2.2.2.2.1, Or.inl hclean.2.2.2.2.2,
      (fun h => absurd (hclean.2.2.1.symm.trans h) (by simp)),
      fun h => by simp at h, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [admFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, admEntry, admCvA]
    · simp [runBlock, evalPhis, execBlock, admWork, admMul1]
    · simp [runBlock, evalPhis, execBlock, admDone, admMul2]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [admFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · -- entry: 3 CV + ADDMOD (duplicating) + JMP work
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [admCvA, admCvB, admCvC, admAddmod], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof admCtx admEntry 1 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
               [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof admCtx admEntry 2 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
               [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof admCtx admEntry 3 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
               [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide))
      | 3 => exact Or.inl (runBlock_oof admCtx admEntry 4 [admCvA, admCvB, admCvC, admAddmod] admJWork admCvA
               [admCvB, admCvC, admAddmod, admJWork] s (admEntrySEnd s) rfl rfl (by decide) hnt (admEntry_thread s) (by decide))
      | (j+4) =>
      rw [show j+4+1 = ([admCvA, admCvB, admCvC, admAddmod] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [admCvA, admCvB, admCvC, admAddmod]) (jmpInst := admJWork) (hd := admCvA)
        (tl := [admCvB, admCvC, admAddmod, admJWork])
        (nextLiveness := ["a", "b", "c", "d"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "work") (off := 12) (bb' := admWork) (sEnd := admEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := admEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := admEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 7 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- work: the CONSUMING MUL %c %d + JMP done
      have hlbl : s.currentBb = "work" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, _, _, _, _, _, _, hwork, _⟩ := hinv
      obtain ⟨haw, hbw, hcw, hdw⟩ := hwork hlbl
      have hpc10 : asm.pc = 10 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof admCtx admWork 1 [admMul1] admJDone admMul1 [admJDone] s
               (admWorkSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (admWork_thread s _ _ hcw hdw) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([admMul1] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmpTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [admMul1]) (jmpInst := admJDone) (hd := admMul1) (tl := [admJDone])
        (nextLiveness := ["a", "b", "e"]) (curBbLabel := "work") (dem := 1)
        (S := ["a", "b", "c", "d"]) (Sn := ["a", "b", "e"])
        (ps0 := psOfFn (fnPlanFuel admFn) admFn 0 0 "work") (lbl := "done") (off := 18) (bb' := admDone)
        (sEnd := admWorkSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := admWork_thread s _ _ hcw hdw)
        (hnothalt := by simpa [updateVar] using hhalt)
        (hready := admWork_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel admFn) admFn 0 0 "work").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c", Operand.Var "d"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, haw⟩
          · exact ⟨_, hbw⟩
          · exact ⟨_, hcw⟩
          · exact ⟨_, hdw⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps := rfl) (hpc := by rw [hpc10]; decide) (hpush := by simp only [hpc10]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc10]; decide)
        (hjump := by simp only [hpc10]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- done: the CONSUMING MUL %b %e + body-then-RETURN
      have hlbl : s.currentBb = "done" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hdone⟩ := hinv
      obtain ⟨ha0, hb0, he0⟩ := hdone hlbl
      have hpc14 : asm.pc = 14 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof admCtx admDone 1 [admMul2] admRet admMul2 [admRet] s
               (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (admDone_thread s _ _ hb0 he0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([admMul2] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [admMul2]) (retInst := admRet) (hd := admMul2) (tl := [admRet])
        (nextLiveness := ["f", "a"]) (curBbLabel := "done") (dem := 1)
        (S := ["a", "b", "e"]) (Sn := ["a", "f"])
        (ps0 := psOfFn (fnPlanFuel admFn) admFn 0 0 "done") (offv := "f") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := admDone_thread s _ _ hb0 he0)
        (hevaloff := by rw [show evalOperand (Operand.Var "f")
              (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "f" (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (admDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (admDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "f")
            = lookupVar "f" (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (admDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (admDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (admDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := admDone_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel admFn) admFn 0 0 "done").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "e"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, he0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc14]; decide) (hret := by simp only [hpc14]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨admEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel admFn) admFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan admFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ A TERNOP (MULMOD) reaches codegen_correct — `codegen_correct_mmdFn_recipeW` (3-block)

The ternop arm needs all 3 operands live ⇒ `entry` delivers `[a,b,c,d]`; two cleanup MULs, each in its
OWN block (so its output is live at that block's exit — the same 3-block shape as `csFn`):
```
entry: %a,%b,%c=CV; %d=MULMOD %a %b %c; JMP work   -- [a,b,c,d]   (ternop, DUP1;DUP3;DUP5;MULMOD)
work:  %e=MUL %c %d; JMP done                       -- [a,b,e]     (consumes c,d)
done:  %f=MUL %b %e; RETURN %f, %a                  -- [a,f]       (consumes b,e; f=0=e; empty window)
```
-/

def mmdCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def mmdCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def mmdCvC : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["c"] }
def mmdMulmod : Instruction :=
  { id := 3, opcode := Opcode.MULMOD, operands := [Operand.Var "a", Operand.Var "b", Operand.Var "c"], outputs := ["d"] }
def mmdJWork : Instruction := { id := 4, opcode := Opcode.JMP, operands := [Operand.Label "work"], outputs := [] }
def mmdMul1 : Instruction :=
  { id := 5, opcode := Opcode.MUL, operands := [Operand.Var "c", Operand.Var "d"], outputs := ["e"] }
def mmdJDone : Instruction := { id := 6, opcode := Opcode.JMP, operands := [Operand.Label "done"], outputs := [] }
def mmdMul2 : Instruction :=
  { id := 7, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "e"], outputs := ["f"] }
def mmdRet : Instruction :=
  { id := 8, opcode := Opcode.RETURN, operands := [Operand.Var "f", Operand.Var "a"], outputs := [] }
def mmdEntry : BasicBlock := { label := "entry", instructions := [mmdCvA, mmdCvB, mmdCvC, mmdMulmod, mmdJWork] }
def mmdWork : BasicBlock := { label := "work", instructions := [mmdMul1, mmdJDone] }
def mmdDone : BasicBlock := { label := "done", instructions := [mmdMul2, mmdRet] }
def mmdFn : IrFunction := { name := "main", blocks := [mmdEntry, mmdWork, mmdDone] }
def mmdCtx : VenomContext := { functions := [mmdFn], entry := some "main" }

theorem mmd_unresolved_asm : executePlan (generateFnPlan mmdFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp "DUP5", AsmInst.AsmOp "MULMOD",
     AsmInst.AsmPushLabel "work", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "work",
     AsmInst.AsmOp "MUL", AsmInst.AsmPushLabel "done", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "done",
     AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

abbrev mmdVal (s : VenomState) : bytes32 :=
  mulmod s.callCtx.callvalue s.callCtx.callvalue s.callCtx.callvalue

theorem mmdEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c", "d"] offsetToPc
      (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 1 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide),
          cv_step (out := "c") (S := ["a", "b"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"d", "MULMOD", rfl, rfl, by decide, by decide,
    Or.inr (Or.inr (Or.inr (Or.inl
      ⟨"a", "b", "c", mulmod, by decide, by decide, rfl, fun _ => rfl, rfl,
       by decide, by decide, by decide, by decide, by decide, by decide,
       by decide, by decide, by decide, fun _ h hg => asmStep_mulmod_ok h hg⟩)))⟩

abbrev mmdEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "d" (mmdVal s)
      { updateVar "c" s.callCtx.callvalue
          { updateVar "b" s.callCtx.callvalue
              { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
            with instIdx := 2 }
        with instIdx := 3 }
    with instIdx := 4 }

theorem mmdEntry_thread (s : VenomState) :
    execBodyThread [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] 0 { s with instIdx := 0 } = some (mmdEntrySEnd s) := by
  set S3 : VenomState :=
    { updateVar "c" s.callCtx.callvalue
        { updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }
      with instIdx := 3 } with hS3
  have hla : evalOperand (Operand.Var "a") S3 = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  have hlb : evalOperand (Operand.Var "b") S3 = some s.callCtx.callvalue := by
    show lookupVar "b" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlc : evalOperand (Operand.Var "c") S3 = some s.callCtx.callvalue := by
    show lookupVar "c" (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]
  have hsub : stepInstBase mmdMulmod S3 = ExecResult.OK (updateVar "d" (mmdVal s) S3) := by
    simp only [mmdMulmod, stepInstBase, execPure3, hla, hlb, hlc]
  have h1 : stepInstBase mmdCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase mmdCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  have h3 : stepInstBase mmdCvC ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } : VenomState)
      = ExecResult.OK (updateVar "c" s.callCtx.callvalue
          ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 })) := rfl
  show (match stepInstBase mmdCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [mmdCvB, mmdCvC, mmdMulmod] 1 { s' with instIdx := 1 }
        | _ => none) = some (mmdEntrySEnd s)
  rw [h1]
  show (match stepInstBase mmdCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [mmdCvC, mmdMulmod] 2 { s' with instIdx := 2 }
        | _ => none) = some (mmdEntrySEnd s)
  rw [h2]
  show (match stepInstBase mmdCvC ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [mmdMulmod] 3 { s' with instIdx := 3 }
        | _ => none) = some (mmdEntrySEnd s)
  rw [h3]
  show (match stepInstBase mmdMulmod S3 with
        | ExecResult.OK s' => execBodyThread [] 4 { s' with instIdx := 4 }
        | _ => none) = some (mmdEntrySEnd s)
  rw [hsub]
  rfl

theorem mmdEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (mmdEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (mmdEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (mmdEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "d" (mmdEntrySEnd s) = some (mmdVal s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "d" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
    rw [lookupVar_updateVar_self]

theorem mmdEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (4 + (j + 1)) mmdCtx mmdEntry s = ExecResult.OK (jumpTo "work" (mmdEntrySEnd s)) :=
  runBlock_body_jmp mmdCtx mmdEntry j [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
    [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) "work" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    (mmdEntry_thread s) (by simpa [updateVar] using hnh)

/-- `work`'s consuming `MUL %c %d` (mirror, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    eats `[c,d]` off `[a,b,c,d]`, leaving `[a,b,e]`. -/
theorem mmdWork_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg mmdFn z.1
        ["a", "b", "e"] false true "work" p)
      (fun _ => 1) ([mmdMul1].zipIdx 0) ["a", "b", "c", "d"] ["a", "b", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := mmdFn) (curBbLabel := "work") (base := ["a", "b"]) (x := "c") (y := "d")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev mmdWorkSEnd (s : VenomState) (wc wd : bytes32) : VenomState :=
  { updateVar "e" (wc * wd) { s with instIdx := 0 } with instIdx := 1 }

theorem mmdWorkSEnd_lookup (s : VenomState) (wc wd : bytes32) :
    lookupVar "e" (mmdWorkSEnd s wc wd) = some (wc * wd)
    ∧ lookupVar "a" (mmdWorkSEnd s wc wd) = lookupVar "a" s
    ∧ lookupVar "b" (mmdWorkSEnd s wc wd) = lookupVar "b" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_, ?_⟩
  · show lookupVar "a" (updateVar "e" (wc * wd) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
  · show lookupVar "b" (updateVar "e" (wc * wd) { s with instIdx := 0 }) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem mmdWork_thread (s : VenomState) (wc wd : bytes32)
    (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = some wd) :
    execBodyThread [mmdMul1] 0 { s with instIdx := 0 } = some (mmdWorkSEnd s wc wd) := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hd' : lookupVar "d" { s with instIdx := 0 } = some wd := hd
  have hstep : stepInstBase mmdMul1 { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wc * wd) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := mmdMul1) (f := fun a b => a * b) (x := "c") (y := "d")
      (out := "e") rfl rfl rfl hc' hd'
  show (match stepInstBase mmdMul1 { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

theorem mmdMul1_error_c (s : VenomState) (hc : lookupVar "c" s = none) :
    stepInstBase mmdMul1 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [mmdMul1, stepInstBase, execPure2, evalOperand, hc']

theorem mmdMul1_error_d (s : VenomState) (wc : bytes32)
    (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = none) :
    stepInstBase mmdMul1 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hd' : lookupVar "d" { s with instIdx := 0 } = none := hd
  simp [mmdMul1, stepInstBase, execPure2, evalOperand, hc', hd']

theorem mmdWork_runBlock (s : VenomState) (j : Nat) (wc wd : bytes32)
    (hnh : s.halted = false) (hc : lookupVar "c" s = some wc) (hd : lookupVar "d" s = some wd) :
    runBlock (1 + (j + 1)) mmdCtx mmdWork s = ExecResult.OK (jumpTo "done" (mmdWorkSEnd s wc wd)) :=
  runBlock_body_jmp mmdCtx mmdWork j [mmdMul1] mmdJDone mmdMul1 [mmdJDone] s
    (mmdWorkSEnd s wc wd) "done" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (mmdWork_thread s wc wd hc hd) (by simpa [updateVar] using hnh)

/-- `done`'s consuming `MUL %b %e` (mirror) as a `BodyStepsReadyHTo`: eats `[b,e]` off `[a,b,e]`,
    leaving `[a,f]`. -/
theorem mmdDone_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg mmdFn z.1
        ["f", "a"] false true "done" p)
      (fun _ => 1) ([mmdMul2].zipIdx 0) ["a", "b", "e"] ["a", "f"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := mmdFn) (curBbLabel := "done") (base := ["a"]) (x := "b") (y := "e")
      (out := "f") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev mmdDoneSEnd (s : VenomState) (wb we : bytes32) : VenomState :=
  { updateVar "f" (wb * we) { s with instIdx := 0 } with instIdx := 1 }

theorem mmdDoneSEnd_lookup (s : VenomState) (wb we : bytes32) :
    lookupVar "f" (mmdDoneSEnd s wb we) = some (wb * we)
    ∧ lookupVar "a" (mmdDoneSEnd s wb we) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "f" (wb * we) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem mmdDone_thread (s : VenomState) (wb we : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we) :
    execBodyThread [mmdMul2] 0 { s with instIdx := 0 } = some (mmdDoneSEnd s wb we) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have he' : lookupVar "e" { s with instIdx := 0 } = some we := he
  have hstep : stepInstBase mmdMul2 { s with instIdx := 0 }
      = ExecResult.OK (updateVar "f" (wb * we) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := mmdMul2) (f := fun a b => a * b) (x := "b") (y := "e")
      (out := "f") rfl rfl rfl hb' he'
  show (match stepInstBase mmdMul2 { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

theorem mmdMul2_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase mmdMul2 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [mmdMul2, stepInstBase, execPure2, evalOperand, hb']

theorem mmdMul2_error_e (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = none) :
    stepInstBase mmdMul2 { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have he' : lookupVar "e" { s with instIdx := 0 } = none := he
  simp [mmdMul2, stepInstBase, execPure2, evalOperand, hb', he']

theorem mmdDone_halts (s : VenomState) (j : Nat) (wb we wa : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) mmdCtx mmdDone s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * we).toNat wa.toNat (mmdDoneSEnd s wb we))
        (mmdDoneSEnd s wb we))) := by
  obtain ⟨hf, haa⟩ := mmdDoneSEnd_lookup s wb we
  rw [ha] at haa
  exact runBlock_body_return mmdCtx mmdDone j [mmdMul2] mmdRet mmdMul2 [mmdRet] s (mmdDoneSEnd s wb we)
    (Operand.Var "f") (Operand.Var "a") (wb * we) wa rfl rfl rfl hf haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (mmdDone_thread s wb we hb he)

theorem mmdDone_error_a (s : VenomState) (j : Nat) (wb we : bytes32)
    (hb : lookupVar "b" s = some wb) (he : lookupVar "e" s = some we) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) mmdCtx mmdDone s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨hf, haa⟩ := mmdDoneSEnd_lookup s wb we
  rw [ha] at haa
  refine runBlock_body_term mmdCtx mmdDone j [mmdMul2] mmdRet mmdMul2 [mmdRet] s (mmdDoneSEnd s wb we)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (mmdDone_thread s wb we hb he) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : mmdDone.instructions = [mmdMul2] ++ [mmdRet])
    (mmdDone_thread s wb we hb he), mmdRet, stepInstBase, evalOperand, hf, haa, isExternalCall]


theorem mmdVal_zero (s : VenomState) (hcv : s.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    mmdVal s = EvmYul.UInt256.ofNat 0 := by
  show mulmod s.callCtx.callvalue s.callCtx.callvalue s.callCtx.callvalue = _
  rw [hcv]; decide

abbrev mmdZ (s : VenomState) (v : String) : Prop :=
  lookupVar v s = none ∨ lookupVar v s = some (EvmYul.UInt256.ofNat 0)

def mmdInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  mmdZ s "a" ∧ mmdZ s "b" ∧ mmdZ s "c" ∧ mmdZ s "d" ∧ mmdZ s "e" ∧ mmdZ s "f" ∧
  (lookupVar "c" s = some (EvmYul.UInt256.ofNat 0) →
     lookupVar "a" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "work" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "done" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
     ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0) ∧ lookupVar "e" s = some (EvmYul.UInt256.ofNat 0))

theorem mmdInv_pres : ∀ bb ∈ mmdFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mmdInv s → runBlock f' mmdCtx bb s = ExecResult.OK s' → mmdInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, hZa, hZb, hZc, hZd, hZe, hZf, hlink, _, _⟩ := hinv
  simp only [mmdFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · -- entry: fuel ≥ 5 → jumpTo "work" (mmdEntrySEnd s)
    have hnt : ∀ inst ∈ [mmdCvA, mmdCvB, mmdCvC, mmdMulmod], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdEntry 0 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
             [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdEntry 1 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
             [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdEntry 2 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
             [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdEntry 3 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
             [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 4 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdEntry 4 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
             [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+5) =>
      rw [show j+5 = 4+(j+1) from by omega, mmdEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0, hd0⟩ := mmdEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      rw [mmdVal_zero s hcv] at hd0
      have ha : lookupVar "a" (jumpTo "work" (mmdEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := ha0
      have hb : lookupVar "b" (jumpTo "work" (mmdEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hb0
      have hc : lookupVar "c" (jumpTo "work" (mmdEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hc0
      have hd : lookupVar "d" (jumpTo "work" (mmdEntrySEnd s)) = some (EvmYul.UInt256.ofNat 0) := hd0
      have hEe : lookupVar "e" (jumpTo "work" (mmdEntrySEnd s)) = lookupVar "e" s := by
        show lookupVar "e" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
          (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
          lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
      have hEf : lookupVar "f" (jumpTo "work" (mmdEntrySEnd s)) = lookupVar "f" s := by
        show lookupVar "f" (updateVar "d" (mmdVal s) (updateVar "c" s.callCtx.callvalue
          (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })))) = _
        rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
          lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
      exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        Or.inr ha, Or.inr hb, Or.inr hc, Or.inr hd,
        (hZe.imp hEe.trans hEe.trans), (hZf.imp hEf.trans hEf.trans),
        fun _ => ⟨ha, hb, hd⟩, fun _ => ⟨ha, hb, hc, hd⟩, fun hdn => by simp [jumpTo] at hdn⟩
  · -- work: reads c,d. Undefined ⇒ head_error. Defined ⇒ csZ 0, link, MUL e=c*d=0.
    rcases hlc : lookupVar "c" s with _ | wc
    · match f' with
      | 0 => rw [runBlock_no_phi 0 mmdCtx mmdWork s mmdMul1 [mmdJDone] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error mmdCtx mmdWork mmdMul1 [mmdJDone] s "undefined operand" j rfl
          (by decide) (mmdMul1_error_c s hlc) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hld : lookupVar "d" s with _ | wd
      · match f' with
        | 0 => rw [runBlock_no_phi 0 mmdCtx mmdWork s mmdMul1 [mmdJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error mmdCtx mmdWork mmdMul1 [mmdJDone] s "undefined operand" j rfl
            (by decide) (mmdMul1_error_d s wc hlc hld) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · have hc0 : wc = EvmYul.UInt256.ofNat 0 := by
          rcases hZc with h | h <;> rw [hlc] at h <;> simp_all
        subst hc0
        obtain ⟨haD, hbD, _⟩ := hlink hlc
        match f' with
        | 0 => rw [runBlock_no_phi 0 mmdCtx mmdWork s mmdMul1 [mmdJDone] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | 1 =>
          rw [runBlock_no_phi 1 mmdCtx mmdWork s mmdMul1 [mmdJDone] rfl (by decide)] at hrun
          have hc' : lookupVar "c" { s with instIdx := 0 } = some (EvmYul.UInt256.ofNat 0) := hlc
          have hd' : lookupVar "d" { s with instIdx := 0 } = some wd := hld
          simp [execBlock, getInstruction, mmdWork, mmdMul1, stepInstBase, execPure2, evalOperand,
            isTerminator, hc', hd'] at hrun
        | (j+2) =>
          rw [show j+2 = 1+(j+1) from by omega,
              mmdWork_runBlock s j (EvmYul.UInt256.ofNat 0) wd hnh hlc hld] at hrun
          injection hrun with h; subst h
          obtain ⟨heD, haaD, hbbD⟩ := mmdWorkSEnd_lookup s (EvmYul.UInt256.ofNat 0) wd
          have hez : (EvmYul.UInt256.ofNat 0) * wd = EvmYul.UInt256.ofNat 0 := uint256_zero_mul wd
          rw [hez] at heD
          have haE : lookupVar "a" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "a" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "a" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, haaD]; exact haD
          have hbE : lookupVar "b" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "b" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "b" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, hbbD]; exact hbD
          have heE : lookupVar "e" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "e" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "e" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl, heD]
          have hcE : lookupVar "c" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "c" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "c" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl,
              show lookupVar "c" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) = lookupVar "c"
                { s with instIdx := 0 } from by
                show lookupVar "c" (updateVar "e" _ { s with instIdx := 0 }) = _
                rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]]; exact hlc
          have hdE : lookupVar "d" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = some (EvmYul.UInt256.ofNat 0) := by
            rw [show lookupVar "d" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "d" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl,
              show lookupVar "d" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) = lookupVar "d"
                { s with instIdx := 0 } from by
                show lookupVar "d" (updateVar "e" _ { s with instIdx := 0 }) = _
                rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]]
            exact (hlink hlc).2.2
          have hfE : lookupVar "f" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "f" s := by
            rw [show lookupVar "f" (jumpTo "done" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd))
              = lookupVar "f" (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) wd) from rfl]
            show lookupVar "f" (updateVar "e" _ { s with instIdx := 0 }) = _
            rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl
          exact ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
            Or.inr haE, Or.inr hbE, Or.inr hcE, Or.inr hdE, Or.inr heE, (hZf.imp hfE.trans hfE.trans),
            fun _ => ⟨haE, hbE, hdE⟩, fun hw => by simp [jumpTo] at hw, fun _ => ⟨haE, hbE, heE⟩⟩
  · -- done: MUL then RETURN — never yields OK
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 mmdCtx mmdDone s mmdMul2 [mmdRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error mmdCtx mmdDone mmdMul2 [mmdRet] s "undefined operand" j rfl
          (by decide) (mmdMul2_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hle : lookupVar "e" s with _ | we
      · match f' with
        | 0 => rw [runBlock_no_phi 0 mmdCtx mmdDone s mmdMul2 [mmdRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error mmdCtx mmdDone mmdMul2 [mmdRet] s "undefined operand" j rfl
            (by decide) (mmdMul2_error_e s wb hlb hle) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mmdCtx mmdDone s mmdMul2 [mmdRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdDone 1 [mmdMul2] mmdRet mmdMul2 [mmdRet] s
                   (mmdDoneSEnd s wb we) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (mmdDone_thread s wb we hlb hle) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mmdDone_error_a s j wb we hlb hle hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mmdCtx mmdDone s mmdMul2 [mmdRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mmdCtx mmdDone 1 [mmdMul2] mmdRet mmdMul2 [mmdRet] s
                   (mmdDoneSEnd s wb we) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (mmdDone_thread s wb we hlb hle) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mmdDone_halts s j wb we wa hlb hle hla] at hrun
            exact absurd hrun (by simp)

theorem mmdFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 mmdCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 mmdCtx vs
      = runBlocks 10 mmdCtx mmdFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, mmdCtx, mmdFn, lookupFunction, fnEntryLabel, mmdEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "work" (mmdEntrySEnd s0) with hs1
  have hentry : runBlock 9 mmdCtx mmdEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 4 + (4 + 1) from by omega]; exact mmdEntry_runBlock s0 4 hnh0
  have hlk0 : lookupBlock s0.currentBb mmdFn.blocks = some mmdEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 mmdCtx mmdFn s0 = runBlocks 9 mmdCtx mmdFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1, hd1⟩ := mmdEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  rw [mmdVal_zero s0 hcv0] at hd1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.ofNat 0) := hc1
  have hd1' : lookupVar "d" s1 = some (EvmYul.UInt256.ofNat 0) := hd1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  set s2 : VenomState := jumpTo "done" (mmdWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0)) with hs2
  have hwork : runBlock 8 mmdCtx mmdWork s1 = ExecResult.OK s2 := by
    rw [show (8 : Nat) = 1 + (6 + 1) from by omega]
    exact mmdWork_runBlock s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0) hnh1 hc1' hd1'
  have hlk1 : lookupBlock s1.currentBb mmdFn.blocks = some mmdWork := rfl
  have hnh2 : s2.halted = false := by rw [hs2]; simpa [jumpTo, updateVar] using hnh1
  have hstep1 : runBlocks 9 mmdCtx mmdFn s1 = runBlocks 8 mmdCtx mmdFn s2 :=
    runBlocks_step_of_block (fuel := 8) hlk1 hwork hnh2
  obtain ⟨he2, ha2, hb2⟩ := mmdWorkSEnd_lookup s1 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
  have hez : (EvmYul.UInt256.ofNat 0) * (EvmYul.UInt256.ofNat 0) = EvmYul.UInt256.ofNat 0 :=
    uint256_zero_mul _
  rw [hez] at he2
  have he2' : lookupVar "e" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "e" s2 = lookupVar "e" (mmdWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, he2]
  have hb2' : lookupVar "b" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "b" s2 = lookupVar "b" (mmdWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, hb2]; exact hb1'
  have ha2' : lookupVar "a" s2 = some (EvmYul.UInt256.ofNat 0) := by
    rw [show lookupVar "a" s2 = lookupVar "a" (mmdWorkSEnd s1 (EvmYul.UInt256.ofNat 0)
      (EvmYul.UInt256.ofNat 0)) from rfl, ha2]; exact ha1'
  have hlk2 : lookupBlock s2.currentBb mmdFn.blocks = some mmdDone := rfl
  have hhalt := mmdDone_halts s2 5 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    (EvmYul.UInt256.ofNat 0) hb2' he2' ha2'
  rw [show (1 : Nat) + (5 + 1) = 7 from by omega] at hhalt
  rw [h0, hstep0, hstep1]
  exact ⟨_, runBlocks_haltDirect_of_block hlk2 hhalt⟩


set_option maxHeartbeats 4000000 in
/-- **A TERNOP (MULMOD) capstone.** `codegen_correct` for the 3-block function
    `entry: %a,%b,%c=CV; %d=MULMOD %a %b %c; JMP work` / `work: %e=MUL %c %d; JMP done` /
    `done: %f=MUL %b %e; RETURN %f %a`. `entry`'s MULMOD is the `RegularStep` ternop sub-arm
    (`asmStep_mulmod_ok`, DUP1;DUP3;DUP5;MULMOD); each cleanup MUL lives in its own block so its output
    is live at that block's exit (the 3-block shape `csFn` established). All-zero ⇒ `e=f=0`
    (`uint256_zero_mul`), size `a=0` ⇒ empty return window. `entry` via `hsupplyW_regularJmp`, `work`
    via `hsupplyW_regularJmpTo` (`mmdWork_ready`), `done` via `hsupplyW_regularReturnTo` (`mmdDone_ready`). -/
theorem codegen_correct_mmdFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hclean : lookupVar "a" vs = none ∧ lookupVar "b" vs = none ∧ lookupVar "c" vs = none
      ∧ lookupVar "d" vs = none ∧ lookupVar "e" vs = none ∧ lookupVar "f" vs = none)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 mmdCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ mmdFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [mmdFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [mmdEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [mmdWork, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [mmdDone, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan mmdFn 0 0
      = some ((generateFnPlan mmdFn 0 0).get!.1, (generateFnPlan mmdFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv mmdInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel mmdFn) mmdFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan mmdFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := mmdCtx) (fn := mmdFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan mmdFn 0 0).get!.1) (psFinal := (generateFnPlan mmdFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ mmdInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero,
      Or.inl hclean.1, Or.inl hclean.2.1, Or.inl hclean.2.2.1, Or.inl hclean.2.2.2.1,
      Or.inl hclean.2.2.2.2.1, Or.inl hclean.2.2.2.2.2,
      (fun h => absurd (hclean.2.2.1.symm.trans h) (by simp)),
      fun h => by simp at h, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [mmdFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, mmdEntry, mmdCvA]
    · simp [runBlock, evalPhis, execBlock, mmdWork, mmdMul1]
    · simp [runBlock, evalPhis, execBlock, mmdDone, mmdMul2]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [mmdFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · -- entry: 3 CV + MULMOD (duplicating) + JMP work
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [mmdCvA, mmdCvB, mmdCvC, mmdMulmod], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mmdCtx mmdEntry 1 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
               [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof mmdCtx mmdEntry 2 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
               [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof mmdCtx mmdEntry 3 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
               [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide))
      | 3 => exact Or.inl (runBlock_oof mmdCtx mmdEntry 4 [mmdCvA, mmdCvB, mmdCvC, mmdMulmod] mmdJWork mmdCvA
               [mmdCvB, mmdCvC, mmdMulmod, mmdJWork] s (mmdEntrySEnd s) rfl rfl (by decide) hnt (mmdEntry_thread s) (by decide))
      | (j+4) =>
      rw [show j+4+1 = ([mmdCvA, mmdCvB, mmdCvC, mmdMulmod] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mmdCvA, mmdCvB, mmdCvC, mmdMulmod]) (jmpInst := mmdJWork) (hd := mmdCvA)
        (tl := [mmdCvB, mmdCvC, mmdMulmod, mmdJWork])
        (nextLiveness := ["a", "b", "c", "d"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "work") (off := 12) (bb' := mmdWork) (sEnd := mmdEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := mmdEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := mmdEntry_body)
        (hsd := ⟨by intro op; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 7 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- work: the CONSUMING MUL %c %d + JMP done
      have hlbl : s.currentBb = "work" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, _, _, _, _, _, _, hwork, _⟩ := hinv
      obtain ⟨haw, hbw, hcw, hdw⟩ := hwork hlbl
      have hpc10 : asm.pc = 10 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mmdCtx mmdWork 1 [mmdMul1] mmdJDone mmdMul1 [mmdJDone] s
               (mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (mmdWork_thread s _ _ hcw hdw) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([mmdMul1] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmpTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mmdMul1]) (jmpInst := mmdJDone) (hd := mmdMul1) (tl := [mmdJDone])
        (nextLiveness := ["a", "b", "e"]) (curBbLabel := "work") (dem := 1)
        (S := ["a", "b", "c", "d"]) (Sn := ["a", "b", "e"])
        (ps0 := psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "work") (lbl := "done") (off := 18) (bb' := mmdDone)
        (sEnd := mmdWorkSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := mmdWork_thread s _ _ hcw hdw)
        (hnothalt := by simpa [updateVar] using hhalt)
        (hready := mmdWork_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "work").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c", Operand.Var "d"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, haw⟩
          · exact ⟨_, hbw⟩
          · exact ⟨_, hcw⟩
          · exact ⟨_, hdw⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc10]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps := rfl) (hpc := by rw [hpc10]; decide) (hpush := by simp only [hpc10]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc10]; decide)
        (hjump := by simp only [hpc10]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · -- done: the CONSUMING MUL %b %e + body-then-RETURN
      have hlbl : s.currentBb = "done" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hdone⟩ := hinv
      obtain ⟨ha0, hb0, he0⟩ := hdone hlbl
      have hpc14 : asm.pc = 14 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mmdCtx mmdDone 1 [mmdMul2] mmdRet mmdMul2 [mmdRet] s
               (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (mmdDone_thread s _ _ hb0 he0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([mmdMul2] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mmdMul2]) (retInst := mmdRet) (hd := mmdMul2) (tl := [mmdRet])
        (nextLiveness := ["f", "a"]) (curBbLabel := "done") (dem := 1)
        (S := ["a", "b", "e"]) (Sn := ["a", "f"])
        (ps0 := psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "done") (offv := "f") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := mmdDone_thread s _ _ hb0 he0)
        (hevaloff := by rw [show evalOperand (Operand.Var "f")
              (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "f" (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (mmdDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (mmdDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "f")
            = lookupVar "f" (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (mmdDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (mmdDoneSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (mmdDoneSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := mmdDone_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "done").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "e"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, he0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj' : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj' : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc14]; decide) (hret := by simp only [hpc14]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨mmdEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel mmdFn) mmdFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan mmdFn 0 0).get!.1)).1.length
      omega

end Example

end EvmYul.Venom.Hol.Codegen

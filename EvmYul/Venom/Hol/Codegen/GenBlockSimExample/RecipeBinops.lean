/-
GenBlockSimExample / ALU binop capstones (DIV..BYTE) + ISZERO + SLOAD

Split from RecipeFinal for readability; layout only, meaning unchanged. Wrapped in
`namespace …Codegen.Example` and imports the previous part (the read capstone chain).
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeReads

namespace EvmYul.Venom.Hol.Codegen

namespace Example

-- non-commutative binop family (DIV/MOD/SDIV/…): 2-input load, RegularStep nonCommBinop arm.
-- Reuses r0's next block. c = f(callvalue,callvalue), killed by MUL-by-0.
def ncbLoad (op : Opcode) : Instruction := { id := 2, opcode := op, operands := [Operand.Var "a", Operand.Var "b"], outputs := ["c"] }
def ncbEntry (op : Opcode) : BasicBlock := { label := "entry", instructions := [r0CvA, r0CvB, ncbLoad op, r0Jmp] }
def ncbFn (op : Opcode) : IrFunction := { name := "main", blocks := [ncbEntry op, r0Next] }
def ncbCtx (op : Opcode) : VenomContext := { functions := [ncbFn op], entry := some "main" }

abbrev ncbEntrySEnd (f : bytes32 → bytes32 → bytes32) (s : VenomState) : VenomState :=
  { updateVar "c" (f s.callCtx.callvalue s.callCtx.callvalue) { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem ncbEntry_thread (op : Opcode) (f : bytes32 → bytes32 → bytes32)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (s : VenomState) :
    execBodyThread [r0CvA, r0CvB, ncbLoad op] 0 { s with instIdx := 0 } = some (ncbEntrySEnd f s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hla : lookupVar "a" S2 = some s.callCtx.callvalue := by
    rw [hS2]; show lookupVar "a" (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 })) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have hlb : lookupVar "b" S2 = some s.callCtx.callvalue := by rw [hS2]; exact lookupVar_updateVar_self _ _ _
  have hsub : stepInstBase (ncbLoad op) S2 = ExecResult.OK (updateVar "c" (f s.callCtx.callvalue s.callCtx.callvalue) S2) :=
    stepInstBase_binopVar (hsem S2) rfl rfl hla hlb
  have h1 : stepInstBase r0CvA { s with instIdx := 0 } = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase r0CvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [r0CvB, ncbLoad op] 1 { s' with instIdx := 1 } | _ => none) = some (ncbEntrySEnd f s)
  rw [h1]
  show (match stepInstBase r0CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [ncbLoad op] 2 { s' with instIdx := 2 } | _ => none) = some (ncbEntrySEnd f s)
  rw [h2]
  show (match stepInstBase (ncbLoad op) S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none) = some (ncbEntrySEnd f s)
  rw [hsub]; rfl

theorem ncbEntry_body (op : Opcode) (nm : String) (f : bytes32 → bytes32 → bytes32)
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP) (hncomm : isCommutative op = false)
    (hcompute : computeOperands (ncbLoad op) = (ncbLoad op).operands.reverse)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmBinop f s) :
    RegularBodyH lo ["a", "b", "c"] offsetToPc prog 1 [r0CvA, r0CvB, ncbLoad op] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, Nat.le_refl 1⟩
  exact ⟨"c", nm, rfl, hname, by decide, by decide,
    Or.inr (Or.inl ⟨"a", "b", f, hncomm, hnjmp, hcompute, hsem, rfl, by decide, by decide, by decide, by decide, by decide,
      (fun s h hg => hasm offsetToPc prog s h hg)⟩)⟩
theorem ncbEntry_runBlock (op : Opcode) (f : bytes32 → bytes32 → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) (ncbCtx op) (ncbEntry op) s = ExecResult.OK (jumpTo "next" (ncbEntrySEnd f s)) :=
  runBlock_body_jmp (ncbCtx op) (ncbEntry op) j [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA [r0CvB, ncbLoad op, r0Jmp] s
    (ncbEntrySEnd f s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm)
    (ncbEntry_thread op f hsem s) (by simpa [updateVar] using hnh)

theorem ncbEntrySEnd_lookup (f : bytes32 → bytes32 → bytes32) (s : VenomState) :
    lookupVar "a" (ncbEntrySEnd f s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (ncbEntrySEnd f s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (ncbEntrySEnd f s) = some (f s.callCtx.callvalue s.callCtx.callvalue) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" _ (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

theorem ncbNext_halts (op : Opcode) (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) (ncbCtx op) r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return (ncbCtx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem ncbNext_error_a (op : Opcode) (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) (ncbCtx op) r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term (ncbCtx op) r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

def ncbInv (f : bytes32 → bytes32 → bytes32) (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (f s.callCtx.callvalue s.callCtx.callvalue))

theorem ncbInv_pres (op : Opcode) (f : bytes32 → bytes32 → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v) :
    ∀ bb ∈ (ncbFn op).blocks, ∀ (s s' : VenomState) (f' : Nat),
      ncbInv f s → runBlock f' (ncbCtx op) bb s = ExecResult.OK s' → ncbInv f s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [r0CvA, r0CvB, ncbLoad op], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · decide
      · decide
      · exact hnterm
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) (ncbEntry op) 0 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
             [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) (ncbEntry op) 1 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
             [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) (ncbEntry op) 2 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
             [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) (ncbEntry op) 3 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
             [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega] at hrun
      rw [ncbEntry_runBlock op f hnterm hsem s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := ncbEntrySEnd_lookup f s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (ncbEntrySEnd f s)) = lookupVar "c" (ncbEntrySEnd f s) from rfl, hc0]
      rfl
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 (ncbCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error (ncbCtx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 (ncbCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error (ncbCtx op) r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (ncbCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, ncbNext_error_a op s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 (ncbCtx op) r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof (ncbCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, ncbNext_halts op s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem ncbFn_halts (op : Opcode) (f : bytes32 → bytes32 → bytes32)
    (hnterm : isTerminator op = false)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (vs : VenomState) (hnh : vs.halted = false) (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 (ncbCtx op) vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 (ncbCtx op) vs
      = runBlocks 10 (ncbCtx op) (ncbFn op) { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, ncbCtx, ncbFn, lookupFunction, fnEntryLabel, ncbEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (ncbEntrySEnd f s0) with hs1
  have hentry : runBlock 9 (ncbCtx op) (ncbEntry op) s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact ncbEntry_runBlock op f hnterm hsem s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb (ncbFn op).blocks = some (ncbEntry op) := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 (ncbCtx op) (ncbFn op) s0 = runBlocks 9 (ncbCtx op) (ncbFn op) s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := ncbEntrySEnd_lookup f s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (f s0.callCtx.callvalue s0.callCtx.callvalue) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (ncbEntrySEnd f s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb (ncbFn op).blocks = some r0Next := rfl
  have hhalt := ncbNext_halts op s1 6 (EvmYul.UInt256.ofNat 0) (f s0.callCtx.callvalue s0.callCtx.callvalue) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩
abbrev NCBUNRES (nm : String) : List AsmInst :=
  [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP1",
   AsmInst.AsmOp "DUP3", AsmInst.AsmOp nm, AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next",
   AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"]

theorem ncbNext_ready (op : Opcode) (nm : String) {lo : AssocList String Nat}
    (ops : List StackOp) (hexec : executePlan ops = NCBUNRES nm) :
    BodyStepsReadyHTo lo (asmResolve (executePlan ops)).2
      (asmResolve (executePlan ops)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg (ncbFn op) z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] := by
  rw [hexec]
  exact bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := ncbFn op) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))
theorem codegen_correct_ncb (op : Opcode) (nm : String) (f : bytes32 → bytes32 → bytes32)
    {lo : AssocList String Nat}
    (hname : opcodeToEvmName op = some nm) (hnjmp : op ≠ Opcode.JMP) (hnterm : isTerminator op = false)
    (hncomm : isCommutative op = false)
    (hcompute : computeOperands (ncbLoad op) = (ncbLoad op).operands.reverse)
    (hrdy : codegenReadyInst (ncbLoad op))
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmBinop f s)
    (ops : List StackOp) (psFinal : PlanState)
    (hplan : generateFnPlan (ncbFn op) 0 0 = some (ops, psFinal))
    (hexec : executePlan ops = NCBUNRES nm)
    (hbodyE : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, ncbLoad op] (initPlanState 0)).1
      = [AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp nm])
    (hbodyN : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")).1
      = [AsmInst.AsmOp "MUL"])
    (hpsN : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, ncbLoad op] (initPlanState 0)).2
      = psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")
    (hpsStack : (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next").stack
      = [Operand.Var "a", Operand.Var "b", Operand.Var "c"])
    (hpsSpill : ∀ op', alookup' (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next").spilled op' = none)
    (hpsVars : StackIsVars ["a", "b", "c"] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next"))
    (hpsNstack : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")).2.stack
      = [Operand.Var "a", Operand.Var "e"])
    {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx op) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hprog : asmResolve (executePlan ops) = asmResolve (NCBUNRES nm) := by rw [hexec]
  have hoffs : (computeLabelOffsets (executePlan ops)).2 = (computeLabelOffsets (NCBUNRES nm)).2 := by rw [hexec]
  have hlen11 : (asmResolve (NCBUNRES nm)).1.length = 11 := rfl
  have hpcN : pcOfLabel (asmResolve (NCBUNRES nm)).1 "next" = 8 := rfl
  have hpcE0 : pcOfLabel (asmResolve (NCBUNRES nm)).1 "entry" = 0 := rfl
  have hlabE : (executePlan [StackOp.SOLabel (ncbEntry op).label]).length = 1 := rfl
  have hlabN : (executePlan [StackOp.SOLabel r0Next.label]).length = 1 := rfl
  have hfnready : ∀ bb ∈ (ncbFn op).blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [ncbEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl
      · unfold codegenReadyInst; decide
      · unfold codegenReadyInst; decide
      · exact hrdy
      · unfold codegenReadyInst; decide
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hpsE : psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv (ncbInv f)
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    (offsets := (computeLabelOffsets (executePlan ops)).2)
    (fuel := 10) (ctx := ncbCtx op) (fn := ncbFn op) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := ops) (psFinal := psFinal)
    hplan rfl rfl rfl ?_ ?_ (ncbInv_pres op f hnterm hsem) ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, ncbEntry, r0CvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hplan
      have hnt : ∀ inst ∈ [r0CvA, r0CvB, ncbLoad op], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm
      match k with
      | 0 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 1 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 1 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 2 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 2 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 3 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | (j+3) =>
      rw [show j+3+1 = ([r0CvA, r0CvB, ncbLoad op] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0CvA, r0CvB, ncbLoad op]) (jmpInst := r0Jmp) (hd := r0CvA) (tl := [r0CvB, ncbLoad op, r0Jmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := r0Next) (sEnd := ncbEntrySEnd f s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := ncbEntry_thread op f hsem s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := ncbEntry_body op nm f hname hnjmp hncomm hcompute hsem hasm)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0, hprog]
                       refine ⟨by simp only [hlabE, hlen11]; omega, fun j hj => ?_⟩
                       simp only [hlabE] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc0, hprog, hbodyE]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen11]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j <;> rfl)
        (hps := hpsN)
        (hpc := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hpush := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hoff_lk := by rw [hoffs]; rfl)
        (hoff := by decide)
        (hpc2 := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hjump := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hidx_lk := by rw [hprog]; rfl) (hlk' := rfl)
        (hw := by rw [hprog, hbodyE]; simp only [ncbEntry, List.length_cons, List.length_nil, hlen11, hpcN, hpcE0]; omega))
    · have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm, hprog]; rfl
      match k with
      | 0 => exact Or.inl (runBlock_oof (ncbCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).2]; exact ha0)
        (hready := ncbNext_ready op nm ops hexec)
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
        (hbLabel := by rw [hpc8, hprog]
                       refine ⟨by simp only [hlabN, hlen11]; omega, fun j hj => ?_⟩
                       simp only [hlabN] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc8, hprog, hbodyN]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen11]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j; rfl)
        (hps'stack := by rw [List.nil_append, hpsNstack])
        (hpc := by rw [hpc8, hprog, hbodyN]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hret := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                    simp only [hexec, hpc8, hbodyN, List.length_cons, List.length_nil]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat])
        (hw := by rw [hprog, hbodyN]; simp only [r0Next, List.length_cons, List.length_nil, hlen11, hpcN]; omega))
  case _ =>
    refine ⟨⟨ncbEntry op, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan ops)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hplan).symm
    · show (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 "entry" ≤ (asmResolve (executePlan ops)).1.length
      omega

/-! ### ✅ The non-commutative BINOP family via the generic `codegen_correct_ncb` driver

DIV/MOD/SDIV/SMOD/LT/GT/SLT/SGT/SHL/SHR/SAR/EXP/SIGNEXTEND/BYTE — one driver, parametrized by the
opcode `op`, its EVM name, and the binop function `f : bytes32 → bytes32 → bytes32`. Same recipe as
the read drivers but a 2-input load (`DUP1 DUP3 op`, 11-inst program, `next`@8) and the `RegularStep`
nonCommBinop arm (`asmBinop f`). Reuses r0's `next` block. Each op is a ~10-line instantiation. -/

theorem codegen_correct_dvvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.Div) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Div) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.Div "DIV" EvmYul.Venom.Hol.safeDiv
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_div_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_mdvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.Mod) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Mod) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.Mod "MOD" EvmYul.Venom.Hol.safeMod
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_mod_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_sdvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SDIV) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SDIV) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SDIV "SDIV" EvmYul.Venom.Hol.safeSdiv
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_sdiv_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_smvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SMOD) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SMOD) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SMOD "SMOD" EvmYul.Venom.Hol.safeSmod
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_smod_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_ltvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.LT) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.LT) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.LT "LT" (fun x y => EvmYul.Venom.Hol.boolToWord (x < y))
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_lt_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_gtvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.GT) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.GT) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.GT "GT" (fun x y => EvmYul.Venom.Hol.boolToWord (x > y))
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_gt_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_slvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SLT) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SLT) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SLT "SLT" EvmYul.UInt256.slt
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_slt_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_sgvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SGT) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SGT) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SGT "SGT" EvmYul.UInt256.sgt
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_sgt_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_shvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SHL) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHL) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SHL "SHL" (fun n w => w <<< n)
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_shl_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_srvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SHR) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SHR) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SHR "SHR" (fun n w => w >>> n)
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_shr_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_savFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SAR) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SAR) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SAR "SAR" EvmYul.UInt256.sar
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_sar_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_exvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.Exp) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.Exp) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.Exp "EXP" EvmYul.UInt256.exp
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_exp_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

/-! ### ✅ A UNOP via the recipe route (ISZERO) — `codegen_correct_iszFn_recipeW`

The first `codegen_correct` for a UNOP (`ISZERO`), a distinct instruction class:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = ISZERO %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                             -- MUL consumes the TOP two (b,c)
```

`ISZERO %a` is the growing unop arm (`RegularStep`'s 3rd disjunct, `asmStep_iszero_ok`), emitted `DUP2 ; ISZERO`,
leaving `[a, b, c]` with `c = ISZERO 0` (NON-zero — so `c` cannot itself be a RETURN operand). In `next` the
consuming `MUL %b %c` eats the top two (`b, c`); since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`,
regardless of `c`), emptying the return window. `a` (bottom) is never buried — no f1a reorder. `entry` via
`hsupplyW_regularJmp`, `next` via `hsupplyW_regularReturnTo` fed the consuming `MUL` (`iszNext_ready`). -/

def iszCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def iszCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def iszNot : Instruction :=
  { id := 2, opcode := Opcode.ISZERO, operands := [Operand.Var "a"], outputs := ["c"] }
def iszJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def iszMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def iszRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def iszEntry : BasicBlock := { label := "entry", instructions := [iszCvA, iszCvB, iszNot, iszJmp] }
def iszNext : BasicBlock := { label := "next", instructions := [iszMul, iszRet] }
def iszFn : IrFunction := { name := "main", blocks := [iszEntry, iszNext] }
def iszCtx : VenomContext := { functions := [iszFn], entry := some "main" }

theorem isz_unresolved_asm : executePlan (generateFnPlan iszFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "ISZERO", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- entry's body `[CV a; CV b; ISZERO %a]` as a `RegularBodyH`: two `cv_step`s then the growing unop `ISZERO`
    via `RegularStep`'s unop arm (`asmStep_iszero_ok`), all outputs live. -/
theorem iszEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 1 [iszCvA, iszCvB, iszNot] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, by decide⟩
  exact ⟨"c", "ISZERO", rfl, rfl, by decide, by decide,
    Or.inr (Or.inr (Or.inl ⟨"a", EvmYul.UInt256.isZero, by decide, rfl, fun _ => rfl, rfl,
      by decide, by decide, fun _ h hg => asmStep_iszero_ok h hg⟩))⟩

/-- Body-end state of `iszEntry`: `a,b := callvalue`, `c := a - b` (= 0 when callvalue = 0). -/
abbrev iszEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (EvmYul.UInt256.isZero s.callCtx.callvalue)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem iszEntry_thread (s : VenomState) :
    execBodyThread [iszCvA, iszCvB, iszNot] 0 { s with instIdx := 0 } = some (iszEntrySEnd s) := by
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
  have hsub := stepInstBase_unopVar (inst := iszNot) (f := EvmYul.UInt256.isZero) (x := "a")
    (out := "c") (w := s.callCtx.callvalue) rfl rfl rfl hla
  have h1 : stepInstBase iszCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase iszCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase iszCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [iszCvB, iszNot] 1 { s' with instIdx := 1 }
        | _ => none) = some (iszEntrySEnd s)
  rw [h1]
  show (match stepInstBase iszCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [iszNot] 2 { s' with instIdx := 2 }
        | _ => none) = some (iszEntrySEnd s)
  rw [h2]
  show (match stepInstBase iszNot ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (iszEntrySEnd s)
  rw [hsub]
  rfl

/-- `iszEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem iszEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) iszCtx iszEntry s = ExecResult.OK (jumpTo "next" (iszEntrySEnd s)) :=
  runBlock_body_jmp iszCtx iszEntry j [iszCvA, iszCvB, iszNot] iszJmp iszCvA [iszCvB, iszNot, iszJmp] s
    (iszEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (iszEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem iszNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg iszFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([iszMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := iszFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev iszNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem iszNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (iszNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (iszNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem iszNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [iszMul] 0 { s with instIdx := 0 } = some (iszNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase iszMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := iszMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase iszMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem iszMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase iszMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [iszMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem iszMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase iszMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [iszMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem iszNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) iszCtx iszNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (iszNextSEnd s wb wc))
        (iszNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := iszNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return iszCtx iszNext j [iszMul] iszRet iszMul [iszRet] s (iszNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (iszNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem iszNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) iszCtx iszNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := iszNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term iszCtx iszNext j [iszMul] iszRet iszMul [iszRet] s (iszNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (iszNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : iszNext.instructions = [iszMul] ++ [iszRet])
    (iszNext_thread s wb wc hb hc), iszRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `iszEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem iszEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (iszEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (iszEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (iszEntrySEnd s) = some (EvmYul.UInt256.isZero s.callCtx.callvalue) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (EvmYul.UInt256.isZero s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (EvmYul.UInt256.isZero s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (EvmYul.UInt256.isZero s.callCtx.callvalue)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def iszInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0)))

theorem iszInv_pres : ∀ bb ∈ iszFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    iszInv s → runBlock f' iszCtx bb s = ExecResult.OK s' → iszInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [iszFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (iszEntrySEnd s)`
    have hnt : ∀ inst ∈ [iszCvA, iszCvB, iszNot], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszEntry 0 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
             [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszEntry 1 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
             [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszEntry 2 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
             [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszEntry 3 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
             [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, iszEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := iszEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hc0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (iszEntrySEnd s)) = lookupVar "c" (iszEntrySEnd s) from rfl, hc0]
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 iszCtx iszNext s iszMul [iszRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error iszCtx iszNext iszMul [iszRet] s "undefined operand" j rfl
          (by decide) (iszMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 iszCtx iszNext s iszMul [iszRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error iszCtx iszNext iszMul [iszRet] s "undefined operand" j rfl
            (by decide) (iszMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 iszCtx iszNext s iszMul [iszRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszNext 1 [iszMul] iszRet iszMul [iszRet] s
                   (iszNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (iszNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, iszNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 iszCtx iszNext s iszMul [iszRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof iszCtx iszNext 1 [iszMul] iszRet iszMul [iszRet] s
                   (iszNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (iszNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, iszNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 iszCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem iszFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 iszCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 iszCtx vs
      = runBlocks 10 iszCtx iszFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, iszCtx, iszFn, lookupFunction, fnEntryLabel, iszEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (iszEntrySEnd s0) with hs1
  have hentry : runBlock 9 iszCtx iszEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact iszEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb iszFn.blocks = some iszEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 iszCtx iszFn s0 = runBlocks 9 iszCtx iszFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := iszEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hc1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0)) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (iszEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb iszFn.blocks = some iszNext := rfl
  have hhalt := iszNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **The first UNOP capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=ADD %a %b ; JMP next` /
    `next: %e=ADD %b %c ; RETURN %e, %a`. `entry`'s ADD exercises the pure commutative var/var GROWING arm (`bodyStep_commBinop`); it is
    duplicating (`DUP1 ; DUP3 ; ADD`). `next`'s ADD consumes the top two `[b, c]`
    (so `a` is never buried — no f1a reorder), and `next` ends in a body-then-RETURN handled by the new
    `hsupplyW_regularReturnTo`. `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_iszFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 iszCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ iszFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [iszFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [iszEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [iszNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan iszFn 0 0
      = some ((generateFnPlan iszFn 0 0).get!.1, (generateFnPlan iszFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel iszFn) iszFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv iszInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel iszFn) iszFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan iszFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := iszCtx) (fn := iszFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan iszFn 0 0).get!.1) (psFinal := (generateFnPlan iszFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ iszInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [iszFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, iszEntry, iszCvA]
    · simp [runBlock, evalPhis, execBlock, iszNext, iszMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [iszFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [iszCvA, iszCvB, iszNot], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof iszCtx iszEntry 1 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
               [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof iszCtx iszEntry 2 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
               [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof iszCtx iszEntry 3 [iszCvA, iszCvB, iszNot] iszJmp iszCvA
               [iszCvB, iszNot, iszJmp] s (iszEntrySEnd s) rfl rfl (by decide) hnt (iszEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([iszCvA, iszCvB, iszNot] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [iszCvA, iszCvB, iszNot]) (jmpInst := iszJmp) (hd := iszCvA) (tl := [iszCvB, iszNot, iszJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := iszNext) (sEnd := iszEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := iszEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := iszEntry_body)
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
      | 0 => exact Or.inl (runBlock_oof iszCtx iszNext 1 [iszMul] iszRet iszMul [iszRet] s
               (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (iszNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([iszMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [iszMul]) (retInst := iszRet) (hd := iszMul) (tl := [iszRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel iszFn) iszFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0)))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := iszNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0)))
            = lookupVar "e" (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) from rfl,
            (iszNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0)))
            = lookupVar "a" (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) from rfl,
            (iszNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))).2]; exact ha0)
        (hvoff := by rw [show operandVal (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) lo
              (Operand.Var "e")
            = lookupVar "e" (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) from rfl,
            (iszNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) lo
              (Operand.Var "a")
            = lookupVar "a" (iszNextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))) from rfl,
            (iszNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0))).2]; exact ha0)
        (hready := iszNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel iszFn) iszFn 0 0 "next").stack
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
    refine ⟨⟨iszEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel iszFn) iszFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan iszFn 0 0).get!.1)).1.length
      omega

theorem cbEntry_body (op : Opcode) (nm : String) (f : bytes32 → bytes32 → bytes32)
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    (hname : opcodeToEvmName op = some nm) (hcomm : isCommutative op = true)
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmBinop f s) :
    RegularBodyH lo ["a", "b", "c"] offsetToPc prog 1 [r0CvA, r0CvB, ncbLoad op] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨Or.inl ?_, Nat.le_refl 1⟩
  exact ⟨"c", nm, rfl, hname, by decide, by decide,
    Or.inl ⟨"a", "b", f, hcomm, hsem, rfl, by decide, by decide, by decide, by decide, by decide,
      (fun s h hg => hasm offsetToPc prog s h hg)⟩⟩

theorem codegen_correct_cb (op : Opcode) (nm : String) (f : bytes32 → bytes32 → bytes32)
    {lo : AssocList String Nat}
    (hname : opcodeToEvmName op = some nm) (hnterm : isTerminator op = false)
    (hcomm : isCommutative op = true)
    (hrdy : codegenReadyInst (ncbLoad op))
    (hsem : ∀ v : VenomState, stepInstBase (ncbLoad op) v = execPure2 f (ncbLoad op) v)
    (hasm : ∀ (o2pc : AssocList Nat Nat) (prg : List AsmInst) (s : AsmState) (h : s.pc < prg.length),
        prg.get ⟨s.pc, h⟩ = AsmInst.AsmOp nm → asmStep o2pc prg s = asmBinop f s)
    (ops : List StackOp) (psFinal : PlanState)
    (hplan : generateFnPlan (ncbFn op) 0 0 = some (ops, psFinal))
    (hexec : executePlan ops = NCBUNRES nm)
    (hbodyE : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, ncbLoad op] (initPlanState 0)).1
      = [AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "DUP1", AsmInst.AsmOp "DUP3", AsmInst.AsmOp nm])
    (hbodyN : executePlan (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")).1
      = [AsmInst.AsmOp "MUL"])
    (hpsN : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["a", "b", "c"] "entry" [r0CvA, r0CvB, ncbLoad op] (initPlanState 0)).2
      = psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")
    (hpsStack : (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next").stack
      = [Operand.Var "a", Operand.Var "b", Operand.Var "c"])
    (hpsSpill : ∀ op', alookup' (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next").spilled op' = none)
    (hpsVars : StackIsVars ["a", "b", "c"] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next"))
    (hpsNstack : (bodyPlanRIP exLiveness DfgAnalysis.empty exCfg (ncbFn op) ["e", "a"] "next" [r0Mul] (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next")).2.stack
      = [Operand.Var "a", Operand.Var "e"])
    {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx op) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hprog : asmResolve (executePlan ops) = asmResolve (NCBUNRES nm) := by rw [hexec]
  have hoffs : (computeLabelOffsets (executePlan ops)).2 = (computeLabelOffsets (NCBUNRES nm)).2 := by rw [hexec]
  have hlen11 : (asmResolve (NCBUNRES nm)).1.length = 11 := rfl
  have hpcN : pcOfLabel (asmResolve (NCBUNRES nm)).1 "next" = 8 := rfl
  have hpcE0 : pcOfLabel (asmResolve (NCBUNRES nm)).1 "entry" = 0 := rfl
  have hlabE : (executePlan [StackOp.SOLabel (ncbEntry op).label]).length = 1 := rfl
  have hlabN : (executePlan [StackOp.SOLabel r0Next.label]).length = 1 := rfl
  have hfnready : ∀ bb ∈ (ncbFn op).blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [ncbEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl
      · unfold codegenReadyInst; decide
      · unfold codegenReadyInst; decide
      · exact hrdy
      · unfold codegenReadyInst; decide
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hpsE : psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv (ncbInv f)
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan ops)).1)
    (psOf := psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0)
    (wOf := fun l => (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 l)
    (offsets := (computeLabelOffsets (executePlan ops)).2)
    (fuel := 10) (ctx := ncbCtx op) (fn := ncbFn op) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry") (ops := ops) (psFinal := psFinal)
    hplan rfl rfl rfl ?_ ?_ (ncbInv_pres op f hnterm hsem) ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, ncbEntry, r0CvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [ncbFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hplan
      have hnt : ∀ inst ∈ [r0CvA, r0CvB, ncbLoad op], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · decide
        · decide
        · exact hnterm
      match k with
      | 0 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 1 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 1 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 2 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | 2 => exact Or.inl (runBlock_oof (ncbCtx op) (ncbEntry op) 3 [r0CvA, r0CvB, ncbLoad op] r0Jmp r0CvA
               [r0CvB, ncbLoad op, r0Jmp] s (ncbEntrySEnd f s) rfl rfl (by decide) hnt (ncbEntry_thread op f hsem s) (by simp only [List.length_cons, List.length_nil]; omega))
      | (j+3) =>
      rw [show j+3+1 = ([r0CvA, r0CvB, ncbLoad op] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [r0CvA, r0CvB, ncbLoad op]) (jmpInst := r0Jmp) (hd := r0CvA) (tl := [r0CvB, ncbLoad op, r0Jmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 10) (bb' := r0Next) (sEnd := ncbEntrySEnd f s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := ncbEntry_thread op f hsem s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := cbEntry_body op nm f hname hcomm hsem hasm)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0, hprog]
                       refine ⟨by simp only [hlabE, hlen11]; omega, fun j hj => ?_⟩
                       simp only [hlabE] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc0, hprog, hbodyE]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen11]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j <;> rfl)
        (hps := hpsN)
        (hpc := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hpush := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hoff_lk := by rw [hoffs]; rfl)
        (hoff := by decide)
        (hpc2 := by rw [hpc0, hprog, hbodyE]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hjump := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                     simp only [hexec, hpc0, hbodyE, List.length_cons, List.length_nil]; rfl)
        (hidx_lk := by rw [hprog]; rfl) (hlk' := rfl)
        (hw := by rw [hprog, hbodyE]; simp only [ncbEntry, List.length_cons, List.length_nil, hlen11, hpcN, hpcE0]; omega))
    · have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc8 : asm.pc = 8 := by rw [hpc_asm, hprog]; rfl
      match k with
      | 0 => exact Or.inl (runBlock_oof (ncbCtx op) r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (f s.callCtx.callvalue s.callCtx.callvalue)).2]; exact ha0)
        (hready := ncbNext_ready op nm ops hexec)
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
        (hbLabel := by rw [hpc8, hprog]
                       refine ⟨by simp only [hlabN, hlen11]; omega, fun j hj => ?_⟩
                       simp only [hlabN] at hj; interval_cases j; rfl)
        (hblock := by rw [hpc8, hprog, hbodyN]
                      refine ⟨by simp only [List.length_cons, List.length_nil, hlen11]; omega, fun j hj => ?_⟩
                      simp only [List.length_cons, List.length_nil] at hj; interval_cases j; rfl)
        (hps'stack := by rw [List.nil_append, hpsNstack])
        (hpc := by rw [hpc8, hprog, hbodyN]; simp only [List.length_cons, List.length_nil, hlen11]; omega)
        (hret := by rw [List.get_eq_getElem, List.getElem_eq_iff]
                    simp only [hexec, hpc8, hbodyN, List.length_cons, List.length_nil]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat])
        (hw := by rw [hprog, hbodyN]; simp only [r0Next, List.length_cons, List.length_nil, hlen11, hpcN]; omega))
  case _ =>
    refine ⟨⟨ncbEntry op, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel (ncbFn op)) (ncbFn op) 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan ops)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hplan).symm
    · show (asmResolve (executePlan ops)).1.length - pcOfLabel (asmResolve (executePlan ops)).1 "entry" ≤ (asmResolve (executePlan ops)).1.length
      omega

/-! ### ✅ The commutative BINOP family via the generic `codegen_correct_cb` driver

MUL/AND/OR/XOR/EQ — same program as the non-comm binops (`DUP1 DUP3 op`), the `RegularStep`
commBinop arm (`isCommutative = true`). Reuses ALL of the `ncb` infrastructure (load, thread,
invariant, driver skeleton) — only the arm (`cbEntry_body`) and `isCommutative` fact differ. -/

theorem codegen_correct_mlvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.MUL) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.MUL) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_cb Opcode.MUL "MUL" (fun a b => a * b)
    rfl (by decide) (by decide) (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_mul_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_anvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.AND) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.AND) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_cb Opcode.AND "AND" (fun a b => a &&& b)
    rfl (by decide) (by decide) (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_and_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_orvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.OR) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.OR) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_cb Opcode.OR "OR" (fun a b => a ||| b)
    rfl (by decide) (by decide) (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_or_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_xrvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.XOR) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.XOR) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_cb Opcode.XOR "XOR" (fun a b => a ^^^ b)
    rfl (by decide) (by decide) (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_xor_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

theorem codegen_correct_eqvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.EQ) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.EQ) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_cb Opcode.EQ "EQ" (fun x y => EvmYul.Venom.Hol.boolToWord (x = y))
    rfl (by decide) (by decide) (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_eq_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

/-! ### ✅ A BINOP (SIGNEXTEND) via the generic `codegen_correct_ncb` driver -/

theorem codegen_correct_sxvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.SIGNEXTEND) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.SIGNEXTEND) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.SIGNEXTEND "SIGNEXTEND" EvmYul.Venom.Hol.signExtend
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_signextend_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

/-! ### ✅ A BINOP (BYTE) via the generic `codegen_correct_ncb` driver -/

theorem codegen_correct_byvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 (ncbCtx Opcode.BYTE) vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan (ncbFn Opcode.BYTE) 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct_ncb Opcode.BYTE "BYTE" EvmYul.Venom.Hol.evmByte
    rfl (by decide) (by decide) (by decide) rfl (by unfold codegenReadyInst; decide) (fun _ => rfl)
    (fun _o2pc _prg _s h hg => asmStep_byte_ok h hg)
    _ _ rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl
    hvshalt hzero hrel haspc

/-! ### ✅ An SLOAD (storage read) via the recipe route — `codegen_correct_sloFn_recipeW`

The persistent-storage read `SLOAD` (the newly-wired 11th `RegularStepG` arm, `asmStep_sload_ok` /
`bodyStep_sload`), twin of `TLOAD`:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = SLOAD %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                               -- MUL consumes the TOP two (b,c)
```

`SLOAD %a` is a 1-input read (`RegularStepG`'s SLOAD arm, emitted `DUP2 ; SLOAD`), leaving `[a, b, c]`
with `c = sloVal s` (the storage word at key `callvalue` — context-dependent, generally NON-zero, so
`c` cannot itself be a RETURN operand). In `next` the consuming `MUL %b %c` eats the top two (`b, c`);
since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`, regardless of `c`), emptying the return window.
`a` (bottom) is never buried — no f1a reorder. `entry` via `hsupplyW_regularJmp`, `next` via
`hsupplyW_regularReturnTo` fed the consuming `MUL` (`sloNext_ready`). -/

def sloCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def sloCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def sloLoad : Instruction :=
  { id := 2, opcode := Opcode.SLOAD, operands := [Operand.Var "a"], outputs := ["c"] }
def sloJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def sloMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def sloRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def sloEntry : BasicBlock := { label := "entry", instructions := [sloCvA, sloCvB, sloLoad, sloJmp] }
def sloNext : BasicBlock := { label := "next", instructions := [sloMul, sloRet] }
def sloFn : IrFunction := { name := "main", blocks := [sloEntry, sloNext] }
def sloCtx : VenomContext := { functions := [sloFn], entry := some "main" }

theorem slo_unresolved_asm : executePlan (generateFnPlan sloFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "SLOAD", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- The persistent-storage word SLOAD reads at key `a` (= the call value); context-dependent, generally NON-zero. -/
abbrev sloVal (s : VenomState) : bytes32 := sload s.callCtx.callvalue s

/-- entry's body `[CV a; CV b; SLOAD %a]` as a `RegularBodyH`: two `cv_step`s then the
    SLOAD read via `RegularStepG`'s SLOAD arm (`asmStep_tload_ok`), output live. -/
theorem sloEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 1 [sloCvA, sloCvB, sloLoad] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, by decide⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨"a", "c", rfl, by decide, rfl, fun _ => rfl, rfl, rfl,
     by decide, by decide, by decide, by decide, fun _ h hg => asmStep_sload_ok h hg⟩))))))))))

/-- Body-end state of `sloEntry`: `a,b := callvalue`, `c := sloVal s` (the transient read at key `a`). -/
abbrev sloEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (sloVal s)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem sloEntry_thread (s : VenomState) :
    execBodyThread [sloCvA, sloCvB, sloLoad] 0 { s with instIdx := 0 } = some (sloEntrySEnd s) := by
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
  have hsub : stepInstBase sloLoad ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = ExecResult.OK (updateVar "c" (sloVal s)
        ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 })) := by
    have he : evalOperand (Operand.Var "a") ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := hla
    simp only [sloLoad, stepInstBase, execRead1, he]
    rfl
  have h1 : stepInstBase sloCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase sloCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase sloCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [sloCvB, sloLoad] 1 { s' with instIdx := 1 }
        | _ => none) = some (sloEntrySEnd s)
  rw [h1]
  show (match stepInstBase sloCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [sloLoad] 2 { s' with instIdx := 2 }
        | _ => none) = some (sloEntrySEnd s)
  rw [h2]
  show (match stepInstBase sloLoad ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (sloEntrySEnd s)
  rw [hsub]
  rfl

/-- `sloEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem sloEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) sloCtx sloEntry s = ExecResult.OK (jumpTo "next" (sloEntrySEnd s)) :=
  runBlock_body_jmp sloCtx sloEntry j [sloCvA, sloCvB, sloLoad] sloJmp sloCvA [sloCvB, sloLoad, sloJmp] s
    (sloEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (sloEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem sloNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg sloFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([sloMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := sloFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev sloNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem sloNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (sloNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (sloNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem sloNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [sloMul] 0 { s with instIdx := 0 } = some (sloNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase sloMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := sloMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase sloMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem sloMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase sloMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [sloMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem sloMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase sloMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [sloMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem sloNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) sloCtx sloNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (sloNextSEnd s wb wc))
        (sloNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := sloNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return sloCtx sloNext j [sloMul] sloRet sloMul [sloRet] s (sloNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (sloNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem sloNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) sloCtx sloNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := sloNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term sloCtx sloNext j [sloMul] sloRet sloMul [sloRet] s (sloNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (sloNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : sloNext.instructions = [sloMul] ++ [sloRet])
    (sloNext_thread s wb wc hb hc), sloRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `sloEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem sloEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (sloEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (sloEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (sloEntrySEnd s) = some (sloVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (sloVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (sloVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (sloVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def sloInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (sloVal s))

theorem sloInv_pres : ∀ bb ∈ sloFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    sloInv s → runBlock f' sloCtx bb s = ExecResult.OK s' → sloInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [sloFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (sloEntrySEnd s)`
    have hnt : ∀ inst ∈ [sloCvA, sloCvB, sloLoad], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloEntry 0 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
             [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloEntry 1 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
             [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloEntry 2 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
             [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloEntry 3 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
             [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, sloEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := sloEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (sloEntrySEnd s)) = lookupVar "c" (sloEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 sloCtx sloNext s sloMul [sloRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error sloCtx sloNext sloMul [sloRet] s "undefined operand" j rfl
          (by decide) (sloMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 sloCtx sloNext s sloMul [sloRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error sloCtx sloNext sloMul [sloRet] s "undefined operand" j rfl
            (by decide) (sloMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 sloCtx sloNext s sloMul [sloRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloNext 1 [sloMul] sloRet sloMul [sloRet] s
                   (sloNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (sloNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, sloNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 sloCtx sloNext s sloMul [sloRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof sloCtx sloNext 1 [sloMul] sloRet sloMul [sloRet] s
                   (sloNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (sloNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, sloNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 sloCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem sloFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 sloCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 sloCtx vs
      = runBlocks 10 sloCtx sloFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, sloCtx, sloFn, lookupFunction, fnEntryLabel, sloEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (sloEntrySEnd s0) with hs1
  have hentry : runBlock 9 sloCtx sloEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact sloEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb sloFn.blocks = some sloEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 sloCtx sloFn s0 = runBlocks 9 sloCtx sloFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := sloEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (sloVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (sloEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb sloFn.blocks = some sloNext := rfl
  have hhalt := sloNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (sloVal s0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **An SLOAD capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=SLOAD %a ; JMP next` /
    `next: %e=MUL %b %c ; RETURN %e, %a`. `entry`'s SLOAD exercises the 1-input transient-read arm
    (`RegularStepG`'s SLOAD disjunct, `asmStep_tload_ok`), emitted `DUP2 ; SLOAD`, leaving `c = sloVal s`
    (context-dependent). `next`'s MUL consumes the top two `[b, c]` (so `a` is never buried — no f1a
    reorder); `b = 0` ⇒ `e = 0` (`uint256_zero_mul`) empties the return window. `next` ends in a
    body-then-RETURN handled by `hsupplyW_regularReturnTo`; `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_sloFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 sloCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ sloFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [sloFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [sloEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [sloNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan sloFn 0 0
      = some ((generateFnPlan sloFn 0 0).get!.1, (generateFnPlan sloFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel sloFn) sloFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv sloInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel sloFn) sloFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan sloFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := sloCtx) (fn := sloFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan sloFn 0 0).get!.1) (psFinal := (generateFnPlan sloFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ sloInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [sloFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, sloEntry, sloCvA]
    · simp [runBlock, evalPhis, execBlock, sloNext, sloMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [sloFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [sloCvA, sloCvB, sloLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof sloCtx sloEntry 1 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
               [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof sloCtx sloEntry 2 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
               [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof sloCtx sloEntry 3 [sloCvA, sloCvB, sloLoad] sloJmp sloCvA
               [sloCvB, sloLoad, sloJmp] s (sloEntrySEnd s) rfl rfl (by decide) hnt (sloEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([sloCvA, sloCvB, sloLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [sloCvA, sloCvB, sloLoad]) (jmpInst := sloJmp) (hd := sloCvA) (tl := [sloCvB, sloLoad, sloJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := sloNext) (sEnd := sloEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := sloEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := sloEntry_body)
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
      | 0 => exact Or.inl (runBlock_oof sloCtx sloNext 1 [sloMul] sloRet sloMul [sloRet] s
               (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (sloNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([sloMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [sloMul]) (retInst := sloRet) (hd := sloMul) (tl := [sloRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel sloFn) sloFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := sloNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s))
            = lookupVar "e" (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) from rfl,
            (sloNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sloVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s))
            = lookupVar "a" (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) from rfl,
            (sloNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sloVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) from rfl,
            (sloNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sloVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (sloNextSEnd s (EvmYul.UInt256.ofNat 0) (sloVal s)) from rfl,
            (sloNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sloVal s)).2]; exact ha0)
        (hready := sloNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel sloFn) sloFn 0 0 "next").stack
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
    refine ⟨⟨sloEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel sloFn) sloFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan sloFn 0 0).get!.1)).1.length
      omega

/-! ### ✅ A BLOCKHASH (block-env read) via the recipe route — `codegen_correct_bkhFn_recipeW`

The block-environment read `BLOCKHASH` (the newly-wired 12th `RegularStepG` arm, `asmStep_blockhash_ok` /
`bodyStep_blockhash`), twin of `BLOCKHASH`/`TLOAD`:

```
entry:  %a = CALLVALUE ; %b = CALLVALUE ; %c = BLOCKHASH %a ; JMP next   -- a,b,c all live → delivered
next:   %e = MUL %b %c ; RETURN %e, %a                               -- MUL consumes the TOP two (b,c)
```

`BLOCKHASH %a` is a 1-input read (`RegularStepG`'s BLOCKHASH arm, emitted `DUP2 ; BLOCKHASH`), leaving `[a, b, c]`
with `c = bkhVal s` (the block hash at index `callvalue` — context-dependent, generally NON-zero, so
`c` cannot itself be a RETURN operand). In `next` the consuming `MUL %b %c` eats the top two (`b, c`);
since `b = 0`, `e = 0 * c = 0` (via `uint256_zero_mul`, regardless of `c`), emptying the return window.
`a` (bottom) is never buried — no f1a reorder. `entry` via `hsupplyW_regularJmp`, `next` via
`hsupplyW_regularReturnTo` fed the consuming `MUL` (`bkhNext_ready`). -/

def bkhCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def bkhCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def bkhLoad : Instruction :=
  { id := 2, opcode := Opcode.BLOCKHASH, operands := [Operand.Var "a"], outputs := ["c"] }
def bkhJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def bkhMul : Instruction :=
  { id := 4, opcode := Opcode.MUL, operands := [Operand.Var "b", Operand.Var "c"], outputs := ["e"] }
def bkhRet : Instruction :=
  { id := 5, opcode := Opcode.RETURN, operands := [Operand.Var "e", Operand.Var "a"], outputs := [] }
def bkhEntry : BasicBlock := { label := "entry", instructions := [bkhCvA, bkhCvB, bkhLoad, bkhJmp] }
def bkhNext : BasicBlock := { label := "next", instructions := [bkhMul, bkhRet] }
def bkhFn : IrFunction := { name := "main", blocks := [bkhEntry, bkhNext] }
def bkhCtx : VenomContext := { functions := [bkhFn], entry := some "main" }

theorem bkh_unresolved_asm : executePlan (generateFnPlan bkhFn 0 0).get!.1 =
    [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
     AsmInst.AsmOp "DUP2", AsmInst.AsmOp "BLOCKHASH", AsmInst.AsmPushLabel "next",
     AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := by rfl

/-- The block hash BLOCKHASH reads at index `a` (= the call value); context-dependent, generally NON-zero. -/
abbrev bkhVal (s : VenomState) : bytes32 := s.blockCtx.blockhash s.callCtx.callvalue.toNat

/-- entry's body `[CV a; CV b; BLOCKHASH %a]` as a `RegularBodyH`: two `cv_step`s then the
    BLOCKHASH read via `RegularStepG`'s BLOCKHASH arm (`asmStep_tload_ok`), output live. -/
theorem bkhEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "c"] offsetToPc
      (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 1 [bkhCvA, bkhCvB, bkhLoad] [] := by
  refine ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
          cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide), ?_, trivial⟩
  refine Or.inl ⟨?_, by decide⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨"a", "c", rfl, by decide, rfl, fun _ => rfl, rfl, rfl,
     by decide, by decide, by decide, by decide, fun _ h hg => asmStep_blockhash_ok h hg⟩))))))))))

/-- Body-end state of `bkhEntry`: `a,b := callvalue`, `c := bkhVal s` (the block-hash read at index `a`). -/
abbrev bkhEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (bkhVal s)
      { updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 }
    with instIdx := 3 }

theorem bkhEntry_thread (s : VenomState) :
    execBodyThread [bkhCvA, bkhCvB, bkhLoad] 0 { s with instIdx := 0 } = some (bkhEntrySEnd s) := by
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
  have hsub : stepInstBase bkhLoad ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = ExecResult.OK (updateVar "c" (bkhVal s)
        ({ updateVar "b" s.callCtx.callvalue
          { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
        with instIdx := 2 })) := by
    have he : evalOperand (Operand.Var "a") ({ updateVar "b" s.callCtx.callvalue
        { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
      with instIdx := 2 } : VenomState) = some s.callCtx.callvalue := hla
    simp only [bkhLoad, stepInstBase, execRead1, he]
    rfl
  have h1 : stepInstBase bkhCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase bkhCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
        with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue
          ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase bkhCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [bkhCvB, bkhLoad] 1 { s' with instIdx := 1 }
        | _ => none) = some (bkhEntrySEnd s)
  rw [h1]
  show (match stepInstBase bkhCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }
          with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [bkhLoad] 2 { s' with instIdx := 2 }
        | _ => none) = some (bkhEntrySEnd s)
  rw [h2]
  show (match stepInstBase bkhLoad ({ updateVar "b" s.callCtx.callvalue
            { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }
          with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 }
        | _ => none) = some (bkhEntrySEnd s)
  rw [hsub]
  rfl

/-- `bkhEntry`'s OK result is `jumpTo "next"` of the body-end state (fuel ≥ 4). -/
theorem bkhEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) bkhCtx bkhEntry s = ExecResult.OK (jumpTo "next" (bkhEntrySEnd s)) :=
  runBlock_body_jmp bkhCtx bkhEntry j [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA [bkhCvB, bkhLoad, bkhJmp] s
    (bkhEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (bkhEntry_thread s) (by simpa [updateVar] using hnh)

/-- `next`'s consuming `MUL %b %c` (mirror order, `bytes32_mul_comm`) as a `BodyStepsReadyHTo`:
    it eats the top two `[b, c]` off the entry stack `[a, b, c]`, leaving `[a, e]`. -/
theorem bkhNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg bkhFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([bkhMul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := bkhFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

abbrev bkhNextSEnd (s : VenomState) (wb wc : bytes32) : VenomState :=
  { updateVar "e" (wb * wc) { s with instIdx := 0 } with instIdx := 1 }

theorem bkhNextSEnd_lookup (s : VenomState) (wb wc : bytes32) :
    lookupVar "e" (bkhNextSEnd s wb wc) = some (wb * wc)
    ∧ lookupVar "a" (bkhNextSEnd s wb wc) = lookupVar "a" s := by
  refine ⟨lookupVar_updateVar_self _ _ _, ?_⟩
  show lookupVar "a" (updateVar "e" (wb * wc) { s with instIdx := 0 }) = _
  rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]; rfl

theorem bkhNext_thread (s : VenomState) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) :
    execBodyThread [bkhMul] 0 { s with instIdx := 0 } = some (bkhNextSEnd s wb wc) := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = some wc := hc
  have hstep : stepInstBase bkhMul { s with instIdx := 0 }
      = ExecResult.OK (updateVar "e" (wb * wc) { s with instIdx := 0 }) :=
    stepInstBase_binopVar (inst := bkhMul) (f := fun a b => a * b) (x := "b") (y := "c")
      (out := "e") rfl rfl rfl hb' hc'
  show (match stepInstBase bkhMul { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none) = _
  rw [hstep]; rfl

/-- The MUL errors when `b` is undefined (the shape `runBlock_body_head_error` consumes). -/
theorem bkhMul_error_b (s : VenomState) (hb : lookupVar "b" s = none) :
    stepInstBase bkhMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = none := hb
  simp [bkhMul, stepInstBase, execPure2, evalOperand, hb']

/-- The MUL errors when `c` is undefined (given `b` defined). -/
theorem bkhMul_error_c (s : VenomState) (wb : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = none) :
    stepInstBase bkhMul { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hb' : lookupVar "b" { s with instIdx := 0 } = some wb := hb
  have hc' : lookupVar "c" { s with instIdx := 0 } = none := hc
  simp [bkhMul, stepInstBase, execPure2, evalOperand, hb', hc']

/-- `next` halts when `a, b, c` are all defined: ADD then RETURN reads `e = b+c` and `a`. -/
theorem bkhNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc)
    (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) bkhCtx bkhNext s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (bkhNextSEnd s wb wc))
        (bkhNextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := bkhNextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return bkhCtx bkhNext j [bkhMul] bkhRet bkhMul [bkhRet] s (bkhNextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (bkhNext_thread s wb wc hb hc)

/-- `next` errors when `a` is undefined (given `b, c` defined): ADD succeeds, RETURN faults on `a`. -/
theorem bkhNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) bkhCtx bkhNext s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := bkhNextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term bkhCtx bkhNext j [bkhMul] bkhRet bkhMul [bkhRet] s (bkhNextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (bkhNext_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : bkhNext.instructions = [bkhMul] ++ [bkhRet])
    (bkhNext_thread s wb wc hb hc), bkhRet, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- lookupVar of `bkhEntrySEnd`: `a, b` are the call value, `c = callvalue - callvalue`. -/
theorem bkhEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (bkhEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (bkhEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (bkhEntrySEnd s) = some (bkhVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (bkhVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (bkhVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (bkhVal s)
      (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- The invariant: unhalted, zero call value, and at `next` the delivered `a, b, c` are all zero. -/
def bkhInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (bkhVal s))

theorem bkhInv_pres : ∀ bb ∈ bkhFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    bkhInv s → runBlock f' bkhCtx bb s = ExecResult.OK s' → bkhInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [bkhFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · -- entry: fuel ≤ 3 is out-of-fuel (Error); fuel ≥ 4 lands on `jumpTo "next" (bkhEntrySEnd s)`
    have hnt : ∀ inst ∈ [bkhCvA, bkhCvB, bkhLoad], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhEntry 0 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
             [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhEntry 1 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
             [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhEntry 2 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
             [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhEntry 3 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
             [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, bkhEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := bkhEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (bkhEntrySEnd s)) = lookupVar "c" (bkhEntrySEnd s) from rfl, hc0]
      rfl
  · -- next: RETURN never yields OK (ADD errors on undefined b/c, RETURN errors on undefined a, else Halt)
    rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 bkhCtx bkhNext s bkhMul [bkhRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error bkhCtx bkhNext bkhMul [bkhRet] s "undefined operand" j rfl
          (by decide) (bkhMul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 bkhCtx bkhNext s bkhMul [bkhRet] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error bkhCtx bkhNext bkhMul [bkhRet] s "undefined operand" j rfl
            (by decide) (bkhMul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 bkhCtx bkhNext s bkhMul [bkhRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhNext 1 [bkhMul] bkhRet bkhMul [bkhRet] s
                   (bkhNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (bkhNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, bkhNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 bkhCtx bkhNext s bkhMul [bkhRet] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof bkhCtx bkhNext 1 [bkhMul] bkhRet bkhMul [bkhRet] s
                   (bkhNextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (bkhNext_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, bkhNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- **Non-vacuity**: `runContext 10 bkhCtx vs` halts for every admitted state (callvalue zero).
    Chains `entry → next`, ending in `next`'s RETURN halt. -/
theorem bkhFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 bkhCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 bkhCtx vs
      = runBlocks 10 bkhCtx bkhFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, bkhCtx, bkhFn, lookupFunction, fnEntryLabel, bkhEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (bkhEntrySEnd s0) with hs1
  have hentry : runBlock 9 bkhCtx bkhEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact bkhEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb bkhFn.blocks = some bkhEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 bkhCtx bkhFn s0 = runBlocks 9 bkhCtx bkhFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := bkhEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (bkhVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (bkhEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb bkhFn.blocks = some bkhNext := rfl
  have hhalt := bkhNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (bkhVal s0)
    (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 4000000 in
/-- **A BLOCKHASH capstone.** `codegen_correct` for
    `entry: %a=CALLVALUE ; %b=CALLVALUE ; %c=BLOCKHASH %a ; JMP next` /
    `next: %e=MUL %b %c ; RETURN %e, %a`. `entry`'s BLOCKHASH exercises the 1-input transient-read arm
    (`RegularStepG`'s BLOCKHASH disjunct, `asmStep_tload_ok`), emitted `DUP2 ; BLOCKHASH`, leaving `c = bkhVal s`
    (context-dependent). `next`'s MUL consumes the top two `[b, c]` (so `a` is never buried — no f1a
    reorder); `b = 0` ⇒ `e = 0` (`uint256_zero_mul`) empties the return window. `next` ends in a
    body-then-RETURN handled by `hsupplyW_regularReturnTo`; `entry` via `hsupplyW_regularJmp`. -/
theorem codegen_correct_bkhFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 bkhCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ bkhFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [bkhFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [bkhEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [bkhNext, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan bkhFn 0 0
      = some ((generateFnPlan bkhFn 0 0).get!.1, (generateFnPlan bkhFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel bkhFn) bkhFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv bkhInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel bkhFn) bkhFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan bkhFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := bkhCtx) (fn := bkhFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan bkhFn 0 0).get!.1) (psFinal := (generateFnPlan bkhFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ bkhInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [bkhFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, bkhEntry, bkhCvA]
    · simp [runBlock, evalPhis, execBlock, bkhNext, bkhMul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [bkhFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: CALLVALUE ×2 + ADD (duplicating) + JMP next
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [bkhCvA, bkhCvB, bkhLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof bkhCtx bkhEntry 1 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
               [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof bkhCtx bkhEntry 2 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
               [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof bkhCtx bkhEntry 3 [bkhCvA, bkhCvB, bkhLoad] bkhJmp bkhCvA
               [bkhCvB, bkhLoad, bkhJmp] s (bkhEntrySEnd s) rfl rfl (by decide) hnt (bkhEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([bkhCvA, bkhCvB, bkhLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [bkhCvA, bkhCvB, bkhLoad]) (jmpInst := bkhJmp) (hd := bkhCvA) (tl := [bkhCvB, bkhLoad, bkhJmp])
        (nextLiveness := ["a", "b", "c"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 0) (lbl := "next") (off := 9) (bb' := bkhNext) (sEnd := bkhEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := bkhEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := bkhEntry_body)
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
      | 0 => exact Or.inl (runBlock_oof bkhCtx bkhNext 1 [bkhMul] bkhRet bkhMul [bkhRet] s
               (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (bkhNext_thread s _ _ hb0 hc0) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([bkhMul] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularReturnTo
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [bkhMul]) (retInst := bkhRet) (hd := bkhMul) (tl := [bkhRet])
        (nextLiveness := ["e", "a"]) (curBbLabel := "next") (dem := 1)
        (S := ["a", "b", "c"]) (Sn := ["a", "e"])
        (ps0 := psOfFn (fnPlanFuel bkhFn) bkhFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := bkhNext_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s))
            = lookupVar "e" (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) from rfl,
            (bkhNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (bkhVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s))
            = lookupVar "a" (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) from rfl,
            (bkhNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (bkhVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) from rfl,
            (bkhNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (bkhVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (bkhNextSEnd s (EvmYul.UInt256.ofNat 0) (bkhVal s)) from rfl,
            (bkhNextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (bkhVal s)).2]; exact ha0)
        (hready := bkhNext_ready)
        (hsd := ⟨by intro op; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel bkhFn) bkhFn 0 0 "next").stack
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
    refine ⟨⟨bkhEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel bkhFn) bkhFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan bkhFn 0 0).get!.1)).1.length
      omega


end Example

end EvmYul.Venom.Hol.Codegen

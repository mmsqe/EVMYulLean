/-
GenBlockSimExample / the MEMORY-OP capstone (MSTORE) — `codegen_correct_msvFn_recipeW`

The first memory-WRITING whole-function capstone: `entry: %a=CALLVALUE; JMP work` /
`work: MSTORE (Lit 0) %a; RETURN (Lit 0) (Lit 32)` at `fnEom = 64`. The callvalue is stored and
returned — the returndata carries the ACTUAL callvalue bytes (no zero-value hypothesis, no
MUL-by-0 kill). Built on the consuming-lit MSTORE fold step (`bodyStepHTo_mstoreLit`,
`asmMstore_noSpill_rel` — no fnEom bound at the store; 64 is needed only by the RETURN-window
slice condition `off+len ≤ fnEom`). The work block's asm run is fully explicit (label, PUSH0,
MSTORE, PUSH 32, PUSH0), with the RETURN-window coverage derived STRUCTURALLY from the write
(`byteArray_write_size_window`). Also hosts the generic Lit-window RETURN slice
`hsupplyW_regularReturnLitTo` (usable when entry-state coverage holds).
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeTernops

namespace EvmYul.Venom.Hol.Codegen

/-- **The Lit-window non-empty-body RETURN slice** — `hsupplyW_regularReturnTo` for
    `RETURN (Lit woff) (Lit wsz)`: the terminator's input plan pushes the two literals
    (`PUSH wsz ; PUSH woff`) between the body and the `RETURN`, so the slice runs
    label + body + 2 pushes and hands `termRecipeW_return_of_body` the pushed stack
    (`woff :: wsz :: rest` directly from the pushes — no positioning hypothesis). The
    operand evaluations are `rfl`. -/
theorem hsupplyW_regularReturnLitTo
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {retInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    {woff wsz : bytes32}
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RETURN)
    (hoperands : retInst.operands = [Operand.Lit woff, Operand.Lit wsz])
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      (fun _ => dem) (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    (hpushes : asmBlockAt prog (asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length)
      (executePlan [StackOp.SOPush (Operand.Lit wsz), StackOp.SOPush (Operand.Lit woff)]))
    (hpc : asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
        + (executePlan [StackOp.SOPush (Operand.Lit wsz), StackOp.SOPush (Operand.Lit woff)]).length
        < prog.length)
    (hret : prog.get ⟨asm.pc + 1 + (executePlan
        (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
        + (executePlan [StackOp.SOPush (Operand.Lit wsz), StackOp.SOPush (Operand.Lit woff)]).length, hpc⟩
      = AsmInst.AsmOp "RETURN")
    (hcov0 : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ asm.memory.size)
    (hbelow : woff.toNat + wsz.toNat
      ≤ (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2.alloc.fnEom)
    (hlenu : wsz.toNat < USize.size)
    (hw : 1 + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
        + (executePlan [StackOp.SOPush (Operand.Lit wsz), StackOp.SOPush (Operand.Lit woff)]).length + 1
      ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simTo (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  -- run the terminator's two literal pushes
  set psB := (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).2 with hpsB
  have hpairEq := emitInputPlan_pair_lit_eq retInst.opcode nextLiveness wsz woff psB
  have hbp : asmBlockAt prog as'.pc
      (executePlan (emitInputPlan retInst.opcode [Operand.Lit wsz, Operand.Lit woff] nextLiveness psB).1) := by
    rw [hpairEq, hpcas]; exact hpushes
  obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emitInputPlan_pair_lit_sim hrel' hbp
  rw [hpairEq] at hrun2 hrel2 hpc2
  have htop : as2.stack = woff :: wsz :: as2.stack.drop 2 :=
    venomAsmRel_asmStack_top2_lit hrel2 rfl
  have hlt : as2.pc < prog.length := by rw [hpc2, hpcas]; exact hpc
  have hpcall : as2.pc = asm.pc + 1
      + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length
      + (executePlan [StackOp.SOPush (Operand.Lit wsz), StackOp.SOPush (Operand.Lit woff)]).length := by
    rw [hpc2, hpcas]
  have hst : prog.get ⟨as2.pc, hlt⟩ = AsmInst.AsmOp "RETURN" := prog_get_transfer hpcall hret
  have hcov : wsz.toNat = 0 ∨ ((woff.toNat + wsz.toNat + 31) / 32) * 32 ≤ as2.memory.size := by
    rcases hcov0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (le_trans h (runAsm_memory_size_mono hbody)) (runAsm_memory_size_mono hrun2))
  refine ⟨as2, { psB with stack := psB.stack ++ [Operand.Lit wsz, Operand.Lit woff] }, sEnd, _, runAsm_compose hbody hrun2, ?_⟩
  exact termRecipeW_return_of_body (front := front) (retInst := retInst) (hd := hd) (tl := tl)
    (restFuel := restFuel) (offOp := Operand.Lit woff) (szOp := Operand.Lit wsz)
    (off := woff) (sz := wsz) (rest := as2.stack.drop 2)
    hbb hop hoperands rfl rfl hcons hphi hnonterm hthread hrel2 (by omega) hlt hst htop hcov
    (by simpa using hbelow) hlenu

namespace Example
open EvmYul.Venom.Hol.Codegen.Example

/-! ### The MSTORE capstone `msv`: `entry: %a=CALLVALUE; JMP work` / `work: MSTORE 0 %a; RETURN 0 32`
    at `fnEom = 64`. First memory-writing whole-function capstone; the returndata carries the
    stored callvalue bytes (no callvalue-0 hypothesis, no MUL-by-0). -/

def msvCv : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def msvJmp : Instruction := { id := 1, opcode := Opcode.JMP, operands := [Operand.Label "work"], outputs := [] }
def msvSt : Instruction := { id := 2, opcode := Opcode.MSTORE, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Var "a"], outputs := [] }
def msvRet : Instruction := { id := 3, opcode := Opcode.RETURN, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Lit (EvmYul.UInt256.ofNat 32)], outputs := [] }
def msvEntry : BasicBlock := { label := "entry", instructions := [msvCv, msvJmp] }
def msvWork : BasicBlock := { label := "work", instructions := [msvSt, msvRet] }
def msvFn : IrFunction := { name := "main", blocks := [msvEntry, msvWork] }
def msvCtx : VenomContext := { functions := [msvFn], entry := some "main" }

/-- Post-write window coverage: writing `source` at `off` into a covering `dest` leaves
    `off + source.size` bytes. The size half of `write_data_of_le`. -/
theorem byteArray_write_size_window (source dest : ByteArray) (off : Nat)
    (hpos : 0 < source.size) (hoff : off ≤ dest.size) :
    off + source.size ≤ (source.write 0 dest off source.size).size := by
  have hd := ByteArray.write_data_of_le source dest off hpos hoff
  have hsz : (source.write 0 dest off source.size).size
      = (dest.data.extract 0 off ++ source.data
          ++ dest.data.extract (off + source.size) dest.data.size).size := by
    rw [ByteArray.size_eq, hd]
  rw [hsz]
  simp only [Array.size_append, Array.size_extract]
  have h1 : dest.data.size = dest.size := rfl
  have h2 : source.data.size = source.size := rfl
  omega

abbrev msvWorkSEnd (s : VenomState) (w : bytes32) : VenomState :=
  { mstore (EvmYul.UInt256.ofNat 0).toNat w { s with instIdx := 0 } with instIdx := 1 }

theorem msvWork_thread (s : VenomState) (w : bytes32) (ha : lookupVar "a" s = some w) :
    execBodyThread [msvSt] 0 { s with instIdx := 0 } = some (msvWorkSEnd s w) := by
  have ha' : lookupVar "a" ({ s with instIdx := 0 } : VenomState) = some w := ha
  have hstep : stepInstBase msvSt { s with instIdx := 0 }
      = ExecResult.OK (mstore (EvmYul.UInt256.ofNat 0).toNat w { s with instIdx := 0 }) := by
    show execWrite2 (fun addr val s => mstore addr.toNat val s) msvSt { s with instIdx := 0 } = _
    unfold execWrite2
    simp only [msvSt, evalOperand, ha']
  show (match stepInstBase msvSt { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none)
      = some (msvWorkSEnd s w)
  rw [hstep]; rfl

theorem msvSt_error (s : VenomState) (ha : lookupVar "a" s = none) :
    stepInstBase msvSt { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have ha' : lookupVar "a" ({ s with instIdx := 0 } : VenomState) = none := ha
  show execWrite2 (fun addr val s => mstore addr.toNat val s) msvSt { s with instIdx := 0 } = _
  unfold execWrite2
  simp [msvSt, evalOperand, ha']

abbrev msvEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }

theorem msvEntry_thread (s : VenomState) :
    execBodyThread [msvCv] 0 { s with instIdx := 0 } = some (msvEntrySEnd s) := by
  have h1 : stepInstBase msvCv { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  show (match stepInstBase msvCv { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none)
      = some (msvEntrySEnd s)
  rw [h1]; rfl

theorem msvEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (1 + (j + 1)) msvCtx msvEntry s = ExecResult.OK (jumpTo "work" (msvEntrySEnd s)) :=
  runBlock_body_jmp msvCtx msvEntry j [msvCv] msvJmp msvCv [msvJmp] s (msvEntrySEnd s) "work"
    rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (msvEntry_thread s) (by simpa [updateVar] using hnh)

theorem msvWork_halts (s : VenomState) (j : Nat) (w : bytes32) (ha : lookupVar "a" s = some w) :
    runBlock (1 + (j + 1)) msvCtx msvWork s = ExecResult.Halt
      (haltState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 32).toNat
        (msvWorkSEnd s w)) (msvWorkSEnd s w))) :=
  runBlock_body_return msvCtx msvWork j [msvSt] msvRet msvSt [msvRet] s (msvWorkSEnd s w)
    (Operand.Lit (EvmYul.UInt256.ofNat 0)) (Operand.Lit (EvmYul.UInt256.ofNat 32))
    (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) rfl rfl rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (msvWork_thread s w ha)

def msvInv (s : VenomState) : Prop :=
  s.halted = false ∧ (s.currentBb = "work" → ∃ w, lookupVar "a" s = some w)

theorem msvInv_pres : ∀ bb ∈ msvFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    msvInv s → runBlock f' msvCtx bb s = ExecResult.OK s' → msvInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hwork⟩ := hinv
  simp only [msvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof msvCtx msvEntry 0 [msvCv] msvJmp msvCv [msvJmp] s
             (msvEntrySEnd s) rfl rfl (by decide)
             (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
             (msvEntry_thread s) (by simp)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof msvCtx msvEntry 1 [msvCv] msvJmp msvCv [msvJmp] s
             (msvEntrySEnd s) rfl rfl (by decide)
             (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
             (msvEntry_thread s) (by simp)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+2) =>
      rw [show j+2 = 1+(j+1) from by omega, msvEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, fun _ => ⟨s.callCtx.callvalue, ?_⟩⟩
      show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) = _
      rw [lookupVar_updateVar_self]
  · rcases hla : lookupVar "a" s with _ | w
    · match f' with
      | 0 => rw [runBlock_no_phi 0 msvCtx msvWork s msvSt [msvRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error msvCtx msvWork msvSt [msvRet] s "undefined operand" j rfl
          (by decide) (msvSt_error s hla) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · match f' with
      | 0 => rw [runBlock_no_phi 0 msvCtx msvWork s msvSt [msvRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | 1 => obtain ⟨e, he⟩ := runBlock_oof msvCtx msvWork 1 [msvSt] msvRet msvSt [msvRet] s
               (msvWorkSEnd s w) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (msvWork_thread s w hla) (by decide)
             rw [he] at hrun; exact absurd hrun (by simp)
      | (j+2) =>
        rw [show j+2 = 1+(j+1) from by omega, msvWork_halts s j w hla] at hrun
        exact absurd hrun (by simp)

theorem msvFn_halts (vs : VenomState) (hnh : vs.halted = false) :
    ∃ vs', runContext 10 msvCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 msvCtx vs
      = runBlocks 10 msvCtx msvFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, msvCtx, msvFn, lookupFunction, fnEntryLabel, msvEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  set s1 : VenomState := jumpTo "work" (msvEntrySEnd s0) with hs1
  have hentry : runBlock 9 msvCtx msvEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 1 + (7 + 1) from by omega]; exact msvEntry_runBlock s0 7 hnh0
  have hlk0 : lookupBlock s0.currentBb msvFn.blocks = some msvEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 msvCtx msvFn s0 = runBlocks 9 msvCtx msvFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  have ha1 : lookupVar "a" s1 = some s0.callCtx.callvalue := by
    show lookupVar "a" (updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 }) = _
    rw [lookupVar_updateVar_self]
  have hlk1 : lookupBlock s1.currentBb msvFn.blocks = some msvWork := rfl
  have hhalt := msvWork_halts s1 6 s0.callCtx.callvalue ha1
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 1000000 in
/-- **The MSTORE capstone.** `codegen_correct` for `entry: %a=CALLVALUE; JMP work` /
    `work: MSTORE (Lit 0) %a; RETURN (Lit 0) (Lit 32)` at `fnEom = 64`: the callvalue is stored
    to memory and RETURNed — the returndata carries the actual callvalue bytes (no zero-value
    hypothesis). The work block runs fully explicit asm steps, with the RETURN-window coverage
    derived STRUCTURALLY from the write (`byteArray_write_size_window`). -/
theorem codegen_correct_msvFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 msvCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ msvFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [msvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [msvEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [msvWork, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan msvFn 64 0
      = some ((generateFnPlan msvFn 64 0).get!.1, (generateFnPlan msvFn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel msvFn) msvFn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv msvInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel msvFn) msvFn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan msvFn 64 0).get!.1)).2)
    (fuel := 10) (ctx := msvCtx) (fn := msvFn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan msvFn 64 0).get!.1) (psFinal := (generateFnPlan msvFn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ msvInv_pres ?_
    ⟨by simpa using hvshalt, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [msvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, msvEntry, msvCv]
    · simp [runBlock, evalPhis, execBlock, msvWork, msvSt]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [msvFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [msvCv], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof msvCtx msvEntry 1 [msvCv] msvJmp msvCv [msvJmp] s
               (msvEntrySEnd s) rfl rfl (by decide) hnt (msvEntry_thread s) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([msvCv] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [msvCv]) (jmpInst := msvJmp) (hd := msvCv) (tl := [msvJmp])
        (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 64) (lbl := "work") (off := 6) (bb' := msvWork) (sEnd := msvEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := msvEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · have hlbl : s.currentBb = "work" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, hwork⟩ := hinv
      obtain ⟨wa, ha⟩ := hwork hlbl
      have hpcw : asm.pc = 4 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof msvCtx msvWork 1 [msvSt] msvRet msvSt [msvRet] s
               (msvWorkSEnd s wa) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (msvWork_thread s wa ha) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([msvSt] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psW := psOfFn (fnPlanFuel msvFn) msvFn 64 0 "work" with hpsW
      have hpsWstack : psW.stack = [Operand.Var "a"] := rfl
      have hpsWspill : ∀ op, alookup' psW.spilled op = none := fun _ => rfl
      set prog := (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).2 with ho2pcdef
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "work"]) := by
        rw [hpcw]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psW { s with instIdx := 0 } asm prog "work" hvrel hbL
      have hpcA : as1.pc = 5 := by
        rw [show (executePlan [StackOp.SOLabel "work"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpcw]
      have hbP0 : asmBlockAt prog as1.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emitOneInput_sim_lit_append (opc := Opcode.MSTORE)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel1 hbP0
      have hpcB : as2.pc = 6 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      have hva : operandVal ({ s with instIdx := 0 } : VenomState) lo (Operand.Var "a") = some wa := ha
      have hstack2 : as2.stack = (EvmYul.UInt256.ofNat 0) :: wa :: as2.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "a")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel2 (base := ([] : List Operand)) ?_ hva rfl
        show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack = _
        rw [hpsWstack]; rfl
      obtain ⟨hmst, hrel3⟩ := asmMstore_noSpill_rel (lo := lo)
        (ps := { psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] })
        (vs := { s with instIdx := 0 }) (as := as2)
        hrel2 hstack2 (fun op => hpsWspill op)
        (Nat.zero_le _) (Nat.zero_le _)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      have hltB : as2.pc < prog.length := by rw [hpcB]; decide
      have hgetB : prog.get ⟨as2.pc, hltB⟩ = AsmInst.AsmOp "MSTORE" := by
        conv_lhs => rw [show (⟨as2.pc, hltB⟩ : Fin _) = ⟨6, by decide⟩ from Fin.ext hpcB]
        rfl
      have hstep3 : asmStep o2pc prog as2 = asmMstore as2 := asmStep_mstore_ok hltB hgetB
      set as3 : AsmState := { asmNext as2 with
          stack := as2.stack.drop 2,
          memory := (wordToBytes wa).write 0
            (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as2.memory)
            (EvmYul.UInt256.ofNat 0).toNat 32 } with has3
      have hstep3ok : asmStep o2pc prog as2 = AsmResult.AsmOK as3 := by rw [hstep3, hmst]
      have hrun3 : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
        rw [runAsm_succ_ok hltB hstep3ok]; rfl
      have hpcC : as3.pc = 7 := by rw [has3]; show as2.pc + 1 = 7; rw [hpcB]
      have hcov3 : 32 ≤ as3.memory.size := by
        have h32 : (wordToBytes wa).size = 32 := length_wordToBytes wa
        have hwin := byteArray_write_size_window (wordToBytes wa)
          (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as2.memory)
          (EvmYul.UInt256.ofNat 0).toNat (by rw [h32]; decide) (Nat.zero_le _)
        rw [h32] at hwin
        simpa [has3, show (EvmYul.UInt256.ofNat 0).toNat = 0 from rfl] using hwin
      have hrel3' : venomAsmRel lo { psW with stack := ([] : List Operand) } (msvWorkSEnd s wa) as3 := by
        have hpop : ({ psW with stack := stackPop 2 ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack } : PlanState)
            = { psW with stack := ([] : List Operand) } := by
          rw [show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack
            = [Operand.Var "a", Operand.Lit (EvmYul.UInt256.ofNat 0)] from by rw [hpsWstack]; rfl]
          rfl
        have h := hrel3
        rw [show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState) = { psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } from rfl] at h
        exact hpop ▸ h
      have hbP32 : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4a⟩ := emitOneInput_sim_lit_append (opc := Opcode.RETURN)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 32) hrel3' hbP32
      have hpcD : as4.pc = 8 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length = 1 from rfl] at hpc4a
        rw [hpc4a, hpcC]
      have hbP0b : asmBlockAt prog as4.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcD]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as5, hrun5, hrel5, hpc5a⟩ := emitOneInput_sim_lit_append (opc := Opcode.RETURN)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel4 hbP0b
      have hpcE2 : as5.pc = 9 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc5a
        rw [hpc5a, hpcD]
      have htop5 : as5.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 32) :: as5.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Lit (EvmYul.UInt256.ofNat 32))
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel5 (base := ([] : List Operand)) ?_ rfl rfl
        rfl
      have hcov5 : 32 ≤ as5.memory.size :=
        le_trans hcov3 (le_trans (runAsm_memory_size_mono hrun4) (runAsm_memory_size_mono hrun5))
      have hrunAll : runAsm (1 + 1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as5 := by
        have hrun1' : runAsm 1 o2pc prog asm = AsmResult.AsmOK as1 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOLabel "work"]).length from rfl]; exact hrun1
        have hrun2' : runAsm 1 o2pc prog as1 = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun2
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length from rfl]; exact hrun4
        have hrun5' : runAsm 1 o2pc prog as4 = AsmResult.AsmOK as5 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun5
        exact runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose hrun1' hrun2') hrun3) hrun4') hrun5'
      have hterm := termRecipeW_return_of_body (front := [msvSt]) (retInst := msvRet) (hd := msvSt)
        (tl := [msvRet]) (restFuel := j)
        (offOp := Operand.Lit (EvmYul.UInt256.ofNat 0)) (szOp := Operand.Lit (EvmYul.UInt256.ofNat 32))
        (off := EvmYul.UInt256.ofNat 0) (sz := EvmYul.UInt256.ofNat 32) (rest := as5.stack.drop 2)
        (bodyLen := 5) (bb := msvWork) (ctx := msvCtx) (prog := prog) (o2pc := o2pc)
        (as' := as5) (fn := msvFn) (lo := lo) (s := s)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel msvFn) msvFn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan msvFn 64 0).get!.1)).2)
        rfl rfl rfl rfl rfl rfl (by decide)
        (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (msvWork_thread s wa ha) hrel5 (by decide)
        (by rw [hpcE2]; decide)
        (by conv_lhs => rw [show (⟨as5.pc, by rw [hpcE2]; decide⟩ : Fin _) = ⟨9, by decide⟩
              from Fin.ext hpcE2]
            rfl)
        htop5
        (Or.inr (by
          rw [show ((EvmYul.UInt256.ofNat 0).toNat + (EvmYul.UInt256.ofNat 32).toNat + 31) / 32 * 32
            = 32 from by rfl]
          exact hcov5))
        (by decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      exact ⟨as5, _, msvWorkSEnd s wa, 5, hrunAll, hterm⟩
  case _ =>
    refine ⟨⟨msvEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel msvFn) msvFn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan msvFn 64 0).get!.1)).1.length
      omega
end Example

/-! ## MSTORE8 — the 1-byte sibling (`codegen_correct_m8vFn_recipeW`)

Full clone of the MSTORE package: `asmMstore8_noSpill_rel` (1-byte write congruence via the
generic `readByte_write_congr`), the consuming-lit fold chain, and the `m8v` capstone —
`entry: %a=CALLVALUE; JMP work` / `work: MSTORE8 (Lit 0) %a; RETURN (Lit 0) (Lit 32)` at
`fnEom = 64`; the returndata carries `[callvalue % 256, 0 × 31]`. The window coverage comes from
`asmExpandMemory_size_rounded` (expansion rounds to a 32-multiple, so even the 1-byte store
covers the 32-byte RETURN window). -/

/-- **The no-spill MSTORE8 step + relation** — the 1-byte sibling of `asmMstore_noSpill_rel`:
    no `fnEom` bound (spill vacuity under `noSpill`; `memoryRel` by 1-byte write congruence
    over the expanded asm memory). -/
theorem asmMstore8_noSpill_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {offset value : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: value :: rest)
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hcovV : offset.toNat ≤ vs.memory.size)
    (hcovA : offset.toNat ≤ (asmExpandMemory (offset.toNat + 1) as.memory).size)
    (hro : ((offset.toNat + 1 + 31) / 32) * 32 < USize.size) :
    asmMstore8 as = AsmResult.AsmOK ({ asmNext as with stack := rest, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 (asmExpandMemory (offset.toNat + 1) as.memory) offset.toNat 1 })
    ∧ venomAsmRel lo { ps with stack := stackPop 2 ps.stack } (mstore8 offset.toNat value vs)
        { asmNext as with stack := rest, memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 (asmExpandMemory (offset.toNat + 1) as.memory) offset.toNat 1 } := by
  constructor
  · simp only [asmMstore8, hstack]
  · obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
    have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
    have hps := planStackRel_popN hStk hlen2
    rw [hstack] at hps
    have hsz1 : (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).size = 1 := rfl
    have hstate : mstore8 offset.toNat value vs
        = { vs with memory := (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray).write 0 vs.memory offset.toNat 1 } := by
      show writeMemoryWithExpansion offset.toNat ⟨#[UInt8.ofNat (value.toNat % 256)]⟩ vs = _
      unfold writeMemoryWithExpansion
      rw [hsz1]
    rw [hstate]
    refine ⟨hps, ?_, ?_, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩
    · intro op off' hlook
      rw [show AssocList.lookup Operand Nat ps.spilled op = alookup' ps.spilled op from rfl,
          hnospill op] at hlook
      exact absurd hlook (by simp)
    · intro i hi
      have hc := readByte_write_congr (⟨#[UInt8.ofNat (value.toNat % 256)]⟩ : ByteArray)
        vs.memory (asmExpandMemory (offset.toNat + 1) as.memory) offset.toNat i
        (by rw [hsz1]; decide) hcovV hcovA
        (by rw [readByte_asmExpandMemory i _ as.memory hro]; exact hMem i hi)
      rw [hsz1] at hc
      exact hc
/-- Headroom preservation for the consuming-lit 1-byte store. -/
theorem stackDisc_mstore8Lit_preserve
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {vs : VenomState} {y : String} {a wy : bytes32} {base : List Operand} {name : String}
    {idx j : Nat}
    (hsd : StackDiscH (j + 1) ps vs)
    (hname : opcodeToEvmName inst.opcode = some name)
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base ++ [Operand.Var y])
    (hnospill_y : alookup' ps.spilled (Operand.Var y) = none)
    (hdead_y : nextLiveness.contains y = false)
    (hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 a.toNat wy vs)) :
    StackDiscH j (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
      nextIsTerminator curBbLabel ps).2 (gvBodyStep (inst, idx) vs) := by
  rw [genRegularInstPlan_mstoreLit_eq hname hncomm hnjmp hcompute hops houts hstack0 hnospill_y hdead_y]
  apply releaseDeadSpills_stackDiscH
  have hrev8 : inst.operands.reverse = [Operand.Var y, Operand.Lit a] := by rw [hops]; rfl
  rw [show ({ (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with stack := base } : PlanState)
      = { ps with stack := base } from by
    rw [hrev8, emitInputPlan_pair_deadVarLit_eq hnospill_y hdead_y]]
  have hgv : gvBodyStep (inst, idx) vs = { mstore8 a.toNat wy vs with instIdx := idx + 1 } := by
    unfold gvBodyStep; rw [hstepEq]
  rw [hgv]
  refine ⟨fun op => hsd.noSpill op, ?_, ?_⟩
  · show base.length + j ≤ 15
    have := hsd.shallow
    rw [hstack0] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  · intro z hz
    show ∃ w, lookupVar z vs = some w
    exact hsd.defined z (by rw [hstack0]; exact List.mem_append_left _ hz)

/-- Runnable sim for `MSTORE8 (Lit a) %y` (y dying at TOS, `a.toNat = 0`, no spills). -/
theorem genRegularInstPlan_mstore8Lit_sim
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {y : String} {a wy : bytes32} {base : List Operand}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [])
    (hstack0 : ps.stack = base ++ [Operand.Var y])
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hdead_y : nextLiveness.contains y = false)
    (hwz : a.toNat = 0)
    (hvy : operandVal vs lo (Operand.Var y) = some wy)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s)
    (hrel : venomAsmRel lo ps vs as)
    (hblock : asmBlockAt prog as.pc
      (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).1)) :
    ∃ as', runAsm (executePlan (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).1).length offsetToPc prog as
             = AsmResult.AsmOK as' ∧
           venomAsmRel lo (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
             nextIsTerminator curBbLabel ps).2 (mstore8 a.toNat wy vs) as' ∧
           as'.pc = as.pc + (executePlan (generateRegularInstPlan liveness dfg cfg fn inst
             nextLiveness false nextIsTerminator curBbLabel ps).1).length := by
  have hrev : inst.operands.reverse = [Operand.Var y, Operand.Lit a] := by rw [hops]; rfl
  have hgen := genRegularInstPlan_mstoreLit_eq (liveness := liveness) (dfg := dfg) (cfg := cfg)
    (fn := fn) (nextIsTerminator := nextIsTerminator) (curBbLabel := curBbLabel)
    hname hncomm hnjmp hcompute hops houts hstack0 (hnospill _) hdead_y
  rw [hgen] at hblock ⊢
  set ps1 := (emitInputPlan inst.opcode inst.operands.reverse nextLiveness ps).2 with hps1def
  have hpair := emitInputPlan_pair_deadVarLit_eq (opc := inst.opcode) (nl := nextLiveness)
    (a := a) (hnospill _) hdead_y
  have hps1stack : ps1.stack = base ++ [Operand.Var y, Operand.Lit a] := by
    rw [hps1def, hrev, hpair]; simp [hstack0]
  have hps1spill : ps1.spilled = ps.spilled := by
    rw [hps1def, hrev, hpair]
  have hsplit : ([StackOp.SOPush (Operand.Lit a), StackOp.SOEmit "MSTORE8"] : List StackOp)
      = [StackOp.SOPush (Operand.Lit a)] ++ [StackOp.SOEmit "MSTORE8"] := rfl
  rw [hsplit, executePlan_append] at hblock
  obtain ⟨hbI, hbE⟩ := asmBlockAt_append hblock
  obtain ⟨as1, hrunI, hrelI', hpcI⟩ := emitOneInput_sim_lit_append (opc := inst.opcode)
    (nl := nextLiveness) (v := a) hrel hbI
  have hrelI : venomAsmRel lo ps1 vs as1 := by
    have : ({ ps with stack := ps.stack ++ [Operand.Lit a] } : PlanState) = ps1 := by
      rw [hps1def, hrev, hpair]; try simp [stackPush]
    rwa [this] at hrelI'
  have hstacktop : as1.stack = a :: wy :: as1.stack.drop 2 :=
    venomAsmRel_asmStack_top2 hrelI hps1stack hvy rfl
  have hbE' : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "MSTORE8"]) := by
    rw [hpcI]; exact hbE
  obtain ⟨hpcE, hgetE⟩ := asmBlockAt_one hbE'
  have hnospill1 : ∀ op, alookup' ps1.spilled op = none := by
    intro op; rw [hps1spill]; exact hnospill op
  obtain ⟨hmst, hrelE⟩ := asmMstore8_noSpill_rel (lo := lo) (ps := ps1) (vs := vs) (as := as1)
    hrelI hstacktop hnospill1
    (by rw [hwz]; exact Nat.zero_le _)
    (by rw [hwz]; exact Nat.zero_le _)
    (by rw [hwz]; try (rcases USize.size_eq with h | h <;> omega))
  have hstepE : asmStep offsetToPc prog as1 = AsmResult.AsmOK ({ asmNext as1 with
      stack := as1.stack.drop 2,
      memory := (⟨#[UInt8.ofNat (wy.toNat % 256)]⟩ : ByteArray).write 0 (asmExpandMemory (a.toNat + 1) as1.memory) a.toNat 1 }) := by
    rw [hdisp as1 hpcE hgetE, hmst]
  have hps5 : ({ ps1 with stack := stackPop 2 ps1.stack } : PlanState) = { ps1 with stack := base } := by
    rw [hps1stack, stackPop_2_append_pair]
  rw [hps5] at hrelE
  have hrelR := releaseDeadSpills_sim (nextLiveness := nextLiveness) hrelE
  refine ⟨_, ?_, hrelR, ?_⟩
  · show runAsm (executePlan ([StackOp.SOPush (Operand.Lit a)] ++ [StackOp.SOEmit "MSTORE8"])).length
        offsetToPc prog as = _
    rw [executePlan_append, List.length_append]
    exact runAsm_compose hrunI (by
      show runAsm (executePlan [StackOp.SOEmit "MSTORE8"]).length offsetToPc prog as1 = _
      rw [show (executePlan [StackOp.SOEmit "MSTORE8"]).length = 1 from rfl,
          runAsm_succ_ok hpcE hstepE]; rfl)
  · show ({ asmNext as1 with stack := as1.stack.drop 2, memory := (⟨#[UInt8.ofNat (wy.toNat % 256)]⟩ : ByteArray).write 0 (asmExpandMemory (a.toNat + 1) as1.memory) a.toNat 1 } : AsmState).pc = as.pc + (executePlan ([StackOp.SOPush (Operand.Lit a)] ++ [StackOp.SOEmit "MSTORE8"])).length
    rw [executePlan_append, List.length_append]
    show (asmNext as1).pc = _
    simp only [asmNext, hpcI]
    rw [show (executePlan [StackOp.SOEmit "MSTORE8"]).length = 1 from rfl]
    omega

/-- **The `StackIsVars`-aware body step for `MSTORE8 (Lit a) %y`.** -/
theorem stackDisc_mstore8Lit_step_S
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nextLiveness : List String} {nextIsTerminator : Bool} {curBbLabel : String}
    {ps : PlanState} {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {prog : List AsmInst}
    {offsetToPc : AssocList Nat Nat}
    {baseS : List String} {y : String} {a : bytes32} {j idx : Nat}
    (hsd : StackDiscH (j + 1) ps vs)
    (hsv : StackIsVars (baseS ++ [y]) ps)
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : stepInstBase inst vs = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst vs)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [])
    (hdead_y : nextLiveness.contains y = false)
    (hwz : a.toNat = 0)
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
    ∧ StackIsVars baseS (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false
        nextIsTerminator curBbLabel ps).2 := by
  have hstack0 : ps.stack = (baseS.map Operand.Var) ++ [Operand.Var y] := by
    have h := hsv
    unfold StackIsVars at h
    rw [h, List.map_append]; rfl
  have hymem : Operand.Var y ∈ ps.stack := by rw [hstack0]; simp
  have hnospill_y : alookup' ps.spilled (Operand.Var y) = none := hsd.noSpill _
  obtain ⟨wy, hwy⟩ := hsd.defined y hymem
  have hvy : operandVal vs lo (Operand.Var y) = some wy := hwy
  have hnospill : ∀ op, alookup' ps.spilled op = none := fun op => hsd.noSpill op
  have hstepEq : stepInstBase inst vs = ExecResult.OK (mstore8 a.toNat wy vs) := by
    rw [hdispatch]; unfold execWrite2; rw [hops]; simp only [evalOperand, hwy]
  have hsim := genRegularInstPlan_mstore8Lit_sim hname hncomm hnjmp hcompute hops houts hstack0
    hnospill hdead_y hwz hvy hdisp hrel hblock
  refine ⟨gvBodyStep_of_ok (idx := idx) hstepEq hsim, ?_, ?_⟩
  · exact stackDisc_mstore8Lit_preserve (idx := idx) hsd hname hncomm hnjmp hcompute hops houts
      hstack0 hnospill_y hdead_y hstepEq
  · show (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness false nextIsTerminator
      curBbLabel ps).2.stack = baseS.map Operand.Var
    rw [genRegularInstPlan_mstoreLit_outStack hname hncomm hnjmp hcompute hops houts hstack0
      hnospill_y hdead_y]

/-- **`BodyStepHTo` for the consuming-lit 1-byte store** `MSTORE8 (Lit a) %y`. -/
theorem bodyStepHTo_mstore8Lit
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst}
    {inst : Instruction} {nextLiveness : List String} {curBbLabel : String}
    {baseS : List String} {y : String} {a : bytes32} {idx : Nat}
    (hname : opcodeToEvmName inst.opcode = some "MSTORE8")
    (hncomm : isCommutative inst.opcode = false)
    (hnjmp : inst.opcode ≠ Opcode.JMP)
    (hcompute : computeOperands inst = inst.operands.reverse)
    (hdispatch : ∀ v, stepInstBase inst v = execWrite2 (fun addr val s => mstore8 addr.toNat val s) inst v)
    (hops : inst.operands = [Operand.Lit a, Operand.Var y])
    (houts : inst.outputs = [])
    (hdead_y : nextLiveness.contains y = false)
    (hwz : a.toNat = 0)
    (hdisp : ∀ (s : AsmState) (h : s.pc < prog.length),
        prog.get ⟨s.pc, h⟩ = AsmInst.AsmOp "MSTORE8" → asmStep offsetToPc prog s = asmMstore8 s) :
    BodyStepHTo lo offsetToPc prog
      (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
      1 (inst, idx) (baseS ++ [y]) baseS := by
  intro p v s j hsd hsv hrel hblock
  exact stackDisc_mstore8Lit_step_S (idx := idx) hsd hsv hname hncomm hnjmp hcompute (hdispatch v)
    hops houts hdead_y hwz hdisp hrel hblock

/-- Expansion covers the ROUNDED request: `((n+31)/32)*32 ≤ (asmExpandMemory n mem).size`. -/
theorem asmExpandMemory_size_rounded (n : Nat) (mem : ByteArray)
    (hro : ((n + 31) / 32) * 32 < USize.size) :
    ((n + 31) / 32) * 32 ≤ (asmExpandMemory n mem).size := by
  unfold asmExpandMemory
  by_cases h : ((n + 31) / 32) * 32 ≤ mem.size
  · simpa [h] using h
  · simp only [h, if_false]
    have hpadsz : (ffi.ByteArray.zeroes ⟨(↑((n + 31) / 32 * 32) - ↑mem.size : BitVec System.Platform.numBits)⟩).size
        = (n + 31) / 32 * 32 - mem.size :=
      ByteArray.zeroes_bvsub_size ((n + 31) / 32 * 32) mem.size (by omega) hro
    set pad := ffi.ByteArray.zeroes ⟨(↑((n + 31) / 32 * 32) - ↑mem.size : BitVec System.Platform.numBits)⟩ with hpad
    have hlen : pad.write 0 mem mem.size ((n + 31) / 32 * 32 - mem.size)
        = pad.write 0 mem mem.size pad.size := by rw [hpadsz]
    rw [hlen]
    have hwin := Example.byteArray_write_size_window pad mem mem.size (by rw [hpadsz]; omega) (Nat.le_refl _)
    have hbound : (n + 31) / 32 * 32 ≤ mem.size + pad.size := by rw [hpadsz]; omega
    omega

namespace Example
open EvmYul.Venom.Hol.Codegen.Example

/-! ### The MSTORE capstone `m8v`: `entry: %a=CALLVALUE; JMP work` / `work: MSTORE 0 %a; RETURN 0 32`
    at `fnEom = 64`. First memory-writing whole-function capstone; the returndata carries the
    stored callvalue bytes (no callvalue-0 hypothesis, no MUL-by-0). -/

def m8vCv : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def m8vJmp : Instruction := { id := 1, opcode := Opcode.JMP, operands := [Operand.Label "work"], outputs := [] }
def m8vSt : Instruction := { id := 2, opcode := Opcode.MSTORE8, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Var "a"], outputs := [] }
def m8vRet : Instruction := { id := 3, opcode := Opcode.RETURN, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Lit (EvmYul.UInt256.ofNat 32)], outputs := [] }
def m8vEntry : BasicBlock := { label := "entry", instructions := [m8vCv, m8vJmp] }
def m8vWork : BasicBlock := { label := "work", instructions := [m8vSt, m8vRet] }
def m8vFn : IrFunction := { name := "main", blocks := [m8vEntry, m8vWork] }
def m8vCtx : VenomContext := { functions := [m8vFn], entry := some "main" }


abbrev m8vWorkSEnd (s : VenomState) (w : bytes32) : VenomState :=
  { mstore8 (EvmYul.UInt256.ofNat 0).toNat w { s with instIdx := 0 } with instIdx := 1 }

theorem m8vWork_thread (s : VenomState) (w : bytes32) (ha : lookupVar "a" s = some w) :
    execBodyThread [m8vSt] 0 { s with instIdx := 0 } = some (m8vWorkSEnd s w) := by
  have ha' : lookupVar "a" ({ s with instIdx := 0 } : VenomState) = some w := ha
  have hstep : stepInstBase m8vSt { s with instIdx := 0 }
      = ExecResult.OK (mstore8 (EvmYul.UInt256.ofNat 0).toNat w { s with instIdx := 0 }) := by
    show execWrite2 (fun addr val s => mstore8 addr.toNat val s) m8vSt { s with instIdx := 0 } = _
    unfold execWrite2
    simp only [m8vSt, evalOperand, ha']
  show (match stepInstBase m8vSt { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none)
      = some (m8vWorkSEnd s w)
  rw [hstep]; rfl

theorem m8vSt_error (s : VenomState) (ha : lookupVar "a" s = none) :
    stepInstBase m8vSt { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have ha' : lookupVar "a" ({ s with instIdx := 0 } : VenomState) = none := ha
  show execWrite2 (fun addr val s => mstore8 addr.toNat val s) m8vSt { s with instIdx := 0 } = _
  unfold execWrite2
  simp [m8vSt, evalOperand, ha']

abbrev m8vEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }

theorem m8vEntry_thread (s : VenomState) :
    execBodyThread [m8vCv] 0 { s with instIdx := 0 } = some (m8vEntrySEnd s) := by
  have h1 : stepInstBase m8vCv { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  show (match stepInstBase m8vCv { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [] 1 { s' with instIdx := 1 } | _ => none)
      = some (m8vEntrySEnd s)
  rw [h1]; rfl

theorem m8vEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (1 + (j + 1)) m8vCtx m8vEntry s = ExecResult.OK (jumpTo "work" (m8vEntrySEnd s)) :=
  runBlock_body_jmp m8vCtx m8vEntry j [m8vCv] m8vJmp m8vCv [m8vJmp] s (m8vEntrySEnd s) "work"
    rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (m8vEntry_thread s) (by simpa [updateVar] using hnh)

theorem m8vWork_halts (s : VenomState) (j : Nat) (w : bytes32) (ha : lookupVar "a" s = some w) :
    runBlock (1 + (j + 1)) m8vCtx m8vWork s = ExecResult.Halt
      (haltState (setReturndata (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 32).toNat
        (m8vWorkSEnd s w)) (m8vWorkSEnd s w))) :=
  runBlock_body_return m8vCtx m8vWork j [m8vSt] m8vRet m8vSt [m8vRet] s (m8vWorkSEnd s w)
    (Operand.Lit (EvmYul.UInt256.ofNat 0)) (Operand.Lit (EvmYul.UInt256.ofNat 32))
    (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) rfl rfl rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (m8vWork_thread s w ha)

def m8vInv (s : VenomState) : Prop :=
  s.halted = false ∧ (s.currentBb = "work" → ∃ w, lookupVar "a" s = some w)

theorem m8vInv_pres : ∀ bb ∈ m8vFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    m8vInv s → runBlock f' m8vCtx bb s = ExecResult.OK s' → m8vInv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hwork⟩ := hinv
  simp only [m8vFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof m8vCtx m8vEntry 0 [m8vCv] m8vJmp m8vCv [m8vJmp] s
             (m8vEntrySEnd s) rfl rfl (by decide)
             (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
             (m8vEntry_thread s) (by simp)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof m8vCtx m8vEntry 1 [m8vCv] m8vJmp m8vCv [m8vJmp] s
             (m8vEntrySEnd s) rfl rfl (by decide)
             (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
             (m8vEntry_thread s) (by simp)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+2) =>
      rw [show j+2 = 1+(j+1) from by omega, m8vEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      refine ⟨by simpa [jumpTo, updateVar] using hnh, fun _ => ⟨s.callCtx.callvalue, ?_⟩⟩
      show lookupVar "a" (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) = _
      rw [lookupVar_updateVar_self]
  · rcases hla : lookupVar "a" s with _ | w
    · match f' with
      | 0 => rw [runBlock_no_phi 0 m8vCtx m8vWork s m8vSt [m8vRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error m8vCtx m8vWork m8vSt [m8vRet] s "undefined operand" j rfl
          (by decide) (m8vSt_error s hla) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · match f' with
      | 0 => rw [runBlock_no_phi 0 m8vCtx m8vWork s m8vSt [m8vRet] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | 1 => obtain ⟨e, he⟩ := runBlock_oof m8vCtx m8vWork 1 [m8vSt] m8vRet m8vSt [m8vRet] s
               (m8vWorkSEnd s w) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (m8vWork_thread s w hla) (by decide)
             rw [he] at hrun; exact absurd hrun (by simp)
      | (j+2) =>
        rw [show j+2 = 1+(j+1) from by omega, m8vWork_halts s j w hla] at hrun
        exact absurd hrun (by simp)

theorem m8vFn_halts (vs : VenomState) (hnh : vs.halted = false) :
    ∃ vs', runContext 10 m8vCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 m8vCtx vs
      = runBlocks 10 m8vCtx m8vFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, m8vCtx, m8vFn, lookupFunction, fnEntryLabel, m8vEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  set s1 : VenomState := jumpTo "work" (m8vEntrySEnd s0) with hs1
  have hentry : runBlock 9 m8vCtx m8vEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 1 + (7 + 1) from by omega]; exact m8vEntry_runBlock s0 7 hnh0
  have hlk0 : lookupBlock s0.currentBb m8vFn.blocks = some m8vEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 m8vCtx m8vFn s0 = runBlocks 9 m8vCtx m8vFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  have ha1 : lookupVar "a" s1 = some s0.callCtx.callvalue := by
    show lookupVar "a" (updateVar "a" s0.callCtx.callvalue { s0 with instIdx := 0 }) = _
    rw [lookupVar_updateVar_self]
  have hlk1 : lookupBlock s1.currentBb m8vFn.blocks = some m8vWork := rfl
  have hhalt := m8vWork_halts s1 6 s0.callCtx.callvalue ha1
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 1000000 in
/-- **The MSTORE capstone.** `codegen_correct` for `entry: %a=CALLVALUE; JMP work` /
    `work: MSTORE (Lit 0) %a; RETURN (Lit 0) (Lit 32)` at `fnEom = 64`: the callvalue is stored
    to memory and RETURNed — the returndata carries the actual callvalue bytes (no zero-value
    hypothesis). The work block runs fully explicit asm steps, with the RETURN-window coverage
    derived STRUCTURALLY from the write (`byteArray_write_size_window`). -/
theorem codegen_correct_m8vFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 m8vCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ m8vFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [m8vFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [m8vEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [m8vWork, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan m8vFn 64 0
      = some ((generateFnPlan m8vFn 64 0).get!.1, (generateFnPlan m8vFn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel m8vFn) m8vFn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv m8vInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel m8vFn) m8vFn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2)
    (fuel := 10) (ctx := m8vCtx) (fn := m8vFn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan m8vFn 64 0).get!.1) (psFinal := (generateFnPlan m8vFn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ m8vInv_pres ?_
    ⟨by simpa using hvshalt, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [m8vFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, m8vEntry, m8vCv]
    · simp [runBlock, evalPhis, execBlock, m8vWork, m8vSt]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [m8vFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [m8vCv], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof m8vCtx m8vEntry 1 [m8vCv] m8vJmp m8vCv [m8vJmp] s
               (m8vEntrySEnd s) rfl rfl (by decide) hnt (m8vEntry_thread s) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([m8vCv] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [m8vCv]) (jmpInst := m8vJmp) (hd := m8vCv) (tl := [m8vJmp])
        (nextLiveness := ["a"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 64) (lbl := "work") (off := 6) (bb' := m8vWork) (sEnd := m8vEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := m8vEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide), trivial⟩)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by decide) (hlk' := rfl)
        (hw := by decide))
    · have hlbl : s.currentBb = "work" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, hwork⟩ := hinv
      obtain ⟨wa, ha⟩ := hwork hlbl
      have hpcw : asm.pc = 4 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof m8vCtx m8vWork 1 [m8vSt] m8vRet m8vSt [m8vRet] s
               (m8vWorkSEnd s wa) rfl rfl (by decide)
               (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
               (m8vWork_thread s wa ha) (by decide))
      | (j+1) =>
      rw [show j+1+1 = ([m8vSt] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psW := psOfFn (fnPlanFuel m8vFn) m8vFn 64 0 "work" with hpsW
      have hpsWstack : psW.stack = [Operand.Var "a"] := rfl
      have hpsWspill : ∀ op, alookup' psW.spilled op = none := fun _ => rfl
      set prog := (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2 with ho2pcdef
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "work"]) := by
        rw [hpcw]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psW { s with instIdx := 0 } asm prog "work" hvrel hbL
      have hpcA : as1.pc = 5 := by
        rw [show (executePlan [StackOp.SOLabel "work"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpcw]
      have hbP0 : asmBlockAt prog as1.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emitOneInput_sim_lit_append (opc := Opcode.MSTORE8)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel1 hbP0
      have hpcB : as2.pc = 6 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      have hva : operandVal ({ s with instIdx := 0 } : VenomState) lo (Operand.Var "a") = some wa := ha
      have hstack2 : as2.stack = (EvmYul.UInt256.ofNat 0) :: wa :: as2.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "a")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel2 (base := ([] : List Operand)) ?_ hva rfl
        show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack = _
        rw [hpsWstack]; rfl
      obtain ⟨hmst, hrel3⟩ := asmMstore8_noSpill_rel (lo := lo)
        (ps := { psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] })
        (vs := { s with instIdx := 0 }) (as := as2)
        hrel2 hstack2 (fun op => hpsWspill op)
        (Nat.zero_le _) (Nat.zero_le _)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      have hltB : as2.pc < prog.length := by rw [hpcB]; decide
      have hgetB : prog.get ⟨as2.pc, hltB⟩ = AsmInst.AsmOp "MSTORE8" := by
        conv_lhs => rw [show (⟨as2.pc, hltB⟩ : Fin _) = ⟨6, by decide⟩ from Fin.ext hpcB]
        rfl
      have hstep3 : asmStep o2pc prog as2 = asmMstore8 as2 := asmStep_mstore8_ok hltB hgetB
      set as3 : AsmState := { asmNext as2 with
          stack := as2.stack.drop 2,
          memory := (⟨#[UInt8.ofNat (wa.toNat % 256)]⟩ : ByteArray).write 0
            (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 1) as2.memory)
            (EvmYul.UInt256.ofNat 0).toNat 1 } with has3
      have hstep3ok : asmStep o2pc prog as2 = AsmResult.AsmOK as3 := by rw [hstep3, hmst]
      have hrun3 : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
        rw [runAsm_succ_ok hltB hstep3ok]; rfl
      have hpcC : as3.pc = 7 := by rw [has3]; show as2.pc + 1 = 7; rw [hpcB]
      have hcov3 : 32 ≤ as3.memory.size := by
        have hexp : 32 ≤ (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 1) as2.memory).size := by
          have := asmExpandMemory_size_rounded ((EvmYul.UInt256.ofNat 0).toNat + 1) as2.memory
            (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
          rw [show (((EvmYul.UInt256.ofNat 0).toNat + 1 + 31) / 32) * 32 = 32 from rfl] at this
          exact this
        have hw := EvmYul.byteArray_write_size (⟨#[UInt8.ofNat (wa.toNat % 256)]⟩ : ByteArray)
          (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 1) as2.memory) (EvmYul.UInt256.ofNat 0).toNat
        have h1 : (⟨#[UInt8.ofNat (wa.toNat % 256)]⟩ : ByteArray).size = 1 := rfl
        rw [h1] at hw
        rw [has3]
        exact le_trans hexp hw
      have hrel3' : venomAsmRel lo { psW with stack := ([] : List Operand) } (m8vWorkSEnd s wa) as3 := by
        have hpop : ({ psW with stack := stackPop 2 ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack } : PlanState)
            = { psW with stack := ([] : List Operand) } := by
          rw [show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack
            = [Operand.Var "a", Operand.Lit (EvmYul.UInt256.ofNat 0)] from by rw [hpsWstack]; rfl]
          rfl
        have h := hrel3
        rw [show ({ psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState) = { psW with stack := psW.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } from rfl] at h
        exact hpop ▸ h
      have hbP32 : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4a⟩ := emitOneInput_sim_lit_append (opc := Opcode.RETURN)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 32) hrel3' hbP32
      have hpcD : as4.pc = 8 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length = 1 from rfl] at hpc4a
        rw [hpc4a, hpcC]
      have hbP0b : asmBlockAt prog as4.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcD]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as5, hrun5, hrel5, hpc5a⟩ := emitOneInput_sim_lit_append (opc := Opcode.RETURN)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel4 hbP0b
      have hpcE2 : as5.pc = 9 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc5a
        rw [hpc5a, hpcD]
      have htop5 : as5.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 32) :: as5.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Lit (EvmYul.UInt256.ofNat 32))
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel5 (base := ([] : List Operand)) ?_ rfl rfl
        rfl
      have hcov5 : 32 ≤ as5.memory.size :=
        le_trans hcov3 (le_trans (runAsm_memory_size_mono hrun4) (runAsm_memory_size_mono hrun5))
      have hrunAll : runAsm (1 + 1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as5 := by
        have hrun1' : runAsm 1 o2pc prog asm = AsmResult.AsmOK as1 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOLabel "work"]).length from rfl]; exact hrun1
        have hrun2' : runAsm 1 o2pc prog as1 = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun2
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length from rfl]; exact hrun4
        have hrun5' : runAsm 1 o2pc prog as4 = AsmResult.AsmOK as5 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun5
        exact runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose hrun1' hrun2') hrun3) hrun4') hrun5'
      have hterm := termRecipeW_return_of_body (front := [m8vSt]) (retInst := m8vRet) (hd := m8vSt)
        (tl := [m8vRet]) (restFuel := j)
        (offOp := Operand.Lit (EvmYul.UInt256.ofNat 0)) (szOp := Operand.Lit (EvmYul.UInt256.ofNat 32))
        (off := EvmYul.UInt256.ofNat 0) (sz := EvmYul.UInt256.ofNat 32) (rest := as5.stack.drop 2)
        (bodyLen := 5) (bb := m8vWork) (ctx := m8vCtx) (prog := prog) (o2pc := o2pc)
        (as' := as5) (fn := m8vFn) (lo := lo) (s := s)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel m8vFn) m8vFn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan m8vFn 64 0).get!.1)).2)
        rfl rfl rfl rfl rfl rfl (by decide)
        (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (m8vWork_thread s wa ha) hrel5 (by decide)
        (by rw [hpcE2]; decide)
        (by conv_lhs => rw [show (⟨as5.pc, by rw [hpcE2]; decide⟩ : Fin _) = ⟨9, by decide⟩
              from Fin.ext hpcE2]
            rfl)
        htop5
        (Or.inr (by
          rw [show ((EvmYul.UInt256.ofNat 0).toNat + (EvmYul.UInt256.ofNat 32).toNat + 31) / 32 * 32
            = 32 from by rfl]
          exact hcov5))
        (by decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      exact ⟨as5, _, m8vWorkSEnd s wa, 5, hrunAll, hterm⟩
  case _ =>
    refine ⟨⟨m8vEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel m8vFn) m8vFn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan m8vFn 64 0).get!.1)).1.length
      omega
end Example


/-! ## The SHA3 capstone: duplicate-literal reorder (`SWAP1`) + covered `emit_sha3_sim` -/

/-- `SWAP1` of two equal top values is the identity on the stack (pc advances). The
    duplicate-literal reorder emits exactly this shape. -/
theorem asmSwap1_top2_eq {st : AsmState} {v : bytes32} {r : List bytes32}
    (h : st.stack = v :: v :: r) :
    asmSwap 1 st = AsmResult.AsmOK ({ asmNext st with stack := st.stack }) := by
  have hlen : 1 < st.stack.length := by rw [h]; simp
  unfold asmSwap
  rw [dif_pos (by norm_num : (0:Nat) < 1), dif_pos hlen]
  dsimp only
  have hget : st.stack.get ⟨1, hlen⟩ = v := by
    rw [List.get_eq_getElem]
    simp [h]
  have hhead : st.stack.head?.getD (EvmYul.UInt256.ofNat 0) = v := by simp [h]
  rw [hget, hhead]
  have hset : (st.stack.set 0 v).set 1 v = st.stack := by
    rw [h]; rfl
  rw [hset]

/-- The `n = 0` base case of the WF-recursive `encodeNumBytes` as a rewrite bridge — its
    equation lemmas fire under `unfold` even though kernel `whnf`/`decide` are stuck on it. -/
theorem encodeNumBytes_zero : encodeNumBytes 0 = [] := by unfold encodeNumBytes; simp

namespace Example

/-! ### The SHA3 capstone `sh3`: `entry: %a=CV; %b=CV; %c=SHA3 (Lit 0)(Lit 0); JMP next` /
    `next = r0Next` (MUL-by-0 kill) at `fnEom = 64`. -/

def sh3CvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def sh3CvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def sh3Sha : Instruction := { id := 2, opcode := Opcode.SHA3, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Lit (EvmYul.UInt256.ofNat 0)], outputs := ["c"] }
def sh3Jmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def sh3Entry : BasicBlock := { label := "entry", instructions := [sh3CvA, sh3CvB, sh3Sha, sh3Jmp] }
def sh3Fn : IrFunction := { name := "main", blocks := [sh3Entry, r0Next] }
def sh3Ctx : VenomContext := { functions := [sh3Fn], entry := some "main" }

/-- The SHA3 read value: hash of the (zero-padded) first 32 memory bytes. Pure in the state's
    memory, so invariant under `updateVar` / `jumpTo` / `instIdx`. -/
abbrev sh3Val (s : VenomState) : bytes32 :=
  keccak256 (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 0).toNat s)

abbrev sh3EntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (sh3Val s) { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem sh3Entry_thread (s : VenomState) :
    execBodyThread [sh3CvA, sh3CvB, sh3Sha] 0 { s with instIdx := 0 } = some (sh3EntrySEnd s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hfv : sh3Val S2 = sh3Val s := rfl
  have hsub : stepInstBase sh3Sha S2 = ExecResult.OK (updateVar "c" (sh3Val s) S2) := by
    show stepInstBase sh3Sha S2 = _
    rw [show stepInstBase sh3Sha S2
      = ExecResult.OK (updateVar "c" (sh3Val S2) S2) from rfl, hfv]
  have h1 : stepInstBase sh3CvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase sh3CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase sh3CvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [sh3CvB, sh3Sha] 1 { s' with instIdx := 1 } | _ => none)
      = some (sh3EntrySEnd s)
  rw [h1]
  show (match stepInstBase sh3CvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [sh3Sha] 2 { s' with instIdx := 2 } | _ => none)
      = some (sh3EntrySEnd s)
  rw [h2]
  show (match stepInstBase sh3Sha S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none)
      = some (sh3EntrySEnd s)
  rw [hsub]; rfl

theorem sh3Entry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) sh3Ctx sh3Entry s = ExecResult.OK (jumpTo "next" (sh3EntrySEnd s)) :=
  runBlock_body_jmp sh3Ctx sh3Entry j [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA [sh3CvB, sh3Sha, sh3Jmp] s
    (sh3EntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (sh3Entry_thread s) (by simpa [updateVar] using hnh)

theorem sh3EntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (sh3EntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (sh3EntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (sh3EntrySEnd s) = some (sh3Val s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (sh3Val s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (sh3Val s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (sh3Val s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

theorem sh3Next_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) sh3Ctx r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return sh3Ctx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem sh3Next_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) sh3Ctx r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term sh3Ctx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

def sh3Inv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (sh3Val s))

theorem sh3Inv_pres : ∀ bb ∈ sh3Fn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    sh3Inv s → runBlock f' sh3Ctx bb s = ExecResult.OK s' → sh3Inv s' := by
  intro bb hbb s s' f' hinv hrun
  obtain ⟨hnh, hcv, _⟩ := hinv
  simp only [sh3Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [sh3CvA, sh3CvB, sh3Sha], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx sh3Entry 0 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
             [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx sh3Entry 1 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
             [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx sh3Entry 2 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
             [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx sh3Entry 3 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
             [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, sh3Entry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := sh3EntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv], fun _ => ⟨ha0, hb0, ?_⟩⟩
      rw [show lookupVar "c" (jumpTo "next" (sh3EntrySEnd s)) = lookupVar "c" (sh3EntrySEnd s) from rfl, hc0]
      rfl
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 sh3Ctx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error sh3Ctx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 sh3Ctx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error sh3Ctx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 sh3Ctx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, sh3Next_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 sh3Ctx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof sh3Ctx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, sh3Next_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem sh3Fn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 sh3Ctx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 sh3Ctx vs
      = runBlocks 10 sh3Ctx sh3Fn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, sh3Ctx, sh3Fn, lookupFunction, fnEntryLabel, sh3Entry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (sh3EntrySEnd s0) with hs1
  have hentry : runBlock 9 sh3Ctx sh3Entry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact sh3Entry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb sh3Fn.blocks = some sh3Entry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 sh3Ctx sh3Fn s0 = runBlocks 9 sh3Ctx sh3Fn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := sh3EntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (sh3Val s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (sh3EntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb sh3Fn.blocks = some r0Next := rfl
  have hhalt := sh3Next_halts s1 6 (EvmYul.UInt256.ofNat 0) (sh3Val s0) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

theorem sh3Next_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg sh3Fn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := sh3Fn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))


/-- The **unresolved** sh3 asm program as a stuck-preserving literal: `rfl` succeeds because
    both sides carry the same stuck `encodeNumBytes 0` payloads; rewriting by `encodeNumBytes_zero` then
    yields an all-structural list on which `buildOffsetToPc` lookups `decide` (the o2pc keys
    accumulate `asmInstSize` over these pushes, so key 11 is otherwise kernel-stuck). -/
theorem sh3_unresolved :
    executePlan (generateFnPlan sh3Fn 64 0).get!.1
      = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
         AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmPush (encodeNumBytes 0),
         AsmInst.AsmOp "SWAP1", AsmInst.AsmOp "SHA3", AsmInst.AsmPushLabel "next",
         AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL",
         AsmInst.AsmOp "RETURN"] := rfl

/-- **The SHA3 capstone.** `codegen_correct` for `entry: %a=CV; %b=CV; %c=SHA3 (Lit 0)(Lit 0);
    JMP next` / `next: %e=MUL %b %c; RETURN %e %a` at `fnEom = 64`. The keccak output is real
    (`c = keccak256` of the empty slice at offset 0, equal on both sides — the size-0 window
    makes the covered `emit_sha3_sim` apply with a trivial coverage bound) and is killed by the
    MUL-by-0 successor. The entry block's asm run is fully explicit — the duplicate-literal
    input plan emits a `SWAP1` (`reorderPlan` `doSwap`s equal targets), which the generic fold
    slices don't model. -/
theorem codegen_correct_sh3Fn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 sh3Ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ sh3Fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [sh3Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [sh3Entry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan sh3Fn 64 0
      = some ((generateFnPlan sh3Fn 64 0).get!.1, (generateFnPlan sh3Fn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_inv sh3Inv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2)
    (fuel := 10) (ctx := sh3Ctx) (fn := sh3Fn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan sh3Fn 64 0).get!.1) (psFinal := (generateFnPlan sh3Fn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ sh3Inv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [sh3Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, sh3Entry, sh3CvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [sh3Fn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: fully explicit — label, CV, CV, PUSH 32, PUSH 0, SHA3, then the JMP handoff
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [sh3CvA, sh3CvB, sh3Sha], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof sh3Ctx sh3Entry 1 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
               [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof sh3Ctx sh3Entry 2 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
               [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof sh3Ctx sh3Entry 3 [sh3CvA, sh3CvB, sh3Sha] sh3Jmp sh3CvA
               [sh3CvB, sh3Sha, sh3Jmp] s (sh3EntrySEnd s) rfl rfl (by decide) hnt (sh3Entry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([sh3CvA, sh3CvB, sh3Sha] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psE := initPlanState 64 with hpsEdef
      set prog := (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2 with ho2pcdef
      have hvrel0 : venomAsmRel lo psE { s with instIdx := 0 } asm := by
        rw [hpsE] at hvrel; exact hvrel
      -- 1: label
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "entry"]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psE { s with instIdx := 0 } asm prog "entry" hvrel0 hbL
      have hpcA : as1.pc = 1 := by
        rw [show (executePlan [StackOp.SOLabel "entry"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpc0]
      -- 2: CALLVALUE → a
      have hbC1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield1 : (fun (a : AsmState) => a.callCtx.callvalue) as1
          = (fun (v : VenomState) => v.callCtx.callvalue) ({ s with instIdx := 0 } : VenomState) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel1
        show as1.callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "a")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel1 (by decide) rfl hbC1 (fun h hg => asmStep_callvalue_ok h hg) hfield1
      have hpcB : as2.pc = 2 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      -- 3: CALLVALUE → b
      have hbC2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcB]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield2 : (fun (a : AsmState) => a.callCtx.callvalue) as2
          = (fun (v : VenomState) => v.callCtx.callvalue)
              (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 }) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel2
        show as2.callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as3, hrun3, hrel3, hpc3⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "b")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel2 (by decide) rfl hbC2 (fun h hg => asmStep_callvalue_ok h hg) hfield2
      have hpcC : as3.pc = 3 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc3
        rw [hpc3, hpcB]
      -- 4/5: PUSH 32 ; PUSH 0
      have hbP32 : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emitOneInput_sim_lit_append (opc := Opcode.SHA3)
        (nl := (["e", "a"] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel3 hbP32
      have hpcD : as4.pc = 4 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc4
        rw [hpc4, hpcC]
      have hbP0 : asmBlockAt prog as4.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcD]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as5, hrun5, hrel5, hpc5⟩ := emitOneInput_sim_lit_append (opc := Opcode.SHA3)
        (nl := (["e", "a"] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel4 hbP0
      have hpcE2 : as5.pc = 5 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc5
        rw [hpc5, hpcD]
      -- 6: SHA3
      have htop5 : as5.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 0) :: as5.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Lit (EvmYul.UInt256.ofNat 0))
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel5
          (base := [Operand.Var "a", Operand.Var "b"]) ?_ rfl rfl
        rfl
      -- the duplicate-lit reorder emits a (value-trivial) SWAP1 of the two equal zeros
      have hltW : as5.pc < prog.length := by rw [hpcE2]; decide
      have hgetW : prog.get ⟨as5.pc, hltW⟩ = AsmInst.AsmOp "SWAP1" := by
        conv_lhs => rw [show (⟨as5.pc, hltW⟩ : Fin _) = ⟨5, by decide⟩ from Fin.ext hpcE2]
        rfl
      have hstepW : asmStep o2pc prog as5 = asmSwap 1 as5 := by
        unfold asmStep; rw [dif_pos hltW, hgetW]; rfl
      have hswapEq : asmSwap 1 as5 = AsmResult.AsmOK ({ asmNext as5 with stack := as5.stack }) :=
        asmSwap1_top2_eq htop5
      set as5w : AsmState := { asmNext as5 with stack := as5.stack } with has5w
      have hrunW : runAsm 1 o2pc prog as5 = AsmResult.AsmOK as5w := by
        rw [runAsm_succ_ok hltW (by rw [hstepW, hswapEq])]; rfl
      have hpcW : as5w.pc = 6 := by rw [has5w]; show as5.pc + 1 = 6; rw [hpcE2]
      have hbS : asmBlockAt prog as5w.pc (executePlan [StackOp.SOEmit "SHA3"]) := by
        rw [hpcW]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have htop5w : as5w.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 0) :: as5w.stack.drop 2 := by
        rw [has5w]; exact htop5
      have hrel5w : venomAsmRel lo _ _ as5w := hrel5
      obtain ⟨as6, hrun6, hrel6, hpc6⟩ := emit_sha3_sim (out := "c") hrel5w htop5w
        (by exact Nat.zero_le _) (by decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide)) (by decide) rfl hbS
        (fun h hg => asmStep_sha3_ok h hg)
      have hpc6' : as6.pc = 7 := by
        rw [show (executePlan [StackOp.SOEmit "SHA3"]).length = 1 from rfl] at hpc6
        rw [hpc6, hpcW]
      have hrunAll := runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose
        hrun1 hrun2) hrun3) hrun4) hrun5) hrunW) hrun6
      have hrunAll6 : runAsm 7 o2pc prog asm = AsmResult.AsmOK as6 := hrunAll
      have hterm := termRecipeW_jmp_of_body (bb := sh3Entry) (bb' := r0Next) (lbl := "next")
        (off := 11) (bodyLen := 7) (ctx := sh3Ctx) (prog := prog) (o2pc := o2pc)
        (fn := sh3Fn) (lo := lo) (s := s) (as' := as6)
        (front := [sh3CvA, sh3CvB, sh3Sha]) (jmpInst := sh3Jmp) (hd := sh3CvA)
        (tl := [sh3CvB, sh3Sha, sh3Jmp]) (restFuel := j)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2)
        rfl rfl rfl rfl (by decide) hnt (sh3Entry_thread s)
        (by simpa [updateVar] using hhalt)
        hrel6 rfl (by decide)
        (by rw [hpc6']; decide)
        (by conv_lhs => rw [show (⟨as6.pc, by rw [hpc6']; decide⟩ : Fin _) = ⟨7, by decide⟩
              from Fin.ext hpc6']
            rfl)
        (by have hlit := sh3_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [hlit]
            decide)
        (by decide)
        (by rw [hpc6']; decide)
        (by conv_lhs => rw [show (⟨as6.pc + 1, by rw [hpc6']; decide⟩ : Fin _) = ⟨8, by decide⟩
              from Fin.ext (show as6.pc + 1 = 8 by omega)]
            rfl)
        (by rw [ho2pcdef, hprogdef,
              show pcOfLabel (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 "next" = 9 from rfl]
            have hlit := sh3_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [show (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).2
                = buildOffsetToPc (executePlan (generateFnPlan sh3Fn 64 0).get!.1) from rfl, hlit]
            decide) rfl
      exact ⟨as6, _, sh3EntrySEnd s, 7, hrunAll6, hterm⟩
    · -- next: the r0 pattern (MUL-by-0 kill + empty RETURN window) at pc 8, fnEom 64
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc9 : asm.pc = 9 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof sh3Ctx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sh3Val s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sh3Val s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sh3Val s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (sh3Val s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (sh3Val s)).2]; exact ha0)
        (hready := sh3Next_ready)
        (hsd := ⟨by intro op'; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc9]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc9]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc9]; decide) (hret := by simp only [hpc9]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨sh3Entry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel sh3Fn) sh3Fn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan sh3Fn 64 0).get!.1)).1.length
      omega

end Example


/-! ## The MLOAD capstone: load-after-store through the expanding no-hcov MLOAD relation -/

/-- Window reads are invariant under `asmExpandMemory` (pointwise from
    `readByte_asmExpandMemory` via `readWithPadding_congr`). -/
theorem readWithPadding_asmExpandMemory (a len n : Nat) (mem : ByteArray)
    (hlen : len < USize.size) (hro : ((n + 31) / 32) * 32 < USize.size) :
    (asmExpandMemory n mem).readWithPadding a len = mem.readWithPadding a len := by
  apply ByteArray.readWithPadding_congr _ _ a len hlen
  intro k hk
  have h := readByte_asmExpandMemory (a + k) n mem hro
  rw [readByte_eq_getElem?_getD, readByte_eq_getElem?_getD] at h
  exact h

/-- **The expanding no-spill MLOAD step + relation** — `venomAsmRel_mload` for an asm memory
    that need NOT cover the window: `asmMload` expands first, and both the loaded value and
    `memoryRel` survive because expansion is read-invariant. `planSpillRel` is vacuous under
    `noSpill`. The 1-input read sibling of the expanding SHA3 relation. -/
theorem asmMload_expand_noSpill_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {out : String} {offset : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = offset :: rest)
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hbelow : offset.toNat + 32 ≤ ps.alloc.fnEom)
    (hro : ((offset.toNat + 32 + 31) / 32) * 32 < USize.size)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack) :
    asmMload as = AsmResult.AsmOK ({ asmNext as with stack := wordOfBytes ((asmExpandMemory (offset.toNat + 32) as.memory).readWithPadding offset.toNat 32) :: rest, memory := asmExpandMemory (offset.toNat + 32) as.memory })
    ∧ venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 1 ps.stack) }
        (updateVar out (mload offset.toNat vs) vs)
        ({ asmNext as with stack := wordOfBytes ((asmExpandMemory (offset.toNat + 32) as.memory).readWithPadding offset.toNat 32) :: rest, memory := asmExpandMemory (offset.toNat + 32) as.memory }) := by
  have hreadE : (asmExpandMemory (offset.toNat + 32) as.memory).readWithPadding offset.toNat 32
      = as.memory.readWithPadding offset.toNat 32 :=
    readWithPadding_asmExpandMemory offset.toNat 32 (offset.toNat + 32) as.memory
      (by rcases USize.size_eq with h | h <;> (rw [h]; norm_num)) hro
  constructor
  · simp only [asmMload, hstack]
  · obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
    have hread : vs.memory.readWithPadding offset.toNat 32
        = as.memory.readWithPadding offset.toNat 32 :=
      memoryRel_readWithPadding_slice hMem hbelow
        (by rcases USize.size_eq with h | h <;> (rw [h]; norm_num))
    have hval : mload offset.toNat vs
        = wordOfBytes ((asmExpandMemory (offset.toNat + 32) as.memory).readWithPadding offset.toNat 32) := by
      simp only [mload, readMemory, hread, hreadE]
    have hlen1 : 1 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
    have hspill' : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hnospill _
    obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
      venomAsmRel_updateVar lo ps vs as out (mload offset.toNat vs)
        ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill'
    refine ⟨?_, ?_, ?_, hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
    · -- planStackRel: pop 1, push the fresh out bound to the loaded word
      have hout : operandVal (updateVar out (mload offset.toNat vs) vs) lo (Operand.Var out)
          = some (wordOfBytes ((asmExpandMemory (offset.toNat + 32) as.memory).readWithPadding offset.toNat 32)) := by
        simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
      have hps := planStackRel_unop hStk' hlen1 hout
      rw [hstack] at hps
      simpa using hps
    · -- planSpillRel: vacuous under noSpill
      intro op off' hlook
      rw [show AssocList.lookup Operand Nat ps.spilled op = alookup' ps.spilled op from rfl,
          hnospill op] at hlook
      exact absurd hlook (by simp)
    · -- memoryRel: venom memory unchanged; asm expansion is readByte-invariant
      intro i hi
      show readByte i vs.memory = readByte i (asmExpandMemory (offset.toNat + 32) as.memory)
      rw [readByte_asmExpandMemory i _ as.memory hro]
      exact hMem i hi

namespace Example

/-! ### The MLOAD capstone `mld`: `entry: %a=CV; %b=CV; %d=CV; JMP st` /
    `st: MSTORE (Lit 0) %d; %c=MLOAD (Lit 0); JMP next` / `next = r0Next` (MUL-by-0 kill)
    at `fnEom = 64`. The load reads back through the store's own window. -/

def mldCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def mldCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def mldCvD : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["d"] }
def mldJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "st"], outputs := [] }
def mldStore : Instruction := { id := 4, opcode := Opcode.MSTORE, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Var "d"], outputs := [] }
def mldLoad : Instruction := { id := 5, opcode := Opcode.MLOAD, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0)], outputs := ["c"] }
def mldJmp2 : Instruction := { id := 6, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def mldEntry : BasicBlock := { label := "entry", instructions := [mldCvA, mldCvB, mldCvD, mldJmp] }
def mldSt : BasicBlock := { label := "st", instructions := [mldStore, mldLoad, mldJmp2] }
def mldFn : IrFunction := { name := "main", blocks := [mldEntry, mldSt, r0Next] }
def mldCtx : VenomContext := { functions := [mldFn], entry := some "main" }

/-- The loaded value as a function of the CURRENT state's memory (invariant under
    `updateVar` / `jumpTo` / `instIdx`, so it can live inside the invariant). -/
abbrev mldCVal (s : VenomState) : bytes32 := mload (EvmYul.UInt256.ofNat 0).toNat s

abbrev mldEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "d" s.callCtx.callvalue { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem mldEntry_thread (s : VenomState) :
    execBodyThread [mldCvA, mldCvB, mldCvD] 0 { s with instIdx := 0 } = some (mldEntrySEnd s) := rfl

theorem mldEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) mldCtx mldEntry s = ExecResult.OK (jumpTo "st" (mldEntrySEnd s)) :=
  runBlock_body_jmp mldCtx mldEntry j [mldCvA, mldCvB, mldCvD] mldJmp mldCvA [mldCvB, mldCvD, mldJmp] s
    (mldEntrySEnd s) "st" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (mldEntry_thread s) (by simpa [updateVar] using hnh)

theorem mldEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (mldEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (mldEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "d" (mldEntrySEnd s) = some s.callCtx.callvalue := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "d" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- entry's body `[CV a; CV b; CV d]` as a `RegularBodyH`: three `cv_step`s. -/
theorem mldEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "d"] offsetToPc
      (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 1 [mldCvA, mldCvB, mldCvD] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
   cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide),
   cv_step (out := "d") (S := ["a", "b"]) rfl (by decide) (by decide), trivial⟩

abbrev mldSt1 (s : VenomState) (wd : bytes32) : VenomState :=
  { mstore (EvmYul.UInt256.ofNat 0).toNat wd { s with instIdx := 0 } with instIdx := 1 }

abbrev mldStSEnd (s : VenomState) (wd : bytes32) : VenomState :=
  { updateVar "c" (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) (mldSt1 s wd) with instIdx := 2 }

theorem mldSt_thread (s : VenomState) (wd : bytes32) (hd : lookupVar "d" s = some wd) :
    execBodyThread [mldStore, mldLoad] 0 { s with instIdx := 0 } = some (mldStSEnd s wd) := by
  have hd' : lookupVar "d" ({ s with instIdx := 0 } : VenomState) = some wd := hd
  have hstep1 : stepInstBase mldStore { s with instIdx := 0 }
      = ExecResult.OK (mstore (EvmYul.UInt256.ofNat 0).toNat wd { s with instIdx := 0 }) := by
    show execWrite2 (fun addr val s => mstore addr.toNat val s) mldStore { s with instIdx := 0 } = _
    unfold execWrite2
    simp only [mldStore, evalOperand, hd']
  have hstep2 : stepInstBase mldLoad (mldSt1 s wd)
      = ExecResult.OK (updateVar "c" (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) (mldSt1 s wd)) := rfl
  show (match stepInstBase mldStore { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [mldLoad] 1 { s' with instIdx := 1 } | _ => none)
      = some (mldStSEnd s wd)
  rw [hstep1]
  show (match stepInstBase mldLoad (mldSt1 s wd) with
        | ExecResult.OK s' => execBodyThread [] 2 { s' with instIdx := 2 } | _ => none)
      = some (mldStSEnd s wd)
  rw [hstep2]; rfl

theorem mldSt_runBlock (s : VenomState) (j : Nat) (wd : bytes32) (hnh : s.halted = false)
    (hd : lookupVar "d" s = some wd) :
    runBlock (2 + (j + 1)) mldCtx mldSt s = ExecResult.OK (jumpTo "next" (mldStSEnd s wd)) :=
  runBlock_body_jmp mldCtx mldSt j [mldStore, mldLoad] mldJmp2 mldStore [mldLoad, mldJmp2] s
    (mldStSEnd s wd) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (mldSt_thread s wd hd) (by simpa [updateVar, mstore, writeMemoryWithExpansion] using hnh)

theorem mldSt_error (s : VenomState) (hd : lookupVar "d" s = none) :
    stepInstBase mldStore { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hd' : lookupVar "d" ({ s with instIdx := 0 } : VenomState) = none := hd
  show execWrite2 (fun addr val s => mstore addr.toNat val s) mldStore { s with instIdx := 0 } = _
  unfold execWrite2
  simp [mldStore, evalOperand, hd']

theorem mldStSEnd_lookup (s : VenomState) (wd : bytes32) :
    lookupVar "a" (mldStSEnd s wd) = lookupVar "a" s
    ∧ lookupVar "b" (mldStSEnd s wd) = lookupVar "b" s
    ∧ lookupVar "c" (mldStSEnd s wd) = some (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) (mldSt1 s wd)) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    rfl
  · show lookupVar "b" (updateVar "c" (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) (mldSt1 s wd)) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    rfl
  · show lookupVar "c" (updateVar "c" (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s wd)) (mldSt1 s wd)) = _
    rw [lookupVar_updateVar_self]

theorem mldNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) mldCtx r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return mldCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem mldNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) mldCtx r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term mldCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

def mldInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "st" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                      ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                      ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (mldCVal s))

theorem mldInv_pres : ∀ bb ∈ mldFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mldInv s → runBlock f' mldCtx bb s = ExecResult.OK s' → s.currentBb = bb.label → mldInv s' := by
  intro bb hbb s s' f' hinv hrun hcur
  obtain ⟨hnh, hcv, hst, _⟩ := hinv
  simp only [mldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · have hnt : ∀ inst ∈ [mldCvA, mldCvB, mldCvD], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof mldCtx mldEntry 0 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
             [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof mldCtx mldEntry 1 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
             [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof mldCtx mldEntry 2 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
             [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof mldCtx mldEntry 3 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
             [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, mldEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hd0⟩ := mldEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hd0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        fun _ => ⟨ha0, hb0, hd0⟩, fun h => by simp [jumpTo] at h⟩
  · match f' with
    | 0 => rw [runBlock_no_phi 0 mldCtx mldSt s mldStore [mldLoad, mldJmp2] rfl (by decide)] at hrun
           simp [execBlock] at hrun
    | 1 =>
      rcases hld : lookupVar "d" s with _ | wd
      · rw [runBlock_body_head_error mldCtx mldSt mldStore [mldLoad, mldJmp2] s "undefined operand" 0 rfl
          (by decide) (mldSt_error s hld) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
      · obtain ⟨e, he⟩ := runBlock_oof mldCtx mldSt 1 [mldStore, mldLoad] mldJmp2 mldStore
          [mldLoad, mldJmp2] s (mldStSEnd s wd) rfl rfl (by decide)
          (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> decide)
          (mldSt_thread s wd hld) (by decide)
        rw [he] at hrun; exact absurd hrun (by simp)
    | 2 =>
      rcases hld : lookupVar "d" s with _ | wd
      · rw [runBlock_body_head_error mldCtx mldSt mldStore [mldLoad, mldJmp2] s "undefined operand" 1 rfl
          (by decide) (mldSt_error s hld) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
      · obtain ⟨e, he⟩ := runBlock_oof mldCtx mldSt 2 [mldStore, mldLoad] mldJmp2 mldStore
          [mldLoad, mldJmp2] s (mldStSEnd s wd) rfl rfl (by decide)
          (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> decide)
          (mldSt_thread s wd hld) (by decide)
        rw [he] at hrun; exact absurd hrun (by simp)
    | (j+3) =>
      obtain ⟨ha0, hb0, hd0⟩ := hst hcur
      rw [show j+3 = 2+(j+1) from by omega, mldSt_runBlock s j (EvmYul.UInt256.ofNat 0) hnh hd0] at hrun
      injection hrun with h; subst h
      obtain ⟨haL, hbL, hcL⟩ := mldStSEnd_lookup s (EvmYul.UInt256.ofNat 0)
      refine ⟨by simpa [jumpTo, updateVar, mstore, writeMemoryWithExpansion] using hnh,
        by simp [jumpTo, updateVar, mstore, writeMemoryWithExpansion, hcv],
        fun h => by simp [jumpTo] at h, fun _ => ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · show lookupVar "a" (mldStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [haL]; exact ha0
      · show lookupVar "b" (mldStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [hbL]; exact hb0
      · show lookupVar "c" (mldStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [hcL]; rfl
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 mldCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error mldCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 mldCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error mldCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mldCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mldCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mldNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mldCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mldCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mldNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem mldNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg mldFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := mldFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

/-- The **unresolved** mld asm program as a stuck-preserving literal (same trick as
    `sh3_unresolved`): late label keys (st at byte 8 is fine, next at byte 17 is not)
    accumulate `asmInstSize` over the two `AsmPush (encodeNumBytes 0)`s and stick. -/
theorem mld_unresolved :
    executePlan (generateFnPlan mldFn 64 0).get!.1
      = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
         AsmInst.AsmOp "CALLVALUE", AsmInst.AsmPushLabel "st", AsmInst.AsmOp "JUMP",
         AsmInst.AsmLabel "st", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "MSTORE",
         AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "MLOAD", AsmInst.AsmPushLabel "next",
         AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL",
         AsmInst.AsmOp "RETURN"] := rfl

theorem mldFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 mldCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 mldCtx vs
      = runBlocks 10 mldCtx mldFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, mldCtx, mldFn, lookupFunction, fnEntryLabel, mldEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "st" (mldEntrySEnd s0) with hs1
  have hentry : runBlock 9 mldCtx mldEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact mldEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb mldFn.blocks = some mldEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 mldCtx mldFn s0 = runBlocks 9 mldCtx mldFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hd1⟩ := mldEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hd1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hd1' : lookupVar "d" s1 = some (EvmYul.UInt256.ofNat 0) := hd1
  set s2 : VenomState := jumpTo "next" (mldStSEnd s1 (EvmYul.UInt256.ofNat 0)) with hs2
  have hstrun : runBlock 8 mldCtx mldSt s1 = ExecResult.OK s2 := by
    rw [show (8 : Nat) = 2 + (5 + 1) from by omega]
    exact mldSt_runBlock s1 5 (EvmYul.UInt256.ofNat 0) hnh1 hd1'
  have hlk1 : lookupBlock s1.currentBb mldFn.blocks = some mldSt := rfl
  have hnh2 : s2.halted = false := by
    rw [hs2]; simpa [jumpTo, updateVar, mstore, writeMemoryWithExpansion] using hnh1
  have hstep1 : runBlocks 9 mldCtx mldFn s1 = runBlocks 8 mldCtx mldFn s2 :=
    runBlocks_step_of_block (fuel := 8) hlk1 hstrun hnh2
  obtain ⟨haL, hbL, hcL⟩ := mldStSEnd_lookup s1 (EvmYul.UInt256.ofNat 0)
  have ha2 : lookupVar "a" s2 = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "a" (mldStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    rw [haL]; exact ha1'
  have hb2 : lookupVar "b" s2 = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "b" (mldStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    rw [hbL]; exact hb1'
  have hc2 : lookupVar "c" s2
      = some (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s1 (EvmYul.UInt256.ofNat 0))) := by
    show lookupVar "c" (mldStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    exact hcL
  have hlk2 : lookupBlock s2.currentBb mldFn.blocks = some r0Next := rfl
  have hhalt := mldNext_halts s2 5 (EvmYul.UInt256.ofNat 0)
    (mload (EvmYul.UInt256.ofNat 0).toNat (mldSt1 s1 (EvmYul.UInt256.ofNat 0)))
    (EvmYul.UInt256.ofNat 0) hb2 hc2 ha2
  rw [show (1 : Nat) + (5 + 1) = 7 from by omega] at hhalt
  rw [h0, hstep0, hstep1]
  exact ⟨_, runBlocks_haltDirect_of_block hlk2 hhalt⟩

/-- **The MLOAD capstone.** `codegen_correct` for
    `entry: %a=CV; %b=CV; %d=CV; JMP st` / `st: MSTORE (Lit 0) %d; %c=MLOAD (Lit 0); JMP next` /
    `next: %e=MUL %b %c; RETURN %e %a` at `fnEom = 64`. The load reads back through the store's
    own window (the store's expansion supplies the load's coverage — no initial-memory
    assumption), and the loaded value is killed by the MUL-by-0 successor. The st block's asm
    run is fully explicit; the entry block rides the generic Var-body JMP slice (first consumer
    of `codegen_correct_ofBlocks_recipeW_invCur`'s currentBb-aware `hpres`). -/
theorem codegen_correct_mldFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 mldCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ mldFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [mldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [mldEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [mldSt, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan mldFn 64 0
      = some ((generateFnPlan mldFn 64 0).get!.1, (generateFnPlan mldFn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel mldFn) mldFn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_invCur mldInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel mldFn) mldFn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan mldFn 64 0).get!.1)).2)
    (fuel := 10) (ctx := mldCtx) (fn := mldFn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan mldFn 64 0).get!.1) (psFinal := (generateFnPlan mldFn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ mldInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [mldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, mldEntry, mldCvA]
    · simp [runBlock, evalPhis, execBlock, mldSt, mldStore]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [mldFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · -- entry: three CALLVALUEs + JMP via the generic Var-body slice
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [mldCvA, mldCvB, mldCvD], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mldCtx mldEntry 1 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
               [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof mldCtx mldEntry 2 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
               [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof mldCtx mldEntry 3 [mldCvA, mldCvB, mldCvD] mldJmp mldCvA
               [mldCvB, mldCvD, mldJmp] s (mldEntrySEnd s) rfl rfl (by decide) hnt (mldEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([mldCvA, mldCvB, mldCvD] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [mldCvA, mldCvB, mldCvD]) (jmpInst := mldJmp) (hd := mldCvA) (tl := [mldCvB, mldCvD, mldJmp])
        (nextLiveness := ["a", "b", "d"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 64) (lbl := "st") (off := 8) (bb' := mldSt) (sEnd := mldEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := mldEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := mldEntry_body)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 3 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by
          rw [show pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 "st" = 6 from rfl]
          have hlit := mld_unresolved
          rw [encodeNumBytes_zero] at hlit
          rw [show (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2
              = buildOffsetToPc (executePlan (generateFnPlan mldFn 64 0).get!.1) from rfl, hlit]
          decide)
        (hlk' := rfl)
        (hw := by decide))
    · -- st: fully explicit — label, PUSH0, MSTORE, PUSH0, MLOAD, then the JMP handoff
      have hlbl : s.currentBb = "st" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hstclause, _⟩ := hinv
      obtain ⟨ha0, hb0, hd0⟩ := hstclause hlbl
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      have hnt : ∀ inst ∈ [mldStore, mldLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mldCtx mldSt 1 [mldStore, mldLoad] mldJmp2 mldStore
               [mldLoad, mldJmp2] s (mldStSEnd s (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide) hnt
               (mldSt_thread s (EvmYul.UInt256.ofNat 0) hd0) (by decide))
      | 1 => exact Or.inl (runBlock_oof mldCtx mldSt 2 [mldStore, mldLoad] mldJmp2 mldStore
               [mldLoad, mldJmp2] s (mldStSEnd s (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide) hnt
               (mldSt_thread s (EvmYul.UInt256.ofNat 0) hd0) (by decide))
      | (j+2) =>
      rw [show j+2+1 = ([mldStore, mldLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psSt := psOfFn (fnPlanFuel mldFn) mldFn 64 0 "st" with hpsSt
      have hpsStack : psSt.stack = [Operand.Var "a", Operand.Var "b", Operand.Var "d"] := rfl
      have hpsSpill : ∀ op, alookup' psSt.spilled op = none := fun _ => rfl
      set prog := (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2 with ho2pcdef
      -- 1: label
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "st"]) := by
        rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psSt { s with instIdx := 0 } asm prog "st" hvrel hbL
      have hpcA : as1.pc = 7 := by
        rw [show (executePlan [StackOp.SOLabel "st"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpc6]
      -- 2: PUSH0 (MSTORE offset)
      have hbP0 : asmBlockAt prog as1.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emitOneInput_sim_lit_append (opc := Opcode.MSTORE)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel1 hbP0
      have hpcB : as2.pc = 8 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      -- 3: MSTORE
      have hvd : operandVal ({ s with instIdx := 0 } : VenomState) lo (Operand.Var "d") = some (EvmYul.UInt256.ofNat 0) := hd0
      have hstack2 : as2.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 0) :: as2.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "d")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel2 (base := [Operand.Var "a", Operand.Var "b"]) ?_ hvd rfl
        show ({ psSt with stack := psSt.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack = _
        rw [hpsStack]; rfl
      obtain ⟨hmst, hrel3⟩ := asmMstore_noSpill_rel (lo := lo)
        (ps := { psSt with stack := psSt.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] })
        (vs := { s with instIdx := 0 }) (as := as2)
        hrel2 hstack2 (fun op => hpsSpill op)
        (Nat.zero_le _) (Nat.zero_le _)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      have hltB : as2.pc < prog.length := by rw [hpcB]; decide
      have hgetB : prog.get ⟨as2.pc, hltB⟩ = AsmInst.AsmOp "MSTORE" := by
        conv_lhs => rw [show (⟨as2.pc, hltB⟩ : Fin _) = ⟨8, by decide⟩ from Fin.ext hpcB]
        rfl
      have hstep3 : asmStep o2pc prog as2 = asmMstore as2 := asmStep_mstore_ok hltB hgetB
      set as3 : AsmState := { asmNext as2 with stack := as2.stack.drop 2, memory := (wordToBytes (EvmYul.UInt256.ofNat 0)).write 0 (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as2.memory) (EvmYul.UInt256.ofNat 0).toNat 32 } with has3
      have hstep3ok : asmStep o2pc prog as2 = AsmResult.AsmOK as3 := by rw [hstep3, hmst]
      have hrun3 : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
        rw [runAsm_succ_ok hltB hstep3ok]; rfl
      have hpcC : as3.pc = 9 := by rw [has3]; show as2.pc + 1 = 9; rw [hpcB]
      -- 4: PUSH0 (MLOAD offset)
      have hbP0b : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emitOneInput_sim_lit_append (opc := Opcode.MLOAD)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel3 hbP0b
      have hpcD : as4.pc = 10 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc4
        rw [hpc4, hpcC]
      -- 5: MLOAD (expanding, no coverage assumption)
      have hvb : operandVal (mstore (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 0) ({ s with instIdx := 0 } : VenomState)) lo (Operand.Var "b") = some (EvmYul.UInt256.ofNat 0) := hb0
      have hstack4 : as4.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 0) :: as4.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "b")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel4 (base := [Operand.Var "a"]) ?_ hvb rfl
        rfl
      obtain ⟨hml, hrel5⟩ := asmMload_expand_noSpill_rel (lo := lo) (out := "c")
        (offset := EvmYul.UInt256.ofNat 0) (rest := (EvmYul.UInt256.ofNat 0) :: as4.stack.drop 2)
        hrel4 hstack4 (fun _ => rfl)
        (by show (EvmYul.UInt256.ofNat 0).toNat + 32 ≤ 64; decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
        (by show ¬ (Operand.Var "c") ∈ [Operand.Var "a", Operand.Var "b", Operand.Lit (EvmYul.UInt256.ofNat 0)]; decide)
      have hltD : as4.pc < prog.length := by rw [hpcD]; decide
      have hgetD : prog.get ⟨as4.pc, hltD⟩ = AsmInst.AsmOp "MLOAD" := by
        conv_lhs => rw [show (⟨as4.pc, hltD⟩ : Fin _) = ⟨10, by decide⟩ from Fin.ext hpcD]
        rfl
      have hstep5 : asmStep o2pc prog as4 = asmMload as4 := asmStep_mload_ok hltD hgetD
      set as5 : AsmState := { asmNext as4 with stack := wordOfBytes ((asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as4.memory).readWithPadding (EvmYul.UInt256.ofNat 0).toNat 32) :: (EvmYul.UInt256.ofNat 0) :: as4.stack.drop 2, memory := asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as4.memory } with has5
      have hstep5ok : asmStep o2pc prog as4 = AsmResult.AsmOK as5 := by rw [hstep5, hml]
      have hrun5 : runAsm 1 o2pc prog as4 = AsmResult.AsmOK as5 := by
        rw [runAsm_succ_ok hltD hstep5ok]; rfl
      have hpcF : as5.pc = 11 := by rw [has5]; show as4.pc + 1 = 11; rw [hpcD]
      -- compose the 5-step body run
      have hrunAll : runAsm (1 + 1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as5 := by
        have hrun1' : runAsm 1 o2pc prog asm = AsmResult.AsmOK as1 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOLabel "st"]).length from rfl]; exact hrun1
        have hrun2' : runAsm 1 o2pc prog as1 = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun2
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun4
        exact runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose hrun1' hrun2') hrun3) hrun4') hrun5
      have hrunAll5 : runAsm 5 o2pc prog asm = AsmResult.AsmOK as5 := hrunAll
      have hterm := termRecipeW_jmp_of_body (bb := mldSt) (bb' := r0Next) (lbl := "next")
        (off := 17) (bodyLen := 5) (ctx := mldCtx) (prog := prog) (o2pc := o2pc)
        (fn := mldFn) (lo := lo) (s := s) (as' := as5)
        (front := [mldStore, mldLoad]) (jmpInst := mldJmp2) (hd := mldStore)
        (tl := [mldLoad, mldJmp2]) (restFuel := j)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel mldFn) mldFn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan mldFn 64 0).get!.1)).2)
        rfl rfl rfl rfl (by decide) hnt (mldSt_thread s (EvmYul.UInt256.ofNat 0) hd0)
        (by simpa [updateVar, mstore, writeMemoryWithExpansion] using hhalt)
        hrel5 rfl (by decide)
        (by rw [hpcF]; decide)
        (by conv_lhs => rw [show (⟨as5.pc, by rw [hpcF]; decide⟩ : Fin _) = ⟨11, by decide⟩
              from Fin.ext hpcF]
            rfl)
        (by have hlit := mld_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [hlit]
            decide)
        (by decide)
        (by rw [hpcF]; decide)
        (by conv_lhs => rw [show (⟨as5.pc + 1, by rw [hpcF]; decide⟩ : Fin _) = ⟨12, by decide⟩
              from Fin.ext (show as5.pc + 1 = 12 by omega)]
            rfl)
        (by rw [ho2pcdef, hprogdef,
              show pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 "next" = 13 from rfl]
            have hlit := mld_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [show (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).2
                = buildOffsetToPc (executePlan (generateFnPlan mldFn 64 0).get!.1) from rfl, hlit]
            decide) rfl
      exact ⟨as5, _, mldStSEnd s (EvmYul.UInt256.ofNat 0), 5, hrunAll5, hterm⟩
    · -- next: the r0 pattern (MUL-by-0 kill + empty RETURN window) at pc 13, fnEom 64
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc13 : asm.pc = 13 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mldCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel mldFn) mldFn 64 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (mldCVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (mldCVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (mldCVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (mldCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (mldCVal s)).2]; exact ha0)
        (hready := mldNext_ready)
        (hsd := ⟨by intro op'; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel mldFn) mldFn 64 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc13]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc13]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc13]; decide) (hret := by simp only [hpc13]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨mldEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel mldFn) mldFn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan mldFn 64 0).get!.1)).1.length
      omega

end Example


/-! ## The store-then-hash SHA3 capstone: real bytes under the hash (sz > 0) -/

/-- **The expanding no-spill SHA3 step + relation** — `venomAsmRel_sha3` for an asm memory that
    does NOT yet cover the window: `asmSha3` expands first, and both the hash value and
    `memoryRel` survive because expansion is read-invariant. `planSpillRel` is vacuous under
    `noSpill`, so the expanded memory needs no spill-slot reasoning. -/
theorem asmSha3_expand_noSpill_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {out : String} {off sz : bytes32} {rest : List bytes32}
    (hrel : venomAsmRel lo ps vs as)
    (hstack : as.stack = off :: sz :: rest)
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hbelow : off.toNat + sz.toNat ≤ ps.alloc.fnEom)
    (hsize : sz.toNat < USize.size)
    (hszne : ¬ sz.toNat = 0)
    (hro : ((off.toNat + sz.toNat + 31) / 32) * 32 < USize.size)
    (hfresh : ¬ (Operand.Var out) ∈ ps.stack) :
    asmSha3 as = AsmResult.AsmOK ({ asmNext as with stack := keccak256 ((asmExpandMemory (off.toNat + sz.toNat) as.memory).readWithPadding off.toNat sz.toNat) :: rest, memory := asmExpandMemory (off.toNat + sz.toNat) as.memory })
    ∧ venomAsmRel lo { ps with stack := stackPush (Operand.Var out) (stackPop 2 ps.stack) }
        (updateVar out (keccak256 (readMemory off.toNat sz.toNat vs)) vs)
        ({ asmNext as with stack := keccak256 ((asmExpandMemory (off.toNat + sz.toNat) as.memory).readWithPadding off.toNat sz.toNat) :: rest, memory := asmExpandMemory (off.toNat + sz.toNat) as.memory }) := by
  have hreadE : (asmExpandMemory (off.toNat + sz.toNat) as.memory).readWithPadding off.toNat sz.toNat
      = as.memory.readWithPadding off.toNat sz.toNat :=
    readWithPadding_asmExpandMemory off.toNat sz.toNat (off.toNat + sz.toNat) as.memory hsize hro
  constructor
  · simp only [asmSha3, hstack, hszne, if_false]
  · obtain ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ := hrel
    have hread : vs.memory.readWithPadding off.toNat sz.toNat
        = as.memory.readWithPadding off.toNat sz.toNat :=
      memoryRel_readWithPadding_slice hMem hbelow hsize
    have hval : keccak256 (readMemory off.toNat sz.toNat vs)
        = keccak256 ((asmExpandMemory (off.toNat + sz.toNat) as.memory).readWithPadding off.toNat sz.toNat) := by
      simp only [readMemory, hread, hreadE]
    have hlen2 : 2 ≤ ps.stack.length := by rw [hStk.1, hstack]; simp
    have hspill' : AssocList.lookup Operand Nat ps.spilled (Operand.Var out) = none := hnospill _
    obtain ⟨hStk', hSpill', hMem', hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩ :=
      venomAsmRel_updateVar lo ps vs as out (keccak256 (readMemory off.toNat sz.toNat vs))
        ⟨hStk, hSpill, hMem, hAcc, hTrans, hRet, hLog, hCall, hTx, hBlk, hCode, hPrev⟩ hfresh hspill'
    refine ⟨?_, ?_, ?_, hAcc', hTrans', hRet', hLog', hCall', hTx', hBlk', hCode', hPrev'⟩
    · -- planStackRel: pop 2, push the fresh out bound to the hash
      have hout : operandVal (updateVar out (keccak256 (readMemory off.toNat sz.toNat vs)) vs)
          lo (Operand.Var out)
          = some (keccak256 ((asmExpandMemory (off.toNat + sz.toNat) as.memory).readWithPadding off.toNat sz.toNat)) := by
        simp only [operandVal, lookupVar_updateVar_self]; rw [hval]
      have hps := planStackRel_binop hStk' hlen2 hout
      rw [hstack] at hps
      simpa using hps
    · -- planSpillRel: vacuous under noSpill
      intro op off' hlook
      rw [show AssocList.lookup Operand Nat ps.spilled op = alookup' ps.spilled op from rfl,
          hnospill op] at hlook
      exact absurd hlook (by simp)
    · -- memoryRel: venom memory unchanged; asm expansion is readByte-invariant
      intro i hi
      show readByte i vs.memory = readByte i (asmExpandMemory (off.toNat + sz.toNat) as.memory)
      rw [readByte_asmExpandMemory i _ as.memory hro]
      exact hMem i hi

/-- `encodeNumBytes 32 = [32]` — the single-byte bridge for the `Lit 32` push (the WF-recursive
    `encodeNumBytes` is kernel-stuck on every nonzero argument; its equation lemmas still fire
    under `unfold`). -/
theorem encodeNumBytes_32 : encodeNumBytes 32 = [(32 : UInt8)] := by
  unfold encodeNumBytes
  norm_num [encodeNumBytes_zero]
  decide

namespace Example

/-! ### The store-then-hash SHA3 capstone `shs`: `entry: %a=CV; %b=CV; %d=CV; JMP st` /
    `st: MSTORE (Lit 0) %d; %c=SHA3 (Lit 0)(Lit 32); JMP next` / `next = r0Next` (MUL-by-0
    kill) at `fnEom = 64`. The hash covers the 32 REAL stored bytes through the store's own
    window (`asmSha3_expand_noSpill_rel` — the sz>0 sibling of the degenerate `sh3`). -/

def shsCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def shsCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def shsCvD : Instruction := { id := 2, opcode := Opcode.CALLVALUE, operands := [], outputs := ["d"] }
def shsJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "st"], outputs := [] }
def shsStore : Instruction := { id := 4, opcode := Opcode.MSTORE, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Var "d"], outputs := [] }
def shsSha : Instruction := { id := 5, opcode := Opcode.SHA3, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Lit (EvmYul.UInt256.ofNat 32)], outputs := ["c"] }
def shsJmp2 : Instruction := { id := 6, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def shsEntry : BasicBlock := { label := "entry", instructions := [shsCvA, shsCvB, shsCvD, shsJmp] }
def shsSt : BasicBlock := { label := "st", instructions := [shsStore, shsSha, shsJmp2] }
def shsFn : IrFunction := { name := "main", blocks := [shsEntry, shsSt, r0Next] }
def shsCtx : VenomContext := { functions := [shsFn], entry := some "main" }

/-- The hashed value as a function of the CURRENT state's memory (invariant under
    `updateVar` / `jumpTo` / `instIdx`, so it can live inside the invariant). -/
abbrev shsCVal (s : VenomState) : bytes32 :=
  keccak256 (readMemory (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 32).toNat s)

abbrev shsEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "d" s.callCtx.callvalue { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem shsEntry_thread (s : VenomState) :
    execBodyThread [shsCvA, shsCvB, shsCvD] 0 { s with instIdx := 0 } = some (shsEntrySEnd s) := rfl

theorem shsEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) shsCtx shsEntry s = ExecResult.OK (jumpTo "st" (shsEntrySEnd s)) :=
  runBlock_body_jmp shsCtx shsEntry j [shsCvA, shsCvB, shsCvD] shsJmp shsCvA [shsCvB, shsCvD, shsJmp] s
    (shsEntrySEnd s) "st" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (shsEntry_thread s) (by simpa [updateVar] using hnh)

theorem shsEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (shsEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (shsEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "d" (shsEntrySEnd s) = some s.callCtx.callvalue := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "d" (updateVar "d" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

/-- entry's body `[CV a; CV b; CV d]` as a `RegularBodyH`: three `cv_step`s. -/
theorem shsEntry_body {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} :
    RegularBodyH lo ["a", "b", "d"] offsetToPc
      (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 1 [shsCvA, shsCvB, shsCvD] [] :=
  ⟨cv_step (out := "a") (S := []) rfl (by decide) (by decide),
   cv_step (out := "b") (S := ["a"]) rfl (by decide) (by decide),
   cv_step (out := "d") (S := ["a", "b"]) rfl (by decide) (by decide), trivial⟩

abbrev shsSt1 (s : VenomState) (wd : bytes32) : VenomState :=
  { mstore (EvmYul.UInt256.ofNat 0).toNat wd { s with instIdx := 0 } with instIdx := 1 }

abbrev shsStSEnd (s : VenomState) (wd : bytes32) : VenomState :=
  { updateVar "c" (shsCVal (shsSt1 s wd)) (shsSt1 s wd) with instIdx := 2 }

theorem shsSt_thread (s : VenomState) (wd : bytes32) (hd : lookupVar "d" s = some wd) :
    execBodyThread [shsStore, shsSha] 0 { s with instIdx := 0 } = some (shsStSEnd s wd) := by
  have hd' : lookupVar "d" ({ s with instIdx := 0 } : VenomState) = some wd := hd
  have hstep1 : stepInstBase shsStore { s with instIdx := 0 }
      = ExecResult.OK (mstore (EvmYul.UInt256.ofNat 0).toNat wd { s with instIdx := 0 }) := by
    show execWrite2 (fun addr val s => mstore addr.toNat val s) shsStore { s with instIdx := 0 } = _
    unfold execWrite2
    simp only [shsStore, evalOperand, hd']
  have hstep2 : stepInstBase shsSha (shsSt1 s wd)
      = ExecResult.OK (updateVar "c" (shsCVal (shsSt1 s wd)) (shsSt1 s wd)) := rfl
  show (match stepInstBase shsStore { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [shsSha] 1 { s' with instIdx := 1 } | _ => none)
      = some (shsStSEnd s wd)
  rw [hstep1]
  show (match stepInstBase shsSha (shsSt1 s wd) with
        | ExecResult.OK s' => execBodyThread [] 2 { s' with instIdx := 2 } | _ => none)
      = some (shsStSEnd s wd)
  rw [hstep2]; rfl

theorem shsSt_runBlock (s : VenomState) (j : Nat) (wd : bytes32) (hnh : s.halted = false)
    (hd : lookupVar "d" s = some wd) :
    runBlock (2 + (j + 1)) shsCtx shsSt s = ExecResult.OK (jumpTo "next" (shsStSEnd s wd)) :=
  runBlock_body_jmp shsCtx shsSt j [shsStore, shsSha] shsJmp2 shsStore [shsSha, shsJmp2] s
    (shsStSEnd s wd) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide)
    (shsSt_thread s wd hd) (by simpa [updateVar, mstore, writeMemoryWithExpansion] using hnh)

theorem shsSt_error (s : VenomState) (hd : lookupVar "d" s = none) :
    stepInstBase shsStore { s with instIdx := 0 } = ExecResult.Error "undefined operand" := by
  have hd' : lookupVar "d" ({ s with instIdx := 0 } : VenomState) = none := hd
  show execWrite2 (fun addr val s => mstore addr.toNat val s) shsStore { s with instIdx := 0 } = _
  unfold execWrite2
  simp [shsStore, evalOperand, hd']

theorem shsStSEnd_lookup (s : VenomState) (wd : bytes32) :
    lookupVar "a" (shsStSEnd s wd) = lookupVar "a" s
    ∧ lookupVar "b" (shsStSEnd s wd) = lookupVar "b" s
    ∧ lookupVar "c" (shsStSEnd s wd) = some (shsCVal (shsSt1 s wd)) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (shsCVal (shsSt1 s wd)) (shsSt1 s wd)) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    rfl
  · show lookupVar "b" (updateVar "c" (shsCVal (shsSt1 s wd)) (shsSt1 s wd)) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    rfl
  · show lookupVar "c" (updateVar "c" (shsCVal (shsSt1 s wd)) (shsSt1 s wd)) = _
    rw [lookupVar_updateVar_self]

theorem shsNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) shsCtx r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return shsCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem shsNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) shsCtx r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term shsCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

def shsInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "st" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                      ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                      ∧ lookupVar "d" s = some (EvmYul.UInt256.ofNat 0)) ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (shsCVal s))

theorem shsInv_pres : ∀ bb ∈ shsFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    shsInv s → runBlock f' shsCtx bb s = ExecResult.OK s' → s.currentBb = bb.label → shsInv s' := by
  intro bb hbb s s' f' hinv hrun hcur
  obtain ⟨hnh, hcv, hst, _⟩ := hinv
  simp only [shsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl | rfl
  · have hnt : ∀ inst ∈ [shsCvA, shsCvB, shsCvD], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof shsCtx shsEntry 0 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
             [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof shsCtx shsEntry 1 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
             [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof shsCtx shsEntry 2 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
             [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof shsCtx shsEntry 3 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
             [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, shsEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hd0⟩ := shsEntrySEnd_lookup s
      rw [hcv] at ha0 hb0 hd0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        fun _ => ⟨ha0, hb0, hd0⟩, fun h => by simp [jumpTo] at h⟩
  · match f' with
    | 0 => rw [runBlock_no_phi 0 shsCtx shsSt s shsStore [shsSha, shsJmp2] rfl (by decide)] at hrun
           simp [execBlock] at hrun
    | 1 =>
      rcases hld : lookupVar "d" s with _ | wd
      · rw [runBlock_body_head_error shsCtx shsSt shsStore [shsSha, shsJmp2] s "undefined operand" 0 rfl
          (by decide) (shsSt_error s hld) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
      · obtain ⟨e, he⟩ := runBlock_oof shsCtx shsSt 1 [shsStore, shsSha] shsJmp2 shsStore
          [shsSha, shsJmp2] s (shsStSEnd s wd) rfl rfl (by decide)
          (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> decide)
          (shsSt_thread s wd hld) (by decide)
        rw [he] at hrun; exact absurd hrun (by simp)
    | 2 =>
      rcases hld : lookupVar "d" s with _ | wd
      · rw [runBlock_body_head_error shsCtx shsSt shsStore [shsSha, shsJmp2] s "undefined operand" 1 rfl
          (by decide) (shsSt_error s hld) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
      · obtain ⟨e, he⟩ := runBlock_oof shsCtx shsSt 2 [shsStore, shsSha] shsJmp2 shsStore
          [shsSha, shsJmp2] s (shsStSEnd s wd) rfl rfl (by decide)
          (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> decide)
          (shsSt_thread s wd hld) (by decide)
        rw [he] at hrun; exact absurd hrun (by simp)
    | (j+3) =>
      obtain ⟨ha0, hb0, hd0⟩ := hst hcur
      rw [show j+3 = 2+(j+1) from by omega, shsSt_runBlock s j (EvmYul.UInt256.ofNat 0) hnh hd0] at hrun
      injection hrun with h; subst h
      obtain ⟨haL, hbL, hcL⟩ := shsStSEnd_lookup s (EvmYul.UInt256.ofNat 0)
      refine ⟨by simpa [jumpTo, updateVar, mstore, writeMemoryWithExpansion] using hnh,
        by simp [jumpTo, updateVar, mstore, writeMemoryWithExpansion, hcv],
        fun h => by simp [jumpTo] at h, fun _ => ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · show lookupVar "a" (shsStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [haL]; exact ha0
      · show lookupVar "b" (shsStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [hbL]; exact hb0
      · show lookupVar "c" (shsStSEnd s (EvmYul.UInt256.ofNat 0)) = _
        rw [hcL]; rfl
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 shsCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error shsCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 shsCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error shsCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 shsCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof shsCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, shsNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 shsCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof shsCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, shsNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem shsNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg shsFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := shsFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

/-- The **unresolved** shs asm program as a stuck-preserving literal (same trick as
    `sh3_unresolved`): late label keys (st at byte 8 is fine, next at byte 17 is not)
    accumulate `asmInstSize` over the two `AsmPush (encodeNumBytes 0)`s and stick. -/
theorem shs_unresolved :
    executePlan (generateFnPlan shsFn 64 0).get!.1
      = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
         AsmInst.AsmOp "CALLVALUE", AsmInst.AsmPushLabel "st", AsmInst.AsmOp "JUMP",
         AsmInst.AsmLabel "st", AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "MSTORE",
         AsmInst.AsmPush (encodeNumBytes 32), AsmInst.AsmPush (encodeNumBytes 0),
         AsmInst.AsmOp "SHA3", AsmInst.AsmPushLabel "next", AsmInst.AsmOp "JUMP",
         AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL", AsmInst.AsmOp "RETURN"] := rfl

theorem shsFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 shsCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 shsCtx vs
      = runBlocks 10 shsCtx shsFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, shsCtx, shsFn, lookupFunction, fnEntryLabel, shsEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "st" (shsEntrySEnd s0) with hs1
  have hentry : runBlock 9 shsCtx shsEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact shsEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb shsFn.blocks = some shsEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 shsCtx shsFn s0 = runBlocks 9 shsCtx shsFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hd1⟩ := shsEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1 hd1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hd1' : lookupVar "d" s1 = some (EvmYul.UInt256.ofNat 0) := hd1
  set s2 : VenomState := jumpTo "next" (shsStSEnd s1 (EvmYul.UInt256.ofNat 0)) with hs2
  have hstrun : runBlock 8 shsCtx shsSt s1 = ExecResult.OK s2 := by
    rw [show (8 : Nat) = 2 + (5 + 1) from by omega]
    exact shsSt_runBlock s1 5 (EvmYul.UInt256.ofNat 0) hnh1 hd1'
  have hlk1 : lookupBlock s1.currentBb shsFn.blocks = some shsSt := rfl
  have hnh2 : s2.halted = false := by
    rw [hs2]; simpa [jumpTo, updateVar, mstore, writeMemoryWithExpansion] using hnh1
  have hstep1 : runBlocks 9 shsCtx shsFn s1 = runBlocks 8 shsCtx shsFn s2 :=
    runBlocks_step_of_block (fuel := 8) hlk1 hstrun hnh2
  obtain ⟨haL, hbL, hcL⟩ := shsStSEnd_lookup s1 (EvmYul.UInt256.ofNat 0)
  have ha2 : lookupVar "a" s2 = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "a" (shsStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    rw [haL]; exact ha1'
  have hb2 : lookupVar "b" s2 = some (EvmYul.UInt256.ofNat 0) := by
    show lookupVar "b" (shsStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    rw [hbL]; exact hb1'
  have hc2 : lookupVar "c" s2
      = some (shsCVal (shsSt1 s1 (EvmYul.UInt256.ofNat 0))) := by
    show lookupVar "c" (shsStSEnd s1 (EvmYul.UInt256.ofNat 0)) = _
    exact hcL
  have hlk2 : lookupBlock s2.currentBb shsFn.blocks = some r0Next := rfl
  have hhalt := shsNext_halts s2 5 (EvmYul.UInt256.ofNat 0)
    (shsCVal (shsSt1 s1 (EvmYul.UInt256.ofNat 0)))
    (EvmYul.UInt256.ofNat 0) hb2 hc2 ha2
  rw [show (1 : Nat) + (5 + 1) = 7 from by omega] at hhalt
  rw [h0, hstep0, hstep1]
  exact ⟨_, runBlocks_haltDirect_of_block hlk2 hhalt⟩

/-- **The store-then-hash SHA3 capstone.** `codegen_correct` for
    `entry: %a=CV; %b=CV; %d=CV; JMP st` / `st: MSTORE (Lit 0) %d; %c=SHA3 (Lit 0)(Lit 32);
    JMP next` / `next: %e=MUL %b %c; RETURN %e %a` at `fnEom = 64`. The hash covers the 32
    REAL stored bytes (`asmSha3_expand_noSpill_rel` — the store's expansion makes the window
    coverage-free), and is killed by the MUL-by-0 successor. The sz>0 completion of the
    degenerate empty-slice `sh3`; the `Lit 32` push exercises the `encodeNumBytes_32`
    stuck-size bridge in the label-key facts. -/
theorem codegen_correct_shsFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 shsCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ shsFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [shsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp only [shsEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [shsSt, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan shsFn 64 0
      = some ((generateFnPlan shsFn 64 0).get!.1, (generateFnPlan shsFn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel shsFn) shsFn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_invCur shsInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel shsFn) shsFn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan shsFn 64 0).get!.1)).2)
    (fuel := 10) (ctx := shsCtx) (fn := shsFn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan shsFn 64 0).get!.1) (psFinal := (generateFnPlan shsFn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ shsInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun h => by simp at h, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [shsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · simp [runBlock, evalPhis, execBlock, shsEntry, shsCvA]
    · simp [runBlock, evalPhis, execBlock, shsSt, shsStore]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [shsFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl | rfl
    · -- entry: three CALLVALUEs + JMP via the generic Var-body slice
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [shsCvA, shsCvB, shsCvD], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof shsCtx shsEntry 1 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
               [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof shsCtx shsEntry 2 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
               [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof shsCtx shsEntry 3 [shsCvA, shsCvB, shsCvD] shsJmp shsCvA
               [shsCvB, shsCvD, shsJmp] s (shsEntrySEnd s) rfl rfl (by decide) hnt (shsEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([shsCvA, shsCvB, shsCvD] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      refine Or.inr (hsupplyW_regularJmp
        (liveness := exLiveness) (dfg := DfgAnalysis.empty) (cfg := exCfg) (restFuel := j)
        (front := [shsCvA, shsCvB, shsCvD]) (jmpInst := shsJmp) (hd := shsCvA) (tl := [shsCvB, shsCvD, shsJmp])
        (nextLiveness := ["a", "b", "d"]) (curBbLabel := "entry") (dem := 1) (S := [])
        (ps0 := initPlanState 64) (lbl := "st") (off := 8) (bb' := shsSt) (sEnd := shsEntrySEnd s)
        (hbb := rfl) (hjmpop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := hnt) (hthread := shsEntry_thread s) (hnothalt := by simpa [updateVar] using hhalt)
        (hreg := shsEntry_body)
        (hsd := ⟨by intro op'; rfl, by simp [initPlanState], by intro z hz; simp [initPlanState] at hz⟩)
        (hsv := by simp [StackIsVars, initPlanState])
        (hrel := by rw [hpsE] at hvrel; exact hvrel)
        (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 3 := hj; interval_cases j <;> rfl)
        (hps := rfl) (hpc := by rw [hpc0]; decide) (hpush := by simp only [hpc0]; rfl)
        (hoff_lk := by decide)
        (hoff := by decide) (hpc2 := by rw [hpc0]; decide)
        (hjump := by simp only [hpc0]; rfl)
        (hidx_lk := by
          rw [show pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 "st" = 6 from rfl]
          have hlit := shs_unresolved
          rw [encodeNumBytes_zero, encodeNumBytes_32] at hlit
          rw [show (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2
              = buildOffsetToPc (executePlan (generateFnPlan shsFn 64 0).get!.1) from rfl, hlit]
          decide)
        (hlk' := rfl)
        (hw := by decide))
    · -- st: fully explicit — label, PUSH0, MSTORE, PUSH32, PUSH0, SHA3, then the JMP handoff
      have hlbl : s.currentBb = "st" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hstclause, _⟩ := hinv
      obtain ⟨ha0, hb0, hd0⟩ := hstclause hlbl
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      have hnt : ∀ inst ∈ [shsStore, shsSha], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof shsCtx shsSt 1 [shsStore, shsSha] shsJmp2 shsStore
               [shsSha, shsJmp2] s (shsStSEnd s (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide) hnt
               (shsSt_thread s (EvmYul.UInt256.ofNat 0) hd0) (by decide))
      | 1 => exact Or.inl (runBlock_oof shsCtx shsSt 2 [shsStore, shsSha] shsJmp2 shsStore
               [shsSha, shsJmp2] s (shsStSEnd s (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide) hnt
               (shsSt_thread s (EvmYul.UInt256.ofNat 0) hd0) (by decide))
      | (j+2) =>
      rw [show j+2+1 = ([shsStore, shsSha] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psSt := psOfFn (fnPlanFuel shsFn) shsFn 64 0 "st" with hpsSt
      have hpsStack : psSt.stack = [Operand.Var "a", Operand.Var "b", Operand.Var "d"] := rfl
      have hpsSpill : ∀ op, alookup' psSt.spilled op = none := fun _ => rfl
      set prog := (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2 with ho2pcdef
      -- 1: label
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "st"]) := by
        rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psSt { s with instIdx := 0 } asm prog "st" hvrel hbL
      have hpcA : as1.pc = 7 := by
        rw [show (executePlan [StackOp.SOLabel "st"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpc6]
      -- 2: PUSH0 (MSTORE offset)
      have hbP0 : asmBlockAt prog as1.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emitOneInput_sim_lit_append (opc := Opcode.MSTORE)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel1 hbP0
      have hpcB : as2.pc = 8 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      -- 3: MSTORE
      have hvd : operandVal ({ s with instIdx := 0 } : VenomState) lo (Operand.Var "d") = some (EvmYul.UInt256.ofNat 0) := hd0
      have hstack2 : as2.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 0) :: as2.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "d")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel2 (base := [Operand.Var "a", Operand.Var "b"]) ?_ hvd rfl
        show ({ psSt with stack := psSt.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] } : PlanState).stack = _
        rw [hpsStack]; rfl
      obtain ⟨hmst, hrel3⟩ := asmMstore_noSpill_rel (lo := lo)
        (ps := { psSt with stack := psSt.stack ++ [Operand.Lit (EvmYul.UInt256.ofNat 0)] })
        (vs := { s with instIdx := 0 }) (as := as2)
        hrel2 hstack2 (fun op => hpsSpill op)
        (Nat.zero_le _) (Nat.zero_le _)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
      have hltB : as2.pc < prog.length := by rw [hpcB]; decide
      have hgetB : prog.get ⟨as2.pc, hltB⟩ = AsmInst.AsmOp "MSTORE" := by
        conv_lhs => rw [show (⟨as2.pc, hltB⟩ : Fin _) = ⟨8, by decide⟩ from Fin.ext hpcB]
        rfl
      have hstep3 : asmStep o2pc prog as2 = asmMstore as2 := asmStep_mstore_ok hltB hgetB
      set as3 : AsmState := { asmNext as2 with stack := as2.stack.drop 2, memory := (wordToBytes (EvmYul.UInt256.ofNat 0)).write 0 (asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as2.memory) (EvmYul.UInt256.ofNat 0).toNat 32 } with has3
      have hstep3ok : asmStep o2pc prog as2 = AsmResult.AsmOK as3 := by rw [hstep3, hmst]
      have hrun3 : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
        rw [runAsm_succ_ok hltB hstep3ok]; rfl
      have hpcC : as3.pc = 9 := by rw [has3]; show as2.pc + 1 = 9; rw [hpcB]
      -- 4: PUSH 32 (SHA3 size)
      have hbP32 : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emitOneInput_sim_lit_append (opc := Opcode.SHA3)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 32) hrel3 hbP32
      have hpcD : as4.pc = 10 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length = 1 from rfl] at hpc4
        rw [hpc4, hpcC]
      -- 5: PUSH0 (SHA3 offset)
      have hbP0c : asmBlockAt prog as4.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcD]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as5, hrun5, hrel5, hpc5⟩ := emitOneInput_sim_lit_append (opc := Opcode.SHA3)
        (nl := ([] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel4 hbP0c
      have hpcE2 : as5.pc = 11 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc5
        rw [hpc5, hpcD]
      -- 6: SHA3 (expanding, no coverage assumption)
      have htop5 : as5.stack = (EvmYul.UInt256.ofNat 0) :: (EvmYul.UInt256.ofNat 32) :: as5.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Lit (EvmYul.UInt256.ofNat 32))
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel5 (base := [Operand.Var "a", Operand.Var "b"]) ?_ rfl rfl
        rfl
      obtain ⟨hsha, hrel6⟩ := asmSha3_expand_noSpill_rel (lo := lo) (out := "c")
        (off := EvmYul.UInt256.ofNat 0) (sz := EvmYul.UInt256.ofNat 32)
        (rest := as5.stack.drop 2)
        hrel5 htop5 (fun _ => rfl)
        (by show (EvmYul.UInt256.ofNat 0).toNat + (EvmYul.UInt256.ofNat 32).toNat ≤ 64; decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
        (by decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
        (by show ¬ (Operand.Var "c") ∈ [Operand.Var "a", Operand.Var "b", Operand.Lit (EvmYul.UInt256.ofNat 32), Operand.Lit (EvmYul.UInt256.ofNat 0)]; decide)
      have hltF : as5.pc < prog.length := by rw [hpcE2]; decide
      have hgetF : prog.get ⟨as5.pc, hltF⟩ = AsmInst.AsmOp "SHA3" := by
        conv_lhs => rw [show (⟨as5.pc, hltF⟩ : Fin _) = ⟨11, by decide⟩ from Fin.ext hpcE2]
        rfl
      have hstep6 : asmStep o2pc prog as5 = asmSha3 as5 := asmStep_sha3_ok hltF hgetF
      set as6 : AsmState := { asmNext as5 with stack := keccak256 ((asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + (EvmYul.UInt256.ofNat 32).toNat) as5.memory).readWithPadding (EvmYul.UInt256.ofNat 0).toNat (EvmYul.UInt256.ofNat 32).toNat) :: as5.stack.drop 2, memory := asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + (EvmYul.UInt256.ofNat 32).toNat) as5.memory } with has6
      have hstep6ok : asmStep o2pc prog as5 = AsmResult.AsmOK as6 := by rw [hstep6, hsha]
      have hrun6 : runAsm 1 o2pc prog as5 = AsmResult.AsmOK as6 := by
        rw [runAsm_succ_ok hltF hstep6ok]; rfl
      have hpcF : as6.pc = 12 := by rw [has6]; show as5.pc + 1 = 12; rw [hpcE2]
      -- compose the 6-step body run
      have hrunAll : runAsm (1 + 1 + 1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as6 := by
        have hrun1' : runAsm 1 o2pc prog asm = AsmResult.AsmOK as1 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOLabel "st"]).length from rfl]; exact hrun1
        have hrun2' : runAsm 1 o2pc prog as1 = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun2
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 32))]).length from rfl]; exact hrun4
        have hrun5' : runAsm 1 o2pc prog as4 = AsmResult.AsmOK as5 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun5
        exact runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose hrun1' hrun2') hrun3) hrun4') hrun5') hrun6
      have hrunAll6 : runAsm 6 o2pc prog asm = AsmResult.AsmOK as6 := hrunAll
      have hterm := termRecipeW_jmp_of_body (bb := shsSt) (bb' := r0Next) (lbl := "next")
        (off := 19) (bodyLen := 6) (ctx := shsCtx) (prog := prog) (o2pc := o2pc)
        (fn := shsFn) (lo := lo) (s := s) (as' := as6)
        (front := [shsStore, shsSha]) (jmpInst := shsJmp2) (hd := shsStore)
        (tl := [shsSha, shsJmp2]) (restFuel := j)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel shsFn) shsFn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan shsFn 64 0).get!.1)).2)
        rfl rfl rfl rfl (by decide) hnt (shsSt_thread s (EvmYul.UInt256.ofNat 0) hd0)
        (by simpa [updateVar, mstore, writeMemoryWithExpansion] using hhalt)
        hrel6 rfl (by decide)
        (by rw [hpcF]; decide)
        (by conv_lhs => rw [show (⟨as6.pc, by rw [hpcF]; decide⟩ : Fin _) = ⟨12, by decide⟩
              from Fin.ext hpcF]
            rfl)
        (by have hlit := shs_unresolved
            rw [encodeNumBytes_zero, encodeNumBytes_32] at hlit
            rw [hlit]
            decide)
        (by decide)
        (by rw [hpcF]; decide)
        (by conv_lhs => rw [show (⟨as6.pc + 1, by rw [hpcF]; decide⟩ : Fin _) = ⟨13, by decide⟩
              from Fin.ext (show as6.pc + 1 = 13 by omega)]
            rfl)
        (by rw [ho2pcdef, hprogdef,
              show pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 "next" = 14 from rfl]
            have hlit := shs_unresolved
            rw [encodeNumBytes_zero, encodeNumBytes_32] at hlit
            rw [show (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).2
                = buildOffsetToPc (executePlan (generateFnPlan shsFn 64 0).get!.1) from rfl, hlit]
            decide) rfl
      exact ⟨as6, _, shsStSEnd s (EvmYul.UInt256.ofNat 0), 6, hrunAll6, hterm⟩
    · -- next: the r0 pattern (MUL-by-0 kill + empty RETURN window) at pc 13, fnEom 64
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc14 : asm.pc = 14 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof shsCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel shsFn) shsFn 64 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (shsCVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (shsCVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (shsCVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (shsCVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (shsCVal s)).2]; exact ha0)
        (hready := shsNext_ready)
        (hsd := ⟨by intro op'; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel shsFn) shsFn 64 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc14]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc14]; decide) (hret := by simp only [hpc14]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨shsEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel shsFn) shsFn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan shsFn 64 0).get!.1)).1.length
      omega

end Example


/-! ## The ILOAD capstone: the immutables-in-memory regime as a Venom-side invariant -/

namespace Example

/-! ### The ILOAD capstone `ild`: `entry: %a=CV; %b=CV; %c=ILOAD (Lit 0); JMP next` /
    `next = r0Next` (MUL-by-0 kill) at `fnEom = 64`, under the IMMUTABLES-IN-MEMORY regime
    hypothesis `ildVal vs = mload 0 vs` (immutable 0 is laid out at memory offset 0). ILOAD
    lowers to `MLOAD`; the asm side runs `asmMload_expand_noSpill_rel` (coverage-free) and the
    regime hypothesis transports the venom value from the memory read to the immutables read. -/

def ildCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def ildCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def ildLoad : Instruction := { id := 2, opcode := Opcode.ILOAD, operands := [Operand.Lit (EvmYul.UInt256.ofNat 0)], outputs := ["c"] }
def ildJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def ildEntry : BasicBlock := { label := "entry", instructions := [ildCvA, ildCvB, ildLoad, ildJmp] }
def ildFn : IrFunction := { name := "main", blocks := [ildEntry, r0Next] }
def ildCtx : VenomContext := { functions := [ildFn], entry := some "main" }

/-- The immutables read at index 0 (with the semantics' zero default). Memory-independent and
    var-independent, so stable under `updateVar` / `jumpTo` / memory writes. -/
abbrev ildVal (s : VenomState) : bytes32 :=
  match alookup s.immutables (EvmYul.UInt256.ofNat 0).toNat with
  | some v => v
  | none => ⟨0⟩

abbrev ildEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (ildVal s) { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem ildEntry_thread (s : VenomState) :
    execBodyThread [ildCvA, ildCvB, ildLoad] 0 { s with instIdx := 0 } = some (ildEntrySEnd s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hfv : ildVal S2 = ildVal s := rfl
  have hsub : stepInstBase ildLoad S2 = ExecResult.OK (updateVar "c" (ildVal s) S2) := by
    rw [show stepInstBase ildLoad S2
      = ExecResult.OK (updateVar "c" (ildVal S2) S2) from rfl, hfv]
  have h1 : stepInstBase ildCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase ildCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase ildCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [ildCvB, ildLoad] 1 { s' with instIdx := 1 } | _ => none)
      = some (ildEntrySEnd s)
  rw [h1]
  show (match stepInstBase ildCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [ildLoad] 2 { s' with instIdx := 2 } | _ => none)
      = some (ildEntrySEnd s)
  rw [h2]
  show (match stepInstBase ildLoad S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none)
      = some (ildEntrySEnd s)
  rw [hsub]; rfl

theorem ildEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) ildCtx ildEntry s = ExecResult.OK (jumpTo "next" (ildEntrySEnd s)) :=
  runBlock_body_jmp ildCtx ildEntry j [ildCvA, ildCvB, ildLoad] ildJmp ildCvA [ildCvB, ildLoad, ildJmp] s
    (ildEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (ildEntry_thread s) (by simpa [updateVar] using hnh)

theorem ildEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (ildEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (ildEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (ildEntrySEnd s) = some (ildVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (ildVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (ildVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (ildVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

theorem ildNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) ildCtx r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return ildCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem ildNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) ildCtx r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term ildCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- The invariant: unhalted, zero call value, the immutables-in-memory regime link, and at
    `next` the delivered `a, b, c`. -/
def ildInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  ildVal s = mload (EvmYul.UInt256.ofNat 0).toNat s ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (ildVal s))

theorem ildInv_pres : ∀ bb ∈ ildFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    ildInv s → runBlock f' ildCtx bb s = ExecResult.OK s' → s.currentBb = bb.label → ildInv s' := by
  intro bb hbb s s' f' hinv hrun _
  obtain ⟨hnh, hcv, himm, _⟩ := hinv
  simp only [ildFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [ildCvA, ildCvB, ildLoad], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof ildCtx ildEntry 0 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
             [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof ildCtx ildEntry 1 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
             [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof ildCtx ildEntry 2 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
             [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof ildCtx ildEntry 3 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
             [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, ildEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := ildEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        himm, fun _ => ⟨ha0, hb0, hc0⟩⟩
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 ildCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error ildCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 ildCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error ildCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 ildCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof ildCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, ildNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 ildCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof ildCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, ildNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem ildNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg ildFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := ildFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

/-- The **unresolved** ild asm program as a stuck-preserving literal (the o2pc/offsets head key
    9 accumulates the `AsmPush (encodeNumBytes 0)` size and is otherwise kernel-stuck). -/
theorem ild_unresolved :
    executePlan (generateFnPlan ildFn 64 0).get!.1
      = [AsmInst.AsmLabel "entry", AsmInst.AsmOp "CALLVALUE", AsmInst.AsmOp "CALLVALUE",
         AsmInst.AsmPush (encodeNumBytes 0), AsmInst.AsmOp "MLOAD", AsmInst.AsmPushLabel "next",
         AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "next", AsmInst.AsmOp "MUL",
         AsmInst.AsmOp "RETURN"] := rfl

theorem ildFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 ildCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 ildCtx vs
      = runBlocks 10 ildCtx ildFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, ildCtx, ildFn, lookupFunction, fnEntryLabel, ildEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (ildEntrySEnd s0) with hs1
  have hentry : runBlock 9 ildCtx ildEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact ildEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb ildFn.blocks = some ildEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 ildCtx ildFn s0 = runBlocks 9 ildCtx ildFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := ildEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (ildVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (ildEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb ildFn.blocks = some r0Next := rfl
  have hhalt := ildNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (ildVal s0) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 1000000 in
/-- **The ILOAD capstone.** `codegen_correct` for `entry: %a=CV; %b=CV; %c=ILOAD (Lit 0);
    JMP next` / `next: %e=MUL %b %c; RETURN %e %a` at `fnEom = 64`, under the
    immutables-in-memory regime hypothesis `himm : ildVal vs = mload 0 vs` (immutable 0 is
    laid out at memory offset 0 — the honest deploy-time layout contract). ILOAD lowers to
    `MLOAD`; the asm run reuses `asmMload_expand_noSpill_rel` (coverage-free) and `himm`
    transports the loaded word back to the immutables read. The MUL-by-0 successor kills the
    (arbitrary) value. -/
theorem codegen_correct_ildFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (himm : ildVal vs = mload (EvmYul.UInt256.ofNat 0).toNat vs)
    (hrel : venomAsmRel lo (initPlanState 64) vs as) (haspc : as.pc = 0) :
    (match runContext 10 ildCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ ildFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [ildFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [ildEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan ildFn 64 0
      = some ((generateFnPlan ildFn 64 0).get!.1, (generateFnPlan ildFn 64 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel ildFn) ildFn 64 0 "entry" = initPlanState 64 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_invCur ildInv
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel ildFn) ildFn 64 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan ildFn 64 0).get!.1)).2)
    (fuel := 10) (ctx := ildCtx) (fn := ildFn) (fnEom := 64) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan ildFn 64 0).get!.1) (psFinal := (generateFnPlan ildFn 64 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ ildInv_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, himm, fun h => by simp at h⟩
  case _ =>
    intro bb hbb s
    simp only [ildFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, ildEntry, ildCvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [ildFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: fully explicit — label, CV, CV, PUSH0, MLOAD (= the lowered ILOAD), JMP handoff
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, himmS, _⟩ := hinv
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [ildCvA, ildCvB, ildLoad], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof ildCtx ildEntry 1 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
               [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof ildCtx ildEntry 2 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
               [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof ildCtx ildEntry 3 [ildCvA, ildCvB, ildLoad] ildJmp ildCvA
               [ildCvB, ildLoad, ildJmp] s (ildEntrySEnd s) rfl rfl (by decide) hnt (ildEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([ildCvA, ildCvB, ildLoad] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psE := initPlanState 64 with hpsEdef
      set prog := (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2 with ho2pcdef
      have hvrel0 : venomAsmRel lo psE { s with instIdx := 0 } asm := by
        rw [hpsE] at hvrel; exact hvrel
      -- 1: label
      have hbL : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel "entry"]) := by
        rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
        soLabel_sim (offsetToPc := o2pc) lo psE { s with instIdx := 0 } asm prog "entry" hvrel0 hbL
      have hpcA : as1.pc = 1 := by
        rw [show (executePlan [StackOp.SOLabel "entry"]).length = 1 from rfl] at hpc1
        rw [hpc1, hpc0]
      -- 2: CALLVALUE → a
      have hbC1 : asmBlockAt prog as1.pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield1 : (fun (a : AsmState) => a.callCtx.callvalue) as1
          = (fun (v : VenomState) => v.callCtx.callvalue) ({ s with instIdx := 0 } : VenomState) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel1
        show as1.callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as2, hrun2, hrel2, hpc2⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "a")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel1 (by decide) rfl hbC1 (fun h hg => asmStep_callvalue_ok h hg) hfield1
      have hpcB : as2.pc = 2 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      -- 3: CALLVALUE → b
      have hbC2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcB]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield2 : (fun (a : AsmState) => a.callCtx.callvalue) as2
          = (fun (v : VenomState) => v.callCtx.callvalue)
              (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 }) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel2
        show as2.callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as3, hrun3, hrel3, hpc3⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "b")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel2 (by decide) rfl hbC2 (fun h hg => asmStep_callvalue_ok h hg) hfield2
      have hpcC : as3.pc = 3 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc3
        rw [hpc3, hpcB]
      -- 4: PUSH0 (the ILOAD→MLOAD offset)
      have hbP0 : asmBlockAt prog as3.pc (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      obtain ⟨as4, hrun4, hrel4, hpc4⟩ := emitOneInput_sim_lit_append (opc := Opcode.ILOAD)
        (nl := (["a", "b", "c"] : List String)) (v := EvmYul.UInt256.ofNat 0) hrel3 hbP0
      have hpcD : as4.pc = 4 := by
        rw [show (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length = 1 from rfl] at hpc4
        rw [hpc4, hpcC]
      -- 5: MLOAD (expanding, no coverage assumption); himm transports the value
      have hvb : operandVal (updateVar "b" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 })) lo (Operand.Var "b") = some ({ s with instIdx := 0 } : VenomState).callCtx.callvalue :=
        lookupVar_updateVar_self _ _ _
      have hstack4 : as4.stack = (EvmYul.UInt256.ofNat 0) :: ({ s with instIdx := 0 } : VenomState).callCtx.callvalue :: as4.stack.drop 2 := by
        refine venomAsmRel_asmStack_top2 (p := Operand.Var "b")
          (q := Operand.Lit (EvmYul.UInt256.ofNat 0)) hrel4 (base := [Operand.Var "a"]) ?_ hvb rfl
        rfl
      obtain ⟨hml, hrel5⟩ := asmMload_expand_noSpill_rel (lo := lo) (out := "c")
        (offset := EvmYul.UInt256.ofNat 0)
        (rest := ({ s with instIdx := 0 } : VenomState).callCtx.callvalue :: as4.stack.drop 2)
        hrel4 hstack4 (fun _ => rfl)
        (by show (EvmYul.UInt256.ofNat 0).toNat + 32 ≤ 64; decide)
        (by rcases USize.size_eq with h | h <;> (rw [h]; decide))
        (by show ¬ (Operand.Var "c") ∈ [Operand.Var "a", Operand.Var "b", Operand.Lit (EvmYul.UInt256.ofNat 0)]; decide)
      have hltE : as4.pc < prog.length := by rw [hpcD]; decide
      have hgetE : prog.get ⟨as4.pc, hltE⟩ = AsmInst.AsmOp "MLOAD" := by
        conv_lhs => rw [show (⟨as4.pc, hltE⟩ : Fin _) = ⟨4, by decide⟩ from Fin.ext hpcD]
        rfl
      have hstep5 : asmStep o2pc prog as4 = asmMload as4 := asmStep_mload_ok hltE hgetE
      set as5 : AsmState := { asmNext as4 with stack := wordOfBytes ((asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as4.memory).readWithPadding (EvmYul.UInt256.ofNat 0).toNat 32) :: ({ s with instIdx := 0 } : VenomState).callCtx.callvalue :: as4.stack.drop 2, memory := asmExpandMemory ((EvmYul.UInt256.ofNat 0).toNat + 32) as4.memory } with has5
      have hstep5ok : asmStep o2pc prog as4 = AsmResult.AsmOK as5 := by rw [hstep5, hml]
      have hrun5 : runAsm 1 o2pc prog as4 = AsmResult.AsmOK as5 := by
        rw [runAsm_succ_ok hltE hstep5ok]; rfl
      have hpcE2 : as5.pc = 5 := by rw [has5]; show as4.pc + 1 = 5; rw [hpcD]
      -- transport the venom value through the regime hypothesis
      have himm0 : ildVal s = mload (EvmYul.UInt256.ofNat 0).toNat ({ s with instIdx := 0 } : VenomState) := himmS
      have hrel5' : venomAsmRel lo { psE with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] }
          (updateVar "c" (ildVal s)
            (updateVar "b" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue
              (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 }))) as5 := by
        rw [himm0]
        exact hrel5
      -- compose the 5-step body run
      have hrunAll : runAsm (1 + 1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as5 := by
        have hrun1' : runAsm 1 o2pc prog asm = AsmResult.AsmOK as1 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOLabel "entry"]).length from rfl]; exact hrun1
        have hrun2' : runAsm 1 o2pc prog as1 = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOEmit "CALLVALUE"]).length from rfl]; exact hrun2
        have hrun3' : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOEmit "CALLVALUE"]).length from rfl]; exact hrun3
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOPush (Operand.Lit (EvmYul.UInt256.ofNat 0))]).length from rfl]; exact hrun4
        exact runAsm_compose (runAsm_compose (runAsm_compose (runAsm_compose hrun1' hrun2') hrun3') hrun4') hrun5
      have hrunAll5 : runAsm 5 o2pc prog asm = AsmResult.AsmOK as5 := hrunAll
      have hterm := termRecipeW_jmp_of_body (bb := ildEntry) (bb' := r0Next) (lbl := "next")
        (off := 9) (bodyLen := 5) (ctx := ildCtx) (prog := prog) (o2pc := o2pc)
        (fn := ildFn) (lo := lo) (s := s) (as' := as5)
        (front := [ildCvA, ildCvB, ildLoad]) (jmpInst := ildJmp) (hd := ildCvA)
        (tl := [ildCvB, ildLoad, ildJmp]) (restFuel := j)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel ildFn) ildFn 64 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan ildFn 64 0).get!.1)).2)
        rfl rfl rfl rfl (by decide) hnt (ildEntry_thread s)
        (by simpa [updateVar] using hhalt)
        hrel5' rfl (by decide)
        (by rw [hpcE2]; decide)
        (by conv_lhs => rw [show (⟨as5.pc, by rw [hpcE2]; decide⟩ : Fin _) = ⟨5, by decide⟩
              from Fin.ext hpcE2]
            rfl)
        (by have hlit := ild_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [hlit]
            decide)
        (by decide)
        (by rw [hpcE2]; decide)
        (by conv_lhs => rw [show (⟨as5.pc + 1, by rw [hpcE2]; decide⟩ : Fin _) = ⟨6, by decide⟩
              from Fin.ext (show as5.pc + 1 = 6 by omega)]
            rfl)
        (by rw [ho2pcdef, hprogdef,
              show pcOfLabel (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 "next" = 7 from rfl]
            have hlit := ild_unresolved
            rw [encodeNumBytes_zero] at hlit
            rw [show (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).2
                = buildOffsetToPc (executePlan (generateFnPlan ildFn 64 0).get!.1) from rfl, hlit]
            decide) rfl
      exact ⟨as5, _, ildEntrySEnd s, 5, hrunAll5, hterm⟩
    · -- next: the r0 pattern (MUL-by-0 kill + empty RETURN window) at pc 7, fnEom 64
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc7 : asm.pc = 7 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof ildCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel ildFn) ildFn 64 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (ildVal s)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (ildVal s)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (ildVal s)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (ildVal s)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (ildVal s)).2]; exact ha0)
        (hready := ildNext_ready)
        (hsd := ⟨by intro op'; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel ildFn) ildFn 64 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc7]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc7]; decide) (hret := by simp only [hpc7]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨ildEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel ildFn) ildFn 64 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan ildFn 64 0).get!.1)).1.length
      omega

end Example


/-! ## The MEMTOP capstone: the first joint-invariant (recipeW_invJ) consumer -/

namespace Example

/-! ### The MEMTOP capstone `mtp`: `entry: %a=CV; %b=CV; %c=MEMTOP; JMP next` /
    `next = r0Next` (MUL-by-0 kill) at `fnEom = 0`, under empty-initial-memory hypotheses on
    BOTH sides (`vs.memory.size = 0` in the invariant, `as.memory.size = 0` through the
    joint-invariant walk `codegen_correct_ofBlocks_recipeW_invJ`). `memoryRel` deliberately
    carries no size correspondence, so the MSIZE value equality is pinned by the two size
    hypotheses instead — both sides push `roundUp32 0 = 0`. -/

def mtpCvA : Instruction := { id := 0, opcode := Opcode.CALLVALUE, operands := [], outputs := ["a"] }
def mtpCvB : Instruction := { id := 1, opcode := Opcode.CALLVALUE, operands := [], outputs := ["b"] }
def mtpTop : Instruction := { id := 2, opcode := Opcode.MEMTOP, operands := [], outputs := ["c"] }
def mtpJmp : Instruction := { id := 3, opcode := Opcode.JMP, operands := [Operand.Label "next"], outputs := [] }
def mtpEntry : BasicBlock := { label := "entry", instructions := [mtpCvA, mtpCvB, mtpTop, mtpJmp] }
def mtpFn : IrFunction := { name := "main", blocks := [mtpEntry, r0Next] }
def mtpCtx : VenomContext := { functions := [mtpFn], entry := some "main" }

/-- The MEMTOP value: the 32-rounded memory size (matches the semantics' `execRead0` body). -/
abbrev mtpVal (s : VenomState) : bytes32 :=
  EvmYul.UInt256.ofNat ((s.memory.size + 31) / 32 * 32)

abbrev mtpEntrySEnd (s : VenomState) : VenomState :=
  { updateVar "c" (mtpVal s) { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

theorem mtpEntry_thread (s : VenomState) :
    execBodyThread [mtpCvA, mtpCvB, mtpTop] 0 { s with instIdx := 0 } = some (mtpEntrySEnd s) := by
  set S2 : VenomState := { updateVar "b" s.callCtx.callvalue
      { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with hS2
  have hfv : mtpVal S2 = mtpVal s := rfl
  have hsub : stepInstBase mtpTop S2 = ExecResult.OK (updateVar "c" (mtpVal s) S2) := by
    rw [show stepInstBase mtpTop S2
      = ExecResult.OK (updateVar "c" (mtpVal S2) S2) from rfl, hfv]
  have h1 : stepInstBase mtpCvA { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase mtpCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  show (match stepInstBase mtpCvA { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [mtpCvB, mtpTop] 1 { s' with instIdx := 1 } | _ => none)
      = some (mtpEntrySEnd s)
  rw [h1]
  show (match stepInstBase mtpCvB ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [mtpTop] 2 { s' with instIdx := 2 } | _ => none)
      = some (mtpEntrySEnd s)
  rw [h2]
  show (match stepInstBase mtpTop S2 with
        | ExecResult.OK s' => execBodyThread [] 3 { s' with instIdx := 3 } | _ => none)
      = some (mtpEntrySEnd s)
  rw [hsub]; rfl

theorem mtpEntry_runBlock (s : VenomState) (j : Nat) (hnh : s.halted = false) :
    runBlock (3 + (j + 1)) mtpCtx mtpEntry s = ExecResult.OK (jumpTo "next" (mtpEntrySEnd s)) :=
  runBlock_body_jmp mtpCtx mtpEntry j [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA [mtpCvB, mtpTop, mtpJmp] s
    (mtpEntrySEnd s) "next" rfl rfl rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
    (mtpEntry_thread s) (by simpa [updateVar] using hnh)

theorem mtpEntrySEnd_lookup (s : VenomState) :
    lookupVar "a" (mtpEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "b" (mtpEntrySEnd s) = some s.callCtx.callvalue
    ∧ lookupVar "c" (mtpEntrySEnd s) = some (mtpVal s) := by
  refine ⟨?_, ?_, ?_⟩
  · show lookupVar "a" (updateVar "c" (mtpVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "b" (updateVar "c" (mtpVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  · show lookupVar "c" (updateVar "c" (mtpVal s) (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]

theorem mtpNext_halts (s : VenomState) (j : Nat) (wb wc wa : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = some wa) :
    runBlock (1 + (j + 1)) mtpCtx r0Next s = ExecResult.Halt
      (haltState (setReturndata (readMemory (wb * wc).toNat wa.toNat (r0NextSEnd s wb wc)) (r0NextSEnd s wb wc))) := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  exact runBlock_body_return mtpCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (Operand.Var "e") (Operand.Var "a") (wb * wc) wa rfl rfl rfl he haa rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc)

theorem mtpNext_error_a (s : VenomState) (j : Nat) (wb wc : bytes32)
    (hb : lookupVar "b" s = some wb) (hc : lookupVar "c" s = some wc) (ha : lookupVar "a" s = none) :
    runBlock (1 + (j + 1)) mtpCtx r0Next s = ExecResult.Error "return: undefined operand" := by
  obtain ⟨he, haa⟩ := r0NextSEnd_lookup s wb wc
  rw [ha] at haa
  refine runBlock_body_term mtpCtx r0Next j [r0Mul] r0Ret r0Mul [r0Ret] s (r0NextSEnd s wb wc)
    (ExecResult.Error "return: undefined operand") rfl rfl (by decide)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
    (r0Next_thread s wb wc hb hc) ?_
  intro inst hget
  simp [execBlock, getInstruction_bodyEnd (by rfl : r0Next.instructions = [r0Mul] ++ [r0Ret])
    (r0Next_thread s wb wc hb hc), r0Ret, stepInstBase, evalOperand, he, haa, isExternalCall]

/-- The Venom-side invariant: unhalted, zero call value, EMPTY MEMORY at entry, and at `next`
    the delivered all-zero `a, b, c` (`c = roundUp32 0 = 0`). -/
def mtpInv (s : VenomState) : Prop :=
  s.halted = false ∧ s.callCtx.callvalue = EvmYul.UInt256.ofNat 0 ∧
  (s.currentBb = "entry" → s.memory.size = 0) ∧
  (s.currentBb = "next" → lookupVar "a" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "b" s = some (EvmYul.UInt256.ofNat 0)
                        ∧ lookupVar "c" s = some (EvmYul.UInt256.ofNat 0))

/-- The JOINT invariant: the block-entry ASM memory is empty while at `entry` — self-vacuifying
    after the transition, so its walk-preservation never inspects the asm run. -/
def mtpInv2 (s : VenomState) (a : AsmState) : Prop :=
  s.currentBb = "entry" → a.memory.size = 0

theorem mtpInv_pres : ∀ bb ∈ mtpFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mtpInv s → runBlock f' mtpCtx bb s = ExecResult.OK s' → s.currentBb = bb.label → mtpInv s' := by
  intro bb hbb s s' f' hinv hrun hcur
  obtain ⟨hnh, hcv, hsz, _⟩ := hinv
  simp only [mtpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [mtpCvA, mtpCvB, mtpTop], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 0 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 1 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 2 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 3 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, mtpEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      obtain ⟨ha0, hb0, hc0⟩ := mtpEntrySEnd_lookup s
      rw [hcv] at ha0 hb0
      have hszs : s.memory.size = 0 := hsz hcur
      have hc0' : lookupVar "c" (mtpEntrySEnd s) = some (EvmYul.UInt256.ofNat 0) := by
        rw [hc0, show mtpVal s = EvmYul.UInt256.ofNat 0 from by rw [mtpVal, hszs]]
      refine ⟨by simpa [jumpTo, updateVar] using hnh, by simp [jumpTo, updateVar, hcv],
        fun h => by simp [jumpTo] at h, fun _ => ⟨ha0, hb0, hc0'⟩⟩
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error mtpCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error mtpCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mtpNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mtpNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

/-- The joint invariant survives every block (asm-blind): entry's only OK exit re-tags
    `currentBb` to `"next"`, killing the guard; `next` never returns OK. -/
theorem mtpInv2_pres : ∀ bb ∈ mtpFn.blocks, ∀ (s s' : VenomState) (f' : Nat),
    mtpInv s → runBlock f' mtpCtx bb s = ExecResult.OK s' → s.currentBb = bb.label →
    ∀ a : AsmState, mtpInv2 s' a := by
  intro bb hbb s s' f' hinv hrun hcur a
  obtain ⟨hnh, _, _, _⟩ := hinv
  simp only [mtpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
  rcases hbb with rfl | rfl
  · have hnt : ∀ inst ∈ [mtpCvA, mtpCvB, mtpTop], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    match f' with
    | 0 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 0 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 1 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 2 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 2 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | 3 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx mtpEntry 3 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
             [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide)
           rw [he] at hrun; exact absurd hrun (by simp)
    | (j+4) =>
      rw [show j+4 = 3+(j+1) from by omega, mtpEntry_runBlock s j hnh] at hrun
      injection hrun with h; subst h
      intro h; simp [jumpTo] at h
  · rcases hlb : lookupVar "b" s with _ | wb
    · match f' with
      | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
             simp [execBlock] at hrun
      | (j+1) =>
        rw [runBlock_body_head_error mtpCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
          (by decide) (r0Mul_error_b s hlb) (by decide) (by decide)] at hrun
        exact absurd hrun (by simp)
    · rcases hlc : lookupVar "c" s with _ | wc
      · match f' with
        | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
               simp [execBlock] at hrun
        | (j+1) =>
          rw [runBlock_body_head_error mtpCtx r0Next r0Mul [r0Ret] s "undefined operand" j rfl
            (by decide) (r0Mul_error_c s wb hlb hlc) (by decide) (by decide)] at hrun
          exact absurd hrun (by simp)
      · rcases hla : lookupVar "a" s with _ | wa
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mtpNext_error_a s j wb wc hlb hlc hla] at hrun
            exact absurd hrun (by simp)
        · match f' with
          | 0 => rw [runBlock_no_phi 0 mtpCtx r0Next s r0Mul [r0Ret] rfl (by decide)] at hrun
                 simp [execBlock] at hrun
          | 1 => obtain ⟨e, he⟩ := runBlock_oof mtpCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
                   (r0NextSEnd s wb wc) rfl rfl (by decide)
                   (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
                   (r0Next_thread s wb wc hlb hlc) (by decide)
                 rw [he] at hrun; exact absurd hrun (by simp)
          | (j+2) =>
            rw [show j+2 = 1+(j+1) from by omega, mtpNext_halts s j wb wc wa hlb hlc hla] at hrun
            exact absurd hrun (by simp)

theorem mtpNext_ready {lo : AssocList String Nat} :
    BodyStepsReadyHTo lo (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2
      (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1
      (fun z p => generateRegularInstPlan exLiveness DfgAnalysis.empty exCfg mtpFn z.1
        ["e", "a"] false true "next" p)
      (fun _ => 1) ([r0Mul].zipIdx 0) ["a", "b", "c"] ["a", "e"] :=
  bodyStepsReadyHTo_singleton
    (bodyStepHTo_commBinopDeadMirror (liveness := exLiveness) (dfg := DfgAnalysis.empty)
      (cfg := exCfg) (fn := mtpFn) (curBbLabel := "next") (base := ["a"]) (x := "b") (y := "c")
      (out := "e") (idx := 0)
      rfl (by decide) bytes32_mul_comm (fun _ => rfl) rfl rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun _ h hg => asmStep_mul_ok h hg))

theorem mtpFn_halts (vs : VenomState) (hnh : vs.halted = false)
    (hcv : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0) :
    ∃ vs', runContext 10 mtpCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 mtpCtx vs
      = runBlocks 10 mtpCtx mtpFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, mtpCtx, mtpFn, lookupFunction, fnEntryLabel, mtpEntry]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hnh0 : s0.halted = false := by simpa [hs0] using hnh
  have hcv0 : s0.callCtx.callvalue = EvmYul.UInt256.ofNat 0 := by simpa [hs0] using hcv
  set s1 : VenomState := jumpTo "next" (mtpEntrySEnd s0) with hs1
  have hentry : runBlock 9 mtpCtx mtpEntry s0 = ExecResult.OK s1 := by
    rw [show (9 : Nat) = 3 + (5 + 1) from by omega]; exact mtpEntry_runBlock s0 5 hnh0
  have hlk0 : lookupBlock s0.currentBb mtpFn.blocks = some mtpEntry := rfl
  have hnh1 : s1.halted = false := by rw [hs1]; simpa [jumpTo, updateVar] using hnh0
  have hstep0 : runBlocks 10 mtpCtx mtpFn s0 = runBlocks 9 mtpCtx mtpFn s1 :=
    runBlocks_step_of_block (fuel := 9) hlk0 hentry hnh1
  obtain ⟨ha1, hb1, hc1⟩ := mtpEntrySEnd_lookup s0
  rw [hcv0] at ha1 hb1
  have ha1' : lookupVar "a" s1 = some (EvmYul.UInt256.ofNat 0) := ha1
  have hb1' : lookupVar "b" s1 = some (EvmYul.UInt256.ofNat 0) := hb1
  have hc1' : lookupVar "c" s1 = some (mtpVal s0) := by
    rw [show lookupVar "c" s1 = lookupVar "c" (mtpEntrySEnd s0) from rfl, hc1]
  have hlk1 : lookupBlock s1.currentBb mtpFn.blocks = some r0Next := rfl
  have hhalt := mtpNext_halts s1 6 (EvmYul.UInt256.ofNat 0) (mtpVal s0) (EvmYul.UInt256.ofNat 0) hb1' hc1' ha1'
  rw [show (1 : Nat) + (6 + 1) = 8 from by omega] at hhalt
  rw [h0, hstep0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk1 hhalt⟩

set_option maxHeartbeats 1000000 in
/-- **The MEMTOP capstone.** `codegen_correct` for `entry: %a=CV; %b=CV; %c=MEMTOP; JMP next` /
    `next: %e=MUL %b %c; RETURN %e %a` under empty-initial-memory hypotheses on both sides.
    `memoryRel` carries no size correspondence, so this is the first capstone through
    `codegen_correct_ofBlocks_recipeW_invJ`: the asm-side `as.memory.size = 0` rides the
    self-vacuifying joint invariant `mtpInv2`, the venom side rides `mtpInv`, and the MSIZE
    push value-equality is discharged by the two pins (`roundUp32 0` on both sides) via
    `emit_ctx_push_sim_mem` (the CV pushes' memory-preservation keeps the asm pin usable at
    the MSIZE step). -/
theorem codegen_correct_mtpFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false) (hzero : vs.callCtx.callvalue = EvmYul.UInt256.ofNat 0)
    (hvs0 : vs.memory.size = 0) (has0 : as.memory.size = 0)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 mtpCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ mtpFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [mtpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp only [mtpEntry, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
    · simp only [r0Next, List.mem_cons, List.not_mem_nil, or_false] at hinst
      rcases hinst with rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan mtpFn 0 0
      = some ((generateFnPlan mtpFn 0 0).get!.1, (generateFnPlan mtpFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel mtpFn) mtpFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_invJ mtpInv mtpInv2
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel mtpFn) mtpFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := mtpCtx) (fn := mtpFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan mtpFn 0 0).get!.1) (psFinal := (generateFnPlan mtpFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ mtpInv_pres mtpInv2_pres ?_
    ⟨by simpa using hvshalt, by simpa using hzero, fun _ => by simpa using hvs0, fun h => by simp at h⟩
    (fun _ => has0)
  case _ =>
    intro bb hbb s
    simp only [mtpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · simp [runBlock, evalPhis, execBlock, mtpEntry, mtpCvA]
    · simp [runBlock, evalPhis, execBlock, r0Next, r0Mul]
  case _ =>
    intro bb hbb s asm N k hE hinv hinv2 hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [mtpFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    rcases hbb with rfl | rfl
    · -- entry: fully explicit — label, CV, CV, MSIZE (both sizes pinned to 0), JMP handoff
      have hlbl : s.currentBb = "entry" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, hszV', _⟩ := hinv
      have hszV : s.memory.size = 0 := hszV' hlbl
      have hszA : asm.memory.size = 0 := hinv2 hlbl
      have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
      have hnt : ∀ inst ∈ [mtpCvA, mtpCvB, mtpTop], isTerminator inst.opcode = false := by
        intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mtpCtx mtpEntry 1 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
               [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide))
      | 1 => exact Or.inl (runBlock_oof mtpCtx mtpEntry 2 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
               [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide))
      | 2 => exact Or.inl (runBlock_oof mtpCtx mtpEntry 3 [mtpCvA, mtpCvB, mtpTop] mtpJmp mtpCvA
               [mtpCvB, mtpTop, mtpJmp] s (mtpEntrySEnd s) rfl rfl (by decide) hnt (mtpEntry_thread s) (by decide))
      | (j+3) =>
      rw [show j+3+1 = ([mtpCvA, mtpCvB, mtpTop] : List Instruction).length + (j+1) from by
        simp only [List.length_cons, List.length_nil]; omega]
      right
      set psE := initPlanState 0 with hpsEdef
      set prog := (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 with hprogdef
      set o2pc := (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2 with ho2pcdef
      have hvrel0 : venomAsmRel lo psE { s with instIdx := 0 } asm := by
        rw [hpsE] at hvrel; exact hvrel
      -- 1: label (explicit, to keep the asm memory identity)
      have hltL : asm.pc < prog.length := by rw [hpc0]; decide
      have hgetL : prog.get ⟨asm.pc, hltL⟩ = AsmInst.AsmLabel "entry" := by
        conv_lhs => rw [show (⟨asm.pc, hltL⟩ : Fin _) = ⟨0, by decide⟩ from Fin.ext hpc0]
        rfl
      have hrun1 : runAsm 1 o2pc prog asm = AsmResult.AsmOK (asmNext asm) := by
        rw [runAsm_succ_ok hltL (asmStep_label_ok hltL hgetL)]; rfl
      have hrel1 : venomAsmRel lo psE { s with instIdx := 0 } (asmNext asm) := hvrel0
      have hpcA : (asmNext asm).pc = 1 := by show asm.pc + 1 = 1; rw [hpc0]
      -- 2: CALLVALUE → a (memory-preserving form)
      have hbC1 : asmBlockAt prog (asmNext asm).pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcA]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield1 : (fun (a : AsmState) => a.callCtx.callvalue) (asmNext asm)
          = (fun (v : VenomState) => v.callCtx.callvalue) ({ s with instIdx := 0 } : VenomState) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel1
        show (asmNext asm).callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as2, hrun2, hrel2, hpc2, hmem2⟩ := emit_ctx_push_sim_mem (name := "CALLVALUE") (out := "a")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel1 (by decide) rfl hbC1 (fun h hg => asmStep_callvalue_ok h hg) hfield1
      have hpcB : as2.pc = 2 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc2
        rw [hpc2, hpcA]
      -- 3: CALLVALUE → b
      have hbC2 : asmBlockAt prog as2.pc (executePlan [StackOp.SOEmit "CALLVALUE"]) := by
        rw [hpcB]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hfield2 : (fun (a : AsmState) => a.callCtx.callvalue) as2
          = (fun (v : VenomState) => v.callCtx.callvalue)
              (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 }) := by
        obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel2
        show as2.callCtx.callvalue = _
        rw [hCall]
      obtain ⟨as3, hrun3, hrel3, hpc3, hmem3⟩ := emit_ctx_push_sim_mem (name := "CALLVALUE") (out := "b")
        (fAsm := fun a => a.callCtx.callvalue) (fV := fun v => v.callCtx.callvalue)
        hrel2 (by decide) rfl hbC2 (fun h hg => asmStep_callvalue_ok h hg) hfield2
      have hpcC : as3.pc = 3 := by
        rw [show (executePlan [StackOp.SOEmit "CALLVALUE"]).length = 1 from rfl] at hpc3
        rw [hpc3, hpcB]
      -- 4: MSIZE (both sizes pinned to 0 through the memory-preserving chain)
      have hbM : asmBlockAt prog as3.pc (executePlan [StackOp.SOEmit "MSIZE"]) := by
        rw [hpcC]; refine ⟨by decide, fun j hj => ?_⟩
        have hj2 : j < 1 := hj; interval_cases j; rfl
      have hm3 : as3.memory = asm.memory := by rw [hmem3, hmem2]; rfl
      have hfield3 : (fun (a : AsmState) => EvmYul.UInt256.ofNat ((a.memory.size + 31) / 32 * 32)) as3
          = (fun (v : VenomState) => EvmYul.UInt256.ofNat ((v.memory.size + 31) / 32 * 32))
              (updateVar "b" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue
                (updateVar "a" ({ s with instIdx := 0 } : VenomState).callCtx.callvalue { s with instIdx := 0 })) := by
        show EvmYul.UInt256.ofNat ((as3.memory.size + 31) / 32 * 32)
          = EvmYul.UInt256.ofNat ((s.memory.size + 31) / 32 * 32)
        rw [hm3, hszA, hszV]
      obtain ⟨as4, hrun4, hrel4, hpc4, hmem4⟩ := emit_ctx_push_sim_mem (name := "MSIZE") (out := "c")
        (fAsm := fun a => EvmYul.UInt256.ofNat ((a.memory.size + 31) / 32 * 32))
        (fV := fun v => EvmYul.UInt256.ofNat ((v.memory.size + 31) / 32 * 32))
        hrel3 (by decide) rfl hbM (fun h hg => asmStep_msize_ok h hg) hfield3
      have hpcD : as4.pc = 4 := by
        rw [show (executePlan [StackOp.SOEmit "MSIZE"]).length = 1 from rfl] at hpc4
        rw [hpc4, hpcC]
      -- compose the 4-step body run
      have hrunAll : runAsm (1 + 1 + 1 + 1) o2pc prog asm = AsmResult.AsmOK as4 := by
        have hrun2' : runAsm 1 o2pc prog (asmNext asm) = AsmResult.AsmOK as2 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOEmit "CALLVALUE"]).length from rfl]; exact hrun2
        have hrun3' : runAsm 1 o2pc prog as2 = AsmResult.AsmOK as3 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOEmit "CALLVALUE"]).length from rfl]; exact hrun3
        have hrun4' : runAsm 1 o2pc prog as3 = AsmResult.AsmOK as4 := by
          rw [show (1 : Nat) = (executePlan [StackOp.SOEmit "MSIZE"]).length from rfl]; exact hrun4
        exact runAsm_compose (runAsm_compose (runAsm_compose hrun1 hrun2') hrun3') hrun4'
      have hrunAll4 : runAsm 4 o2pc prog asm = AsmResult.AsmOK as4 := hrunAll
      have hterm := termRecipeW_jmp_of_body (bb := mtpEntry) (bb' := r0Next) (lbl := "next")
        (off := 8) (bodyLen := 4) (ctx := mtpCtx) (prog := prog) (o2pc := o2pc)
        (fn := mtpFn) (lo := lo) (s := s) (as' := as4)
        (front := [mtpCvA, mtpCvB, mtpTop]) (jmpInst := mtpJmp) (hd := mtpCvA)
        (tl := [mtpCvB, mtpTop, mtpJmp]) (restFuel := j)
        (pcOf := pcOfLabel prog) (psOf := psOfFn (fnPlanFuel mtpFn) mtpFn 0 0)
        (wOf := fun l => prog.length - pcOfLabel prog l)
        (offsets := (computeLabelOffsets (executePlan (generateFnPlan mtpFn 0 0).get!.1)).2)
        rfl rfl rfl rfl (by decide) hnt (mtpEntry_thread s)
        (by simpa [updateVar] using hhalt)
        hrel4 rfl (by decide)
        (by rw [hpcD]; decide)
        (by conv_lhs => rw [show (⟨as4.pc, by rw [hpcD]; decide⟩ : Fin _) = ⟨4, by decide⟩
              from Fin.ext hpcD]
            rfl)
        (by decide)
        (by decide)
        (by rw [hpcD]; decide)
        (by conv_lhs => rw [show (⟨as4.pc + 1, by rw [hpcD]; decide⟩ : Fin _) = ⟨5, by decide⟩
              from Fin.ext (show as4.pc + 1 = 5 by omega)]
            rfl)
        (by decide) rfl
      exact ⟨as4, _, mtpEntrySEnd s, 4, hrunAll4, hterm⟩
    · -- next: the r0 pattern at pc 6, all-zero triple
      have hlbl : s.currentBb = "next" := hlbleq
      rw [hlbl] at hvrel hpc_asm
      obtain ⟨_, _, _, hnext⟩ := hinv
      obtain ⟨ha0, hb0, hc0⟩ := hnext hlbl
      have hpc6 : asm.pc = 6 := by rw [hpc_asm]; decide
      match k with
      | 0 => exact Or.inl (runBlock_oof mtpCtx r0Next 1 [r0Mul] r0Ret r0Mul [r0Ret] s
               (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) rfl rfl (by decide)
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
        (ps0 := psOfFn (fnPlanFuel mtpFn) mtpFn 0 0 "next") (offv := "e") (szv := "a") (base := [])
        (woff := EvmYul.UInt256.ofNat 0) (wsz := EvmYul.UInt256.ofNat 0)
        (sEnd := r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
        (hbb := rfl) (hop := rfl) (hoperands := rfl) (hcons := rfl) (hphi := by decide)
        (hnonterm := by intro i hi; simp only [List.mem_singleton] at hi; subst hi; decide)
        (hthread := r0Next_thread s _ _ hb0 hc0)
        (hevaloff := by rw [show evalOperand (Operand.Var "e")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hevalsz := by rw [show evalOperand (Operand.Var "a")
              (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0))
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hvoff := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "e")
            = lookupVar "e" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).1, uint256_zero_mul])
        (hvsz := by rw [show operandVal (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) lo
              (Operand.Var "a")
            = lookupVar "a" (r0NextSEnd s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)) from rfl,
            (r0NextSEnd_lookup s (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)).2]; exact ha0)
        (hready := mtpNext_ready)
        (hsd := ⟨by intro op'; rfl, by decide, by
          intro z hz
          rw [show (psOfFn (fnPlanFuel mtpFn) mtpFn 0 0 "next").stack
            = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from rfl] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h <;> injection h with h' <;> subst h'
          · exact ⟨_, ha0⟩
          · exact ⟨_, hb0⟩
          · exact ⟨_, hc0⟩⟩)
        (hsv := rfl)
        (hrel := hvrel)
        (hbLabel := by rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
                       have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hblock := by rw [hpc6]; refine ⟨by decide, fun j hj => ?_⟩
                      have hj2 : j < 1 := hj; interval_cases j; rfl)
        (hps'stack := by decide)
        (hpc := by rw [hpc6]; decide) (hret := by simp only [hpc6]; rfl)
        (hcov0 := Or.inl (by simp [EvmYul.uint256_ofNat_toNat]))
        (hbelow := by simp [EvmYul.uint256_ofNat_toNat])
        (hlenu := by simp [EvmYul.uint256_ofNat_toNat]) (hw := by decide))
  case _ =>
    refine ⟨⟨mtpEntry, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel mtpFn) mtpFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan mtpFn 0 0).get!.1)).1.length
      omega

end Example


/-! ## f1a stage 1: the buried-consume plan decompositions (`deadBuriedFn`)

The concrete plan-level equations for the swap-threading route (status.md f1a; see the
f1a memory scoping): the third CALLVALUE's non-noop `optimisticSwapPlan`, the buried
pair's two-swap reorder (and the losing branch of the cheaper-order comparison), and
the two consuming decompositions `d = ADD %a %b` / `SSTORE %c %d` they feed. The sim
layer (doSwap_sim-based fold steps) and the `deadBuriedFn` capstone build on these. -/

namespace Example

/-- The real dataflow analysis of `deadBuriedFn` (the optimistic-swap oracle). -/
def dbDfg : DfgAnalysis := DfgAnalysis.buildFunction deadBuriedFn

/-- **The third CALLVALUE's optimistic swap fires** — output `c` differs from the next
    scheduled var `b` (`operandEquiv` decides on the concrete dfg), which sits at depth 1, so
    the generator pre-positions it with one `SWAP1`. The concrete non-noop `optimisticSwapPlan`
    equation the f1a fold steps consume in place of the usual `hoptnoop`. -/
theorem optimisticSwapPlan_dCv0 (ps : PlanState)
    (hstack : ps.stack = [Operand.Var "a", Operand.Var "b", Operand.Var "c"]) :
    optimisticSwapPlan dbDfg dCv0 ["c", "a", "b"] false ps
      = ([StackOp.SOSwap 1], { ps with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }) := by
  have hd : stackGetDepth (Operand.Var "b") ps.stack = some 1 := by rw [hstack]; rfl
  have hsw : stackSwap 1 ps.stack = [Operand.Var "a", Operand.Var "c", Operand.Var "b"] := by
    rw [hstack]; rfl
  unfold optimisticSwapPlan
  simp [show dCv0.outputs.isEmpty = false from rfl, hd, doSwap, hsw]
  decide

/-- **The buried-pair reorder** — targets `[b, a]` on the post-optimism stack `[a, c, b]`:
    `b` (TOS) goes to depth 1 (`SWAP1`), then `a` (depth 2) comes to the top (`SWAP2`), leaving
    `[c, b, a]` with the pair positioned for a bare consume. Cost 2. -/
theorem reorderPlan_dbBuried (ps : PlanState)
    (hstack : ps.stack = [Operand.Var "a", Operand.Var "c", Operand.Var "b"]) :
    reorderPlan [Operand.Var "b", Operand.Var "a"] ps
      = ([StackOp.SOSwap 1, StackOp.SOSwap 2], { ps with stack := [Operand.Var "c", Operand.Var "b", Operand.Var "a"] }) := by
  have hstep0 : reorderOne () [Operand.Var "b", Operand.Var "a"] 0 (Operand.Var "b") ps
      = ([StackOp.SOSwap 1], { ps with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] }) := by
    have hd : stackGetDepth (Operand.Var "b") ps.stack = some 0 := by rw [hstack]; rfl
    have hsw : stackSwap 1 ps.stack = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] := by
      rw [hstack]; rfl
    unfold reorderOne
    simp [hd, doSwap, hsw]
    try rfl
  have hstep1 : reorderOne () [Operand.Var "b", Operand.Var "a"] 1 (Operand.Var "a")
      ({ ps with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] } : PlanState)
      = ([StackOp.SOSwap 2], { ps with stack := [Operand.Var "c", Operand.Var "b", Operand.Var "a"] }) := by
    have hd : stackGetDepth (Operand.Var "a")
        (({ ps with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] } : PlanState)).stack = some 2 := rfl
    unfold reorderOne
    simp [hd, doSwap]
    try rfl
  unfold reorderPlan
  have henum : ([Operand.Var "b", Operand.Var "a"] : List Operand).enum
      = [(0, Operand.Var "b"), (1, Operand.Var "a")] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.nil_append]
  try rfl

/-- **The losing branch of the commutative cheaper-order choice** — targets `[a, b]` on
    `[a, c, b]` cost 3 (`SWAP2;SWAP1;SWAP2`), so the generator's `reorderCost` comparison
    (2 < 3) picks the `computeOperands` order `[b, a]` and hence the TRUE evaluation order. -/
theorem reorderPlan_dbBuried_swapped (ps : PlanState)
    (hstack : ps.stack = [Operand.Var "a", Operand.Var "c", Operand.Var "b"]) :
    reorderPlan [Operand.Var "a", Operand.Var "b"] ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1, StackOp.SOSwap 2], { ps with stack := [Operand.Var "c", Operand.Var "a", Operand.Var "b"] }) := by
  have hstep0 : reorderOne () [Operand.Var "a", Operand.Var "b"] 0 (Operand.Var "a") ps
      = ([StackOp.SOSwap 2, StackOp.SOSwap 1], { ps with stack := [Operand.Var "b", Operand.Var "a", Operand.Var "c"] }) := by
    have hd : stackGetDepth (Operand.Var "a") ps.stack = some 2 := by rw [hstack]; rfl
    have hsw2 : stackSwap 2 ps.stack = [Operand.Var "b", Operand.Var "c", Operand.Var "a"] := by
      rw [hstack]; rfl
    unfold reorderOne
    simp [hd, doSwap, hsw2]
    try rfl
  have hstep1 : reorderOne () [Operand.Var "a", Operand.Var "b"] 1 (Operand.Var "b")
      ({ ps with stack := [Operand.Var "b", Operand.Var "a", Operand.Var "c"] } : PlanState)
      = ([StackOp.SOSwap 2], { ps with stack := [Operand.Var "c", Operand.Var "a", Operand.Var "b"] }) := by
    have hd : stackGetDepth (Operand.Var "b")
        (({ ps with stack := [Operand.Var "b", Operand.Var "a", Operand.Var "c"] } : PlanState)).stack = some 2 := rfl
    unfold reorderOne
    simp [hd, doSwap]
    try rfl
  unfold reorderPlan
  have henum : ([Operand.Var "a", Operand.Var "b"] : List Operand).enum
      = [(0, Operand.Var "a"), (1, Operand.Var "b")] := rfl
  rw [henum]
  simp only [List.foldl_cons, List.foldl_nil, hstep0, hstep1, List.nil_append]
  try rfl

/-- **The buried commutative consume, decomposed** — `d = ADD %a %b` on the post-optimism stack
    `[a, c, b]`, both operands dead-unspilled: emission is empty, the cheaper-order comparison
    picks `computeOperands` (`[b, a]`, cost 2 vs 3 — TRUE evaluation order, no `hfcomm`), the
    reorder is `SWAP1;SWAP2`, and the consume leaves `[c, d]`. The buried sibling of
    `genRegularInstPlan_commBinopPair_eq`, with the reorder resolved by `reorderPlan_dbBuried`
    instead of `reorderPlan_pair_nil`. -/
theorem genRegularInstPlan_dAdd_buried_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    (hstack : ps.stack = [Operand.Var "a", Operand.Var "c", Operand.Var "b"])
    (hnsa : alookup' ps.spilled (Operand.Var "a") = none)
    (hnsb : alookup' ps.spilled (Operand.Var "b") = none) :
    generateRegularInstPlan liveness dfg cfg fn dAdd ["c", "d"] isHalting nextIsTerminator curBbLabel ps
      = ([StackOp.SOSwap 1, StackOp.SOSwap 2, StackOp.SOEmit "ADD"]
           ++ (optimisticSwapPlan dfg dAdd ["c", "d"] nextIsTerminator { ps with stack := [Operand.Var "c", Operand.Var "d"] }).1,
         releaseDeadSpills ["c", "d"]
           (optimisticSwapPlan dfg dAdd ["c", "d"] nextIsTerminator { ps with stack := [Operand.Var "c", Operand.Var "d"] }).2) := by
  have hemit : emitInputPlan Opcode.ADD [Operand.Var "b", Operand.Var "a"] ["c", "d"] ps = ([], ps) :=
    emitInputPlan_pair_dead_eq hnsb (by decide) hnsa (by decide)
  have hro := reorderPlan_dbBuried ps hstack
  have hro2 := reorderPlan_dbBuried_swapped ps hstack
  unfold generateRegularInstPlan
  cases isHalting <;>
    simp [show computeOperands dAdd = [Operand.Var "b", Operand.Var "a"] from rfl,
      show dAdd.opcode = Opcode.ADD from rfl, show dAdd.outputs = ["d"] from rfl,
      hemit, hro, hro2, reorderCost, popmanyPlan_nil, stackPop, stackPush,
      generateEmitOps_evmName (show opcodeToEvmName dAdd.opcode = some "ADD" from rfl),
      isCommutative]

/-- **The swapped dead SSTORE, decomposed** — `SSTORE %c %d` on `[c, d]`, both dead-unspilled,
    empty next-liveness: emission empty, the (non-commutative) reorder to `[d, c]` is one
    `SWAP1` (`reorderPlan_swapped_pair`), the store consumes both. -/
theorem genRegularInstPlan_dStore_swapped_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {isHalting nextIsTerminator : Bool} {curBbLabel : String} {ps : PlanState}
    (hstack : ps.stack = [Operand.Var "c", Operand.Var "d"])
    (hnsc : alookup' ps.spilled (Operand.Var "c") = none)
    (hnsd : alookup' ps.spilled (Operand.Var "d") = none) :
    generateRegularInstPlan liveness dfg cfg fn dStore [] isHalting nextIsTerminator curBbLabel ps
      = ([StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"], releaseDeadSpills [] { ps with stack := [] }) := by
  have hemit : emitInputPlan Opcode.SSTORE [Operand.Var "d", Operand.Var "c"] [] ps = ([], ps) :=
    emitInputPlan_pair_dead_eq hnsd (by decide) hnsc (by decide)
  have hro := reorderPlan_swapped_pair [] (Operand.Var "c") (Operand.Var "d") ps (by simpa using hstack)
  unfold generateRegularInstPlan
  simp [show computeOperands dStore = [Operand.Var "d", Operand.Var "c"] from rfl,
    show dStore.opcode = Opcode.SSTORE from rfl, show dStore.outputs = ([] : List String) from rfl,
    hemit, hro, stackPop, isCommutative,
    generateEmitOps_evmName (show opcodeToEvmName dStore.opcode = some "SSTORE" from rfl)]

end Example


namespace Example

/-! ### f1a stage 2: the `deadBuriedFn` fold steps (aux layer) -/

/-- The real liveness analysis of `deadBuriedFn`. -/
abbrev dbLive : DfState (List String) := livenessAnalyzeFuel (fnPlanFuel deadBuriedFn) deadBuriedFn
/-- The real cfg analysis of `deadBuriedFn`. -/
abbrev dbCfg : CfgAnalysis := cfgAnalyze deadBuriedFn
/-- Per-index next-liveness table (probed against the real generator). -/
abbrev dbNl : Nat → List String
  | 0 => ["a"] | 1 => ["a", "b"] | 2 => ["c", "a", "b"] | 3 => ["c", "d"] | _ => []
/-- Per-index next-is-terminator table (the STOP follows index 4). -/
abbrev dbNt : Nat → Bool := fun i => decide (i = 4)
/-- The per-index fold step: the REAL generator call, per-instruction liveness included. -/
abbrev dbGp : Instruction × Nat → PlanState → List StackOp × PlanState :=
  fun z p => generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn z.1 (dbNl z.2) true (dbNt z.2) "entry" p

/-- `isHalting` only gates the dead-output pop; with the single output LIVE both branches are
    nil, so the halting flag is irrelevant to the generated plan. -/
theorem gRIP_halting_live_eq
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {inst : Instruction} {nl : List String} {nt : Bool} {lbl : String} {p : PlanState} {out : String}
    (houts : inst.outputs = [out]) (hlive : nl.contains out = true) :
    generateRegularInstPlan liveness dfg cfg fn inst nl true nt lbl p
      = generateRegularInstPlan liveness dfg cfg fn inst nl false nt lbl p := by
  have hmem : out ∈ nl := by simpa using hlive
  unfold generateRegularInstPlan
  simp [houts, hlive, hmem, popmanyPlan_nil]

/-- CV#1's optimistic swap is a no-op (`a` is both the output and the next scheduled var). -/
theorem optimisticSwapPlan_dCv1_noop (p : PlanState) :
    optimisticSwapPlan dbDfg dCv1 ["a"] false p = ([], p) := by
  unfold optimisticSwapPlan
  simp [show dCv1.outputs.getLast?.getD "" = "a" from rfl,
    show operandEquiv dbDfg (Operand.Var "a") (Operand.Var "a") = true from by decide,
    show dCv1.outputs.isEmpty = false from rfl]

/-- CV#2's optimistic swap is a no-op (`b` is both the output and the next scheduled var). -/
theorem optimisticSwapPlan_dCv2_noop (p : PlanState) :
    optimisticSwapPlan dbDfg dCv2 ["a", "b"] false p = ([], p) := by
  unfold optimisticSwapPlan
  simp [show dCv2.outputs.getLast?.getD "" = "b" from rfl,
    show operandEquiv dbDfg (Operand.Var "b") (Operand.Var "b") = true from by decide,
    show dCv2.outputs.isEmpty = false from rfl]

/-- The ADD's optimistic swap is a no-op (`d` is both the output and the next scheduled var). -/
theorem optimisticSwapPlan_dAdd_noop (p : PlanState) :
    optimisticSwapPlan dbDfg dAdd ["c", "d"] false p = ([], p) := by
  unfold optimisticSwapPlan
  simp [show dAdd.outputs.getLast?.getD "" = "d" from rfl,
    show operandEquiv dbDfg (Operand.Var "d") (Operand.Var "d") = true from by decide,
    show dAdd.outputs.isEmpty = false from rfl]

/-- `doSwap` at distance 1 in closed form. -/
theorem doSwap_one_eq (p : PlanState) :
    doSwap 1 p = ([StackOp.SOSwap 1], { p with stack := stackSwap 1 p.stack }) := by
  unfold doSwap; simp

/-- `doSwap` at distance 2 in closed form. -/
theorem doSwap_two_eq (p : PlanState) :
    doSwap 2 p = ([StackOp.SOSwap 2], { p with stack := stackSwap 2 p.stack }) := by
  unfold doSwap; simp

/-- **Fold step 0: `%a = CALLVALUE`** (quiet optimism). `[] ↦ ["a"]`. -/
theorem bodyStepHTo_db0 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} :
    BodyStepHTo lo offsetToPc prog dbGp 1 (dCv1, 0) [] ["a"] := by
  intro p v s j hsd hsv hrel hblock
  have hstk : p.stack = [] := hsv
  have hplan : dbGp (dCv1, 0) p
      = ([StackOp.SOEmit "CALLVALUE"], releaseDeadSpills ["a"] { p with stack := p.stack ++ [Operand.Var "a"] }) := by
    show generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn dCv1 ["a"] true false "entry" p = _
    rw [gRIP_halting_live_eq rfl (by decide),
        genRegularInstPlan_read0_eq rfl (by decide) rfl rfl rfl (by decide),
        optimisticSwapPlan_dCv1_noop]
    simp
  rw [hplan] at hblock
  simp only [hplan]
  have hnos' : ∀ o, alookup' ({ p with stack := p.stack ++ [Operand.Var "a"] } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  have hstepEq : stepInstBase dCv1 v = ExecResult.OK (updateVar "a" v.callCtx.callvalue v) := rfl
  have hfield : (fun (a : AsmState) => a.callCtx.callvalue) s
      = (fun (w : VenomState) => w.callCtx.callvalue) v := by
    obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel
    show s.callCtx.callvalue = _
    rw [hCall]
  obtain ⟨s', hrun, hrel', hpc⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "a")
    (fAsm := fun a => a.callCtx.callvalue) (fV := fun w => w.callCtx.callvalue)
    hrel (by rw [hstk]; simp) (hsd.noSpill _) hblock
    (fun h hg => asmStep_callvalue_ok h hg) hfield
  have hrelR := releaseDeadSpills_sim (nextLiveness := ["a"]) hrel'
  refine ⟨gvBodyStep_of_updateVar (idx := 0) (plan := [StackOp.SOEmit "CALLVALUE"]) hstepEq
    ⟨s', hrun, hrelR, hpc⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro op
      exact releaseDeadSpills_noSpill _ _ hnos' op
    · show (releaseDeadSpills ["a"] { p with stack := p.stack ++ [Operand.Var "a"] }).stack.length + j ≤ 15
      rw [releaseDeadSpills_stack]
      have := hsd.shallow
      simp only [hstk] at this ⊢
      simp at this ⊢
      omega
    · intro z hz
      rw [show (releaseDeadSpills ["a"] { p with stack := p.stack ++ [Operand.Var "a"] }).stack
          = p.stack ++ [Operand.Var "a"] from releaseDeadSpills_stack _ _, hstk] at hz
      simp only [List.nil_append, List.mem_singleton] at hz
      injection hz with hz'
      subst hz'
      exact ⟨v.callCtx.callvalue, by
        show lookupVar "a" (gvBodyStep (dCv1, 0) v) = _
        rw [show gvBodyStep (dCv1, 0) v
            = { updateVar "a" v.callCtx.callvalue v with instIdx := 1 } from by
              unfold gvBodyStep; rw [hstepEq]]
        exact lookupVar_updateVar_self _ _ _⟩
  · show (releaseDeadSpills ["a"] { p with stack := p.stack ++ [Operand.Var "a"] }).stack = (["a"] : List String).map Operand.Var
    rw [releaseDeadSpills_stack, hstk]
    rfl

/-- **Fold step 1: `%b = CALLVALUE`** (quiet optimism). `["a"] ↦ ["a", "b"]`. -/
theorem bodyStepHTo_db1 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} :
    BodyStepHTo lo offsetToPc prog dbGp 1 (dCv2, 1) ["a"] ["a", "b"] := by
  intro p v s j hsd hsv hrel hblock
  have hstk : p.stack = [Operand.Var "a"] := hsv
  have hplan : dbGp (dCv2, 1) p
      = ([StackOp.SOEmit "CALLVALUE"], releaseDeadSpills ["a", "b"] { p with stack := p.stack ++ [Operand.Var "b"] }) := by
    show generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn dCv2 ["a", "b"] true false "entry" p = _
    rw [gRIP_halting_live_eq rfl (by decide),
        genRegularInstPlan_read0_eq rfl (by decide) rfl rfl rfl (by decide),
        optimisticSwapPlan_dCv2_noop]
    simp
  rw [hplan] at hblock
  simp only [hplan]
  have hnos' : ∀ o, alookup' ({ p with stack := p.stack ++ [Operand.Var "b"] } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  have hstepEq : stepInstBase dCv2 v = ExecResult.OK (updateVar "b" v.callCtx.callvalue v) := rfl
  have hfield : (fun (a : AsmState) => a.callCtx.callvalue) s
      = (fun (w : VenomState) => w.callCtx.callvalue) v := by
    obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel
    show s.callCtx.callvalue = _
    rw [hCall]
  obtain ⟨s', hrun, hrel', hpc⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "b")
    (fAsm := fun a => a.callCtx.callvalue) (fV := fun w => w.callCtx.callvalue)
    hrel (by rw [hstk]; simp) (hsd.noSpill _) hblock
    (fun h hg => asmStep_callvalue_ok h hg) hfield
  have hrelR := releaseDeadSpills_sim (nextLiveness := ["a", "b"]) hrel'
  refine ⟨gvBodyStep_of_updateVar (idx := 1) (plan := [StackOp.SOEmit "CALLVALUE"]) hstepEq
    ⟨s', hrun, hrelR, hpc⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro op
      exact releaseDeadSpills_noSpill _ _ hnos' op
    · show (releaseDeadSpills ["a", "b"] { p with stack := p.stack ++ [Operand.Var "b"] }).stack.length + j ≤ 15
      rw [releaseDeadSpills_stack]
      have := hsd.shallow
      simp only [hstk] at this ⊢
      simp at this ⊢
      omega
    · intro z hz
      rw [show (releaseDeadSpills ["a", "b"] { p with stack := p.stack ++ [Operand.Var "b"] }).stack
          = p.stack ++ [Operand.Var "b"] from releaseDeadSpills_stack _ _, hstk] at hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | hz
      · injection hz with hz'
        subst hz'
        obtain ⟨w, hw⟩ := hsd.defined "a" (by rw [hstk]; simp)
        exact ⟨w, by
          show lookupVar "a" (gvBodyStep (dCv2, 1) v) = _
          rw [show gvBodyStep (dCv2, 1) v
              = { updateVar "b" v.callCtx.callvalue v with instIdx := 2 } from by
                unfold gvBodyStep; rw [hstepEq]]
          rw [show lookupVar "a" ({ updateVar "b" v.callCtx.callvalue v with instIdx := 2 } : VenomState)
              = lookupVar "a" (updateVar "b" v.callCtx.callvalue v) from rfl,
            lookupVar_updateVar_ne _ _ _ _ (by decide)]
          exact hw⟩
      · injection hz with hz'
        subst hz'
        exact ⟨v.callCtx.callvalue, by
          show lookupVar "b" (gvBodyStep (dCv2, 1) v) = _
          rw [show gvBodyStep (dCv2, 1) v
              = { updateVar "b" v.callCtx.callvalue v with instIdx := 2 } from by
                unfold gvBodyStep; rw [hstepEq]]
          exact lookupVar_updateVar_self _ _ _⟩
  · show (releaseDeadSpills ["a", "b"] { p with stack := p.stack ++ [Operand.Var "b"] }).stack = (["a", "b"] : List String).map Operand.Var
    rw [releaseDeadSpills_stack, hstk]
    rfl

/-- **Fold step 2: `%c = CALLVALUE` with the optimistic `SWAP1`.** `["a","b"] ↦ ["a","c","b"]`. -/
theorem bodyStepHTo_db2 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} :
    BodyStepHTo lo offsetToPc prog dbGp 1 (dCv0, 2) ["a", "b"] ["a", "c", "b"] := by
  intro p v s j hsd hsv hrel hblock
  have hstk : p.stack = [Operand.Var "a", Operand.Var "b"] := hsv
  have hpushstk : ({ p with stack := p.stack ++ [Operand.Var "c"] } : PlanState).stack
      = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] := by
    show p.stack ++ [Operand.Var "c"] = _
    rw [hstk]
    rfl
  have hplan : dbGp (dCv0, 2) p
      = ([StackOp.SOEmit "CALLVALUE", StackOp.SOSwap 1],
         releaseDeadSpills ["c", "a", "b"] { p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }) := by
    show generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn dCv0 ["c", "a", "b"] true false "entry" p = _
    rw [gRIP_halting_live_eq rfl (by decide),
        genRegularInstPlan_read0_eq rfl (by decide) rfl rfl rfl (by decide),
        optimisticSwapPlan_dCv0 _ hpushstk]
    rfl
  rw [hplan] at hblock
  simp only [hplan]
  rw [show executePlan [StackOp.SOEmit "CALLVALUE", StackOp.SOSwap 1]
      = executePlan [StackOp.SOEmit "CALLVALUE"] ++ executePlan [StackOp.SOSwap 1] from rfl] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  have hnos' : ∀ o, alookup' ({ p with stack := p.stack ++ [Operand.Var "c"] } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  have hstepEq : stepInstBase dCv0 v = ExecResult.OK (updateVar "c" v.callCtx.callvalue v) := rfl
  have hfield : (fun (a : AsmState) => a.callCtx.callvalue) s
      = (fun (w : VenomState) => w.callCtx.callvalue) v := by
    obtain ⟨_, _, _, _, _, _, _, hCall, _, _, _, _⟩ := hrel
    show s.callCtx.callvalue = _
    rw [hCall]
  obtain ⟨s1, hrun1, hrel1, hpc1⟩ := emit_ctx_push_sim (name := "CALLVALUE") (out := "c")
    (fAsm := fun a => a.callCtx.callvalue) (fV := fun w => w.callCtx.callvalue)
    hrel (by rw [hstk]; simp) (hsd.noSpill _) hb1
    (fun h hg => asmStep_callvalue_ok h hg) hfield
  have hswapEq : doSwap 1 ({ p with stack := p.stack ++ [Operand.Var "c"] } : PlanState)
      = ([StackOp.SOSwap 1], { p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }) := by
    rw [doSwap_one_eq]
    have : stackSwap 1 ({ p with stack := p.stack ++ [Operand.Var "c"] } : PlanState).stack
        = [Operand.Var "a", Operand.Var "c", Operand.Var "b"] := by
      rw [hpushstk]; rfl
    rw [this]
  obtain ⟨s2, hrun2, hrel2, hpc2⟩ := doSwap_sim hswapEq
    (by exact hrel1)
    (by rw [hpushstk]; decide)
    (by rw [hpc1]; exact hb2)
    (fun h => absurd h (by omega))
  have hrelR := releaseDeadSpills_sim (nextLiveness := ["c", "a", "b"]) hrel2
  have hrunBoth : runAsm (executePlan [StackOp.SOEmit "CALLVALUE"] ++ executePlan [StackOp.SOSwap 1]).length
      offsetToPc prog s = AsmResult.AsmOK s2 := by
    rw [List.length_append]
    exact runAsm_compose hrun1 hrun2
  have hpcBoth : s2.pc = s.pc + (executePlan [StackOp.SOEmit "CALLVALUE"] ++ executePlan [StackOp.SOSwap 1]).length := by
    rw [List.length_append, hpc2, hpc1]
    omega
  have hnos2 : ∀ o, alookup' ({ p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  refine ⟨gvBodyStep_of_updateVar (idx := 2)
    (plan := [StackOp.SOEmit "CALLVALUE", StackOp.SOSwap 1]) hstepEq
    ⟨s2, hrunBoth, hrelR, hpcBoth⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro op
      exact releaseDeadSpills_noSpill _ _ hnos2 op
    · show (releaseDeadSpills ["c", "a", "b"] { p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }).stack.length + j ≤ 15
      rw [releaseDeadSpills_stack]
      have := hsd.shallow
      simp only [hstk] at this
      simp at this ⊢
      omega
    · intro z hz
      rw [show (releaseDeadSpills ["c", "a", "b"] { p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }).stack
          = [Operand.Var "a", Operand.Var "c", Operand.Var "b"] from releaseDeadSpills_stack _ _] at hz
      have hgv : gvBodyStep (dCv0, 2) v = { updateVar "c" v.callCtx.callvalue v with instIdx := 3 } := by
        unfold gvBodyStep; rw [hstepEq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz | hz
      · injection hz with hz'; subst hz'
        obtain ⟨w, hw⟩ := hsd.defined "a" (by rw [hstk]; simp)
        refine ⟨w, ?_⟩
        show lookupVar "a" (gvBodyStep (dCv0, 2) v) = some w
        rw [hgv]
        rw [show lookupVar "a" ({ updateVar "c" v.callCtx.callvalue v with instIdx := 3 } : VenomState)
            = lookupVar "a" (updateVar "c" v.callCtx.callvalue v) from rfl,
          lookupVar_updateVar_ne _ _ _ _ (by decide)]
        exact hw
      · injection hz with hz'; subst hz'
        refine ⟨v.callCtx.callvalue, ?_⟩
        show lookupVar "c" (gvBodyStep (dCv0, 2) v) = _
        rw [hgv]
        exact lookupVar_updateVar_self _ _ _
      · injection hz with hz'; subst hz'
        obtain ⟨w, hw⟩ := hsd.defined "b" (by rw [hstk]; simp)
        refine ⟨w, ?_⟩
        show lookupVar "b" (gvBodyStep (dCv0, 2) v) = some w
        rw [hgv]
        rw [show lookupVar "b" ({ updateVar "c" v.callCtx.callvalue v with instIdx := 3 } : VenomState)
            = lookupVar "b" (updateVar "c" v.callCtx.callvalue v) from rfl,
          lookupVar_updateVar_ne _ _ _ _ (by decide)]
        exact hw
  · show (releaseDeadSpills ["c", "a", "b"] { p with stack := [Operand.Var "a", Operand.Var "c", Operand.Var "b"] }).stack
        = (["a", "c", "b"] : List String).map Operand.Var
    rw [releaseDeadSpills_stack]
    rfl

/-- **Fold step 3: `%d = ADD %a %b`, both operands DEAD and BURIED.** The two-swap reorder
    positions the pair in TRUE order and the bare `ADD` consumes it: `["a","c","b"] ↦ ["c","d"]`.
    The f1a payoff step. -/
theorem bodyStepHTo_db3 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} :
    BodyStepHTo lo offsetToPc prog dbGp 1 (dAdd, 3) ["a", "c", "b"] ["c", "d"] := by
  intro p v s j hsd hsv hrel hblock
  have hstk : p.stack = [Operand.Var "a", Operand.Var "c", Operand.Var "b"] := hsv
  have hplan : dbGp (dAdd, 3) p
      = ([StackOp.SOSwap 1, StackOp.SOSwap 2, StackOp.SOEmit "ADD"],
         releaseDeadSpills ["c", "d"] { p with stack := [Operand.Var "c", Operand.Var "d"] }) := by
    show generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn dAdd ["c", "d"] true false "entry" p = _
    rw [genRegularInstPlan_dAdd_buried_eq hstk (hsd.noSpill _) (hsd.noSpill _),
        optimisticSwapPlan_dAdd_noop]
    rfl
  rw [hplan] at hblock
  simp only [hplan]
  rw [show executePlan [StackOp.SOSwap 1, StackOp.SOSwap 2, StackOp.SOEmit "ADD"]
      = executePlan [StackOp.SOSwap 1] ++ (executePlan [StackOp.SOSwap 2] ++ executePlan [StackOp.SOEmit "ADD"]) from rfl] at hblock ⊢
  obtain ⟨hb1, hb23⟩ := asmBlockAt_append hblock
  have hswap1 : doSwap 1 p = ([StackOp.SOSwap 1], { p with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] }) := by
    rw [doSwap_one_eq]
    rw [show stackSwap 1 p.stack = [Operand.Var "a", Operand.Var "b", Operand.Var "c"] from by rw [hstk]; rfl]
  obtain ⟨s1, hrun1, hrel1, hpc1⟩ := doSwap_sim hswap1 hrel
    (by rw [hstk]; decide) hb1 (fun h => absurd h (by omega))
  obtain ⟨hb2, hb3⟩ := asmBlockAt_append hb23
  have hswap2 : doSwap 2 ({ p with stack := [Operand.Var "a", Operand.Var "b", Operand.Var "c"] } : PlanState)
      = ([StackOp.SOSwap 2], { p with stack := [Operand.Var "c", Operand.Var "b", Operand.Var "a"] }) := by
    rw [doSwap_two_eq]
    rfl
  obtain ⟨s2, hrun2, hrel2, hpc2⟩ := doSwap_sim hswap2 hrel1
    (by simp) (by rw [hpc1]; exact hb2) (fun h => absurd h (by omega))
  obtain ⟨wa, hwa⟩ := hsd.defined "a" (by rw [hstk]; simp)
  obtain ⟨wb, hwb⟩ := hsd.defined "b" (by rw [hstk]; simp)
  have htop : s2.stack = wa :: wb :: s2.stack.drop 2 := by
    refine venomAsmRel_asmStack_top2 (p := Operand.Var "b") (q := Operand.Var "a")
      hrel2 (base := [Operand.Var "c"]) rfl ?_ ?_
    · exact hwb
    · exact hwa
  have hstepEq : stepInstBase dAdd v = ExecResult.OK (updateVar "d" (wa + wb) v) := by
    show execPure2 (· + ·) dAdd v = _
    unfold execPure2
    simp only [dAdd, evalOperand, hwa, hwb]
  obtain ⟨s3, hrun3, hrel3, hpc3⟩ := emit_binop_sim (name := "ADD") (out := "d")
    (f := (· + ·)) hrel2 htop (by simp) (hsd.noSpill _)
    (by rw [hpc2, hpc1]; exact hb3)
    (fun h hg => asmStep_add_ok h hg)
  have hrelR := releaseDeadSpills_sim (nextLiveness := ["c", "d"]) hrel3
  have hrunAll : runAsm (executePlan [StackOp.SOSwap 1] ++ (executePlan [StackOp.SOSwap 2] ++ executePlan [StackOp.SOEmit "ADD"])).length
      offsetToPc prog s = AsmResult.AsmOK s3 := by
    simp only [List.length_append]
    exact runAsm_compose hrun1 (runAsm_compose hrun2 hrun3)
  have hpcAll : s3.pc = s.pc + (executePlan [StackOp.SOSwap 1] ++ (executePlan [StackOp.SOSwap 2] ++ executePlan [StackOp.SOEmit "ADD"])).length := by
    simp only [List.length_append]
    rw [hpc3, hpc2, hpc1]
    omega
  have hnos3 : ∀ o, alookup' ({ p with stack := [Operand.Var "c", Operand.Var "d"] } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  refine ⟨gvBodyStep_of_updateVar (idx := 3)
    (plan := [StackOp.SOSwap 1, StackOp.SOSwap 2, StackOp.SOEmit "ADD"]) hstepEq
    ⟨s3, hrunAll, hrelR, hpcAll⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro op
      exact releaseDeadSpills_noSpill _ _ hnos3 op
    · show (releaseDeadSpills ["c", "d"] { p with stack := [Operand.Var "c", Operand.Var "d"] }).stack.length + j ≤ 15
      rw [releaseDeadSpills_stack]
      have := hsd.shallow
      simp only [hstk] at this
      simp at this ⊢
      omega
    · intro z hz
      rw [show (releaseDeadSpills ["c", "d"] { p with stack := [Operand.Var "c", Operand.Var "d"] }).stack
          = [Operand.Var "c", Operand.Var "d"] from releaseDeadSpills_stack _ _] at hz
      have hgv : gvBodyStep (dAdd, 3) v = { updateVar "d" (wa + wb) v with instIdx := 4 } := by
        unfold gvBodyStep; rw [hstepEq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz
      · injection hz with hz'; subst hz'
        obtain ⟨w, hw⟩ := hsd.defined "c" (by rw [hstk]; simp)
        refine ⟨w, ?_⟩
        show lookupVar "c" (gvBodyStep (dAdd, 3) v) = some w
        rw [hgv]
        rw [show lookupVar "c" ({ updateVar "d" (wa + wb) v with instIdx := 4 } : VenomState)
            = lookupVar "c" (updateVar "d" (wa + wb) v) from rfl,
          lookupVar_updateVar_ne _ _ _ _ (by decide)]
        exact hw
      · injection hz with hz'; subst hz'
        refine ⟨wa + wb, ?_⟩
        show lookupVar "d" (gvBodyStep (dAdd, 3) v) = _
        rw [hgv]
        exact lookupVar_updateVar_self _ _ _
  · show (releaseDeadSpills ["c", "d"] { p with stack := [Operand.Var "c", Operand.Var "d"] }).stack
        = (["c", "d"] : List String).map Operand.Var
    rw [releaseDeadSpills_stack]
    rfl

/-- **Fold step 4: `SSTORE %c %d`, swapped dead pair.** One `SWAP1` then the bare store:
    `["c","d"] ↦ []`. -/
theorem bodyStepHTo_db4 {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} :
    BodyStepHTo lo offsetToPc prog dbGp 1 (dStore, 4) ["c", "d"] [] := by
  intro p v s j hsd hsv hrel hblock
  have hstk : p.stack = [Operand.Var "c", Operand.Var "d"] := hsv
  have hplan : dbGp (dStore, 4) p
      = ([StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"], releaseDeadSpills [] { p with stack := [] }) := by
    show generateRegularInstPlan dbLive dbDfg dbCfg deadBuriedFn dStore [] true true "entry" p = _
    rw [genRegularInstPlan_dStore_swapped_eq hstk (hsd.noSpill _) (hsd.noSpill _)]
  rw [hplan] at hblock
  simp only [hplan]
  rw [show executePlan [StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"]
      = executePlan [StackOp.SOSwap 1] ++ executePlan [StackOp.SOEmit "SSTORE"] from rfl] at hblock ⊢
  obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
  have hswap1 : doSwap 1 p = ([StackOp.SOSwap 1], { p with stack := [Operand.Var "d", Operand.Var "c"] }) := by
    rw [doSwap_one_eq]
    rw [show stackSwap 1 p.stack = [Operand.Var "d", Operand.Var "c"] from by rw [hstk]; rfl]
  obtain ⟨s1, hrun1, hrel1, hpc1⟩ := doSwap_sim hswap1 hrel
    (by rw [hstk]; decide) hb1 (fun h => absurd h (by omega))
  obtain ⟨wc, hwc⟩ := hsd.defined "c" (by rw [hstk]; simp)
  obtain ⟨wd, hwd⟩ := hsd.defined "d" (by rw [hstk]; simp)
  have htop : s1.stack = wc :: wd :: s1.stack.drop 2 := by
    refine venomAsmRel_asmStack_top2 (p := Operand.Var "d") (q := Operand.Var "c")
      hrel1 (base := ([] : List Operand)) rfl ?_ ?_
    · exact hwd
    · exact hwc
  have hstepEq : stepInstBase dStore v = ExecResult.OK (sstore wc wd v) := by
    show execWrite2 (fun key val s => sstore key val s) dStore v = _
    unfold execWrite2
    simp only [dStore, evalOperand, hwc, hwd]
  obtain ⟨s2, hrun2, hrel2, hpc2⟩ := emit_sstore_sim hrel1 htop
    (by rw [hpc1]; exact hb2) (fun h hg => asmStep_sstore_ok h hg)
  have hrelR := releaseDeadSpills_sim (nextLiveness := ([] : List String)) hrel2
  have hrunAll : runAsm (executePlan [StackOp.SOSwap 1] ++ executePlan [StackOp.SOEmit "SSTORE"]).length
      offsetToPc prog s = AsmResult.AsmOK s2 := by
    simp only [List.length_append]
    exact runAsm_compose hrun1 hrun2
  have hpcAll : s2.pc = s.pc + (executePlan [StackOp.SOSwap 1] ++ executePlan [StackOp.SOEmit "SSTORE"]).length := by
    simp only [List.length_append]
    rw [hpc2, hpc1]
    omega
  have hnos4 : ∀ o, alookup' ({ p with stack := ([] : List Operand) } : PlanState).spilled o = none :=
    fun o => hsd.noSpill o
  refine ⟨gvBodyStep_of_ok (idx := 4)
    (plan := [StackOp.SOSwap 1, StackOp.SOEmit "SSTORE"]) hstepEq
    ⟨s2, hrunAll, hrelR, hpcAll⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro op
      exact releaseDeadSpills_noSpill _ _ hnos4 op
    · show (releaseDeadSpills [] { p with stack := ([] : List Operand) }).stack.length + j ≤ 15
      rw [releaseDeadSpills_stack]
      have := hsd.shallow
      simp at this ⊢
      omega
    · intro z hz
      rw [show (releaseDeadSpills [] { p with stack := ([] : List Operand) }).stack
          = ([] : List Operand) from releaseDeadSpills_stack _ _] at hz
      simp at hz
  · show (releaseDeadSpills [] { p with stack := ([] : List Operand) }).stack
        = ([] : List String).map Operand.Var
    rw [releaseDeadSpills_stack]
    rfl

end Example


/-! ## f1a stage 3: the gp-abstract STOP slice and the buried-dead-operand capstone -/

/-- **`labelThenBody_simTo`, gp-abstract**: the label step then the body fold for an ARBITRARY
    per-instruction generator `gp` (in particular one carrying per-instruction liveness and a
    real dfg, as `deadBuriedFn`'s optimism-emitting body needs). The constant-`nextLiveness`
    original is the `gp := generateRegularInstPlan … nextLiveness false true …` instance. -/
theorem labelThenBody_simToG
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {dem : Instruction × Nat → Nat}
    {ps0 : PlanState} {asm : AsmState} {bb : BasicBlock}
    {front : List Instruction} {s sEnd : VenomState} {S Sn : List String}
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog gp dem (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map dem).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1)) :
    ∃ as' : AsmState,
      runAsm (1 + (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length)
          o2pc prog asm = AsmResult.AsmOK as' ∧
      venomAsmRel lo ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).2 sEnd as' ∧
      as'.pc = asm.pc + 1 + (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length := by
  obtain ⟨as1, hrun1, hrel1, hpc1⟩ :=
    soLabel_sim (offsetToPc := o2pc) lo ps0 { s with instIdx := 0 } asm prog bb.label hrel hbLabel
  have hlen1 : (executePlan [StackOp.SOLabel bb.label]).length = 1 := rfl
  have hpc1' : as1.pc = asm.pc + 1 := by rw [hlen1] at hpc1; exact hpc1
  rw [hlen1] at hrun1
  have hblock1 : asmBlockAt prog as1.pc (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1) := by
    rw [hpc1']; exact hblock
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyHTo_sim_inv
    gp dem (front.zipIdx 0) S Sn ps0 { s with instIdx := 0 } as1 hready hsd hsv hrel1 hblock1
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  refine ⟨as', ?_, hrel', by rw [hpc', hpc1']⟩
  rw [runAsm_add_ok hrun1]; exact hrun

/-- **The STOP slice, gp-abstract** — `hsupplyW_regularStopTo` for an arbitrary per-instruction
    generator; the walk obligation for a STOP block whose body needs per-instruction liveness
    (or a real, optimism-emitting dfg) in its fold. -/
theorem hsupplyW_regularStopToG
    {fn : IrFunction} {lo : AssocList String Nat} {o2pc : AssocList Nat Nat}
    {offsets : AssocList String Nat} {prog : List AsmInst}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {dem : Instruction × Nat → Nat}
    {ps0 : PlanState} {asm : AsmState} {restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopI hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S Sn : List String}
    (hbb : bb.instructions = front ++ [stopI]) (hstopop : stopI.opcode = Opcode.STOP)
    (hcons : front ++ [stopI] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hready : BodyStepsReadyHTo lo o2pc prog gp dem (front.zipIdx 0) S Sn)
    (hsd : StackDiscH ((front.zipIdx 0).map dem).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel : venomAsmRel lo ps0 { s with instIdx := 0 } asm)
    (hbLabel : asmBlockAt prog asm.pc (executePlan [StackOp.SOLabel bb.label]))
    (hblock : asmBlockAt prog (asm.pc + 1)
      (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1))
    (hpc : asm.pc + 1 + (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length < prog.length)
    (hstop : prog.get ⟨asm.pc + 1 + (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length, hpc⟩
      = AsmInst.AsmOp "STOP")
    (hw : 1 + (executePlan ((front.zipIdx 0).foldl (fun acc x => (acc.1 ++ (gp x acc.2).1, (gp x acc.2).2)) ([], ps0)).1).length + 1 ≤ wOf bb.label) :
    ∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
      runAsm bodyLen o2pc prog asm = AsmResult.AsmOK as' ∧
      TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen
        (front.length + (restFuel + 1)) ctx bb s := by
  obtain ⟨as', hbody, hrel', hpcas⟩ :=
    labelThenBody_simToG (bb := bb) hthread hready hsd hsv hrel hbLabel hblock
  have hlt : as'.pc < prog.length := by rw [hpcas]; exact hpc
  have hst : prog.get ⟨as'.pc, hlt⟩ = AsmInst.AsmOp "STOP" := prog_get_transfer hpcas hstop
  exact ⟨as', _, sEnd, _, hbody,
    termRecipeW_stop_of_body hbb hstopop hcons hphi hnonterm hthread hrel' hw hlt hst⟩

namespace Example

/-- The five-step ready chain for `deadBuriedFn`'s body: the layouts thread
    `[] → ["a"] → ["a","b"] → ["a","c","b"] → ["c","d"] → []`. -/
theorem dbReady {lo : AssocList String Nat} {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} :
    BodyStepsReadyHTo lo offsetToPc prog dbGp (fun _ => 1)
      ([dCv1, dCv2, dCv0, dAdd, dStore].zipIdx 0) [] [] :=
  ⟨["a"], bodyStepHTo_db0,
    ⟨["a", "b"], bodyStepHTo_db1,
      ⟨["a", "c", "b"], bodyStepHTo_db2,
        ⟨["c", "d"], bodyStepHTo_db3,
          ⟨[], bodyStepHTo_db4, rfl⟩⟩⟩⟩⟩

def dbCtx : VenomContext := { functions := [deadBuriedFn], entry := some "main" }

abbrev dbA3 (s : VenomState) : VenomState :=
  { updateVar "c" s.callCtx.callvalue { updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } with instIdx := 3 }

abbrev dbA4 (s : VenomState) : VenomState :=
  { updateVar "d" (s.callCtx.callvalue + s.callCtx.callvalue) (dbA3 s) with instIdx := 4 }

abbrev dbSEnd (s : VenomState) : VenomState :=
  { sstore s.callCtx.callvalue (s.callCtx.callvalue + s.callCtx.callvalue) (dbA4 s) with instIdx := 5 }

theorem dbEntry_thread (s : VenomState) :
    execBodyThread [dCv1, dCv2, dCv0, dAdd, dStore] 0 { s with instIdx := 0 } = some (dbSEnd s) := by
  have ha3 : lookupVar "a" (dbA3 s) = some s.callCtx.callvalue := by
    show lookupVar "a" (updateVar "c" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_ne _ _ _ _ (by decide),
      lookupVar_updateVar_self]
  have hb3 : lookupVar "b" (dbA3 s) = some s.callCtx.callvalue := by
    show lookupVar "b" (updateVar "c" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide), lookupVar_updateVar_self]
  have h4 : stepInstBase dAdd (dbA3 s)
      = ExecResult.OK (updateVar "d" (s.callCtx.callvalue + s.callCtx.callvalue) (dbA3 s)) := by
    show execPure2 (· + ·) dAdd (dbA3 s) = _
    unfold execPure2
    simp only [dAdd, evalOperand, ha3, hb3]
  have hc4 : lookupVar "c" (dbA4 s) = some s.callCtx.callvalue := by
    show lookupVar "c" (updateVar "d" (s.callCtx.callvalue + s.callCtx.callvalue) (dbA3 s)) = _
    rw [lookupVar_updateVar_ne _ _ _ _ (by decide)]
    show lookupVar "c" (updateVar "c" s.callCtx.callvalue (updateVar "b" s.callCtx.callvalue (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }))) = _
    rw [lookupVar_updateVar_self]
  have hd4 : lookupVar "d" (dbA4 s) = some (s.callCtx.callvalue + s.callCtx.callvalue) := by
    show lookupVar "d" (updateVar "d" (s.callCtx.callvalue + s.callCtx.callvalue) (dbA3 s)) = _
    rw [lookupVar_updateVar_self]
  have h5 : stepInstBase dStore (dbA4 s)
      = ExecResult.OK (sstore s.callCtx.callvalue (s.callCtx.callvalue + s.callCtx.callvalue) (dbA4 s)) := by
    show execWrite2 (fun key val s => sstore key val s) dStore (dbA4 s) = _
    unfold execWrite2
    simp only [dStore, evalOperand, hc4, hd4]
  have h1 : stepInstBase dCv1 { s with instIdx := 0 }
      = ExecResult.OK (updateVar "a" s.callCtx.callvalue { s with instIdx := 0 }) := rfl
  have h2 : stepInstBase dCv2 ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } : VenomState)
      = ExecResult.OK (updateVar "b" s.callCtx.callvalue ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 })) := rfl
  have h3 : stepInstBase dCv0 ({ updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 } : VenomState)
      = ExecResult.OK (updateVar "c" s.callCtx.callvalue ({ updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 })) := rfl
  show (match stepInstBase dCv1 { s with instIdx := 0 } with
        | ExecResult.OK s' => execBodyThread [dCv2, dCv0, dAdd, dStore] 1 { s' with instIdx := 1 } | _ => none)
      = some (dbSEnd s)
  rw [h1]
  show (match stepInstBase dCv2 ({ updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 }) with
        | ExecResult.OK s' => execBodyThread [dCv0, dAdd, dStore] 2 { s' with instIdx := 2 } | _ => none)
      = some (dbSEnd s)
  rw [h2]
  show (match stepInstBase dCv0 ({ updateVar "b" s.callCtx.callvalue { updateVar "a" s.callCtx.callvalue { s with instIdx := 0 } with instIdx := 1 } with instIdx := 2 }) with
        | ExecResult.OK s' => execBodyThread [dAdd, dStore] 3 { s' with instIdx := 3 } | _ => none)
      = some (dbSEnd s)
  rw [h3]
  show (match stepInstBase dAdd (dbA3 s) with
        | ExecResult.OK s' => execBodyThread [dStore] 4 { s' with instIdx := 4 } | _ => none)
      = some (dbSEnd s)
  rw [h4]
  show (match stepInstBase dStore (dbA4 s) with
        | ExecResult.OK s' => execBodyThread [] 5 { s' with instIdx := 5 } | _ => none)
      = some (dbSEnd s)
  rw [h5]
  rfl

theorem dbFn_halts (vs : VenomState) (hnh : vs.halted = false) :
    ∃ vs', runContext 10 dbCtx vs = ExecResult.Halt vs' := by
  have h0 : runContext 10 dbCtx vs
      = runBlocks 10 dbCtx deadBuriedFn { vs with prevBb := none, currentBb := "entry", instIdx := 0 } := by
    simp [runContext, runFunction, dbCtx, deadBuriedFn, lookupFunction, fnEntryLabel]
  set s0 : VenomState := { vs with prevBb := none, currentBb := "entry", instIdx := 0 } with hs0
  have hlk0 : lookupBlock s0.currentBb deadBuriedFn.blocks
      = some { label := "entry", instructions := [dCv1, dCv2, dCv0, dAdd, dStore, stopInst] } := rfl
  have hhalt : runBlock 9 dbCtx { label := "entry", instructions := [dCv1, dCv2, dCv0, dAdd, dStore, stopInst] } s0
      = ExecResult.Halt (haltState (dbSEnd s0)) := by
    rw [show (9 : Nat) = ([dCv1, dCv2, dCv0, dAdd, dStore] : List Instruction).length + (3 + 1) from rfl]
    exact runBlock_body_stop dbCtx _ 3 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
      [dCv2, dCv0, dAdd, dStore, stopInst] s0 (dbSEnd s0) rfl rfl rfl (by decide)
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (dbEntry_thread s0)
  rw [h0]
  exact ⟨_, runBlocks_haltDirect_of_block hlk0 hhalt⟩

set_option maxHeartbeats 1000000 in
/-- **The buried-dead-operand capstone (f1a closed).** `codegen_correct` for `deadBuriedFn` —
    `entry: %a=CV; %b=CV; %c=CV; %d=ADD %a %b; SSTORE %c %d; STOP` — the function whose emitted
    program is the pinned `deadBuried_asm` swap chain: the third CALLVALUE's optimistic `SWAP1`,
    the buried pair's `SWAP1;SWAP2` reorder before the bare `ADD`, and the store's `SWAP1`. The
    fold runs the REAL analyses with PER-INSTRUCTION liveness (`dbGp`) through the gp-abstract
    STOP slice. Storage carries `c ↦ d = 2·callvalue` into the halt state. -/
theorem codegen_correct_deadBuriedFn_recipeW {lo : AssocList String Nat} {vs : VenomState} {as : AsmState}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    (match runContext 10 dbCtx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).2 (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  have hfnready : ∀ bb ∈ deadBuriedFn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst := by
    intro bb hbb inst hinst
    simp only [deadBuriedFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    subst hbb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hinst
    rcases hinst with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold codegenReadyInst; decide)
  have hgen : generateFnPlan deadBuriedFn 0 0
      = some ((generateFnPlan deadBuriedFn 0 0).get!.1, (generateFnPlan deadBuriedFn 0 0).get!.2) := rfl
  have hpsE : psOfFn (fnPlanFuel deadBuriedFn) deadBuriedFn 0 0 "entry" = initPlanState 0 :=
    psOfFn_entry rfl hfnready (by simp only [fnPlanFuel]; omega)
  refine codegen_correct_ofBlocks_recipeW_invCur (fun _ => True)
    (lo := lo) (pcOf := pcOfLabel (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1)
    (psOf := psOfFn (fnPlanFuel deadBuriedFn) deadBuriedFn 0 0)
    (wOf := fun l => (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 l)
    (offsets := (computeLabelOffsets (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).2)
    (fuel := 10) (ctx := dbCtx) (fn := deadBuriedFn) (fnEom := 0) (lblCtr := 0)
    (entryName := "main") (entryLbl := "entry")
    (ops := (generateFnPlan deadBuriedFn 0 0).get!.1) (psFinal := (generateFnPlan deadBuriedFn 0 0).get!.2)
    hgen rfl rfl rfl ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial) ?_ trivial
  case _ =>
    intro bb hbb s
    simp only [deadBuriedFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    subst hbb
    simp [runBlock, evalPhis, execBlock, dCv1]
  case _ =>
    intro bb hbb s asm N k hE _ hlbleq
    obtain ⟨⟨bb0, hlk_s, hvrel, hpc_asm⟩, hwN, hhalt⟩ := hE
    simp only [deadBuriedFn, List.mem_cons, List.not_mem_nil, or_false] at hbb
    subst hbb
    have hlbl : s.currentBb = "entry" := hlbleq
    rw [hlbl] at hvrel hpc_asm
    have hpc0 : asm.pc = 0 := by rw [hpc_asm]; exact pcOfLabel_entry_zero rfl hfnready hgen
    have hnt : ∀ inst ∈ [dCv1, dCv2, dCv0, dAdd, dStore], isTerminator inst.opcode = false := by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    match k with
    | 0 => exact Or.inl (runBlock_oof dbCtx _ 1 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
             [dCv2, dCv0, dAdd, dStore, stopInst] s (dbSEnd s) rfl rfl (by decide) hnt (dbEntry_thread s) (by decide))
    | 1 => exact Or.inl (runBlock_oof dbCtx _ 2 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
             [dCv2, dCv0, dAdd, dStore, stopInst] s (dbSEnd s) rfl rfl (by decide) hnt (dbEntry_thread s) (by decide))
    | 2 => exact Or.inl (runBlock_oof dbCtx _ 3 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
             [dCv2, dCv0, dAdd, dStore, stopInst] s (dbSEnd s) rfl rfl (by decide) hnt (dbEntry_thread s) (by decide))
    | 3 => exact Or.inl (runBlock_oof dbCtx _ 4 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
             [dCv2, dCv0, dAdd, dStore, stopInst] s (dbSEnd s) rfl rfl (by decide) hnt (dbEntry_thread s) (by decide))
    | 4 => exact Or.inl (runBlock_oof dbCtx _ 5 [dCv1, dCv2, dCv0, dAdd, dStore] stopInst dCv1
             [dCv2, dCv0, dAdd, dStore, stopInst] s (dbSEnd s) rfl rfl (by decide) hnt (dbEntry_thread s) (by decide))
    | (j+5) =>
    rw [show j+5+1 = ([dCv1, dCv2, dCv0, dAdd, dStore] : List Instruction).length + (j+1) from by
      simp only [List.length_cons, List.length_nil]; omega]
    refine Or.inr (hsupplyW_regularStopToG
      (gp := dbGp) (dem := fun _ => 1) (restFuel := j)
      (front := [dCv1, dCv2, dCv0, dAdd, dStore]) (stopI := stopInst) (hd := dCv1)
      (tl := [dCv2, dCv0, dAdd, dStore, stopInst])
      (ps0 := initPlanState 0) (sEnd := dbSEnd s) (S := []) (Sn := [])
      (hbb := rfl) (hstopop := rfl) (hcons := rfl) (hphi := by decide)
      (hnonterm := hnt) (hthread := dbEntry_thread s)
      (hready := dbReady)
      (hsd := ⟨fun op => rfl, by simp [initPlanState], fun z hz => by simp [initPlanState] at hz⟩)
      (hsv := rfl)
      (hrel := by rw [hpsE] at hvrel; exact hvrel)
      (hbLabel := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                     have hj2 : j < 1 := hj; interval_cases j; rfl)
      (hblock := by rw [hpc0]; refine ⟨by decide, fun j hj => ?_⟩
                    have hj2 : j < 9 := hj; interval_cases j <;> rfl)
      (hpc := by rw [hpc0]; decide)
      (hstop := prog_get_transfer (by rw [hpc0]; decide)
        (show (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.get ⟨10, by decide⟩
          = AsmInst.AsmOp "STOP" from rfl))
      (hw := by decide))
  case _ =>
    refine ⟨⟨{ label := "entry", instructions := [dCv1, dCv2, dCv0, dAdd, dStore, stopInst] }, rfl, ?_, ?_⟩, ?_, hvshalt⟩
    · show venomAsmRel lo (psOfFn (fnPlanFuel deadBuriedFn) deadBuriedFn 0 0 "entry") _ as
      rw [hpsE]; exact hrel
    · show as.pc = pcOfLabel (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 "entry"
      rw [haspc]; exact (pcOfLabel_entry_zero rfl hfnready hgen).symm
    · show (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length - pcOfLabel (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1 "entry" ≤ (asmResolve (executePlan (generateFnPlan deadBuriedFn 0 0).get!.1)).1.length
      omega

end Example

end EvmYul.Venom.Hol.Codegen

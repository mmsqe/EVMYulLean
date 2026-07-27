/-
GenBlockSimExample / canonical Entry, hsupply slices & the CFG assembly

Split part of `GenBlockSimExample`; see that module's header for the full roadmap.
This part is wrapped in `namespace EvmYul.Venom.Hol.Codegen` (the enclosing namespace of the second half); layout only, meaning unchanged.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeEntry

namespace EvmYul.Venom.Hol.Codegen

/-! ## The OK-continuing arm with a canonical Entry — the inter-block threading, packaged -/


/-- A canonical walk invariant `Entry`: at Venom state `s` related to asm state `asm`, the current block
    is found, `venomAsmRel` holds against its recorded plan, and the asm pc sits at the block's label.
    This is the shape a block simulation naturally establishes at a block's entry; the budget slot is
    left free for the walk to supply. -/
def CanonEntry (fn : IrFunction) (lo : AssocList String Nat) (pcOf : String → Nat)
    (psOf : String → PlanState) : VenomState → AsmState → Nat → Prop :=
  fun s asm _N =>
    ∃ bb, lookupBlock s.currentBb fn.blocks = some bb ∧
          venomAsmRel lo (psOf s.currentBb) s asm ∧ asm.pc = pcOf s.currentBb

/-- **The OK-continuing `hbsim` arm, with the canonical `Entry` preserved.** A continuing block
    (`runBlock = OK s'`, not halted) whose recipe asm run lands at the successor's label supplies the
    whole match — and the successor invariant `CanonEntry s' asm' N'` is discharged from exactly what the
    block simulation produces: the successor lookup, the `venomAsmRel` on arrival, and the recipe's
    landing pc. Nothing about the terminator or the program position is assumed beyond that. -/
theorem HbsimMatch_continue_canon {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm asm' : AsmState}
    {f' blockLen N' : Nat} {ctx : VenomContext} {bb bb' : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s') (hnh : s'.halted = false)
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmOK asm')
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hrel' : venomAsmRel lo (psOf s'.currentBb) s' asm')
    (hpc' : asm'.pc = pcOf s'.currentBb) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog asm (blockLen + N')
      (runBlock f' ctx bb s) := by
  rw [hrb]; simp only [HbsimMatch, hnh, Bool.false_eq_true, if_false]
  exact ⟨asm', N', runAsm_append_ok hrun, bb', hlk', hrel', hpc'⟩

/-- Fired on Dia's `then` (real compiler output): the recipe run lands the walk at the join, and
    `CanonEntry` at the join is discharged from the successor facts alone. -/
theorem dia_then_HbsimMatch_canon {pcOf : String → Nat} {psOf : String → PlanState}
    {f' N' : Nat} {ctx : VenomContext} {s s' : VenomState} {asm : AsmState} {bb' : BasicBlock}
    (hrb : runBlock f' ctx Dia.bThen s = ExecResult.OK s') (hnh : s'.halted = false)
    (hpc : asm.pc = 13)
    (hlk' : lookupBlock s'.currentBb Dia.fn.blocks = some bb')
    (hrel' : venomAsmRel Dia.lo (psOf s'.currentBb) s' { asm with pc := 11 })
    (hpc' : (11 : Nat) = pcOf s'.currentBb) :
    HbsimMatch (CanonEntry Dia.fn Dia.lo pcOf psOf) Dia.o2pc Dia.prog asm (5 + N')
      (runBlock f' ctx Dia.bThen s) :=
  HbsimMatch_continue_canon hrb hnh (dia_hasm_then_via_recipe hpc) hlk' hrel' hpc'

/-! ## The body sim composes with the terminator into hbsim — the remaining obligation, connected -/


/-- **The body sim output composes with the STOP terminator into `hbsim`.**

`genBlockBodyH_sim_inv` (the existing body simulation) produces, over the whole-function program, the
body's asm run to `as'` together with `venomAsmRel lo ps' vs' as'` at the post-body state. This composes
that with the STOP terminator: the body run reaches `as'`, one more asm step (STOP) halts at
`asmNext as'`, the Venom block halts at `haltState vs'`, and the terminal relation is *derived* from the
body sim's `venomAsmRel` (`terminalRel_stop_of_rel`). No terminal relation is separately assumed — the
whole hbsim comes from the body sim plus the terminator's own step. -/
theorem HbsimMatch_stop_from_body {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s vs' : VenomState}
    -- Venom: the block runs its body to vs', then STOPs
    (hrb : runBlock f' ctx bb s = ExecResult.Halt (haltState vs'))
    -- body sim output (from genBlockBodyH_sim_inv): asm reaches as', related to vs'
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    -- terminator: STOP sits at as'.pc, so one asm step halts at asmNext as'
    (hstoppc : as'.pc < prog.length)
    (hstop : prog.get ⟨as'.pc, hstoppc⟩ = AsmInst.AsmOp "STOP")
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  -- the STOP step from as'
  have hstep : runAsm 1 o2pc prog as' = AsmResult.AsmHalt (asmNext as') := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runAsm, asmStep, dif_pos hstoppc]
    simp only [hstop]
  -- compose body ++ STOP
  have hfull : runAsm (bodyLen + 1) o2pc prog as0 = AsmResult.AsmHalt (asmNext as') := by
    rw [runAsm_append_ok hbody, hstep]
  exact HbsimMatch_of_halt hrb hfull hle (terminalRel_stop_of_rel hrel')

/-- Body sim + INVALID → hbsim (fault arm; terminal relation derived). -/
theorem HbsimMatch_invalid_from_body {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s vs' : VenomState}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vs')))
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    (hpc : as'.pc < prog.length) (hinv : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "INVALID")
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hstep : runAsm 1 o2pc prog as'
      = AsmResult.AsmFault { asmNext as' with returndata := ByteArray.empty } := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runAsm, asmStep, dif_pos hpc]; simp only [hinv]
  have hfull : runAsm (bodyLen + 1) o2pc prog as0
      = AsmResult.AsmFault { asmNext as' with returndata := ByteArray.empty } := by
    rw [runAsm_append_ok hbody, hstep]
  exact HbsimMatch_of_fault hrb hfull hle (terminalRel_invalid_of_rel hrel')

/-- Body sim + RETURN → hbsim (halt arm; terminal relation derived from `venomAsmRel` + memory-safety). -/
theorem HbsimMatch_return_from_body {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb : BasicBlock} {s vs' : VenomState} {offW szW : bytes32}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Halt (haltState (setReturndata (readMemory offW.toNat szW.toNat vs') vs')))
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    (hpc : as'.pc < prog.length) (hret : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "RETURN")
    (hstk : as'.stack = offW :: szW :: rest)
    (hcov : szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
    (hbelow : offW.toNat + szW.toNat ≤ ps'.alloc.fnEom) (hlen : szW.toNat < USize.size)
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hstep := runAsm_return (offsetToPc := o2pc) (prog := prog) (asMid := as') 0 hpc hret hstk hcov
  refine HbsimMatch_of_halt hrb (by rw [runAsm_append_ok hbody]; exact hstep) hle ?_
  exact terminalRel_return_of_rel (off := offW.toNat) (sz := szW.toNat) (rest := rest) hrel' hbelow hlen

/-- Body sim + REVERT → hbsim (revert arm; terminal relation derived). -/
theorem HbsimMatch_revert_from_body {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb : BasicBlock} {s vs' : VenomState} {offW szW : bytes32}
    (hrb : runBlock f' ctx bb s
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata (readMemory offW.toNat szW.toNat vs') vs')))
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    (hpc : as'.pc < prog.length) (hrev : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "REVERT")
    (hstk : as'.stack = offW :: szW :: rest)
    (hcov : szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
    (hbelow : offW.toNat + szW.toNat ≤ ps'.alloc.fnEom) (hlen : szW.toNat < USize.size)
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hstep := runAsm_revert (offsetToPc := o2pc) (prog := prog) (asMid := as') 0 hpc hrev hstk hcov
  refine HbsimMatch_of_revert hrb (by rw [runAsm_append_ok hbody]; exact hstep) hle ?_
  exact terminalRel_revert_of_rel (off := offW.toNat) (sz := szW.toNat) (rest := rest) hrel' hbelow hlen

/-! ## The continuing (JMP) case: body sim + JMP + successor-recording → hbsim -/


/-- `jumpTo` only changes control-flow fields (prevBb/currentBb/instIdx), which `venomAsmRel` never
    reads — so it is insensitive, exactly like `venomAsmRel_setPc`. -/
theorem venomAsmRel_jumpTo (lo : AssocList String Nat) (ps : PlanState) (vs : VenomState)
    (as : AsmState) (lbl : String) (h : venomAsmRel lo ps vs as) :
    venomAsmRel lo ps (jumpTo lbl vs) as := h

/-- **Body sim + JMP → the OK-continuing hbsim, with the canonical Entry.**

The one continuing-case ingredient beyond the halting connectors is the successor-recording fact
`ps' = psOf target` — the post-body plan lines up with the target's recorded entry (established for JMP
chains). Given that, plus the body sim's `venomAsmRel` and the resolved `PUSH target; JUMP`, the walk
resumes at the target with `CanonEntry` discharged: `jumpTo` and the landing pc are both invisible to the
relation, so the arrival `venomAsmRel` is exactly the body sim's. -/
theorem HbsimMatch_jmp_from_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {ps' : PlanState} {as0 as' : AsmState} {f' bodyLen N off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {target : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs'' as')
    (hps : ps' = psOf target)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as'.pc + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hle : bodyLen + 2 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  obtain ⟨N', rfl⟩ := Nat.le.dest hle
  have hjmp := resolved_jump_sim (s := as') hpush1 hpush hoff_lk hoff hjump1 hjump hidx_lk
  have hfull : runAsm (bodyLen + 2) o2pc prog as0 = AsmResult.AsmOK { as' with pc := pcOf target } := by
    rw [runAsm_append_ok hbody, hjmp]
  have harr : venomAsmRel lo (psOf (jumpTo target vs'').currentBb) (jumpTo target vs'')
      { as' with pc := pcOf target } := by
    show venomAsmRel lo (psOf target) (jumpTo target vs'') { as' with pc := pcOf target }
    refine venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc ?_)
    rw [← hps]; exact hrel'
  exact HbsimMatch_continue_canon (bb' := bb') (N' := N') hrb hnh hfull hlk' harr rfl

/-! ## The N-constrained walk `Entry`: threading the budget through continuing blocks

`CanonEntry` ignores `N`, so feeding the recipe connectors to the multi-block driver
`codegen_correct_ofBlocks_HbsimMatch` hits the halting-block ∀-N vacuity (`HbsimMatch (Halt) N` is false for
`N < blockLen`). The fix is to carry `wOf currentBb ≤ N` (the remaining program length fits the walk budget)
in the Entry — a halting block reached with `wOf(block) ≤ N` has `N ≥ blockLen`, so its `HbsimMatch (Halt)`
holds; a continuing block threads `wOf(succ) ≤ N'` to its successor from the layout fact
`wOf(succ) + blockLen ≤ wOf(cur)`. The halting connectors are already Entry-independent, so only the
continuing connectors need this strengthened form. -/

/-- **The N-constrained continuing-walk `Entry`**: `CanonEntry`, the budget lower-bound `wOf ≤ N`, and
    `s.halted = false`. The JMP (and every
    continuing) block needs the not-halted fact: `codegen_correct_ofBlocks_HbsimMatch`'s hstep exposes only
    `Entry ∧ s.currentBb = bb.label` (no halted), yet a JMP block's `runBlock = OK (jumpTo …)` and the
    continue arm's `hnh` both require `s.halted = false` (else the OK result is halted and the halt arm's
    `runAsm N = AsmHalt` is false for a continuing terminator). Threading it in the Entry supplies it; the
    continue arm re-establishes it at the successor for free (its `hnh`). -/
def CanonEntryWH (fn : IrFunction) (lo : AssocList String Nat) (pcOf : String → Nat)
    (psOf : String → PlanState) (wOf : String → Nat) : VenomState → AsmState → Nat → Prop :=
  fun s asm N => CanonEntry fn lo pcOf psOf s asm N ∧ wOf s.currentBb ≤ N ∧ s.halted = false

/-- **The OK-continuing arm for `CanonEntryWH`.** A continuing block whose recipe run lands at the successor
    supplies the whole `HbsimMatch`: the successor's budget bound `wOf(successor) ≤ N'` is supplied by the
    caller (derived from the layout fact `wOf(succ) + blockLen ≤ wOf(cur)`), and its `s'.halted = false` is
    exactly the `hnh` the OK arm already carries. Otherwise this is `HbsimMatch_continue_canon`. -/
theorem HbsimMatch_continue_canonWH {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm asm' : AsmState}
    {f' blockLen N' : Nat} {ctx : VenomContext} {bb bb' : BasicBlock} {s s' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.OK s') (hnh : s'.halted = false)
    (hrun : runAsm blockLen o2pc prog asm = AsmResult.AsmOK asm')
    (hlk' : lookupBlock s'.currentBb fn.blocks = some bb')
    (hrel' : venomAsmRel lo (psOf s'.currentBb) s' asm')
    (hpc' : asm'.pc = pcOf s'.currentBb)
    (hwsucc : wOf s'.currentBb ≤ N') :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog asm (blockLen + N')
      (runBlock f' ctx bb s) := by
  rw [hrb]; simp only [HbsimMatch, hnh, Bool.false_eq_true, if_false]
  exact ⟨asm', N', runAsm_append_ok hrun, ⟨bb', hlk', hrel', hpc'⟩, hwsucc, hnh⟩

/-- **The JMP connector for the N-constrained continuing-walk Entry.** Mirrors `HbsimMatch_jmp_from_body`
    but produces `HbsimMatch (CanonEntryWH …)`: the successor's budget bound `wOf(target) ≤ N − (bodyLen+2)`
    is derived from the block's layout fact `hlayout` and the current bound `hcur`, and `halted = false` is
    threaded to the successor. -/
theorem HbsimMatch_jmp_from_body_canonWH {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {ps' : PlanState} {as0 as' : AsmState} {f' bodyLen N off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {target : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs'' as')
    (hps : ps' = psOf target)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as'.pc + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hlayout : wOf target + (bodyLen + 2) ≤ wOf bb.label)
    (hcur : wOf bb.label ≤ N) :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hle : bodyLen + 2 ≤ N := by omega
  obtain ⟨N', hNeq⟩ := Nat.le.dest hle
  subst hNeq
  have hjmp := resolved_jump_sim (s := as') hpush1 hpush hoff_lk hoff hjump1 hjump hidx_lk
  have hfull : runAsm (bodyLen + 2) o2pc prog as0 = AsmResult.AsmOK { as' with pc := pcOf target } := by
    rw [runAsm_append_ok hbody, hjmp]
  have harr : venomAsmRel lo (psOf (jumpTo target vs'').currentBb) (jumpTo target vs'')
      { as' with pc := pcOf target } := by
    show venomAsmRel lo (psOf target) (jumpTo target vs'') { as' with pc := pcOf target }
    refine venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc ?_)
    rw [← hps]; exact hrel'
  have hnh' : (jumpTo target vs'').halted = false := by simp [jumpTo, hnh]
  have hwsucc : wOf (jumpTo target vs'').currentBb ≤ N' := by show wOf target ≤ N'; omega
  exact HbsimMatch_continue_canonWH (bb' := bb') (N' := N') hrb hnh' hfull hlk' harr rfl hwsucc

/-- **The `Inv`-carrying JMP arm — the first invariant in this development that constrains the ASM side.**
    Identical to `HbsimMatch_jmp_from_body_canonWH` but parameterised by `Inv : VenomState → AsmState → Prop`
    and carrying it into the successor `Entry`. The point is WHERE the conjunction happens: a post-hoc
    `HbsimMatch E ∧ Inv` lemma is sound but USELESS, because `HbsimMatch`'s continuing arm characterises the
    successor asm state only by a run-equality (`runAsm N o2pc prog asm = runAsm N' o2pc prog asm'`), so its
    obligation quantifies over an `asm'` the caller cannot constrain — the same trap as `reorderPlan_sim`'s
    ∀-p `hstep` (`GenBlockSimComp.lean:2965`). Building the conjoined `Entry` HERE instead, via the
    `Entry`-generic `HbsimMatch_of_OK_continue`, makes `hinvA` name the CONCRETE successor
    `{ as' with pc := pcOf target }` — which the caller discharges from `runAsm_memory_size_mono`
    (`GenInstSim.lean:14638`), since a JMP successor edits only `pc`. -/
theorem HbsimMatch_jmp_from_body_canonWH_invA {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {ps' : PlanState} {as0 as' : AsmState} {f' bodyLen N off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {target : String}
    {Inv : VenomState → AsmState → Prop}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs'' as')
    (hps : ps' = psOf target)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as'.pc + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hlayout : wOf target + (bodyLen + 2) ≤ wOf bb.label)
    (hcur : wOf bb.label ≤ N)
    (hinvA : Inv (jumpTo target vs'') { as' with pc := pcOf target }) :
    HbsimMatch (fun s a n => CanonEntryWH fn lo pcOf psOf wOf s a n ∧ Inv s a)
      o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hle : bodyLen + 2 ≤ N := by omega
  obtain ⟨N', hNeq⟩ := Nat.le.dest hle
  subst hNeq
  have hjmp := resolved_jump_sim (s := as') hpush1 hpush hoff_lk hoff hjump1 hjump hidx_lk
  have hfull : runAsm (bodyLen + 2) o2pc prog as0 = AsmResult.AsmOK { as' with pc := pcOf target } := by
    rw [runAsm_append_ok hbody, hjmp]
  have harr : venomAsmRel lo (psOf (jumpTo target vs'').currentBb) (jumpTo target vs'')
      { as' with pc := pcOf target } := by
    show venomAsmRel lo (psOf target) (jumpTo target vs'') { as' with pc := pcOf target }
    refine venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc ?_)
    rw [← hps]; exact hrel'
  have hnh' : (jumpTo target vs'').halted = false := by simp [jumpTo, hnh]
  have hwsucc : wOf (jumpTo target vs'').currentBb ≤ N' := by show wOf target ≤ N'; omega
  exact HbsimMatch_of_OK_continue hrb hnh' hfull
    ⟨⟨⟨bb', hlk', harr, rfl⟩, hwsucc, hnh'⟩, hinvA⟩

/-! ## JNZ both branches: body sim + JNZ + successor-recording → hbsim (continuing terminators) -/


/-- **Body sim + JNZ (taken) → the OK-continuing hbsim.** Unlike JMP, the JUMPI pops the branch
    condition, so the arrival stack is the body-end stack minus the condition. The inter-block input is
    therefore the successor relation with the condition already dropped (`hrel_succ`) — the JNZ
    successor-recording, playing the role `ps' = psOf target` plays for JMP. `jumpTo` and the landing pc
    are still invisible to the relation. -/
theorem HbsimMatch_jnz_taken_from_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N off : Nat} {cond : bytes32} {stk : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {ifNz : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo ifNz vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hstk_c : as'.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hrel_succ : venomAsmRel lo (psOf ifNz) vs'' { as' with stack := stk })
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hle : bodyLen + 2 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  obtain ⟨N', rfl⟩ := Nat.le.dest hle
  have hstep := resolved_jumpi_taken_sim (s := as') hstk_c hcond hpush1 hpush hoff_lk hoff
    hjumpi1 hjumpi hidx_lk
  have hfull : runAsm (bodyLen + 2) o2pc prog as0
      = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifNz } := by
    rw [runAsm_append_ok hbody, hstep]
  have harr : venomAsmRel lo (psOf (jumpTo ifNz vs'').currentBb) (jumpTo ifNz vs'')
      { as' with stack := stk, pc := pcOf ifNz } := by
    show venomAsmRel lo (psOf ifNz) (jumpTo ifNz vs'') { as' with stack := stk, pc := pcOf ifNz }
    have h1 : venomAsmRel lo (psOf ifNz) vs'' { { as' with stack := stk } with pc := pcOf ifNz } :=
      venomAsmRel_setPc hrel_succ
    exact venomAsmRel_jumpTo _ _ _ _ _ h1
  exact HbsimMatch_continue_canon (bb' := bb') (N' := N') hrb hnh hfull hlk' harr rfl

/-- **Body sim + JNZ (not taken) → the OK-continuing hbsim.** Condition zero: the JUMPI falls through
    (popping the condition), then `PUSH ifZ; JUMP` lands at `ifZ`. Four terminator instructions; same
    successor-recording input, now for `ifZ`. -/
theorem HbsimMatch_jnz_nottaken_from_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N offN offZ : Nat} {stk : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {ifNz ifZ : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo ifZ vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hstk_c : as'.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpush1 : as'.pc < prog.length)
    (hpushN : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hpush2 : as'.pc + 2 < prog.length)
    (hpushZ : prog.get ⟨as'.pc + 2, hpush2⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hjump1 : as'.pc + 2 + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 2 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hrel_succ : venomAsmRel lo (psOf ifZ) vs'' { as' with stack := stk })
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hle : bodyLen + 4 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  obtain ⟨N', rfl⟩ := Nat.le.dest hle
  have hjumpi_step := resolved_jumpi_nottaken_sim (offsetToPc := o2pc) (prog := prog) (s := as')
    hstk_c hpush1 hpushN hoffN_lk hoffN hjumpi1 hjumpi
  have hjump_step := resolved_jump_sim (s := { as' with stack := stk, pc := as'.pc + 2 })
    (by simpa using hpush2) (by simpa using hpushZ) hoffZ_lk hoffZ
    (by simpa using hjump1) (by simpa using hjump) hidxZ_lk
  have hterm4 : runAsm 4 o2pc prog as'
      = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifZ } := by
    rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hjumpi_step, hjump_step]
  have hfull : runAsm (bodyLen + 4) o2pc prog as0
      = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifZ } := by
    rw [runAsm_append_ok hbody, hterm4]
  have harr : venomAsmRel lo (psOf (jumpTo ifZ vs'').currentBb) (jumpTo ifZ vs'')
      { as' with stack := stk, pc := pcOf ifZ } := by
    show venomAsmRel lo (psOf ifZ) (jumpTo ifZ vs'') { as' with stack := stk, pc := pcOf ifZ }
    exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hrel_succ)
  exact HbsimMatch_continue_canon (bb' := bb') (N' := N') hrb hnh hfull hlk' harr rfl

/-! ## Non-vacuity: a bare STOP block instantiates the body-sim connector -/


/-- **Non-vacuity of the body-sim connectors.** A bare STOP block instantiates
    `HbsimMatch_stop_from_body` with an empty body (`bodyLen = 0`, so the body-end state is the entry):
    `runBlock` reduces to `Halt (haltState {s with instIdx := 0})`, the entry `venomAsmRel` is the body
    sim's output, and the whole hbsim match is produced. So the connector's hypotheses are jointly
    satisfiable — it is not vacuous. -/
theorem HbsimMatch_stop_from_body_nonvacuous
    {Entry : VenomState → AsmState → Nat → Prop} {lo : AssocList String Nat} {ps : PlanState}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {as0 : AsmState}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {N f' : Nat} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } as0)
    (hstoppc : as0.pc < prog.length) (hstop : prog.get ⟨as0.pc, hstoppc⟩ = AsmInst.AsmOp "STOP")
    (hle : 0 + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (f' + 1) ctx bb { s with instIdx := 0 }) := by
  have hrb : runBlock (f' + 1) ctx bb { s with instIdx := 0 }
      = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, hbb, hstopop, stepInstBase,
      isTerminator]
  refine HbsimMatch_stop_from_body (bodyLen := 0) (as' := as0) (ps' := ps) hrb ?_ hrel hstoppc hstop hle
  simp [runAsm]

/-! ## Accurate terminator scope: RET is trivial, SINK is pre-codegen -/


/-- **RET needs no hbsim connector: it falls into the `_ => True` arm.** A `RET` steps to `IntRet`, which
    `hbsim` (and `HbsimMatch`) leaves as `True` — the walk claims correspondence only when the block step
    reaches OK/Halt/Abort, never IntRet (which is call-level, handled by INVOKE, not `runBlocks`). So a
    RET block's hbsim is trivially satisfied. -/
theorem HbsimMatch_ret_trivial {Entry : VenomState → AsmState → Nat → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm : AsmState} {N : Nat}
    {retVals : List bytes32} {s' : VenomState} :
    HbsimMatch Entry o2pc prog asm N (ExecResult.IntRet retVals s') := by
  unfold HbsimMatch; trivial

/-- SINK is a pre-codegen pseudo-instruction, so it never appears in generated code —
    `generateInstPlan` returns `none` for it. No hbsim connector is needed. -/
theorem sink_is_precodegen : isPreCodegenOpcode Opcode.SINK = true := rfl

/-! ## SELFDESTRUCT: body sim + SELFDESTRUCT → hbsim (accounts change handled) -/


/-- **SELFDESTRUCT's terminal relation from `venomAsmRel`.** Both sides apply `selfdestruct addr` to
    accounts (the Venom inline logic equals the `selfdestruct` function; the asm reuses it on the
    converted state). `selfdestruct` reads only `callCtx.contract` and `accounts`, both of which
    `venomAsmRel` equates (and `toVenomState` preserves), so the resulting accounts agree by
    `selfdestruct_accounts_congr`; transient/returndata/logs come from the relation (selfdestruct and
    asmNext touch none of them). The stack top being `addr` is the operand correspondence the body sim's
    `planStackRel` provides. -/
theorem terminalRel_selfdestruct_of_rel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {addr : bytes32} {stk : List bytes32}
    (h : venomAsmRel lo ps vs as) :
    venomAsmTerminalRel (haltState (selfdestruct addr vs))
      { asmNext as with stack := stk, accounts := (selfdestruct addr as.toVenomState).accounts } := by
  obtain ⟨_, _, _, hacc, htr, hrd, hlog, hcc, _, _, _, _⟩ := h
  refine ⟨?_, htr, hrd, hlog⟩
  -- accounts: (selfdestruct addr as.toVenomState).accounts = (selfdestruct addr vs).accounts
  show (selfdestruct addr as.toVenomState).accounts = (selfdestruct addr vs).accounts
  exact selfdestruct_accounts_congr addr (s1 := as.toVenomState) (s2 := vs) hacc hcc

/-- **Body sim + SELFDESTRUCT → hbsim** (halt arm; terminal relation derived, accounts included). -/
theorem HbsimMatch_selfdestruct_from_body {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {addr : bytes32} {stk : List bytes32}
    {ctx : VenomContext} {bb : BasicBlock} {s vs' : VenomState}
    (hrb : runBlock f' ctx bb s = ExecResult.Halt (haltState (selfdestruct addr vs')))
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    (hpc : as'.pc < prog.length) (hsd : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hstk : as'.stack = addr :: stk) (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hrel := terminalRel_selfdestruct_of_rel (lo := lo) (ps := ps') (addr := addr) (stk := stk) hrel'
  refine HbsimMatch_of_halt hrb ?_ hle hrel
  rw [runAsm_append_ok hbody, show (1 : Nat) = 0 + 1 from rfl, runAsm, asmStep, dif_pos hpc]
  simp only [hsd]
  simp only [asmSelfdestruct, hstk]

/-! ## DJMP: body sim + dispatch chain → hbsim (the last terminator; every terminator now covered) -/


/-- **Body sim + DJMP → the OK-continuing hbsim.** DJMP is the dynamic analog of JMP: the Venom step
    jumps to `targetLabel` (the selector-indexed label), and the asm dispatch chain
    (`djmp_switch_sim`) runs from the post-body state to `pcOf targetLabel`, consuming the selector.
    Structurally identical to JNZ: the selector is popped, so the inter-block input is the successor
    relation with the selector dropped; `jumpTo` and the landing pc stay invisible to `venomAsmRel`.
    The dispatch run (to the exact target state) is the input the existing DJMP machinery supplies. -/
theorem HbsimMatch_djmp_from_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen chainLen N : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {targetLabel : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo targetLabel vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hdispatch : runAsm chainLen o2pc prog as'
      = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel })
    (hrel_succ : venomAsmRel lo (psOf targetLabel) vs'' { as' with stack := rest })
    (hlk' : lookupBlock targetLabel fn.blocks = some bb')
    (hle : bodyLen + chainLen ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  obtain ⟨N', rfl⟩ := Nat.le.dest hle
  have hfull : runAsm (bodyLen + chainLen) o2pc prog as0
      = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel } := by
    rw [runAsm_append_ok hbody, hdispatch]
  have harr : venomAsmRel lo (psOf (jumpTo targetLabel vs'').currentBb) (jumpTo targetLabel vs'')
      { as' with stack := rest, pc := pcOf targetLabel } := by
    show venomAsmRel lo (psOf targetLabel) (jumpTo targetLabel vs'')
      { as' with stack := rest, pc := pcOf targetLabel }
    exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hrel_succ)
  exact HbsimMatch_continue_canon (bb' := bb') (N' := N') hrb hnh hfull hlk' harr rfl

theorem HbsimMatch_jnz_taken_from_body_canonWH {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N off : Nat} {cond : bytes32} {stk : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {ifNz : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo ifNz vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hstk_c : as'.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hrel_succ : venomAsmRel lo (psOf ifNz) vs'' { as' with stack := stk })
    (hlk' : lookupBlock ifNz fn.blocks = some bb')
    (hlayout : wOf ifNz + (bodyLen + 2) ≤ wOf bb.label) (hcur : wOf bb.label ≤ N) :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hle : bodyLen + 2 ≤ N := by omega
  obtain ⟨N', hNeq⟩ := Nat.le.dest hle; subst hNeq
  have hstep := resolved_jumpi_taken_sim (s := as') hstk_c hcond hpush1 hpush hoff_lk hoff hjumpi1 hjumpi hidx_lk
  have hfull : runAsm (bodyLen + 2) o2pc prog as0 = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifNz } := by
    rw [runAsm_append_ok hbody, hstep]
  have harr : venomAsmRel lo (psOf (jumpTo ifNz vs'').currentBb) (jumpTo ifNz vs'')
      { as' with stack := stk, pc := pcOf ifNz } := by
    show venomAsmRel lo (psOf ifNz) (jumpTo ifNz vs'') { as' with stack := stk, pc := pcOf ifNz }
    exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hrel_succ)
  have hnh' : (jumpTo ifNz vs'').halted = false := by simp [jumpTo, hnh]
  have hwsucc : wOf (jumpTo ifNz vs'').currentBb ≤ N' := by show wOf ifNz ≤ N'; omega
  exact HbsimMatch_continue_canonWH (bb' := bb') (N' := N') hrb hnh' hfull hlk' harr rfl hwsucc

theorem HbsimMatch_jnz_nottaken_from_body_canonWH {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N offN offZ : Nat} {stk : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {ifNz ifZ : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo ifZ vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hstk_c : as'.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpush1 : as'.pc < prog.length)
    (hpushN : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffN : offN < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hpush2 : as'.pc + 2 < prog.length)
    (hpushZ : prog.get ⟨as'.pc + 2, hpush2⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZ : offZ < 2 ^ 256)
    (hjump1 : as'.pc + 2 + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 2 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hrel_succ : venomAsmRel lo (psOf ifZ) vs'' { as' with stack := stk })
    (hlk' : lookupBlock ifZ fn.blocks = some bb')
    (hlayout : wOf ifZ + (bodyLen + 4) ≤ wOf bb.label) (hcur : wOf bb.label ≤ N) :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hle : bodyLen + 4 ≤ N := by omega
  obtain ⟨N', hNeq⟩ := Nat.le.dest hle; subst hNeq
  have hjumpi_step := resolved_jumpi_nottaken_sim (offsetToPc := o2pc) (prog := prog) (s := as')
    hstk_c hpush1 hpushN hoffN_lk hoffN hjumpi1 hjumpi
  have hjump_step := resolved_jump_sim (s := { as' with stack := stk, pc := as'.pc + 2 })
    (by simpa using hpush2) (by simpa using hpushZ) hoffZ_lk hoffZ
    (by simpa using hjump1) (by simpa using hjump) hidxZ_lk
  have hterm4 : runAsm 4 o2pc prog as' = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifZ } := by
    rw [show (4 : Nat) = 2 + 2 from rfl, runAsm_append_ok hjumpi_step, hjump_step]
  have hfull : runAsm (bodyLen + 4) o2pc prog as0 = AsmResult.AsmOK { as' with stack := stk, pc := pcOf ifZ } := by
    rw [runAsm_append_ok hbody, hterm4]
  have harr : venomAsmRel lo (psOf (jumpTo ifZ vs'').currentBb) (jumpTo ifZ vs'')
      { as' with stack := stk, pc := pcOf ifZ } := by
    show venomAsmRel lo (psOf ifZ) (jumpTo ifZ vs'') { as' with stack := stk, pc := pcOf ifZ }
    exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hrel_succ)
  have hnh' : (jumpTo ifZ vs'').halted = false := by simp [jumpTo, hnh]
  have hwsucc : wOf (jumpTo ifZ vs'').currentBb ≤ N' := by show wOf ifZ ≤ N'; omega
  exact HbsimMatch_continue_canonWH (bb' := bb') (N' := N') hrb hnh' hfull hlk' harr rfl hwsucc

theorem HbsimMatch_djmp_from_body_canonWH {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen chainLen N : Nat} {rest : List bytes32}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s vs'' : VenomState} {targetLabel : String}
    (hrb : runBlock f' ctx bb s = ExecResult.OK (jumpTo targetLabel vs'')) (hnh : vs''.halted = false)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hdispatch : runAsm chainLen o2pc prog as'
      = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel })
    (hrel_succ : venomAsmRel lo (psOf targetLabel) vs'' { as' with stack := rest })
    (hlk' : lookupBlock targetLabel fn.blocks = some bb')
    (hlayout : wOf targetLabel + (bodyLen + chainLen) ≤ wOf bb.label) (hcur : wOf bb.label ≤ N) :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  have hle : bodyLen + chainLen ≤ N := by omega
  obtain ⟨N', hNeq⟩ := Nat.le.dest hle; subst hNeq
  have hfull : runAsm (bodyLen + chainLen) o2pc prog as0
      = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel } := by
    rw [runAsm_append_ok hbody, hdispatch]
  have harr : venomAsmRel lo (psOf (jumpTo targetLabel vs'').currentBb) (jumpTo targetLabel vs'')
      { as' with stack := rest, pc := pcOf targetLabel } := by
    show venomAsmRel lo (psOf targetLabel) (jumpTo targetLabel vs'') { as' with stack := rest, pc := pcOf targetLabel }
    exact venomAsmRel_jumpTo _ _ _ _ _ (venomAsmRel_setPc hrel_succ)
  have hnh' : (jumpTo targetLabel vs'').halted = false := by simp [jumpTo, hnh]
  have hwsucc : wOf (jumpTo targetLabel vs'').currentBb ≤ N' := by show wOf targetLabel ≤ N'; omega
  exact HbsimMatch_continue_canonWH (bb' := bb') (N' := N') hrb hnh' hfull hlk' harr rfl hwsucc


namespace Example

set_option maxHeartbeats 1600000 in
/-- **Non-vacuity of the JNZ-taken connector for the N-constrained walk Entry.** The concrete conditional
    block `entry: JNZ 1 then else` on the literal program `jnzProg`
    (`[LABEL entry; PUSH 1; PUSH then@11; JUMPI; PUSH else@13; JUMP; …]`, offsets
    `[("then",11),("else",13)]`, offsetToPc `[(11,6),(13,8)]`) satisfies EVERY hypothesis of
    `HbsimMatch_jnz_taken_from_body_canonWH` simultaneously — the condition literal `1 ≠ 0` takes the branch,
    the body (JUMPDEST + condition push) lands at the `PUSH then`, the successor relation holds with the
    condition dropped, and the layout/budget bounds hold — so the connector fires and is not vacuous.
    Uses the literal program deliberately: the *generated* program's label-offset map does not reduce in the
    kernel for this (branching) function, while `jnzProg` does. -/
theorem HbsimMatch_jnz_taken_from_body_canonWH_nonvacuous
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {ctx : VenomContext} {k : Nat}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    HbsimMatch
      (CanonEntryWH jnzStopFnR lo (fun l => if l = "then" then 6 else 8) (fun _ => initPlanState 0)
        (fun l => if l = "then" then 0 else 10))
      ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as 10
      (runBlock (k + 1) ctx jnzEntryR vs) := by
  have hlen : jnzProg.length = 10 := rfl
  set cond : bytes32 := wordOfBytes (List.toByteArray
    (List.replicate (32 - (encodeNumBytes 1).length) (0 : byte) ++ encodeNumBytes 1)) with hcondd
  have hct : cond.toNat = 1 := by rw [hcondd]; exact pushed_offset_toNat 1 (by norm_num)
  have hcondne : cond ≠ EvmYul.UInt256.ofNat 0 := by
    intro h; rw [h, EvmYul.uint256_ofNat_toNat] at hct; simp at hct
  set s1 : AsmState := asmNext as with hs1
  set s2 : AsmState := { asmNext s1 with stack := cond :: s1.stack } with hs2
  have p1 : s1.pc = 1 := by rw [hs1]; show as.pc + 1 = 1; rw [haspc]
  have p2 : s2.pc = 2 := by rw [hs2]; show s1.pc + 1 = 2; rw [p1]
  have hb0 : as.pc < jnzProg.length := by rw [haspc, hlen]; decide
  have hb1 : s1.pc < jnzProg.length := by rw [p1, hlen]; decide
  have hb2 : s2.pc < jnzProg.length := by rw [p2, hlen]; decide
  have hb3 : s2.pc + 1 < jnzProg.length := by rw [p2, hlen]; decide
  have g0 : jnzProg.get ⟨as.pc, hb0⟩ = AsmInst.AsmLabel "entry" := by
    rw [show (⟨as.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext haspc]; rfl
  have g1 : jnzProg.get ⟨s1.pc, hb1⟩ = AsmInst.AsmPush (encodeNumBytes 1) := by
    rw [show (⟨s1.pc, hb1⟩ : Fin _) = ⟨1, by rw [hlen]; decide⟩ from Fin.ext p1]; rfl
  have hpush : jnzProg.get ⟨s2.pc, hb2⟩
      = resolveInst ([("then", 11), ("else", 13)] : AssocList String Nat) (AsmInst.AsmPushLabel "then") := by
    rw [show (⟨s2.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext p2]; rfl
  have e3 : s2.pc + 1 = 3 := by rw [p2]
  have hjumpi : jnzProg.get ⟨s2.pc + 1, hb3⟩ = AsmInst.AsmOp "JUMPI" := by
    conv_lhs => rw [show (⟨s2.pc + 1, hb3⟩ : Fin jnzProg.length) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext e3]
    rfl
  have hpushstep : asmStep ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg s1 = AsmResult.AsmOK s2 := by
    rw [asmStep_push_ok hb1 g1]; rfl
  have hbody : runAsm 2 ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as = AsmResult.AsmOK s2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hb0 (asmStep_label_ok hb0 g0)]
    rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hb1 hpushstep]; rfl
  have hone : (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ { val := 0 } := by decide
  have hrb : runBlock (k + 1) ctx jnzEntryR vs
      = ExecResult.OK (jumpTo "then" { vs with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jnzEntryR, jnzInstR,
      stepInstBase, isTerminator, jumpTo, evalOperand, hvshalt, hone]
  have hnh : ({ vs with instIdx := 0 } : VenomState).halted = false := by simpa using hvshalt
  refine HbsimMatch_jnz_taken_from_body_canonWH (bb' := thenBB) (off := 11) (cond := cond)
    (stk := s1.stack) (bodyLen := 2) hrb hnh hbody rfl hcondne hb2 hpush (by decide) (by norm_num)
    hb3 hjumpi (by decide) ?_ rfl (by decide) (by decide)
  -- successor relation: the JUMPI drops the condition, leaving the entry stack at the `then` pc
  show venomAsmRel lo (initPlanState 0) { vs with instIdx := 0 } { s2 with stack := s1.stack }
  exact venomAsmRel_setPc hrel



/-- A conditional block whose condition literal is ZERO: `entry: JNZ 0 then else` falls through to `else`. -/
def jnzInst0 : Instruction :=
  { id := 0, opcode := Opcode.JNZ,
    operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Label "then", Operand.Label "else"],
    outputs := [] }
def jnzEntry0 : BasicBlock := { label := "entry", instructions := [jnzInst0] }
def jnzStopFn0 : IrFunction := { name := "main", blocks := [jnzEntry0, thenBB, elseBB] }

set_option maxHeartbeats 1600000 in
/-- **Non-vacuity of the JNZ-not-taken connector for the N-constrained walk Entry.** The sibling of
    `HbsimMatch_jnz_taken_from_body_canonWH_nonvacuous`, on the zero-condition block
    `entry: JNZ 0 then else`: the JUMPI falls through (popping the condition) and the following
    `PUSH else@13 ; JUMP` lands at `else` — the four-instruction terminator. Reuses the literal `jnzProg`,
    whose pc 2..5 is exactly `PUSH then@11 ; JUMPI ; PUSH else@13 ; JUMP`, with the arrival state placed at
    pc 2 carrying the zero condition on top (`bodyLen = 0`, so the body-sim run is `runAsm 0`). Every
    hypothesis of the connector is satisfied at once, so it fires. -/
theorem HbsimMatch_jnz_nottaken_from_body_canonWH_nonvacuous
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {ctx : VenomContext} {k : Nat}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 2) :
    HbsimMatch
      (CanonEntryWH jnzStopFn0 lo (fun l => if l = "else" then 8 else 6) (fun _ => initPlanState 0)
        (fun l => if l = "else" then 0 else 10))
      ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg
      { as with stack := EvmYul.UInt256.ofNat 0 :: as.stack } 10
      (runBlock (k + 1) ctx jnzEntry0 vs) := by
  have hlen : jnzProg.length = 10 := rfl
  set as0 : AsmState := { as with stack := EvmYul.UInt256.ofNat 0 :: as.stack } with has0
  have q0 : as0.pc = 2 := by rw [has0]; exact haspc
  have hb2 : as0.pc < jnzProg.length := by rw [q0, hlen]; decide
  have hb3 : as0.pc + 1 < jnzProg.length := by rw [q0, hlen]; decide
  have hb4 : as0.pc + 2 < jnzProg.length := by rw [q0, hlen]; decide
  have hb5 : as0.pc + 2 + 1 < jnzProg.length := by rw [q0, hlen]; decide
  have hpushN : jnzProg.get ⟨as0.pc, hb2⟩
      = resolveInst ([("then", 11), ("else", 13)] : AssocList String Nat) (AsmInst.AsmPushLabel "then") := by
    rw [show (⟨as0.pc, hb2⟩ : Fin _) = ⟨2, by rw [hlen]; decide⟩ from Fin.ext q0]; rfl
  have e3 : as0.pc + 1 = 3 := by rw [q0]
  have hjumpi : jnzProg.get ⟨as0.pc + 1, hb3⟩ = AsmInst.AsmOp "JUMPI" := by
    conv_lhs => rw [show (⟨as0.pc + 1, hb3⟩ : Fin jnzProg.length) = ⟨3, by rw [hlen]; decide⟩ from Fin.ext e3]
    rfl
  have e4 : as0.pc + 2 = 4 := by rw [q0]
  have hpushZ : jnzProg.get ⟨as0.pc + 2, hb4⟩
      = resolveInst ([("then", 11), ("else", 13)] : AssocList String Nat) (AsmInst.AsmPushLabel "else") := by
    conv_lhs => rw [show (⟨as0.pc + 2, hb4⟩ : Fin jnzProg.length) = ⟨4, by rw [hlen]; decide⟩ from Fin.ext e4]
    rfl
  have e5 : as0.pc + 2 + 1 = 5 := by rw [q0]
  have hjump : jnzProg.get ⟨as0.pc + 2 + 1, hb5⟩ = AsmInst.AsmOp "JUMP" := by
    conv_lhs => rw [show (⟨as0.pc + 2 + 1, hb5⟩ : Fin jnzProg.length) = ⟨5, by rw [hlen]; decide⟩ from Fin.ext e5]
    rfl
  have hbody : runAsm 0 ([(11, 6), (13, 8)] : AssocList Nat Nat) jnzProg as0 = AsmResult.AsmOK as0 := by
    simp [runAsm]
  have hzero : (EvmYul.UInt256.ofNat 0 : EvmYul.UInt256) = { val := 0 } := by decide
  have hrb : runBlock (k + 1) ctx jnzEntry0 vs
      = ExecResult.OK (jumpTo "else" { vs with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, jnzEntry0, jnzInst0,
      stepInstBase, isTerminator, jumpTo, evalOperand, hvshalt, hzero]
  have hnh : ({ vs with instIdx := 0 } : VenomState).halted = false := by simpa using hvshalt
  refine HbsimMatch_jnz_nottaken_from_body_canonWH (bb' := elseBB) (offN := 11) (offZ := 13)
    (stk := as.stack) (bodyLen := 0) (ifNz := "then") hrb hnh hbody ?_ hb2 hpushN (by decide) (by norm_num)
    hb3 hjumpi hb4 hpushZ (by decide) (by norm_num) hb5 hjump (by decide) ?_ rfl (by decide) (by decide)
  · -- the arrival stack carries the zero condition on top
    show as0.stack = EvmYul.UInt256.ofNat 0 :: as.stack
    rw [has0]
  · -- successor relation: the JUMPI pops the condition, restoring the entry stack
    show venomAsmRel lo (initPlanState 0) { vs with instIdx := 0 } { as0 with stack := as.stack }
    exact venomAsmRel_setPc hrel


/-- A dynamic-jump block with a literal selector: `entry: DJMP 0 t0 t1` selects label index 0 = `t0`. -/
def djmpInst0 : Instruction :=
  { id := 0, opcode := Opcode.DJMP,
    operands := [Operand.Lit (EvmYul.UInt256.ofNat 0), Operand.Label "t0", Operand.Label "t1"],
    outputs := [] }
def djmpEntry0 : BasicBlock := { label := "entry", instructions := [djmpInst0] }
def dT0 : BasicBlock := { label := "t0", instructions := [stopInst] }
def dT1 : BasicBlock := { label := "t1", instructions := [stopInst] }
def djmpFn0 : IrFunction := { name := "main", blocks := [djmpEntry0, dT0, dT1] }

/-- The dispatch tail: a bare `JUMP` consuming an already-computed destination, then `t0`'s block. -/
def djmpProg0 : List AsmInst :=
  [AsmInst.AsmOp "JUMP", AsmInst.AsmLabel "t0", AsmInst.AsmOp "STOP"]

set_option maxHeartbeats 1600000 in
/-- **Non-vacuity of the DJMP connector for the N-constrained walk Entry.** Completes the
    continuing-connector witness set (JMP `e9bd237`-era, JNZ-taken `e9bd237`, JNZ-not-taken `be87070`).
    The venom side is `entry: DJMP 0 t0 t1` — the selector literal `0` indexes the label list, so the block
    steps to `OK (jumpTo "t0" …)`. The asm side is the simplest real dispatch chain: a bare `JUMP`
    (`chainLen = 1`) consuming a destination already on the stack, which `asmJump` pops and resolves through
    `offsetToPc [(7,1)]` to `pcOf "t0" = 1`, restoring the entry stack. Every connector hypothesis holds at
    once (`bodyLen = 0`, so the body-sim run is `runAsm 0`), so the connector fires. -/
theorem HbsimMatch_djmp_from_body_canonWH_nonvacuous
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {ctx : VenomContext} {k : Nat}
    (hvshalt : vs.halted = false)
    (hrel : venomAsmRel lo (initPlanState 0) vs as) (haspc : as.pc = 0) :
    HbsimMatch
      (CanonEntryWH djmpFn0 lo (fun l => if l = "t0" then 1 else 2) (fun _ => initPlanState 0)
        (fun l => if l = "t0" then 0 else 10))
      ([(7, 1)] : AssocList Nat Nat) djmpProg0
      { as with stack := EvmYul.UInt256.ofNat 7 :: as.stack } 10
      (runBlock (k + 1) ctx djmpEntry0 vs) := by
  have hlen : djmpProg0.length = 3 := rfl
  set as' : AsmState := { as with stack := EvmYul.UInt256.ofNat 7 :: as.stack } with has'
  have q0 : as'.pc = 0 := by rw [has']; exact haspc
  have hb0 : as'.pc < djmpProg0.length := by rw [q0, hlen]; decide
  have gJ : djmpProg0.get ⟨as'.pc, hb0⟩ = AsmInst.AsmOp "JUMP" := by
    rw [show (⟨as'.pc, hb0⟩ : Fin _) = ⟨0, by rw [hlen]; decide⟩ from Fin.ext q0]; rfl
  have hbody : runAsm 0 ([(7, 1)] : AssocList Nat Nat) djmpProg0 as' = AsmResult.AsmOK as' := by
    simp [runAsm]
  -- the dispatch chain: one bare JUMP, resolved via offsetToPc
  have hdispatch : runAsm 1 ([(7, 1)] : AssocList Nat Nat) djmpProg0 as'
      = AsmResult.AsmOK { as' with stack := as.stack, pc := 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hb0 ?step]
    · rfl
    · rw [asmStep_jump_ok hb0 gJ]
      show asmJump ([(7, 1)] : AssocList Nat Nat) as' = _
      rw [has']; rfl
  have hsel : (EvmYul.UInt256.ofNat 0).toNat = 0 := by decide
  have hrb : runBlock (k + 1) ctx djmpEntry0 vs
      = ExecResult.OK (jumpTo "t0" { vs with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, djmpEntry0, djmpInst0,
      stepInstBase, isTerminator, jumpTo, evalOperand, extractLabels, hvshalt, hsel]
  have hnh : ({ vs with instIdx := 0 } : VenomState).halted = false := by simpa using hvshalt
  refine HbsimMatch_djmp_from_body_canonWH (bb' := dT0) (targetLabel := "t0") (chainLen := 1)
    (rest := as.stack) (bodyLen := 0) hrb hnh hbody ?_ ?_ rfl (by decide) (by decide)
  · -- the dispatch run lands at pcOf "t0" = 1 with the entry stack
    show runAsm 1 ([(7, 1)] : AssocList Nat Nat) djmpProg0 as'
        = AsmResult.AsmOK { as' with stack := as.stack, pc := (if "t0" = "t0" then 1 else 2) }
    simpa using hdispatch
  · -- successor relation: the JUMP popped the destination, restoring the entry stack
    show venomAsmRel lo (initPlanState 0) { vs with instIdx := 0 } { as' with stack := as.stack }
    exact venomAsmRel_setPc hrel

end Example

/-! ## Top-level bridge: the per-block HbsimMatch is exactly codegen_correct's input -/


/-- **`codegen_correct` from a per-block `HbsimMatch`.** The hbsim connectors of this arc each produce a
    `HbsimMatch` for one block. This shows the `∀`-block `HbsimMatch` is exactly what `codegen_correct`
    consumes: each is converted to the raw hbsim match by `HbsimMatch_is_hbsim` (the proven
    correspondence), and `codegen_correct` does the rest. So a whole-function result reduces to supplying
    the per-block `HbsimMatch` — which the connectors build from the body sim and the terminator. -/
theorem codegen_correct_of_HbsimMatch
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String}
    (Entry : VenomState → AsmState → Nat → Prop)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hbsim : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat) (bb : BasicBlock),
        Entry s asm N → lookupBlock s.currentBb fn.blocks = some bb →
        HbsimMatch Entry (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm N
          (runBlock f' ctx bb s))
    (hentry : Entry { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as
        (asmResolve (executePlan ops)).1.length) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length
         (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) :=
  codegen_correct Entry hplan hent hlk hlbl
    (fun s asm N f' bb hE hL => by
      have h := hbsim s asm N f' bb hE hL
      unfold HbsimMatch at h
      cases hr : runBlock f' ctx bb s with
      | OK s' => rw [hr] at h; exact h
      | Halt s' => rw [hr] at h; exact h
      | Abort a s' => cases a <;> (rw [hr] at h; exact h)
      | IntRet _ _ => rw [hr] at h; exact h
      | Error _ => rw [hr] at h; exact h) hentry

/-! ## The CFG assembly, base case: single-block via the HbsimMatch route -/


/-- `lookupBlock` on a singleton block list: succeeds only at that block's label. -/
theorem lookupBlock_singleton {lbl : String} {bb bb' : BasicBlock}
    (h : lookupBlock lbl [bb] = some bb') : lbl = bb.label ∧ bb' = bb := by
  simp only [lookupBlock, List.find?] at h
  split at h
  · rename_i hp; cases h
    refine ⟨?_, rfl⟩
    have : bb.label = lbl := by simpa using hp
    exact this.symm
  · simp at h

/-- **The single-block CFG assembly, via the HbsimMatch route.** For a one-block function the `∀`-block
    quantifier of `codegen_correct`'s hbsim collapses to a single per-state `HbsimMatch` obligation
    (`lookupBlock` succeeds only at the block's label), which the connectors discharge from the body sim
    and the terminator. The base case of the CFG assembly; the general case adds successor threading. -/
theorem codegen_correct_singleBlock_of_HbsimMatch
    {fuel : Nat} {ctx : VenomContext} {fnName : String} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {bb : BasicBlock}
    (Entry : VenomState → AsmState → Nat → Prop)
    (hplan : generateFnPlan { name := fnName, blocks := [bb] } fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some { name := fnName, blocks := [bb] })
    (hlbl : fnEntryLabel { name := fnName, blocks := [bb] } = some entryLbl)
    (hstep : ∀ (s : VenomState) (asm : AsmState) (N f' : Nat),
        Entry s asm N → s.currentBb = bb.label →
        HbsimMatch Entry (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm N
          (runBlock f' ctx bb s))
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
  refine codegen_correct_of_HbsimMatch Entry hplan hent hlk hlbl ?_ hentry
  intro s asm N f' bb' hE hL
  obtain ⟨hcurEq, hbbEq⟩ := lookupBlock_singleton hL
  subst hbbEq
  exact hstep s asm N f' hE hcurEq

/-! ## The CFG assembly, general shape: ∀-block hbsim ⇒ per-block obligation over the function -/


/-- `lookupBlock` returns a member of the list whose label matches. -/
theorem lookupBlock_mem {lbl : String} {bs : List BasicBlock} {bb : BasicBlock}
    (h : lookupBlock lbl bs = some bb) : bb ∈ bs ∧ bb.label = lbl := by
  simp only [lookupBlock] at h
  exact ⟨List.mem_of_find?_eq_some h, by
    have := List.find?_some h; simpa using this⟩

/-- **The general CFG assembly reduction, via the HbsimMatch route.** For an arbitrary function,
    `codegen_correct`'s ∀-block hbsim reduces to a per-block obligation: for every block of the function,
    when the walk is at that block, its `HbsimMatch` holds. `lookupBlock` returns a block of the function
    matching the current label, so the ∀ over states-and-lookups becomes a ∀ over the function's blocks.
    Each per-block obligation is what the connectors discharge (body sim + terminator, and for continuing
    blocks the successor-recording). This is the shape of the CFG assembly; what remains is discharging
    the per-block obligation for each block — the semantic body-sim + successor content.

    ⚠️ NB the per-block `hstep` is `∀ N` (the walk budget), and `HbsimMatch (Halt) N` is FALSE for
    `N < blockLen`. So this reduction is only dischargeable with an `Entry` that CONSTRAINS `N` (e.g.
    `codegen_correct_singleBlockHalt`'s `N = programLength`, threading `N' = N − blockLen` to successors);
    a bare `CanonEntry` (no N-constraint) makes the `hstep` unsatisfiable — see the retracted
    `codegen_correct_ofRecipes` note below. -/
theorem codegen_correct_ofBlocks_HbsimMatch
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String}
    (Entry : VenomState → AsmState → Nat → Prop)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hstep : ∀ bb ∈ fn.blocks, ∀ (s : VenomState) (asm : AsmState) (N f' : Nat),
        Entry s asm N → s.currentBb = bb.label →
        HbsimMatch Entry (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm N
          (runBlock f' ctx bb s))
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
  refine codegen_correct_of_HbsimMatch Entry hplan hent hlk hlbl ?_ hentry
  intro s asm N f' bb hE hL
  obtain ⟨hmem, hlbleq⟩ := lookupBlock_mem hL
  exact hstep bb hmem s asm N f' hE hlbleq.symm

/-! ## Discharging a per-block obligation from the body thread (STOP): runBlock derived, not assumed -/


/-- **The Venom-side `hrb` for a body+STOP block, derived from the body thread.** `runBlock` reduces to
    `execBlock` on the body-end state (`runBlock_to_term`), whose `instIdx` is `front.length`
    (`execBodyThread_instIdx`) — exactly the STOP's position — so the STOP step halts at `haltState sEnd`.
    This turns the `hrb` hypothesis of `HbsimMatch_stop_from_body` into a derivation. -/
theorem runBlock_body_stop (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (stopInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [stopInst])
    (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.Halt (haltState sEnd) := by
  rw [runBlock_to_term ctx bb (restFuel + 1) front stopInst hd tl s sEnd hbb hcons hphi hnonterm hthread]
  have hidx : sEnd.instIdx = front.length := by
    have h := execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
    simpa using h
  have hget : getInstruction bb sEnd.instIdx = some stopInst := by
    rw [hidx]; simp [getInstruction, hbb]
  simp only [execBlock, hget, stepInstBase, hstopop]

/-- **A STOP block's `HbsimMatch` from the body thread + the body sim's asm output.** No `runBlock`
    result is assumed: `runBlock_body_stop` derives it from the body thread. So the STOP per-block
    obligation is discharged from exactly the body simulation's natural interface — the Venom body thread
    (`hthread`) and the asm run + relation at the body-end (`hbody`/`hrel'`). -/
theorem HbsimMatch_stop_bodyThread {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {bodyLen N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hpc : as'.pc < prog.length) (hstop : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (front.length + (restFuel + 1)) ctx bb s) :=
  HbsimMatch_stop_from_body
    (runBlock_body_stop ctx bb restFuel front stopInst hd tl s sEnd hbb hstopop hcons hphi hnonterm hthread)
    hbody hrel' hpc hstop hle

/-! ## runBlock-derivation, general + halting/continuing representatives -/


/-- The body-end state sees the terminator as its current instruction. -/
theorem getInstruction_bodyEnd {bb : BasicBlock} {front : List Instruction} {term : Instruction}
    {s sEnd : VenomState} (hbb : bb.instructions = front ++ [term])
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    getInstruction bb sEnd.instIdx = some term := by
  have hidx : sEnd.instIdx = front.length := by
    have h := execBodyThread_instIdx front 0 { s with instIdx := 0 } sEnd rfl hthread
    simpa using h
  rw [hidx]; simp [getInstruction, hbb]

/-- **General: `runBlock` of a body+terminator block reduces to the terminator's step on the body-end
    state.** Factors the common `runBlock_to_term` + body-thread part; each terminator instantiates the
    step (`hstep`). -/
theorem runBlock_body_term (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (term hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (R : ExecResult)
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hstep : ∀ inst, getInstruction bb sEnd.instIdx = some inst →
      execBlock (restFuel + 1) ctx bb sEnd = R) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = R := by
  rw [runBlock_to_term ctx bb (restFuel + 1) front term hd tl s sEnd hbb hcons hphi hnonterm hthread]
  exact hstep term (getInstruction_bodyEnd hbb hthread)

/-- INVALID instantiation: the block faults at the body-end state. -/
theorem runBlock_body_invalid (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (invInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState)
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty sEnd)) := by
  refine runBlock_body_term ctx bb restFuel front invInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hinvop]

/-- JMP instantiation (continuing): the block steps to `OK (jumpTo lbl sEnd)`. -/
theorem runBlock_body_jmp (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (jmpInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (lbl : String)
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo lbl sEnd) := by
  refine runBlock_body_term ctx bb restFuel front jmpInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hjmpop, hoperands,
    isTerminator]
  show (if (jumpTo lbl sEnd).halted = true then _ else _) = _
  rw [show (jumpTo lbl sEnd).halted = sEnd.halted from rfl, hnothalt]
  rfl

/-! ## runBlock-derivation for the rest of the terminator family (RETURN/REVERT/SELFDESTRUCT/JNZ/DJMP) -/


/-- RETURN instantiation. -/
theorem runBlock_body_return (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (retInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (offOp szOp : Operand) (off sz : bytes32)
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RETURN)
    (hoperands : retInst.operands = [offOp, szOp])
    (hoff : evalOperand offOp sEnd = some off) (hsz : evalOperand szOp sEnd = some sz)
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.Halt (haltState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) := by
  refine runBlock_body_term ctx bb restFuel front retInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hoff, hsz]

/-- REVERT instantiation. -/
theorem runBlock_body_revert (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (revInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (offOp szOp : Operand) (off sz : bytes32)
    (hbb : bb.instructions = front ++ [revInst]) (hop : revInst.opcode = Opcode.REVERT)
    (hoperands : revInst.operands = [offOp, szOp])
    (hoff : evalOperand offOp sEnd = some off) (hsz : evalOperand szOp sEnd = some sz)
    (hcons : front ++ [revInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.Abort AbortType.RevertAbort
          (revertState (setReturndata (readMemory off.toNat sz.toNat sEnd) sEnd)) := by
  refine runBlock_body_term ctx bb restFuel front revInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hoff, hsz]

/-- SELFDESTRUCT instantiation (accounts change). -/
theorem runBlock_body_selfdestruct (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (sdInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (addrOp : Operand) (addr : bytes32)
    (hbb : bb.instructions = front ++ [sdInst]) (hop : sdInst.opcode = Opcode.SELFDESTRUCT)
    (hoperands : sdInst.operands = [addrOp]) (haddr : evalOperand addrOp sEnd = some addr)
    (hcons : front ++ [sdInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd) :
    runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.Halt (haltState (selfdestruct addr sEnd)) := by
  refine runBlock_body_term ctx bb restFuel front sdInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, haddr,
    selfdestruct]

/-- JNZ taken (condition nonzero). -/
theorem runBlock_body_jnz_taken (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (jnzInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (condOp : Operand) (ifNz ifZ : String) (cond : bytes32)
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcond : evalOperand condOp sEnd = some cond) (hne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo ifNz sEnd) := by
  refine runBlock_body_term ctx bb restFuel front jnzInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  have hb : (cond != ({ val := 0 } : bytes32)) = true := by
    rw [bne_iff_ne]; intro h; exact hne h
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hcond,
    if_pos hb, isTerminator]
  show (if (jumpTo ifNz sEnd).halted = true then _ else _) = _
  rw [show (jumpTo ifNz sEnd).halted = sEnd.halted from rfl, hnothalt]; rfl

/-- JNZ not-taken (condition zero). -/
theorem runBlock_body_jnz_nottaken (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (jnzInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (condOp : Operand) (ifNz ifZ : String)
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcond : evalOperand condOp sEnd = some ({ val := 0 } : bytes32))
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false) :
    runBlock (front.length + (restFuel + 1)) ctx bb s = ExecResult.OK (jumpTo ifZ sEnd) := by
  refine runBlock_body_term ctx bb restFuel front jnzInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hcond,
    bne_self_eq_false, if_neg (by decide : ¬ (false = true)), isTerminator]
  show (if (jumpTo ifZ sEnd).halted = true then _ else _) = _
  rw [show (jumpTo ifZ sEnd).halted = sEnd.halted from rfl, hnothalt]; rfl

/-- DJMP (dynamic jump to the selector-indexed label). -/
theorem runBlock_body_djmp (ctx : VenomContext) (bb : BasicBlock) (restFuel : Nat)
    (front : List Instruction) (dInst hd : Instruction) (tl : List Instruction)
    (s sEnd : VenomState) (selectorOp : Operand) (labelOps : List Operand)
    (idx : bytes32) (labels : List String) (hi : idx.toNat < labels.length)
    (hbb : bb.instructions = front ++ [dInst]) (hop : dInst.opcode = Opcode.DJMP)
    (hoperands : dInst.operands = selectorOp :: labelOps)
    (hsel : evalOperand selectorOp sEnd = some idx) (hlabels : extractLabels labelOps = some labels)
    (hcons : front ++ [dInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false) :
    runBlock (front.length + (restFuel + 1)) ctx bb s
      = ExecResult.OK (jumpTo (labels.get ⟨idx.toNat, hi⟩) sEnd) := by
  refine runBlock_body_term ctx bb restFuel front dInst hd tl s sEnd _ hbb hcons hphi hnonterm
    hthread ?_
  intro inst hget
  simp only [execBlock, getInstruction_bodyEnd hbb hthread, stepInstBase, hop, hoperands, hsel,
    hlabels, dif_pos hi, isTerminator]
  show (if (jumpTo _ sEnd).halted = true then _ else _) = _
  rw [show (jumpTo (labels.get ⟨idx.toNat, hi⟩) sEnd).halted = sEnd.halted from rfl, hnothalt]; rfl

/-! ## The alignment bridge: genBlockBodyH_sim_inv output → HbsimMatch (the last gap closed) -/


/-- **The alignment bridge: `genBlockBodyH_sim_inv`'s output → `HbsimMatch` for a STOP block.**

`genBlockBodyH_sim_inv` produces the body's asm run plus `venomAsmRel` at the *`gvBodyStep`-fold* state
(its Venom body model). `runBlock` threads the body via `execBodyThread`, and `execBodyThread_eq_gvFold`
shows the two coincide. So the body sim's `venomAsmRel` — stated against the fold — is exactly the
relation `HbsimMatch_stop_bodyThread` wants against the `execBodyThread` end state, and the STOP block's
`HbsimMatch` follows. This closes the last gap between the reduction chain and the existing per-instruction
body simulation. -/
theorem HbsimMatch_stop_of_gvFold {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {bodyLen N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel_gv : venomAsmRel lo ps'
      ((front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 }) as')
    (hpc : as'.pc < prog.length) (hstop : prog.get ⟨as'.pc, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : bodyLen + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (front.length + (restFuel + 1)) ctx bb s) := by
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel_gv
  exact HbsimMatch_stop_bodyThread hbb hstopop hcons hphi hnonterm hthread hbody hrel_gv hpc hstop hle

/-! ## The full stack: a STOP block of modeled instructions ⇒ HbsimMatch, from RegularBodyH -/


/-- **`venomAsmRel` is preserved by popping the shared TOS** (plan `stackPop 1` ↔ asm cons-tail). Only
    `planStackRel` reads the stacks; the spill/memory relations and the 9 shared-field equalities are
    untouched by a stack-only update. -/
theorem venomAsmRel_pop_tos {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    {as : AsmState} {a : bytes32} {A : List bytes32}
    (hrel : venomAsmRel lo ps vs as) (hstk : as.stack = a :: A) :
    venomAsmRel lo { ps with stack := stackPop 1 ps.stack } vs { as with stack := A } := by
  obtain ⟨hplan, hspill, hmem, hacc, htr, hrd, hlog, hcc, htx, hbc, hcode, hph⟩ := hrel
  rw [hstk] at hplan
  exact ⟨planStackRel_pop hplan, hspill, hmem, hacc, htr, hrd, hlog, hcc, htx, hbc, hcode, hph⟩

/-- The regular-instruction body plan (ops, end-state) — the fold `genBlockBodyH_sim_inv` builds over the
    block body `front`. -/
abbrev bodyPlanRIP (liveness : DfState (List String)) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (nextLiveness : List String) (curBbLabel : String)
    (front : List Instruction) (ps0 : PlanState) : List StackOp × PlanState :=
  (front.zipIdx 0).foldl
    (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1
      nextLiveness false true curBbLabel acc.2).1,
      (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel acc.2).2))
    ([], ps0)

/-- **The full stack: a STOP block of modeled instructions ⇒ `HbsimMatch`, from the per-instruction
    condition `RegularBodyH`.** Threads the three existing layers:
    `bodyStepsReadyH_regular_list` (RegularBodyH ⇒ BodyStepsReadyH) → `genBlockBodyH_sim_inv` (the body
    simulation, producing the asm run + `venomAsmRel` at the gvBodyStep fold) → `HbsimMatch_stop_of_gvFold`
    (⇒ the block's `HbsimMatch`). So for a STOP block whose body is modeled regular opcodes, the whole
    per-block obligation reduces to exactly `RegularBodyH` — the per-instruction correctness — plus the
    structural plan-state invariants and the entry relation. -/
theorem HbsimMatch_stop_regular {Entry : VenomState → AsmState → Nat → Prop}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    -- the per-instruction condition (irreducible) + structural invariants
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1))
    -- STOP placed right after the body
    (hpc : as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length < prog.length)
    (hstop : prog.get ⟨as0.pc + (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : (executePlan (bodyPlanRIP liveness dfg cfg fn nextLiveness curBbLabel front ps0).1).length + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (front.length + (restFuel + 1)) ctx bb s) := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hstop_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "STOP" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hstop
  exact HbsimMatch_stop_of_gvFold hbb hstopop hcons hphi hnonterm hthread hrun hrel'
    hpc_as hstop_as hle

/-! ## Sound rebuild: INVALID (halting, no emit) and JMP (continuing, PUSH-label emit) at RegularBodyH
    via the CONCRETE post-body position (the vacuity-free formulation) -/


/-- INVALID full-stack through the body sim (sound, concrete-position formulation — the halting sibling
    of STOP). INVALID has no operands and emits no code, so it sits at the CONCRETE post-body position
    `as0.pc + (executePlan bodyPlan).1.length`; the terminator facts are stated there (not via a
    `∀`-quantified `hmk`, which was unsatisfiable). The sim gives `as'.pc = as0.pc + L`, transferring
    them to the existential `as'`. -/
theorem HbsimMatch_invalid_regular {Entry : VenomState → AsmState → Nat → Prop}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1))
    (hpc : as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length < prog.length)
    (hinv : prog.get ⟨as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length, hpc⟩ = AsmInst.AsmOp "INVALID")
    (hle : (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (front.length + (restFuel + 1)) ctx bb s) := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) (offsetToPc := o2pc) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hpc_as : as'.pc < prog.length := hpc' ▸ hpc
  have hinv_as : prog.get ⟨as'.pc, hpc_as⟩ = AsmInst.AsmOp "INVALID" := by
    rw [show (⟨as'.pc, hpc_as⟩ : Fin prog.length) = ⟨_, hpc⟩ from Fin.ext hpc']
    exact hinv
  exact HbsimMatch_invalid_from_body
    (runBlock_body_invalid ctx bb restFuel front invInst hd tl s sEnd hbb hinvop hcons hphi hnonterm
      hthread)
    hrun hrel' hpc_as hinv_as hle


/-- JMP full-stack through the body sim (sound, concrete-position formulation — the continuing shape).
    `JMP target` has `computeOperands = []`, so its terminator asm is `joinOps ++ [PUSH target; JUMP]`
    where `joinOps` is the join reorder (`reorderPlan` for the target's expected layout). **This lemma
    handles the EMPTY-JOIN case** (`joinOps = []` — the arriving layout already matches the target, common
    for straight-through edges): then `PUSH; JUMP` are adjacent right after the body, at the CONCRETE
    positions `as0.pc + L` / `+1` (L = the body plan's asm length), and the program facts are stated there
    and transferred to the existential `as'` via `as'.pc = as0.pc + L`. For a JMP that NEEDS a join
    reorder the `PUSH` sits after the SWAPs, so `hpush`/`hjump` (as stated at `as0.pc + L`) cannot be
    discharged — that case is the mature `GenBlockSim` machinery's job, not this lemma's. The one
    inter-block input is the successor-recording `hps` (post-body plan fold = target's recorded entry),
    stated against the concrete plan fold (not `as'`), so it is satisfiable. -/
theorem HbsimMatch_jmp_regular
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst} {pcOf : String → Nat} {psOf : String → PlanState}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction}
    {s sEnd : VenomState} {S : List String} {target : String} {off : Nat}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label target])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hreg : RegularBodyH lo nextLiveness o2pc prog dem front S)
    (hsd : StackDiscH ((front.zipIdx 0).map (fun _ => dem)).sum ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1))
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hps : ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).2 = psOf target)
    (hpush1 : as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length < prog.length)
    (hpush : prog.get ⟨as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hle : (executePlan ((front.zipIdx 0).foldl
        (fun acc x => (acc.1 ++ (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness
          false true curBbLabel acc.2).1,
          (generateRegularInstPlan liveness dfg cfg fn x.1 nextLiveness false true curBbLabel
            acc.2).2)) ([], ps0)).1).length + 2 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N
      (runBlock (front.length + (restFuel + 1)) ctx bb s) := by
  have hbrh := bodyStepsReadyH_regular_list (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (curBbLabel := curBbLabel) (offsetToPc := o2pc) front S 0 hreg
  obtain ⟨as', hrun, hrel', hpc', _, _⟩ := genBlockBodyH_sim_inv
    (fun z p => generateRegularInstPlan liveness dfg cfg fn z.1 nextLiveness false true curBbLabel p)
    (fun _ => dem) (front.zipIdx 0) S ps0 { s with instIdx := 0 } as0 hbrh hsd hsv hrel0 hblock
  have hgv : (front.zipIdx 0).foldl (fun v x => gvBodyStep x v) { s with instIdx := 0 } = sEnd :=
    execBodyThread_eq_gvFold front 0 { s with instIdx := 0 } sEnd hthread
  rw [hgv] at hrel'
  have hpc_as1 : as'.pc < prog.length := hpc' ▸ hpush1
  have hpush_as : prog.get ⟨as'.pc, hpc_as1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target) := by
    rw [show (⟨as'.pc, hpc_as1⟩ : Fin prog.length) = ⟨_, hpush1⟩ from Fin.ext hpc']
    exact hpush
  have hjump_as1 : as'.pc + 1 < prog.length := hpc' ▸ hjump1
  have hjump_as : prog.get ⟨as'.pc + 1, hjump_as1⟩ = AsmInst.AsmOp "JUMP" := by
    rw [show (⟨as'.pc + 1, hjump_as1⟩ : Fin prog.length) = ⟨_, hjump1⟩ from Fin.ext (congrArg (· + 1) hpc')]
    exact hjump
  exact HbsimMatch_jmp_from_body (bb' := bb') (target := target) (off := off)
    (runBlock_body_jmp ctx bb restFuel front jmpInst hd tl s sEnd target hbb hjmpop hoperands hcons
      hphi hnonterm hthread hnothalt)
    hnothalt hrun hrel' hps hpc_as1 hpush_as hoff_lk hoff hjump_as1 hjump_as hidx_lk hlk' hle

/-! ## ⚠️ Vacuity refutation: the ∀-∃ `hmk` shape is UNSATISFIABLE (terminator `_regular` retraction) -/


/-- **The `∀ as' bodyLen, as'.pc = as0.pc + bodyLen → ∃ (h : as'.pc < prog.length), …` shape is
    unsatisfiable for any finite `prog`.** An earlier formulation of the operand/continuing terminator
    full-stacks (INVALID / JMP / RETURN / REVERT / SELFDESTRUCT / JNZ / DJMP `_regular`) packaged the
    terminator's resolved-asm facts this way, obtaining them from the body sim's *existential* `bodyLen`.
    But that made `bodyLen` universally quantified in the hypothesis: choose `bodyLen = prog.length`, so
    `as'.pc = as0.pc + prog.length ≥ prog.length` and the required `h : as'.pc < prog.length` cannot
    exist. Those lemmas, though valid, could never be APPLIED to a real function — they were vacuous, so
    they are retracted (this refutation is kept in their place, per the "keep the refutation, remove the
    trap" rule). The SOUND formulation (as in `HbsimMatch_stop_regular`) states the terminator facts
    about the CONCRETE post-body position `as0.pc + (executePlan bodyPlan).1.length`, and DERIVES any
    stack / successor-recording facts from the body sim's `venomAsmRel` (`planStackRel_peek`, …) rather
    than taking them as `∀`-quantified inputs (a stack fact quantified over all `as'` at a fixed pc is as
    unsatisfiable as the pc bound). Rebuilding the operand/continuing terminators on that footing is the
    open follow-up. -/
theorem hmk_shape_unsatisfiable
    (as0pc : Nat) (offW szW : bytes32) (rest : List bytes32) (N : Nat) (prog : List AsmInst) :
    ¬ (∀ (as' : AsmState) (bodyLen : Nat), as'.pc = as0pc + bodyLen →
        ∃ (h : as'.pc < prog.length), prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "RETURN"
          ∧ as'.stack = offW :: szW :: rest ∧ bodyLen + 1 ≤ N) := by
  intro hmk
  obtain ⟨h, _, _, _⟩ := hmk { (default : AsmState) with pc := as0pc + prog.length } prog.length rfl
  exact Nat.not_lt.2 (Nat.le_add_left prog.length as0pc) h

/-! ## Non-vacuity witness: the SOUND STOP `_regular` actually fires (counterpart to the refutation) -/


/-- **Non-vacuity of the sound STOP `_regular`.** A bare `[STOP]` block (front = `[]`) instantiates
    `HbsimMatch_stop_regular` with EVERY structural/reducible hypothesis discharged — `RegularBodyH []`
    is `True`, `execBodyThread []` is identity, the empty plan fold gives an empty body asm — leaving only
    the genuine semantic inputs (`venomAsmRel`, `StackDiscH`, `StackIsVars` — the invariants a real block
    always carries) and the concrete STOP placement. So the lemma FIRES; it is not the vacuous ∀-∃ `hmk`
    trap that its retracted siblings were. This is the "exhibit a witness for every hypothesis" check the
    original vacuous version could never have survived. -/
theorem HbsimMatch_stop_regular_nonvacuous
    {Entry : VenomState → AsmState → Nat → Prop}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s : VenomState} {S : List String} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hphi : stopInst.opcode ≠ Opcode.PHI)
    (hsd : StackDiscH 0 ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc [])
    (hpc : as0.pc < prog.length) (hstop : prog.get ⟨as0.pc, hpc⟩ = AsmInst.AsmOp "STOP")
    (hle : 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (0 + (restFuel + 1)) ctx bb s) := by
  refine HbsimMatch_stop_regular (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) (front := [])
    (lo := lo) (ps0 := ps0) (S := S) (o2pc := o2pc) (prog := prog) (as0 := as0)
    (hd := stopInst) (tl := []) (sEnd := { s with instIdx := 0 })
    (by simpa using hbb) hstopop (by simpa using hbb) hphi (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl                                             -- execBodyThread [] = identity
  · trivial                                         -- RegularBodyH [] = True
  · simpa using hsd
  · exact hsv
  · exact hrel0
  · exact hblock
  · exact hpc
  · exact hstop
  · exact hle


/-- **Non-vacuity of the sound JMP `_regular` — the CONTINUING discriminating case.** A bare `[JMP target]`
    block (front = []) instantiates `HbsimMatch_jmp_regular` with every structural/reducible hypothesis
    discharged, leaving only the genuine inter-block inputs: the entry `venomAsmRel`/invariants, the
    successor lookup + successor-recording `hps` (post-body plan fold = `psOf target`, here `ps0` since the
    body is empty), and the concrete `PUSH target; JUMP` placement + label/offset resolutions. The lemma
    FIRES, producing the walk's `HbsimMatch` with the `CanonEntry`. Unlike STOP this exercises the
    successor-recording clause, so it validates the continuing shape's rebuild, not just the halting one.
    (This witnesses the EMPTY-JOIN JMP subclass that `HbsimMatch_jmp_regular` handles — `PUSH; JUMP`
    adjacent right after the body; a JMP needing a join reorder is out of that lemma's scope, per its
    docstring.) -/
theorem HbsimMatch_jmp_regular_nonvacuous
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat}
    {prog : List AsmInst} {pcOf : String → Nat} {psOf : String → PlanState}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb bb' : BasicBlock}
    {s : VenomState} {S : List String} {jmpInst : Instruction} {target : String} {off : Nat}
    (hbb : bb.instructions = [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label target])
    (hnothalt : s.halted = false)
    (hsd : StackDiscH 0 ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc [])
    (hlk' : lookupBlock target fn.blocks = some bb')
    (hps : ps0 = psOf target)
    (hpush1 : as0.pc < prog.length)
    (hpush : prog.get ⟨as0.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as0.pc + 1 < prog.length)
    (hjump : prog.get ⟨as0.pc + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf target))
    (hle : 2 ≤ N) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N
      (runBlock (0 + (restFuel + 1)) ctx bb s) := by
  refine HbsimMatch_jmp_regular (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) (front := [])
    (lo := lo) (ps0 := ps0) (S := S) (o2pc := o2pc) (offsets := offsets) (prog := prog)
    (as0 := as0) (pcOf := pcOf) (psOf := psOf) (target := target) (off := off)
    (hd := jmpInst) (tl := []) (sEnd := { s with instIdx := 0 }) (bb' := bb')
    (by simpa using hbb) hjmpop hoperands (by simp) (by rw [hjmpop]; decide) (by simp) rfl
    (by simpa using hnothalt) trivial ?_ hsv hrel0 ?_ hlk' ?_ ?_ ?_ hoff_lk hoff ?_ ?_ hidx_lk ?_
  · simpa using hsd
  · exact hblock
  · exact hps
  · exact hpush1
  · exact hpush
  · exact hjump1
  · exact hjump
  · exact hle

/-! ## Filling the SELFDESTRUCT gap in the mature terminator hstep family
    (the one codegen terminator with a connector but no `hstep_regularHSVP_*`) -/


/-- **Spill-aware residual SELFDESTRUCT segment (VAR operand)** — the single-operand, accounts-terminal
    twin of `hasm_regularHSVP_return_var`. Body prefix sim + single-operand emit (`emitInputPlan_single_var_sim`
    puts the beneficiary on top) + the SELFDESTRUCT halt (`asmSelfdestruct_ok`); the terminal relation is
    `venomAsmRel_selfdestruct` (accounts congruence). No memory-safety segment (SELFDESTRUCT reads no memory). -/
theorem hasm_regularHSVP_selfdestruct_var {prog : List AsmInst} {offsetToPc : AssocList Nat Nat}
    {lo : AssocList String Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {addrv : String} {waddr : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen budget : Nat}
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (haddrS : addrv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (haddrM : alookup' M1 (Operand.Var addrv) = none)
    (hliveaddr : nl.contains addrv = true)
    (hvaddr : lookupVar addrv sEnd = some waddr)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (emitInputPlan opc [Operand.Var addrv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var addrv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hbudget : bodyLen + emitLen + 1 ≤ budget) :
    ∃ as', runAsm budget offsetToPc prog as0 = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel (haltState (selfdestruct waddr sEnd)) as' := by
  rw [executePlan_append] at hblock
  obtain ⟨hbpre, hbemit⟩ := asmBlockAt_append hblock
  obtain ⟨asMid, hbrun, hbrel, hbpc, hbsd, hbsv⟩ :=
    genBlockPrefixBodyHSVP_sim_inv P l gp lg front S0 M0 ps0 vs0 sEnd as0
      hfront hready hsd0 hsv0 hspM hrel0 hthread hbpre
  rw [← hbodyLenEq] at hbrun hbpc
  have haddrmem := stackPerm_mem hbsv haddrS
  have hshallow : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack.length ≤ 15 := by have := hbsd.shallow; omega
  obtain ⟨d, hdepth, hlen⟩ := stackGetDepth_of_mem haddrmem
  have hsmall : d ≤ 15 := by omega
  have hnospill := alookup_of_spilled_eq hspMF haddrM
  have hbemit' : asmBlockAt prog asMid.pc
      (executePlan (emitInputPlan opc [Operand.Var addrv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1) := by
    rw [hbpc, hbodyLenEq]; exact hbemit
  obtain ⟨asMid2, herun, herel, hepc⟩ :=
    emitInputPlan_single_var_sim hnospill hliveaddr hdepth hsmall hbrel hlen hbemit'
  rw [← hemitLenEq] at herun hepc
  have hpeek : stackPeek d (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2))
      ([], ps0)).2.stack = Operand.Var addrv := stackGetDepth_peek hdepth
  have hemitstack : (emitInputPlan opc [Operand.Var addrv] nl
      (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).2.stack
      = (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.stack
        ++ [Operand.Var addrv] := by
    rw [emitInputPlan_single_var_eq hnospill hliveaddr hdepth hsmall hpeek]
  have hval : operandVal sEnd lo (Operand.Var addrv) = some waddr := hvaddr
  have htop : asMid2.stack = waddr :: asMid2.stack.drop 1 :=
    venomAsmRel_asmStack_top1_var herel hemitstack hval
  have hpc' : asMid2.pc < prog.length := by rw [hepc, hbpc]; omega
  have hget' : prog.get ⟨asMid2.pc, hpc'⟩ = AsmInst.AsmOp "SELFDESTRUCT" :=
    prog_get_transfer (by rw [hepc, hbpc]) hget
  have hget'' : prog[asMid2.pc]? = some (AsmInst.AsmOp "SELFDESTRUCT") := by
    rw [List.getElem?_eq_getElem hpc']
    simp only [Option.some.injEq, List.get_eq_getElem] at hget' ⊢
    exact hget'
  have hsdblock : asmBlockAt prog asMid2.pc (executePlan [StackOp.SOEmit "SELFDESTRUCT"]) := by
    have hep : executePlan [StackOp.SOEmit "SELFDESTRUCT"] = [AsmInst.AsmOp "SELFDESTRUCT"] := rfl
    rw [hep]
    refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    simp only [Nat.add_zero, List.getElem?_cons_zero, hget'']
  obtain ⟨asF, hFrun, hFterm⟩ :=
    emit_selfdestruct_sim (offsetToPc := offsetToPc) herel htop hsdblock
  have hcompose : runAsm (bodyLen + emitLen + 1) offsetToPc prog as0 = AsmResult.AsmHalt asF := by
    rw [show bodyLen + emitLen + 1 = bodyLen + (emitLen + 1) from by omega,
        runAsm_add_ok hbrun, runAsm_add_ok herun]
    exact hFrun
  exact ⟨asF, runAsm_le_of_ne_ok (fun s => by simp) hbudget hcompose, hFterm⟩

/-- **Per-block SELFDESTRUCT `hstep`** — the accounts-terminal, single-operand analogue of
    `hstep_regularHSVP_return`, completing the mature terminator hstep family (SELFDESTRUCT was the one
    codegen terminator with a connector but no hstep). `runBlock` halts with the accounts change
    (`runBlock_halt` + `stepInstBase` = `Halt (haltState (selfdestruct ...))`); the asm run + terminal
    relation come from `hasm_regularHSVP_selfdestruct_var`. `pcOf`/`psOf`/`wOf` abstract (SELFDESTRUCT
    halts, no successor). -/
theorem hstep_regularHSVP_selfdestruct
    {fn : IrFunction} {ctx : VenomContext} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {lo : AssocList String Nat}
    (pcOf : String → Nat) (psOf : String → PlanState) (wOf : String → Nat)
    {bb : BasicBlock} {term hd : Instruction} {tl : List Instruction}
    {extraFuel N : Nat} (P : Nat)
    {l : String} {gp : Instruction × Nat → PlanState → List StackOp × PlanState}
    {lg : List ((Instruction × Nat) × List String)}
    {front : List Instruction} {S0 : List String} {M0 M1 : AssocList Operand Nat}
    {ps0 : PlanState} {vs0 sEnd : VenomState} {as0 : AsmState}
    {addrv : String} {waddr : bytes32} {opc : Opcode} {nl : List String}
    {bodyLen emitLen : Nat}
    (hbb : bb.instructions = front ++ [term])
    (hcons : front ++ [term] = hd :: tl)
    (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hterm_step : stepInstBase term sEnd = ExecResult.Halt (haltState (selfdestruct waddr sEnd)))
    (hfront : lg.map Prod.fst = front.zipIdx 0)
    (hready : BodyStepsReadyHSVP P lo offsetToPc prog gp lg S0 M0)
    (hsd0 : StackDiscHS (totalGain lg + P) ps0 vs0 as0)
    (hsv0 : StackPerm S0 ps0) (hspM : ps0.spilled = M0)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hthread : execBodyThread front 0 vs0 = some sEnd)
    (hvs0 : vs0 = { vs0 with instIdx := 0 })
    (haddrS : addrv ∈ S0 ++ lg.flatMap (fun e => e.2))
    (hspMF : (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2.spilled
      = M1)
    (haddrM : alookup' M1 (Operand.Var addrv) = none)
    (hliveaddr : nl.contains addrv = true)
    (hvaddr : lookupVar addrv sEnd = some waddr)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)
        ++ (emitInputPlan opc [Operand.Var addrv] nl
             (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1)))
    (hbodyLenEq : bodyLen = (executePlan ([StackOp.SOLabel l] ++ (lg.foldl
        (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).1)).length)
    (hemitLenEq : emitLen = (executePlan (emitInputPlan opc [Operand.Var addrv] nl
        (lg.foldl (fun acc x => (acc.1 ++ (gp x.1 acc.2).1, (gp x.1 acc.2).2)) ([], ps0)).2).1).length)
    (hlt : as0.pc + bodyLen + emitLen < prog.length)
    (hget : prog.get ⟨as0.pc + bodyLen + emitLen, hlt⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hN : bodyLen + emitLen + 1 ≤ N) :
    WalkStep fn pcOf psOf wOf lo offsetToPc prog bb as0 N
      (runBlock (front.length + (extraFuel + 1)) ctx bb vs0) := by
  have hthread' : execBodyThread front 0 { vs0 with instIdx := 0 } = some sEnd := by
    rw [← hvs0]; exact hthread
  have hrb : runBlock (front.length + (extraFuel + 1)) ctx bb vs0
      = ExecResult.Halt (haltState (selfdestruct waddr sEnd)) :=
    runBlock_halt ctx bb extraFuel front term hd tl vs0 sEnd
      (haltState (selfdestruct waddr sEnd)) hbb hcons hphi hnonterm hthread' hterm_step
  obtain ⟨as', hasm, hterm⟩ :=
    hasm_regularHSVP_selfdestruct_var P hfront hready hsd0 hsv0 hspM hrel0 hthread
      haddrS hspMF haddrM hliveaddr hvaddr hblock hbodyLenEq hemitLenEq hlt hget hN
  rw [hrb]
  exact ⟨as', hasm, hterm⟩

/-! ## Reframing the walk-invariant gap: `StackDiscHS` = threaded `venomAsmRel` (`defined`) + plan facts -/


/-- **`venomAsmRel` supplies the `defined` component of `StackDiscHS`.** Every `Var z` on the plan stack
    has a value in the Venom state — because `planStackRel` (the first conjunct of `venomAsmRel`) evaluates
    each plan-stack entry to its asm-stack counterpart via `operandVal`, and `operandVal … (Var z)` is
    exactly `lookupVar z vs`. So of the three `StackDiscHS` fields (`shallow`/`noSpill`/`defined`), `defined`
    is not a fresh invariant to thread across blocks — it falls out of the relation the walk already
    carries. -/
theorem venomAsmRel_stack_defined {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} (h : venomAsmRel lo ps vs as) :
    ∀ z, Operand.Var z ∈ ps.stack → ∃ w, lookupVar z vs = some w := by
  intro z hz
  obtain ⟨hlen, hrel⟩ := h.1
  have hzr : Operand.Var z ∈ ps.stack.reverse := List.mem_reverse.mpr hz
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hzr
  have hi' : i < ps.stack.length := by rwa [List.length_reverse] at hi
  have hval := hrel i hi'
  have hrev : ps.stack.reverse[i]! = Operand.Var z := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hget]
  rw [hrev, operandVal] at hval
  exact ⟨_, hval⟩

/-- **`StackDiscH` reduces to `venomAsmRel` plus two PLAN facts.** Packaging `venomAsmRel_stack_defined`:
    the no-spill block-entry discipline `StackDiscH k ps vs` follows from the walk-threaded `venomAsmRel`
    (giving `defined`) together with `shallow` (`ps.stack.length + k ≤ 15`) and `noSpill` — both properties
    of the RECORDED entry plan state `ps = psOf bb`, not of the arriving Venom/asm states. -/
theorem stackDiscH_of_venomAsmRel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {k : Nat}
    (hrel : venomAsmRel lo ps vs as)
    (hshallow : ps.stack.length + k ≤ 15)
    (hnospill : ∀ op, alookup' ps.spilled op = none) :
    StackDiscH k ps vs where
  noSpill := hnospill
  shallow := hshallow
  defined := venomAsmRel_stack_defined hrel

/-- **`StackDiscHS` (the spill-aware form the hsteps consume) from `venomAsmRel` + two plan facts**, for a
    spill-free block entry. Composes `stackDiscH_of_venomAsmRel` with `StackDiscHS.of_stackDiscH` (a no-spill
    state is spill-aware for any asm state — `spillWf` vacuous). So the whole `StackDiscHS` input the mature
    terminator hsteps require is NOT a fresh invariant to thread block-to-block: `defined` comes from the
    `venomAsmRel` the walk already carries, and `shallow`/`noSpill` are properties of the RECORDED entry
    plan state `psOf bb`. This reframes the "walk invariant" gap I called the deep load-bearing piece: it is
    a PLAN-GENERATOR-invariant problem (prove `psOf bb`'s stack is `≤ 15` and spill-free at every entry, and
    `StackPerm S0 (psOf bb)` = `(psOf bb).stack = S0.map Var`), NOT a strengthening of the driver's
    block-to-block contract. A meaningfully different — and more localized — remaining task. -/
theorem stackDiscHS_of_venomAsmRel {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {k : Nat}
    (hrel : venomAsmRel lo ps vs as)
    (hshallow : ps.stack.length + k ≤ 15)
    (hnospill : ∀ op, alookup' ps.spilled op = none) :
    StackDiscHS k ps vs as :=
  StackDiscHS.of_stackDiscH (stackDiscH_of_venomAsmRel hrel hshallow hnospill)

/-! ## Reframed gap (4), base case: plan properties at the ENTRY block (StackDiscHS/StackPerm from venomAsmRel) -/


/-- **Plan properties at the ENTRY block — the base case of the reframed gap (4).** `psOfFn_entry` says the
    recorded entry plan state is `initPlanState` (empty stack, no spills). So `StackPerm [] (psOf entry)`
    holds trivially, and — composed with `stackDiscHS_of_venomAsmRel` (the reframing) — `StackDiscHS` at the
    entry follows from the walk-threaded `venomAsmRel` alone. This is the base of the plan-generation
    induction; the DFS-recording inductive step (`psOf bb`'s stack shape for non-entry blocks) is the
    remaining deep part. -/
theorem stackPerm_at_entry {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hfuel : 0 < fuel) :
    StackPerm [] (psOfFn fuel fn fnEom lblCtr entry.label) := by
  rw [psOfFn_entry hentry hfn hfuel]
  simp [StackPerm, initPlanState]

theorem stackDiscHS_at_entry {fuel fnEom lblCtr : Nat} {fn : IrFunction} {entry : BasicBlock}
    {lo : AssocList String Nat} {vs : VenomState} {as : AsmState} {k : Nat}
    (hentry : entryBlock fn = some entry)
    (hfn : ∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst)
    (hfuel : 0 < fuel)
    (hrel : venomAsmRel lo (psOfFn fuel fn fnEom lblCtr entry.label) vs as)
    (hk : k ≤ 15) :
    StackDiscHS k (psOfFn fuel fn fnEom lblCtr entry.label) vs as := by
  have hpe := psOfFn_entry (fnEom := fnEom) (lblCtr := lblCtr) hentry hfn hfuel
  refine stackDiscHS_of_venomAsmRel hrel ?_ ?_
  · rw [hpe, show ({initPlanState fnEom with labelCounter := lblCtr} : PlanState).stack.length = 0 from rfl,
      Nat.zero_add]
    exact hk
  · intro op; rw [hpe]; rfl

/-! ## Reframed gap (4): var-set reconciliation — `StackPerm` respects a permutation of its var set -/


/-- **`StackPerm` respects a permutation of its var set.** Since `StackPerm S p` is `List.Perm p.stack
    (S.map Var)`, permuting `S` to `S'` (`List.Perm S S'`) transfers the stack discipline. This is the
    var-set reconciliation step for the universal walk invariant: the body sim produces `StackPerm (S0 ++
    body-vars) (psOf succ)`, while a successor's hstep wants `StackPerm succLiveIn (psOf succ)`; whenever the
    two var lists agree up to permutation (which a well-formed jump guarantees), this lemma bridges them.
    Both hypotheses are manifestly satisfiable (`StackPerm S p` for any `p` with `stack = S.map Var`;
    `Perm S S'` for `S' = S`), so it is not vacuous. -/
theorem stackPerm_congr {S S' : List String} {p : PlanState}
    (h : StackPerm S p) (hperm : List.Perm S S') : StackPerm S' p :=
  h.trans (hperm.map Operand.Var)

/-- Non-vacuity witness: a concrete state satisfies both hypotheses and the conclusion fires. -/
theorem stackPerm_congr_nonvacuous (p : PlanState) (hp : p.stack = [Operand.Var "a", Operand.Var "b"]) :
    StackPerm ["b", "a"] p :=
  stackPerm_congr (S := ["a", "b"]) (by rw [StackPerm, hp]; rfl) (by decide)

/-! ## Reframed gap (4): `StackDiscHS` from `venomAsmRel` + `StackPerm` + var-count bound (body-sim shape) -/


/-- **`StackDiscHS` from `venomAsmRel` + `StackPerm` + a var-count bound.** A variant of
    `stackDiscHS_of_venomAsmRel` where the caller supplies `StackPerm S ps` and a bound on `S.length`
    instead of the raw `shallow` — the shape the body sim yields at a successor entry
    (`StackPerm (S0 ++ body-vars) (psOf succ)`). `stackPerm_length` turns the var count into the stack
    bound; `venomAsmRel_stack_defined` gives `defined`; `noSpill` (spill-free entry) makes `spillWf`
    vacuous. So the whole `StackDiscHS` a successor hstep consumes is assembled from the walk-threaded
    `venomAsmRel`, the body-sim `StackPerm`, and two plan facts (var count ≤ 15, spill-free). -/
theorem stackDiscHS_of_venomAsmRel_perm {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {k : Nat} {S : List String}
    (hrel : venomAsmRel lo ps vs as)
    (hsv : StackPerm S ps)
    (hlen : S.length + k ≤ 15)
    (hnospill : ∀ op, alookup' ps.spilled op = none) :
    StackDiscHS k ps vs as := by
  refine stackDiscHS_of_venomAsmRel hrel ?_ hnospill
  rw [stackPerm_length hsv]; exact hlen

/-- Non-vacuity witness (built up front, per the discipline): a spill-free empty-stack state satisfies
    every hypothesis and the conclusion fires. -/
theorem stackDiscHS_of_venomAsmRel_perm_nonvacuous {lo : AssocList String Nat} {ps : PlanState}
    {vs : VenomState} {as : AsmState} {k : Nat}
    (hrel : venomAsmRel lo ps vs as) (hemp : ps.stack = []) (hsp : ps.spilled = []) (hk : k ≤ 15) :
    StackDiscHS k ps vs as :=
  stackDiscHS_of_venomAsmRel_perm (S := []) hrel
    (by show List.Perm ps.stack _; rw [hemp]; exact List.Perm.refl _)
    (by simpa using hk)
    (by intro op; rw [hsp]; rfl)

/-! ## Reframed gap (4): successor hstep invariants from venomAsmRel + per-block plan facts (no threading) -/


/-- **A successor block's `StackDiscHS` + `StackPerm` hstep inputs, from the walk-threaded `venomAsmRel`
    plus per-block plan facts.** This bundles the reframed-gap-(4) consumption lemmas and makes their
    payoff explicit: the driver does NOT need to thread `StackDiscHS`/`StackPerm` block-to-block — it
    threads `venomAsmRel` (which it already does), and the two hstep invariants are RE-DERIVED at each
    successor entry from `venomAsmRel` + properties of the RECORDED plan state `ps = psOf succ` (spill-free,
    the body-sim `StackPerm bodyVarSet`, the var-list reconciliation `bodyVarSet ≡ succLiveIn`, and the var
    count bound). So the only genuinely per-block-plan obligations left are those `psOf`-facts; the
    invariant "threading" dissolves. -/
theorem succ_hstep_invariants_of_venomAsmRel
    {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState} {as : AsmState} {k : Nat}
    {bodyVarSet succLiveIn : List String}
    (hrel : venomAsmRel lo ps vs as)
    (hnospill : ∀ op, alookup' ps.spilled op = none)
    (hsv : StackPerm bodyVarSet ps)
    (hperm : List.Perm bodyVarSet succLiveIn)
    (hlen : succLiveIn.length + k ≤ 15) :
    StackDiscHS k ps vs as ∧ StackPerm succLiveIn ps :=
  ⟨stackDiscHS_of_venomAsmRel_perm hrel (stackPerm_congr hsv hperm) hlen hnospill,
   stackPerm_congr hsv hperm⟩

/-- Non-vacuity witness: a spill-free empty-stack state with `bodyVarSet = succLiveIn = []` satisfies
    every hypothesis and both conclusions fire. -/
theorem succ_hstep_invariants_nonvacuous
    {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState} {as : AsmState} {k : Nat}
    (hrel : venomAsmRel lo ps vs as) (hemp : ps.stack = []) (hsp : ps.spilled = []) (hk : k ≤ 15) :
    StackDiscHS k ps vs as ∧ StackPerm [] ps :=
  succ_hstep_invariants_of_venomAsmRel (bodyVarSet := []) (succLiveIn := [])
    hrel (by intro op; rw [hsp]; rfl)
    (by show List.Perm ps.stack _; rw [hemp]; exact List.Perm.refl _)
    (List.Perm.refl _) (by simpa using hk)

/-! ## Non-vacuity witness for INVALID `_regular` (completes the no-emit sound family: STOP/INVALID/JMP) -/


/-- **Non-vacuity of the sound INVALID `_regular`.** The halting sibling of `HbsimMatch_stop_regular_nonvacuous`:
    a bare `[INVALID]` block (front = []) instantiates `HbsimMatch_invalid_regular` with every
    structural/reducible hypothesis discharged, leaving only the genuine invariants + the concrete INVALID
    placement. So the lemma fires — completing the witness set for the no-emit/empty-join sound `_regular`
    family (STOP, INVALID, JMP). -/
theorem HbsimMatch_invalid_regular_nonvacuous
    {Entry : VenomState → AsmState → Nat → Prop}
    {liveness : DfState (List String)} {dfg : DfgAnalysis} {cfg : CfgAnalysis} {fn : IrFunction}
    {lo : AssocList String Nat} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {nextLiveness : List String} {curBbLabel : String} {dem : Nat}
    {ps0 : PlanState} {as0 : AsmState} {N restFuel : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s : VenomState} {S : List String} {invInst : Instruction}
    (hbb : bb.instructions = [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hphi : invInst.opcode ≠ Opcode.PHI)
    (hsd : StackDiscH 0 ps0 { s with instIdx := 0 })
    (hsv : StackIsVars S ps0)
    (hrel0 : venomAsmRel lo ps0 { s with instIdx := 0 } as0)
    (hblock : asmBlockAt prog as0.pc [])
    (hpc : as0.pc < prog.length) (hinv : prog.get ⟨as0.pc, hpc⟩ = AsmInst.AsmOp "INVALID")
    (hle : 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (0 + (restFuel + 1)) ctx bb s) := by
  refine HbsimMatch_invalid_regular (liveness := liveness) (dfg := dfg) (cfg := cfg) (fn := fn)
    (nextLiveness := nextLiveness) (curBbLabel := curBbLabel) (dem := dem) (front := [])
    (lo := lo) (ps0 := ps0) (S := S) (o2pc := o2pc) (prog := prog) (as0 := as0)
    (hd := invInst) (tl := []) (sEnd := { s with instIdx := 0 })
    (by simpa using hbb) hinvop (by simpa using hbb) hphi (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · trivial
  · simpa using hsd
  · exact hsv
  · exact hrel0
  · exact hblock
  · exact hpc
  · exact hinv
  · exact hle

/-! ## The ∀-block terminator-dispatch assembler: one per-block connector for every terminator

The per-block obligation of `codegen_correct_ofBlocks_HbsimMatch` was previously discharged by picking,
at each call site, the matching `HbsimMatch_*_from_body` connector by hand. These two lemmas collapse
that hand-dispatch into a single per-block entry point: supply the block's body-sim run plus its
terminator-classified recipe and get the `HbsimMatch`, with the case analysis carried once, inside the
lemma. `HbsimMatch_halting_dispatch` covers the five halting terminators for an arbitrary `Entry`;
`HbsimMatch_dispatch` covers all eight for the canonical walk `Entry`. -/


/-- **A block's halting-terminator recipe**: the block runs its body to `vs'`, then executes one of the
    five halting terminators (STOP / INVALID / RETURN / REVERT / SELFDESTRUCT), each bundled with the
    Venom-side `runBlock` result and the asm-side terminator instruction sitting at `as'.pc` (plus the
    operand/memory facts the operand-carrying terminators need). The body-sim half (`hbody`/`hrel'`) is
    shared across all five arms. -/
def HaltingTermRecipe (prog : List AsmInst) (as' : AsmState)
    (ps' : PlanState) (vs' : VenomState)
    (f' : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : Prop :=
  (runBlock f' ctx bb s = ExecResult.Halt (haltState vs')
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "STOP")
  ∨ (runBlock f' ctx bb s
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vs'))
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "INVALID")
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32),
      runBlock f' ctx bb s
          = ExecResult.Halt (haltState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "RETURN")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32),
      runBlock f' ctx bb s
          = ExecResult.Abort AbortType.RevertAbort
              (revertState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "REVERT")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  ∨ (∃ (addr : bytes32) (stk : List bytes32),
      runBlock f' ctx bb s = ExecResult.Halt (haltState (selfdestruct addr vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "SELFDESTRUCT")
      ∧ as'.stack = addr :: stk)

/-- **The halting-terminator dispatcher.** Given the shared body-sim output (`hbody`/`hrel'`) and a
    `HaltingTermRecipe` classifying the block's halting terminator, produce the block's `HbsimMatch` for
    ANY `Entry` — dispatching to the matching per-terminator connector. Unifies the five halting
    connectors into a single per-block entry point (the halting half of the ∀-block assembler). -/
theorem HbsimMatch_halting_dispatch {Entry : VenomState → AsmState → Nat → Prop}
    {lo : AssocList String Nat} {ps' : PlanState} {o2pc : AssocList Nat Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {f' bodyLen N : Nat} {ctx : VenomContext} {bb : BasicBlock}
    {s vs' : VenomState}
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrel' : venomAsmRel lo ps' vs' as')
    (hle : bodyLen + 1 ≤ N)
    (hrecipe : HaltingTermRecipe prog as' ps' vs' f' ctx bb s) :
    HbsimMatch Entry o2pc prog as0 N (runBlock f' ctx bb s) := by
  rcases hrecipe with ⟨hrb, hpc, hstop⟩ | ⟨hrb, hpc, hinv⟩
    | ⟨offW, szW, rest, hrb, ⟨hpc, hret⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨offW, szW, rest, hrb, ⟨hpc, hrev⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨addr, stk, hrb, ⟨hpc, hsd⟩, hstk⟩
  · exact HbsimMatch_stop_from_body hrb hbody hrel' hpc hstop hle
  · exact HbsimMatch_invalid_from_body hrb hbody hrel' hpc hinv hle
  · exact HbsimMatch_return_from_body hrb hbody hrel' hpc hret hstk hcov hbelow hlen hle
  · exact HbsimMatch_revert_from_body hrb hbody hrel' hpc hrev hstk hcov hbelow hlen hle
  · exact HbsimMatch_selfdestruct_from_body hrb hbody hrel' hpc hsd hstk hle

/-- **Non-vacuity: a bare STOP block drives the dispatcher.** Empty body (`bodyLen = 0`), STOP arm of the
    recipe — every hypothesis is satisfied and the `HbsimMatch` is produced, so the dispatcher applies to
    a real block. -/
theorem HbsimMatch_halting_dispatch_nonvacuous
    {Entry : VenomState → AsmState → Nat → Prop} {lo : AssocList String Nat} {ps : PlanState}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {as0 : AsmState}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {N f' : Nat} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hrel : venomAsmRel lo ps { s with instIdx := 0 } as0)
    (hstoppc : as0.pc < prog.length) (hstop : prog.get ⟨as0.pc, hstoppc⟩ = AsmInst.AsmOp "STOP")
    (hle : 0 + 1 ≤ N) :
    HbsimMatch Entry o2pc prog as0 N (runBlock (f' + 1) ctx bb { s with instIdx := 0 }) := by
  have hrb : runBlock (f' + 1) ctx bb { s with instIdx := 0 }
      = ExecResult.Halt (haltState { s with instIdx := 0 }) := by
    simp [runBlock, evalPhis, phiPrefixLength, execBlock, getInstruction, hbb, hstopop, stepInstBase]
  refine HbsimMatch_halting_dispatch (bodyLen := 0) (as' := as0) (ps' := ps)
    (by simp [runAsm]) hrel hle ?_
  exact Or.inl ⟨hrb, hstoppc, hstop⟩

/-- **A block's full terminator recipe** (all eight codegen terminators). Each disjunct bundles exactly
    the hypotheses its per-terminator connector needs beyond the shared body-sim run `hbody`: the Venom
    `runBlock` result, the resolved asm terminator instruction(s), the operand/memory facts, the arrival
    relation, the successor lookup, and the fuel bound. Halting arms carry the body-end relation
    `venomAsmRel lo ps' vs' as'`; continuing arms carry the successor-recording relation instead
    (`ps' = psOf target` for JMP; the condition/selector-dropped `venomAsmRel` for JNZ/DJMP). -/
def TermRecipe (fn : IrFunction) (lo : AssocList String Nat) (pcOf : String → Nat)
    (psOf : String → PlanState) (o2pc : AssocList Nat Nat) (offsets : AssocList String Nat)
    (prog : List AsmInst) (as' : AsmState) (ps' : PlanState) (vs' : VenomState)
    (bodyLen N f' : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : Prop :=
  -- STOP
  (venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ N
    ∧ runBlock f' ctx bb s = ExecResult.Halt (haltState vs')
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "STOP")
  -- INVALID
  ∨ (venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ N
    ∧ runBlock f' ctx bb s
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vs'))
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "INVALID")
  -- RETURN
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ N
      ∧ runBlock f' ctx bb s
          = ExecResult.Halt (haltState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "RETURN")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  -- REVERT
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ N
      ∧ runBlock f' ctx bb s
          = ExecResult.Abort AbortType.RevertAbort
              (revertState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "REVERT")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  -- SELFDESTRUCT
  ∨ (∃ (addr : bytes32) (stk : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ N
      ∧ runBlock f' ctx bb s = ExecResult.Halt (haltState (selfdestruct addr vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "SELFDESTRUCT")
      ∧ as'.stack = addr :: stk)
  -- JMP
  ∨ (∃ (target : String) (off : Nat) (bb' : BasicBlock),
      venomAsmRel lo ps' vs' as' ∧ ps' = psOf target ∧ bodyLen + 2 ≤ N ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs')
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
      ∧ AssocList.lookup String Nat offsets target = some off ∧ off < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMP")
      ∧ AssocList.lookup Nat Nat o2pc off = some (pcOf target)
      ∧ lookupBlock target fn.blocks = some bb')
  -- JNZ (taken)
  ∨ (∃ (ifNz : String) (off : Nat) (cond : bytes32) (stk : List bytes32) (bb' : BasicBlock),
      bodyLen + 2 ≤ N ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo ifNz vs')
      ∧ as'.stack = cond :: stk ∧ cond ≠ EvmYul.UInt256.ofNat 0
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
      ∧ AssocList.lookup String Nat offsets ifNz = some off ∧ off < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI")
      ∧ AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz)
      ∧ venomAsmRel lo (psOf ifNz) vs' { as' with stack := stk }
      ∧ lookupBlock ifNz fn.blocks = some bb')
  -- JNZ (not taken)
  ∨ (∃ (ifNz ifZ : String) (offN offZ : Nat) (stk : List bytes32) (bb' : BasicBlock),
      bodyLen + 4 ≤ N ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo ifZ vs')
      ∧ as'.stack = EvmYul.UInt256.ofNat 0 :: stk
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
      ∧ AssocList.lookup String Nat offsets ifNz = some offN ∧ offN < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI")
      ∧ (∃ h3 : as'.pc + 2 < prog.length,
          prog.get ⟨as'.pc + 2, h3⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
      ∧ AssocList.lookup String Nat offsets ifZ = some offZ ∧ offZ < 2 ^ 256
      ∧ (∃ h4 : as'.pc + 2 + 1 < prog.length, prog.get ⟨as'.pc + 2 + 1, h4⟩ = AsmInst.AsmOp "JUMP")
      ∧ AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ)
      ∧ venomAsmRel lo (psOf ifZ) vs' { as' with stack := stk }
      ∧ lookupBlock ifZ fn.blocks = some bb')
  -- DJMP
  ∨ (∃ (targetLabel : String) (chainLen : Nat) (rest : List bytes32) (bb' : BasicBlock),
      bodyLen + chainLen ≤ N ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo targetLabel vs')
      ∧ runAsm chainLen o2pc prog as'
          = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel }
      ∧ venomAsmRel lo (psOf targetLabel) vs' { as' with stack := rest }
      ∧ lookupBlock targetLabel fn.blocks = some bb')

/-- **The ∀-block terminator-dispatch assembler.** Given the shared body-sim run `hbody` and a
    `TermRecipe` classifying the block's terminator, produce the block's `HbsimMatch` for the canonical
    walk `Entry` — dispatching each of the eight terminators to its connector. This is the per-block
    obligation of `codegen_correct_ofBlocks_HbsimMatch` discharged uniformly: a block is handled by
    supplying its body sim plus its (decidable-terminator-classified) recipe, with no case analysis at
    the call site. -/
theorem HbsimMatch_dispatch {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {ps' : PlanState} {bodyLen N f' : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s vs' : VenomState}
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hrecipe : TermRecipe fn lo pcOf psOf o2pc offsets prog as' ps' vs' bodyLen N f' ctx bb s) :
    HbsimMatch (CanonEntry fn lo pcOf psOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  rcases hrecipe with
      ⟨hrel', hle, hrb, hpc, hstop⟩
    | ⟨hrel', hle, hrb, hpc, hinv⟩
    | ⟨offW, szW, rest, hrel', hle, hrb, ⟨hpc, hret⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨offW, szW, rest, hrel', hle, hrb, ⟨hpc, hrev⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨addr, stk, hrel', hle, hrb, ⟨hpc, hsd⟩, hstk⟩
    | ⟨target, off, bb', hrel', hps, hle, hnh, hrb, ⟨hp1, hpush⟩, hoff_lk, hoff, ⟨hp2, hjump⟩,
        hidx_lk, hlk'⟩
    | ⟨ifNz, off, cond, stk, bb', hle, hnh, hrb, hstk_c, hcond, ⟨hp1, hpush⟩, hoff_lk, hoff,
        ⟨hp2, hjumpi⟩, hidx_lk, hrel_succ, hlk'⟩
    | ⟨ifNz, ifZ, offN, offZ, stk, bb', hle, hnh, hrb, hstk_c, ⟨hp1, hpushN⟩, hoffN_lk, hoffN,
        ⟨hp2, hjumpi⟩, ⟨hp3, hpushZ⟩, hoffZ_lk, hoffZ, ⟨hp4, hjump⟩, hidxZ_lk, hrel_succ, hlk'⟩
    | ⟨targetLabel, chainLen, rest, bb', hle, hnh, hrb, hdispatch, hrel_succ, hlk'⟩
  · exact HbsimMatch_stop_from_body hrb hbody hrel' hpc hstop hle
  · exact HbsimMatch_invalid_from_body hrb hbody hrel' hpc hinv hle
  · exact HbsimMatch_return_from_body hrb hbody hrel' hpc hret hstk hcov hbelow hlen hle
  · exact HbsimMatch_revert_from_body hrb hbody hrel' hpc hrev hstk hcov hbelow hlen hle
  · exact HbsimMatch_selfdestruct_from_body hrb hbody hrel' hpc hsd hstk hle
  · exact HbsimMatch_jmp_from_body hrb hnh hbody hrel' hps hp1 hpush hoff_lk hoff hp2 hjump
      hidx_lk hlk' hle
  · exact HbsimMatch_jnz_taken_from_body hrb hnh hbody hstk_c hcond hp1 hpush hoff_lk hoff hp2
      hjumpi hidx_lk hrel_succ hlk' hle
  · exact HbsimMatch_jnz_nottaken_from_body hrb hnh hbody hstk_c hp1 hpushN hoffN_lk hoffN hp2
      hjumpi hp3 hpushZ hoffZ_lk hoffZ hp4 hjump hidxZ_lk hrel_succ hlk' hle
  · exact HbsimMatch_djmp_from_body hrb hnh hbody hdispatch hrel_succ hlk' hle

/-- **The N-constrained block terminator recipe.** `TermRecipe` with every fuel bound `bodyLen + K ≤ N`
    replaced by the block-layout fact against `wOf bb.label` (halting: `bodyLen + 1 ≤ wOf bb.label`;
    continuing: `wOf(succ) + blockLen ≤ wOf bb.label`). Paired with `wOf bb.label ≤ N` (the Entry's
    budget bound) this yields both the halting `hle` and the continuing successor bound. -/
def TermRecipeW (fn : IrFunction) (lo : AssocList String Nat) (pcOf : String → Nat)
    (psOf : String → PlanState) (wOf : String → Nat) (o2pc : AssocList Nat Nat)
    (offsets : AssocList String Nat) (prog : List AsmInst) (as' : AsmState) (ps' : PlanState)
    (vs' : VenomState) (bodyLen f' : Nat) (ctx : VenomContext) (bb : BasicBlock) (s : VenomState) : Prop :=
  (venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ wOf bb.label
    ∧ runBlock f' ctx bb s = ExecResult.Halt (haltState vs')
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "STOP")
  ∨ (venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ wOf bb.label
    ∧ runBlock f' ctx bb s
        = ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty vs'))
    ∧ ∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "INVALID")
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ wOf bb.label
      ∧ runBlock f' ctx bb s
          = ExecResult.Halt (haltState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "RETURN")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  ∨ (∃ (offW szW : bytes32) (rest : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ wOf bb.label
      ∧ runBlock f' ctx bb s
          = ExecResult.Abort AbortType.RevertAbort
              (revertState (setReturndata (readMemory offW.toNat szW.toNat vs') vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "REVERT")
      ∧ as'.stack = offW :: szW :: rest
      ∧ (szW.toNat = 0 ∨ ((offW.toNat + szW.toNat + 31) / 32) * 32 ≤ as'.memory.size)
      ∧ offW.toNat + szW.toNat ≤ ps'.alloc.fnEom ∧ szW.toNat < USize.size)
  ∨ (∃ (addr : bytes32) (stk : List bytes32), venomAsmRel lo ps' vs' as' ∧ bodyLen + 1 ≤ wOf bb.label
      ∧ runBlock f' ctx bb s = ExecResult.Halt (haltState (selfdestruct addr vs'))
      ∧ (∃ h : as'.pc < prog.length, prog.get ⟨as'.pc, h⟩ = AsmInst.AsmOp "SELFDESTRUCT")
      ∧ as'.stack = addr :: stk)
  ∨ (∃ (target : String) (off : Nat) (bb' : BasicBlock),
      venomAsmRel lo ps' vs' as' ∧ ps' = psOf target ∧ wOf target + (bodyLen + 2) ≤ wOf bb.label
      ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo target vs')
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
      ∧ AssocList.lookup String Nat offsets target = some off ∧ off < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMP")
      ∧ AssocList.lookup Nat Nat o2pc off = some (pcOf target)
      ∧ lookupBlock target fn.blocks = some bb')
  ∨ (∃ (ifNz : String) (off : Nat) (cond : bytes32) (stk : List bytes32) (bb' : BasicBlock),
      wOf ifNz + (bodyLen + 2) ≤ wOf bb.label ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo ifNz vs')
      ∧ as'.stack = cond :: stk ∧ cond ≠ EvmYul.UInt256.ofNat 0
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
      ∧ AssocList.lookup String Nat offsets ifNz = some off ∧ off < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI")
      ∧ AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz)
      ∧ venomAsmRel lo (psOf ifNz) vs' { as' with stack := stk }
      ∧ lookupBlock ifNz fn.blocks = some bb')
  ∨ (∃ (ifNz ifZ : String) (offN offZ : Nat) (stk : List bytes32) (bb' : BasicBlock),
      wOf ifZ + (bodyLen + 4) ≤ wOf bb.label ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo ifZ vs')
      ∧ as'.stack = EvmYul.UInt256.ofNat 0 :: stk
      ∧ (∃ h1 : as'.pc < prog.length,
          prog.get ⟨as'.pc, h1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
      ∧ AssocList.lookup String Nat offsets ifNz = some offN ∧ offN < 2 ^ 256
      ∧ (∃ h2 : as'.pc + 1 < prog.length, prog.get ⟨as'.pc + 1, h2⟩ = AsmInst.AsmOp "JUMPI")
      ∧ (∃ h3 : as'.pc + 2 < prog.length,
          prog.get ⟨as'.pc + 2, h3⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
      ∧ AssocList.lookup String Nat offsets ifZ = some offZ ∧ offZ < 2 ^ 256
      ∧ (∃ h4 : as'.pc + 2 + 1 < prog.length, prog.get ⟨as'.pc + 2 + 1, h4⟩ = AsmInst.AsmOp "JUMP")
      ∧ AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ)
      ∧ venomAsmRel lo (psOf ifZ) vs' { as' with stack := stk }
      ∧ lookupBlock ifZ fn.blocks = some bb')
  ∨ (∃ (targetLabel : String) (chainLen : Nat) (rest : List bytes32) (bb' : BasicBlock),
      wOf targetLabel + (bodyLen + chainLen) ≤ wOf bb.label ∧ vs'.halted = false
      ∧ runBlock f' ctx bb s = ExecResult.OK (jumpTo targetLabel vs')
      ∧ runAsm chainLen o2pc prog as'
          = AsmResult.AsmOK { as' with stack := rest, pc := pcOf targetLabel }
      ∧ venomAsmRel lo (psOf targetLabel) vs' { as' with stack := rest }
      ∧ lookupBlock targetLabel fn.blocks = some bb')

/-- **The ∀-block terminator-dispatch assembler for the N-constrained walk Entry.** Given the body-sim run
    `hbody`, the Entry's budget bound `hcur : wOf bb.label ≤ N`, and a `TermRecipeW` classifying the block's
    terminator, produce the block's `HbsimMatch (CanonEntryWH …)` — halting arms via the Entry-independent
    connectors (deriving `bodyLen + 1 ≤ N` from the layout fact + `hcur`), continuing arms via the `canonWH`
    connectors (which thread `wOf`/`halted` to the successor). This is the generic per-block obligation of a
    multi-block recipe driver, discharged uniformly with no vacuity. -/
theorem HbsimMatch_dispatchW {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as0 as' : AsmState} {ps' : PlanState} {bodyLen N f' : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s vs' : VenomState}
    (hbody : runAsm bodyLen o2pc prog as0 = AsmResult.AsmOK as')
    (hcur : wOf bb.label ≤ N)
    (hrecipe : TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' vs' bodyLen f' ctx bb s) :
    HbsimMatch (CanonEntryWH fn lo pcOf psOf wOf) o2pc prog as0 N (runBlock f' ctx bb s) := by
  rcases hrecipe with
      ⟨hrel', hw, hrb, hpc, hstop⟩
    | ⟨hrel', hw, hrb, hpc, hinv⟩
    | ⟨offW, szW, rest, hrel', hw, hrb, ⟨hpc, hret⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨offW, szW, rest, hrel', hw, hrb, ⟨hpc, hrev⟩, hstk, hcov, hbelow, hlen⟩
    | ⟨addr, stk, hrel', hw, hrb, ⟨hpc, hsd⟩, hstk⟩
    | ⟨target, off, bb', hrel', hps, hw, hnh, hrb, ⟨hp1, hpush⟩, hoff_lk, hoff, ⟨hp2, hjump⟩,
        hidx_lk, hlk'⟩
    | ⟨ifNz, off, cond, stk, bb', hw, hnh, hrb, hstk_c, hcond, ⟨hp1, hpush⟩, hoff_lk, hoff,
        ⟨hp2, hjumpi⟩, hidx_lk, hrel_succ, hlk'⟩
    | ⟨ifNz, ifZ, offN, offZ, stk, bb', hw, hnh, hrb, hstk_c, ⟨hp1, hpushN⟩, hoffN_lk, hoffN,
        ⟨hp2, hjumpi⟩, ⟨hp3, hpushZ⟩, hoffZ_lk, hoffZ, ⟨hp4, hjump⟩, hidxZ_lk, hrel_succ, hlk'⟩
    | ⟨targetLabel, chainLen, rest, bb', hw, hnh, hrb, hdispatch, hrel_succ, hlk'⟩
  · exact HbsimMatch_stop_from_body hrb hbody hrel' hpc hstop (by omega)
  · exact HbsimMatch_invalid_from_body hrb hbody hrel' hpc hinv (by omega)
  · exact HbsimMatch_return_from_body hrb hbody hrel' hpc hret hstk hcov hbelow hlen (by omega)
  · exact HbsimMatch_revert_from_body hrb hbody hrel' hpc hrev hstk hcov hbelow hlen (by omega)
  · exact HbsimMatch_selfdestruct_from_body hrb hbody hrel' hpc hsd hstk (by omega)
  · exact HbsimMatch_jmp_from_body_canonWH hrb hnh hbody hrel' hps hp1 hpush hoff_lk hoff hp2 hjump
      hidx_lk hlk' hw hcur
  · exact HbsimMatch_jnz_taken_from_body_canonWH hrb hnh hbody hstk_c hcond hp1 hpush hoff_lk hoff hp2
      hjumpi hidx_lk hrel_succ hlk' hw hcur
  · exact HbsimMatch_jnz_nottaken_from_body_canonWH hrb hnh hbody hstk_c hp1 hpushN hoffN_lk hoffN hp2
      hjumpi hp3 hpushZ hoffZ_lk hoffZ hp4 hjump hidxZ_lk hrel_succ hlk' hw hcur
  · exact HbsimMatch_djmp_from_body_canonWH hrb hnh hbody hdispatch hrel_succ hlk' hw hcur

/-- **The generic multi-block recipe driver.** Reduces a whole function's `codegen_correct` to a per-block
    obligation: for each block reached under the N-constrained walk Entry `CanonEntryWH`, supply the block's
    body-sim run and its `TermRecipeW`. Threads through `codegen_correct_ofBlocks_HbsimMatch` with the
    per-block `HbsimMatch` discharged uniformly by `HbsimMatch_dispatchW` — no per-terminator case analysis at
    the call site, and no vacuity: the wOf-bounded Entry keeps the budget sound.

    `hsupply` is an error-OR-recipe disjunction, and that is load-bearing. A block with `m` body
    instructions needs `m+1` steps, so `runBlock (k+1)` is out-of-fuel `Error` for `k < m` — which NO
    `TermRecipeW` arm matches. Demanding a recipe at every `k` would therefore be unsatisfiable for every
    non-empty-body block, restricting the driver to all-empty-body functions; the disjunction lets the caller
    answer "at this fuel the block just runs out" instead. (`hrun0` is the same story at `f' = 0`.) -/
theorem codegen_correct_ofBlocks_recipeW
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat}
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hrun0 : ∀ bb ∈ fn.blocks, ∀ s : VenomState, runBlock 0 ctx bb s = ExecResult.Error "out of fuel")
    (hsupply : ∀ bb ∈ fn.blocks, ∀ (s : VenomState) (asm : AsmState) (N k : Nat),
        CanonEntryWH fn lo pcOf psOf wOf s asm N → s.currentBb = bb.label →
        (∃ e, runBlock (k+1) ctx bb s = ExecResult.Error e) ∨
        (∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
          runAsm bodyLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
            = AsmResult.AsmOK as' ∧
          TermRecipeW fn lo pcOf psOf wOf (asmResolve (executePlan ops)).2 offsets
            (asmResolve (executePlan ops)).1 as' ps' vs' bodyLen (k+1) ctx bb s))
    (hentry : CanonEntryWH fn lo pcOf psOf wOf
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as
        (asmResolve (executePlan ops)).1.length) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_ofBlocks_HbsimMatch (Entry := CanonEntryWH fn lo pcOf psOf wOf)
    hplan hent hlk hlbl ?_ hentry
  intro bb hbb s asm N f' hE hlbleq
  have hcur : wOf bb.label ≤ N := by
    obtain ⟨_, hwN, _⟩ := hE; rw [hlbleq] at hwN; exact hwN
  cases f' with
  | zero => rw [hrun0 bb hbb s]; simp [HbsimMatch]
  | succ k =>
    rcases hsupply bb hbb s asm N k hE hlbleq with ⟨e, herr⟩ | ⟨as', ps', vs', bodyLen, hbody, hrecipe⟩
    · rw [herr]; simp [HbsimMatch]
    · exact HbsimMatch_dispatchW hbody hcur hrecipe

/-- **Strengthening `HbsimMatch`'s Entry with a state invariant.** `HbsimMatch` mentions `Entry` in exactly
    ONE arm (OK / not-halted), so an invariant can be conjoined onto it wholesale: given the match for `E` and
    a proof that `Inv` holds of the continuing result, the match holds for `E ∧ Inv`. No per-terminator work —
    the eight dispatcher arms are untouched. -/
theorem HbsimMatch_and_inv {E : VenomState → AsmState → Nat → Prop} {Inv : VenomState → Prop}
    {o2pc : AssocList Nat Nat} {prog : List AsmInst} {asm : AsmState} {N : Nat} {r : ExecResult}
    (h : HbsimMatch E o2pc prog asm N r)
    (hinv : ∀ s', r = ExecResult.OK s' → s'.halted = false → Inv s') :
    HbsimMatch (fun s a n => E s a n ∧ Inv s) o2pc prog asm N r := by
  cases r with
  | OK s' =>
    by_cases hh : s'.halted
    · simp only [HbsimMatch, hh, if_true] at h ⊢; exact h
    · simp only [HbsimMatch, hh] at h ⊢
      obtain ⟨asm', N', hrun, hE⟩ := h
      exact ⟨asm', N', hrun, hE, hinv s' rfl (by simpa using hh)⟩
  | Halt s' => exact h
  | Abort t s' => cases t <;> exact h
  | IntRet l s' => trivial
  | Error e => trivial


set_option maxHeartbeats 1000000 in
/-- **The invariant-carrying driver.** Same as `codegen_correct_ofBlocks_recipeW`, but the walk carries a
    caller-chosen `Inv : VenomState → Prop`: `hsupply` receives `Inv s` (so a recipe may depend on the state's
    VALUES — e.g. RETURN's `hbelow : off + sz ≤ fnEom`, which is false for an arbitrary `s` and unprovable
    under the plain driver), and in exchange the caller discharges `hpres`, that `Inv` survives a block.

    This is a strict generalisation: `Inv := fun _ => True` recovers the original. It works because
    `codegen_correct_ofBlocks_HbsimMatch` takes `Entry` as a FREE PARAMETER and `HbsimMatch` mentions `Entry`
    in exactly one arm, so `HbsimMatch_and_inv` conjoins the invariant wholesale — the eight dispatcher arms
    need no change. -/
theorem codegen_correct_ofBlocks_recipeW_inv
    {fuel : Nat} {ctx : VenomContext} {fn : IrFunction} {fnEom lblCtr : Nat}
    {ops : List StackOp} {psFinal : PlanState} {vs : VenomState} {as : AsmState}
    {entryName entryLbl : String} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {offsets : AssocList String Nat} (Inv : VenomState → Prop)
    (hplan : generateFnPlan fn fnEom lblCtr = some (ops, psFinal))
    (hent : ctx.entry = some entryName)
    (hlk : lookupFunction entryName ctx.functions = some fn)
    (hlbl : fnEntryLabel fn = some entryLbl)
    (hrun0 : ∀ bb ∈ fn.blocks, ∀ s : VenomState, runBlock 0 ctx bb s = ExecResult.Error "out of fuel")
    (hsupply : ∀ bb ∈ fn.blocks, ∀ (s : VenomState) (asm : AsmState) (N k : Nat),
        CanonEntryWH fn lo pcOf psOf wOf s asm N → Inv s → s.currentBb = bb.label →
        (∃ e, runBlock (k+1) ctx bb s = ExecResult.Error e) ∨
        (∃ (as' : AsmState) (ps' : PlanState) (vs' : VenomState) (bodyLen : Nat),
          runAsm bodyLen (asmResolve (executePlan ops)).2 (asmResolve (executePlan ops)).1 asm
            = AsmResult.AsmOK as' ∧
          TermRecipeW fn lo pcOf psOf wOf (asmResolve (executePlan ops)).2 offsets
            (asmResolve (executePlan ops)).1 as' ps' vs' bodyLen (k+1) ctx bb s))
    (hpres : ∀ bb ∈ fn.blocks, ∀ (s s' : VenomState) (f' : Nat),
        Inv s → runBlock f' ctx bb s = ExecResult.OK s' → Inv s')
    (hentry : CanonEntryWH fn lo pcOf psOf wOf
        { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 } as
        (asmResolve (executePlan ops)).1.length)
    (hinv0 : Inv { vs with prevBb := none, currentBb := entryLbl, instIdx := 0 }) :
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm (asmResolve (executePlan ops)).1.length (asmResolve (executePlan ops)).2
         (asmResolve (executePlan ops)).1 as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | _ => True) := by
  refine codegen_correct_ofBlocks_HbsimMatch
    (Entry := fun s a n => CanonEntryWH fn lo pcOf psOf wOf s a n ∧ Inv s)
    hplan hent hlk hlbl ?_ ⟨hentry, hinv0⟩
  intro bb hbb s asm N f' hE hlbleq
  obtain ⟨hE', hinv⟩ := hE
  have hcur : wOf bb.label ≤ N := by
    obtain ⟨_, hwN, _⟩ := hE'; rw [hlbleq] at hwN; exact hwN
  refine HbsimMatch_and_inv ?_ (fun s' hr _ => hpres bb hbb s s' f' hinv hr)
  cases f' with
  | zero => rw [hrun0 bb hbb s]; simp [HbsimMatch]
  | succ k =>
    rcases hsupply bb hbb s asm N k hE' hinv hlbleq with ⟨e, herr⟩ | ⟨as', ps', vs', bodyLen, hbody, hrecipe⟩
    · rw [herr]; simp [HbsimMatch]
    · exact HbsimMatch_dispatchW hbody hcur hrecipe

/-! ## Generic `TermRecipeW` producers: the Venom result DERIVED from the block, not assumed

`codegen_correct_ofBlocks_recipeW`'s `hsupply` must hand each block a `TermRecipeW`, whose Venom component is
a `runBlock … = …` fact. The concrete capstones discharge that per function by `simp`. These producers derive
it instead, from the block's *structure* (`bb.instructions = front ++ [term]`, the terminator's opcode, and
the body thread `execBodyThread`) via the `runBlock_body_*` family — so a caller supplies only the asm-side
placement and the body-end relation. This is the first slice of discharging `hsupply` generically. -/

/-- **Generic STOP `TermRecipeW`.** For ANY block `front ++ [stopInst]` whose body threads to `sEnd`, the
    STOP arm's Venom result is derived (`runBlock_body_stop`), not assumed. -/
theorem termRecipeW_stop_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {stopInst hd : Instruction} {tl : List Instruction}
    (hbb : bb.instructions = front ++ [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hcons : front ++ [stopInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hw : bodyLen + 1 ≤ wOf bb.label)
    (hstoppc : as'.pc < prog.length)
    (hstop : prog.get ⟨as'.pc, hstoppc⟩ = AsmInst.AsmOp "STOP") :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inl ⟨hrel', hw,
    runBlock_body_stop ctx bb restFuel front stopInst hd tl s sEnd hbb hstopop hcons hphi hnonterm hthread,
    hstoppc, hstop⟩

/-- **Generic INVALID `TermRecipeW`.** The aborting sibling: the `Abort ExHaltAbort` result is derived
    (`runBlock_body_invalid`) from the block's structure. -/
theorem termRecipeW_invalid_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {invInst hd : Instruction} {tl : List Instruction}
    (hbb : bb.instructions = front ++ [invInst]) (hinvop : invInst.opcode = Opcode.INVALID)
    (hcons : front ++ [invInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hw : bodyLen + 1 ≤ wOf bb.label)
    (hinvpc : as'.pc < prog.length)
    (hinv : prog.get ⟨as'.pc, hinvpc⟩ = AsmInst.AsmOp "INVALID") :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inl ⟨hrel', hw,
    runBlock_body_invalid ctx bb restFuel front invInst hd tl s sEnd hbb hinvop hcons hphi hnonterm hthread,
    hinvpc, hinv⟩)

/-- Non-vacuity: a bare `[STOP]` block (empty body) drives the generic STOP producer — the body thread is
    trivial, so every hypothesis is dischargeable and the recipe is produced. -/
theorem termRecipeW_stop_of_body_nonvacuous {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s : VenomState} {stopInst : Instruction}
    (hbb : bb.instructions = [stopInst]) (hstopop : stopInst.opcode = Opcode.STOP)
    (hrel' : venomAsmRel lo ps' { s with instIdx := 0 } as')
    (hw : 0 + 1 ≤ wOf bb.label)
    (hstoppc : as'.pc < prog.length)
    (hstop : prog.get ⟨as'.pc, hstoppc⟩ = AsmInst.AsmOp "STOP") :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' { s with instIdx := 0 } 0
      (([] : List Instruction).length + (restFuel + 1)) ctx bb s :=
  termRecipeW_stop_of_body (front := []) (stopInst := stopInst) (hd := stopInst) (tl := [])
    (by simpa using hbb) hstopop (by simp) (by rw [hstopop]; decide) (by intro i hi; cases hi)
    (by simp [execBodyThread]) hrel' hw hstoppc hstop

/-- **Generic SELFDESTRUCT `TermRecipeW`.** The operand-carrying halting sibling: the Venom result
    (`Halt (haltState (selfdestruct addr sEnd))`) is derived from the block's structure plus the operand
    evaluation (`runBlock_body_selfdestruct`), not assumed. -/
theorem termRecipeW_selfdestruct_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {sdInst hd : Instruction} {tl : List Instruction}
    {addrOp : Operand} {addr : bytes32} {stk : List bytes32}
    (hbb : bb.instructions = front ++ [sdInst]) (hop : sdInst.opcode = Opcode.SELFDESTRUCT)
    (hoperands : sdInst.operands = [addrOp]) (haddr : evalOperand addrOp sEnd = some addr)
    (hcons : front ++ [sdInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hw : bodyLen + 1 ≤ wOf bb.label)
    (hsdpc : as'.pc < prog.length)
    (hsd : prog.get ⟨as'.pc, hsdpc⟩ = AsmInst.AsmOp "SELFDESTRUCT")
    (hstk : as'.stack = addr :: stk) :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨addr, stk, hrel', hw,
      runBlock_body_selfdestruct ctx bb restFuel front sdInst hd tl s sEnd addrOp addr hbb hop
        hoperands haddr hcons hphi hnonterm hthread,
      ⟨hsdpc, hsd⟩, hstk⟩))))

/-- **Generic JMP `TermRecipeW`.** The continuing case: the Venom result (`OK (jumpTo lbl sEnd)`) is derived
    from the block's structure (`runBlock_body_jmp`), not assumed; the caller still supplies the resolved
    push/JUMP placement, the successor's plan state, and the layout bound. -/
theorem termRecipeW_jmp_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {jmpInst hd : Instruction} {tl : List Instruction} {lbl : String}
    (hbb : bb.instructions = front ++ [jmpInst]) (hjmpop : jmpInst.opcode = Opcode.JMP)
    (hoperands : jmpInst.operands = [Operand.Label lbl])
    (hcons : front ++ [jmpInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hrel' : venomAsmRel lo ps' sEnd as') (hps : ps' = psOf lbl)
    (hw : wOf lbl + (bodyLen + 2) ≤ wOf bb.label)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hoff_lk : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256)
    (hjump1 : as'.pc + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf lbl))
    (hlk' : lookupBlock lbl fn.blocks = some bb') :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨lbl, off, bb', hrel', hps, hw, hnothalt,
      runBlock_body_jmp ctx bb restFuel front jmpInst hd tl s sEnd lbl hbb hjmpop hoperands hcons hphi
        hnonterm hthread hnothalt,
      ⟨hpush1, hpush⟩, hoff_lk, hoff, ⟨hjump1, hjump⟩, hidx_lk, hlk'⟩)))))

/-- **Generic RETURN `TermRecipeW`.** Venom result derived (`runBlock_body_return`); the caller supplies the
    RETURN placement, the operand stack, and the memory-safety side conditions. -/
theorem termRecipeW_return_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {retInst hd : Instruction} {tl : List Instruction}
    {offOp szOp : Operand} {off sz : bytes32} {rest : List bytes32}
    (hbb : bb.instructions = front ++ [retInst]) (hop : retInst.opcode = Opcode.RETURN)
    (hoperands : retInst.operands = [offOp, szOp])
    (hoffv : evalOperand offOp sEnd = some off) (hszv : evalOperand szOp sEnd = some sz)
    (hcons : front ++ [retInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hw : bodyLen + 1 ≤ wOf bb.label)
    (hretpc : as'.pc < prog.length) (hret : prog.get ⟨as'.pc, hretpc⟩ = AsmInst.AsmOp "RETURN")
    (hstk : as'.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ as'.memory.size)
    (hbelow : off.toNat + sz.toNat ≤ ps'.alloc.fnEom) (hlen : sz.toNat < USize.size) :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inl
    ⟨off, sz, rest, hrel', hw,
      runBlock_body_return ctx bb restFuel front retInst hd tl s sEnd offOp szOp off sz hbb hop
        hoperands hoffv hszv hcons hphi hnonterm hthread,
      ⟨hretpc, hret⟩, hstk, hcov, hbelow, hlen⟩))

/-- **Generic REVERT `TermRecipeW`.** The aborting sibling of RETURN (`runBlock_body_revert`). -/
theorem termRecipeW_revert_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel : Nat}
    {ctx : VenomContext} {bb : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {revInst hd : Instruction} {tl : List Instruction}
    {offOp szOp : Operand} {off sz : bytes32} {rest : List bytes32}
    (hbb : bb.instructions = front ++ [revInst]) (hop : revInst.opcode = Opcode.REVERT)
    (hoperands : revInst.operands = [offOp, szOp])
    (hoffv : evalOperand offOp sEnd = some off) (hszv : evalOperand szOp sEnd = some sz)
    (hcons : front ++ [revInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hrel' : venomAsmRel lo ps' sEnd as')
    (hw : bodyLen + 1 ≤ wOf bb.label)
    (hrevpc : as'.pc < prog.length) (hrev : prog.get ⟨as'.pc, hrevpc⟩ = AsmInst.AsmOp "REVERT")
    (hstk : as'.stack = off :: sz :: rest)
    (hcov : sz.toNat = 0 ∨ ((off.toNat + sz.toNat + 31) / 32) * 32 ≤ as'.memory.size)
    (hbelow : off.toNat + sz.toNat ≤ ps'.alloc.fnEom) (hlen : sz.toNat < USize.size) :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inl
    ⟨off, sz, rest, hrel', hw,
      runBlock_body_revert ctx bb restFuel front revInst hd tl s sEnd offOp szOp off sz hbb hop
        hoperands hoffv hszv hcons hphi hnonterm hthread,
      ⟨hrevpc, hrev⟩, hstk, hcov, hbelow, hlen⟩)))

/-- **Generic JNZ-taken `TermRecipeW`.** Venom result derived (`runBlock_body_jnz_taken`). -/
theorem termRecipeW_jnz_taken_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel off : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {condOp : Operand} {ifNz ifZ : String} {cond : bytes32} {stk : List bytes32}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand condOp sEnd = some cond) (hne : cond ≠ EvmYul.UInt256.ofNat 0)
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hw : wOf ifNz + (bodyLen + 2) ≤ wOf bb.label)
    (hstk_c : as'.stack = cond :: stk)
    (hpush1 : as'.pc < prog.length)
    (hpush : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoffb : off < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat o2pc off = some (pcOf ifNz))
    (hrel_succ : venomAsmRel lo (psOf ifNz) sEnd { as' with stack := stk })
    (hlk' : lookupBlock ifNz fn.blocks = some bb') :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨ifNz, off, cond, stk, bb', hw, hnothalt,
      runBlock_body_jnz_taken ctx bb restFuel front jnzInst hd tl s sEnd condOp ifNz ifZ cond hbb hop
        hoperands hcondv hne hcons hphi hnonterm hthread hnothalt,
      hstk_c, hne, ⟨hpush1, hpush⟩, hoff_lk, hoffb, ⟨hjumpi1, hjumpi⟩, hidx_lk, hrel_succ, hlk'⟩))))))

/-- **Generic JNZ-not-taken `TermRecipeW`.** Venom result derived (`runBlock_body_jnz_nottaken`): the
    condition evaluates to zero, so the block falls through to `ifZ`. -/
theorem termRecipeW_jnz_nottaken_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel offN offZ : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {jnzInst hd : Instruction} {tl : List Instruction}
    {condOp : Operand} {ifNz ifZ : String} {stk : List bytes32}
    (hbb : bb.instructions = front ++ [jnzInst]) (hop : jnzInst.opcode = Opcode.JNZ)
    (hoperands : jnzInst.operands = [condOp, Operand.Label ifNz, Operand.Label ifZ])
    (hcondv : evalOperand condOp sEnd = some ({ val := 0 } : bytes32))
    (hcons : front ++ [jnzInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hw : wOf ifZ + (bodyLen + 4) ≤ wOf bb.label)
    (hstk_c : as'.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpush1 : as'.pc < prog.length)
    (hpushN : prog.get ⟨as'.pc, hpush1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoffN_lk : AssocList.lookup String Nat offsets ifNz = some offN) (hoffNb : offN < 2 ^ 256)
    (hjumpi1 : as'.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨as'.pc + 1, hjumpi1⟩ = AsmInst.AsmOp "JUMPI")
    (hpush2 : as'.pc + 2 < prog.length)
    (hpushZ : prog.get ⟨as'.pc + 2, hpush2⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifZ))
    (hoffZ_lk : AssocList.lookup String Nat offsets ifZ = some offZ) (hoffZb : offZ < 2 ^ 256)
    (hjump1 : as'.pc + 2 + 1 < prog.length)
    (hjump : prog.get ⟨as'.pc + 2 + 1, hjump1⟩ = AsmInst.AsmOp "JUMP")
    (hidxZ_lk : AssocList.lookup Nat Nat o2pc offZ = some (pcOf ifZ))
    (hrel_succ : venomAsmRel lo (psOf ifZ) sEnd { as' with stack := stk })
    (hlk' : lookupBlock ifZ fn.blocks = some bb') :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨ifNz, ifZ, offN, offZ, stk, bb', hw, hnothalt,
      runBlock_body_jnz_nottaken ctx bb restFuel front jnzInst hd tl s sEnd condOp ifNz ifZ hbb hop
        hoperands hcondv hcons hphi hnonterm hthread hnothalt,
      hstk_c, ⟨hpush1, hpushN⟩, hoffN_lk, hoffNb, ⟨hjumpi1, hjumpi⟩, ⟨hpush2, hpushZ⟩, hoffZ_lk, hoffZb,
      ⟨hjump1, hjump⟩, hidxZ_lk, hrel_succ, hlk'⟩)))))))

/-- **Generic DJMP `TermRecipeW`.** Venom result derived (`runBlock_body_djmp`): the selector indexes the
    label list. The caller supplies the dispatch chain's asm run. Completes the generic-producer family:
    the Venom side of every one of the eight `TermRecipeW` arms is now derived from the block's structure. -/
theorem termRecipeW_djmp_of_body {fn : IrFunction} {lo : AssocList String Nat}
    {pcOf : String → Nat} {psOf : String → PlanState} {wOf : String → Nat}
    {o2pc : AssocList Nat Nat} {offsets : AssocList String Nat} {prog : List AsmInst}
    {as' : AsmState} {ps' : PlanState} {bodyLen restFuel chainLen : Nat}
    {ctx : VenomContext} {bb bb' : BasicBlock} {s sEnd : VenomState}
    {front : List Instruction} {dInst hd : Instruction} {tl : List Instruction}
    {selectorOp : Operand} {labelOps : List Operand} {idx : bytes32} {labels : List String}
    {rest : List bytes32} {hi : idx.toNat < labels.length}
    (hbb : bb.instructions = front ++ [dInst]) (hop : dInst.opcode = Opcode.DJMP)
    (hoperands : dInst.operands = selectorOp :: labelOps)
    (hsel : evalOperand selectorOp sEnd = some idx) (hlabels : extractLabels labelOps = some labels)
    (hcons : front ++ [dInst] = hd :: tl) (hphi : hd.opcode ≠ Opcode.PHI)
    (hnonterm : ∀ inst ∈ front, isTerminator inst.opcode = false)
    (hthread : execBodyThread front 0 { s with instIdx := 0 } = some sEnd)
    (hnothalt : sEnd.halted = false)
    (hw : wOf (labels.get ⟨idx.toNat, hi⟩) + (bodyLen + chainLen) ≤ wOf bb.label)
    (hdispatch : runAsm chainLen o2pc prog as'
      = AsmResult.AsmOK { as' with stack := rest, pc := pcOf (labels.get ⟨idx.toNat, hi⟩) })
    (hrel_succ : venomAsmRel lo (psOf (labels.get ⟨idx.toNat, hi⟩)) sEnd { as' with stack := rest })
    (hlk' : lookupBlock (labels.get ⟨idx.toNat, hi⟩) fn.blocks = some bb') :
    TermRecipeW fn lo pcOf psOf wOf o2pc offsets prog as' ps' sEnd bodyLen
      (front.length + (restFuel + 1)) ctx bb s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨labels.get ⟨idx.toNat, hi⟩, chainLen, rest, bb', hw, hnothalt,
      runBlock_body_djmp ctx bb restFuel front dInst hd tl s sEnd selectorOp labelOps idx labels hi
        hbb hop hoperands hsel hlabels hcons hphi hnonterm hthread hnothalt,
      hdispatch, hrel_succ, hlk'⟩)))))))


end EvmYul.Venom.Hol.Codegen

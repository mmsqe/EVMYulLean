import EvmYul.Venom.Hol.Codegen.GenInstSim

/-!
# AsmResolve correctness (label-resolution layer)

`genBlockSimulation` runs the *raw* `executePlan` with unresolved `AsmPushLabel` (which
`asmStep` rejects) and an empty `offsetToPc`, so control-flow blocks are unprovable at that
layer. The fix is to run the *resolved* program `asmResolve (executePlan ops)`. This file
builds the correctness of that resolution:

* the resolved label push pushes the byte offset (`resolved_push_toNat`, codec round-trip);
* (todo) `buildOffsetToPc` maps the offset back to the target's list index;
* (todo) the resolved terminator's `PUSH; JUMP` simulates the block-to-block transition;
* (todo) lifting `genBlockSimulation` to the resolved program (body sims transfer via
  `map_resolveInst_eq_self`, terminator via the above).

The `resolveInst` characterization (`resolveInst_self_of_ne`, `map_resolveInst_eq_self`, …)
lives in `GenBlockSimSupport`.
-/

namespace EvmYul.Venom.Hol.Codegen

open EvmYul.Venom.Hol EvmYul

/-- The value pushed by a resolved label push round-trips to the byte offset (`off < 2^256`,
    so `toNat` is exact). The codec atom of the terminator-resolution sim — `JUMP` reads this
    value as its destination and resolves it via `offsetToPc`. -/
theorem resolved_push_toNat (off : Nat) (hoff : off < 2 ^ 256) :
    (wordOfBytes (List.toByteArray (padBytes symbolSize (encodeNumBytes off)))).toNat = off := by
  unfold wordOfBytes padBytes
  rw [EvmYul.uint256_ofNat_toNat, EvmYul.toByteArray_toList]
  split
  · rw [fromBytesBigEndian_encodeNumBytes]; exact Nat.mod_eq_of_lt hoff
  · rw [fromBytesBigEndian_zero_prefix, fromBytesBigEndian_encodeNumBytes]
    exact Nat.mod_eq_of_lt hoff

/-! ## Resolution safety: no label/offset push survives

`resolveInst` rewrites every `AsmPushLabel`/`AsmPushOfst` to an `AsmPush`, so the resolved
program is push-label-free — `asmStep` never hits the "unresolved PUSH label/ofst" error on
it. (This is the whole point of running the resolved program in the lifted capstone.) -/

theorem resolveInst_ne_pushLabel (offsets) (inst : AsmInst) (lbl : String) :
    resolveInst offsets inst ≠ AsmInst.AsmPushLabel lbl := by
  cases inst <;> simp [resolveInst] <;> (try split) <;> simp

theorem resolveInst_ne_pushOfst (offsets) (inst : AsmInst) (lbl : String) (d : Nat) :
    resolveInst offsets inst ≠ AsmInst.AsmPushOfst lbl d := by
  cases inst <;> simp [resolveInst] <;> (try split) <;> simp

/-- No `AsmPushLabel` survives resolution: every element of the resolved program differs
    from `AsmPushLabel _`. -/
theorem mem_map_resolveInst_ne_pushLabel (offsets) (L : List AsmInst) (lbl : String)
    (a : AsmInst) (ha : a ∈ L.map (resolveInst offsets)) : a ≠ AsmInst.AsmPushLabel lbl := by
  rw [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact resolveInst_ne_pushLabel offsets b lbl

/-! ## Resolved label push: `asmStep` pushes the byte offset

The push half of the terminator resolution: `asmStep` over a resolved label push pushes a
value reading back as the label's byte offset — exactly what the following `JUMP`/`JUMPI`
consumes as its destination (then resolved to a list index via `offsetToPc`). -/

theorem fromBytesBigEndian_padBytes (k off : Nat) :
    EvmYul.fromBytesBigEndian (padBytes k (encodeNumBytes off)) = off := by
  unfold padBytes
  split
  · exact fromBytesBigEndian_encodeNumBytes off
  · rw [fromBytesBigEndian_zero_prefix]; exact fromBytesBigEndian_encodeNumBytes off

/-- `asmStep` over a resolved label push: pushes a value whose `toNat` is the label's byte
    offset (the destination `JUMP` reads). -/
theorem asmStep_resolved_pushLabel {offsetToPc : AssocList Nat Nat}
    {offsets : AssocList String Nat} {prog : List AsmInst}
    {s : AsmState} {lbl : String} {off : Nat} (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = resolveInst offsets (AsmInst.AsmPushLabel lbl))
    (hlook : AssocList.lookup String Nat offsets lbl = some off) (hoff : off < 2 ^ 256) :
    ∃ v : bytes32, asmStep offsetToPc prog s
        = AsmResult.AsmOK ({ asmNext s with stack := v :: s.stack }) ∧ v.toNat = off := by
  rw [resolveInst_AsmPushLabel hlook] at hprog
  rw [asmStep_push_ok hpc hprog]
  refine ⟨_, rfl, ?_⟩
  unfold wordOfBytes
  rw [EvmYul.uint256_ofNat_toNat, EvmYul.toByteArray_toList, fromBytesBigEndian_zero_prefix,
      fromBytesBigEndian_padBytes]
  exact Nat.mod_eq_of_lt hoff

/-- `asmStep` at a `JUMP` opcode dispatches to `asmJump offsetToPc` (the string match on the
    opcode literal reduces definitionally). -/
theorem asmStep_jump_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "JUMP") :
    asmStep offsetToPc prog s = asmJump offsetToPc s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **Resolved JUMP simulation**: the resolved `[push-label target ; JUMP]` jumps to the
    target's list index `idx` (where `offsets.lookup target = some off` and
    `offsetToPc.lookup off = some idx` — both discharged by `computeLabelOffsets_lookup` /
    `buildOffsetToPc_lookup`). Pops the pushed destination, sets `pc := idx`. -/
theorem resolved_jump_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {target : String} {off idx : Nat}
    (hpc1 : s.pc < prog.length)
    (hpush : prog.get ⟨s.pc, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : s.pc + 1 < prog.length)
    (hjump : prog.get ⟨s.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runAsm 2 offsetToPc prog s = AsmResult.AsmOK { s with pc := idx } := by
  obtain ⟨v, hstep1, hvoff⟩ :=
    asmStep_resolved_pushLabel (offsetToPc := offsetToPc) hpc1 hpush hoff_lk hoff
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hpc1 hstep1]
  have hjstep : asmStep offsetToPc prog ({ asmNext s with stack := v :: s.stack })
      = AsmResult.AsmOK { s with pc := idx } := by
    rw [asmStep_jump_ok hpc2 hjump]
    simp only [asmJump, hvoff, hidx_lk]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc2 hjstep]
  rfl

/-- **Block-local JMP asm composition** (toward the multi-block `hfsim`): given the block's body asm
    run reaching the pre-JMP state `asmPreJmp` (`runAsm bodyLen … asm = AsmOK asmPreJmp`, composed from
    `soLabel_sim` + the body fold) and the resolved `[push-label target ; JUMP]` at `asmPreJmp.pc`,
    running the whole block (`bodyLen + 2` steps) lands at the successor's entry index `idx` with the
    stack unchanged from `asmPreJmp` (the pushed destination is popped). This is exactly the
    block-local JMP sim's `runAsm n … asm = AsmOK asm'` (`n := bodyLen + 2`,
    `asm' := { asmPreJmp with pc := idx }`) that `jmp_budget_step` consumes; the remaining content is
    relating `asm'` to the successor Venom state via the successor's `Entry` (the reconciled stack
    layout — `asmPreJmp.stack` must be the target's expected entry layout, established by the JMP's
    join-point reorder). -/
theorem block_jmp_asm_compose {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {asm asmPreJmp : AsmState} {target : String} {off idx bodyLen : Nat}
    (hbody : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asmPreJmp)
    (hpc1 : asmPreJmp.pc < prog.length)
    (hpush : prog.get ⟨asmPreJmp.pc, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asmPreJmp.pc + 1 < prog.length)
    (hjump : prog.get ⟨asmPreJmp.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runAsm (bodyLen + 2) offsetToPc prog asm = AsmResult.AsmOK { asmPreJmp with pc := idx } :=
  runAsm_compose hbody (resolved_jump_sim hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk)

/-- `venomAsmRel` ignores the asm `pc` (it relates stack / spill / memory / shared state, never
    `as.pc`), so setting the pc preserves it — definitional. The post-JMP state (`pc := idx`) stays
    related to the same Venom/plan state as the pre-JMP state. -/
theorem venomAsmRel_setPc {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    {as : AsmState} {p : Nat} (h : venomAsmRel lo ps vs as) :
    venomAsmRel lo ps vs { as with pc := p } := h

/-- **Block-local JMP sim** (toward the multi-block `hfsim`): packages the asm run with its
    `venomAsmRel`. Given the body asm run reaching `asmPreJmp` related to the post-body Venom/plan
    state (`hbody`/`hrel`) and the resolved `[push-label target ; JUMP]`, running the whole block
    lands at the successor's entry index `idx` (`asm'.pc = idx`) still related to the post-body state
    (the JMP only changes the pc, which `venomAsmRel` ignores). This is the
    `runAsm n … asm = AsmOK asm'` + `venomAsmRel`-at-successor-entry that the successor's `Entry`
    construction (and `jmp_budget_step`) consume; the remaining content is that the post-body plan
    stack is the target's expected entry layout (the JMP join-point reorder + the cross-block plan-state
    threading of `generateFnPlan`). -/
theorem block_jmp_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {asm asmPreJmp : AsmState} {target : String} {off idx bodyLen : Nat}
    {lo : AssocList String Nat} {psPostBody : PlanState} {sPostBody : VenomState}
    (hbody : runAsm bodyLen offsetToPc prog asm = AsmResult.AsmOK asmPreJmp)
    (hrel : venomAsmRel lo psPostBody sPostBody asmPreJmp)
    (hpc1 : asmPreJmp.pc < prog.length)
    (hpush : prog.get ⟨asmPreJmp.pc, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : asmPreJmp.pc + 1 < prog.length)
    (hjump : prog.get ⟨asmPreJmp.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asm', runAsm (bodyLen + 2) offsetToPc prog asm = AsmResult.AsmOK asm' ∧
            venomAsmRel lo psPostBody sPostBody asm' ∧ asm'.pc = idx :=
  ⟨{ asmPreJmp with pc := idx },
   block_jmp_asm_compose hbody hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk,
   venomAsmRel_setPc hrel, rfl⟩

/-- **Asm-side sim for a bare JMP entry block** (`[SOLabel l, SOPushLabel target, SOEmit "JUMP"]`) —
    the simplest `hentryAsm` for `hfsim_jmp_then_halt`. Running the block (`JUMPDEST ; push-label ;
    JUMP`) from the entry `as` reaches the successor's entry index `idx` (`runAsm 3 = AsmOK asMid`,
    `asMid.pc = idx`), still related to the same Venom/plan state. Composes `asmStep_label_ok` (the
    `JUMPDEST` advances pc to the concrete `asmNext as`) with `block_jmp_sim` (the resolved
    `[push-label ; JUMP]`); `venomAsmRel` is pc-independent, so `hrel` transfers unchanged. Reduces
    `hentryAsm` to the whole-program facts the caller supplies: the `asmBlockAt` for the `JUMPDEST` and
    the resolved-JUMP destination lookups. -/
theorem hentryAsm_bare_jmp {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {as : AsmState} {l target : String} {off idx : Nat}
    {lo : AssocList String Nat} {ps : PlanState} {vs : VenomState}
    (hrel : venomAsmRel lo ps vs as)
    (hbLabel : asmBlockAt prog as.pc (executePlan [StackOp.SOLabel l]))
    (hpc1 : as.pc + 1 < prog.length)
    (hpush : prog.get ⟨as.pc + 1, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel target))
    (hoff_lk : AssocList.lookup String Nat offsets target = some off) (hoff : off < 2 ^ 256)
    (hpc2 : as.pc + 2 < prog.length)
    (hjump : prog.get ⟨as.pc + 2, hpc2⟩ = AsmInst.AsmOp "JUMP")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    ∃ asMid, runAsm 3 offsetToPc prog as = AsmResult.AsmOK asMid ∧
             venomAsmRel lo ps vs asMid ∧ asMid.pc = idx := by
  obtain ⟨hpcL, hgetL⟩ := asmBlockAt_one hbLabel
  have hbody : runAsm 1 offsetToPc prog as = AsmResult.AsmOK (asmNext as) := by
    unfold runAsm; rw [asmStep_label_ok hpcL hgetL]; rfl
  rw [show (3 : Nat) = 1 + 2 from rfl]
  exact block_jmp_sim hbody hrel hpc1 hpush hoff_lk hoff hpc2 hjump hidx_lk

/-- `asmStep` at a `JUMPI` opcode dispatches to `asmJumpi offsetToPc`. -/
theorem asmStep_jumpi_ok {offsetToPc : AssocList Nat Nat} {prog : List AsmInst} {s : AsmState}
    (hpc : s.pc < prog.length) (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "JUMPI") :
    asmStep offsetToPc prog s = asmJumpi offsetToPc s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- **Resolved JNZ — branch taken**: with a nonzero condition `cond` on top of the stack, the
    resolved `[push-label ifNz ; JUMPI]` consumes both `cond` and the pushed destination and jumps
    to `ifNz`'s list index `idx`. (JNZ lowers to `[push ifNz ; JUMPI ; push ifZ ; JUMP]`.) -/
theorem resolved_jumpi_taken_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {ifNz : String} {off idx : Nat} {cond : bytes32}
    {stk : List bytes32}
    (hstack : s.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpc1 : s.pc < prog.length)
    (hpush : prog.get ⟨s.pc, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc2 : s.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨s.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI")
    (hidx_lk : AssocList.lookup Nat Nat offsetToPc off = some idx) :
    runAsm 2 offsetToPc prog s = AsmResult.AsmOK { s with stack := stk, pc := idx } := by
  obtain ⟨v, hstep1, hvoff⟩ :=
    asmStep_resolved_pushLabel (offsetToPc := offsetToPc) hpc1 hpush hoff_lk hoff
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hpc1 hstep1]
  have hjstep : asmStep offsetToPc prog ({ asmNext s with stack := v :: s.stack })
      = AsmResult.AsmOK { s with stack := stk, pc := idx } := by
    rw [asmStep_jumpi_ok hpc2 hjumpi]
    unfold asmJumpi
    rw [hstack]
    simp only [if_neg hcond, hvoff, hidx_lk]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc2 hjstep]
  rfl

/-- **Resolved JNZ — branch not taken**: with a zero condition on top of the stack, the resolved
    `[push-label ifNz ; JUMPI]` consumes `cond` and the pushed destination and falls through to
    `pc + 2` (the following `[push-label ifZ ; JUMP]`, handled by `resolved_jump_sim`). -/
theorem resolved_jumpi_nottaken_sim {offsets : AssocList String Nat} {offsetToPc : AssocList Nat Nat}
    {prog : List AsmInst} {s : AsmState} {ifNz : String} {off : Nat} {stk : List bytes32}
    (hstack : s.stack = EvmYul.UInt256.ofNat 0 :: stk)
    (hpc1 : s.pc < prog.length)
    (hpush : prog.get ⟨s.pc, hpc1⟩ = resolveInst offsets (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat offsets ifNz = some off) (hoff : off < 2 ^ 256)
    (hpc2 : s.pc + 1 < prog.length)
    (hjumpi : prog.get ⟨s.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI") :
    runAsm 2 offsetToPc prog s = AsmResult.AsmOK { s with stack := stk, pc := s.pc + 2 } := by
  obtain ⟨v, hstep1, _hvoff⟩ :=
    asmStep_resolved_pushLabel (offsetToPc := offsetToPc) hpc1 hpush hoff_lk hoff
  rw [show (2 : Nat) = 1 + 1 from rfl, runAsm_succ_ok hpc1 hstep1]
  have hjstep : asmStep offsetToPc prog ({ asmNext s with stack := v :: s.stack })
      = AsmResult.AsmOK { s with stack := stk, pc := s.pc + 2 } := by
    rw [asmStep_jumpi_ok hpc2 hjumpi]
    unfold asmJumpi
    rw [hstack]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runAsm_succ_ok hpc2 hjstep]
  rfl

/-! ## `asmResolve` structure

Projections and length preservation: resolution keeps the program length, so `pc` bounds and
`asmBlockAt` lengths transfer between the unresolved and resolved programs. -/

theorem asmResolve_fst (asm : List AsmInst) :
    (asmResolve asm).1 = asm.map (resolveInst (computeLabelOffsets asm).2) := rfl

theorem asmResolve_snd (asm : List AsmInst) :
    (asmResolve asm).2 = buildOffsetToPc asm := rfl

/-- Resolution preserves program length, so `pc` bounds (and `asmBlockAt` lengths) transfer
    between the unresolved and resolved programs. -/
theorem asmResolve_length (asm : List AsmInst) :
    (asmResolve asm).1.length = asm.length := by
  rw [asmResolve_fst, List.length_map]

/-- For a label-push-free program, resolution is the identity: `(asmResolve asm).1 = asm`. So a
    block with no label pushes (e.g. a STOP/INVALID-terminated block) runs identically on the
    resolved and unresolved programs — every sim already proved transfers verbatim, lifting the
    terminal-terminator cases of `genBlockSimulation` to the resolved layer for free. -/
theorem asmResolve_fst_eq_of_no_label (asm : List AsmInst)
    (h1 : ∀ a ∈ asm, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (h2 : ∀ a ∈ asm, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    (asmResolve asm).1 = asm := by
  rw [asmResolve_fst, map_resolveInst_eq_self _ asm h1 h2]

/-- **A block segment is an `asmBlockAt` in the resolved program, at its offset.** Combines
    `asmBlockAt_of_middle` (the segment is at offset `A.length` in `A ++ insts ++ B`) with
    `asmBlockAt_map` (lift through `resolveInst`, since `(asmResolve …).1 = … .map (resolveInst …)`).
    The resolved block is `insts.map (resolveInst offsets)`. -/
theorem asmBlockAt_resolved_of_middle (A insts B : List AsmInst) :
    asmBlockAt (asmResolve (A ++ insts ++ B)).1 A.length
      (insts.map (resolveInst (computeLabelOffsets (A ++ insts ++ B)).2)) := by
  rw [asmResolve_fst]
  exact asmBlockAt_map _ (asmBlockAt_of_middle A insts B)

/-- For a **label-push-free** block segment (e.g. a STOP/INVALID-terminated block with no internal
    `JMP`), resolution is the identity, so the segment is itself an `asmBlockAt` in the resolved
    program at its offset. This is exactly `hasm_stop`'s `hblock`: the resolved STOP block
    `[AsmLabel l, AsmOp "STOP"]` sits at the terminal block's pc. -/
theorem asmBlockAt_resolved_of_middle_no_label (A insts B : List AsmInst)
    (h1 : ∀ a ∈ insts, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (h2 : ∀ a ∈ insts, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    asmBlockAt (asmResolve (A ++ insts ++ B)).1 A.length insts := by
  have h := asmBlockAt_resolved_of_middle A insts B
  rwa [map_resolveInst_eq_self _ insts h1 h2] at h

/-! ## `buildOffsetToPc` offset accumulation

Foundation for `buildOffsetToPc` exact-index correctness (the JUMP-destination side): the fold's
offset component accumulates the cumulative instruction size — the same accumulation
`computeLabelOffsets` uses, so the two resolution maps assign byte offsets consistently. -/

theorem buildOffsetToPc_off_acc (asm : List AsmInst) :
    ∀ (i0 off0 : Nat) (m0 : AssocList Nat Nat),
      ((asm.zipIdx i0).foldl (fun (acc : Nat × AssocList Nat Nat) (instI : AsmInst × Nat) =>
        (acc.1 + asmInstSize instI.1,
         match instI.1 with
         | AsmInst.AsmLabel _ => AssocList.insert Nat Nat acc.2 acc.1 instI.2
         | _ => acc.2)) (off0, m0)).1
      = off0 + (asm.map asmInstSize).sum := by
  induction asm with
  | nil => intro i0 off0 m0; simp
  | cons a as ih =>
    intro i0 off0 m0
    rw [List.zipIdx_cons, List.foldl_cons, ih (i0 + 1)]
    simp [List.sum_cons, Nat.add_assoc]

/-! ## `buildOffsetToPc` exact-index correctness (JUMP destination) -/

theorem assocLookup_insert_self {α β} [BEq α] [LawfulBEq α] (m : AssocList α β) (k : α) (v : β) :
    AssocList.lookup α β (AssocList.insert α β m k v) k = some v := by
  rw [assocLookup_eq_listLookup]; simp [AssocList.insert]

/-- Processing a suffix whose accumulated offsets all exceed `o` preserves `lookup o` (every
    inserted key is an offset `> o`, hence `≠ o`). -/
theorem buildStep_fold_lookup_preserved (asm : List AsmInst) (o : Nat) :
    ∀ (i0 off_start : Nat) (m : AssocList Nat Nat), o < off_start →
      AssocList.lookup Nat Nat ((asm.zipIdx i0).foldl
        (fun (acc : Nat × AssocList Nat Nat) (instI : AsmInst × Nat) =>
          (acc.1 + asmInstSize instI.1,
           match instI.1 with
           | AsmInst.AsmLabel _ => AssocList.insert Nat Nat acc.2 acc.1 instI.2
           | _ => acc.2)) (off_start, m)).2 o
      = AssocList.lookup Nat Nat m o := by
  induction asm with
  | nil => intro i0 off_start m h; simp
  | cons a as ih =>
    intro i0 off_start m h
    rw [List.zipIdx_cons, List.foldl_cons, ih (i0 + 1) (off_start + asmInstSize a) _ (by omega)]
    cases a <;> first | rfl | exact assocLookup_insert_ne m off_start o _ (by omega)

/-- **`buildOffsetToPc` exact-index correctness** — the JUMP-destination lemma: a label at list
    index `pre.length` (byte offset `(pre.map asmInstSize).sum`) resolves to its index. Offset
    uniqueness is automatic: the label contributes size 1, so the suffix's offsets all exceed it
    (preservation), and the prefix never inserted that key. -/
theorem buildOffsetToPc_lookup (pre : List AsmInst) (lbl : String) (suf : List AsmInst) :
    AssocList.lookup Nat Nat (buildOffsetToPc (pre ++ AsmInst.AsmLabel lbl :: suf))
      ((pre.map asmInstSize).sum) = some pre.length := by
  have heq : buildOffsetToPc (pre ++ AsmInst.AsmLabel lbl :: suf)
      = ((pre ++ AsmInst.AsmLabel lbl :: suf).zipIdx.foldl
          (fun (acc : Nat × AssocList Nat Nat) (instI : AsmInst × Nat) =>
            (acc.1 + asmInstSize instI.1,
             match instI.1 with
             | AsmInst.AsmLabel _ => AssocList.insert Nat Nat acc.2 acc.1 instI.2
             | _ => acc.2)) (0, [])).2 := rfl
  rw [heq, List.zipIdx_append, List.foldl_append]
  set step := (fun (acc : Nat × AssocList Nat Nat) (instI : AsmInst × Nat) =>
            (acc.1 + asmInstSize instI.1,
             match instI.1 with
             | AsmInst.AsmLabel _ => AssocList.insert Nat Nat acc.2 acc.1 instI.2
             | _ => acc.2)) with hstepdef
  set P := (pre.zipIdx 0).foldl step (0, []) with hPdef
  have hP1 : P.1 = (pre.map asmInstSize).sum := by
    rw [hPdef]; have := buildOffsetToPc_off_acc pre 0 0 []; simpa [hstepdef] using this
  have hLstep : step P (AsmInst.AsmLabel lbl, pre.length)
      = (P.1 + 1, AssocList.insert Nat Nat P.2 P.1 pre.length) := by
    rw [hstepdef]; simp [asmInstSize]
  rw [Nat.zero_add, List.zipIdx_cons, List.foldl_cons, hLstep, ← hP1,
      buildStep_fold_lookup_preserved suf P.1 (pre.length + 1) (P.1 + 1)
        (AssocList.insert Nat Nat P.2 P.1 pre.length) (by omega)]
  exact assocLookup_insert_self _ _ _

/-! ## `computeLabelOffsets` correctness (label → byte offset)

The companion of `buildOffsetToPc_lookup`: a `JUMP`'s pushed offset is `computeLabelOffsets`'
value for the target label, and it must equal the byte offset `buildOffsetToPc` maps back to
the target index. Both fold `asmInstSize`, so they agree. -/

theorem computeLabelOffsets_pc_acc (asm : List AsmInst) :
    ∀ (pc0 : Nat) (m0 : AssocList String Nat),
      (asm.foldl (fun (acc : Nat × AssocList String Nat) (inst : AsmInst) =>
        let labels := match inst with
          | AsmInst.AsmLabel lbl => AssocList.insert String Nat acc.2 lbl acc.1
          | AsmInst.AsmDataHeader lbl => AssocList.insert String Nat acc.2 lbl acc.1
          | _ => acc.2
        (acc.1 + asmInstSize inst, labels)) (pc0, m0)).1
      = pc0 + (asm.map asmInstSize).sum := by
  induction asm with
  | nil => intro pc0 m0; simp
  | cons a as ih => intro pc0 m0; rw [List.foldl_cons, ih]; simp [List.sum_cons, Nat.add_assoc]

/-- Processing a suffix that inserts no label/dataheader named `lbl` preserves `lookup lbl`. -/
theorem computeLabelOffsets_preserved (asm : List AsmInst) (lbl : String) :
    ∀ (pc0 : Nat) (m : AssocList String Nat),
      (∀ inst ∈ asm, inst ≠ AsmInst.AsmLabel lbl ∧ inst ≠ AsmInst.AsmDataHeader lbl) →
      AssocList.lookup String Nat (asm.foldl (fun (acc : Nat × AssocList String Nat) (inst : AsmInst) =>
        let labels := match inst with
          | AsmInst.AsmLabel l => AssocList.insert String Nat acc.2 l acc.1
          | AsmInst.AsmDataHeader l => AssocList.insert String Nat acc.2 l acc.1
          | _ => acc.2
        (acc.1 + asmInstSize inst, labels)) (pc0, m)).2 lbl
      = AssocList.lookup String Nat m lbl := by
  induction asm with
  | nil => intro pc0 m _; simp
  | cons a as ih =>
    intro pc0 m h
    rw [List.foldl_cons, ih (pc0 + asmInstSize a) _
          (fun inst hinst => h inst (List.mem_cons_of_mem _ hinst))]
    obtain ⟨hne1, hne2⟩ := h a List.mem_cons_self
    cases a <;> first | rfl | exact assocLookup_insert_ne m _ lbl pc0 (fun he => by simp_all)

/-- **`computeLabelOffsets` correctness** (label → byte offset): a label at list index
    `pre.length` resolves to byte offset `(pre.map asmInstSize).sum`, given its name is unique in
    the suffix. The label→offset companion of `buildOffsetToPc_lookup`. -/
theorem computeLabelOffsets_lookup (pre : List AsmInst) (lbl : String) (suf : List AsmInst)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel lbl ∧ inst ≠ AsmInst.AsmDataHeader lbl) :
    AssocList.lookup String Nat (computeLabelOffsets (pre ++ AsmInst.AsmLabel lbl :: suf)).2 lbl
      = some ((pre.map asmInstSize).sum) := by
  have heq : computeLabelOffsets (pre ++ AsmInst.AsmLabel lbl :: suf)
      = (pre ++ AsmInst.AsmLabel lbl :: suf).foldl (fun (acc : Nat × AssocList String Nat) (inst : AsmInst) =>
          let labels := match inst with
            | AsmInst.AsmLabel l => AssocList.insert String Nat acc.2 l acc.1
            | AsmInst.AsmDataHeader l => AssocList.insert String Nat acc.2 l acc.1
            | _ => acc.2
          (acc.1 + asmInstSize inst, labels)) (0, []) := rfl
  rw [heq, List.foldl_append]
  set step := (fun (acc : Nat × AssocList String Nat) (inst : AsmInst) =>
          let labels := match inst with
            | AsmInst.AsmLabel l => AssocList.insert String Nat acc.2 l acc.1
            | AsmInst.AsmDataHeader l => AssocList.insert String Nat acc.2 l acc.1
            | _ => acc.2
          (acc.1 + asmInstSize inst, labels)) with hstepdef
  set P := pre.foldl step (0, []) with hPdef
  have hP1 : P.1 = (pre.map asmInstSize).sum := by
    rw [hPdef]; have := computeLabelOffsets_pc_acc pre 0 []; simpa [hstepdef] using this
  have hLstep : step P (AsmInst.AsmLabel lbl) = (P.1 + 1, AssocList.insert String Nat P.2 lbl P.1) := by
    rw [hstepdef]; simp [asmInstSize]
  rw [List.foldl_cons, hLstep, computeLabelOffsets_preserved suf lbl (P.1 + 1) _ hsuf, hP1,
      assocLookup_insert_self]

/-- **Resolved-JUMP destination = the target label's list index (`pcOf`).** The `offsetToPc` round-trip
    for a JMP/JNZ target: composing `computeLabelOffsets_lookup` (label `lbl` → its byte offset
    `(pre.map asmInstSize).sum`) with `buildOffsetToPc_lookup` (that byte offset → its list index
    `pre.length`), the destination the resolved JUMP jumps to — `offsetToPc.lookup (offsets.lookup lbl)`
    — is exactly `lbl`'s list index `pre.length` in the program. This is the well-scheduling label-offset
    fact `idx = pcOf bb'.label`: `pcOf bb'.label = pre.length` (the position of `bb'`'s `AsmLabel` in
    `prog`), and the JMP lands there. -/
theorem resolvedJump_target_index (pre : List AsmInst) (lbl : String) (suf : List AsmInst)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel lbl ∧ inst ≠ AsmInst.AsmDataHeader lbl) :
    AssocList.lookup Nat Nat (asmResolve (pre ++ AsmInst.AsmLabel lbl :: suf)).2
      ((AssocList.lookup String Nat
        (computeLabelOffsets (pre ++ AsmInst.AsmLabel lbl :: suf)).2 lbl).getD 0)
      = some pre.length := by
  rw [computeLabelOffsets_lookup pre lbl suf hsuf, Option.getD_some]
  exact buildOffsetToPc_lookup pre lbl suf

/-- **Concrete scheduled entry pc** — the uniform `pcOf` instantiating `hfsim_venomAsmRelSched`'s
    abstract parameter: a block label's scheduled entry pc is the list index of its `AsmLabel` marker
    in the assembled program. -/
def pcOfLabel (prog : List AsmInst) (lbl : String) : Nat :=
  prog.findIdx (fun i => match i with | AsmInst.AsmLabel l => l == lbl | _ => false)

/-- For a program that contains `lbl`'s `AsmLabel` exactly once (none in the `pre` prefix),
    `pcOfLabel` is the prefix length — the marker's position. -/
theorem pcOfLabel_of_decomp (pre : List AsmInst) (lbl : String) (suf : List AsmInst)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel lbl) :
    pcOfLabel (pre ++ AsmInst.AsmLabel lbl :: suf) lbl = pre.length := by
  unfold pcOfLabel
  have hb : ∀ x ∈ pre, (match x with | AsmInst.AsmLabel l => l == lbl | _ => false) = false := by
    intro x hx
    cases x with
    | AsmLabel l =>
      show (l == lbl) = false
      exact beq_eq_false_iff_ne.mpr (fun h => hpre _ hx (by rw [h]))
    | _ => rfl
  rw [List.findIdx_append, List.findIdx_eq_length.mpr hb, if_neg (by omega)]
  simp [List.findIdx_cons]

/-- **Resolved JMP lands at `pcOfLabel` (concrete `idx = pcOf bb'.label`).** Packages
    `resolvedJump_target_index` against the concrete `pcOfLabel`: for a program with `lbl`'s marker
    unique, the destination a resolved JUMP to `lbl` computes — `offsetToPc.lookup (offsets.lookup lbl)`
    — is exactly `some (pcOfLabel prog lbl)`. This is the well-scheduling pc fact
    `hfsim_venomAsmRelSched` abstracts, now with a concrete uniform `pcOf` — the JMP branch of the
    global assembly's per-block obligation is discharged by this (via `wellsched_jmp_ok_continue`'s
    `hidx`). -/
theorem resolvedJump_pcOf (pre : List AsmInst) (lbl : String) (suf : List AsmInst)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel lbl ∧ inst ≠ AsmInst.AsmDataHeader lbl)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel lbl) :
    AssocList.lookup Nat Nat (asmResolve (pre ++ AsmInst.AsmLabel lbl :: suf)).2
      ((AssocList.lookup String Nat
        (computeLabelOffsets (pre ++ AsmInst.AsmLabel lbl :: suf)).2 lbl).getD 0)
      = some (pcOfLabel (pre ++ AsmInst.AsmLabel lbl :: suf) lbl) := by
  rw [pcOfLabel_of_decomp pre lbl suf hpre]
  exact resolvedJump_target_index pre lbl suf hsuf

/-- **`block_jmp_sim`'s target index is the concrete scheduled entry pc.** For the resolved program,
    the `idx` that `block_jmp_sim` lands the JMP at (`offsetToPc.lookup off = some idx`, where
    `off = offsets.lookup target`) is exactly `pcOfLabel prog target`. This is `wellsched_jmp_ok_continue`'s
    `hidx : idx = pcOf bb'.label` with the concrete `pcOf := pcOfLabel prog` — the last gap between
    `block_jmp_sim`'s output language and the well-scheduling pc obligation. -/
theorem resolvedJump_idx_eq_pcOfLabel (pre suf : List AsmInst) (target : String) (off idx : Nat)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel target ∧ inst ≠ AsmInst.AsmDataHeader target)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel target)
    (hoff_lk : AssocList.lookup String Nat
      (computeLabelOffsets (pre ++ AsmInst.AsmLabel target :: suf)).2 target = some off)
    (hidx_lk : AssocList.lookup Nat Nat
      (asmResolve (pre ++ AsmInst.AsmLabel target :: suf)).2 off = some idx) :
    idx = pcOfLabel (pre ++ AsmInst.AsmLabel target :: suf) target := by
  have hp := resolvedJump_pcOf pre target suf hsuf hpre
  rw [hoff_lk, Option.getD_some, hidx_lk] at hp
  exact Option.some.inj hp

/-- **`asmResolve` preserves `AsmLabel` positions.** `resolveInst` only rewrites label *pushes*
    (`AsmPushLabel`/`AsmPushOfst` → `AsmPush`), leaving `AsmLabel` markers in place, and `List.map`
    preserves positions — so a label's list index (`pcOfLabel`) is the same before and after resolution.
    This bridges the resolved program's `pcOfLabel` to the *unresolved* plan's offsets. -/
theorem pcOfLabel_asmResolve (X : List AsmInst) (lbl : String) :
    pcOfLabel (asmResolve X).1 lbl = pcOfLabel X lbl := by
  unfold pcOfLabel asmResolve
  rw [List.findIdx_map]
  congr 1
  funext i
  cases i with
  | AsmPushLabel l =>
    simp only [Function.comp_apply, resolveInst]
    cases AssocList.lookup String Nat (computeLabelOffsets X).2 l <;> rfl
  | AsmPushOfst l d =>
    simp only [Function.comp_apply, resolveInst]
    cases AssocList.lookup String Nat (computeLabelOffsets X).2 l <;> rfl
  | _ => rfl


/-- **Resolved JNZ taken branch lands at `pcOfLabel` (§5 JNZ pc side).** The JNZ analog of the JMP pc
    bridge: for the resolved program, a taken JUMPI to `ifNz` (`cond ≠ 0`) runs 2 asm steps to
    `pc = pcOfLabel prog ifNz`, consuming the condition. Composes `resolved_jumpi_taken_sim` with the
    concrete pc bridge `resolvedJump_pcOf` (the destination = the label's list index). -/
theorem resolved_jumpi_taken_pcOfLabel (pre suf : List AsmInst) (ifNz : String)
    (s : AsmState) (off : Nat) (cond : bytes32) (stk : List bytes32)
    (hsuf : ∀ inst ∈ suf, inst ≠ AsmInst.AsmLabel ifNz ∧ inst ≠ AsmInst.AsmDataHeader ifNz)
    (hpre : ∀ x ∈ pre, x ≠ AsmInst.AsmLabel ifNz)
    (hstack : s.stack = cond :: stk) (hcond : cond ≠ EvmYul.UInt256.ofNat 0)
    (hpc1 : s.pc < (pre ++ AsmInst.AsmLabel ifNz :: suf).length)
    (hpush : (pre ++ AsmInst.AsmLabel ifNz :: suf).get ⟨s.pc, hpc1⟩
      = resolveInst (computeLabelOffsets (pre ++ AsmInst.AsmLabel ifNz :: suf)).2
          (AsmInst.AsmPushLabel ifNz))
    (hoff_lk : AssocList.lookup String Nat
      (computeLabelOffsets (pre ++ AsmInst.AsmLabel ifNz :: suf)).2 ifNz = some off)
    (hoff : off < 2 ^ 256)
    (hpc2 : s.pc + 1 < (pre ++ AsmInst.AsmLabel ifNz :: suf).length)
    (hjumpi : (pre ++ AsmInst.AsmLabel ifNz :: suf).get ⟨s.pc + 1, hpc2⟩ = AsmInst.AsmOp "JUMPI") :
    runAsm 2 (asmResolve (pre ++ AsmInst.AsmLabel ifNz :: suf)).2
        (pre ++ AsmInst.AsmLabel ifNz :: suf) s
      = AsmResult.AsmOK
          { s with stack := stk,
                   pc := pcOfLabel (pre ++ AsmInst.AsmLabel ifNz :: suf) ifNz } := by
  have hidx_lk : AssocList.lookup Nat Nat (asmResolve (pre ++ AsmInst.AsmLabel ifNz :: suf)).2 off
      = some (pcOfLabel (pre ++ AsmInst.AsmLabel ifNz :: suf) ifNz) := by
    have h := resolvedJump_pcOf pre ifNz suf hsuf hpre
    rw [hoff_lk, Option.getD_some] at h; exact h
  exact resolved_jumpi_taken_sim hstack hcond hpc1 hpush hoff_lk hoff hpc2 hjumpi hidx_lk

/-- **A block's asm segment sits at the preceding length in the whole-function resolved program.** The
    AsmResolve layout for a general function: when the whole-function plan decomposes as
    `precedingOps ++ blockOps ++ followingOps` (the DFS concatenation), the resolved whole program has
    the block's resolved asm at pc `(executePlan precedingOps).length`. This is the position half of the
    layout discharge — the `hblock` that a per-block `hstep` needs, generalized from the concrete-case
    `hblock_twoBlock_next_discharged` to an arbitrary plan decomposition. -/
theorem asmBlockAt_of_plan_decomp (precedingOps blockOps followingOps : List StackOp) :
    asmBlockAt (asmResolve (executePlan (precedingOps ++ blockOps ++ followingOps))).1
      (executePlan precedingOps).length
      ((executePlan blockOps).map
        (resolveInst (computeLabelOffsets
          (executePlan (precedingOps ++ blockOps ++ followingOps))).2)) := by
  have he : executePlan (precedingOps ++ blockOps ++ followingOps)
      = executePlan precedingOps ++ executePlan blockOps ++ executePlan followingOps := by
    rw [executePlan_append, executePlan_append]
  rw [he]
  exact asmBlockAt_resolved_of_middle _ _ _

/-- **Label-push-free block segment sits *unchanged* at the preceding length.** For a terminal block
    whose asm has no label pushes (STOP/INVALID-terminated, no internal JMP), resolution is the
    identity, so its asm `executePlan blockOps` appears verbatim at pc `(executePlan precedingOps).length`
    in the whole-function resolved program. The `hblock`/`hget` for a terminal block, generalized to any
    plan decomposition — the STOP-block half of the layout discharge (a terminal block's whole-program
    halt sim then runs over this segment via `hasm_stop`-style lemmas). -/
theorem asmBlockAt_of_plan_decomp_no_label (precedingOps blockOps followingOps : List StackOp)
    (h1 : ∀ a ∈ executePlan blockOps, ∀ lbl, a ≠ AsmInst.AsmPushLabel lbl)
    (h2 : ∀ a ∈ executePlan blockOps, ∀ lbl d, a ≠ AsmInst.AsmPushOfst lbl d) :
    asmBlockAt (asmResolve (executePlan (precedingOps ++ blockOps ++ followingOps))).1
      (executePlan precedingOps).length (executePlan blockOps) := by
  have h := asmBlockAt_of_plan_decomp precedingOps blockOps followingOps
  rwa [map_resolveInst_eq_self _ (executePlan blockOps) h1 h2] at h

end EvmYul.Venom.Hol.Codegen

import EvmYul.Venom.Hol.Codegen.Dataflow
import EvmYul.Venom.Hol.Codegen.Liveness
import EvmYul.Venom.Hol.Codegen.DfgAnalysis

/-!
# Liveness analysis — the dataflow instance

Port of `vyper-hol main:venom/analysis/liveness/defs/livenessDefsScript.sml`:
liveness as the `Backward / list_union` instance of the generic dataflow framework.
`liveVarsAt` (the query the stack-plan generator needs at a `JMP` join) is now
available: `liveVarsAt = dfAt [] (livenessAnalyzeFuel …)`.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `list_union`: set union of two var lists (left-biased). -/
def listUnion (xs ys : List String) : List String :=
  xs ++ ys.filter (fun v => ¬ xs.contains v)

/-- `live_update`: backward transfer — drop the defs, add the uses. -/
def liveUpdate (defs uses live : List String) : List String :=
  let live' := live.filter (fun v => ¬ defs.contains v)
  live' ++ uses.filter (fun v => ¬ live'.contains v)

/-- `inst_defs`. -/
def instDefs (inst : Instruction) : List String := inst.outputs

/-- `inst_uses`. -/
def instUses (inst : Instruction) : List String := operandVars inst.operands

/-- `liveness_transfer` (the context — the block list — is unused by the transfer). -/
def livenessTransfer (_bbs : List BasicBlock) (inst : Instruction) (live : List String) : List String :=
  liveUpdate (instDefs inst) (instUses inst) live

/-- `liveness_edge_transfer`: live-in across a CFG edge (with phi substitution). -/
def livenessEdgeTransfer (bbs : List BasicBlock) (succLbl curLbl : String) (live : List String)
    : List String :=
  match bbs.find? (·.label == succLbl) with
  | none        => live
  | some succBb => inputVarsFrom curLbl succBb.instructions live

/-- `liveness_analyze_fuel`: backward set-union fixpoint. -/
def livenessAnalyzeFuel (fuel : Nat) (fn : IrFunction) : DfState (List String) :=
  dfAnalyzeFuel fuel Direction.Backward [] listUnion livenessTransfer livenessEdgeTransfer
    fn.blocks none fn

/-- `live_vars_at`: live vars before instruction `idx` in block `lbl`
    (`idx = #instructions` gives the block's live-out). -/
def liveVarsAt (st : DfState (List String)) (lbl : String) (idx : Nat) : List String :=
  dfAt [] st lbl idx

/-! ## Liveness transfer soundness

The backward transfer `liveUpdate defs uses live = (live \ defs) ∪ uses` is *sound*: every var used
by an instruction is live-in, and every var live afterwards and not redefined here stays live-in —
and it introduces nothing else. These are the per-instruction correctness facts behind the codegen's
`nextLiveness.contains v` reasoning (`liveVarsAt` reads the fixpoint the transfer defines). -/

/-- **`liveUpdate` adds every use.** Its output contains all `uses` — the soundness half (every use is
    live-in). -/
theorem liveUpdate_mem_of_use {defs uses live : List String} {v : String} (h : v ∈ uses) :
    v ∈ liveUpdate defs uses live := by
  unfold liveUpdate
  by_cases hv : v ∈ live.filter (fun w => ¬ defs.contains w = true)
  · exact List.mem_append_left _ hv
  · refine List.mem_append_right _ ?_
    rw [List.mem_filter]
    refine ⟨h, ?_⟩
    have hc : (live.filter (fun w => ¬ defs.contains w = true)).contains v = false := by
      rw [List.contains_eq_mem, decide_eq_false_iff_not]; exact hv
    rw [hc]; decide

/-- **`liveUpdate` keeps every live-through var.** A var live afterwards and not (re)defined here stays
    live-in — the framing half of liveness soundness. -/
theorem liveUpdate_mem_of_live {defs uses live : List String} {v : String}
    (hlive : v ∈ live) (hdef : ¬ defs.contains v = true) :
    v ∈ liveUpdate defs uses live := by
  unfold liveUpdate
  refine List.mem_append_left _ ?_
  rw [List.mem_filter]
  exact ⟨hlive, by simpa [List.contains_eq_mem] using hdef⟩

/-- **`liveUpdate` introduces nothing spurious.** Every var in the transfer output is either a use or
    a live-through (live afterwards and not defined here) — completeness of the transfer. -/
theorem liveUpdate_mem_elim {defs uses live : List String} {v : String}
    (h : v ∈ liveUpdate defs uses live) :
    v ∈ uses ∨ (v ∈ live ∧ ¬ defs.contains v = true) := by
  unfold liveUpdate at h
  rcases List.mem_append.1 h with h | h
  · rw [List.mem_filter] at h
    exact Or.inr ⟨h.1, by simpa using h.2⟩
  · rw [List.mem_filter] at h
    exact Or.inl h.1

/-- **Instruction-level liveness soundness: every operand var is live-in.** The var-operands used by
    `inst` all appear in the transferred live-in set. -/
theorem livenessTransfer_mem_of_use {bbs : List BasicBlock} {inst : Instruction} {live : List String}
    {v : String} (h : v ∈ operandVars inst.operands) :
    v ∈ livenessTransfer bbs inst live := by
  unfold livenessTransfer instUses
  exact liveUpdate_mem_of_use h

/-- **Instruction-level liveness framing: a live-through var not defined by `inst` stays live-in.** -/
theorem livenessTransfer_mem_of_live {bbs : List BasicBlock} {inst : Instruction} {live : List String}
    {v : String} (hlive : v ∈ live) (hdef : ¬ inst.outputs.contains v = true) :
    v ∈ livenessTransfer bbs inst live := by
  unfold livenessTransfer instDefs
  exact liveUpdate_mem_of_live hlive hdef

/-! ## Dataflow fixpoint correctness — the intra-block transfer equation

The liveness query `liveVarsAt = dfAt` reads the per-instruction map that `dfPopulateInst` fills by
folding `dfFoldBackward` across each block from its (converged) block-exit value. The load-bearing
fact is that this fold realises the transfer equation `dfAt (lbl, k) = livenessTransfer (instr k)
(dfAt (lbl, k+1))` **exactly, by construction** — independent of whether the boundary fixpoint has
converged (only the block-exit seed depends on that). Composed with `livenessTransfer_mem_of_use`,
this proves that every use is live-in at its own instruction in the stored map (`dfFoldBackward_use_mem`).
The remaining step to lift this to the global `liveVarsAt` query is bookkeeping about `dfPopulateInst`'s
per-block-key storage map (each block's `instMap` carries only its own `(lbl, ·)` keys). -/

section AL
variable {κ β : Type} [BEq κ] [LawfulBEq κ]

/-- The repo's `AssocList.lookup` agrees with core `List.lookup` (its recursive tail *is*
    `List.lookup`; the head comparison is symmetric under `LawfulBEq`). -/
theorem al_lookup_eq (l : AssocList κ β) (q : κ) :
    AssocList.lookup κ β l q = List.lookup q l := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    obtain ⟨k', v'⟩ := hd
    by_cases hc : (q == k') = true
    · have hc' : (k' == q) = true := by rw [beq_iff_eq] at hc ⊢; exact hc.symm
      simp only [AssocList.lookup, List.lookup, hc, hc', if_true]
    · rw [Bool.not_eq_true] at hc
      have hc' : (k' == q) = false := by
        rw [beq_eq_false_iff_ne] at hc ⊢; exact fun x => hc x.symm
      simp only [AssocList.lookup, List.lookup, hc, hc', Bool.false_eq_true, if_false]

/-- `List.lookup` of `q ≠ k` is unchanged by dropping key-`k` entries. -/
theorem list_lookup_filter_ne (l : List (κ × β)) (k q : κ) (h : q ≠ k) :
    List.lookup q (l.filter (fun e => e.1 != k)) = List.lookup q l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [List.filter_cons, List.lookup_cons]
    by_cases hk' : k' = k
    · subst hk'
      rw [show ((k', v').1 != k') = false by simp, if_neg (by simp)]
      rw [ih, show (q == k') = false by rw [beq_eq_false_iff_ne]; exact fun hc => h (hc.trans rfl)]
    · rw [show ((k', v').1 != k) = true by simp [hk'], if_pos (by trivial), List.lookup_cons, ih]

/-- `lookup` after `insert` at a different key. -/
theorem lookup_insert_ne (l : AssocList κ β) (k q : κ) (v : β) (h : q ≠ k) :
    AssocList.lookup κ β (AssocList.insert κ β l k v) q = AssocList.lookup κ β l q := by
  show AssocList.lookup κ β ((k, v) :: l.filter (fun e => e.1 != k)) q = _
  show (if (k == q) then some v else List.lookup q (l.filter (fun e => e.1 != k))) = _
  rw [show (k == q) = false by rw [beq_eq_false_iff_ne]; exact fun hc => h hc.symm, al_lookup_eq]
  exact list_lookup_filter_ne l k q h

/-- `lookup` after `insert` at the same key. -/
theorem lookup_insert_self (l : AssocList κ β) (k : κ) (v : β) :
    AssocList.lookup κ β (AssocList.insert κ β l k v) k = some v := by
  show (if (k == k) then _ else _) = _
  rw [show (k == k) = true by simp]; rfl

end AL

/-- **`dfFoldBackward` head lookup = returned value.** Looking up the fold's start key `(lbl, idx0)`
    yields the fold's returned accumulator (the segment's live-in). -/
theorem dfFoldBackward_lookup_head {α} (transfer : Instruction → α → α) (lbl : String)
    (instrs : List Instruction) (idx0 : Nat) (acc0 : α) (m0 : AssocList (String × Nat) α) :
    AssocList.lookup (String × Nat) α (dfFoldBackward transfer lbl instrs idx0 acc0 m0).2 (lbl, idx0)
      = (dfFoldBackward transfer lbl instrs idx0 acc0 m0).1 := by
  cases instrs with
  | nil => exact lookup_insert_self m0 (lbl, idx0) acc0
  | cons i rest => exact lookup_insert_self _ (lbl, idx0) _

/-- **Intra-block liveness soundness.** Every operand var used by the instruction at position `k`
    of a block is live-in at `(lbl, idx0 + k)` in the backward transfer fold — a use is live before
    the instruction that uses it, by construction of `dfFoldBackward` (fixpoint-independent). -/
theorem dfFoldBackward_use_mem {ctx : List BasicBlock} (lbl : String) (instrs : List Instruction)
    (idx0 : Nat) (acc0 : List String) (m0 : AssocList (String × Nat) (List String))
    (k : Nat) (hk : k < instrs.length) {v : String}
    (hv : v ∈ operandVars (instrs.get ⟨k, hk⟩).operands) :
    ∃ L, AssocList.lookup (String × Nat) (List String)
      (dfFoldBackward (livenessTransfer ctx) lbl instrs idx0 acc0 m0).2 (lbl, idx0 + k) = some L
      ∧ v ∈ L := by
  induction instrs generalizing idx0 k with
  | nil => exact absurd hk (by simp)
  | cons i rest ih =>
    cases k with
    | zero =>
      refine ⟨_, by rw [Nat.add_zero]; exact dfFoldBackward_lookup_head _ _ _ _ _ _, ?_⟩
      show v ∈ livenessTransfer ctx i _
      exact livenessTransfer_mem_of_use hv
    | succ k' =>
      have hk' : k' < rest.length := by simpa using hk
      have hkey : (lbl, idx0 + (k' + 1)) ≠ (lbl, idx0) := by
        intro he; exact absurd (Prod.ext_iff.1 he).2 (by omega)
      obtain ⟨L, hL, hvL⟩ := ih (idx0 + 1) k' hk' (by simpa using hv)
      refine ⟨L, ?_, hvL⟩
      show AssocList.lookup _ _
        (AssocList.insert _ _ (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).2
          (lbl, idx0) _) (lbl, idx0 + (k' + 1)) = some L
      rw [lookup_insert_ne _ (lbl, idx0) _ _ hkey, show idx0 + (k' + 1) = idx0 + 1 + k' from by omega]
      exact hL

/-- **`dfFoldBackward` intra-block transfer equation.** For an instruction at position `k` with a next
    position `k+1` still inside the block, the stored live-in at `(lbl, idx0+k)` is the transfer of the
    live-in at `(lbl, idx0+k+1)` — the fixpoint-independent transfer equation, made explicit at the
    lookup level. The framing companion to `dfFoldBackward_use_mem`'s use-soundness. -/
theorem dfFoldBackward_transfer_step {ctx : List BasicBlock} (lbl : String)
    (instrs : List Instruction) (idx0 : Nat) (acc0 : List String)
    (m0 : AssocList (String × Nat) (List String))
    (k : Nat) (hk1 : k + 1 < instrs.length) {Lnext : List String}
    (hnext : AssocList.lookup (String × Nat) (List String)
      (dfFoldBackward (livenessTransfer ctx) lbl instrs idx0 acc0 m0).2 (lbl, idx0 + (k + 1)) = some Lnext) :
    AssocList.lookup (String × Nat) (List String)
      (dfFoldBackward (livenessTransfer ctx) lbl instrs idx0 acc0 m0).2 (lbl, idx0 + k)
      = some (livenessTransfer ctx (instrs.get ⟨k, by omega⟩) Lnext) := by
  induction instrs generalizing idx0 k with
  | nil => exact absurd hk1 (by simp)
  | cons i rest ih =>
    have hkey : ∀ j : Nat, (lbl, idx0 + (j + 1)) ≠ (lbl, idx0) := fun j he =>
      absurd (Prod.ext_iff.1 he).2 (by omega)
    cases k with
    | zero =>
      have hheadfull : AssocList.lookup (String × Nat) (List String)
          (dfFoldBackward (livenessTransfer ctx) lbl (i :: rest) idx0 acc0 m0).2 (lbl, idx0)
          = some (livenessTransfer ctx i (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).1) := by
        show AssocList.lookup _ _ (AssocList.insert _ _ _ (lbl, idx0) _) (lbl, idx0) = _
        exact lookup_insert_self _ (lbl, idx0) _
      have hnext1 : (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).1 = Lnext := by
        have hl : AssocList.lookup (String × Nat) (List String)
            (dfFoldBackward (livenessTransfer ctx) lbl (i :: rest) idx0 acc0 m0).2 (lbl, idx0 + (0 + 1))
            = some (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).1 := by
          show AssocList.lookup _ _ (AssocList.insert _ _ _ (lbl, idx0) _) (lbl, idx0 + (0 + 1)) = _
          rw [lookup_insert_ne _ (lbl, idx0) _ _ (hkey 0),
              show idx0 + (0 + 1) = idx0 + 1 from by omega]
          exact dfFoldBackward_lookup_head _ _ _ _ _ _
        rw [hl] at hnext; exact Option.some.inj hnext
      rw [Nat.add_zero, hheadfull, hnext1]; rfl
    | succ k' =>
      have hk1' : k' + 1 < rest.length := by simpa using hk1
      have hnext' : AssocList.lookup (String × Nat) (List String)
          (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).2 (lbl, (idx0 + 1) + (k' + 1)) = some Lnext := by
        have hlk1 : AssocList.lookup (String × Nat) (List String)
            (dfFoldBackward (livenessTransfer ctx) lbl (i :: rest) idx0 acc0 m0).2 (lbl, idx0 + (k' + 1 + 1))
            = AssocList.lookup (String × Nat) (List String)
              (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).2 (lbl, (idx0 + 1) + (k' + 1)) := by
          show AssocList.lookup _ _ (AssocList.insert _ _ _ (lbl, idx0) _) (lbl, idx0 + (k' + 1 + 1)) = _
          rw [lookup_insert_ne _ (lbl, idx0) _ _ (hkey (k' + 1)),
              show idx0 + (k' + 1 + 1) = (idx0 + 1) + (k' + 1) from by omega]
        rw [← hlk1]; exact hnext
      have hstep := ih (idx0 + 1) k' hk1' hnext'
      have hlk : AssocList.lookup (String × Nat) (List String)
          (dfFoldBackward (livenessTransfer ctx) lbl (i :: rest) idx0 acc0 m0).2 (lbl, idx0 + (k' + 1))
          = AssocList.lookup (String × Nat) (List String)
            (dfFoldBackward (livenessTransfer ctx) lbl rest (idx0 + 1) acc0 m0).2 (lbl, (idx0 + 1) + k') := by
        show AssocList.lookup _ _ (AssocList.insert _ _ _ (lbl, idx0) _) (lbl, idx0 + (k' + 1)) = _
        rw [lookup_insert_ne _ (lbl, idx0) _ _ (hkey k'),
            show idx0 + (k' + 1) = (idx0 + 1) + k' from by omega]
      rw [hlk, hstep]; rfl

/-- **Liveness framing lifted through the block: a use propagates back to earlier positions.** A var
    used at position `k` is live-in at every earlier position `i ≤ k` at which — and after which up to
    `k` — it is not redefined. The framing (live-through) direction of intra-block liveness soundness,
    twin to `dfFoldBackward_use_mem`. Induction on the gap `k - i` via `dfFoldBackward_transfer_step`
    and `livenessTransfer_mem_of_live`. This is the mechanism behind the codegen's `nextLiveness.contains`
    for an operand reused *later* in the block (not just by the immediately-following instruction). -/
theorem dfFoldBackward_use_live_earlier {ctx : List BasicBlock} (lbl : String)
    (instrs : List Instruction) (idx0 : Nat) (acc0 : List String)
    (m0 : AssocList (String × Nat) (List String)) {v : String} :
    ∀ (gap i k : Nat) (hk : k < instrs.length), k = i + gap →
      v ∈ operandVars (instrs.get ⟨k, hk⟩).operands →
      (∀ m (hm : m < instrs.length), i ≤ m → m < k → v ∉ (instrs.get ⟨m, hm⟩).outputs) →
      ∃ L, AssocList.lookup (String × Nat) (List String)
        (dfFoldBackward (livenessTransfer ctx) lbl instrs idx0 acc0 m0).2 (lbl, idx0 + i) = some L ∧ v ∈ L := by
  intro gap
  induction gap with
  | zero =>
    intro i k hk hik hv _
    obtain ⟨L, hLk, hvL⟩ := dfFoldBackward_use_mem lbl instrs idx0 acc0 m0 k hk hv
    exact ⟨L, by rw [show idx0 + i = idx0 + k from by omega]; exact hLk, hvL⟩
  | succ g ih =>
    intro i k hk hik hv hnodef
    have hik1 : k = (i + 1) + g := by omega
    obtain ⟨L, hL, hvL⟩ := ih (i + 1) k hk hik1 hv
      (fun m hm h1 h2 => hnodef m hm (by omega) h2)
    have hk1 : i + 1 < instrs.length := by omega
    have hnodef_i : v ∉ (instrs.get ⟨i, by omega⟩).outputs := hnodef i (by omega) (le_refl _) (by omega)
    have hLeq : AssocList.lookup (String × Nat) (List String)
        (dfFoldBackward (livenessTransfer ctx) lbl instrs idx0 acc0 m0).2 (lbl, idx0 + (i + 1)) = some L := by
      rw [show idx0 + (i + 1) = idx0 + i + 1 from by omega] at hL
      rw [show idx0 + (i + 1) = idx0 + i + 1 from by omega]; exact hL
    have hstep := dfFoldBackward_transfer_step (ctx := ctx) lbl instrs idx0 acc0 m0 i hk1 hLeq
    exact ⟨_, hstep, livenessTransfer_mem_of_live hvL (by simpa [List.contains_eq_mem] using hnodef_i)⟩

/-- **`dfFoldBackward` touches only its own block's keys.** Looking up a *different* block's key
    `(lbl', j)` (`lbl' ≠ lbl`) in the fold's instruction map is the same as in the initial map — the
    fold only inserts `(lbl, ·)` keys. (Cross-block key disjointness for the `dfPopulateInst` lift to
    the global `liveVarsAt` query.) -/
theorem dfFoldBackward_lookup_diff_label {α} (transfer : Instruction → α → α) (lbl lbl' : String)
    (hne : lbl' ≠ lbl) (j : Nat) (instrs : List Instruction) (idx0 : Nat) (acc0 : α)
    (m0 : AssocList (String × Nat) α) :
    AssocList.lookup (String × Nat) α (dfFoldBackward transfer lbl instrs idx0 acc0 m0).2 (lbl', j)
      = AssocList.lookup (String × Nat) α m0 (lbl', j) := by
  have hkey : ∀ i : Nat, (lbl', j) ≠ (lbl, i) := fun i he => hne (Prod.ext_iff.1 he).1
  induction instrs generalizing idx0 with
  | nil =>
    show AssocList.lookup _ _ (AssocList.insert _ _ m0 (lbl, idx0) acc0) (lbl', j) = _
    exact lookup_insert_ne m0 (lbl, idx0) (lbl', j) acc0 (hkey idx0)
  | cons i rest ih =>
    show AssocList.lookup _ _
      (AssocList.insert _ _ (dfFoldBackward transfer lbl rest (idx0 + 1) acc0 m0).2 (lbl, idx0) _)
      (lbl', j) = _
    rw [lookup_insert_ne _ (lbl, idx0) (lbl', j) _ (hkey idx0)]
    exact ih (idx0 + 1)

section AL2
variable {κ : Type} [BEq κ] [LawfulBEq κ]

/-- lookup over an append: the left wins if it has the key, else the right. -/
theorem al_lookup_append {β} (A B : AssocList κ β) (q : κ) :
    AssocList.lookup κ β (A ++ B) q
      = match AssocList.lookup κ β A q with
        | some x => some x
        | none => AssocList.lookup κ β B q := by
  rw [al_lookup_eq, al_lookup_eq, al_lookup_eq]
  induction A with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [List.cons_append, List.lookup_cons]
    cases q == k' <;> simp [ih]

end AL2

/-- **Prepend-fold lookup (all-miss).** A `dfPopulateInst`-style fold that prepends each block's
    instruction map leaves the lookup at `q` unchanged when no block's map carries `q`. -/
theorem foldl_prepend_lookup_none {β} {g : String → AssocList (String × Nat) β} {q : String × Nat}
    (lbls : List String) :
    ∀ (init : AssocList (String × Nat) β), (∀ l ∈ lbls, AssocList.lookup _ _ (g l) q = none) →
      AssocList.lookup _ _ (lbls.foldl (fun acc l => g l ++ acc) init) q
        = AssocList.lookup _ _ init q := by
  induction lbls with
  | nil => intro init _; rfl
  | cons l ls ih =>
    intro init h
    rw [List.foldl_cons, ih (g l ++ init) (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
        al_lookup_append, h l List.mem_cons_self]

/-- **Prepend-fold lookup (unique hit).** With distinct block labels (`Nodup`), the fold finds the
    one block `lbl0` carrying `q`. This is the `dfPopulateInst` concatenation resolving to the target
    block's `dfFoldBackward` map — the last step to lift `dfFoldBackward_use_mem` to `liveVarsAt`. -/
theorem foldl_prepend_lookup_some {β} {g : String → AssocList (String × Nat) β} {q : String × Nat}
    {lbl0 : String} {L : β} :
    ∀ (lbls : List String), lbls.Nodup → ∀ (init : AssocList (String × Nat) β), lbl0 ∈ lbls →
      (∀ l ∈ lbls, l ≠ lbl0 → AssocList.lookup _ _ (g l) q = none) →
      AssocList.lookup _ _ (g lbl0) q = some L →
      AssocList.lookup _ _ (lbls.foldl (fun acc l => g l ++ acc) init) q = some L := by
  intro lbls
  induction lbls with
  | nil => intro _ _ hin _ _; exact absurd hin (by simp)
  | cons l ls ih =>
    intro hnd init hin hdisj hsome
    rw [List.foldl_cons, List.nodup_cons] at *
    by_cases hll : l = lbl0
    · subst hll
      have hnone : ∀ l' ∈ ls, AssocList.lookup _ _ (g l') q = none := fun l' hl' =>
        hdisj l' (List.mem_cons_of_mem _ hl') (fun he => hnd.1 (he ▸ hl'))
      rw [foldl_prepend_lookup_none ls (g l ++ init) hnone, al_lookup_append, hsome]
    · have hin' : lbl0 ∈ ls := (List.mem_cons.1 hin).resolve_left (fun he => hll he.symm)
      exact ih hnd.2 (g l ++ init) hin'
        (fun l' hl' hne => hdisj l' (List.mem_cons_of_mem _ hl') hne) hsome

/-- **Liveness fixpoint correctness: every use is live-in at its instruction.** For a function with
    distinct block labels, a var used by the instruction at index `idx` of block `lbl0` is in
    `liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 idx` — the global query the codegen reads. This
    lifts the intra-block transfer equation (`dfFoldBackward_use_mem`) through the `dfPopulateInst`
    storage map (`dfPopulateInst_inst_eq` + `foldl_prepend_lookup_some`, with cross-block key
    disjointness `dfFoldBackward_lookup_diff_label`). Fixpoint-convergence-independent: a use is live
    before its instruction by construction of the backward transfer, whatever the block-exit seed. -/
theorem livenessAnalyzeFuel_use_live {fuel : Nat} {fn : IrFunction} {lbl0 : String}
    {bb : BasicBlock} {idx : Nat} {v : String}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hidx : idx < bb.instructions.length)
    (hv : v ∈ operandVars (bb.instructions.get ⟨idx, hidx⟩).operands) :
    v ∈ liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 idx := by
  set boundaryResult := (wlIterateFuel fuel
    (fun lbl old new => dfBoundary [] new lbl != dfBoundary [] old lbl)
    (fun lbl st => dfProcessBlock Direction.Backward [] listUnion livenessTransfer livenessEdgeTransfer
      fn.blocks none (cfgAnalyze fn) fn.blocks lbl st)
    (cfgAnalyze fn).predsOf (cfgAnalyze fn).dfsPost (initDfState [] (fn.blocks.map (·.label)))).2
    with hbr
  set g : String → AssocList (String × Nat) (List String) := fun lbl =>
    (dfFoldBlock Direction.Backward (livenessTransfer fn.blocks) lbl
      (match findBlock lbl fn.blocks with | none => [] | some bb => bb.instructions)
      (dfJoinedVal Direction.Backward [] listUnion livenessEdgeTransfer fn.blocks none
        (cfgAnalyze fn) boundaryResult lbl)).2 with hg
  obtain ⟨L, hL, hvL⟩ := dfFoldBackward_use_mem (ctx := fn.blocks) lbl0 bb.instructions 0
    (dfJoinedVal Direction.Backward [] listUnion livenessEdgeTransfer fn.blocks none
      (cfgAnalyze fn) boundaryResult lbl0) [] idx hidx hv
  have hsome : AssocList.lookup _ _ (g lbl0) (lbl0, idx) = some L := by
    rw [hg]; simp only [hfind]
    show AssocList.lookup _ _ (dfFoldBackward (livenessTransfer fn.blocks) lbl0 bb.instructions 0 _ []).2
      (lbl0, idx) = some L
    rw [Nat.zero_add] at hL; exact hL
  have hdisj : ∀ l ∈ fn.blocks.map (·.label), l ≠ lbl0 →
      AssocList.lookup _ _ (g l) (lbl0, idx) = none := by
    intro l _ hne
    rw [hg]
    show AssocList.lookup _ _ (dfFoldBackward (livenessTransfer fn.blocks) l _ 0 _ []).2 (lbl0, idx) = none
    rw [dfFoldBackward_lookup_diff_label (livenessTransfer fn.blocks) l lbl0 (Ne.symm hne) idx]
    rfl
  have hinst : (livenessAnalyzeFuel fuel fn).inst
      = (fn.blocks.map (·.label)).foldl (fun acc l => g l ++ acc) boundaryResult.inst := by
    unfold livenessAnalyzeFuel dfAnalyzeFuel
    rw [dfPopulateInst_inst_eq]
    rfl
  show v ∈ (AssocList.lookup _ _ (livenessAnalyzeFuel fuel fn).inst (lbl0, idx)).getD []
  rw [hinst, foldl_prepend_lookup_some (g := g) (fn.blocks.map (·.label)) hnd _ hlbl hdisj hsome]
  simpa using hvL

/-- **Global liveness framing: a use is live at earlier positions where not redefined.** For a WF
    function (distinct labels), a var used at position `idx` of block `lbl0` is in
    `liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 i` for every earlier `i ≤ idx` at which — and after
    which up to `idx` — it is not redefined. Lifts `dfFoldBackward_use_live_earlier` through the
    `dfPopulateInst` storage map exactly as `livenessAnalyzeFuel_use_live` lifts the use case. This is
    the global query the codegen reads to justify `nextLiveness.contains x` for an operand reused later
    in the block: with `i := k+1`, the operand of the instruction at `k` is in the live-out
    (`nextLiveness = liveVarsAt lbl (k+1)`) whenever it is used again at some later position. -/
theorem livenessAnalyzeFuel_live_earlier {fuel : Nat} {fn : IrFunction} {lbl0 : String}
    {bb : BasicBlock} {i idx : Nat} {v : String}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hidx : idx < bb.instructions.length)
    (hile : i ≤ idx)
    (hv : v ∈ operandVars (bb.instructions.get ⟨idx, hidx⟩).operands)
    (hnodef : ∀ m (hm : m < bb.instructions.length), i ≤ m → m < idx →
        v ∉ (bb.instructions.get ⟨m, hm⟩).outputs) :
    v ∈ liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 i := by
  set boundaryResult := (wlIterateFuel fuel
    (fun lbl old new => dfBoundary [] new lbl != dfBoundary [] old lbl)
    (fun lbl st => dfProcessBlock Direction.Backward [] listUnion livenessTransfer livenessEdgeTransfer
      fn.blocks none (cfgAnalyze fn) fn.blocks lbl st)
    (cfgAnalyze fn).predsOf (cfgAnalyze fn).dfsPost (initDfState [] (fn.blocks.map (·.label)))).2
    with hbr
  set g : String → AssocList (String × Nat) (List String) := fun lbl =>
    (dfFoldBlock Direction.Backward (livenessTransfer fn.blocks) lbl
      (match findBlock lbl fn.blocks with | none => [] | some bb => bb.instructions)
      (dfJoinedVal Direction.Backward [] listUnion livenessEdgeTransfer fn.blocks none
        (cfgAnalyze fn) boundaryResult lbl)).2 with hg
  obtain ⟨L, hL, hvL⟩ := dfFoldBackward_use_live_earlier (ctx := fn.blocks) lbl0 bb.instructions 0
    (dfJoinedVal Direction.Backward [] listUnion livenessEdgeTransfer fn.blocks none
      (cfgAnalyze fn) boundaryResult lbl0) [] (idx - i) i idx hidx (by omega) hv hnodef
  have hsome : AssocList.lookup _ _ (g lbl0) (lbl0, i) = some L := by
    rw [hg]; simp only [hfind]
    show AssocList.lookup _ _ (dfFoldBackward (livenessTransfer fn.blocks) lbl0 bb.instructions 0 _ []).2
      (lbl0, i) = some L
    rw [Nat.zero_add] at hL; exact hL
  have hdisj : ∀ l ∈ fn.blocks.map (·.label), l ≠ lbl0 →
      AssocList.lookup _ _ (g l) (lbl0, i) = none := by
    intro l _ hne
    rw [hg]
    show AssocList.lookup _ _ (dfFoldBackward (livenessTransfer fn.blocks) l _ 0 _ []).2 (lbl0, i) = none
    rw [dfFoldBackward_lookup_diff_label (livenessTransfer fn.blocks) l lbl0 (Ne.symm hne) i]
    rfl
  have hinst : (livenessAnalyzeFuel fuel fn).inst
      = (fn.blocks.map (·.label)).foldl (fun acc l => g l ++ acc) boundaryResult.inst := by
    unfold livenessAnalyzeFuel dfAnalyzeFuel
    rw [dfPopulateInst_inst_eq]
    rfl
  show v ∈ (AssocList.lookup _ _ (livenessAnalyzeFuel fuel fn).inst (lbl0, i)).getD []
  rw [hinst, foldl_prepend_lookup_some (g := g) (fn.blocks.map (·.label)) hnd _ hlbl hdisj hsome]
  simpa using hvL

/-- **`.contains` form of `livenessAnalyzeFuel_use_live`** — the exact shape a `RegularStepG` classifier
    consumes (`nextLiveness.contains v = true`). -/
theorem liveVarsAt_contains_of_use {fuel fn lbl0 bb idx v}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hidx : idx < bb.instructions.length)
    (hv : v ∈ operandVars (bb.instructions.get ⟨idx, hidx⟩).operands) :
    (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 idx).contains v = true := by
  rw [List.contains_eq_mem]
  simpa using livenessAnalyzeFuel_use_live hnd hfind hlbl hidx hv

/-- **`.contains` form of `livenessAnalyzeFuel_live_earlier`** — directly discharges a classifier's
    `nextLiveness.contains x = true` for an operand reused later in the block. -/
theorem liveVarsAt_contains_of_use_later {fuel fn lbl0 bb} {i idx v}
    (hnd : (fn.blocks.map (·.label)).Nodup)
    (hfind : findBlock lbl0 fn.blocks = some bb)
    (hlbl : lbl0 ∈ fn.blocks.map (·.label))
    (hidx : idx < bb.instructions.length)
    (hile : i ≤ idx)
    (hv : v ∈ operandVars (bb.instructions.get ⟨idx, hidx⟩).operands)
    (hnodef : ∀ m (hm : m < bb.instructions.length), i ≤ m → m < idx →
        v ∉ (bb.instructions.get ⟨m, hm⟩).outputs) :
    (liveVarsAt (livenessAnalyzeFuel fuel fn) lbl0 i).contains v = true := by
  rw [List.contains_eq_mem]
  simpa using livenessAnalyzeFuel_live_earlier hnd hfind hlbl hidx hile hv hnodef

end EvmYul.Venom.Hol.Codegen

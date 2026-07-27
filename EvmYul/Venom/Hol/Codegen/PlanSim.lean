/-
Plan Operation Simulation Lemmas

Port of vyper-hol/venom/codegen/proofs/{doSwapSim,spillSim,reorderSim,...}Script.sml

Key theorems:
  - doSwap_sim (fully proven, incl. the dist>16 big-swap), doSpillAt_sim,
    doRestore_sim, doSpillTos_sim — all proven
  - foldl_ops_sim — the fold-composition harness
  - reorderPlan_sim, popmanyPlan_sim — proven via the harness (residual: the
    per-step simulations as hypotheses; see the allocator-generalisation note)
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.PlanTypes
import EvmYul.Venom.Hol.Codegen.PlanOps
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.Hol.Codegen.AsmSem
import EvmYul.Venom.Hol.Codegen.CodegenRel
import EvmYul.Venom.Hol.Codegen.AsmSpillMem
import Mathlib.Tactic.IntervalCases
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen

namespace EvmYul.Venom.Hol.Codegen

/- The whole-function byte-offset → list-index map under which `JUMP`/`JUMPI` resolve. The
   swap/spill/fold sims below never inspect it (their `asmStep`s are PUSH/MSTORE/MLOAD/SWAP, which
   ignore `offsetToPc`), so it threads through generically; auto-included in every lemma that
   references it without binding its own. -/
variable {offsetToPc : AssocList Nat Nat}

/-! ## `LawfulBEq` for `Operand` (and `UInt256`)

`Operand` derives `BEq` + `DecidableEq` but no lawfulness, which the `AssocList`
(`spilled` map) reasoning in the restore simulation needs. The derived `BEq`
reduces structurally to the field comparisons, so lawfulness lifts from the
fields (`UInt256` via its `Fin`, `String` standard). -/

instance instReflBEqUInt256 : ReflBEq UInt256 where
  rfl {a} := by cases a with | mk v => exact beq_self_eq_true v
instance instLawfulBEqUInt256 : LawfulBEq UInt256 where
  eq_of_beq {a b} h := by cases a; cases b; exact congrArg UInt256.mk (eq_of_beq h)

instance instReflBEqOperand : ReflBEq Operand where
  rfl {a} := by cases a with
    | Lit v => exact beq_self_eq_true v
    | Var s => exact beq_self_eq_true s
    | Label s => exact beq_self_eq_true s
instance instLawfulBEqOperand : LawfulBEq Operand where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      first | exact congrArg _ (eq_of_beq h) | exact Bool.noConfusion h

/-! ## `aremove` lookup facts (the `planSpillRel` side of restore)

`AssocList.lookup` does one step of its own dispatch then delegates to stdlib
`List.lookup`, so the `aremove`/`filter` reasoning is done over `List.lookup`
(which recurses) and bridged back. -/

/-- `AssocList.lookup` agrees with stdlib `List.lookup` (head `==` symmetry). -/
theorem assocLookup_eq_listLookup {α β} [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) :
    AssocList.lookup α β l k = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons hd tl _ =>
    obtain ⟨k', v'⟩ := hd
    by_cases h : k' = k
    · subst h; simp [AssocList.lookup, List.lookup]
    · simp [AssocList.lookup, List.lookup, beq_eq_false_iff_ne.mpr h,
        beq_eq_false_iff_ne.mpr (Ne.symm h)]

/-- Removing key `k` (filtering it out) makes `List.lookup k` return `none`. -/
theorem listLookup_filter_self_none {α β} [BEq α] [LawfulBEq α] (m : List (α × β)) (k : α) :
    List.lookup k (m.filter (fun x => x.1 != k)) = none := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [List.filter_cons]
    by_cases hk : k' = k
    · subst hk; simp only [bne_self_eq_false, Bool.false_eq_true, if_false]; exact ih
    · have hne : (k' != k) = true := by simp [bne_iff_ne, hk]
      simp only [hne, if_true, List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hk),
        Bool.false_eq_true, if_false]
      exact ih

/-- Removing key `k` preserves a `some`-lookup at any other key. -/
theorem listLookup_filter_some {α β} [BEq α] [LawfulBEq α] (m : List (α × β)) (k o : α) (v : β) :
    List.lookup o (m.filter (fun x => x.1 != k)) = some v → List.lookup o m = some v := by
  induction m with
  | nil => intro h; simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    intro h
    rw [List.filter_cons] at h
    by_cases hk : k' = k
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at h
      simp only [List.lookup]
      by_cases hko : o = k'
      · subst hko; rw [listLookup_filter_self_none] at h; exact absurd h (by simp)
      · simp only [beq_eq_false_iff_ne.mpr hko, Bool.false_eq_true, if_false]; exact ih h
    · have hne : (k' != k) = true := by simp [bne_iff_ne, hk]
      simp only [hne, if_true, List.lookup] at h ⊢
      by_cases hko : o = k'
      · subst hko; simp only [beq_self_eq_true, if_true] at h ⊢; exact h
      · simp only [beq_eq_false_iff_ne.mpr hko, Bool.false_eq_true, if_false] at h ⊢; exact ih h

/-- `aremove` analogue of `listLookup_filter_some`, in `AssocList.lookup` form. -/
theorem aremove_lookup_some {β} (m : AssocList Operand β) (k o : Operand) (v : β)
    (h : AssocList.lookup Operand β (aremove m k) o = some v) :
    AssocList.lookup Operand β m o = some v := by
  rw [assocLookup_eq_listLookup] at h ⊢
  exact listLookup_filter_some m k o v h

/-- Inserting `(k, val)` makes `k` look up to `val`. -/
theorem ainsert'_lookup_self {β} (m : AssocList Operand β) (k : Operand) (val : β) :
    AssocList.lookup Operand β (ainsert' m k val) k = some val := by
  simp [ainsert', AssocList.insert, AssocList.lookup]

/-- Looking up a key other than the inserted one sees through to the `aremove`d map. -/
theorem ainsert'_lookup_other {β} (m : AssocList Operand β) (k o : Operand) (val : β) (h : o ≠ k) :
    AssocList.lookup Operand β (ainsert' m k val) o
      = AssocList.lookup Operand β (aremove m k) o := by
  rw [assocLookup_eq_listLookup (aremove m k) o]
  simp only [ainsert', AssocList.insert, AssocList.lookup]
  rw [if_neg (by rw [beq_eq_false_iff_ne.mpr (Ne.symm h)]; simp)]
  rfl

/-! ## Phase 2 — per-op asm step lemmas (mechanical building blocks)

These mirror HOL `stackOpAsmSimScript` / `spillSimScript`:
`asm_step_X_ok` (single step → `AsmOK` + state shape) composed via
`asm_steps_all_ok` into `runAsm n = AsmOK`.

Lean's `asmSwap`/`asmDup`/`asmPop` are already parameterized (no 16-way
case split needed, unlike HOL). -/

/-- Bridge: `List.get!` (deprecated) to `get` with a Fin proof.
    Needed because `asmSwap` uses `get` while `planStackRel_swap` uses `get!`. -/
lemma List_get!_eq_get {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! = l.get ⟨i, h⟩ := by
  rw [getElem!_eq_getD, getD_eq_getElem?_getD, List.getElem?_eq_getElem (h := h)]; rfl

/-- `l[i]? = some (l[i]!)` when `i` is in range. -/
lemma getElem?_eq_some_get! {α : Type} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l[i]? = some (l[i]!) := by
  rw [List.getElem?_eq_getElem hi, List_get!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]

/-- TOS read agreement: `asmSwap` reads its top via `head?.getD`, the plan side
    via `get!`/`getElem? 0`. On a non-empty stack they coincide. Shared by both
    swap simulations (`doSwap_sim`, the leading swap in `doSpillAt_sim`). -/
lemma head?_getD_eq_zero (l : List bytes32) (h : l ≠ []) :
    l.head?.getD (UInt256.ofNat 0) = l[0]?.getD default := by
  cases hl : l with
  | nil => exact absurd hl h
  | cons a t => simp

/-- `runAsm (n+1) s1 = runAsm n s2` when the first step yields `AsmOK s2` and
    `s1.pc` is in range (mirrors HOL `asm_steps_suc_ok`). -/
theorem runAsm_succ_ok {offsetToPc prog s1 s2 n}
    (hpc : s1.pc < prog.length)
    (hstep : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2) :
    runAsm (n + 1) offsetToPc prog s1 = runAsm n offsetToPc prog s2 := by
  simp only [show (n + 1) = Nat.succ n from rfl, runAsm, if_pos hpc, hstep]

-- Single-step `asmStep` on `AsmOp (swapName n)` (n ∈ [1,16]) dispatches to
-- `asmSwap n s` (mirrors HOL `asm_step_swap_ok`). `asmSwap` internally
-- produces `AsmOK ({asmNext s with stack := swapped})` when `0 < n` and
-- `n < s.stack.length`. Proved by `unfold + dif_pos + rfl`: kernel reduction
-- of the match is lazy (unlike `simp`, it does not whnf all branch bodies),
-- so for a concrete `swapName n` string it walks the dispatch cheaply.
theorem asmStep_swap_ok {offsetToPc prog s n}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp (swapName n))
    (hn0 : 0 < n) (hn16 : n ≤ 16) (hnlen : n < s.stack.length) :
    asmStep offsetToPc prog s = asmSwap n s := by
  interval_cases n <;> unfold asmStep <;> rw [dif_pos hpc, hprog] <;> rfl

/-- Single-step `asmStep` on `AsmPush bytes` dispatches to `asmPushVal v`, where
    `v` is the 32-byte right-zero-padded word (mirrors HOL `asm_step_push_ok`).
    `asmPushVal` never errors, so this is the full step. -/
theorem asmStep_push_ok {offsetToPc prog s bytes}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmPush bytes) :
    asmStep offsetToPc prog s =
      asmPushVal (wordOfBytes (List.toByteArray (List.replicate (32 - bytes.length) (0 : byte) ++ bytes))) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]

/-- Single-step `asmStep` on `AsmOp "MSTORE"` dispatches to `asmMstore`
    (mirrors HOL `asm_step_mstore_ok`). -/
theorem asmStep_mstore_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MSTORE") :
    asmStep offsetToPc prog s = asmMstore s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-- Single-step `asmStep` on `AsmOp "MLOAD"` dispatches to `asmMload`
    (mirrors HOL `asm_step_mload_ok`). -/
theorem asmStep_mload_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MLOAD") :
    asmStep offsetToPc prog s = asmMload s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

/-! ## Big-swap (`dist > 16`) stack-effect spec

For `dist > 16` EVM cannot `SWAP` directly, so `doSwap` spills the top
`dist+1` items to fresh slots and restores them in the permuted order
`[dist, 1, …, dist-1, 0]` (swap first/last of the chunk, keep the middle).
The lemmas below prove — by *pure list/arithmetic reasoning, no `asmStep`
involved* — the two "spec halves" of the big-swap obligation, both sorry-free:

  - `bigSwap_stack_spec`: the resulting plan stack equals `stackSwap dist`, i.e.
    the codegen plan computes the intended permutation.
  - `spillFold_chars`: with `freeSlots = []` (the big-swap precondition) the
    allocator hands out `nextOffset + 32·k`, so the temp spill slots are
    distinct/aligned/in-region by construction — the cross-slot disjointness
    becomes arithmetic, not a bespoke invariant.

What remains for the full `doSwap_sim` big-swap is the `venomAsmRel`-preserving
*asm-execution* of the spill/restore fold: composing the chunk `PUSH;MSTORE`
then chunk `PUSH;MLOAD` steps (cf. the proven `doSpillTos_sim`/`doRestore_sim`
single-op lemmas, but iterated and without plan-map updates), and discharging
`memoryRel`/`planSpillRel` against the above two facts. That is voluminous
asm bookkeeping rather than further conceptual difficulty. -/

/-- `topN c s` is the last `c` elements of `s`. -/
theorem topN_eq_drop (c : Nat) (s : List Operand) :
    topN c s = s.drop (s.length - c) := by
  unfold topN
  rw [List.reverse_take, List.reverse_reverse, List.length_reverse]

/-- length of `topN` (for `c ≤ s.length`). -/
theorem topN_length (c : Nat) (s : List Operand) (h : c ≤ s.length) :
    (topN c s).length = c := by
  rw [topN_eq_drop c s, List.length_drop]; omega

/-- The `desired` permutation index list `[d] ++ [1..d-1] ++ [0]` reads as
    `d` at position 0, `0` at position `d`, and the identity in between. -/
theorem desired_get! (d k : Nat) (h0 : 0 < d) (hk : k < d + 1) :
    ([d] ++ (List.range (d - 1)).map (· + 1) ++ [0])[k]!
      = (if k = 0 then d else if k = d then 0 else k) := by
  rw [List_get!_eq_getElem?_getD]
  have hlenA : ([d] ++ (List.range (d - 1)).map (· + 1)).length = d := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
  rcases Nat.lt_or_ge k d with hkd | hkd
  · rw [List.getElem?_append_left (by rw [hlenA]; exact hkd)]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [List.getElem?_append_left (by simp), List.getElem?_cons_zero]; simp
    · rw [List.getElem?_append_right (l₁ := [d]) (by simp only [List.length_singleton]; omega)]
      simp only [List.length_singleton]
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [if_neg (by omega), if_neg (by omega)]; omega
  · obtain rfl : k = d := by omega
    rw [List.getElem?_append_right (le_of_eq hlenA), hlenA, Nat.sub_self,
        List.getElem?_cons_zero]
    simp [show k ≠ 0 from by omega]

/-- The `desired`-indexed list reads as `some` of its value below its length. -/
theorem desired_getElem? (d m : Nat) (h0 : 0 < d) (hm : m < d + 1) :
    ([d] ++ (List.range (d - 1)).map (· + 1) ++ [0])[m]?
      = some (if m = 0 then d else if m = d then 0 else m) := by
  have hml : m < ([d] ++ (List.range (d - 1)).map (· + 1) ++ [0]).length := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
  rw [List.getElem?_eq_getElem hml, ← desired_get! d m h0 hm, List_get!_eq_getElem?_getD,
      List.getElem?_eq_getElem hml, Option.getD_some]

/-- **Big-swap plan correctness (spec half).** The op list `doSwap` emits for
    `dist > 16` produces a plan stack equal to `stackSwap dist` — the intended
    effect. Pure list reasoning; no memory/allocator involved. -/
theorem bigSwap_stack_spec (s : List Operand) (d : Nat) (h0 : 0 < d) (hlen : d < s.length) :
    s.take (s.length - (d + 1)) ++
      (([d] ++ (List.range (d - 1)).map (· + 1) ++ [0]).map (fun j => (topN (d + 1) s)[j]!))
    = stackSwap d s := by
  have hcle : d + 1 ≤ s.length := hlen
  have hbaselen : (s.take (s.length - (d + 1))).length = s.length - (d + 1) := by
    rw [List.length_take]; omega
  have hitemget : ∀ j, (topN (d + 1) s)[j]! = s[s.length - (d + 1) + j]! := by
    intro j
    rw [topN_eq_drop]
    simp only [List_get!_eq_getElem?_getD, List.getElem?_drop]
  have hsget : ∀ i, i < s.length → s[i]? = some (s[i]!) := fun i hi => getElem?_eq_some_get! s i hi
  have hbleq : s.length - 1 - d = s.length - (d + 1) := by omega
  apply List.ext_getElem?
  intro i
  simp only [stackSwap]
  rw [hbleq]
  by_cases hib : i < s.length - (d + 1)
  · -- baseStack region: both sides are `s[i]?`
    rw [List.getElem?_append_left (by rw [hbaselen]; exact hib), List.getElem?_take, if_pos hib,
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · push Not at hib
    rw [List.getElem?_append_right (by rw [hbaselen]; exact hib), hbaselen, List.getElem?_map]
    by_cases hi_in : i - (s.length - (d + 1)) < d + 1
    · rw [desired_getElem? d _ h0 hi_in, Option.map_some]
      rcases Nat.eq_zero_or_pos (i - (s.length - (d + 1))) with hm0 | hmpos
      · -- i = baseStack length: top of chunk, value `s[len-1]!`
        rw [if_pos hm0, hitemget]
        have hival : i = s.length - (d + 1) := by omega
        subst hival
        rw [List.getElem?_set_self (by rw [List.length_set]; omega),
            show s.length - (d + 1) + d = s.length - 1 from by omega]
      · by_cases hmd : i - (s.length - (d + 1)) = d
        · -- i = len-1: bottom of chunk, value `s[len-1-d]!`
          rw [if_neg (by omega), if_pos hmd, hitemget]
          have hival : i = s.length - 1 := by omega
          subst hival
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
              show s.length - (d + 1) + 0 = s.length - (d + 1) from by omega]
        · -- middle: identity, `s[i]!`
          rw [if_neg (by omega), if_neg hmd, hitemget,
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              hsget i (by omega),
              show s.length - (d + 1) + (i - (s.length - (d + 1))) = i from by omega]
    · -- past the end: both sides `none`
      push Not at hi_in
      rw [List.getElem?_eq_none (by
            simp only [List.length_append, List.length_map, List.length_range,
              List.length_singleton]; omega),
          Option.map_none,
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_eq_none (by omega)]

/-- `range (n+1)` mapped through an affine-in-`k` function peels off its head and
    re-bases the step. -/
theorem range_succ_map_affine {α} (f : Nat → α) (c n : Nat) :
    (List.range (n + 1)).map (fun k => f (c + 32 * k))
    = f c :: (List.range n).map (fun k => f ((c + 32) + 32 * k)) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  cases i with
  | zero =>
    rw [List.getElem?_range (by omega)]; simp
  | succ j =>
    rw [List.getElem?_cons_succ, List.getElem?_map]
    by_cases hj : j < n
    · rw [List.getElem?_range (by omega), List.getElem?_range hj, Option.map_some, Option.map_some]
      congr 2; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]; simp

/-- Nat specialization of `range_succ_map_affine`. -/
theorem range_succ_map_nat (c n : Nat) :
    (List.range (n + 1)).map (fun k => c + 32 * k)
    = c :: (List.range n).map (fun k => (c + 32) + 32 * k) := by
  simpa using range_succ_map_affine id c n

/-- **Big-swap allocator-fold characterization.** With no free slots (the
    big-swap precondition `ps.alloc.freeSlots = []`), folding the spill step over
    a length-`n` list hands out the offsets `nextOffset, nextOffset+32, …`,
    bumps `nextOffset` by `32·n`, and keeps `freeSlots` empty. The offsets are
    therefore distinct and 32-aligned by construction — so the cross-slot
    disjointness the memory fold needs reduces to pure arithmetic, not a
    bespoke invariant. The `foldl` lambda is written exactly as `doSwap` writes
    it, so this lemma rewrites the real fold. -/
theorem spillFold_chars (L : List Operand) (ops0 : List StackOp) (offs0 : List Nat)
    (a0 : SpillAlloc) (hfree : a0.freeSlots = []) :
    L.foldl (fun (ops, offs, al) (_item : Operand) =>
        let (off, al') := allocSpillSlot al
        (ops ++ [StackOp.SOSpill off], offs ++ [off], al'))
      (ops0, offs0, a0)
    = (ops0 ++ (List.range L.length).map (fun k => StackOp.SOSpill (a0.nextOffset + 32 * k)),
       offs0 ++ (List.range L.length).map (fun k => a0.nextOffset + 32 * k),
       { a0 with nextOffset := a0.nextOffset + 32 * L.length }) := by
  induction L generalizing ops0 offs0 a0 with
  | nil => simp
  | cons x xs ih =>
    have hstep : allocSpillSlot a0 = (a0.nextOffset, { a0 with nextOffset := a0.nextOffset + 32 }) := by
      simp only [allocSpillSlot, hfree]
    rw [List.foldl_cons]
    simp only [hstep]
    rw [ih (ops0 ++ [StackOp.SOSpill a0.nextOffset]) (offs0 ++ [a0.nextOffset])
        { a0 with nextOffset := a0.nextOffset + 32 } hfree]
    simp only [List.length_cons, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [range_succ_map_affine StackOp.SOSpill, List.append_assoc, List.singleton_append]
    · rw [range_succ_map_nat, List.append_assoc, List.singleton_append]
    · congr 1; omega

/-- Running `n` then `m` steps composes (when the first run succeeds). -/
theorem runAsm_compose {n m offsetToPc prog as s1 s2}
    (h1 : runAsm n offsetToPc prog as = AsmResult.AsmOK s1)
    (h2 : runAsm m offsetToPc prog s1 = AsmResult.AsmOK s2) :
    runAsm (n + m) offsetToPc prog as = AsmResult.AsmOK s2 := by
  induction n generalizing as with
  | zero => rw [runAsm] at h1; injection h1 with he; subst he; simpa using h2
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by omega]
    rw [runAsm] at h1 ⊢
    cases hstep : asmStep offsetToPc prog as with
    | AsmOK s' => rw [hstep] at h1; exact ih h1
    | AsmHalt s' => rw [hstep] at h1; simp at h1
    | AsmRevert s' => rw [hstep] at h1; simp at h1
    | AsmFault s' => rw [hstep] at h1; simp at h1
    | AsmError msg => rw [hstep] at h1; simp at h1

/-- **`runAsm` splits after an OK prefix.** If the first `n` steps reach `AsmOK s1`, then `n + m`
    steps equal `m` steps from `s1` — for *any* tail result (OK or terminal), unlike `runAsm_compose`
    which needs the tail OK too. The asm-side composition for the CFG walk's OK/JMP step: a block runs
    `n` steps to its successor's pc, then the rest of the walk continues. -/
theorem runAsm_append_ok {n m offsetToPc prog as s1}
    (h1 : runAsm n offsetToPc prog as = AsmResult.AsmOK s1) :
    runAsm (n + m) offsetToPc prog as = runAsm m offsetToPc prog s1 := by
  induction n generalizing as with
  | zero => rw [runAsm] at h1; injection h1 with he; subst he; rw [Nat.zero_add]
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by omega]
    rw [runAsm] at h1 ⊢
    cases hstep : asmStep offsetToPc prog as with
    | AsmOK s' => rw [hstep] at h1; exact ih h1
    | AsmHalt s' => rw [hstep] at h1; simp at h1
    | AsmRevert s' => rw [hstep] at h1; simp at h1
    | AsmFault s' => rw [hstep] at h1; simp at h1
    | AsmError msg => rw [hstep] at h1; simp at h1

/-- **Terminal results are fuel-monotone.** `runAsm` stops at the first non-`AsmOK` step, so once it
    reaches a terminal `R` (≠ `AsmOK`) within `n` steps, extra fuel leaves it unchanged. The asm-side
    counterpart of the CFG composition's need: the whole-function `runAsm` runs `prog.length` steps,
    far more than any single block needs to reach its terminator. -/
theorem runAsm_add_of_ne_ok {offsetToPc prog R} (hR : ∀ s, R ≠ AsmResult.AsmOK s) {m : Nat} :
    ∀ {n : Nat} {as : AsmState},
      runAsm n offsetToPc prog as = R → runAsm (n + m) offsetToPc prog as = R := by
  intro n
  induction n with
  | zero => intro as h; rw [runAsm] at h; exact absurd h.symm (hR as)
  | succ k ih =>
    intro as h
    rw [show k + 1 + m = (k + m) + 1 from by omega]
    rw [runAsm] at h ⊢
    cases hstep : asmStep offsetToPc prog as with
    | AsmOK s' => rw [hstep] at h; exact ih h
    | AsmHalt s' => rw [hstep] at h; exact h
    | AsmRevert s' => rw [hstep] at h; exact h
    | AsmFault s' => rw [hstep] at h; exact h
    | AsmError msg => rw [hstep] at h; exact h

/-- `≤`-form of `runAsm_add_of_ne_ok`: a terminal reached within `n` steps survives any larger fuel
    `N ≥ n`. This is the form the CFG walk uses (`n` = a block's plan length, `N` = `prog.length`). -/
theorem runAsm_le_of_ne_ok {offsetToPc prog R} (hR : ∀ s, R ≠ AsmResult.AsmOK s) {n N : Nat}
    {as : AsmState} (hle : n ≤ N) (h : runAsm n offsetToPc prog as = R) :
    runAsm N offsetToPc prog as = R := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hle
  exact runAsm_add_of_ne_ok hR h

/-! ## Plan-op sequencing framework

`reorderPlan`/`popmanyPlan` build their op lists by concatenation, so the
simulation composes block-by-block: `executePlan` distributes over `++`, an
`asmBlockAt` placement splits into its prefix/suffix, and the runs chain via
`runAsm_compose`. -/

/-- `executePlan` distributes over list append. -/
theorem executePlan_append (ops1 ops2 : List StackOp) :
    executePlan (ops1 ++ ops2) = executePlan ops1 ++ executePlan ops2 := by
  simp [executePlan]

/-- A block placed at `pc` splits into its prefix (at `pc`) and suffix (at
    `pc + l1.length`). -/
theorem asmBlockAt_append {prog pc} {l1 l2 : List AsmInst}
    (h : asmBlockAt prog pc (l1 ++ l2)) :
    asmBlockAt prog pc l1 ∧ asmBlockAt prog (pc + l1.length) l2 := by
  obtain ⟨hlen, hget⟩ := h
  rw [List.length_append] at hlen
  refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩
  · intro j hj
    have hj' := hget j (by rw [List.length_append]; omega)
    rwa [List.getElem?_append_left hj] at hj'
  · intro j hj
    have hj' := hget (l1.length + j) (by rw [List.length_append]; omega)
    rw [show pc + (l1.length + j) = pc + l1.length + j from by omega,
      List.getElem?_append_right (by omega)] at hj'
    simpa using hj'

/-- **A contiguous segment is a block at its offset** (whole-program threading foundation). When the
    program is `A ++ insts ++ B`, the segment `insts` is `asmBlockAt` at offset `A.length`. Each
    block's plan is a segment of the concatenated function program, so it sits at its computed pc. -/
theorem asmBlockAt_of_middle (A insts B : List AsmInst) :
    asmBlockAt (A ++ insts ++ B) A.length insts := by
  refine ⟨?_, ?_⟩
  · rw [List.length_append, List.length_append]; omega
  · intro j hj
    have h1 : A.length + j < (A ++ insts).length := by rw [List.length_append]; omega
    rw [List.getElem?_append_left h1, List.getElem?_append_right (Nat.le_add_right A.length j),
        show A.length + j - A.length = j from by omega]

/-- `asmBlockAt` lifts through a per-instruction map (e.g. `resolveInst`): a block in `prog` becomes
    the mapped block in `prog.map f`, at the same offset (length-preserving). Bridges the unresolved
    `asmBlockAt` (from `asmBlockAt_of_middle`) to the resolved program `(asmResolve …).1 =
    prog.map (resolveInst …)`. -/
theorem asmBlockAt_map {prog : List AsmInst} {pc : Nat} {insts : List AsmInst}
    (f : AsmInst → AsmInst) (h : asmBlockAt prog pc insts) :
    asmBlockAt (prog.map f) pc (insts.map f) := by
  obtain ⟨hlen, hget⟩ := h
  refine ⟨by rw [List.length_map, List.length_map]; exact hlen, ?_⟩
  intro j hj
  rw [List.length_map] at hj
  rw [List.getElem?_map, List.getElem?_map, hget j hj]

/-! ## Big-swap asm-execution folds

The asm program for the big-swap is `chunk` raw spills (`PUSH;MSTORE`) then
`chunk` raw restores (`PUSH;MLOAD`). These lemmas run those folds: `runSpillRange`
pops the top `chunk` items and writes them to the fresh slots `base+32k`;
`runRestoreRange` reads the slots back and pushes them. Together with
`bigSwap_stack_spec` (stack permutation) and `spillFold_chars` (offset layout)
they are the full machinery the big-swap `doSwap_sim` case composes. -/

/-- **Raw spill step.** Running `[PUSH off; MSTORE]` pops the asm TOS `v` and
    writes it to slot `off` (which must be aligned, in-range, and covered),
    leaving every other field of the state untouched. No plan-map involved —
    this is the atom the big-swap spill fold composes. -/
theorem asmSpillStep {prog : List AsmInst} {as : AsmState} {off : Nat} {v : bytes32}
    {rest : List bytes32}
    (hstk : as.stack = v :: rest)
    (halign : 32 ∣ off) (hoff256 : off < 2 ^ 256) (hcov : off + 32 ≤ as.memory.size)
    (hblock : asmBlockAt prog as.pc [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"]) :
    runAsm 2 offsetToPc prog as = AsmResult.AsmOK
      { as with pc := as.pc + 2, stack := rest,
                memory := (wordToBytes v).write 0 as.memory off 32 } := by
  set pw := wordOfBytes (List.toByteArray
    (List.replicate (32 - (encodeNumBytes off).length) 0 ++ encodeNumBytes off)) with hpwdef
  have hpwoff : pw.toNat = off := pushed_offset_toNat off hoff256
  set as1 : AsmState := { asmNext as with stack := pw :: as.stack } with has1def
  have hnoop : asmExpandMemory (off + 32) as.memory = as.memory :=
    asmExpandMemory_of_covered (off + 32) as.memory
      (by rw [rounded_add_32_of_aligned halign]; exact hcov)
  have hpc0 : as.pc < prog.length := asmBlockAt_pc_lt hblock (by simp)
  have hg0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmPush (encodeNumBytes off) := by
    have := asmBlockAt_get hblock (j := 0) (by simp); simpa using this
  have hpc1 : as1.pc < prog.length := by
    rcases hblock with ⟨hbl, _⟩; show as.pc + 1 < prog.length; simp at hbl; omega
  have hg1 : prog.get ⟨as1.pc, hpc1⟩ = AsmInst.AsmOp "MSTORE" := by
    have := asmBlockAt_get hblock (j := 1) (by simp)
    show prog.get ⟨as.pc + 1, hpc1⟩ = _; simpa using this
  have hstep0 : asmStep offsetToPc prog as = AsmResult.AsmOK as1 := by
    rw [asmStep_push_ok hpc0 hg0]; rfl
  have hstep1 : asmStep offsetToPc prog as1 = AsmResult.AsmOK
      { as with pc := as.pc + 2, stack := rest,
                memory := (wordToBytes v).write 0 as.memory off 32 } := by
    rw [asmStep_mstore_ok hpc1 hg1]
    show asmMstore as1 = _
    have hs1stk : as1.stack = pw :: v :: rest := by rw [has1def]; simp [hstk]
    have hs1mem : as1.memory = as.memory := rfl
    simp only [asmMstore, hs1stk, hs1mem, hpwoff, hnoop]
    rfl
  rw [runAsm_succ_ok hpc0 hstep0, runAsm_succ_ok hpc1 hstep1, runAsm]

/-- **Raw restore step.** Running `[PUSH off; MLOAD]` pushes the word stored at
    slot `off` (aligned, covered) onto the asm stack, leaving memory and every
    other field unchanged. The atom the big-swap restore fold composes. -/
theorem asmRestoreStep {prog : List AsmInst} {as : AsmState} {off : Nat}
    (halign : 32 ∣ off) (hoff256 : off < 2 ^ 256) (hcov : off + 32 ≤ as.memory.size)
    (hblock : asmBlockAt prog as.pc [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"]) :
    runAsm 2 offsetToPc prog as = AsmResult.AsmOK
      { as with pc := as.pc + 2,
                stack := wordOfBytes (as.memory.readWithPadding off 32) :: as.stack } := by
  set pw := wordOfBytes (List.toByteArray
    (List.replicate (32 - (encodeNumBytes off).length) 0 ++ encodeNumBytes off)) with hpwdef
  have hpwoff : pw.toNat = off := pushed_offset_toNat off hoff256
  set as1 : AsmState := { asmNext as with stack := pw :: as.stack } with has1def
  have hnoop : asmExpandMemory (off + 32) as.memory = as.memory :=
    asmExpandMemory_of_covered (off + 32) as.memory
      (by rw [rounded_add_32_of_aligned halign]; exact hcov)
  have hpc0 : as.pc < prog.length := asmBlockAt_pc_lt hblock (by simp)
  have hg0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmPush (encodeNumBytes off) := by
    have := asmBlockAt_get hblock (j := 0) (by simp); simpa using this
  have hpc1 : as1.pc < prog.length := by
    rcases hblock with ⟨hbl, _⟩; show as.pc + 1 < prog.length; simp at hbl; omega
  have hg1 : prog.get ⟨as1.pc, hpc1⟩ = AsmInst.AsmOp "MLOAD" := by
    have := asmBlockAt_get hblock (j := 1) (by simp)
    show prog.get ⟨as.pc + 1, hpc1⟩ = _; simpa using this
  have hstep0 : asmStep offsetToPc prog as = AsmResult.AsmOK as1 := by
    rw [asmStep_push_ok hpc0 hg0]; rfl
  have hstep1 : asmStep offsetToPc prog as1 = AsmResult.AsmOK
      { as with pc := as.pc + 2,
                stack := wordOfBytes (as.memory.readWithPadding off 32) :: as.stack } := by
    rw [asmStep_mload_ok hpc1 hg1]
    show asmMload as1 = _
    have hs1stk : as1.stack = pw :: as.stack := rfl
    have hs1mem : as1.memory = as.memory := rfl
    simp only [asmMload, hs1stk, hs1mem, hpwoff, hnoop]
    rfl
  rw [runAsm_succ_ok hpc0 hstep0, runAsm_succ_ok hpc1 hstep1, runAsm]

/-- `executePlan (op :: ops) = execStackOp op ++ executePlan ops`. -/
theorem executePlan_cons (op : StackOp) (ops : List StackOp) :
    executePlan (op :: ops) = execStackOp op ++ executePlan ops := by
  simp [executePlan, List.flatMap_cons]

/-- **Spill fold.** Running `n` consecutive spills at offsets `base, base+32, …`
    (the big-swap layout, all aligned/covered) pops the top `n` of the asm stack
    and writes them to those slots. Result memory `m`: slot `base+32k` holds the
    bytes of `as.stack[k]` (read straight back), every 32-window disjoint from the
    temp region is unchanged, every byte outside it is unchanged, and `size`
    never shrinks. -/
theorem runSpillRange (n : Nat) (base : Nat) (prog : List AsmInst) (as : AsmState)
    (halign : 32 ∣ base) (hbound : base + 32 * n < 2 ^ 256) (hcov : base + 32 * n ≤ as.memory.size)
    (hlen : n ≤ as.stack.length)
    (hblock : asmBlockAt prog as.pc
       (executePlan ((List.range n).map (fun k => StackOp.SOSpill (base + 32 * k))))) :
    ∃ m : ByteArray,
      runAsm (2 * n) offsetToPc prog as
        = AsmResult.AsmOK { as with pc := as.pc + 2 * n, stack := as.stack.drop n, memory := m } ∧
      (∀ k, k < n → m.readWithPadding (base + 32 * k) 32 = wordToBytes (as.stack[k]!)) ∧
      (∀ off', off' + 32 ≤ base ∨ base + 32 * n ≤ off' →
         m.readWithPadding off' 32 = as.memory.readWithPadding off' 32) ∧
      (∀ i, i < base ∨ base + 32 * n ≤ i → readByte i m = readByte i as.memory) ∧
      as.memory.size ≤ m.size := by
  induction n generalizing base as with
  | zero =>
    refine ⟨as.memory, ?_, fun k hk => (Nat.not_lt_zero k hk).elim, fun _ _ => rfl,
            fun _ _ => rfl, le_refl _⟩
    simp [runAsm]
  | succ n ih =>
    obtain ⟨v, rest, hstk⟩ : ∃ v rest, as.stack = v :: rest := by
      cases h : as.stack with
      | nil => rw [h] at hlen; simp at hlen
      | cons v r => exact ⟨v, r, rfl⟩
    -- split the block into [PUSH base; MSTORE] ++ (rest of the spills at base+32)
    rw [range_succ_map_affine StackOp.SOSpill, executePlan_cons,
        show execStackOp (StackOp.SOSpill base)
          = [AsmInst.AsmPush (encodeNumBytes base), AsmInst.AsmOp "MSTORE"] from rfl] at hblock
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    -- first spill (the atom)
    have hbase256 : base < 2 ^ 256 := by omega
    have hbasecov : base + 32 ≤ as.memory.size := by omega
    have hstep1 := asmSpillStep (offsetToPc := offsetToPc) (off := base) (v := v) (rest := rest)
      hstk halign hbase256 hbasecov hb1
    set as1 : AsmState :=
      { as with pc := as.pc + 2, stack := rest, memory := (wordToBytes v).write 0 as.memory base 32 }
      with has1def
    -- the IH on the tail
    have hwrsize : as.memory.size ≤ as1.memory.size := by
      have : (wordToBytes v).size = 32 := length_wordToBytes v
      have hge := EvmYul.byteArray_write_size (wordToBytes v) as.memory base
      rw [this] at hge; exact hge
    have hb2' : asmBlockAt prog as1.pc
        (executePlan ((List.range n).map (fun k => StackOp.SOSpill (base + 32 + 32 * k)))) := by
      have : ([AsmInst.AsmPush (encodeNumBytes base), AsmInst.AsmOp "MSTORE"]).length = 2 := rfl
      rw [this] at hb2; exact hb2
    obtain ⟨m, hrun, hA, hB, hBb, hsz⟩ :=
      ih (base + 32) as1 (Dvd.dvd.add halign ⟨1, rfl⟩) (by omega) (by
        show base + 32 + 32 * n ≤ as1.memory.size; omega) (by
        show n ≤ as1.stack.length; rw [has1def]; show n ≤ rest.length
        have : as.stack.length = rest.length + 1 := by rw [hstk]; simp
        omega) hb2'
    refine ⟨m, ?_, ?_, ?_, ?_, ?_⟩
    · -- run composition
      rw [show 2 * (n + 1) = 2 + 2 * n from by ring]
      have hcomp := runAsm_compose hstep1 hrun
      rw [hcomp]
      congr 1
      rw [has1def]
      simp only [List.drop_succ_cons, hstk]
      congr 1
      · omega
    · -- per-slot readback
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- slot base = first write, preserved by the tail (window frame)
        simp only [Nat.mul_zero, Nat.add_zero]
        rw [hB base (Or.inl (by omega)), has1def]
        show ((wordToBytes v).write 0 as.memory base 32).readWithPadding base 32
              = wordToBytes (as.stack[0]!)
        have hsz : (wordToBytes v).size = 32 := length_wordToBytes v
        rw [← hsz, EvmYul.byteArray_write_read (wordToBytes v) as.memory base
              (by rw [hsz]; norm_num) (by rcases USize.size_eq with h | h <;> omega)
              (by rw [hsz]; norm_num)]
        simp [hstk]
      · -- slot base+32k = (k-1)-th tail write
        have hk' : k - 1 < n := by omega
        have hAk := hA (k - 1) hk'
        have has1stk : as1.stack = rest := rfl
        rw [has1stk] at hAk
        have hget : rest[k - 1]! = as.stack[k]! := by
          rw [hstk, List_get!_eq_getElem?_getD, List_get!_eq_getElem?_getD]
          congr 1
          conv_rhs => rw [show k = (k - 1) + 1 from by omega]
          rw [List.getElem?_cons_succ]
        rw [show base + 32 * k = base + 32 + 32 * (k - 1) from by omega, hAk, hget]
    · -- window frame
      intro off' hoff'
      rw [hB off' (by omega), has1def]
      show ((wordToBytes v).write 0 as.memory base 32).readWithPadding off' 32 = _
      rw [mstore_readWithPadding_frame v as.memory base off' (by omega) (by omega)]
    · -- byte frame
      intro i hi
      rw [hBb i (by omega), has1def]
      show readByte i ((wordToBytes v).write 0 as.memory base 32) = _
      rw [mstore_readByte_frame v as.memory base i (by omega) (by omega)]
    · -- size
      exact le_trans hwrsize hsz

/-- **Restore fold.** Running the restores for `roffs` (each aligned/covered)
    pushes the words stored at those slots onto the asm stack, in reverse order
    (last restore = TOS), leaving memory untouched. -/
theorem runRestoreRange (roffs : List Nat) (prog : List AsmInst) (as : AsmState)
    (hwf : ∀ off ∈ roffs, 32 ∣ off ∧ off < 2 ^ 256 ∧ off + 32 ≤ as.memory.size)
    (hblock : asmBlockAt prog as.pc (executePlan (roffs.map StackOp.SORestore))) :
    runAsm (2 * roffs.length) offsetToPc prog as = AsmResult.AsmOK
      { as with pc := as.pc + 2 * roffs.length,
                stack := (roffs.reverse.map
                          (fun off => wordOfBytes (as.memory.readWithPadding off 32))) ++ as.stack } := by
  induction roffs generalizing as with
  | nil => simp [runAsm]
  | cons o tail ih =>
    -- split block: [PUSH o; MLOAD] ++ rest
    rw [List.map_cons, executePlan_cons,
        show execStackOp (StackOp.SORestore o)
          = [AsmInst.AsmPush (encodeNumBytes o), AsmInst.AsmOp "MLOAD"] from rfl] at hblock
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨ho_align, ho256, ho_cov⟩ := hwf o (by simp)
    have hstep1 := asmRestoreStep (offsetToPc := offsetToPc) (off := o) ho_align ho256 ho_cov hb1
    set as1 : AsmState :=
      { as with pc := as.pc + 2,
                stack := wordOfBytes (as.memory.readWithPadding o 32) :: as.stack } with has1def
    have has1mem : as1.memory = as.memory := rfl
    have hb2' : asmBlockAt prog as1.pc (executePlan (tail.map StackOp.SORestore)) := by
      have : ([AsmInst.AsmPush (encodeNumBytes o), AsmInst.AsmOp "MLOAD"]).length = 2 := rfl
      rw [this] at hb2; exact hb2
    have hwf' : ∀ off ∈ tail, 32 ∣ off ∧ off < 2 ^ 256 ∧ off + 32 ≤ as1.memory.size := by
      intro off hoff; rw [has1mem]; exact hwf off (by simp [hoff])
    have hrun := ih as1 hwf' hb2'
    rw [has1mem] at hrun
    rw [List.length_cons,
        show 2 * (tail.length + 1) = 2 + 2 * tail.length from by ring]
    rw [runAsm_compose hstep1 hrun]
    congr 1
    rw [has1def]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
               List.append_assoc, List.singleton_append]
    congr 1
    · omega

/-- **Big-swap asm-stack spec.** The restored top chunk `desired.map (s.get!)`
    (TOS first) followed by the untouched base `s.drop (d+1)` is exactly the asm
    stack of a *small* swap: TOS `s[0]` exchanged with `s[d]`. This lets the
    big-swap reuse `planStackRel_swap` — the asm side is the same swapped stack
    the small case produces. Pure list reasoning. -/
theorem bigSwap_asmStack_spec (s : List bytes32) (d : Nat) (h0 : 0 < d) (hlen : d < s.length) :
    (([d] ++ (List.range (d - 1)).map (· + 1) ++ [0]).map (fun idx => s[idx]!))
        ++ s.drop (d + 1)
    = (s.set 0 (s[d]!)).set d (s[0]!) := by
  have hcle : d + 1 ≤ s.length := hlen
  have hmaplen : (([d] ++ (List.range (d - 1)).map (· + 1) ++ [0]).map (fun idx => s[idx]!)).length
      = d + 1 := by
    rw [List.length_map]
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
  have hsget : ∀ i, i < s.length → s[i]? = some (s[i]!) := fun i hi => getElem?_eq_some_get! s i hi
  apply List.ext_getElem?
  intro i
  by_cases hic : i < d + 1
  · rw [List.getElem?_append_left (by rw [hmaplen]; exact hic), List.getElem?_map,
        desired_getElem? d i h0 hic, Option.map_some]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [if_pos rfl, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
    · by_cases hid : i = d
      · subst hid
        have hdl : i < (s.set 0 (s[i]!)).length := by simp only [List.length_set]; omega
        rw [if_neg (by omega), if_pos rfl, List.getElem?_set_self hdl]
      · have hdi : d ≠ i := fun h => hid h.symm
        have h0i : (0 : Nat) ≠ i := by omega
        have hilt : i < s.length := by omega
        rw [if_neg (by omega), if_neg hid,
            List.getElem?_set_ne hdi, List.getElem?_set_ne h0i, hsget i hilt]
  · push Not at hic
    rw [List.getElem?_append_right (by rw [hmaplen]; exact hic), hmaplen, List.getElem?_drop,
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    congr 1
    omega

/-- The `k`-th allocated offset reads back as `base + 32·k`. -/
theorem rangeMap_get! (n base idx : Nat) (h : idx < n) :
    ((List.range n).map (fun k => base + 32 * k))[idx]! = base + 32 * idx := by
  rw [List_get!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
      Option.getD_some]

/-- Every index in `desired` is `≤ dist`. -/
theorem desired_mem_le (dist idx : Nat) (h0 : 0 < dist)
    (h : idx ∈ ([dist] ++ (List.range (dist - 1)).map (· + 1) ++ [0])) : idx ≤ dist := by
  simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at h
  rcases h with (rfl | ⟨a, ha, rfl⟩) | rfl <;> omega

/-- **`doSwap` for `dist > 16`** (with no free slots): the explicit op list and
    resulting plan state. Spills the top `dist+1` items to `nextOffset+32k`, then
    restores them in the `[dist,1..dist-1,0]` order. -/
theorem doSwap_big_eq {dist : Nat} {ps : PlanState} (hd : 16 < dist)
    (hlen : dist < ps.stack.length) (hfree : ps.alloc.freeSlots = []) :
    doSwap dist ps =
      ( (List.range (dist + 1)).map (fun k => StackOp.SOSpill (ps.alloc.nextOffset + 32 * k))
        ++ ([dist] ++ (List.range (dist - 1)).map (· + 1) ++ [0]).reverse.map
             (fun idx => StackOp.SORestore (ps.alloc.nextOffset + 32 * idx)),
        { ps with
          stack := ps.stack.take (ps.stack.length - (dist + 1))
                   ++ ([dist] ++ (List.range (dist - 1)).map (· + 1) ++ [0]).map
                        (fun idx => (topN (dist + 1) ps.stack)[idx]!),
          alloc := ((List.range (dist + 1)).map (fun k => ps.alloc.nextOffset + 32 * k)).foldl
                     (fun al off => freeSpillSlot off al)
                     { ps.alloc with nextOffset := ps.alloc.nextOffset + 32 * (dist + 1) } }) := by
  have hitemslen : (topN (dist + 1) ps.stack).length = dist + 1 := topN_length _ _ (by omega)
  unfold doSwap
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [spillFold_chars (topN (dist + 1) ps.stack) [] [] ps.alloc hfree, hitemslen,
             List.nil_append]
  congr 1
  -- restore-op list: simplify `offsets[idx]!` to `base + 32·idx`
  congr 1
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_reverse] at hidx
  rw [rangeMap_get! _ _ _ (by have := desired_mem_le dist idx (by omega) hidx; omega)]

/-- A plan whose every op lowers to exactly two asm instructions has asm length
    `2 · ops.length`. -/
theorem execLen_two (ops : List StackOp) (h : ∀ op ∈ ops, (execStackOp op).length = 2) :
    (executePlan ops).length = 2 * ops.length := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [executePlan_cons, List.length_append, h o (by simp),
        ih (fun op hop => h op (by simp [hop])), List.length_cons]
    omega

/-- `executePlan` of a list of spills: `2 · length`. -/
theorem execLen_spillMap {α} (l : List α) (g : α → Nat) :
    (executePlan (l.map (fun x => StackOp.SOSpill (g x)))).length = 2 * l.length := by
  rw [execLen_two _ (by intro op hop; rw [List.mem_map] at hop; obtain ⟨x, _, rfl⟩ := hop; rfl),
      List.length_map]

/-- `executePlan` of a list of restores: `2 · length`. -/
theorem execLen_restoreMap (roffs : List Nat) :
    (executePlan (roffs.map StackOp.SORestore)).length = 2 * roffs.length := by
  rw [execLen_two _ (by intro op hop; rw [List.mem_map] at hop; obtain ⟨x, _, rfl⟩ := hop; rfl),
      List.length_map]

/-- length of `desired`. -/
theorem desired_length (dist : Nat) (h0 : 0 < dist) :
    ([dist] ++ (List.range (dist - 1)).map (· + 1) ++ [0]).length = dist + 1 := by
  simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]; omega

/-- Freeing slots (a `foldl` of `freeSpillSlot`) never moves `nextOffset`. -/
theorem foldl_free_nextOffset (l : List Nat) (a : SpillAlloc) :
    (l.foldl (fun al off => freeSpillSlot off al) a).nextOffset = a.nextOffset := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl

/-- Freeing slots never moves `fnEom`. -/
theorem foldl_free_fnEom (l : List Nat) (a : SpillAlloc) :
    (l.foldl (fun al off => freeSpillSlot off al) a).fnEom = a.fnEom := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl

/-- **Big-swap simulation** (`dist > 16`). The final assembly: compose the spill
    and restore folds, recognise the resulting asm stack as the small-swap stack,
    and discharge `venomAsmRel`. -/
theorem doSwap_big_sim {dist ps ps' ops labelOffsets vs as prog}
    (hd : 16 < dist)
    (hswap : doSwap dist ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : dist < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hwf : SpillAllocWf ps.alloc)
    (hfree : ps.alloc.freeSlots = [])
    (h256 : ps.alloc.nextOffset + 32 * (dist + 1) < 2 ^ 256)
    (hcov : ps.alloc.nextOffset + 32 * (dist + 1) ≤ as.memory.size)
    (hspillbnd : ∀ o off', alookup' ps.spilled o = some off' → off' + 32 ≤ ps.alloc.nextOffset) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  rcases hrel with ⟨hstack, hspill, hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
  have hd0 : 0 < dist := by omega
  have haslen : as.stack.length = ps.stack.length := (planStackRel_length hstack).symm
  have halign : 32 ∣ ps.alloc.nextOffset := hwf.align_next
  -- explicit ops / ps'
  rw [doSwap_big_eq hd hlen hfree, Prod.mk.injEq] at hswap
  obtain ⟨hops, hps'⟩ := hswap
  subst hops; subst hps'
  -- abbreviations
  set base := ps.alloc.nextOffset with hbase
  set desired := ([dist] ++ (List.range (dist - 1)).map (· + 1) ++ [0]) with hdes
  set roffs := desired.reverse.map (fun idx => base + 32 * idx) with hroffs
  have hdeslen : desired.length = dist + 1 := desired_length dist hd0
  have hrofflen : roffs.length = dist + 1 := by rw [hroffs, List.length_map, List.length_reverse, hdeslen]
  -- restoreOps as a `.map SORestore`
  have hre : desired.reverse.map (fun idx => StackOp.SORestore (base + 32 * idx)) = roffs.map StackOp.SORestore := by
    rw [hroffs, List.map_map]; rfl
  rw [hre] at hblock ⊢
  rw [executePlan_append] at hblock ⊢
  obtain ⟨hblock_sp, hblock_re⟩ := asmBlockAt_append hblock
  -- lengths
  have hsplen : (executePlan ((List.range (dist + 1)).map (fun k => StackOp.SOSpill (base + 32 * k)))).length
      = 2 * (dist + 1) := by rw [execLen_spillMap]; simp
  have hrelen : (executePlan (roffs.map StackOp.SORestore)).length = 2 * (dist + 1) := by
    rw [execLen_restoreMap, hrofflen]
  -- run the spill fold
  obtain ⟨m, hrun_sp, hslot, hwin, hbyte, hsz⟩ :=
    runSpillRange (offsetToPc := offsetToPc) (dist + 1) base prog as halign h256 hcov (by omega) hblock_sp
  set as_sp : AsmState :=
    { as with pc := as.pc + 2 * (dist + 1), stack := as.stack.drop (dist + 1), memory := m } with has_sp
  -- run the restore fold
  have hre_cov : ∀ off ∈ roffs, 32 ∣ off ∧ off < 2 ^ 256 ∧ off + 32 ≤ as_sp.memory.size := by
    intro off hoff
    rw [hroffs, List.mem_map] at hoff
    obtain ⟨idx, hidx, rfl⟩ := hoff
    rw [List.mem_reverse] at hidx
    have hile : idx ≤ dist := desired_mem_le dist idx hd0 hidx
    refine ⟨halign.add (dvd_mul_right 32 idx), by omega, ?_⟩
    show base + 32 * idx + 32 ≤ as_sp.memory.size
    have : as_sp.memory.size = m.size := rfl
    rw [this]; omega
  have hblock_re' : asmBlockAt prog as_sp.pc (executePlan (roffs.map StackOp.SORestore)) := by
    show asmBlockAt prog (as.pc + 2 * (dist + 1)) _
    rw [← hsplen]; exact hblock_re
  have hrun_re := runRestoreRange (offsetToPc := offsetToPc) roffs prog as_sp hre_cov hblock_re'
  set asf : AsmState := { as_sp with pc := as_sp.pc + 2 * roffs.length, stack := (roffs.reverse.map (fun off => wordOfBytes (as_sp.memory.readWithPadding off 32))) ++ as_sp.stack }
  refine ⟨asf, ?_, ?_, ?_⟩
  · rw [List.length_append, hsplen, hrelen, show 2 * (dist + 1) + 2 * (dist + 1)
          = 2 * (dist + 1) + 2 * roffs.length from by rw [hrofflen]]
    exact runAsm_compose hrun_sp hrun_re
  · -- venomAsmRel
    have haslen' : dist < as.stack.length := by rw [haslen]; exact hlen
    have hps'stk : ps.stack.take (ps.stack.length - (dist + 1))
                   ++ desired.map (fun idx => (topN (dist + 1) ps.stack)[idx]!)
                 = stackSwap dist ps.stack := bigSwap_stack_spec ps.stack dist hd0 hlen
    have hprefix : (roffs.reverse.map (fun off => wordOfBytes (m.readWithPadding off 32)))
                 = desired.map (fun idx => as.stack[idx]!) := by
      have hstep : roffs.reverse.map (fun off => wordOfBytes (m.readWithPadding off 32))
                 = desired.map (fun idx => wordOfBytes (m.readWithPadding (base + 32 * idx) 32)) := by
        simp only [hroffs, List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]
      rw [hstep]
      apply List.map_congr_left
      intro idx hidx
      rw [hslot idx (by have := desired_mem_le dist idx hd0 hidx; omega), wordOfBytes_wordToBytes]
    have hasfstk : asf.stack = (as.stack.set 0 (as.stack[dist]!)).set dist (as.stack[0]!) := by
      show (roffs.reverse.map (fun off => wordOfBytes (m.readWithPadding off 32)))
            ++ as.stack.drop (dist + 1) = _
      rw [hprefix]; exact bigSwap_asmStack_spec as.stack dist hd0 haslen'
    set A := ((List.range (dist + 1)).map (fun k => base + 32 * k)).foldl
               (fun al off => freeSpillSlot off al)
               ({ ps.alloc with nextOffset := base + 32 * (dist + 1) }) with hA
    have hAnext : A.nextOffset = base + 32 * (dist + 1) := by rw [hA, foldl_free_nextOffset]
    have hAfn : A.fnEom = ps.alloc.fnEom := by rw [hA, foldl_free_fnEom]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show planStackRel labelOffsets vs
        (ps.stack.take (ps.stack.length - (dist + 1))
          ++ desired.map (fun idx => (topN (dist + 1) ps.stack)[idx]!)) asf.stack
      rw [hps'stk, hasfstk]; exact planStackRel_swap hstack hd0 hlen
    · intro op off hlook
      obtain ⟨v, hov, hmemv⟩ := hspill op off hlook
      refine ⟨v, hov, ?_⟩
      show wordOfBytes (asf.memory.readWithPadding off 32) = v
      have hbnd : off + 32 ≤ base := hspillbnd op off hlook
      show wordOfBytes (m.readWithPadding off 32) = v
      rw [hwin off (Or.inl hbnd), hmemv]
    · intro i hi
      show readByte i vs.memory = readByte i asf.memory
      show readByte i vs.memory = readByte i m
      rw [hAnext, hAfn] at hi
      have hfnle : ps.alloc.fnEom ≤ base := hwf.fnEom_le
      have hcase : i < base ∨ base + 32 * (dist + 1) ≤ i := by
        rw [not_and_or, not_le, not_lt] at hi; omega
      rw [hmem i (by rw [not_and_or, not_le, not_lt]; omega), hbyte i hcase]
    · exact hacc
    · exact htr
    · exact hrd
    · exact hlog
    · exact hcc
    · exact htc
    · exact hbc
    · exact hcode
    · exact hprev
  · have hpc : asf.pc = as.pc + 2 * (dist + 1) + 2 * roffs.length := rfl
    rw [List.length_append, hsplen, hrelen, hpc, hrofflen]; omega

/-- `doSwap dist ps = (ops, ps')` simulates: running `executePlan ops` on the
    asm state preserves `venomAsmRel` (mirrors HOL `do_swap_venom_asm_rel`).

    Preconditions (matching HOL):
    - `dist < ps.stack.length` (swap target exists)
    - `dist > 16` ⇒ spill-allocator well-formedness, distinct top items,
      no overlap with spilled set, offset range (the big-swap bulk
      spill/restore case — proof deferred; the full side-condition set is
      captured by `hbig` and will be discharged once `spillAllocWf` and the
      bulk spill/restore per-op lemmas are in place)
    - `asmBlockAt prog as.pc (executePlan ops)` (planned ops are placed at PC)

    Conclusion adds `as'.pc = as.pc + (executePlan ops).length` (PC advance),
    needed for block composition. -/
theorem doSwap_sim {dist ps ps' ops labelOffsets vs as prog}
    (hswap : doSwap dist ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : dist < ps.stack.length)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hbig : dist > 16 →
            -- big-swap side conditions (discharged by `doSwap_big_sim`):
            -- a well-formed allocator with no free slots, the temp spill region
            -- `[nextOffset, nextOffset+32·(dist+1))` in range and memory-covered,
            -- and the existing spills disjoint below `nextOffset`.
            (SpillAllocWf ps.alloc ∧
             ps.alloc.freeSlots = [] ∧
             ps.alloc.nextOffset + 32 * (dist + 1) < 2 ^ 256 ∧
             ps.alloc.nextOffset + 32 * (dist + 1) ≤ as.memory.size ∧
             (∀ o off', alookup' ps.spilled o = some off' → off' + 32 ≤ ps.alloc.nextOffset))) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as =
             AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  by_cases hdist0 : dist = 0
  · subst hdist0
    have hdo0 : doSwap 0 ps = ([], ps) := by unfold doSwap; simp
    rw [hdo0] at hswap
    rcases hswap with ⟨rfl, rfl⟩
    have hprog : executePlan ([] : List StackOp) = [] := rfl
    rw [hprog]
    refine ⟨as, ?_, hrel, ?_⟩
    · simp [runAsm]
    · simp
  · have hd0 : 0 < dist := Nat.pos_of_ne_zero hdist0
    by_cases hd16 : dist ≤ 16
    · have hdo_small : doSwap dist ps = ([StackOp.SOSwap dist],
                          { ps with stack := stackSwap dist ps.stack }) := by
        unfold doSwap; simp [hdist0, hd16]
      rw [hdo_small] at hswap
      rcases hswap with ⟨rfl, rfl⟩
      have hlen_ops : (executePlan [StackOp.SOSwap dist]).length = 1 := by
        simp [executePlan, execStackOp, swapName]
      have hpc_prog : as.pc < prog.length := by
        rcases hblock with ⟨hbound, _⟩
        rw [hlen_ops] at hbound
        omega
      have hprog_get : prog.get ⟨as.pc, hpc_prog⟩ = AsmInst.AsmOp (swapName dist) := by
        have hblock_len : 0 < (executePlan [StackOp.SOSwap dist]).length := by
          simp [executePlan, execStackOp, swapName]
        have h_get := asmBlockAt_get hblock hblock_len
        -- h_get : prog.get ⟨as.pc + 0, ?_⟩ = (executePlan ...).get ⟨0, ?_⟩
        -- RHS = AsmOp (swapName dist) by definition
        have h_rhs : (executePlan [StackOp.SOSwap dist]).get ⟨0, hblock_len⟩ = AsmInst.AsmOp (swapName dist) := rfl
        rw [h_rhs] at h_get
        -- LHS: as.pc + 0 = as.pc
        simpa [add_zero] using h_get
      have hstk_len : dist < as.stack.length := by
        rcases hrel with ⟨hstack, _, _, _, _, _, _, _, _, _, _, _⟩
        have hlen_stk : ps.stack.length = as.stack.length := planStackRel_length hstack
        omega
      let as' : AsmState :=
        { asmNext as with
          stack := (as.stack.set 0 (as.stack[dist]!)).set dist (as.stack[0]!) }
      have hasm : asmStep offsetToPc prog as = asmSwap dist as := by
        apply asmStep_swap_ok hpc_prog hprog_get hd0 hd16 hstk_len
      have hasm_as' : asmSwap dist as = AsmResult.AsmOK as' := by
        have h0stk : 0 < as.stack.length := by
          rcases hrel with ⟨hstack, _, _, _, _, _, _, _, _, _, _, _⟩
          have hlen_stk : ps.stack.length = as.stack.length := planStackRel_length hstack
          omega
        have hne : as.stack ≠ [] := by
          intro h; rw [h] at hstk_len; exact Nat.not_lt_zero _ hstk_len
        simp [asmSwap, asmNext, as', hd0, hstk_len, hne]
        rw [head?_getD_eq_zero as.stack hne]
      have hstep_as' : asmStep offsetToPc prog as = AsmResult.AsmOK as' :=
        calc
          asmStep offsetToPc prog as = asmSwap dist as := hasm
          _ = AsmResult.AsmOK as' := hasm_as'
      rw [hlen_ops]
      have hrun : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as' := by
        have hrun' : runAsm 1 offsetToPc prog as = runAsm 0 offsetToPc prog as' :=
          runAsm_succ_ok hpc_prog hstep_as'
        rw [hrun', runAsm]
      refine ⟨as', hrun, ?_, ?_⟩
      · rcases hrel with ⟨hstack, hspill, hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
        exact ⟨planStackRel_swap hstack hd0 hlen, hspill, hmem, hacc, htr, hrd, hlog,
               hcc, htc, hbc, hcode, hprev⟩
      · simp [as', asmNext]
    · -- dist > 16: bulk spill/restore, discharged by `doSwap_big_sim`
      obtain ⟨hwf, hfree, h256, hcov, hspillbnd⟩ := hbig (by omega)
      exact doSwap_big_sim (by omega) hswap hrel hlen hblock hwf hfree h256 hcov hspillbnd

/-- **Sequencing**: two sims placed consecutively in `prog` compose into one over
    `ops1 ++ ops2`. The run chains via `runAsm_compose`, the PC advance adds. -/
theorem plan_seq_sim {prog lo vs ps2 as as1 as2} {offsetToPc : AssocList Nat Nat}
    {ops1 ops2 : List StackOp}
    (h1run : runAsm (executePlan ops1).length offsetToPc prog as
              = AsmResult.AsmOK as1)
    (h1pc : as1.pc = as.pc + (executePlan ops1).length)
    (h2run : runAsm (executePlan ops2).length offsetToPc prog as1
              = AsmResult.AsmOK as2)
    (h2rel : venomAsmRel lo ps2 vs as2)
    (h2pc : as2.pc = as1.pc + (executePlan ops2).length) :
    runAsm (executePlan (ops1 ++ ops2)).length offsetToPc prog as
        = AsmResult.AsmOK as2 ∧
    venomAsmRel lo ps2 vs as2 ∧
    as2.pc = as.pc + (executePlan (ops1 ++ ops2)).length := by
  rw [executePlan_append, List.length_append]
  exact ⟨runAsm_compose h1run h2run, h2rel, by rw [h2pc, h1pc]; omega⟩

/-- The TOS-spill core (`doSpillTos`): `PUSH off; MSTORE` spills the top operand
    to slot `off`, preserving `venomAsmRel`. `doRestore_sim`'s dual — but the
    `MSTORE` writes memory, so the new spill entry is recovered by
    `asm_spill_roundtrip`, existing entries survive by the disjoint `MSTORE`
    frame, and `memoryRel` survives because the write lands inside the (grown)
    spill region. -/
theorem doSpillTos_sim {ps off alloc' op labelOffsets vs as prog}
    (hoff : allocSpillSlot ps.alloc = (off, alloc'))
    (hop : op = stackPeek 0 ps.stack)
    (hwf : SpillAllocWf ps.alloc)
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : 0 < ps.stack.length)
    (hblock : asmBlockAt prog as.pc [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"])
    (hcov : off + 32 ≤ as.memory.size) (hoff256 : off < 2 ^ 256)
    (hdisj : ∀ o' off', alookup' ps.spilled o' = some off' → off' + 32 ≤ off ∨ off + 32 ≤ off') :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets
             { ps with stack := stackPop 1 ps.stack,
                       spilled := ainsert' ps.spilled op off, alloc := alloc' } vs as' ∧
           as'.pc = as.pc + 2 := by
  rcases hrel with ⟨hstack, hsp, hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
  have halign : 32 ∣ off := by have := allocSpillSlot_aligned hwf; rwa [hoff] at this
  have hfnle : ps.alloc.fnEom ≤ off := by
    have := (allocSpillSlot_region hwf).1; rwa [hoff] at this
  have hnext : off + 32 ≤ alloc'.nextOffset := by
    have := (allocSpillSlot_region hwf).2; rwa [hoff] at this
  have halloc_fnEom : alloc'.fnEom = ps.alloc.fnEom := by
    have := allocSpillSlot_fnEom ps.alloc; rwa [hoff] at this
  have halloc_next : ps.alloc.nextOffset ≤ alloc'.nextOffset := by
    have := allocSpillSlot_nextOffset_ge ps.alloc; rwa [hoff] at this
  have haslen : 0 < as.stack.length := by have := planStackRel_length hstack; omega
  obtain ⟨value, rest, hstkd⟩ : ∃ v r, as.stack = v :: r := by
    cases hs : as.stack with
    | nil => rw [hs] at haslen; simp at haslen
    | cons v r => exact ⟨v, r, rfl⟩
  have hopv : operandVal vs labelOffsets op = some value := by
    rw [hop]; have := planStackRel_peek hstack hlen; rw [hstkd] at this; simpa using this
  set pw := wordOfBytes (List.toByteArray
    (List.replicate (32 - (encodeNumBytes off).length) 0 ++ encodeNumBytes off)) with hpwdef
  have hpwoff : pw.toNat = off := pushed_offset_toNat off hoff256
  set as1 : AsmState := { asmNext as with stack := pw :: as.stack } with has1def
  have hnoop : asmExpandMemory (off + 32) as.memory = as.memory :=
    asmExpandMemory_of_covered (off + 32) as.memory
      (by rw [rounded_add_32_of_aligned halign]; exact hcov)
  set newmem : ByteArray := (wordToBytes value).write 0 as.memory off 32 with hnmdef
  set as2 : AsmState := { asmNext as1 with stack := rest, memory := newmem } with has2def
  have hpc0 : as.pc < prog.length := asmBlockAt_pc_lt hblock (by simp)
  have hg0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmPush (encodeNumBytes off) := by
    have := asmBlockAt_get hblock (j := 0) (by simp); simpa using this
  have hpc1 : as1.pc < prog.length := by
    rcases hblock with ⟨hbl, _⟩; show as.pc + 1 < prog.length; simp at hbl; omega
  have hg1 : prog.get ⟨as1.pc, hpc1⟩ = AsmInst.AsmOp "MSTORE" := by
    have := asmBlockAt_get hblock (j := 1) (by simp)
    show prog.get ⟨as.pc + 1, hpc1⟩ = _; simpa using this
  have hstep0 : asmStep offsetToPc prog as = AsmResult.AsmOK as1 := by
    rw [asmStep_push_ok hpc0 hg0]; rfl
  have hstep1 : asmStep offsetToPc prog as1 = AsmResult.AsmOK as2 := by
    rw [asmStep_mstore_ok hpc1 hg1]
    show asmMstore as1 = AsmResult.AsmOK as2
    have hs1stk : as1.stack = pw :: value :: rest := by rw [has1def]; simp [hstkd]
    have hs1mem : as1.memory = as.memory := rfl
    simp only [asmMstore, hs1stk, hs1mem, hpwoff, hnoop]
    rfl
  have hrun : runAsm 2 offsetToPc prog as = AsmResult.AsmOK as2 := by
    rw [runAsm_succ_ok hpc0 hstep0, runAsm_succ_ok hpc1 hstep1, runAsm]
  refine ⟨as2, hrun, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hpr : planStackRel labelOffsets vs ps.stack (value :: rest) := by rw [← hstkd]; exact hstack
      exact planStackRel_pop hpr
    · intro o off' hlook'
      by_cases ho : o = op
      · subst ho
        rw [ainsert'_lookup_self] at hlook'
        injection hlook' with heq; subst heq
        exact ⟨value, hopv, asm_spill_roundtrip value as.memory off (by omega)⟩
      · rw [ainsert'_lookup_other ps.spilled op o off ho] at hlook'
        have hps := aremove_lookup_some ps.spilled op o off' hlook'
        obtain ⟨vo, hov, hmemo⟩ := hsp o off' hps
        refine ⟨vo, hov, ?_⟩
        show wordOfBytes (newmem.readWithPadding off' 32) = vo
        rw [hnmdef, mstore_readWithPadding_frame value as.memory off off' (by omega) (hdisj o off' hps)]
        exact hmemo
    · show memoryRel alloc' vs.memory newmem
      intro i hi
      rw [not_and_or, not_le, not_lt] at hi
      have hidisj : i < off ∨ off + 32 ≤ i := by omega
      have hmemcond : ¬(ps.alloc.fnEom ≤ i ∧ i < ps.alloc.nextOffset) := by
        rw [not_and_or, not_le, not_lt]; omega
      rw [hmem i hmemcond]
      show readByte i as.memory = readByte i newmem
      rw [hnmdef, mstore_readByte_frame value as.memory off i (by omega) hidisj]
    · exact hacc
    · exact htr
    · exact hrd
    · exact hlog
    · exact hcc
    · exact htc
    · exact hbc
    · exact hcode
    · exact hprev
  · show as2.pc = as.pc + 2
    rfl

/-- `doSpillAt dist ps = (ops, ps')` simulates (mirrors HOL
    `spill_op_venom_asm_rel` / the spill half of `spillSimScript`).
    Spills TOS (or TOS-after-swap when dist>0) to a fresh memory slot.

    Preconditions:
    - `0 < ps.stack.length` (stack non-empty)
    - the allocated offset `off < 2^256`, `ps.alloc.fnEom ≤ off`, and `off`
      doesn't overlap existing spill entries
    - `asmBlockAt prog as.pc (executePlan ops)`
    Proof deferred pending the `spillAsmSteps` per-op lemma (PUSH+MSTORE). -/
theorem doSpillAt_sim {dist ps ps' ops labelOffsets vs as prog}
    (hspill : doSpillAt dist ps = (ops, ps'))
    (hwf : SpillAllocWf ps.alloc)
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hlen : 0 < ps.stack.length)
    (hdlen : dist < ps.stack.length)
    (hdist16 : dist ≤ 16)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hcov : (allocSpillSlot ps.alloc).1 + 32 ≤ as.memory.size)
    (hoff256 : (allocSpillSlot ps.alloc).1 < 2 ^ 256)
    (hdisj : ∀ o' off', alookup' ps.spilled o' = some off' →
        off' + 32 ≤ (allocSpillSlot ps.alloc).1 ∨ (allocSpillSlot ps.alloc).1 + 32 ≤ off') :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as =
             AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  rcases haslot : allocSpillSlot ps.alloc with ⟨off0, alloc0⟩
  have hoff0 : (allocSpillSlot ps.alloc).1 = off0 := by rw [haslot]
  rw [hoff0] at hcov hoff256 hdisj
  by_cases hd0 : dist = 0
  · -- dist = 0: doSpillAt 0 = doSpillTos
    rw [doSpillAt, if_pos hd0, doSpillTos, haslot] at hspill
    rw [Prod.mk.injEq] at hspill
    obtain ⟨rfl, rfl⟩ := hspill
    rw [show executePlan [StackOp.SOSpill off0]
          = [AsmInst.AsmPush (encodeNumBytes off0), AsmInst.AsmOp "MSTORE"] from rfl] at hblock ⊢
    rw [show [AsmInst.AsmPush (encodeNumBytes off0), AsmInst.AsmOp "MSTORE"].length = 2 from rfl]
    exact doSpillTos_sim haslot rfl hwf hrel hlen hblock hcov hoff256 hdisj
  · -- dist ≠ 0: a leading SWAP then the spill
    have hd_pos : 0 < dist := Nat.pos_of_ne_zero hd0
    rcases hrel with ⟨hstack, hsp, hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
    simp only [doSpillAt, if_neg hd0, doSpillTos, haslot] at hspill
    rw [Prod.mk.injEq] at hspill
    obtain ⟨rfl, rfl⟩ := hspill
    -- block: [swap, push, mstore]
    have hep3 : executePlan [StackOp.SOSwap dist, StackOp.SOSpill off0]
        = [AsmInst.AsmOp (swapName dist), AsmInst.AsmPush (encodeNumBytes off0),
           AsmInst.AsmOp "MSTORE"] := rfl
    rw [hep3] at hblock ⊢
    rw [show [AsmInst.AsmOp (swapName dist), AsmInst.AsmPush (encodeNumBytes off0),
        AsmInst.AsmOp "MSTORE"].length = 3 from rfl]
    obtain ⟨hpchd, hblock_tail⟩ := asmBlockAt_cons_drop hblock
    have hpc0 : as.pc < prog.length := asmBlockAt_pc_lt hblock (by simp)
    have hg0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmOp (swapName dist) := by
      have := asmBlockAt_get hblock (j := 0) (by simp); simpa using this
    have hstk_len : dist < as.stack.length := by
      have := planStackRel_length hstack; omega
    -- swap step (explicit post-swap state)
    set as_sw : AsmState := { asmNext as with
      stack := (as.stack.set 0 (as.stack[dist]!)).set dist (as.stack[0]!) } with has_sw
    have hstep0 : asmStep offsetToPc prog as = AsmResult.AsmOK as_sw := by
      rw [asmStep_swap_ok hpc0 hg0 hd_pos hdist16 hstk_len]
      have hne : as.stack ≠ [] := by
        intro h; rw [h] at hstk_len; exact Nat.not_lt_zero _ hstk_len
      simp only [asmSwap, asmNext, has_sw, hd_pos, hstk_len, dif_pos]
      rw [head?_getD_eq_zero as.stack hne, List_get!_eq_get as.stack dist hstk_len,
        List_get!_eq_getElem?_getD as.stack 0]
    have hrun1 : runAsm 1 offsetToPc prog as = AsmResult.AsmOK as_sw := by
      rw [runAsm, hstep0]; rfl
    -- venomAsmRel for the swapped plan/asm states
    have hrel_sw : venomAsmRel labelOffsets { ps with stack := stackSwap dist ps.stack } vs as_sw := by
      refine ⟨planStackRel_swap hstack hd_pos hdlen, hsp, hmem, hacc, htr, hrd, hlog,
        hcc, htc, hbc, hcode, hprev⟩
    -- spill on the swapped state
    have hcov_sw : off0 + 32 ≤ as_sw.memory.size := hcov
    have hlen_sw : 0 < ({ ps with stack := stackSwap dist ps.stack } : PlanState).stack.length := by
      show 0 < (stackSwap dist ps.stack).length
      rw [stackSwap]; simp only [List.length_set]; omega
    have hblock_sw : asmBlockAt prog as_sw.pc
        [AsmInst.AsmPush (encodeNumBytes off0), AsmInst.AsmOp "MSTORE"] := by
      show asmBlockAt prog (as.pc + 1) _; exact hblock_tail
    obtain ⟨as2, hrun2, hrel2, hpc2⟩ :=
      doSpillTos_sim (ps := { ps with stack := stackSwap dist ps.stack }) haslot rfl hwf
        hrel_sw hlen_sw hblock_sw hcov_sw hoff256 hdisj
    refine ⟨as2, ?_, hrel2, ?_⟩
    · rw [show (3 : Nat) = 1 + 2 from rfl]; exact runAsm_compose hrun1 hrun2
    · rw [hpc2]; show as_sw.pc + 2 = as.pc + 3; rfl

/-- `doRestore op ps = (ops, ps')` simulates (mirrors HOL
    `restore_op_venom_asm_rel`). Restores a spilled operand from memory.
    Preconditions: `op` is in `ps.spilled` at its offset; `asmBlockAt`.
    Proof deferred pending `restoreAsmSteps` (PUSH+MLOAD). -/
theorem doRestore_sim {op ps ps' ops labelOffsets vs as prog}
    (hrestore : doRestore op ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hspillWf : ∀ o off, alookup' ps.spilled o = some off →
        32 ∣ off ∧ off + 32 ≤ as.memory.size ∧ off < 2 ^ 256) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as =
             AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  unfold doRestore at hrestore
  cases hlook : alookup' ps.spilled op with
  | none =>
    rw [hlook] at hrestore
    rw [Prod.mk.injEq] at hrestore
    obtain ⟨rfl, rfl⟩ := hrestore
    exact ⟨as, by simp [executePlan, runAsm], hrel, by simp [executePlan]⟩
  | some off =>
    rw [hlook] at hrestore
    rw [Prod.mk.injEq] at hrestore
    obtain ⟨rfl, rfl⟩ := hrestore
    obtain ⟨halign, hcov, hoff256⟩ := hspillWf op off hlook
    rcases hrel with ⟨hstack, hsp, hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
    obtain ⟨v, hopv, hmemv⟩ := hsp op off hlook
    have hep : executePlan [StackOp.SORestore off]
        = [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"] := rfl
    set pw := wordOfBytes (List.toByteArray
      (List.replicate (32 - (encodeNumBytes off).length) 0 ++ encodeNumBytes off)) with hpwdef
    have hpwoff : pw.toNat = off := pushed_offset_toNat off hoff256
    set as1 : AsmState := { asmNext as with stack := pw :: as.stack } with has1def
    set as2 : AsmState := { asmNext as1 with stack := v :: as.stack, memory := as.memory } with has2def
    -- block placement
    have hpc0 : as.pc < prog.length := asmBlockAt_pc_lt hblock (by rw [hep]; simp)
    have hg0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmPush (encodeNumBytes off) := by
      have := asmBlockAt_get hblock (j := 0) (by rw [hep]; simp)
      simpa [hep] using this
    have hpc1 : as1.pc < prog.length := by
      rcases hblock with ⟨hbl, _⟩; rw [hep] at hbl; show as.pc + 1 < prog.length; simp at hbl; omega
    have hg1 : prog.get ⟨as1.pc, hpc1⟩ = AsmInst.AsmOp "MLOAD" := by
      have := asmBlockAt_get hblock (j := 1) (by rw [hep]; simp)
      show prog.get ⟨as.pc + 1, hpc1⟩ = _
      simpa [hep] using this
    -- the two steps
    have hstep0 : asmStep offsetToPc prog as = AsmResult.AsmOK as1 := by
      rw [asmStep_push_ok hpc0 hg0]; rfl
    have hnoop : asmExpandMemory (off + 32) as.memory = as.memory :=
      asmExpandMemory_of_covered (off + 32) as.memory
        (by rw [rounded_add_32_of_aligned halign]; exact hcov)
    have hstep1 : asmStep offsetToPc prog as1 = AsmResult.AsmOK as2 := by
      rw [asmStep_mload_ok hpc1 hg1]
      show asmMload as1 = AsmResult.AsmOK as2
      have hs1stk : as1.stack = pw :: as.stack := rfl
      have hs1mem : as1.memory = as.memory := rfl
      simp only [asmMload, hs1stk, hs1mem, hpwoff, hnoop, hmemv]
      rfl
    -- run
    rw [hep, show [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"].length = 2 from rfl]
    have hrun : runAsm 2 offsetToPc prog as = AsmResult.AsmOK as2 := by
      rw [runAsm_succ_ok hpc0 hstep0, runAsm_succ_ok hpc1 hstep1, runAsm]
    refine ⟨as2, hrun, ?_, ?_⟩
    · exact ⟨planStackRel_push hstack hopv,
            fun o off' hlook' => hsp o off' (aremove_lookup_some ps.spilled op o off' hlook'),
            hmem, hacc, htr, hrd, hlog, hcc, htc, hbc, hcode, hprev⟩
    · show as2.pc = as.pc + 2
      rfl

/-! ## Plan fold-composition harness

`reorderPlan` / `popmanyPlan` build their op lists by a `List.foldl` whose step
appends the next chunk: `(ops, ps) ↦ (ops ++ delta, ps')`. The harness composes
the run block-by-block over such a fold (iterating `plan_seq_sim`); the
per-fold theorems then supply the per-step simulation. -/

/-- Accumulator law for the plan `foldl`: the initial op-prefix factors out. -/
theorem foldl_ops_acc {α} (g : PlanState → α → List StackOp × PlanState)
    (l : List α) (ops0 : List StackOp) (p : PlanState) :
    (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) (ops0, p))
    = (ops0 ++ (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], p)).1,
       (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], p)).2) := by
  induction l generalizing ops0 p with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.nil_append]
    rw [ih (ops0 ++ (g p a).1) (g p a).2, ih (g p a).1 (g p a).2, List.append_assoc]

/-- **Plan fold-composition harness.** If every step's emitted ops simulate (from
    any reachable plan/asm state, placed in `prog`), then the whole `foldl`'s ops
    simulate. `plan_seq_sim` iterated over a fold — the reusable engine under
    `reorderPlan_sim`. -/
theorem foldl_ops_sim {α} (lo : AssocList String Nat) (vs : VenomState) (prog : List AsmInst)
    (offsetToPc : AssocList Nat Nat)
    (g : PlanState → α → List StackOp × PlanState)
    (hstep : ∀ (a : α) (p : PlanState) (s : AsmState),
        venomAsmRel lo p vs s →
        asmBlockAt prog s.pc (executePlan (g p a).1) →
        ∃ s', runAsm (executePlan (g p a).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel lo (g p a).2 vs s' ∧
              s'.pc = s.pc + (executePlan (g p a).1).length)
    (l : List α) (ps0 : PlanState) (as0 : AsmState)
    (hrel0 : venomAsmRel lo ps0 vs as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1)) :
    ∃ as', runAsm
            (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1).length
            offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo
            (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).2 vs as' ∧
           as'.pc = as0.pc +
            (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1).length := by
  induction l generalizing ps0 as0 with
  | nil =>
    refine ⟨as0, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
  | cons a as ih =>
    have key : ∀ (p : PlanState),
        (a :: as).foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], p)
        = ((g p a).1 ++ (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g p a).2)).1,
           (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g p a).2)).2) := by
      intro p; rw [List.foldl_cons]; exact foldl_ops_acc g as (g p a).1 (g p a).2
    simp only [key ps0] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ := hstep a ps0 as0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g ps0 a).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc'⟩ := ih (g ps0 a).2 as1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_⟩
    · rw [List.length_append]
      exact runAsm_compose hrun1 hrun'
    · rw [List.length_append]; omega

/-- **Fold-simulation harness with a state invariant.** Like `foldl_ops_sim`, but the per-step asm sim
    `hstep` need only hold for plan states satisfying `Inv` (preserved by each step, `hInvStep`) — so a
    genuine reorder, whose per-`reorderOne` swap is only bounded on *reachable* states, can be discharged
    where the unrestricted `∀ p` `hstep` cannot (an unbounded `p` admits swap distances > 16). -/
theorem foldl_ops_sim_inv {α} (lo : AssocList String Nat) (vs : VenomState) (prog : List AsmInst)
    (offsetToPc : AssocList Nat Nat)
    (g : PlanState → α → List StackOp × PlanState)
    (Inv : PlanState → Prop)
    (hInvStep : ∀ (a : α) (p : PlanState), Inv p → Inv (g p a).2)
    (hstep : ∀ (a : α) (p : PlanState) (s : AsmState),
        Inv p → venomAsmRel lo p vs s →
        asmBlockAt prog s.pc (executePlan (g p a).1) →
        ∃ s', runAsm (executePlan (g p a).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel lo (g p a).2 vs s' ∧
              s'.pc = s.pc + (executePlan (g p a).1).length)
    (l : List α) (ps0 : PlanState) (as0 : AsmState)
    (hInv0 : Inv ps0)
    (hrel0 : venomAsmRel lo ps0 vs as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1)) :
    ∃ as', runAsm
            (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1).length
            offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo
            (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).2 vs as' ∧
           as'.pc = as0.pc +
            (executePlan (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)).1).length := by
  induction l generalizing ps0 as0 with
  | nil =>
    refine ⟨as0, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
  | cons a as ih =>
    have key : ∀ (p : PlanState),
        (a :: as).foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], p)
        = ((g p a).1 ++ (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g p a).2)).1,
           (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g p a).2)).2) := by
      intro p; rw [List.foldl_cons]; exact foldl_ops_acc g as (g p a).1 (g p a).2
    simp only [key ps0] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ := hstep a ps0 as0 hInv0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (as.foldl (fun acc b => (acc.1 ++ (g acc.2 b).1, (g acc.2 b).2)) ([], (g ps0 a).2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc'⟩ := ih (g ps0 a).2 as1 (hInvStep a ps0 hInv0) hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append]; omega

/-- `foldl_ops_sim` in `(ops, ps')`-equation form: once the fold is known to
    collapse to `(ops, ps')`, the run over `ops` simulates. Lets the per-fold
    theorems apply it directly to their `… = (ops, ps')` hypothesis. -/
theorem foldl_ops_sim' {α} (lo : AssocList String Nat) (vs : VenomState) (prog : List AsmInst)
    (offsetToPc : AssocList Nat Nat)
    (g : PlanState → α → List StackOp × PlanState)
    (hstep : ∀ (a : α) (p : PlanState) (s : AsmState),
        venomAsmRel lo p vs s →
        asmBlockAt prog s.pc (executePlan (g p a).1) →
        ∃ s', runAsm (executePlan (g p a).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel lo (g p a).2 vs s' ∧
              s'.pc = s.pc + (executePlan (g p a).1).length)
    {l : List α} {ps0 : PlanState} {as0 : AsmState} {ops : List StackOp} {ps' : PlanState}
    (hfold : (l.foldl (fun acc a => (acc.1 ++ (g acc.2 a).1, (g acc.2 a).2)) ([], ps0)) = (ops, ps'))
    (hrel0 : venomAsmRel lo ps0 vs as0)
    (hblock : asmBlockAt prog as0.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo ps' vs as' ∧
           as'.pc = as0.pc + (executePlan ops).length := by
  have hops : ops = _ := congrArg Prod.fst hfold.symm
  have hps' : ps' = _ := congrArg Prod.snd hfold.symm
  rw [hops, hps']
  exact foldl_ops_sim lo vs prog offsetToPc g hstep l ps0 as0 hrel0 (by rw [← hops]; exact hblock)

/-! ## vs-varying fold harness (instruction-level composition)

`foldl_ops_sim` composes per-step sims over a fold with a *fixed* `vs`. The block simulation
needs the analogue where each step also advances `vs` (via `stepInstBase`) — instructions are
folded threading `(ps, vs)` together. These mirror `foldl_ops_acc`/`foldl_ops_sim` with the
accumulator carrying `(ops, ps, vs)`. -/

/-- vs-varying analogue of `foldl_ops_acc`: pull the initial ops accumulator out of a fold
    whose accumulator threads `(ops, ps, vs)`. -/
theorem foldl_inst_acc {α} (g : PlanState → VenomState → α → List StackOp × PlanState × VenomState)
    (l : List α) (a0 : List StackOp) (p0 : PlanState) (v0 : VenomState) :
    l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                           (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) (a0, p0, v0)
      = (a0 ++ (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                  (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], p0, v0)).1,
         (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
            (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], p0, v0)).2) := by
  induction l generalizing a0 p0 v0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.nil_append]
    rw [ih (a0 ++ (g p0 v0 x).1) (g p0 v0 x).2.1 (g p0 v0 x).2.2,
        ih (g p0 v0 x).1 (g p0 v0 x).2.1 (g p0 v0 x).2.2, List.append_assoc]

/-- **vs-varying fold simulation** — the instruction-level composition engine for the block
    simulation. Composing a per-element sim (`hstep`, which advances `vs` via `g`) over a list
    yields a sim for the whole folded plan, threading `(ps, vs)` and the asm state. Mirrors
    `foldl_ops_sim` with `vs` varying (each `stepInstBase` advances `vs`). -/
theorem foldl_inst_sim {α} (lo : AssocList String Nat) (offsetToPc : AssocList Nat Nat)
    (prog : List AsmInst)
    (g : PlanState → VenomState → α → List StackOp × PlanState × VenomState)
    (hstep : ∀ (x : α) (p : PlanState) (v : VenomState) (s : AsmState),
        venomAsmRel lo p v s →
        asmBlockAt prog s.pc (executePlan (g p v x).1) →
        ∃ s', runAsm (executePlan (g p v x).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel lo (g p v x).2.1 (g p v x).2.2 s' ∧
              s'.pc = s.pc + (executePlan (g p v x).1).length)
    (l : List α) (ps0 : PlanState) (vs0 : VenomState) (as0 : AsmState)
    (hrel0 : venomAsmRel lo ps0 vs0 as0)
    (hblock : asmBlockAt prog as0.pc
      (executePlan (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                    (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], ps0, vs0)).1)) :
    ∃ as', runAsm (executePlan (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                    (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], ps0, vs0)).1).length
             offsetToPc prog as0 = AsmResult.AsmOK as' ∧
           venomAsmRel lo (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                    (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], ps0, vs0)).2.1
             (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                    (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], ps0, vs0)).2.2 as' ∧
           as'.pc = as0.pc + (executePlan (l.foldl (fun acc x => (acc.1 ++ (g acc.2.1 acc.2.2 x).1,
                    (g acc.2.1 acc.2.2 x).2.1, (g acc.2.1 acc.2.2 x).2.2)) ([], ps0, vs0)).1).length := by
  induction l generalizing ps0 vs0 as0 with
  | nil =>
    refine ⟨as0, ?_, ?_, ?_⟩
    · simp [executePlan, runAsm]
    · simpa using hrel0
    · simp [executePlan]
  | cons x xs ih =>
    have key : (x :: xs).foldl (fun acc y => (acc.1 ++ (g acc.2.1 acc.2.2 y).1,
                   (g acc.2.1 acc.2.2 y).2.1, (g acc.2.1 acc.2.2 y).2.2)) ([], ps0, vs0)
        = ((g ps0 vs0 x).1 ++ (xs.foldl (fun acc y => (acc.1 ++ (g acc.2.1 acc.2.2 y).1,
              (g acc.2.1 acc.2.2 y).2.1, (g acc.2.1 acc.2.2 y).2.2))
              ([], (g ps0 vs0 x).2.1, (g ps0 vs0 x).2.2)).1,
           (xs.foldl (fun acc y => (acc.1 ++ (g acc.2.1 acc.2.2 y).1,
              (g acc.2.1 acc.2.2 y).2.1, (g acc.2.1 acc.2.2 y).2.2))
              ([], (g ps0 vs0 x).2.1, (g ps0 vs0 x).2.2)).2) := by
      simp only [List.foldl_cons, List.nil_append]
      exact foldl_inst_acc g xs (g ps0 vs0 x).1 (g ps0 vs0 x).2.1 (g ps0 vs0 x).2.2
    simp only [key] at hblock ⊢
    rw [executePlan_append] at hblock ⊢
    obtain ⟨hb1, hb2⟩ := asmBlockAt_append hblock
    obtain ⟨as1, hrun1, hrel1, hpc1⟩ := hstep x ps0 vs0 as0 hrel0 hb1
    have hb2' : asmBlockAt prog as1.pc
        (executePlan (xs.foldl (fun acc y => (acc.1 ++ (g acc.2.1 acc.2.2 y).1,
            (g acc.2.1 acc.2.2 y).2.1, (g acc.2.1 acc.2.2 y).2.2))
            ([], (g ps0 vs0 x).2.1, (g ps0 vs0 x).2.2)).1) := by
      rw [hpc1]; exact hb2
    obtain ⟨as', hrun', hrel', hpc'⟩ := ih (g ps0 vs0 x).2.1 (g ps0 vs0 x).2.2 as1 hrel1 hb2'
    refine ⟨as', ?_, hrel', ?_⟩
    · rw [List.length_append]; exact runAsm_compose hrun1 hrun'
    · rw [List.length_append]; omega

/-! ## De-Option bridge for the generator's `instOps` fold

The block generator's instruction fold is `Option`-wrapped (`generateInstPlan` may fail on a
pre-codegen opcode). On a codegen-ready block it always succeeds, so the fold collapses to a
plain `(ops, ps)` fold — these lemmas extract per-step success and the cons decomposition from
`= some …`, the bridge to `foldl_inst_sim`'s plain fold. -/

/-- The generator's `Option (List StackOp × PlanState)` fold step. -/
def optFoldStep {α} (g : α → PlanState → Option (List StackOp × PlanState))
    (acc : Option (List StackOp × PlanState)) (a : α) : Option (List StackOp × PlanState) :=
  match acc with
  | none => none
  | some (ops, psc) =>
    match g a psc with
    | none => none
    | some (so, psn) => some (ops ++ so, psn)

/-- Once the option-fold reaches `none`, it stays `none`. -/
theorem foldl_optFold_none {α} (g : α → PlanState → Option (List StackOp × PlanState))
    (l : List α) : l.foldl (optFoldStep g) none = none := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons]; exact ih

/-- If the option-fold over `x :: xs` succeeds, the head step succeeded and the tail fold
    (from the head's output, with the head's ops prepended) succeeds to the same result. The
    inductive de-Option step for the generator's `instOps` fold. -/
theorem foldl_optFold_cons_some {α} (g : α → PlanState → Option (List StackOp × PlanState))
    (x : α) (xs : List α) (ops0 : List StackOp) (ps0 : PlanState)
    (res : List StackOp × PlanState)
    (h : (x :: xs).foldl (optFoldStep g) (some (ops0, ps0)) = some res) :
    ∃ so psn, g x ps0 = some (so, psn) ∧
      xs.foldl (optFoldStep g) (some (ops0 ++ so, psn)) = some res := by
  rw [List.foldl_cons] at h
  cases hg : g x ps0 with
  | none =>
    have hhead : optFoldStep g (some (ops0, ps0)) x = none := by simp only [optFoldStep, hg]
    rw [hhead, foldl_optFold_none] at h; exact absurd h (by simp)
  | some r =>
    obtain ⟨so, psn⟩ := r
    have hhead : optFoldStep g (some (ops0, ps0)) x = some (ops0 ++ so, psn) := by
      simp only [optFoldStep, hg]
    rw [hhead] at h
    exact ⟨so, psn, rfl, h⟩

set_option maxHeartbeats 1000000 in
/-- `reorderPlan targetOps ps = (ops, ps')` simulates, via the fold harness
    (mirrors HOL `reorderSimScript`). The residual `hstep` is the per-`reorderOne`
    simulation; closing it without that hypothesis needs `doSwap_sim` generalized
    to an arbitrary well-formed allocator (a `doRestore` inside the fold breaks
    the `freeSlots = []` the big-swap case relies on). -/
theorem reorderPlan_sim {targetOps ps ps' ops labelOffsets vs as prog}
    (hreorder : reorderPlan targetOps ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hstep : ∀ (i : Nat × Operand) (p : PlanState) (s : AsmState),
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (reorderOne () targetOps i.1 i.2 p).1) →
        ∃ s', runAsm (executePlan (reorderOne () targetOps i.1 i.2 p).1).length
                offsetToPc prog s = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (reorderOne () targetOps i.1 i.2 p).2 vs s' ∧
              s'.pc = s.pc + (executePlan (reorderOne () targetOps i.1 i.2 p).1).length) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have hrp : reorderPlan targetOps ps = targetOps.enum.foldl
      (fun acc a => (acc.1 ++ (reorderOne () targetOps a.1 a.2 acc.2).1,
                     (reorderOne () targetOps a.1 a.2 acc.2).2)) ([], ps) := by
    unfold reorderPlan
    congr 1
  rw [hrp] at hreorder
  exact foldl_ops_sim' labelOffsets vs prog offsetToPc
    (fun (p : PlanState) (i : Nat × Operand) => reorderOne () targetOps i.1 i.2 p)
    hstep hreorder hrel hblock

/-- The per-item pop step, abstracted so `popmanyPlan`'s fold matches the harness. -/
def gpop (p : PlanState) (v : Operand) : List StackOp × PlanState :=
  match stackGetDepth v p.stack with
  | none => ([], p)
  | some dist =>
    let (swapOps, ps') := if dist = 0 then ([], p) else doSwap dist p
    (swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack })

/-- `popmanyPlan`'s per-item fold step (its exact source lambda) equals the
    harness step built from `gpop` — the difference is `++`-assoc / `++ []`. -/
theorem popmany_step_eq :
    (fun (x : List StackOp × PlanState) (v : Operand) =>
      match x with
      | (ops, ps) =>
        match stackGetDepth v ps.stack with
        | none => (ops, ps)
        | some dist =>
          let (swapOps, ps') := if dist = 0 then ([], ps) else doSwap dist ps
          (ops ++ swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack }))
    = (fun acc v => (acc.1 ++ (gpop acc.2 v).1, (gpop acc.2 v).2)) := by
  funext x v
  obtain ⟨ops, p⟩ := x
  rcases hsd : stackGetDepth v p.stack with _ | dist
  · simp [gpop, hsd]
  · rcases hd0 : (if dist = 0 then (([], p) : List StackOp × PlanState) else doSwap dist p) with ⟨sw, p'⟩
    simp [gpop, hsd, hd0, List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- `popmanyPlan toPop ps = (ops, ps')` simulates (mirrors HOL `popmanyPlan`
    lemmas), via the fold harness. The empty case is trivial; the contiguous
    `doSwap n; POP n` case is `hcontig`; the per-item swap+pop folds go through
    `foldl_ops_sim` with the residual per-step hypothesis `hpopstep` (same
    allocator-generalisation caveat as `reorderPlan_sim`). -/
theorem popmanyPlan_sim {toPop ps ps' ops labelOffsets vs as prog}
    (hpop : popmanyPlan toPop ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hpopstep : ∀ (v : Operand) (p : PlanState) (s : AsmState),
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (gpop p v).1) →
        ∃ s', runAsm (executePlan (gpop p v).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (gpop p v).2 vs s' ∧
              s'.pc = s.pc + (executePlan (gpop p v).1).length)
    (hcontig :
        asmBlockAt prog as.pc
          (executePlan ((doSwap toPop.length ps).1 ++ [StackOp.SOPop toPop.length])) →
        ∃ as', runAsm (executePlan ((doSwap toPop.length ps).1
                  ++ [StackOp.SOPop toPop.length])).length offsetToPc prog as
                = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets
                { (doSwap toPop.length ps).2 with
                  stack := stackPop toPop.length (doSwap toPop.length ps).2.stack } vs as' ∧
              as'.pc = as.pc + (executePlan ((doSwap toPop.length ps).1
                  ++ [StackOp.SOPop toPop.length])).length) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have fold_case : ∀ (l : List Operand),
      (l.foldl (fun (x : List StackOp × PlanState) (v : Operand) =>
        match x with
        | (ops, ps) =>
          match stackGetDepth v ps.stack with
          | none => (ops, ps)
          | some dist =>
            let (swapOps, ps') := if dist = 0 then ([], ps) else doSwap dist ps
            (ops ++ swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack }))
        ([], ps)) = (ops, ps') →
      ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
             venomAsmRel labelOffsets ps' vs as' ∧
             as'.pc = as.pc + (executePlan ops).length := by
    intro l hfold
    rw [popmany_step_eq] at hfold
    exact foldl_ops_sim' labelOffsets vs prog offsetToPc gpop hpopstep hfold hrel hblock
  simp only [popmanyPlan] at hpop
  split at hpop
  · rw [Prod.mk.injEq] at hpop; obtain ⟨rfl, rfl⟩ := hpop
    exact ⟨as, by simp [executePlan, runAsm], hrel, by simp [executePlan]⟩
  · split at hpop
    · split at hpop
      · rw [Prod.mk.injEq] at hpop; obtain ⟨rfl, rfl⟩ := hpop
        exact hcontig hblock
      · exact fold_case _ hpop
    · exact fold_case _ hpop

set_option maxHeartbeats 1000000 in
/-- **`popmanyPlan` simulation with a state invariant** — the usable form of `popmanyPlan_sim`.

    `popmanyPlan_sim`'s `hpopstep` residual is quantified over *every* plan state, which is why it was
    never discharged and has no callers: at an unbounded stack depth a `doSwap` may exceed `SWAP16` and
    route through the temp spill region, dragging in `doSwap_sim`'s big-swap side condition, and there
    is no way to establish that for an arbitrary `p`.

    Here the per-step sim need only hold on states satisfying an invariant `Inv` that the step itself
    preserves (`foldl_ops_sim_inv`, built for exactly this). A caller instantiating `Inv` with a shallow
    stack bound gets every swap distance `≤ 16`, making the big-swap condition vacuous. `hcontig` (the
    closed-form contiguous branch — one `doSwap n` + one `SOPop n`) stays a parameter; it has no fold,
    so it carries no ∀-quantified residual and is dischargeable directly. -/
theorem popmanyPlan_sim_inv {toPop ps ps' ops labelOffsets vs as prog}
    (Inv : PlanState → Prop)
    (hInvStep : ∀ (v : Operand) (p : PlanState), Inv p → Inv (gpop p v).2)
    (hInv0 : Inv ps)
    (hpop : popmanyPlan toPop ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops))
    (hpopstep : ∀ (v : Operand) (p : PlanState) (s : AsmState),
        Inv p →
        venomAsmRel labelOffsets p vs s →
        asmBlockAt prog s.pc (executePlan (gpop p v).1) →
        ∃ s', runAsm (executePlan (gpop p v).1).length offsetToPc prog s
                = AsmResult.AsmOK s' ∧
              venomAsmRel labelOffsets (gpop p v).2 vs s' ∧
              s'.pc = s.pc + (executePlan (gpop p v).1).length)
    (hcontig :
        asmBlockAt prog as.pc
          (executePlan ((doSwap toPop.length ps).1 ++ [StackOp.SOPop toPop.length])) →
        ∃ as', runAsm (executePlan ((doSwap toPop.length ps).1
                  ++ [StackOp.SOPop toPop.length])).length offsetToPc prog as
                = AsmResult.AsmOK as' ∧
              venomAsmRel labelOffsets
                { (doSwap toPop.length ps).2 with
                  stack := stackPop toPop.length (doSwap toPop.length ps).2.stack } vs as' ∧
              as'.pc = as.pc + (executePlan ((doSwap toPop.length ps).1
                  ++ [StackOp.SOPop toPop.length])).length) :
    ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' ∧
           as'.pc = as.pc + (executePlan ops).length := by
  have fold_case : ∀ (l : List Operand),
      (l.foldl (fun (x : List StackOp × PlanState) (v : Operand) =>
        match x with
        | (ops, ps) =>
          match stackGetDepth v ps.stack with
          | none => (ops, ps)
          | some dist =>
            let (swapOps, ps') := if dist = 0 then ([], ps) else doSwap dist ps
            (ops ++ swapOps ++ [StackOp.SOPop 1], { ps' with stack := stackPop 1 ps'.stack }))
        ([], ps)) = (ops, ps') →
      ∃ as', runAsm (executePlan ops).length offsetToPc prog as = AsmResult.AsmOK as' ∧
             venomAsmRel labelOffsets ps' vs as' ∧
             as'.pc = as.pc + (executePlan ops).length := by
    intro l hfold
    rw [popmany_step_eq] at hfold
    have h := foldl_ops_sim_inv labelOffsets vs prog offsetToPc gpop Inv hInvStep hpopstep
      l ps as hInv0 hrel (by rw [hfold]; exact hblock)
    rw [hfold] at h
    exact h
  simp only [popmanyPlan] at hpop
  split at hpop
  · rw [Prod.mk.injEq] at hpop; obtain ⟨rfl, rfl⟩ := hpop
    exact ⟨as, by simp [executePlan, runAsm], hrel, by simp [executePlan]⟩
  · split at hpop
    · split at hpop
      · rw [Prod.mk.injEq] at hpop; obtain ⟨rfl, rfl⟩ := hpop
        exact hcontig hblock
      · exact fold_case _ hpop
    · exact fold_case _ hpop

/- Removed vestigial port artifacts (`asmStep_error_nonempty`,
   `execStackOp_step_sim`, `executePlan_sim`): they were unused by everything
   substantive (codegen_correct and the spill/restore sims don't reference them),
   and the "every `AsmError` message is non-empty" property is intractable to
   prove cheaply — `asmStep`'s ~50-arm string dispatch makes the case split blow
   up `whnf` (>8M heartbeats). If ever needed, the clean route is to refactor
   `asmStep`'s opcode dispatch into a handler table so the proof iterates over it
   rather than case-splitting 50 string literals. -/

end EvmYul.Venom.Hol.Codegen

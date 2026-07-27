import EvmYul.Venom.Hol.Types

/-!
# Liveness — the pure (fixpoint-free) helpers

Port of the phi/edge helpers from `vyper-hol main:venom/analysis/liveness/defs/
livenessDefsScript.sml` that the stack-plan generator uses directly (at a `JMP`
join point). `inputVarsFrom` rewrites a block's live-in set across a control edge,
substituting phi-related entries with the operand coming from the source block.

These are pure (they take the live-var list as input). The *fixpoint* that computes
those live-var lists — `live_vars_at = df_at (df_analyze_fuel …)` — needs the full
dataflow framework (+ cfg + worklist) and is a separate, larger port.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `phi_pairs`: `(label, value)` pairs from PHI operands `[Label l, Var v, …]`. -/
def phiPairs : List Operand → List (String × String)
  | []                                      => []
  | [_]                                     => []
  | Operand.Label l :: Operand.Var v :: rest => (l, v) :: phiPairs rest
  | _ :: _ :: rest                          => phiPairs rest

/-- `collect_phis`: the leading PHI instructions of a block. -/
def collectPhis : List Instruction → List Instruction
  | []          => []
  | inst :: rest => if inst.opcode = Opcode.PHI then inst :: collectPhis rest else []

/-- `build_phi_maps`: `(output-var → phi-index)` and `(phi-index → src-var for src_label)`. -/
def buildPhiMaps (srcLabel : String) (phis : List Instruction)
    : AssocList String Nat × AssocList Nat String :=
  phis.zipIdx.foldl
    (fun (maps : AssocList String Nat × AssocList Nat String) (phiI : Instruction × Nat) =>
      let (opMap, matching) := maps
      let (phi, i) := phiI
      let pairs := phiPairs phi.operands
      let opMap' := phi.outputs.foldl (fun m v => AssocList.insert String Nat m v i) opMap
      let matching' :=
        match pairs.find? (fun p => p.1 == srcLabel) with
        | some (_, v) => AssocList.insert Nat String matching i v
        | none        => matching
      (opMap', matching'))
    ([], [])

/-- `input_vars_from`: rewrite `baseLiveness` at a join, replacing phi-related entries
    with the source-matching operand (deduped by phi index). -/
def inputVarsFrom (srcLabel : String) (targetInstrs : List Instruction)
    (baseLiveness : List String) : List String :=
  let phis := collectPhis targetInstrs
  if phis.isEmpty then baseLiveness
  else
    let (opMap, matching) := buildPhiMaps srcLabel phis
    (baseLiveness.foldl
      (fun (acc : List String × List Nat) v =>
        let (res, placed) := acc
        match AssocList.lookup String Nat opMap v with
        | some phiIdx =>
          if placed.contains phiIdx then (res, placed)
          else
            match AssocList.lookup Nat String matching phiIdx with
            | some srcV => (res ++ [srcV], phiIdx :: placed)
            | none      => (res, placed)
        | none => (res ++ [v], placed))
      ([], [])).1

/-- **`inputVarsFrom` for a phi-free target** is just the base liveness: with no `PHI` instructions in
    the target, there is nothing to remap, so the expected entry layout is exactly the target's live
    vars at entry. The common case (phis live only at join points) — it reduces the well-scheduling
    obligation `S = inputVarsFrom …` to the cleaner `S = liveVarsAt …`. -/
theorem inputVarsFrom_no_phi (srcLabel : String) (targetInstrs : List Instruction)
    (baseLiveness : List String) (hphi : collectPhis targetInstrs = []) :
    inputVarsFrom srcLabel targetInstrs baseLiveness = baseLiveness := by
  unfold inputVarsFrom
  rw [hphi]
  simp

/-! ## Join agreement

A join with two or more predecessors gets no stack reconciliation from the plan generator
(`cleanStackPlan` fires only at a *single*-predecessor block), and it is compiled against whichever
predecessor the plan DFS reached first. Correctness therefore needs the join to be compiled *the same
way* whichever predecessor that is. `inputVarsFrom` is what makes that true: it hands each edge a
target layout of the same shape, differing only at the phi slots — and those are exactly the slots the
join's `SOPoke` renames to the phi outputs.

(This is the property whose *failure* was the phi-join miscompile: when the liveness transfer counted a
phi's operands as uses at the join, the phi output dropped out of the live set, `inputVarsFrom` had
nothing to rewrite, and the shape below degenerated. See `phi_join_agreement` in `GenBlockSimExample`
for the end-to-end witness on a real diamond.) -/

private theorem forall2_append {α β : Type} {R : α → β → Prop} {l1 r1 l2 r2 : List _}
    (h1 : List.Forall₂ R l1 r1) (h2 : List.Forall₂ R l2 r2) :
    List.Forall₂ R (l1 ++ l2) (r1 ++ r2) := by
  induction h1 with
  | nil => simpa using h2
  | cons hab _ ih => exact List.Forall₂.cons hab ih

/-- **The phi-output map is predecessor-independent.** `buildPhiMaps` assembles it from `phi.outputs`,
which mention no source label; only the `matching` map (phi index ↦ the source var arriving on *this*
edge) depends on `srcLabel`. This is why the two edges' folds below run in lockstep. -/
theorem buildPhiMaps_fst_indep (s1 s2 : String) (phis : List Instruction) :
    (buildPhiMaps s1 phis).1 = (buildPhiMaps s2 phis).1 := by
  unfold buildPhiMaps
  suffices h : ∀ (l : List (Instruction × Nat)) (m : AssocList String Nat)
      (n1 n2 : AssocList Nat String),
      (l.foldl (fun maps phiI =>
          let (opMap, matching) := maps
          let (phi, i) := phiI
          let pairs := phiPairs phi.operands
          let opMap' := phi.outputs.foldl (fun m v => AssocList.insert String Nat m v i) opMap
          let matching' :=
            match pairs.find? (fun p => p.1 == s1) with
            | some (_, v) => AssocList.insert Nat String matching i v
            | none        => matching
          (opMap', matching')) (m, n1)).1
        = (l.foldl (fun maps phiI =>
          let (opMap, matching) := maps
          let (phi, i) := phiI
          let pairs := phiPairs phi.operands
          let opMap' := phi.outputs.foldl (fun m v => AssocList.insert String Nat m v i) opMap
          let matching' :=
            match pairs.find? (fun p => p.1 == s2) with
            | some (_, v) => AssocList.insert Nat String matching i v
            | none        => matching
          (opMap', matching')) (m, n2)).1 from h phis.zipIdx [] [] []
  intro l
  induction l with
  | nil => intro m n1 n2; rfl
  | cons hd tl ih => intro m n1 n2; simp only [List.foldl_cons]; exact ih _ _ _

/-- **Slot-wise join agreement.** Two predecessors of the same join are handed target layouts that
agree *position by position*: at every slot they either name the same variable, or they name the two
edges' own sources for the **same** phi — and that is precisely the slot the join's `SOPoke` renames to
that phi's output. So the layouts coincide once the phis are applied, and it does not matter which
predecessor the plan DFS compiled the join against.

The single hypothesis is that the phi substitution is defined on the same indices for both edges —
i.e. every phi covers both predecessors, which is what a well-formed SSA producer emits. Both folds
run over the same base with the same `opMap` (`buildPhiMaps_fst_indep`), so they take the same branch
at every step and their `placed` sets stay equal; only the substituted *values* differ. -/
theorem inputVarsFrom_slot_agree (s1 s2 : String) (T : List Instruction) (base : List String)
    (hcov : ∀ i, (AssocList.lookup Nat String (buildPhiMaps s1 (collectPhis T)).2 i).isSome
               = (AssocList.lookup Nat String (buildPhiMaps s2 (collectPhis T)).2 i).isSome) :
    List.Forall₂
      (fun v1 v2 => v1 = v2 ∨ ∃ i,
          AssocList.lookup Nat String (buildPhiMaps s1 (collectPhis T)).2 i = some v1 ∧
          AssocList.lookup Nat String (buildPhiMaps s2 (collectPhis T)).2 i = some v2)
      (inputVarsFrom s1 T base) (inputVarsFrom s2 T base) := by
  unfold inputVarsFrom
  by_cases hp : (collectPhis T).isEmpty
  · simp only [hp, if_true]
    exact List.forall₂_same.2 (fun v _ => Or.inl rfl)
  · simp only [hp, if_false, Bool.false_eq_true]
    have hop := buildPhiMaps_fst_indep s1 s2 (collectPhis T)
    rw [← hop]
    set m1 := (buildPhiMaps s1 (collectPhis T)).2 with hm1
    set m2 := (buildPhiMaps s2 (collectPhis T)).2 with hm2
    set op := (buildPhiMaps s1 (collectPhis T)).1 with hopd
    set R : String → String → Prop := fun v1 v2 => v1 = v2 ∨ ∃ i,
        AssocList.lookup Nat String m1 i = some v1 ∧
        AssocList.lookup Nat String m2 i = some v2 with hR
    suffices h : ∀ (l : List String) (r1 r2 : List String) (pl : List Nat),
        List.Forall₂ R r1 r2 →
        List.Forall₂ R
          ((l.foldl (fun (acc : List String × List Nat) v =>
            match AssocList.lookup String Nat op v with
            | some i => if acc.2.contains i then acc
                        else match AssocList.lookup Nat String m1 i with
                             | some sv => (acc.1 ++ [sv], i :: acc.2)
                             | none    => acc
            | none => (acc.1 ++ [v], acc.2)) (r1, pl)).1)
          ((l.foldl (fun (acc : List String × List Nat) v =>
            match AssocList.lookup String Nat op v with
            | some i => if acc.2.contains i then acc
                        else match AssocList.lookup Nat String m2 i with
                             | some sv => (acc.1 ++ [sv], i :: acc.2)
                             | none    => acc
            | none => (acc.1 ++ [v], acc.2)) (r2, pl)).1) from h base [] [] [] List.Forall₂.nil
    intro l
    induction l with
    | nil => intro r1 r2 pl h; exact h
    | cons v tl ih =>
      intro r1 r2 pl h
      simp only [List.foldl_cons]
      cases hlk : AssocList.lookup String Nat op v with
      | none =>
        exact ih _ _ _ (forall2_append h (List.Forall₂.cons (Or.inl rfl) List.Forall₂.nil))
      | some i =>
        by_cases hc : pl.contains i
        · simp only [hc, if_true]; exact ih _ _ _ h
        · simp only [hc, if_false, Bool.false_eq_true]
          have hcv := hcov i
          cases h1 : AssocList.lookup Nat String m1 i with
          | none =>
            have h2 : AssocList.lookup Nat String m2 i = none := by
              rw [hm1, h1] at hcv; simp at hcv
              cases h2' : AssocList.lookup Nat String m2 i with
              | none => rfl
              | some x => rw [hm2, h2'] at hcv; simp at hcv
            simp only [h2]; exact ih _ _ _ h
          | some x1 =>
            have h2 : ∃ x2, AssocList.lookup Nat String m2 i = some x2 := by
              rw [hm1, h1] at hcv; simp at hcv
              cases h2' : AssocList.lookup Nat String m2 i with
              | none => rw [hm2, h2'] at hcv; simp at hcv
              | some x => exact ⟨x, rfl⟩
            obtain ⟨x2, h2⟩ := h2
            simp only [h2]
            exact ih _ _ _ (forall2_append h (List.Forall₂.cons (Or.inr ⟨i, h1, h2⟩) List.Forall₂.nil))

/-- **Every predecessor is asked for a layout of the same depth.** So the join's incoming stack shape
is predecessor-independent — the immediate corollary of `inputVarsFrom_slot_agree`. -/
theorem inputVarsFrom_length_eq (s1 s2 : String) (T : List Instruction) (base : List String)
    (hcov : ∀ i, (AssocList.lookup Nat String (buildPhiMaps s1 (collectPhis T)).2 i).isSome
               = (AssocList.lookup Nat String (buildPhiMaps s2 (collectPhis T)).2 i).isSome) :
    (inputVarsFrom s1 T base).length = (inputVarsFrom s2 T base).length :=
  (inputVarsFrom_slot_agree s1 s2 T base hcov).length_eq

/-- **Phi-free targets agree exactly.** With no phi to substitute, slot agreement collapses to
equality — the common case, and the reason most joins need no reconciliation at all. -/
theorem inputVarsFrom_eq_of_no_phi (s1 s2 : String) (T : List Instruction) (base : List String)
    (hphi : collectPhis T = []) :
    inputVarsFrom s1 T base = inputVarsFrom s2 T base := by
  rw [inputVarsFrom_no_phi s1 T base hphi, inputVarsFrom_no_phi s2 T base hphi]

end EvmYul.Venom.Hol.Codegen

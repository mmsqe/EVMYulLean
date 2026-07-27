/-
Execution Equivalence Proofs — Venom Core Proofs Layer 3

Port of vyper-hol/venom/proofs/execEquivProofsScript.sml

Proves that stepInstBase preserves state_equiv / result_equiv.
Key theorem: stepInstBase_result_equiv.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.StateEquiv
import EvmYul.Venom.Hol.StateEquivProofs
open EvmYul.Venom.Hol

set_option linter.unusedVariables false
set_option maxHeartbeats 0

namespace EvmYul.Venom.Hol

/-- `jumpTo` only changes `prevBb`, `currentBb`, `instIdx` — all outside `executionEquiv`.
    Since both sides jump to the same label, the new control-flow fields are equal. -/
theorem jumpTo_preserves {vars : Set String} {lbl : String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (jumpTo lbl s1) (jumpTo lbl s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  refine ⟨heq, rfl, rfl, ?_⟩
  show (jumpTo lbl s1).prevBb = (jumpTo lbl s2).prevBb
  rw [jumpTo, jumpTo, hbb]

/-- `haltState` only sets `halted := true`; both sides get the same value. -/
theorem haltState_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2) :
    executionEquiv vars (haltState s1) (haltState s2) := by
  rcases hst with ⟨heq, _⟩
  rcases heq with ⟨hv, hm, ht, _, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  unfold haltState
  refine ⟨hv, hm, ht, rfl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩

/-- `revertState` is identical to `haltState` (both set `halted := true`). -/
theorem revertState_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2) :
    executionEquiv vars (revertState s1) (revertState s2) := by
  rcases hst with ⟨heq, _⟩
  rcases heq with ⟨hv, hm, ht, _, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  unfold revertState
  refine ⟨hv, hm, ht, rfl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩

/-- `setReturndata` only changes `returndata`; both sides set the same rd → equal. -/
theorem setReturndata_preserves {vars : Set String} {rd : ByteArray}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (setReturndata rd s1) (setReturndata rd s2) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, _, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, hm, ht, hhl, rfl, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩

/-- `mstore` only changes `memory`; equal inputs produce equal inst.outputs. -/
theorem mstore_preserves {vars : Set String} {offset : Nat} {val : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (mstore offset val s1) (mstore offset val s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  rcases heq with ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  refine ⟨?_, hbb, hidx, hprev⟩
  refine ⟨hv, ?_, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  show (mstore offset val s1).memory = (mstore offset val s2).memory
  unfold mstore writeMemoryWithExpansion
  rw [hm]

/-- `mstore8` only changes `memory` (writes 1 byte); same pattern as `mstore`. -/
theorem mstore8_preserves {vars : Set String} {offset : Nat} {val : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (mstore8 offset val s1) (mstore8 offset val s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  rcases heq with ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  refine ⟨?_, hbb, hidx, hprev⟩
  refine ⟨hv, ?_, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  show (mstore8 offset val s1).memory = (mstore8 offset val s2).memory
  unfold mstore8 writeMemoryWithExpansion
  rw [hm]

/-- `sstore` only changes `accounts`; equal inputs → equal. -/
theorem sstore_preserves {vars : Set String} {key val : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (sstore key val s1) (sstore key val s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  rcases heq with ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  refine ⟨?_, hbb, hidx, hprev⟩
  refine ⟨hv, hm, ht, hhl, hrd, ?_, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  show (sstore key val s1).accounts = (sstore key val s2).accounts
  unfold sstore
  rw [hcc, hac]

/-- `tstore` only changes `transient`; equal inputs → equal. -/
theorem tstore_preserves {vars : Set String} {key val : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (tstore key val s1) (tstore key val s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  rcases heq with ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  refine ⟨?_, hbb, hidx, hprev⟩
  refine ⟨hv, hm, ?_, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  show (tstore key val s1).transient = (tstore key val s2).transient
  unfold tstore
  rw [hcc, ht]

-- Get field equalities from state_equiv
-- getStateFields pattern: rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩

/- ===== Helper: eval_operand under state_equiv ===== -/

/-- If two states are equivalent modulo `vars`, and operand `op` contains no
    variable in `vars`, then `evalOperand` gives the same result on both. -/
theorem evalOperand_equiv {vars : Set String} {op : Operand} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2)
    (hvars : ∀ x, Operand.Var x = op → x ∉ vars) :
    evalOperand op s1 = evalOperand op s2 := by
  rcases hst with ⟨heq, _⟩
  rcases heq with ⟨hv, _, _, _, _, _, _, _, _, _, _, _, hlb, _, _, _, _, _⟩
  cases op
  · rfl
  · simp only [evalOperand, hv _ (hvars _ rfl)]
  · simp only [evalOperand, hlb]

theorem evalOperand_mem_equiv {vars : Set String} {op : Operand} {ops : List Operand} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hmem : op ∈ ops) (hvars : ∀ x, Operand.Var x ∈ ops → x ∉ vars) :
  evalOperand op s1 = evalOperand op s2 := by
  apply evalOperand_equiv hst
  intro x h; apply hvars x
  rw [h]; exact hmem


/-- `updateVar out v` only changes the `vars` field. Since both sides write
    the same `out ↦ v`, variables outside `vars` remain equivalent. -/
theorem updateVar_preserves {vars : Set String} {out : String} {v : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (updateVar out v s1) (updateVar out v s2) := by
  rcases hst with ⟨heq, hbb, hidx, hprev⟩
  refine ⟨?_, hbb, hidx, hprev⟩
  rcases heq with ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  refine ⟨?_, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩
  intro v' hv'
  show AssocList.lookup String bytes32 (updateVar out v s1).vars v' =
       AssocList.lookup String bytes32 (updateVar out v s2).vars v'
  simp only [updateVar, ainsert, AssocList.insert, alookup, AssocList.lookup]
  by_cases hcase : v' = out
  · -- v' = out: insert puts (out, v) at head, lookup finds v on both sides
    subst hcase
    simp
  · -- v' ≠ out: lookup skips inserted (out, v) head on both sides
    have hne : out ≠ v' := fun h => hcase h.symm
    -- filter_lookup: for v' ≠ out, lookup v' (filter (λ(k,_)=> k != out) al) = lookup v' al
    have filter_lookup : ∀ (al : List (String × bytes32)),
        List.lookup v' (List.filter (fun (x : String × bytes32) => x.1 != out) al) = List.lookup v' al := by
      intro al
      induction al with
      | nil => rfl
      | cons hd tl ih =>
        obtain ⟨k, val⟩ := hd
        simp only [List.filter, List.lookup_cons]
        split
        · -- k != out = true: kept
          simp only [List.lookup_cons]
          split
          · rfl
          · exact ih
        · -- k != out = false: k = out, removed
          rename_i heq
          simp at heq
          have hkv : (v' == k) = false := by simp [heq, hcase]
          simp only [List.lookup_cons, hkv, if_false, ih]
    -- out == v' is false → if reduces to else → filter_lookup → lookup v' al
    have hbeq : (out == v') = false := by simp [hne]
    simp only [hbeq, filter_lookup s1.vars, filter_lookup s2.vars]
    simp
    -- Now: List.lookup v' s1.vars = List.lookup v' s2.vars
    -- hv: lookupVar v' s1 = lookupVar v' s2 → unfold → AssocList.lookup
    have assoc_list_eq : ∀ (al : List (String × bytes32)),
        AssocList.lookup String bytes32 al v' = List.lookup v' al := by
      intro al
      cases al with
      | nil => rfl
      | cons hd tl =>
        obtain ⟨k, val⟩ := hd
        simp only [AssocList.lookup, List.lookup_cons]
        -- Need: if (k == v') = true then some val else List.lookup v' tl
        --     = match v' == k with | true => some val | false => List.lookup v' tl
        -- k == v' ↔ v' == k by BEq.symm for String
        by_cases h : (v' == k) = true
        · -- v' == k → k == v' (symm) → both = some val
          have : (k == v') = true := by simp [BEq.symm, h]
          simp [this, h]
        · -- v' ≠ k → k ≠ v' → both = List.lookup v' tl
          have : (k == v') = false := by
            by_contra h2
            simp at h2
            -- k == v' → v' == k by symm
            have : (v' == k) = true := by simp [BEq.symm, h2]
            exact h this
          simp [this, h]
    unfold lookupVar alookup at hv
    have hv' := hv v' hv'
    rw [assoc_list_eq s1.vars, assoc_list_eq s2.vars] at hv'
    exact hv'

theorem updateVar_preserves' {vars : Set String} {out : String} {v1 v2 : bytes32}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) (hval : v1 = v2) :
    stateEquiv vars (updateVar out v1 s1) (updateVar out v2 s2) := by
  rw [hval]
  exact updateVar_preserves hst



/- ===== Pure Operations Preserve result_equiv ===== -/

theorem execPure1_result_equiv {vars : Set String} {f : bytes32 → bytes32} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars (execPure1 f inst s1) (execPure1 f inst s2) := by
  unfold execPure1
  cases h_ops : inst.operands
  · trivial
  · next op1 ops =>
    cases h_ops' : ops
    · -- ops = []: inst.operands = [op1]
      cases h_outs : inst.outputs
      · trivial
      · next out outs =>
        cases h_outs' : outs
        · -- outs = []: inst.outputs = [out]
          have hmem : op1 ∈ inst.operands := by
            simp [h_ops, h_ops']
          have h : evalOperand op1 s1 = evalOperand op1 s2 :=
            evalOperand_mem_equiv hst hmem hvars
          simp
          rw [h]
          cases evalOperand op1 s2 with
          | none => trivial
          | some v =>
            simp [resultEquiv, liftResult]
            apply updateVar_preserves hst
        · trivial
    · trivial

theorem execPure2_result_equiv {vars : Set String} {f : bytes32 → bytes32 → bytes32} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars (execPure2 f inst s1) (execPure2 f inst s2) := by
  unfold execPure2
  cases h_ops : inst.operands
  · trivial
  · next op1 ops =>
    cases h_ops' : ops
    · trivial
    · next op2 ops' =>
      cases h_ops'' : ops'
      · -- inst.operands = [op1, op2]
        cases h_outs : inst.outputs
        · trivial
        · next out outs =>
          cases h_outs' : outs
          · -- inst.outputs = [out]
            have hmem1 : op1 ∈ inst.operands := by
              simp [h_ops, h_ops']
            have hmem2 : op2 ∈ inst.operands := by
              simp [h_ops, h_ops', h_ops'']
            have h1 : evalOperand op1 s1 = evalOperand op1 s2 :=
              evalOperand_mem_equiv hst hmem1 hvars
            have h2 : evalOperand op2 s1 = evalOperand op2 s2 :=
              evalOperand_mem_equiv hst hmem2 hvars
            simp
            rw [h1, h2]
            cases evalOperand op1 s2 with
            | none => trivial
            | some v1 =>
              cases evalOperand op2 s2 with
              | none => trivial
              | some v2 =>
                simp [resultEquiv, liftResult]
                apply updateVar_preserves hst
          · trivial
      · trivial

theorem execPure3_result_equiv {vars : Set String} {f : bytes32 → bytes32 → bytes32 → bytes32} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars (execPure3 f inst s1) (execPure3 f inst s2) := by
  unfold execPure3
  cases h_ops : inst.operands
  · trivial
  · next op1 ops =>
    cases h_ops' : ops
    · trivial
    · next op2 ops' =>
      cases h_ops'' : ops'
      · trivial
      · next op3 ops'' =>
        cases h_ops''' : ops''
        · -- inst.operands = [op1, op2, op3]
          cases h_outs : inst.outputs
          · trivial
          · next out outs =>
            cases h_outs' : outs
            · -- inst.outputs = [out]
              have hmem1 : op1 ∈ inst.operands := by
                simp [h_ops, h_ops']
              have hmem2 : op2 ∈ inst.operands := by
                simp [h_ops, h_ops', h_ops'']
              have hmem3 : op3 ∈ inst.operands := by
                simp [h_ops, h_ops', h_ops'', h_ops''']
              have h1 : evalOperand op1 s1 = evalOperand op1 s2 :=
                evalOperand_mem_equiv hst hmem1 hvars
              have h2 : evalOperand op2 s1 = evalOperand op2 s2 :=
                evalOperand_mem_equiv hst hmem2 hvars
              have h3 : evalOperand op3 s1 = evalOperand op3 s2 :=
                evalOperand_mem_equiv hst hmem3 hvars
              simp
              rw [h1, h2, h3]
              cases evalOperand op1 s2 with
              | none => trivial
              | some v1 =>
                cases evalOperand op2 s2 with
                | none => trivial
                | some v2 =>
                  cases evalOperand op3 s2 with
                  | none => trivial
                  | some v3 =>
                    simp [resultEquiv, liftResult]
                    apply updateVar_preserves hst
            · trivial
        · trivial

/- ===== Read Operations Preserve result_equiv =====

  For read0 (no operand): the read function reads from state fields that
  state_equiv guarantees equal (call context, tx context, block context, etc.)
  So the read value is the same, and update_var preserves state_equiv. -/

theorem execRead0_result_equiv {vars : Set String} {f : VenomState → bytes32} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hf_reads_context : f s1 = f s2) :
  resultEquiv vars (execRead0 f inst s1) (execRead0 f inst s2) := by
  unfold execRead0
  cases h_outs : inst.outputs
  · trivial
  · next out outs =>
    cases h_outs' : outs
    · -- inst.outputs = [out]
      simp [resultEquiv, liftResult, hf_reads_context]
      apply updateVar_preserves hst
    · trivial

theorem execRead1_result_equiv {vars : Set String} {f : bytes32 → VenomState → bytes32} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hf_reads_context : ∀ v, f v s1 = f v s2) :
  resultEquiv vars (execRead1 f inst s1) (execRead1 f inst s2) := by
  unfold execRead1
  cases h_ops : inst.operands
  · trivial
  · next op1 ops =>
    cases h_ops' : ops
    · -- inst.operands = [op1]
      cases h_outs : inst.outputs
      · trivial
      · next out outs =>
        cases h_outs' : outs
        · -- inst.outputs = [out]
          have hmem : op1 ∈ inst.operands := by
            simp [h_ops, h_ops']
          have h : evalOperand op1 s1 = evalOperand op1 s2 :=
            evalOperand_mem_equiv hst hmem hvars
          simp
          rw [h]
          cases evalOperand op1 s2 with
          | none => trivial
          | some v =>
            simp [resultEquiv, liftResult, hf_reads_context]
            apply updateVar_preserves hst
        · trivial
    · trivial

theorem execWrite2_result_equiv {vars : Set String} {f : bytes32 → bytes32 → VenomState → VenomState} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hf_preserves : ∀ v1 v2, stateEquiv vars (f v1 v2 s1) (f v1 v2 s2)) :
  resultEquiv vars (execWrite2 f inst s1) (execWrite2 f inst s2) := by
  unfold execWrite2
  cases h_ops : inst.operands
  · trivial
  · next op1 ops =>
    cases h_ops' : ops
    · trivial
    · next op2 ops' =>
      cases h_ops'' : ops'
      · -- inst.operands = [op1, op2]
        have hmem1 : op1 ∈ inst.operands := by
          simp [h_ops, h_ops']
        have hmem2 : op2 ∈ inst.operands := by
          simp [h_ops, h_ops', h_ops'']
        have h1 : evalOperand op1 s1 = evalOperand op1 s2 :=
          evalOperand_mem_equiv hst hmem1 hvars
        have h2 : evalOperand op2 s1 = evalOperand op2 s2 :=
          evalOperand_mem_equiv hst hmem2 hvars
        simp
        rw [h1, h2]
        cases evalOperand op1 s2 with
        | none => trivial
        | some v1 =>
          cases evalOperand op2 s2 with
          | none => trivial
          | some v2 =>
            simp [resultEquiv, liftResult]
            exact hf_preserves v1 v2
      · trivial


/-- If two states are equivalent, lists of operands evaluate identically. -/
theorem evalOperands_equiv {vars : Set String} {ops : List Operand} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ ops → x ∉ vars) :
  evalOperands ops s1 = evalOperands ops s2 := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp [evalOperands]
    have hop : evalOperand op s1 = evalOperand op s2 :=
      evalOperand_mem_equiv hst (by simp) hvars
    simp [hop]
    have hvars' : ∀ x, Operand.Var x ∈ ops → x ∉ vars := by
      intro x hx; apply hvars x; simp [hx]
    have hops : evalOperands ops s1 = evalOperands ops s2 := ih hvars'
    simp [hops]


-- `readMemory` only reads from `s.memory`; equal memory → equal result.
theorem readMemory_equiv {off sz : Nat} {s1 s2 : VenomState}
    (hmem : s1.memory = s2.memory) :
    readMemory off sz s1 = readMemory off sz s2 := by
  simp [readMemory, hmem]

-- `writeMemoryWithExpansion` only changes `memory`; equal inputs → equal.
theorem writeMemoryWithExpansion_preserves {vars : Set String} {dst : Nat} {bytes : ByteArray}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (writeMemoryWithExpansion dst bytes s1) (writeMemoryWithExpansion dst bytes s2) := by
  unfold writeMemoryWithExpansion
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, ?_, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  simp [hm]

-- `mcopy` only changes `memory`; equal inputs → equal.
theorem mcopy_preserves {vars : Set String} {dst src sz : Nat}
    {s1 s2 : VenomState} (hst : stateEquiv vars s1 s2) :
    stateEquiv vars (mcopy dst src sz s1) (mcopy dst src sz s2) := by
  unfold mcopy
  have hmem : s1.memory = s2.memory := by
    rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
    exact hm
  have hrd : readMemory src sz s1 = readMemory src sz s2 := readMemory_equiv hmem
  rw [hrd]
  exact writeMemoryWithExpansion_preserves hst

-- Update one field of VenomState, given proof the new values are equal.
theorem fieldUpdate_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2)
    {im1 im2 : AssocList Nat bytes32} (him_eq : im1 = im2) :
    stateEquiv vars ({ s1 with immutables := im1 }) ({ s2 with immutables := im2 }) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him_eq, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩

/-- Updating both states' `accounts` to the same value preserves `stateEquiv`
    (the `SELFDESTRUCT` building block; re-added after the vendored rewrite). -/
theorem accountsUpdate_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2)
    {a1 a2 : Accounts} (ha_eq : a1 = a2) :
    stateEquiv vars ({ s1 with accounts := a1 }) ({ s2 with accounts := a2 }) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, hm, ht, hhl, hrd, ha_eq, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩

theorem logsUpdate_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2)
    {l1 l2 : List Event} (hlg_eq : l1 = l2) :
    stateEquiv vars ({ s1 with logs := l1 }) ({ s2 with logs := l2 }) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg_eq, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩

theorem allocasUpdate_preserves {vars : Set String} {s1 s2 : VenomState}
    (hst : stateEquiv vars s1 s2)
    {a1 a2 : AssocList Nat (Nat × Nat)} (hal_eq : a1 = a2)
    {n1 n2 : Nat} (hnx_eq : n1 = n2) :
    stateEquiv vars ({ s1 with allocas := a1, allocaNext := n1 })
                   ({ s2 with allocas := a2, allocaNext := n2 }) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  refine ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal_eq, hnx_eq⟩, hbb, hidx, hprev⟩


/-- MCOPY: match 3 operands, evaluate, mcopy. -/
theorem mcopy_stepInstBase_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hm : s1.memory = s2.memory) :
  resultEquiv vars
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s1, evalOperand opSrc s1, evalOperand opSize s1 with
       | some dst, some src, some sz => ExecResult.OK (mcopy dst.toNat src.toNat sz.toNat s1)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "mcopy requires 3 operands")
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s2, evalOperand opSrc s2, evalOperand opSize s2 with
       | some dst, some src, some sz => ExecResult.OK (mcopy dst.toNat src.toNat sz.toNat s2)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "mcopy requires 3 operands") := by
  have hmem : s1.memory = s2.memory := hm
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opDst ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opSrc rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSize rest2 =>
        cases h_ops4 : rest2
        · have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsrc : evalOperand opSrc s1 = evalOperand opSrc s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          cases hd : evalOperand opDst s1
          · simp [← hdst, hd, resultEquiv, liftResult]
          · next dst =>
            cases hs : evalOperand opSrc s1
            · simp [← hsrc, hs, resultEquiv, liftResult]
            · next src =>
              cases hz : evalOperand opSize s1
              · simp [← hsize, hz, resultEquiv, liftResult]
              · next sz =>
                simpa [← hdst, hd, ← hsrc, hs, ← hsize, hz, resultEquiv, liftResult] using mcopy_preserves hst
        · simp [resultEquiv, liftResult]

/-- ISTORE: match 2 operands, evaluate, update immutables. -/
theorem istore_stepInstBase_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (him : s1.immutables = s2.immutables) :
  resultEquiv vars
    (match inst.operands with
     | [offsetOp, valOp] =>
       match evalOperand offsetOp s1, evalOperand valOp s1 with
       | some off, some v => ExecResult.OK { s1 with immutables := ainsert s1.immutables off.toNat v }
       | _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "istore requires 2 operands")
    (match inst.operands with
     | [offsetOp, valOp] =>
       match evalOperand offsetOp s2, evalOperand valOp s2 with
       | some off, some v => ExecResult.OK { s2 with immutables := ainsert s2.immutables off.toNat v }
       | _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "istore requires 2 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next offsetOp ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next valOp rest =>
      cases h_ops3 : rest
      · have hoff : evalOperand offsetOp s1 = evalOperand offsetOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        have hval : evalOperand valOp s1 = evalOperand valOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        cases ho : evalOperand offsetOp s1
        · simp [← hoff, ho, resultEquiv, liftResult]
        · next off =>
          cases hv : evalOperand valOp s1
          · simp [← hval, hv, resultEquiv, liftResult]
          · next v =>
            simpa [← hoff, ho, ← hval, hv, resultEquiv, liftResult] using fieldUpdate_preserves hst (by rw [him])
      · simp [resultEquiv, liftResult]

/-- JMP: match single Label operand, jumpTo. -/
theorem jmp_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands with | [Operand.Label lbl] => ExecResult.OK (jumpTo lbl s1) | _ => ExecResult.Error "jmp requires label operand")
    (match inst.operands with | [Operand.Label lbl] => ExecResult.OK (jumpTo lbl s2) | _ => ExecResult.Error "jmp requires label operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next op1 ops =>
    cases h_ops2 : ops
    · cases op1
      · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
        exact jumpTo_preserves hst
    · simp [resultEquiv, liftResult]

/-- JNZ: match 3 operands (cond + 2 labels), evaluate cond, conditional jump. -/
theorem jnz_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands with
     | [condOp, Operand.Label ifNonzero, Operand.Label ifZero] =>
       match evalOperand condOp s1 with
       | some cond => if (cond != ⟨0⟩) = true then ExecResult.OK (jumpTo ifNonzero s1) else ExecResult.OK (jumpTo ifZero s1)
       | none => ExecResult.Error "undefined condition"
     | _ => ExecResult.Error "jnz requires cond and 2 labels")
    (match inst.operands with
     | [condOp, Operand.Label ifNonzero, Operand.Label ifZero] =>
       match evalOperand condOp s2 with
       | some cond => if (cond != ⟨0⟩) = true then ExecResult.OK (jumpTo ifNonzero s2) else ExecResult.OK (jumpTo ifZero s2)
       | none => ExecResult.Error "undefined condition"
     | _ => ExecResult.Error "jnz requires cond and 2 labels") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next condOp ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next lbl1 rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next lbl2 rest2 =>
        cases h_ops4 : rest2
        · cases lbl1
          · simp [resultEquiv, liftResult]
          · simp [resultEquiv, liftResult]
          · next ifNonzero =>
            cases lbl2
            · simp [resultEquiv, liftResult]
            · simp [resultEquiv, liftResult]
            · next ifZero =>
              have hcond : evalOperand condOp s1 = evalOperand condOp s2 :=
                evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
              cases h : evalOperand condOp s1
              · simp [← hcond, h, resultEquiv, liftResult]
              · next cond =>
                simp [← hcond, h]
                by_cases hz : (cond != ⟨0⟩) = true
                · simp only [if_pos hz]; exact jumpTo_preserves hst
                · simp only [if_neg hz]; exact jumpTo_preserves hst
        · simp [resultEquiv, liftResult]

/-- DJMP: dynamic jump with extractLabels. -/
theorem djmp_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands with
     | selectorOp :: labelOps =>
       match evalOperand selectorOp s1, extractLabels labelOps with
       | some idx, some labels =>
         let i := idx.toNat
         if h : i < labels.length then ExecResult.OK (jumpTo (labels.get ⟨i, h⟩) s1)
         else ExecResult.Error "djmp: index out of range"
       | _, _ => ExecResult.Error "djmp: undefined operand or invalid labels"
     | _ => ExecResult.Error "djmp requires selector and labels")
    (match inst.operands with
     | selectorOp :: labelOps =>
       match evalOperand selectorOp s2, extractLabels labelOps with
       | some idx, some labels =>
         let i := idx.toNat
         if h : i < labels.length then ExecResult.OK (jumpTo (labels.get ⟨i, h⟩) s2)
         else ExecResult.Error "djmp: index out of range"
       | _, _ => ExecResult.Error "djmp: undefined operand or invalid labels"
     | _ => ExecResult.Error "djmp requires selector and labels") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next selectorOp labelOps =>
    have hsel : evalOperand selectorOp s1 = evalOperand selectorOp s2 :=
      evalOperand_mem_equiv hst (by simp [h_ops]) hvars
    cases hlabels : extractLabels labelOps
    · cases h : evalOperand selectorOp s1
      · simp [hlabels, ← hsel, h, resultEquiv, liftResult]
      · next idx => simp [hlabels, ← hsel, h, resultEquiv, liftResult]
    · next labels =>
      cases h : evalOperand selectorOp s1
      · simp [← hsel, h, resultEquiv, liftResult]
      · next idx =>
        simp [← hsel, h, hlabels]
        by_cases hbound : idx.toNat < labels.length
        · simp only [dif_pos hbound, resultEquiv, liftResult]
          exact jumpTo_preserves hst
        · simp only [dif_neg hbound, resultEquiv, liftResult]

/-- PARAM: access function parameters. -/
theorem param_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hpr : s1.params = s2.params) :
  resultEquiv vars
    (match inst.operands with
     | [Operand.Lit idx] =>
       let i := idx.toNat
       if h : i < s1.params.length then
         match inst.outputs with | [out] => ExecResult.OK (updateVar out (s1.params.get ⟨i, h⟩) s1) | _ => ExecResult.Error "param requires single output"
       else ExecResult.Error "param: index out of range"
     | _ => ExecResult.Error "param requires literal index")
    (match inst.operands with
     | [Operand.Lit idx] =>
       let i := idx.toNat
       if h : i < s2.params.length then
         match inst.outputs with | [out] => ExecResult.OK (updateVar out (s2.params.get ⟨i, h⟩) s2) | _ => ExecResult.Error "param requires single output"
       else ExecResult.Error "param: index out of range"
     | _ => ExecResult.Error "param requires literal index") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next firstOp rest =>
    cases h_ops3 : rest
    · cases firstOp
      · next idx =>
        have hpr_eq : s1.params = s2.params := hpr
        by_cases hbound : idx.toNat < s1.params.length
        · have hbound2 : idx.toNat < s2.params.length := by rw [← hpr_eq]; exact hbound
          simp only [dif_pos hbound, dif_pos hbound2]
          cases inst.outputs
          · simp [resultEquiv, liftResult]
          · next out outs =>
            cases outs
            · simp only [hpr, resultEquiv, liftResult]
              refine updateVar_preserves' hst ?_
              simp [hpr]
            · simp [resultEquiv, liftResult]
        · have hbound2 : ¬ idx.toNat < s2.params.length := by rw [← hpr_eq]; exact hbound
          simp only [dif_neg hbound, dif_neg hbound2, resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
    · simp [resultEquiv, liftResult]

/-- RETURN: read memory, halt with returndata. -/
theorem return_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hm : s1.memory = s2.memory) :
  resultEquiv vars
    (match inst.operands with
     | [offOp, szOp] =>
       match evalOperand offOp s1, evalOperand szOp s1 with
       | some off, some sz => ExecResult.Halt (haltState (setReturndata (readMemory off.toNat sz.toNat s1) s1))
       | _, _ => ExecResult.Error "return: undefined operand"
     | _ => ExecResult.Error "return requires 2 operands")
    (match inst.operands with
     | [offOp, szOp] =>
       match evalOperand offOp s2, evalOperand szOp s2 with
       | some off, some sz => ExecResult.Halt (haltState (setReturndata (readMemory off.toNat sz.toNat s2) s2))
       | _, _ => ExecResult.Error "return: undefined operand"
     | _ => ExecResult.Error "return requires 2 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next offOp ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next szOp rest =>
      cases h_ops3 : rest
      · have hoff : evalOperand offOp s1 = evalOperand offOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        have hsz : evalOperand szOp s1 = evalOperand szOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        cases ho : evalOperand offOp s1
        · simp [← hoff, ho, resultEquiv, liftResult]
        · next off =>
          cases hs : evalOperand szOp s1
          · simp [← hsz, hs, resultEquiv, liftResult]
          · next sz =>
            simpa [← hoff, ho, ← hsz, hs, readMemory_equiv hm, resultEquiv, liftResult] using haltState_preserves (setReturndata_preserves hst)
      · simp [resultEquiv, liftResult]

/-- REVERT: read memory, revert. -/
theorem revert_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hm : s1.memory = s2.memory) :
  resultEquiv vars
    (match inst.operands with
     | [offOp, szOp] =>
       match evalOperand offOp s1, evalOperand szOp s1 with
       | some off, some sz => ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory off.toNat sz.toNat s1) s1))
       | _, _ => ExecResult.Error "revert: undefined operand"
     | _ => ExecResult.Error "revert requires 2 operands")
    (match inst.operands with
     | [offOp, szOp] =>
       match evalOperand offOp s2, evalOperand szOp s2 with
       | some off, some sz => ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata (readMemory off.toNat sz.toNat s2) s2))
       | _, _ => ExecResult.Error "revert: undefined operand"
     | _ => ExecResult.Error "revert requires 2 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next offOp ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next szOp rest =>
      cases h_ops3 : rest
      · have hoff : evalOperand offOp s1 = evalOperand offOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        have hsz : evalOperand szOp s1 = evalOperand szOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        cases ho : evalOperand offOp s1
        · simp [← hoff, ho, resultEquiv, liftResult]
        · next off =>
          cases hs : evalOperand szOp s1
          · simp [← hsz, hs, resultEquiv, liftResult]
          · next sz =>
            simpa [← hoff, ho, ← hsz, hs, readMemory_equiv hm, resultEquiv, liftResult] using revertState_preserves (setReturndata_preserves hst)
      · simp [resultEquiv, liftResult]

/-- ASSIGN: single operand, single output, updateVar. -/
theorem assign_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands, inst.outputs with
     | [op1], [out] =>
       match evalOperand op1 s1 with | some v => ExecResult.OK (updateVar out v s1) | none => ExecResult.Error "undefined operand"
     | _, _ => ExecResult.Error "assign requires 1 operand and single output")
    (match inst.operands, inst.outputs with
     | [op1], [out] =>
       match evalOperand op1 s2 with | some v => ExecResult.OK (updateVar out v s2) | none => ExecResult.Error "undefined operand"
     | _, _ => ExecResult.Error "assign requires 1 operand and single output") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next op1 ops =>
    cases h_ops2 : ops
    · cases inst.outputs
      · simp [resultEquiv, liftResult]
      · next out outs =>
        cases outs
        · have hop : evalOperand op1 s1 = evalOperand op1 s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2]) hvars
          cases h : evalOperand op1 s1
          · simp [← hop, h, resultEquiv, liftResult]
          · next v => simpa [← hop, h, resultEquiv, liftResult] using updateVar_preserves hst
        · simp [resultEquiv, liftResult]
    · simp [resultEquiv, liftResult]

/-- ALLOCA: allocate memory. -/
theorem alloca_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hal : s1.allocas = s2.allocas) (hnx : s1.allocaNext = s2.allocaNext) :
  resultEquiv vars
    (match inst.operands with
     | [Operand.Lit allocSize] =>
       match inst.outputs with
       | [out] =>
         match alookup s1.allocas inst.id with
         | some (offset, _sz) => ExecResult.OK (updateVar out (UInt256.ofNat offset) s1)
         | none =>
           let offset := s1.allocaNext
           let sz := allocSize.toNat
           let s' := { s1 with allocas := ainsert s1.allocas inst.id (offset, sz), allocaNext := offset + sz }
           ExecResult.OK (updateVar out (UInt256.ofNat offset) s')
       | _ => ExecResult.Error "alloca requires single output"
     | _ => ExecResult.Error "alloca requires 1 literal operand")
    (match inst.operands with
     | [Operand.Lit allocSize] =>
       match inst.outputs with
       | [out] =>
         match alookup s2.allocas inst.id with
         | some (offset, _sz) => ExecResult.OK (updateVar out (UInt256.ofNat offset) s2)
         | none =>
           let offset := s2.allocaNext
           let sz := allocSize.toNat
           let s' := { s2 with allocas := ainsert s2.allocas inst.id (offset, sz), allocaNext := offset + sz }
           ExecResult.OK (updateVar out (UInt256.ofNat offset) s')
       | _ => ExecResult.Error "alloca requires single output"
     | _ => ExecResult.Error "alloca requires 1 literal operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next firstOp rest =>
    cases h_ops3 : rest
    · cases firstOp
      · next allocSize =>
        cases inst.outputs
        · simp [resultEquiv, liftResult]
        · next out outs =>
          cases outs
          · have hal_eq : s1.allocas = s2.allocas := hal
            have hnx_eq : s1.allocaNext = s2.allocaNext := hnx
            cases halook : alookup s1.allocas inst.id
            · have halook2 : alookup s2.allocas inst.id = none := by rw [← hal_eq]; exact halook
              simp only [halook, halook2]
              have hoffset : s1.allocaNext = s2.allocaNext := hnx_eq
              simp only [hoffset]
              have hallocas : ainsert s1.allocas inst.id (s2.allocaNext, UInt256.toNat allocSize) =
                              ainsert s2.allocas inst.id (s2.allocaNext, UInt256.toNat allocSize) := by rw [hal_eq]
              have hs' : stateEquiv vars
                ({ s1 with allocas := ainsert s1.allocas inst.id (s2.allocaNext, UInt256.toNat allocSize),
                           allocaNext := s2.allocaNext + UInt256.toNat allocSize })
                ({ s2 with allocas := ainsert s2.allocas inst.id (s2.allocaNext, UInt256.toNat allocSize),
                           allocaNext := s2.allocaNext + UInt256.toNat allocSize }) := by
                have hnx2 : s2.allocaNext + UInt256.toNat allocSize = s2.allocaNext + UInt256.toNat allocSize := rfl
                exact allocasUpdate_preserves hst hallocas hnx2
              exact updateVar_preserves hs'
            · next alloc_info =>
              have halook2 : alookup s2.allocas inst.id = some alloc_info := by rw [← hal_eq]; exact halook
              simp only [halook, halook2]
              exact updateVar_preserves hst
          · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]
    · simp [resultEquiv, liftResult]

/-- CALLDATACOPY: copy calldata to memory. -/
theorem calldatacopy_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hcc : s1.callCtx = s2.callCtx) :
  resultEquiv vars
    (match inst.operands with
     | [opDestOffset, opOffset, opSize] =>
       match evalOperand opDestOffset s1, evalOperand opOffset s1, evalOperand opSize s1 with
       | some destOffset, some offset, some sizeVal =>
         let data := s1.callCtx.calldata
         let size := sizeVal.toNat
         let srcOffset := offset.toNat
         let srcBA : ByteArray := ⟨data.toArray⟩
         let bytes := srcBA.readWithPadding srcOffset size
         ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s1)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "calldatacopy requires 3 operands")
    (match inst.operands with
     | [opDestOffset, opOffset, opSize] =>
       match evalOperand opDestOffset s2, evalOperand opOffset s2, evalOperand opSize s2 with
       | some destOffset, some offset, some sizeVal =>
         let data := s2.callCtx.calldata
         let size := sizeVal.toNat
         let srcOffset := offset.toNat
         let srcBA : ByteArray := ⟨data.toArray⟩
         let bytes := srcBA.readWithPadding srcOffset size
         ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s2)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "calldatacopy requires 3 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opDst ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opOff rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSize rest2 =>
        cases h_ops4 : rest2
        · have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hoff : evalOperand opOff s1 = evalOperand opOff s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          cases hd : evalOperand opDst s1
          · simp [← hdst, hd, resultEquiv, liftResult]
          · next dst =>
            cases ho : evalOperand opOff s1
            · simp [← hoff, ho, resultEquiv, liftResult]
            · next off =>
              cases hs : evalOperand opSize s1
              · simp [← hsize, hs, resultEquiv, liftResult]
              · next sz =>
                simpa [← hdst, hd, ← hoff, ho, ← hsize, hs, hcc, resultEquiv, liftResult] using writeMemoryWithExpansion_preserves hst
        · simp [resultEquiv, liftResult]

/-- CODECOPY: copy code to memory. -/
theorem codecopy_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hcd : s1.code = s2.code) :
  resultEquiv vars
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s1, evalOperand opSrc s1, evalOperand opSize s1 with
       | some dst, some src, some sizeVal =>
         let srcBA : ByteArray := ⟨s1.code.toArray⟩
         let size := sizeVal.toNat
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s1)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "codecopy requires 3 operands")
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s2, evalOperand opSrc s2, evalOperand opSize s2 with
       | some dst, some src, some sizeVal =>
         let srcBA : ByteArray := ⟨s2.code.toArray⟩
         let size := sizeVal.toNat
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s2)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "codecopy requires 3 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opDst ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opSrc rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSize rest2 =>
        cases h_ops4 : rest2
        · have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsrc : evalOperand opSrc s1 = evalOperand opSrc s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          cases hd : evalOperand opDst s1
          · simp [← hdst, hd, resultEquiv, liftResult]
          · next dst =>
            cases hs : evalOperand opSrc s1
            · simp [← hsrc, hs, resultEquiv, liftResult]
            · next src =>
              cases hz : evalOperand opSize s1
              · simp [← hsize, hz, resultEquiv, liftResult]
              · next sz =>
                simpa [← hdst, hd, ← hsrc, hs, ← hsize, hz, hcd, resultEquiv, liftResult] using writeMemoryWithExpansion_preserves hst
        · simp [resultEquiv, liftResult]

/-- EXTCODECOPY: copy external code to memory. -/
theorem extcodecopy_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hac : s1.accounts = s2.accounts) :
  resultEquiv vars
    (match inst.operands with
     | [opAddr, opDst, opSrc, opSize] =>
       match evalOperand opAddr s1, evalOperand opDst s1, evalOperand opSrc s1, evalOperand opSize s1 with
       | some addr, some dst, some src, some sizeVal =>
         let code := (lookupAccount (AccountAddress.ofUInt256 addr) s1.accounts).code
         let size := sizeVal.toNat
         let srcBA : ByteArray := ⟨code.toArray⟩
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s1)
       | _, _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "extcodecopy requires 4 operands")
    (match inst.operands with
     | [opAddr, opDst, opSrc, opSize] =>
       match evalOperand opAddr s2, evalOperand opDst s2, evalOperand opSrc s2, evalOperand opSize s2 with
       | some addr, some dst, some src, some sizeVal =>
         let code := (lookupAccount (AccountAddress.ofUInt256 addr) s2.accounts).code
         let size := sizeVal.toNat
         let srcBA : ByteArray := ⟨code.toArray⟩
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s2)
       | _, _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "extcodecopy requires 4 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opAddr ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opDst rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSrc rest2 =>
        cases h_ops4 : rest2
        · simp [resultEquiv, liftResult]
        · next opSize rest3 =>
          cases h_ops5 : rest3
          · have haddr : evalOperand opAddr s1 = evalOperand opAddr s2 :=
              evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4, h_ops5]) hvars
            have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
              evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4, h_ops5]) hvars
            have hsrc : evalOperand opSrc s1 = evalOperand opSrc s2 :=
              evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4, h_ops5]) hvars
            have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
              evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4, h_ops5]) hvars
            cases ha : evalOperand opAddr s1
            · simp [← haddr, ha, resultEquiv, liftResult]
            · next addr =>
              cases hd : evalOperand opDst s1
              · simp [← hdst, hd, resultEquiv, liftResult]
              · next dst =>
                cases hs : evalOperand opSrc s1
                · simp [← hsrc, hs, resultEquiv, liftResult]
                · next src =>
                  cases hz : evalOperand opSize s1
                  · simp [← hsize, hz, resultEquiv, liftResult]
                  · next sz =>
                    simpa [← haddr, ha, ← hdst, hd, ← hsrc, hs, ← hsize, hz, hac, resultEquiv, liftResult] using writeMemoryWithExpansion_preserves hst
          · simp [resultEquiv, liftResult]

/-- RETURNDATACOPY: copy returndata to memory (with bounds check). -/
theorem returndatacopy_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hrd : s1.returndata = s2.returndata) :
  resultEquiv vars
    (match inst.operands with
     | [opDestOffset, opOffset, opSize] =>
       match evalOperand opDestOffset s1, evalOperand opOffset s1, evalOperand opSize s1 with
       | some destOffset, some offset, some sizeVal =>
         let size := sizeVal.toNat
         let srcOffset := offset.toNat
         if srcOffset + size > s1.returndata.size then
           ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s1))
         else
           let bytes := s1.returndata.readWithPadding srcOffset size
           ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s1)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "returndatacopy requires 3 operands")
    (match inst.operands with
     | [opDestOffset, opOffset, opSize] =>
       match evalOperand opDestOffset s2, evalOperand opOffset s2, evalOperand opSize s2 with
       | some destOffset, some offset, some sizeVal =>
         let size := sizeVal.toNat
         let srcOffset := offset.toNat
         if srcOffset + size > s2.returndata.size then
           ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s2))
         else
           let bytes := s2.returndata.readWithPadding srcOffset size
           ExecResult.OK (writeMemoryWithExpansion destOffset.toNat bytes s2)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "returndatacopy requires 3 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opDst ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opOff rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSize rest2 =>
        cases h_ops4 : rest2
        · have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hoff : evalOperand opOff s1 = evalOperand opOff s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          cases hd : evalOperand opDst s1
          · simp [← hdst, hd, resultEquiv, liftResult]
          · next dst =>
            cases ho : evalOperand opOff s1
            · simp [← hoff, ho, resultEquiv, liftResult]
            · next off =>
              cases hs : evalOperand opSize s1
              · simp [← hsize, hs, resultEquiv, liftResult]
              · next sz =>
                simp [← hdst, hd, ← hoff, ho, ← hsize, hs]
                by_cases hcheck : off.toNat + sz.toNat > s1.returndata.size
                · have hcheck2 : off.toNat + sz.toNat > s2.returndata.size := by rw [← hrd]; exact hcheck
                  simp only [if_pos hcheck, if_pos hcheck2]
                  exact ⟨rfl, haltState_preserves (setReturndata_preserves hst)⟩
                · have hcheck2 : ¬ (off.toNat + sz.toNat > s2.returndata.size) := by rw [← hrd]; exact hcheck
                  simp only [if_neg hcheck, if_neg hcheck2]
                  simp only [hrd]
                  exact writeMemoryWithExpansion_preserves hst
        · simp [resultEquiv, liftResult]

/-- SHA3: keccak256 of memory region, store result. -/
theorem sha3_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hm : s1.memory = s2.memory) :
  resultEquiv vars
    (match inst.operands with
     | [opOffset, opSize] =>
       match evalOperand opOffset s1, evalOperand opSize s1 with
       | some offset, some sizeVal =>
         match inst.outputs with
         | [out] =>
           let bytes := readMemory offset.toNat sizeVal.toNat s1
           let hash := keccak256 bytes
           ExecResult.OK (updateVar out hash s1)
         | _ => ExecResult.Error "sha3 requires single output"
       | _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "sha3 requires 2 operands")
    (match inst.operands with
     | [opOffset, opSize] =>
       match evalOperand opOffset s2, evalOperand opSize s2 with
       | some offset, some sizeVal =>
         match inst.outputs with
         | [out] =>
           let bytes := readMemory offset.toNat sizeVal.toNat s2
           let hash := keccak256 bytes
           ExecResult.OK (updateVar out hash s2)
         | _ => ExecResult.Error "sha3 requires single output"
       | _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "sha3 requires 2 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next offOp ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next szOp rest =>
      cases h_ops3 : rest
      · have hoff : evalOperand offOp s1 = evalOperand offOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        have hsz : evalOperand szOp s1 = evalOperand szOp s2 :=
          evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3]) hvars
        cases ho : evalOperand offOp s1
        · simp [← hoff, ho, resultEquiv, liftResult]
        · next off =>
          cases hs : evalOperand szOp s1
          · simp [← hsz, hs, resultEquiv, liftResult]
          · next sz =>
            simp [← hoff, ho, ← hsz, hs]
            cases inst.outputs
            · simp [resultEquiv, liftResult]
            · next out outs =>
              cases outs
              · simp only [readMemory_equiv hm]
                exact updateVar_preserves hst
              · simp [resultEquiv, liftResult]
      · simp [resultEquiv, liftResult]

/-- LOG: emit log event. -/
theorem log_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hm : s1.memory = s2.memory) (hcc : s1.callCtx = s2.callCtx) (hlg : s1.logs = s2.logs) :
  resultEquiv vars
    (match inst.operands with
     | Operand.Lit tc :: rest =>
       let n := tc.toNat
       if rest.length != n + 2 then ExecResult.Error "log: wrong operand count"
       else
         let offsetOp := rest[0]!
         let sizeOp := rest[1]!
         let topicOps := rest.drop 2
         match evalOperand offsetOp s1, evalOperand sizeOp s1, evalOperands topicOps s1 with
         | some off, some sz, some topics =>
           let data := (readMemory off.toNat sz.toNat s1).toList
           let ev : Event := { logger := s1.callCtx.contract, topics := topics, data := data }
           ExecResult.OK { s1 with logs := s1.logs ++ [ev] }
         | _, _, _ => ExecResult.Error "log: undefined operand"
     | _ => ExecResult.Error "log requires Lit topic_count as first operand")
    (match inst.operands with
     | Operand.Lit tc :: rest =>
       let n := tc.toNat
       if rest.length != n + 2 then ExecResult.Error "log: wrong operand count"
       else
         let offsetOp := rest[0]!
         let sizeOp := rest[1]!
         let topicOps := rest.drop 2
         match evalOperand offsetOp s2, evalOperand sizeOp s2, evalOperands topicOps s2 with
         | some off, some sz, some topics =>
           let data := (readMemory off.toNat sz.toNat s2).toList
           let ev : Event := { logger := s2.callCtx.contract, topics := topics, data := data }
           ExecResult.OK { s2 with logs := s2.logs ++ [ev] }
         | _, _, _ => ExecResult.Error "log: undefined operand"
     | _ => ExecResult.Error "log requires Lit topic_count as first operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next firstOp rest =>
    cases firstOp
    · next tc =>
      by_cases hcount : (rest.length != tc.toNat + 2) = true
      · simp only [if_pos hcount, resultEquiv, liftResult]
      · simp only [if_neg hcount]
        have hlen_eq : rest.length = tc.toNat + 2 := by
          have h' : (rest.length != tc.toNat + 2) = false := by
            by_contra h; apply hcount; exact (by simpa using h : (rest.length != tc.toNat + 2) = true)
          simpa using h'
        have hlen0 : 0 < rest.length := by
          rw [hlen_eq]; exact Nat.succ_pos (tc.toNat + 1)
        have hlen1 : 1 < rest.length := by
          rw [hlen_eq]; exact Nat.succ_lt_succ (Nat.succ_pos tc.toNat)
        have h0mem : rest[0]! ∈ rest := by
          rw [getElem!_pos rest 0 hlen0]; exact List.getElem_mem hlen0
        have h1mem : rest[1]! ∈ rest := by
          rw [getElem!_pos rest 1 hlen1]; exact List.getElem_mem hlen1
        have hoffOp : evalOperand rest[0]! s1 = evalOperand rest[0]! s2 := by
          apply evalOperand_equiv hst
          intro x hx; apply hvars x; rw [h_ops, hx]; exact List.mem_cons_of_mem _ h0mem
        have hszOp : evalOperand rest[1]! s1 = evalOperand rest[1]! s2 := by
          apply evalOperand_equiv hst
          intro x hx; apply hvars x; rw [h_ops, hx]; exact List.mem_cons_of_mem _ h1mem
        have htopics : evalOperands (rest.drop 2) s1 = evalOperands (rest.drop 2) s2 := by
          apply evalOperands_equiv hst
          intro x hx; apply hvars x; rw [h_ops]; right; exact List.mem_of_mem_drop hx
        cases ho : evalOperand rest[0]! s1
        · rw [← hoffOp, ho]; simp [resultEquiv, liftResult]
        · next off =>
          cases hs : evalOperand rest[1]! s1
          · rw [← hszOp, hs]; simp [resultEquiv, liftResult]
          · next sz =>
            cases ht : evalOperands (rest.drop 2) s1
            · rw [← htopics, ht]; simp [resultEquiv, liftResult]
            · next topics =>
              rw [← hoffOp, ho, ← hszOp, hs, ← htopics, ht]
              have hdata : (readMemory off.toNat sz.toNat s1).toList = (readMemory off.toNat sz.toNat s2).toList := by
                simp [readMemory_equiv hm]
              have hcontract : s1.callCtx.contract = s2.callCtx.contract := by rw [hcc]
              simp only [hdata, hcontract, hlg]
              refine logsUpdate_preserves hst ?_
              rfl
    · simp [resultEquiv, liftResult]
    · simp [resultEquiv, liftResult]

/-- RET: return from internal function. -/
theorem ret_stepInstBase_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match evalOperands inst.operands s1 with
     | some retVals => ExecResult.IntRet retVals s1
     | none => ExecResult.Error "ret: undefined return value")
    (match evalOperands inst.operands s2 with
     | some retVals => ExecResult.IntRet retVals s2
     | none => ExecResult.Error "ret: undefined return value") := by
  have heq : evalOperands inst.operands s1 = evalOperands inst.operands s2 :=
    evalOperands_equiv hst hvars
  cases h_ops : evalOperands inst.operands s1
  · rw [← heq, h_ops]
    simp only [resultEquiv, liftResult]
  · next retVals =>
    rw [← heq, h_ops]
    exact ⟨hst.1, rfl⟩


/-- SELFDESTRUCT: destroy contract, transfer funds. -/
theorem selfdestruct_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hac : s1.accounts = s2.accounts) (hcc : s1.callCtx = s2.callCtx) :
  resultEquiv vars
    (match inst.operands with
     | [addrOp] =>
       match evalOperand addrOp s1 with
       | some addr =>
         let self := s1.callCtx.contract
         let selfAcct := lookupAccount self s1.accounts
         let bal := selfAcct.balance
         let beneficiary := AccountAddress.ofUInt256 addr
         let benAcct := lookupAccount beneficiary s1.accounts
         let newAccounts := ainsert s1.accounts self { selfAcct with balance := 0 }
         let newAccounts := ainsert newAccounts beneficiary { benAcct with balance := benAcct.balance + bal }
         ExecResult.Halt (haltState { s1 with accounts := newAccounts })
       | none => ExecResult.Error "selfdestruct: undefined operand"
     | _ => ExecResult.Error "selfdestruct requires 1 operand")
    (match inst.operands with
     | [addrOp] =>
       match evalOperand addrOp s2 with
       | some addr =>
         let self := s2.callCtx.contract
         let selfAcct := lookupAccount self s2.accounts
         let bal := selfAcct.balance
         let beneficiary := AccountAddress.ofUInt256 addr
         let benAcct := lookupAccount beneficiary s2.accounts
         let newAccounts := ainsert s2.accounts self { selfAcct with balance := 0 }
         let newAccounts := ainsert newAccounts beneficiary { benAcct with balance := benAcct.balance + bal }
         ExecResult.Halt (haltState { s2 with accounts := newAccounts })
       | none => ExecResult.Error "selfdestruct: undefined operand"
     | _ => ExecResult.Error "selfdestruct requires 1 operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next addrOp ops =>
    cases h_ops2 : ops
    · have haddr : evalOperand addrOp s1 = evalOperand addrOp s2 :=
        evalOperand_mem_equiv hst (by simp [h_ops, h_ops2]) hvars
      cases h : evalOperand addrOp s1
      · simp [← haddr, h, resultEquiv, liftResult]
      · next addr =>
        -- both sides `Halt (haltState {s with accounts := newAccounts})`; `newAccounts`
        -- is a pure function of `accounts` / `callCtx.contract` / `addr`, all equal.
        simp only [← haddr, h, resultEquiv, liftResult]
        refine haltState_preserves (accountsUpdate_preserves hst ?_)
        rw [hac, hcc]
    · next _ rest => cases rest <;> simp [resultEquiv, liftResult]

/-- ASSERT: conditional revert. -/
theorem assert_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands with
     | [condOp] =>
       match evalOperand condOp s1 with
       | some cond =>
         if cond = ⟨0⟩ then ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata ByteArray.empty s1))
         else ExecResult.OK s1
       | none => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "assert requires 1 operand")
    (match inst.operands with
     | [condOp] =>
       match evalOperand condOp s2 with
       | some cond =>
         if cond = ⟨0⟩ then ExecResult.Abort AbortType.RevertAbort (revertState (setReturndata ByteArray.empty s2))
         else ExecResult.OK s2
       | none => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "assert requires 1 operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next condOp ops =>
    cases h_ops2 : ops
    · have hcond : evalOperand condOp s1 = evalOperand condOp s2 :=
        evalOperand_mem_equiv hst (by simp [h_ops, h_ops2]) hvars
      cases h : evalOperand condOp s1
      · simp [← hcond, h, resultEquiv, liftResult]
      · next cond =>
        simp [← hcond, h]
        by_cases hz : cond = ⟨0⟩
        · simp only [if_pos hz]
          exact ⟨rfl, revertState_preserves (setReturndata_preserves hst)⟩
        · simp only [if_neg hz]
          exact hst
    · next _ rest => cases rest <;> simp [resultEquiv, liftResult]

/-- ASSERT_UNREACHABLE: conditional halt. -/
theorem assert_unreachable_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars) :
  resultEquiv vars
    (match inst.operands with
     | [condOp] =>
       match evalOperand condOp s1 with
       | some cond =>
         if cond = ⟨0⟩ then ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s1))
         else ExecResult.OK s1
       | none => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "assert_unreachable requires 1 operand")
    (match inst.operands with
     | [condOp] =>
       match evalOperand condOp s2 with
       | some cond =>
         if cond = ⟨0⟩ then ExecResult.Abort AbortType.ExHaltAbort (haltState (setReturndata ByteArray.empty s2))
         else ExecResult.OK s2
       | none => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "assert_unreachable requires 1 operand") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next condOp ops =>
    cases h_ops2 : ops
    · have hcond : evalOperand condOp s1 = evalOperand condOp s2 :=
        evalOperand_mem_equiv hst (by simp [h_ops, h_ops2]) hvars
      cases h : evalOperand condOp s1
      · simp [← hcond, h, resultEquiv, liftResult]
      · next cond =>
        simp [← hcond, h]
        by_cases hz : cond = ⟨0⟩
        · simp only [if_pos hz]
          exact ⟨rfl, haltState_preserves (setReturndata_preserves hst)⟩
        · simp only [if_neg hz]
          exact hst
    · next _ rest => cases rest <;> simp [resultEquiv, liftResult]

/-- DLOADBYTES: copy data section to memory. -/
theorem dloadbytes_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2) (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hds : s1.dataSection = s2.dataSection) :
  resultEquiv vars
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s1, evalOperand opSrc s1, evalOperand opSize s1 with
       | some dst, some src, some sizeVal =>
         let size := sizeVal.toNat
         let srcBA : ByteArray := ⟨s1.dataSection.toArray⟩
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s1)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "dloadbytes requires 3 operands")
    (match inst.operands with
     | [opDst, opSrc, opSize] =>
       match evalOperand opDst s2, evalOperand opSrc s2, evalOperand opSize s2 with
       | some dst, some src, some sizeVal =>
         let size := sizeVal.toNat
         let srcBA : ByteArray := ⟨s2.dataSection.toArray⟩
         let bytes := srcBA.readWithPadding src.toNat size
         ExecResult.OK (writeMemoryWithExpansion dst.toNat bytes s2)
       | _, _, _ => ExecResult.Error "undefined operand"
     | _ => ExecResult.Error "dloadbytes requires 3 operands") := by
  cases h_ops : inst.operands
  · simp [resultEquiv, liftResult]
  · next opDst ops =>
    cases h_ops2 : ops
    · simp [resultEquiv, liftResult]
    · next opSrc rest =>
      cases h_ops3 : rest
      · simp [resultEquiv, liftResult]
      · next opSize rest2 =>
        cases h_ops4 : rest2
        · have hdst : evalOperand opDst s1 = evalOperand opDst s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsrc : evalOperand opSrc s1 = evalOperand opSrc s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          have hsize : evalOperand opSize s1 = evalOperand opSize s2 :=
            evalOperand_mem_equiv hst (by simp [h_ops, h_ops2, h_ops3, h_ops4]) hvars
          cases hd : evalOperand opDst s1
          · simp [← hdst, hd, resultEquiv, liftResult]
          · next dst =>
            cases hs : evalOperand opSrc s1
            · simp [← hsrc, hs, resultEquiv, liftResult]
            · next src =>
              cases hz : evalOperand opSize s1
              · simp [← hsize, hz, resultEquiv, liftResult]
              · next sz =>
                simpa [← hdst, hd, ← hsrc, hs, ← hsize, hz, hds, resultEquiv, liftResult] using writeMemoryWithExpansion_preserves hst
        · simp [resultEquiv, liftResult]

/- ===== KEY THEOREM: stepInstBase preserves result_equiv ===== -/

/--
Main theorem: If two Venom states are equivalent (modulo vars),
and no operand variable is in the exception set, then stepping
any instruction (except INVOKE/ext calls) produces equivalent results.
-/
theorem stepInstBase_result_equiv {vars : Set String} {inst : Instruction} {s1 s2 : VenomState}
  (hst : stateEquiv vars s1 s2)
  (hvars : ∀ x, Operand.Var x ∈ inst.operands → x ∉ vars)
  (hno_invoke : inst.opcode ≠ Opcode.INVOKE) :
  resultEquiv vars (stepInstBase inst s1) (stepInstBase inst s2) := by
  rcases hst with ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  let hst : stateEquiv vars s1 s2 :=
    ⟨⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩, hbb, hidx, hprev⟩
  unfold stepInstBase
  match inst.opcode with
  | Opcode.ADD => exact execPure2_result_equiv hst hvars
  | Opcode.SUB => exact execPure2_result_equiv hst hvars
  | Opcode.MUL => exact execPure2_result_equiv hst hvars
  | Opcode.Div => exact execPure2_result_equiv hst hvars
  | Opcode.SDIV => exact execPure2_result_equiv hst hvars
  | Opcode.Mod => exact execPure2_result_equiv hst hvars
  | Opcode.SMOD => exact execPure2_result_equiv hst hvars
  | Opcode.Exp => exact execPure2_result_equiv hst hvars
  | Opcode.ADDMOD => exact execPure3_result_equiv hst hvars
  | Opcode.MULMOD => exact execPure3_result_equiv hst hvars
  | Opcode.EQ => exact execPure2_result_equiv hst hvars
  | Opcode.LT => exact execPure2_result_equiv hst hvars
  | Opcode.GT => exact execPure2_result_equiv hst hvars
  | Opcode.SLT => exact execPure2_result_equiv hst hvars
  | Opcode.SGT => exact execPure2_result_equiv hst hvars
  | Opcode.ISZERO => exact execPure1_result_equiv hst hvars
  | Opcode.AND => exact execPure2_result_equiv hst hvars
  | Opcode.OR => exact execPure2_result_equiv hst hvars
  | Opcode.XOR => exact execPure2_result_equiv hst hvars
  | Opcode.NOT => exact execPure1_result_equiv hst hvars
  | Opcode.SHL => exact execPure2_result_equiv hst hvars
  | Opcode.SHR => exact execPure2_result_equiv hst hvars
  | Opcode.SAR => exact execPure2_result_equiv hst hvars
  | Opcode.SIGNEXTEND => exact execPure2_result_equiv hst hvars
  | Opcode.BYTE => exact execPure2_result_equiv hst hvars
  | Opcode.MLOAD => exact execRead1_result_equiv hst hvars (by intro v; simpa [hm, mload, readMemory])
  | Opcode.MSTORE => exact execWrite2_result_equiv hst hvars (λ v1 v2 => mstore_preserves hst)
  | Opcode.MSTORE8 => exact execWrite2_result_equiv hst hvars (λ v1 v2 => mstore8_preserves hst)
  | Opcode.MCOPY => exact mcopy_stepInstBase_result_equiv hst hvars hm
  | Opcode.MEMTOP => exact execRead0_result_equiv hst (by simp [hm])
  | Opcode.SLOAD => exact execRead1_result_equiv hst hvars (by intro v; simpa [hac, hcc, sload, contractStorage, alookup])
  | Opcode.SSTORE => exact execWrite2_result_equiv hst hvars (λ v1 v2 => sstore_preserves hst)
  | Opcode.TLOAD => exact execRead1_result_equiv hst hvars (by intro v; simpa [ht, hcc, tload, contractTransient, alookup])
  | Opcode.TSTORE => exact execWrite2_result_equiv hst hvars (λ v1 v2 => tstore_preserves hst)
  | Opcode.ILOAD => exact execRead1_result_equiv hst hvars (by intro v; simp [him])
  | Opcode.ISTORE => exact istore_stepInstBase_result_equiv hst hvars him
  | Opcode.JMP => exact jmp_result_equiv hst hvars
  | Opcode.JNZ => exact jnz_result_equiv hst hvars
  | Opcode.DJMP => exact djmp_result_equiv hst hvars
  | Opcode.PARAM => exact param_result_equiv hst hvars hpr
  | Opcode.RET => exact ret_stepInstBase_result_equiv hst hvars
  | Opcode.RETURN => exact return_result_equiv hst hvars hm
  | Opcode.REVERT => exact revert_result_equiv hst hvars hm
  | Opcode.STOP => simp [resultEquiv, liftResult]; exact haltState_preserves hst
  | Opcode.SINK => simp [resultEquiv, liftResult]; exact haltState_preserves hst
  | Opcode.PHI => trivial
  | Opcode.ASSIGN => exact assign_result_equiv hst hvars
  | Opcode.NOP => simp [resultEquiv, liftResult]; exact hst
  | Opcode.ALLOCA => exact alloca_result_equiv hst hvars hal hnx
  | Opcode.INVOKE => trivial
  | Opcode.CALLER => exact execRead0_result_equiv hst (by simp [hcc])
  | Opcode.ADDRESS => exact execRead0_result_equiv hst (by simp [hcc])
  | Opcode.CALLVALUE => exact execRead0_result_equiv hst (by simp [hcc])
  | Opcode.CALLDATALOAD => exact execRead1_result_equiv hst hvars (by intro v; simp [hcc])
  | Opcode.CALLDATASIZE => exact execRead0_result_equiv hst (by simp [hcc])
  | Opcode.CALLDATACOPY => exact calldatacopy_result_equiv hst hvars hcc
  | Opcode.ORIGIN => exact execRead0_result_equiv hst (by simp [htx])
  | Opcode.GASPRICE => exact execRead0_result_equiv hst (by simp [htx])
  | Opcode.GAS => exact execRead0_result_equiv hst (by simp [hcc])
  | Opcode.GASLIMIT => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.COINBASE => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.TIMESTAMP => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.NUMBER => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.PREVRANDAO => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.CHAINID => exact execRead0_result_equiv hst (by simp [htx])
  | Opcode.SELFBALANCE => exact execRead0_result_equiv hst (by simp [hcc, hac])
  | Opcode.BALANCE => exact execRead1_result_equiv hst hvars (by intro v; simp [hac, hcc])
  | Opcode.BLOCKHASH => exact execRead1_result_equiv hst hvars (by intro v; simp [hbc])
  | Opcode.BASEFEE => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.BLOBBASEFEE => exact execRead0_result_equiv hst (by simp [hbc])
  | Opcode.CODESIZE => exact execRead0_result_equiv hst (by simp [hcd])
  | Opcode.CODECOPY => exact codecopy_result_equiv hst hvars hcd
  | Opcode.EXTCODESIZE => exact execRead1_result_equiv hst hvars (by intro v; simp [hac])
  | Opcode.EXTCODEHASH => exact execRead1_result_equiv hst hvars (by intro v; simp [hac])
  | Opcode.EXTCODECOPY => exact extcodecopy_result_equiv hst hvars hac
  | Opcode.RETURNDATASIZE => exact execRead0_result_equiv hst (by simp [hrd])
  | Opcode.RETURNDATACOPY => exact returndatacopy_result_equiv hst hvars hrd
  | Opcode.BLOBHASH => exact execRead1_result_equiv hst hvars (by intro v; simp [htx])
  | Opcode.SHA3 => exact sha3_result_equiv hst hvars hm
  | Opcode.LOG => exact log_result_equiv hst hvars hm hcc hlg
  | Opcode.SELFDESTRUCT => exact selfdestruct_result_equiv hst hvars hac hcc
  | Opcode.INVALID => exact ⟨rfl, haltState_preserves (setReturndata_preserves hst)⟩
  | Opcode.ASSERT => exact assert_result_equiv hst hvars
  | Opcode.ASSERT_UNREACHABLE => exact assert_unreachable_result_equiv hst hvars
  | Opcode.DLOAD => exact execRead1_result_equiv hst hvars (by intro v; simp [hds])
  | Opcode.DLOADBYTES => exact dloadbytes_result_equiv hst hvars hds
  | Opcode.OFFSET => exact execPure2_result_equiv hst hvars
  | Opcode.CALL | Opcode.STATICCALL | Opcode.DELEGATECALL | Opcode.CREATE | Opcode.CREATE2 => trivial
end EvmYul.Venom.Hol

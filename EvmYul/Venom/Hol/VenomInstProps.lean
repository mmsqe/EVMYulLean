/-
Venom Instruction Properties — Theorem Statements

Port of vyper-hol/venom/proofs/venomInstProofs1Script.sml (core classification)

Key theorems (proofs deferred):
  - Opcode classification: effect-free ⇏ terminator
  - Helper preservation: exec_pure1/2/3, exec_read0/1 only change output vars
  - Mega-lemma: step_inst_base_preserves_all
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.StateEquiv
import EvmYul.Venom.Hol.StateEquivProofs
open EvmYul.Venom.Hol

set_option maxHeartbeats 0

namespace EvmYul.Venom.Hol

/- ===== Opcode Classification ===== -/

theorem is_effect_free_not_terminator {op : Opcode} (h : isEffectFreeOp op = true) : ¬ isTerminator op := by
  intro hterm
  unfold isTerminator at hterm
  unfold isEffectFreeOp at h
  cases op <;> simp at h hterm ⊢

theorem nonterminator_opcode_class {op : Opcode} (h : ¬ isTerminator op) :
  isEffectFreeOp op = true ∨ isMemWriteOp op = true ∨ op = Opcode.SSTORE ∨ op = Opcode.TSTORE ∨
  op = Opcode.ISTORE ∨ op = Opcode.LOG ∨ op = Opcode.ASSERT ∨
  op = Opcode.ASSERT_UNREACHABLE ∨ op = Opcode.INVOKE ∨ op = Opcode.ALLOCA ∨
  op = Opcode.CALL ∨ op = Opcode.STATICCALL ∨ op = Opcode.DELEGATECALL ∨
  op = Opcode.CREATE ∨ op = Opcode.CREATE2 := by
  unfold isTerminator at h
  unfold isEffectFreeOp isMemWriteOp
  cases op <;> simp at h ⊢

/-
Helper: lookup in an inserted AssocList for a key different from the inserted key
returns the same result as lookup in the original list.
-/
private lemma filter_lookup_same (v' out : String) (tl : AssocList String bytes32) (hne : v' ≠ out) :
  List.lookup v' (List.filter (fun (x : String × bytes32) => x.1 != out) tl) = List.lookup v' tl := by
  induction tl with
  | nil => simp
  | cons hd tl' ih =>
    rcases hd with ⟨k, val⟩
    by_cases h_k_out : k != out
    · simp [h_k_out, List.lookup_cons, ih]
    · -- filter removes (k,val), so k = out
      have h_k_out' : k = out := by
        have : ¬ (k != out) := h_k_out
        simp at this; exact this
      have h_v'_ne_k : v' ≠ k := by
        intro h_eq; apply hne; rw [h_k_out'] at h_eq; exact h_eq
      have h_v'_nk : (v' == k) = false := by simp [h_v'_ne_k]
      have h_v'_nout : (v' == out) = false := by simp [hne]
      simp [h_k_out, h_k_out', h_v'_nk, h_v'_nout, List.lookup_cons, ih]

private lemma lookup_insert_ne (al : AssocList String bytes32) (out : String) (v : bytes32) (v' : String) (hne : v' ≠ out) :
  AssocList.lookup String bytes32 (AssocList.insert String bytes32 al out v) v' = AssocList.lookup String bytes32 al v' := by
  unfold AssocList.insert
  induction al generalizing out with
  | nil =>
    unfold AssocList.lookup
    have : out ≠ v' := hne.symm
    simp [this]
  | cons hd tl ih =>
    unfold AssocList.lookup
    rcases hd with ⟨k, val⟩
    by_cases h_out_eq_v' : out = v'
    · exfalso; exact hne h_out_eq_v'.symm
    · simp [h_out_eq_v']
      by_cases h_k_eq_v' : k = v'
      · simp [h_k_eq_v']
        have : v' != out := by
          have := hne; simp [this]
        simp [this]
      · have h_v'_ne_k : v' ≠ k := by
          intro h_eq; apply h_k_eq_v'; exact h_eq.symm
        have h_v'_nk : (v' == k) = false := by simp [h_v'_ne_k]
        simp [h_v'_nk, h_k_eq_v']
        by_cases h_k_out : k != out
        · simp [h_k_out]
          have h_skip : List.lookup v' ((k, val) :: List.filter (fun (x : String × bytes32) => x.1 != out) tl) = List.lookup v' (List.filter (fun (x : String × bytes32) => x.1 != out) tl) :=
            by simpa [List.lookup_cons, h_v'_nk]
          have h_filter_eq : List.lookup v' (List.filter (fun (x : String × bytes32) => x.1 != out) tl) = List.lookup v' tl :=
            filter_lookup_same v' out tl hne
          simpa [h_skip, h_filter_eq]
        · simp [h_k_out, filter_lookup_same v' out tl hne]

theorem update_var_state_equiv {out : String} {v : bytes32} {s : VenomState} :
  stateEquiv {out} s (updateVar out v s) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold executionEquiv
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro v' hv'
  unfold lookupVar updateVar alookup ainsert
  have : v' ≠ out := by
    intro h_eq
    apply hv'
    simp [h_eq]
  symm
  exact lookup_insert_ne s.vars out v v' this

/- ===== Helper-level preservation: each helper only writes its output vars ===== -/

theorem exec_pure1_state_equiv {f inst s s'} (h : execPure1 f inst s = ExecResult.OK s') :
  stateEquiv {x | x ∈ inst.outputs} s s' := by
  unfold execPure1 at h
  -- use case_eq to extract the pattern-matched structure
  cases h' : inst.operands with
  | nil => simp [h'] at h
  | cons op1 ops =>
    cases h'' : ops with
    | nil =>
      cases h_out : inst.outputs with
      | nil => simp [h', h'', h_out] at h
      | cons out outs =>
        cases h_outs : outs with
        | nil =>
          cases h_eval : evalOperand op1 s with
          | none => simp [h', h'', h_out, h_outs, h_eval] at h
          | some v =>
            simp [h', h'', h_out, h_outs, h_eval] at h
            subst h
            have huv : stateEquiv {out} s (updateVar out (f v) s) := update_var_state_equiv
            have hsub : {out} ⊆ {x | x ∈ out :: outs} := by
              intro x hx; simp at hx; subst hx; simp
            simpa [h_out, h_outs] using stateEquiv_subset huv hsub
        | cons _ _ => simp [h', h'', h_out, h_outs] at h
    | cons _ _ => simp [h', h''] at h

theorem exec_pure2_state_equiv {f inst s s'} (h : execPure2 f inst s = ExecResult.OK s') :
  stateEquiv {x | x ∈ inst.outputs} s s' := by
  unfold execPure2 at h
  cases h_op1 : inst.operands with
  | nil => simp [h_op1] at h
  | cons op1 ops1 =>
    cases h_op2 : ops1 with
    | nil => simp [h_op1, h_op2] at h
    | cons op2 ops2 =>
      cases h_rest : ops2 with
      | nil =>
        cases h_out : inst.outputs with
        | nil => simp [h_op1, h_op2, h_rest, h_out] at h
        | cons out outs =>
          cases h_outs : outs with
          | nil =>
            cases h_eval1 : evalOperand op1 s with
            | none => simp [h_op1, h_op2, h_rest, h_out, h_outs, h_eval1] at h
            | some v1 =>
              cases h_eval2 : evalOperand op2 s with
              | none => simp [h_op1, h_op2, h_rest, h_out, h_outs, h_eval1, h_eval2] at h
              | some v2 =>
                simp [h_op1, h_op2, h_rest, h_out, h_outs, h_eval1, h_eval2] at h
                subst h
                have huv : stateEquiv {out} s (updateVar out (f v1 v2) s) := update_var_state_equiv
                have hsub : {out} ⊆ {x | x ∈ out :: outs} := by
                  intro x hx; simp at hx; subst hx; simp
                simpa [h_out, h_outs] using stateEquiv_subset huv hsub
          | cons _ _ => simp [h_op1, h_op2, h_rest, h_out, h_outs] at h
      | cons _ _ => simp [h_op1, h_op2, h_rest] at h

theorem exec_pure3_state_equiv {f inst s s'} (h : execPure3 f inst s = ExecResult.OK s') :
  stateEquiv {x | x ∈ inst.outputs} s s' := by
  unfold execPure3 at h
  cases h_op1 : inst.operands with
  | nil => simp [h_op1] at h
  | cons op1 ops1 =>
    cases h_op2 : ops1 with
    | nil => simp [h_op1, h_op2] at h
    | cons op2 ops2 =>
      cases h_op3 : ops2 with
      | nil => simp [h_op1, h_op2, h_op3] at h
      | cons op3 ops3 =>
        cases h_rest : ops3 with
        | nil =>
          cases h_out : inst.outputs with
          | nil => simp [h_op1, h_op2, h_op3, h_rest, h_out] at h
          | cons out outs =>
            cases h_outs : outs with
            | nil =>
              cases h_eval1 : evalOperand op1 s with
              | none => simp [h_op1, h_op2, h_op3, h_rest, h_out, h_outs, h_eval1] at h
              | some v1 =>
                cases h_eval2 : evalOperand op2 s with
                | none => simp [h_op1, h_op2, h_op3, h_rest, h_out, h_outs, h_eval1, h_eval2] at h
                | some v2 =>
                  cases h_eval3 : evalOperand op3 s with
                  | none => simp [h_op1, h_op2, h_op3, h_rest, h_out, h_outs, h_eval1, h_eval2, h_eval3] at h
                  | some v3 =>
                    simp [h_op1, h_op2, h_op3, h_rest, h_out, h_outs, h_eval1, h_eval2, h_eval3] at h
                    subst h
                    have huv : stateEquiv {out} s (updateVar out (f v1 v2 v3) s) := update_var_state_equiv
                    have hsub : {out} ⊆ {x | x ∈ out :: outs} := by
                      intro x hx; simp at hx; subst hx; simp
                    simpa [h_out, h_outs] using stateEquiv_subset huv hsub
            | cons _ _ => simp [h_op1, h_op2, h_op3, h_rest, h_out, h_outs] at h
        | cons _ _ => simp [h_op1, h_op2, h_op3, h_rest] at h

theorem exec_read0_state_equiv {f inst s s'} (h : execRead0 f inst s = ExecResult.OK s') :
  stateEquiv {x | x ∈ inst.outputs} s s' := by
  unfold execRead0 at h
  cases h_out : inst.outputs with
  | nil => simp [h_out] at h
  | cons out outs =>
    cases h_outs : outs with
    | nil =>
      simp [h_out, h_outs] at h
      subst h
      have huv : stateEquiv {out} s (updateVar out (f s) s) := update_var_state_equiv
      have hsub : {out} ⊆ {x | x ∈ out :: outs} := by
        intro x hx; simp at hx; subst hx; simp
      simpa [h_out, h_outs] using stateEquiv_subset huv hsub
    | cons _ _ => simp [h_out, h_outs] at h

theorem exec_read1_state_equiv {f inst s s'} (h : execRead1 f inst s = ExecResult.OK s') :
  stateEquiv {x | x ∈ inst.outputs} s s' := by
  unfold execRead1 at h
  cases h_op1 : inst.operands with
  | nil => simp [h_op1] at h
  | cons op1 ops =>
    cases h_rest : ops with
    | nil =>
      cases h_out : inst.outputs with
      | nil => simp [h_op1, h_rest, h_out] at h
      | cons out outs =>
        cases h_outs : outs with
        | nil =>
          cases h_eval : evalOperand op1 s with
          | none => simp [h_op1, h_rest, h_out, h_outs, h_eval] at h
          | some v =>
            simp [h_op1, h_rest, h_out, h_outs, h_eval] at h
            subst h
            have huv : stateEquiv {out} s (updateVar out (f v s) s) := update_var_state_equiv
            have hsub : {out} ⊆ {x | x ∈ out :: outs} := by
              intro x hx; simp at hx; subst hx; simp
            simpa [h_out, h_outs] using stateEquiv_subset huv hsub
        | cons _ _ => simp [h_op1, h_rest, h_out, h_outs] at h
    | cons _ _ => simp [h_op1, h_rest] at h

/- ===== NOP / ASSERT identity ===== -/

theorem step_nop_identity {inst s} (h : inst.opcode = Opcode.NOP) : stepInstBase inst s = ExecResult.OK s := by
  unfold stepInstBase
  simp [h]

theorem step_assert_identity {inst s s'} (hstep : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.ASSERT) : s' = s := by
  unfold stepInstBase at hstep
  simp [hop] at hstep
  split at hstep
  · -- matched operands = [condOp]
    split at hstep
    · -- evalOperand condOp s = some cond
      split at hstep
      · -- cond = 0: Abort case, contradicts hstep being OK
        simp at hstep
      · -- cond ≠ 0: OK s case
        simp at hstep
        subst hstep; rfl
    · simp at hstep
  · simp at hstep

theorem step_assert_unreachable_identity {inst s s'} (hstep : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.ASSERT_UNREACHABLE) : s' = s := by
  unfold stepInstBase at hstep
  simp [hop] at hstep
  split at hstep
  · split at hstep
    · split at hstep
      · simp at hstep
      · simp at hstep; subst hstep; rfl
    · simp at hstep
  · simp at hstep

/- ===== Write-opcode field preservation ===== -/

theorem step_mstore_preserves {inst s s'} (h : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.MSTORE) :
  s'.transient = s.transient ∧ s'.accounts = s.accounts ∧ s'.logs = s.logs ∧
  s'.immutables = s.immutables ∧ s'.returndata = s.returndata ∧
  s'.allocas = s.allocas ∧ s'.halted = s.halted ∧
  s'.currentBb = s.currentBb ∧ s'.instIdx = s.instIdx ∧ s'.prevBb = s.prevBb ∧
  (∀ v, lookupVar v s' = lookupVar v s) := by
  unfold stepInstBase at h
  simp [hop] at h
  -- MSTORE -> execWrite2 (λ addr val s => mstore addr.toNat val s) inst s
  unfold execWrite2 at h
  split at h
  · -- matched 2 operands
    split at h
    · -- evalOperand op1 s = some addr, evalOperand op2 s = some val
      simp at h
      -- h: mstore addr.toNat val s = s'
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro v
      unfold lookupVar mstore writeMemoryWithExpansion
      simp
    · simp at h
  · simp at h

theorem step_sstore_preserves {inst s s'} (h : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.SSTORE) :
  s'.memory = s.memory ∧ s'.transient = s.transient ∧ s'.logs = s.logs ∧
  s'.immutables = s.immutables ∧ s'.returndata = s.returndata ∧
  s'.allocas = s.allocas ∧ s'.halted = s.halted ∧
  s'.currentBb = s.currentBb ∧ s'.instIdx = s.instIdx ∧ s'.prevBb = s.prevBb ∧
  (∀ v, lookupVar v s' = lookupVar v s) := by
  unfold stepInstBase at h
  simp [hop] at h
  unfold execWrite2 at h
  split at h
  · split at h
    · simp at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro v
      unfold lookupVar sstore
      simp
    · simp at h
  · simp at h

theorem step_tstore_preserves {inst s s'} (h : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.TSTORE) :
  s'.memory = s.memory ∧ s'.accounts = s.accounts ∧ s'.logs = s.logs ∧
  s'.immutables = s.immutables ∧ s'.returndata = s.returndata ∧
  s'.allocas = s.allocas ∧ s'.halted = s.halted ∧
  s'.currentBb = s.currentBb ∧ s'.instIdx = s.instIdx ∧ s'.prevBb = s.prevBb ∧
  (∀ v, lookupVar v s' = lookupVar v s) := by
  unfold stepInstBase at h
  simp [hop] at h
  unfold execWrite2 at h
  split at h
  · split at h
    · simp at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro v
      unfold lookupVar tstore
      simp
    · simp at h
  · simp at h

theorem step_istore_preserves {inst s s'} (h : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.ISTORE) :
  s'.memory = s.memory ∧ s'.transient = s.transient ∧ s'.accounts = s.accounts ∧ s'.logs = s.logs ∧
  s'.returndata = s.returndata ∧ s'.allocas = s.allocas ∧ s'.halted = s.halted ∧
  s'.currentBb = s.currentBb ∧ s'.instIdx = s.instIdx ∧ s'.prevBb = s.prevBb ∧
  (∀ v, lookupVar v s' = lookupVar v s) := by
  unfold stepInstBase at h
  simp [hop] at h
  split at h
  · -- matched [offsetOp, valOp]
    split at h
    · -- evalOperand both succeed
      simp at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro v
      unfold lookupVar
      simp
    · simp at h
  · simp at h

theorem step_log_preserves {inst s s'} (h : stepInstBase inst s = ExecResult.OK s') (hop : inst.opcode = Opcode.LOG) :
  s'.memory = s.memory ∧ s'.transient = s.transient ∧ s'.accounts = s.accounts ∧
  s'.immutables = s.immutables ∧ s'.returndata = s.returndata ∧
  s'.allocas = s.allocas ∧ s'.halted = s.halted ∧
  s'.currentBb = s.currentBb ∧ s'.instIdx = s.instIdx ∧ s'.prevBb = s.prevBb ∧
  (∀ v, lookupVar v s' = lookupVar v s) := by
  unfold stepInstBase at h
  simp [hop] at h
  split at h
  · -- Lit tc :: rest
    split at h
    · -- rest.length check OK
      split at h
      · -- all some: ok
        cases h
        repeat (apply And.intro <;> try rfl)
        intro v; rfl
      · -- some none: error
        simp at h
    · -- rest.length check failed
      simp at h
  · -- not Lit tc :: rest
    simp at h


end EvmYul.Venom.Hol

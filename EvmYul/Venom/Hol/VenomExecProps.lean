/-
Venom Execution Properties — run_block lemmas

Port of vyper-hol/venom/proofs/venomExecProofsScript.sml + venomExecPropsScript.sml

Key theorems (proofs deferred):
  - run_blocks_unfold: unfold one iteration of run_blocks
  - step_inst_base_preserves_inst_idx: non-terminators preserve inst_idx
  - run_block properties
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Exec
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol

/- ===== boolToWord ===== -/

theorem boolToWord_T : boolToWord true = EvmYul.UInt256.ofNat 1 := by rfl
theorem boolToWord_F : boolToWord false = EvmYul.UInt256.ofNat 0 := by rfl

/- ===== run_blocks unfolds to run_block ===== -/

theorem run_blocks_unfold {fuel ctx fn s} : runBlocks (fuel+1) ctx fn s =
  match lookupBlock s.currentBb fn.blocks with
  | none => ExecResult.Error "block not found"
  | some bb =>
    match runBlock fuel ctx bb s with
    | ExecResult.OK s' => (if s'.halted then ExecResult.Halt s' else runBlocks fuel ctx fn s')
    | ExecResult.IntRet vals s' => ExecResult.IntRet vals s'
    | other => other := by
  rfl

/- ===== step_inst_base preserves inst_idx for non-terminators ===== -/

theorem step_inst_base_preserves_inst_idx {inst s s'} (hok : stepInstBase inst s = ExecResult.OK s') (hnoterm : ¬ isTerminator inst.opcode) :
  s'.instIdx = s.instIdx := by
  set_option maxHeartbeats 1000000 in
  rcases inst with ⟨id, opcode, operands, outputs⟩
  cases opcode <;> simp only [stepInstBase] at hok <;>
    simp [execPure1, execPure2, execPure3, execRead0, execRead1, execWrite2, updateVar, isTerminator] at hok hnoterm ⊢ <;>
    repeat (first | split at hok | (injection hok with h; subst h; rfl) | (subst hok; rfl) | (simp at hok))

theorem exec_block_OK_not_halted {fuel ctx bb s s'} (hr : execBlock fuel ctx bb s = ExecResult.OK s') :
  s'.halted = false := by
  induction fuel generalizing s s' with
  | zero =>
    unfold execBlock at hr; simp at hr
  | succ fuel ih =>
    unfold execBlock at hr
    cases h_get : getInstruction bb s.instIdx
    · simp [h_get] at hr
    · next inst =>
      simp [h_get] at hr
      cases h_step : stepInstBase inst s
      · next s'' =>
        simp [h_step] at hr
        by_cases h_term : isTerminator inst.opcode
        · simp [h_term] at hr
          split at hr
          · simp at hr
          · rename_i h_not_halted
            injection hr with h; subst h
            simpa using h_not_halted
        · simp [h_term] at hr
          exact ih hr
      · simp [h_step] at hr
      · simp [h_step] at hr
      · simp [h_step] at hr
      · simp [h_step] at hr

/- If runBlock returns OK, the result state is not halted.
   (HOL4: exec_block_OK_not_halted) -/
theorem run_block_result {fuel ctx bb s s'} (hr : runBlock fuel ctx bb s = ExecResult.OK s') :
  s'.halted = false := by
  unfold runBlock at hr
  cases h_phis : evalPhis s bb.instructions
  · next sPhi =>
    simp [h_phis] at hr
    exact exec_block_OK_not_halted hr
  · simp [h_phis] at hr
  · simp [h_phis] at hr
  · simp [h_phis] at hr
  · simp [h_phis] at hr

end EvmYul.Venom.Hol

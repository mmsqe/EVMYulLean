/-
State Equivalence Definitions — Venom Core Proofs Layer 1

Port of vyper-hol/venom/defs/stateEquivScript.sml

Defines the equivalence hierarchy:
  1. observable_equiv : only externally visible effects
  2. execution_equiv  : all state except control flow, modulo vars
  3. state_equiv      : full state with variable exceptions

Also: revert_equiv, lift_result, result_equiv.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol

/- ===== Observable Equivalence (weakest) ===== -/

/-- Only externally visible effects: accounts, returndata, logs, transient, immutables. -/
def observableEquiv (s1 s2 : VenomState) : Prop :=
  s1.accounts = s2.accounts ∧
  s1.returndata = s2.returndata ∧
  s1.halted = s2.halted ∧
  s1.logs = s2.logs ∧
  s1.transient = s2.transient ∧
  s1.immutables = s2.immutables

/- ===== Execution Equivalence (intermediate) ===== -/

/-- State equivalence ignoring control flow fields (currentBb, instIdx, prevBb).
    vars: set of variable names to exclude from comparison. -/
def executionEquiv (vars : Set String) (s1 s2 : VenomState) : Prop :=
  (∀ v, v ∉ vars → lookupVar v s1 = lookupVar v s2) ∧
  s1.memory = s2.memory ∧
  s1.transient = s2.transient ∧
  s1.halted = s2.halted ∧
  s1.returndata = s2.returndata ∧
  s1.accounts = s2.accounts ∧
  s1.callCtx = s2.callCtx ∧
  s1.txCtx = s2.txCtx ∧
  s1.blockCtx = s2.blockCtx ∧
  s1.logs = s2.logs ∧
  s1.immutables = s2.immutables ∧
  s1.dataSection = s2.dataSection ∧
  s1.labels = s2.labels ∧
  s1.code = s2.code ∧
  s1.params = s2.params ∧
  s1.prevHashes = s2.prevHashes ∧
  s1.allocas = s2.allocas ∧
  s1.allocaNext = s2.allocaNext

/- ===== Full State Equivalence (strongest) ===== -/

/-- Full state equivalence ignoring only the specified variable set.
    For full equivalence with no exceptions, use `stateEquiv ∅`. -/
def stateEquiv (vars : Set String) (s1 s2 : VenomState) : Prop :=
  executionEquiv vars s1 s2 ∧
  s1.currentBb = s2.currentBb ∧
  s1.instIdx = s2.instIdx ∧
  s1.prevBb = s2.prevBb

/- ===== Revert Equivalence ===== -/

/-- What survives EVM rollback on abort: only returndata. -/
def revertEquiv (s1 s2 : VenomState) : Prop :=
  s1.returndata = s2.returndata

/- ===== Result Equivalence ===== -/

/-- Generic combinator: lift three state relations through ExecResult. -/
def liftResult (Rok Rterm Rabort : VenomState → VenomState → Prop) : ExecResult → ExecResult → Prop
  | ExecResult.OK s1, ExecResult.OK s2 => Rok s1 s2
  | ExecResult.Halt s1, ExecResult.Halt s2 => Rterm s1 s2
  | ExecResult.Abort a1 s1, ExecResult.Abort a2 s2 => a1 = a2 ∧ Rabort s1 s2
  | ExecResult.IntRet v1 s1, ExecResult.IntRet v2 s2 => Rterm s1 s2 ∧ v1 = v2
  | ExecResult.Error _, ExecResult.Error _ => True
  | _, _ => False

/-- Canonical result equivalence: state_equiv for OK, execution_equiv for terminal. -/
def resultEquiv (vars : Set String) : ExecResult → ExecResult → Prop :=
  liftResult (stateEquiv vars) (executionEquiv vars) (executionEquiv vars)

end EvmYul.Venom.Hol

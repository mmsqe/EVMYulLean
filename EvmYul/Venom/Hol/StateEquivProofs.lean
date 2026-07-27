/-
State Equivalence Proofs — Venom Core Proofs Layer 2

Port of vyper-hol/venom/proofs/stateEquivProofsScript.sml

Proves refl/sym/trans for state_equiv, execution_equiv, result_equiv.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.StateEquiv
open EvmYul.Venom.Hol

set_option linter.unusedVariables false

namespace EvmYul.Venom.Hol

/- ===== Helper: build executionEquiv explicitly ===== -/

private def mkExecutionEquiv (vars : Set String) (s1 s2 : VenomState)
  (hv  : ∀ v, v ∉ vars → lookupVar v s1 = lookupVar v s2)
  (hm  : s1.memory = s2.memory) (ht : s1.transient = s2.transient)
  (hhl : s1.halted = s2.halted) (hrd : s1.returndata = s2.returndata)
  (hac : s1.accounts = s2.accounts) (hcc : s1.callCtx = s2.callCtx)
  (htx : s1.txCtx = s2.txCtx) (hbc : s1.blockCtx = s2.blockCtx)
  (hlg : s1.logs = s2.logs) (him : s1.immutables = s2.immutables)
  (hds : s1.dataSection = s2.dataSection) (hlb : s1.labels = s2.labels)
  (hcd : s1.code = s2.code) (hpr : s1.params = s2.params)
  (hph : s1.prevHashes = s2.prevHashes) (hal : s1.allocas = s2.allocas)
  (hnx : s1.allocaNext = s2.allocaNext) : executionEquiv vars s1 s2 :=
  And.intro hv (And.intro hm (And.intro ht (And.intro hhl (And.intro hrd
  (And.intro hac (And.intro hcc (And.intro htx (And.intro hbc (And.intro hlg
  (And.intro him (And.intro hds (And.intro hlb (And.intro hcd (And.intro hpr
  (And.intro hph (And.intro hal hnx))))))))))))))))

/- ===== state_equiv Properties ===== -/

theorem stateEquiv_refl {vars : Set String} (s : VenomState) : stateEquiv vars s s := by
  refine ⟨mkExecutionEquiv vars s s (by intro v _; rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl⟩

theorem stateEquiv_sym {vars : Set String} {s1 s2 : VenomState} (h : stateEquiv vars s1 s2) : stateEquiv vars s2 s1 := by
  rcases h with ⟨heq, hbb, hidx, hprev⟩
  have ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩ := heq
  refine ⟨mkExecutionEquiv vars s2 s1 (by intro v hvx; simp [hv v hvx]) hm.symm ht.symm hhl.symm hrd.symm hac.symm hcc.symm htx.symm hbc.symm hlg.symm him.symm hds.symm hlb.symm hcd.symm hpr.symm hph.symm hal.symm hnx.symm, hbb.symm, hidx.symm, hprev.symm⟩

theorem stateEquiv_trans {vars : Set String} {s1 s2 s3 : VenomState}
  (h12 : stateEquiv vars s1 s2) (h23 : stateEquiv vars s2 s3) : stateEquiv vars s1 s3 := by
  rcases h12 with ⟨heq12, hbb12, hidx12, hprev12⟩
  rcases h23 with ⟨heq23, hbb23, hidx23, hprev23⟩
  have ⟨hv12, hm12, ht12, hhl12, hrd12, hac12, hcc12, htx12, hbc12, hlg12, him12, hds12, hlb12, hcd12, hpr12, hph12, hal12, hnx12⟩ := heq12
  have ⟨hv23, hm23, ht23, hhl23, hrd23, hac23, hcc23, htx23, hbc23, hlg23, him23, hds23, hlb23, hcd23, hpr23, hph23, hal23, hnx23⟩ := heq23
  refine ⟨mkExecutionEquiv vars s1 s3 (by intro v hvx; rw [hv12 v hvx, hv23 v hvx])
    (hm12.trans hm23) (ht12.trans ht23) (hhl12.trans hhl23) (hrd12.trans hrd23)
    (hac12.trans hac23) (hcc12.trans hcc23) (htx12.trans htx23) (hbc12.trans hbc23)
    (hlg12.trans hlg23) (him12.trans him23) (hds12.trans hds23) (hlb12.trans hlb23)
    (hcd12.trans hcd23) (hpr12.trans hpr23) (hph12.trans hph23) (hal12.trans hal23)
    (hnx12.trans hnx23), hbb12.trans hbb23, hidx12.trans hidx23, hprev12.trans hprev23⟩

theorem stateEquiv_subset {vars1 vars2 : Set String} {s1 s2 : VenomState}
  (h : stateEquiv vars1 s1 s2) (hsub : vars1 ⊆ vars2) : stateEquiv vars2 s1 s2 := by
  rcases h with ⟨heq, hbb, hidx, hprev⟩
  have ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩ := heq
  refine ⟨mkExecutionEquiv vars2 s1 s2 (by intro v hvx; apply hv v; intro hv1; exact hvx (hsub hv1))
    hm ht hhl hrd hac hcc htx hbc hlg him hds hlb hcd hpr hph hal hnx, hbb, hidx, hprev⟩

/- ===== execution_equiv Properties ===== -/

theorem executionEquiv_refl {vars : Set String} (s : VenomState) : executionEquiv vars s s :=
  mkExecutionEquiv vars s s (by intro v _; rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem executionEquiv_sym {vars : Set String} {s1 s2 : VenomState} (h : executionEquiv vars s1 s2) : executionEquiv vars s2 s1 := by
  have ⟨hv, hm, ht, hhl, hrd, hac, hcc, htx, hbc, hlg, him, hds, hlb, hcd, hpr, hph, hal, hnx⟩ := h
  exact mkExecutionEquiv vars s2 s1 (by intro v hvx; simp [hv v hvx]) hm.symm ht.symm hhl.symm hrd.symm hac.symm hcc.symm htx.symm hbc.symm hlg.symm him.symm hds.symm hlb.symm hcd.symm hpr.symm hph.symm hal.symm hnx.symm

theorem executionEquiv_trans {vars : Set String} {s1 s2 s3 : VenomState}
  (h12 : executionEquiv vars s1 s2) (h23 : executionEquiv vars s2 s3) : executionEquiv vars s1 s3 := by
  have ⟨hv12, hm12, ht12, hhl12, hrd12, hac12, hcc12, htx12, hbc12, hlg12, him12, hds12, hlb12, hcd12, hpr12, hph12, hal12, hnx12⟩ := h12
  have ⟨hv23, hm23, ht23, hhl23, hrd23, hac23, hcc23, htx23, hbc23, hlg23, him23, hds23, hlb23, hcd23, hpr23, hph23, hal23, hnx23⟩ := h23
  exact mkExecutionEquiv vars s1 s3 (by intro v hvx; rw [hv12 v hvx, hv23 v hvx])
    (hm12.trans hm23) (ht12.trans ht23) (hhl12.trans hhl23) (hrd12.trans hrd23)
    (hac12.trans hac23) (hcc12.trans hcc23) (htx12.trans htx23) (hbc12.trans hbc23)
    (hlg12.trans hlg23) (him12.trans him23) (hds12.trans hds23) (hlb12.trans hlb23)
    (hcd12.trans hcd23) (hpr12.trans hpr23) (hph12.trans hph23) (hal12.trans hal23) (hnx12.trans hnx23)

/- ===== result_equiv Properties ===== -/

theorem resultEquiv_sym {vars : Set String} {r1 r2 : ExecResult} (h : resultEquiv vars r1 r2) : resultEquiv vars r2 r1 := by
  unfold resultEquiv at h ⊢
  cases r1 <;> cases r2 <;> simp [liftResult] at h ⊢
  · exact stateEquiv_sym h
  · exact executionEquiv_sym h
  · rcases h with ⟨ha, heq⟩; exact ⟨ha.symm, executionEquiv_sym heq⟩
  · rcases h with ⟨heq, hvals⟩; exact ⟨executionEquiv_sym heq, Eq.symm hvals⟩

theorem resultEquiv_trans {vars : Set String} {r1 r2 r3 : ExecResult}
  (h12 : resultEquiv vars r1 r2) (h23 : resultEquiv vars r2 r3) : resultEquiv vars r1 r3 := by
  unfold resultEquiv at h12 h23 ⊢
  cases r1 <;> cases r2 <;> cases r3 <;> simp [liftResult] at h12 h23 ⊢
  · exact stateEquiv_trans h12 h23
  · exact executionEquiv_trans h12 h23
  · rcases h12 with ⟨ha12, heq12⟩; rcases h23 with ⟨ha23, heq23⟩
    exact ⟨Eq.trans ha12 ha23, executionEquiv_trans heq12 heq23⟩
  · rcases h12 with ⟨heq12, hvals12⟩; rcases h23 with ⟨heq23, hvals23⟩
    exact ⟨executionEquiv_trans heq12 heq23, Eq.trans hvals12 hvals23⟩

end EvmYul.Venom.Hol

import EvmYul.Venom.Backend

/-!
# Non-vacuity: the simulation and its lemmas, instantiated on real execution

The backend lemmas are conditional (`… EVM.step … = .ok es' → Sim … `). A
skeptic's worry is vacuity — that the `Sim` relation or the `EVM.step … = .ok …`
hypotheses are never *simultaneously* satisfiable, so the lemmas say nothing.

This file rules that out **concretely**: it builds explicit states, proves `Sim`
holds by `rfl` (so the relation is satisfiable, not empty), and discharges the
step hypotheses by letting the Lean **kernel actually run `EVM.step`** (`rfl`
reduces the opcode on the concrete stack/storage to `.ok …`). Feeding the real
execution into a backend lemma then yields a concrete post-state `Sim` — the
conditional chain instantiated end to end on an actual run.

The single-op lowerings are instantiated this way across the board:

* **arithmetic / comparison** — `ADD`, `SUB`, `LT`, `GT`, `EQ`, `ISZERO`, `NOT`
* **scheduling** — `DUP1`, `DUP2`, `SWAP1`, `POP`
* **control-flow landing** — `JUMPDEST`
* **storage** — `SLOAD` (read) and `SSTORE` (write, the core transfer mutation)

The multi-step storage *combinators* (`lowered_debit/credit/transfer`) are not
reduced by kernel `rfl` (a 5-step `RBMap` SLOAD/SSTORE chain blows up); their
non-vacuity is covered by the execution-level differential suite
(`scripts/venom_differential.sh`), which runs whole `.venom` programs — including
the balance transfer — against a production EVM.
-/

namespace EvmYul.Venom.NonVacuity
open EvmYul EvmYul.EVM EvmYul.Venom EvmYul.Venom.Backend

set_option maxRecDepth 8192

/-- SSA environment binding `a ↦ 5`, `b ↦ 9` (else 0). -/
def vs : VenomState :=
  { env := fun x => if x = "a" then UInt256.ofNat 5 else if x = "b" then UInt256.ofNat 9
                    else UInt256.ofNat 0 }

/-- A concrete EVM state: stack `[5]`, empty accounts — realizes layout `["a"]`. -/
def esA : EVM.State := { (default : EVM.State) with stack := [UInt256.ofNat 5] }

/-- A concrete EVM state: stack `[5, 9]` — realizes layout `["a", "b"]`. -/
def esAB : EVM.State := { (default : EVM.State) with stack := [UInt256.ofNat 5, UInt256.ofNat 9] }

/-- Like `esAB`, but with an (empty-storage) account at the code owner — the
fixture `SSTORE` needs, since it mutates the executing account's storage. -/
def esS : EVM.State :=
  { esAB with accountMap := esAB.accountMap.insert esAB.executionEnv.codeOwner default }

/-- **`Sim` is satisfiable.** A concrete witness: the stack `[5]` realizes the
layout `["a"]` and the (empty) EVM storage agrees with the (zero) SSA storage —
both by `rfl`. So the relation the whole development reasons about is not vacuous. -/
theorem sim_satisfiable : Sim vs esA ["a"] := ⟨rfl, fun _ => rfl⟩

theorem sim_satisfiable₂ : Sim vs esAB ["a", "b"] := ⟨rfl, fun _ => rfl⟩

theorem sim_satisfiableS : Sim vs esS ["a", "b"] := ⟨rfl, fun _ => rfl⟩

/-- **`NOT` instantiated on a real run.** The kernel runs `EVM.step .NOT` on `[5]`
to `.ok es'` (discharging the step hypothesis), and `sim_not` produces a concrete
post-`Sim` with `%c = ~5`. -/
theorem not_instantiated :
    ∃ es', EVM.step 1 0 (some (.NOT, none)) esA = .ok es' ∧
      Sim (vs.set "c" (UInt256.lnot (UInt256.ofNat 5))) es' ["c"] :=
  ⟨_, rfl, sim_not vs esA _ [] "c" "a" 1 0 none (by decide) rfl sim_satisfiable⟩

/-- **`ADD` instantiated on a real run.** `EVM.step .ADD` on `[5, 9]` runs to
`.ok es'`, and `sim_add` yields `%c = 5 + 9`. -/
theorem add_instantiated :
    ∃ es', EVM.step 1 0 (some (.ADD, none)) esAB = .ok es' ∧
      Sim (vs.set "c" (UInt256.add (UInt256.ofNat 5) (UInt256.ofNat 9))) es' ["c"] :=
  ⟨_, rfl, sim_add vs esAB _ [] "c" "a" "b" 1 0 none (by decide) rfl sim_satisfiable₂⟩

/-- **`DUP1` (scheduling) instantiated on a real run.** `EVM.step .DUP1` on `[5]`
runs to `.ok es'`, and `sim_dup1` duplicates the live value (`["a"] ↦ ["a","a"]`)
with the SSA state unchanged. -/
theorem dup1_instantiated :
    ∃ es', EVM.step 1 0 (some (.DUP1, none)) esA = .ok es' ∧ Sim vs es' ["a", "a"] :=
  ⟨_, rfl, sim_dup1 vs esA _ [] "a" 1 0 none rfl sim_satisfiable⟩

/-! ### More arithmetic / comparison, each instantiated end to end -/

/-- **`SUB`** on `[5, 9]` runs to `.ok es'`; `sim_sub` yields `%c = 5 - 9`. -/
theorem sub_instantiated :
    ∃ es', EVM.step 1 0 (some (.SUB, none)) esAB = .ok es' ∧
      Sim (vs.set "c" (UInt256.sub (UInt256.ofNat 5) (UInt256.ofNat 9))) es' ["c"] :=
  ⟨_, rfl, sim_sub vs esAB _ [] "c" "a" "b" 1 0 none (by decide) rfl sim_satisfiable₂⟩

/-- **`LT`** on `[5, 9]` runs to `.ok es'`; `sim_lt` yields `%c = (5 < 9)`. -/
theorem lt_instantiated :
    ∃ es', EVM.step 1 0 (some (.LT, none)) esAB = .ok es' ∧
      Sim (vs.set "c" (UInt256.lt (UInt256.ofNat 5) (UInt256.ofNat 9))) es' ["c"] :=
  ⟨_, rfl, sim_lt vs esAB _ [] "c" "a" "b" 1 0 none (by decide) rfl sim_satisfiable₂⟩

/-- **`GT`** on `[5, 9]` runs to `.ok es'`; `sim_gt` yields `%c = (5 > 9)`. -/
theorem gt_instantiated :
    ∃ es', EVM.step 1 0 (some (.GT, none)) esAB = .ok es' ∧
      Sim (vs.set "c" (UInt256.gt (UInt256.ofNat 5) (UInt256.ofNat 9))) es' ["c"] :=
  ⟨_, rfl, sim_gt vs esAB _ [] "c" "a" "b" 1 0 none (by decide) rfl sim_satisfiable₂⟩

/-- **`EQ`** on `[5, 9]` runs to `.ok es'`; `sim_eq` yields `%c = (5 = 9)`. -/
theorem eq_instantiated :
    ∃ es', EVM.step 1 0 (some (.EQ, none)) esAB = .ok es' ∧
      Sim (vs.set "c" (UInt256.eq (UInt256.ofNat 5) (UInt256.ofNat 9))) es' ["c"] :=
  ⟨_, rfl, sim_eq vs esAB _ [] "c" "a" "b" 1 0 none (by decide) rfl sim_satisfiable₂⟩

/-- **`ISZERO`** on `[5]` runs to `.ok es'`; `sim_iszero` yields `%c = (5 == 0)`. -/
theorem iszero_instantiated :
    ∃ es', EVM.step 1 0 (some (.ISZERO, none)) esA = .ok es' ∧
      Sim (vs.set "c" (UInt256.isZero (UInt256.ofNat 5))) es' ["c"] :=
  ⟨_, rfl, sim_iszero vs esA _ [] "c" "a" 1 0 none (by decide) rfl sim_satisfiable⟩

/-! ### More scheduling, instantiated end to end -/

/-- **`SWAP1`** on `[5, 9]` runs to `.ok es'`; `sim_swap1` exchanges the live
values (`["a","b"] ↦ ["b","a"]`), SSA state unchanged. -/
theorem swap1_instantiated :
    ∃ es', EVM.step 1 0 (some (.SWAP1, none)) esAB = .ok es' ∧ Sim vs es' ["b", "a"] :=
  ⟨_, rfl, sim_swap1 vs esAB _ [] "a" "b" 1 0 none rfl sim_satisfiable₂⟩

/-- **`POP`** on `[5]` runs to `.ok es'`; `sim_pop` drops the dead value
(`["a"] ↦ []`), SSA state unchanged. -/
theorem pop_instantiated :
    ∃ es', EVM.step 1 0 (some (.POP, none)) esA = .ok es' ∧ Sim vs es' [] :=
  ⟨_, rfl, sim_pop vs esA _ [] "a" 1 0 none rfl sim_satisfiable⟩

/-- **`DUP2`** on `[5, 9]` runs to `.ok es'`; `sim_dup2` duplicates the second
live value (`["a","b"] ↦ ["b","a","b"]`), SSA state unchanged. -/
theorem dup2_instantiated :
    ∃ es', EVM.step 1 0 (some (.DUP2, none)) esAB = .ok es' ∧ Sim vs es' ["b", "a", "b"] :=
  ⟨_, rfl, sim_dup2 vs esAB _ [] "a" "b" 1 0 none rfl sim_satisfiable₂⟩

/-! ### Control-flow landing pad and storage read, instantiated end to end -/

/-- **`JUMPDEST`** (a block's entry label) on `[5]` runs to `.ok es'`;
`sim_jumpdest` preserves the simulation (`["a"]` unchanged) — the landing pad
after a control transfer. -/
theorem jumpdest_instantiated :
    ∃ es', EVM.step 1 0 (some (.JUMPDEST, none)) esA = .ok es' ∧ Sim vs es' ["a"] :=
  ⟨_, rfl, sim_jumpdest vs esA _ ["a"] 1 0 none rfl sim_satisfiable⟩

/-- **`SLOAD`** on `[5]` runs to `.ok es'`; `sim_sload` reads slot `5` of the
(empty) storage — `%c = vs.storage 5 = 0` — agreeing with the SSA storage. -/
theorem sload_instantiated :
    ∃ es', EVM.step 1 0 (some (.SLOAD, none)) esA = .ok es' ∧
      Sim (vs.set "c" (vs.storage (vs.env "a"))) es' ["c"] :=
  ⟨_, rfl, sim_sload vs esA _ [] "c" "a" 1 0 none (by decide) rfl sim_satisfiable⟩

/-- **`SSTORE`** on `[5, 9]` (with an account at the code owner) runs to `.ok es'`;
`sim_sstore` writes `%b = 9` to slot `%a = 5`, and the resulting EVM storage agrees
with the SSA store `vs.sstore 5 9`. The storage *write* — the core mutation a
balance transfer performs — instantiated end to end on a real run. -/
theorem sstore_instantiated :
    ∃ es', EVM.step 1 0 (some (.SSTORE, none)) esS = .ok es' ∧
      Sim (vs.sstore (vs.env "a") (vs.env "b")) es' [] :=
  ⟨_, rfl, sim_sstore vs esS _ [] "a" "b" 1 0 none default rfl (by decide) rfl sim_satisfiableS⟩

/-! The multi-step storage *combinators* (`lowered_debit` / `lowered_credit` /
`lowered_transfer`: a `DUP2; SLOAD; SUB/ADD; SWAP1; SSTORE` chain) are not
instantiated by kernel `rfl` here — reducing a 5-step chain through the
`RBMap`-backed `SLOAD`/`SSTORE` symbolically blows up. Their non-vacuity is
covered instead by the **execution-level** differential suite
(`scripts/venom_differential.sh`), which runs whole `.venom` programs — including
the balance transfer — against a production EVM. -/

end EvmYul.Venom.NonVacuity

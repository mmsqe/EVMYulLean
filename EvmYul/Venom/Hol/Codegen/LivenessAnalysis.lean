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

end EvmYul.Venom.Hol.Codegen

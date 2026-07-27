import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Codegen.Cfg

/-!
# Generic dataflow analysis framework

Port of `vyper-hol main:venom/analysis/dataflow/defs/{worklistDefsScript,
dfAnalyzeDefsScript}.sml`: a parameterized (lattice `α`, context `γ`) dataflow
engine — `dfAnalyzeFuel direction bottom join transfer edgeTransfer ctx entryVal fn`
— driven by a fuel-bounded worklist over the CFG. The liveness analysis is the
`Backward / list_union` instance (next file).

HOL iterates the worklist to a true fixpoint (`wl_iterate`); the fuel variant
(`wl_iterate_fuel`, the one the generator path uses) is what is ported here.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `direction`. -/
inductive Direction where
  | Forward
  | Backward

/- ===== Worklist ===== -/

/-- `wl_step`: process the head label; if it changed the state, enqueue its deps. -/
def wlStep {α β : Type} (changed : α → β → β → Bool) (process : α → β → β)
    (deps : α → List α) : (List α × β) → (List α × β)
  | ([],          st) => ([], st)
  | (lbl :: rest, st) =>
    let st' := process lbl st
    if changed lbl st st' then (rest ++ deps lbl, st') else (rest, st')

/-- `wl_iterate_fuel`: fuel-bounded worklist iteration. -/
def wlIterateFuel {α β : Type} : Nat → (α → β → β → Bool) → (α → β → β) → (α → List α) →
    List α → β → (List α × β)
  | 0,        _,       _,       _,    wl,           st => (wl, st)
  | _ + 1,    _,       _,       _,    [],           st => ([], st)
  | fuel + 1, changed, process, deps, lbl :: rest,  st =>
    let (wl', st') := wlStep changed process deps (lbl :: rest, st)
    wlIterateFuel fuel changed process deps wl' st'

/- ===== Analysis state ===== -/

/-- `df_state`: per-instruction values (keyed by `(block, idx)`) + per-block boundary. -/
structure DfState (α : Type) where
  inst     : AssocList (String × Nat) α
  boundary : AssocList String α

/-- `df_at`: lattice value before instruction `idx` in block `lbl` (`bottom` if absent). -/
def dfAt {α : Type} [BEq α] (bottom : α) (st : DfState α) (lbl : String) (idx : Nat) : α :=
  (AssocList.lookup (String × Nat) α st.inst (lbl, idx)).getD bottom

/-- `df_boundary`. -/
def dfBoundary {α : Type} (bottom : α) (st : DfState α) (lbl : String) : α :=
  (AssocList.lookup String α st.boundary lbl).getD bottom

/- ===== Fold transfer across instructions ===== -/

/-- `df_fold_forward`. -/
def dfFoldForward {α : Type} (transfer : Instruction → α → α) (lbl : String)
    : List Instruction → Nat → α → AssocList (String × Nat) α → (α × AssocList (String × Nat) α)
  | [],          idx, acc, instMap => (acc, AssocList.insert (String × Nat) α instMap (lbl, idx) acc)
  | inst :: rest, idx, acc, instMap =>
    let instMap' := AssocList.insert (String × Nat) α instMap (lbl, idx) acc
    dfFoldForward transfer lbl rest (idx + 1) (transfer inst acc) instMap'

/-- `df_fold_backward`. -/
def dfFoldBackward {α : Type} (transfer : Instruction → α → α) (lbl : String)
    : List Instruction → Nat → α → AssocList (String × Nat) α → (α × AssocList (String × Nat) α)
  | [],          idx, acc, instMap => (acc, AssocList.insert (String × Nat) α instMap (lbl, idx) acc)
  | inst :: rest, idx, acc, instMap =>
    let (acc', instMap') := dfFoldBackward transfer lbl rest (idx + 1) acc instMap
    let valBefore := transfer inst acc'
    (valBefore, AssocList.insert (String × Nat) α instMap' (lbl, idx) valBefore)

/-- `df_fold_block`. -/
def dfFoldBlock {α : Type} (dir : Direction) (transfer : Instruction → α → α) (lbl : String)
    (instrs : List Instruction) (initVal : α) : (α × AssocList (String × Nat) α) :=
  match dir with
  | Direction.Forward  => dfFoldForward  transfer lbl instrs 0 initVal []
  | Direction.Backward => dfFoldBackward transfer lbl instrs 0 initVal []

/- ===== Per-block processing ===== -/

/-- `df_joined_val`: join the neighbour boundaries (+ optional entry override). -/
def dfJoinedVal {α γ : Type} (dir : Direction) (bottom : α) (join : α → α → α)
    (edgeTransfer : γ → String → String → α → α) (ctx : γ) (entryVal : Option (String × α))
    (cfg : CfgAnalysis) (st : DfState α) (lbl : String) : α :=
  let neighbors :=
    match dir with
    | Direction.Forward  => cfg.predsOf lbl
    | Direction.Backward => cfg.succsOf lbl
  let edgeVals := neighbors.map (fun nbr => edgeTransfer ctx nbr lbl (dfBoundary bottom st nbr))
  let base := match edgeVals with | [] => bottom | _ => edgeVals.foldl join bottom
  match entryVal with
  | none => base
  | some (evLbl, v) => if lbl = evLbl then join v base else base

private def findBlock (lbl : String) (bbs : List BasicBlock) : Option BasicBlock :=
  bbs.find? (·.label == lbl)

/-- `df_process_block`: one block update (join inputs, fold, refresh boundary). -/
def dfProcessBlock {α γ : Type} [BEq α] (dir : Direction) (bottom : α) (join : α → α → α)
    (transfer : γ → Instruction → α → α) (edgeTransfer : γ → String → String → α → α)
    (ctx : γ) (entryVal : Option (String × α)) (cfg : CfgAnalysis) (bbs : List BasicBlock)
    (lbl : String) (st : DfState α) : DfState α :=
  let joined := dfJoinedVal dir bottom join edgeTransfer ctx entryVal cfg st lbl
  let instrs := match findBlock lbl bbs with | none => [] | some bb => bb.instructions
  let (finalVal, _) := dfFoldBlock dir (transfer ctx) lbl instrs joined
  let oldBoundary := dfBoundary bottom st lbl
  let newBoundary := join oldBoundary finalVal
  if newBoundary == oldBoundary then st
  else { st with boundary := AssocList.insert String α st.boundary lbl newBoundary }

/- ===== Initialization + populate + top level ===== -/

/-- `init_df_state`. -/
def initDfState {α : Type} (bottom : α) (lbls : List String) : DfState α :=
  { inst := [], boundary := lbls.foldl (fun m lbl => AssocList.insert String α m lbl bottom) [] }

/-- `df_populate_inst`: after the boundary fixpoint, fill `inst` by folding each block. -/
def dfPopulateInst {α γ : Type} (dir : Direction) (bottom : α) (join : α → α → α)
    (transfer : γ → Instruction → α → α) (edgeTransfer : γ → String → String → α → α)
    (ctx : γ) (entryVal : Option (String × α)) (cfg : CfgAnalysis) (bbs : List BasicBlock)
    (lbls : List String) (st : DfState α) : DfState α :=
  lbls.foldl (fun st' lbl =>
    let joined := dfJoinedVal dir bottom join edgeTransfer ctx entryVal cfg st lbl
    let instrs := match findBlock lbl bbs with | none => [] | some bb => bb.instructions
    let (_, instMap) := dfFoldBlock dir (transfer ctx) lbl instrs joined
    { st' with inst := instMap ++ st'.inst }) st

/-- `df_analyze_fuel`: the full fuel-bounded analysis. -/
def dfAnalyzeFuel {α γ : Type} [BEq α] (fuel : Nat) (dir : Direction) (bottom : α)
    (join : α → α → α) (transfer : γ → Instruction → α → α)
    (edgeTransfer : γ → String → String → α → α) (ctx : γ) (entryVal : Option (String × α))
    (fn : IrFunction) : DfState α :=
  let cfg := cfgAnalyze fn
  let bbs := fn.blocks
  let lbls := bbs.map (·.label)
  let st0 := initDfState bottom lbls
  let st0' := match entryVal with
    | none => st0
    | some (lbl, v) => { st0 with boundary := AssocList.insert String α st0.boundary lbl v }
  let process := fun lbl st =>
    dfProcessBlock dir bottom join transfer edgeTransfer ctx entryVal cfg bbs lbl st
  let changed := fun lbl old new => dfBoundary bottom new lbl != dfBoundary bottom old lbl
  let deps := match dir with
    | Direction.Forward  => cfg.succsOf
    | Direction.Backward => cfg.predsOf
  let wl0 := match dir with
    | Direction.Forward  => cfg.dfsPre
    | Direction.Backward => cfg.dfsPost
  let boundaryResult := (wlIterateFuel fuel changed process deps wl0 st0').2
  dfPopulateInst dir bottom join transfer edgeTransfer ctx entryVal cfg bbs lbls boundaryResult

end EvmYul.Venom.Hol.Codegen

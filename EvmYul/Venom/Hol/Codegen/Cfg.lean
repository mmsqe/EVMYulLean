import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics

/-!
# Control-flow graph analysis

Port of `vyper-hol main:venom/analysis/cfg/defs/cfgDefsScript.sml` (the parts the
dataflow framework needs): the successor/predecessor maps and the DFS pre/post
orders (used as worklist seed). HOL defines the DFS by a manual well-founded
recursion on `CARD (FDOM succs \ visited)`; here it's a structural recursion on
`fuel` (with the same `visited` guard), and `cfgAnalyze` supplies a fuel bound large
enough that it never cuts a real DFS short.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `get_label`. -/
def getLabel : Operand → Option String
  | Operand.Label l => some l
  | _               => none

/-- `get_successors`: target labels of a terminator instruction. -/
def getSuccessors (inst : Instruction) : List String :=
  if isTerminator inst.opcode then inst.operands.filterMap getLabel else []

/-- `bb_succs`: a block's successor labels (from its terminator). -/
def bbSuccs (bb : BasicBlock) : List String :=
  match bb.instructions with
  | []    => []
  | insts => (getSuccessors insts.getLast!).reverse.dedup

/-- `entry_block`: the first block. -/
def entryBlock (fn : IrFunction) : Option BasicBlock := fn.blocks.head?

/- ===== Result type + queries ===== -/

/-- `cfg_analysis`. -/
structure CfgAnalysis where
  succs     : AssocList String (List String)
  preds     : AssocList String (List String)
  reachable : AssocList String Bool
  dfsPost   : List String
  dfsPre    : List String

/-- `fmap_lookup_list`. -/
def fmapLookupList (m : AssocList String (List String)) (k : String) : List String :=
  (AssocList.lookup String (List String) m k).getD []

/-- `cfg_succs_of`. -/
def CfgAnalysis.succsOf (cfg : CfgAnalysis) (lbl : String) : List String :=
  fmapLookupList cfg.succs lbl

/-- `cfg_preds_of`. -/
def CfgAnalysis.predsOf (cfg : CfgAnalysis) (lbl : String) : List String :=
  fmapLookupList cfg.preds lbl

/- ===== succ / pred map construction ===== -/

/-- `set_insert`. -/
def setInsert (x : String) (xs : List String) : List String :=
  if xs.contains x then xs else x :: xs

/-- label → [] for all blocks (`init_succs` / `init_preds`). -/
def initLblMap (bbs : List BasicBlock) : AssocList String (List String) :=
  bbs.foldl (fun m bb => AssocList.insert String (List String) m bb.label []) []

/-- `build_succs`. -/
def buildSuccs (bbs : List BasicBlock) : AssocList String (List String) :=
  bbs.foldl (fun m bb => AssocList.insert String (List String) m bb.label (bbSuccs bb))
    (initLblMap bbs)

/-- `build_preds`. -/
def buildPreds (bbs : List BasicBlock) (succs : AssocList String (List String))
    : AssocList String (List String) :=
  bbs.foldl (fun m bb =>
    let succsLbl := fmapLookupList succs bb.label
    succsLbl.foldr (fun succ m2 =>
      let old := fmapLookupList m2 succ
      AssocList.insert String (List String) m2 succ (setInsert bb.label old)) m)
    (initLblMap bbs)

/- ===== DFS (fuel-bounded mutual recursion) ===== -/

mutual
/-- `dfs_post_walk`. -/
def dfsPostWalk : Nat → AssocList String (List String) → List String → String →
    (List String × List String)
  | 0,        _,     visited, _   => (visited, [])
  | fuel + 1, succs, visited, lbl =>
    if visited.contains lbl then (visited, [])
    else
      let visited' := setInsert lbl visited
      let (vis2, orders) := dfsPostWalkList fuel succs visited' (fmapLookupList succs lbl)
      (vis2, orders ++ [lbl])
/-- `dfs_post_walk_list`. -/
def dfsPostWalkList : Nat → AssocList String (List String) → List String → List String →
    (List String × List String)
  | 0,        _,     visited, _       => (visited, [])
  | _ + 1,    _,     visited, []      => (visited, [])
  | fuel + 1, succs, visited, s :: ss =>
    let (v', ords')   := dfsPostWalk fuel succs visited s
    let (v'', ords'') := dfsPostWalkList fuel succs v' ss
    (v'', ords' ++ ords'')
end

mutual
/-- `dfs_pre_walk`. -/
def dfsPreWalk : Nat → AssocList String (List String) → List String → String →
    (List String × List String)
  | 0,        _,     visited, _   => (visited, [])
  | fuel + 1, succs, visited, lbl =>
    if visited.contains lbl then (visited, [])
    else
      let visited' := setInsert lbl visited
      let (vis2, orders) := dfsPreWalkList fuel succs visited' (fmapLookupList succs lbl)
      (vis2, lbl :: orders)
/-- `dfs_pre_walk_list`. -/
def dfsPreWalkList : Nat → AssocList String (List String) → List String → List String →
    (List String × List String)
  | 0,        _,     visited, _       => (visited, [])
  | _ + 1,    _,     visited, []      => (visited, [])
  | fuel + 1, succs, visited, s :: ss =>
    let (v', ords')   := dfsPreWalk fuel succs visited s
    let (v'', ords'') := dfsPreWalkList fuel succs v' ss
    (v'', ords' ++ ords'')
end

/-- `build_reachable`. -/
def buildReachable (labels : List String) (visited : List String) : AssocList String Bool :=
  labels.foldl (fun m k => AssocList.insert String Bool m k (visited.contains k)) []

/- ===== top-level ===== -/

/-- `cfg_analyze`. -/
def cfgAnalyze (fn : IrFunction) : CfgAnalysis :=
  let bbs := fn.blocks
  let succs := buildSuccs bbs
  let preds := buildPreds bbs succs
  let labels := bbs.map (·.label)
  -- fuel ≥ total DFS calls (≤ 2·(#blocks + #edges)); the visited guard does the real bounding.
  let fuel := 2 * (bbs.length + bbs.foldl (fun a bb => a + (bbSuccs bb).length) 0) + 10
  let (visPost, post) :=
    match entryBlock fn with
    | none    => ([], [])
    | some bb => dfsPostWalk fuel succs [] bb.label
  let (_, pre) :=
    match entryBlock fn with
    | none    => ([], [])
    | some bb => dfsPreWalk fuel succs [] bb.label
  { succs := succs, preds := preds, reachable := buildReachable labels visPost,
    dfsPost := post, dfsPre := pre }

end EvmYul.Venom.Hol.Codegen

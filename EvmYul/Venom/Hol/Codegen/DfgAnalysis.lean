import EvmYul.Venom.Hol.Types

/-!
# Data-flow graph (DFG) — query side

Port of `vyper-hol main:venom/analysis/dfg/defs/dfgDefsScript.sml` (the parts the
stack-plan generator queries). The generator takes a `DfgAnalysis` as input and uses
`operandEquiv` to decide when two operands denote the same SSA value (so a reorder /
optimistic swap can be skipped). `operandEquiv` normalizes each operand by following
the `ASSIGN` chain (`normalizeOperand`) and compares the roots.

The DFG *builder* (constructing a `DfgAnalysis` from a function) is a separate piece,
deferred to the function-level wiring.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `dfg_analysis`: use/def/id maps over a function's instructions. -/
structure DfgAnalysis where
  uses : AssocList String (List Instruction)
  defs : AssocList String Instruction
  ids  : AssocList Nat Instruction

/-- `dfg_empty`. -/
def DfgAnalysis.empty : DfgAnalysis := ⟨[], [], []⟩

instance : Inhabited DfgAnalysis := ⟨DfgAnalysis.empty⟩

/-- `dfg_get_def`. -/
def DfgAnalysis.getDef (dfg : DfgAnalysis) (v : String) : Option Instruction :=
  AssocList.lookup String Instruction dfg.defs v

/-- `normalize_operand`: follow the `ASSIGN` chain to the root operand.

    HOL uses well-founded recursion on `CARD (FDOM defs \ visited)`; here the
    recursion is structural on `fuel` and the `visited` guard breaks any cycle, so
    for valid SSA (acyclic ASSIGN chains shorter than the number of defs) the result
    is exactly the HOL one. `operandEquiv` supplies `fuel = |defs| + 1`. -/
def normalizeOperand : Nat → DfgAnalysis → List String → Operand → Operand
  | 0,        _,   _,       op => op
  | fuel + 1, dfg, visited, op =>
    match op with
    | Operand.Var v =>
      if visited.contains v then Operand.Var v
      else
        match dfg.getDef v with
        | some inst =>
          if inst.opcode = Opcode.ASSIGN then
            match inst.operands with
            | [op'] => normalizeOperand fuel dfg (v :: visited) op'
            | _     => Operand.Var v
          else Operand.Var v
        | none => Operand.Var v
    | _ => op

/-- `operand_equiv`: equal up to `ASSIGN`-chain normalization. -/
def operandEquiv (dfg : DfgAnalysis) (op1 op2 : Operand) : Bool :=
  let fuel := dfg.defs.length + 1
  normalizeOperand fuel dfg [] op1 == normalizeOperand fuel dfg [] op2

/- ===== DFG builder (function → DfgAnalysis) ===== -/

/-- `operand_var`: a `Var`'s name, else `none`. -/
def operandVar : Operand → Option String
  | Operand.Var v => some v
  | _             => none

/-- `operand_vars`: the variable names among a list of operands. -/
def operandVars (ops : List Operand) : List String := ops.filterMap operandVar

/-- `dfg_get_uses`. -/
def DfgAnalysis.getUses (dfg : DfgAnalysis) (v : String) : List Instruction :=
  (AssocList.lookup String (List Instruction) dfg.uses v).getD []

/-- `dfg_add_use`. (HOL dedups by `MEM inst uses`; here by instruction `id`, which
    is equivalent for unique-id SSA and avoids a structural `BEq Instruction`.) -/
def DfgAnalysis.addUse (dfg : DfgAnalysis) (v : String) (inst : Instruction) : DfgAnalysis :=
  let uses := dfg.getUses v
  if uses.any (fun i => i.id == inst.id) then dfg
  else { dfg with uses := AssocList.insert String (List Instruction) dfg.uses v (inst :: uses) }

/-- `dfg_add_uses`. -/
def DfgAnalysis.addUses : DfgAnalysis → List String → Instruction → DfgAnalysis
  | dfg, [],      _    => dfg
  | dfg, v :: vs, inst => DfgAnalysis.addUses (dfg.addUse v inst) vs inst

/-- `dfg_add_defs`. -/
def DfgAnalysis.addDefs : DfgAnalysis → List String → Instruction → DfgAnalysis
  | dfg, [],      _    => dfg
  | dfg, v :: vs, inst =>
    DfgAnalysis.addDefs { dfg with defs := AssocList.insert String Instruction dfg.defs v inst } vs inst

/-- `dfg_add_inst`: register a single instruction's uses, defs and id. -/
def DfgAnalysis.addInst (dfg : DfgAnalysis) (inst : Instruction) : DfgAnalysis :=
  let inVars := operandVars inst.operands
  let dfg1 := dfg.addUses inVars inst
  let dfg2 := dfg1.addDefs inst.outputs inst
  { dfg2 with ids := AssocList.insert Nat Instruction dfg2.ids inst.id inst }

/-- `dfg_build_insts_rev`. -/
def DfgAnalysis.buildInstsRev : DfgAnalysis → List Instruction → DfgAnalysis
  | dfg, []          => dfg
  | dfg, inst :: rest => DfgAnalysis.buildInstsRev (dfg.addInst inst) rest

/-- `dfg_build_insts`: build over instructions (HOL folds the reversed list). -/
def DfgAnalysis.buildInsts (insts : List Instruction) : DfgAnalysis :=
  DfgAnalysis.buildInstsRev DfgAnalysis.empty insts.reverse

/-- `dfg_build_function`: build the DFG of a whole function. -/
def DfgAnalysis.buildFunction (fn : IrFunction) : DfgAnalysis :=
  DfgAnalysis.buildInsts (fn.blocks.flatMap (·.instructions))

end EvmYul.Venom.Hol.Codegen

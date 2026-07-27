import EvmYul.UInt256

/-!
# Venom IR — operands

[Venom](https://docs.vyperlang.org/en/latest/venom.html) is Vyper's
SSA-based optimizing IR (selected by `vyper --experimental-codegen`).
Unlike stack-based EVM bytecode, Venom instructions operate on *named SSA
values*. An operand (`vyper.venom.basicblock.IROperand`) is one of three
things:

* an **`IRLiteral`** — a 256-bit integer constant;
* an **`IRVariable`** — a `%`-prefixed SSA variable name; or
* an **`IRLabel`** — a basic-block / function label (a jump target).

We model the three with one inductive. Variable and label names are kept
as `String`s (matching the Python IR, which stores them verbatim), so the
representation round-trips with a parsed `.venom` file.
-/

namespace EvmYul.Venom

/-- An SSA variable name (the Python IR stores these `%`-prefixed, e.g.
`%1`, `%cond`). We keep whatever string the producer used. -/
abbrev VarName := String

/-- A basic-block / function label (a jump target). -/
abbrev Label := String

/-- A Venom operand: a literal, an SSA variable, or a label.

Mirrors `vyper.venom.basicblock.IROperand`'s three concrete subclasses
(`IRLiteral`, `IRVariable`, `IRLabel`). -/
inductive Operand where
  /-- A 256-bit integer literal (`IRLiteral`). -/
  | lit (n : UInt256)
  /-- An SSA variable reference (`IRVariable`). -/
  | var (x : VarName)
  /-- A label / jump target (`IRLabel`). -/
  | label (l : Label)
deriving DecidableEq, Inhabited, Repr

namespace Operand

/-- Is this operand a label? (Used to split jump targets from value
operands, as `IRInstruction.get_label_operands` does.) -/
def isLabel : Operand → Bool
  | .label _ => true
  | _        => false

/-- The label carried by an operand, if it is one. -/
def asLabel? : Operand → Option Label
  | .label l => some l
  | _        => none

end Operand

end EvmYul.Venom

import EvmYul.Venom.Operand

/-!
# Venom IR — instructions, basic blocks, functions

A Venom `IRInstruction` is `opcode (str) + operands (list) + outputs
(list of variables)`. The vast majority of instructions have zero or one
output; we model the single-output case (`output : Option VarName`),
which covers every opcode the Vyper backend emits (`phi`/`param`/`invoke`
included — `invoke` with multiple returns is lowered before assembly).

`Op` enumerates the opcodes we give semantics to, grouped as:

* **pure arithmetic / bitwise / comparison** — evaluated purely from
  operand values (`add`, `lt`, `and`, `shl`, …);
* **memory** — `mload` / `mstore` / `mstore8` / `mcopy` / `msize`;
* **storage** — `sload` / `sstore` and transient `tload` / `tstore`;
* **`keccak256`** — hashes a memory window (FFI, opaque);
* **SSA / pseudo** — `assign` (the SSA copy, formerly `store`), `phi`,
  `param`, `nop`;
* **terminators** — `jmp` / `jnz` / `djmp` (control flow) and the halting
  `ret` / `return` / `revert` / `stop` / `invalid` / `selfdestruct`.

Opcodes that touch the wider call environment (`call`, `create`, `log`,
`calldataload`, …) are represented by `Op.unsupported` so a program that
uses them parses and steps to a well-defined *stuck* state rather than
being unrepresentable. See `EvmYul/Venom/Semantics.lean`.
-/

namespace EvmYul.Venom

/-- Venom opcodes we model. The string spelling in the IR is the
lower-cased constructor name (`Op.keccak256` ↔ `"keccak256"`), except
`assign` which the IR historically also spelled `store`. -/
inductive Op where
  -- Arithmetic
  | add | sub | mul | div | sdiv | mod | smod | exp | addmod | mulmod | signextend
  -- Comparison
  | lt | gt | slt | sgt | eq | iszero
  -- Bitwise
  | and | or | xor | not | shl | shr | sar | byte
  -- Hashing
  | keccak256
  -- Memory
  | mload | mstore | mstore8 | msize | mcopy
  -- Storage (persistent + transient)
  | sload | sstore | tload | tstore
  -- Call environment / calldata
  | calldataload | calldatasize | calldatacopy | callvalue | caller | «address» | «assert»
  -- Logging (events) — modelled as a no-op (no storage/return effect)
  | log
  -- SSA / pseudo
  | assign | phi | param | nop
  -- Control-flow terminators
  | jmp | jnz | djmp
  -- Halting terminators
  | ret | «return» | revert | stop | invalid | selfdestruct
  -- Anything we do not give semantics to (call/create/log/calldata/…)
  | unsupported (name : String)
deriving Inhabited, Repr

namespace Op

/-- The instructions Venom treats as basic-block terminators
(`vyper.venom.basicblock.BB_TERMINATORS`). -/
def isTerminator : Op → Bool
  | jmp | djmp | jnz | ret | «return» | revert | stop | invalid | selfdestruct => true
  | _ => false

/-- Terminators that halt the message-call execution entirely
(`HALTING_TERMINATORS`). -/
def isHalting : Op → Bool
  | «return» | revert | stop | invalid | selfdestruct => true
  | _ => false

/-- The pseudo-instructions that are not real machine ops. -/
def isPseudo : Op → Bool
  | phi | param | nop => true
  | _ => false

end Op

/-- A single Venom instruction: `output = opcode operands…`.

* `output = none` for instructions with no result (`mstore`, `sstore`,
  the terminators, …; `NO_OUTPUT_INSTRUCTIONS` in the Python IR).
* Operand order follows the IR's printed order. For `phi`, operands
  alternate `label, value, label, value, …` (one pair per predecessor
  block). -/
structure Instruction where
  output   : Option VarName := none
  opcode   : Op
  operands : List Operand := []
deriving Inhabited, Repr

/-- A basic block: an (ordered) list of instructions. The last
instruction is expected to be a terminator (`Op.isTerminator`); the exec
semantics treat a missing terminator as a stuck state. -/
structure BasicBlock where
  label : Label
  instrs : List Instruction
deriving Inhabited, Repr

/-- A Venom function: a labelled entry block plus the remaining blocks,
forming a CFG keyed by block label. -/
structure Function where
  entry : Label
  blocks : List BasicBlock
deriving Inhabited, Repr

namespace Function

/-- Look a block up by its label. -/
def find? (fn : Function) (l : Label) : Option BasicBlock :=
  fn.blocks.find? (·.label == l)

end Function

end EvmYul.Venom

import EvmYul.Venom.Instruction

/-!
# A parser for Vyper's `.venom` text format

Turns the textual Venom IR that `vyper --experimental-codegen` emits (the
format round-tripped by `vyper.venom.parser`) into `EvmYul.Venom.Function`s,
so the Lean interpreter can run real compiler output as a reference oracle.

The format is line-oriented:

```
function runtime [fmp_lowered] {
  runtime:                       ; a basic-block label
      %1 = calldatasize          ; assignment: lhs = instruction
      %82 = 4                    ; assignment: lhs = operand   (a copy)
      %2 = gt %82, %1
      jnz %2, @then, @else       ; bare instruction (no output)
      ...
  data readonly { ... }          ; data segment (skipped)
}
```

Operands are `%var`, `@label`, or a constant (`4`, `0x2a`, `-1`). Keccak is
spelled `sha3`. Comments start with `;`, `//`, or `#`. We do a forgiving
line scan rather than a full grammar parse: enough to execute real output,
not to validate it. Unmodelled opcodes become `Op.unsupported` and step to
a defined `stuck` state.
-/

namespace EvmYul.Venom
namespace Parse

/-! ## Lexical helpers -/

/-- Drop a trailing `;`, `//`, or `#` comment. -/
def stripComment (line : String) : String :=
  ((line.splitOn ";").headD "" |>.splitOn "//").headD "" |>.splitOn "#" |>.headD ""

/-- Split on spaces/tabs and commas, dropping empties. -/
def tokenize (s : String) : List String :=
  ((s.replace "," " ").split (fun c => c == ' ' || c == '\t')).toList.map (·.toString) |>.filter (· ≠ "")

/-- Strip a surrounding pair of double quotes (escaped-string labels). -/
def unquote (s : String) : String :=
  if s.startsWith "\"" && s.endsWith "\"" then ((s.drop 1).dropEnd 1).toString else s

private def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else
    let lc := c.toLower
    if 'a' ≤ lc && lc ≤ 'f' then some (10 + (lc.toNat - 'a'.toNat)) else none

private def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c => if c == '_' then acc else acc * 16 + (hexDigit? c).getD 0) 0

/-- The magnitude of a (non-negative) numeric token. -/
private def parseMag (t : String) : Nat :=
  if t.startsWith "0x" || t.startsWith "0X" then hexToNat (t.drop 2).toString
  else (t.toNat?).getD 0

/-- Parse a constant token (`4`, `0x2a`, `-1`) to a `UInt256` (two's
complement for negatives). -/
def parseConst (t : String) : UInt256 :=
  if t.startsWith "-" then
    let m := parseMag (t.drop 1).toString % UInt256.size
    UInt256.ofNat ((UInt256.size - m) % UInt256.size)
  else UInt256.ofNat (parseMag t)

/-- Parse a single operand token. -/
def parseOperand (t : String) : Operand :=
  if t.startsWith "%" then .var t
  else if t.startsWith "@" then .label (unquote (t.drop 1).toString)
  else .lit (parseConst t)

/-- Does a token denote an operand (vs an opcode mnemonic)? -/
def isOperandTok (t : String) : Bool :=
  t.startsWith "%" || t.startsWith "@" || t.startsWith "0x" || t.startsWith "-" ||
    (match t.toList.head? with | some c => c.isDigit | none => false)

/-! ## Opcode mnemonics -/

/-- Map a Venom opcode mnemonic to an `Op`. `sha3` is keccak; `store`/`assign`
are the SSA copy; unknown mnemonics become `Op.unsupported`. -/
def parseOp : String → Op
  | "add" => .add | "sub" => .sub | "mul" => .mul | "div" => .div | "sdiv" => .sdiv
  | "mod" => .mod | "smod" => .smod | "exp" => .exp | "addmod" => .addmod
  | "mulmod" => .mulmod | "signextend" => .signextend
  | "lt" => .lt | "gt" => .gt | "slt" => .slt | "sgt" => .sgt | "eq" => .eq
  | "iszero" => .iszero
  | "and" => .and | "or" => .or | "xor" => .xor | "not" => .not
  | "shl" => .shl | "shr" => .shr | "sar" => .sar | "byte" => .byte
  | "sha3" => .keccak256 | "keccak256" => .keccak256
  | "mload" => .mload | "mstore" => .mstore | "mstore8" => .mstore8
  | "msize" => .msize | "mcopy" => .mcopy
  | "sload" => .sload | "sstore" => .sstore | "tload" => .tload | "tstore" => .tstore
  | "calldataload" => .calldataload | "calldatasize" => .calldatasize
  | "calldatacopy" => .calldatacopy | "callvalue" => .callvalue
  | "caller" => .caller | "address" => .«address» | "assert" => .«assert»
  | "log" => .log
  | "store" => .assign | "assign" => .assign | "phi" => .phi | "param" => .param | "nop" => .nop
  | "jmp" => .jmp | "jnz" => .jnz | "djmp" => .djmp
  | "ret" => .ret | "return" => .«return» | "revert" => .revert | "stop" => .stop
  | "invalid" => .invalid | "selfdestruct" => .selfdestruct
  | other => .unsupported other

/-! ## Statements -/

/-- Parse one statement line (already comment-stripped, non-empty, not a
label/brace) into an `Instruction`. -/
def parseStmt (l : String) : Instruction :=
  match l.splitOn "=" with
  | lhs :: rhs :: _ =>
      let out := (tokenize lhs).head?
      match tokenize rhs with
      | [] => { output := out, opcode := .nop }
      | f :: rest =>
          if isOperandTok f then
            { output := out, opcode := .assign, operands := (f :: rest).map parseOperand }
          else
            { output := out, opcode := parseOp f, operands := rest.map parseOperand }
  | _ =>
      match tokenize l with
      | [] => { opcode := .nop }
      | f :: rest => { opcode := parseOp f, operands := rest.map parseOperand }

/-! ## Function / block assembly -/

/-- Incremental parser state. -/
structure PSt where
  inData    : Bool := false
  curName   : Option String := none
  blocksRev : List BasicBlock := []
  curLbl    : Option String := none
  instrsRev : List Instruction := []
  funcsRev  : List Function := []

/-- Close off the current basic block into `blocksRev`. -/
def PSt.flushBlock (st : PSt) : PSt :=
  match st.curLbl with
  | none => st
  | some lbl =>
      { st with
        blocksRev := { label := lbl, instrs := st.instrsRev.reverse } :: st.blocksRev
        curLbl := none, instrsRev := [] }

/-- Close off the current function into `funcsRev` (entry = first block). -/
def PSt.flushFunc (st : PSt) : PSt :=
  let st := st.flushBlock
  match st.curName with
  | none => st
  | some _ =>
      match st.blocksRev.reverse with
      | [] => { st with curName := none, blocksRev := [] }
      | b :: bs =>
          { st with
            funcsRev := { entry := b.label, blocks := b :: bs } :: st.funcsRev
            curName := none, blocksRev := [] }

/-- Process one source line. -/
def PSt.step (st : PSt) (rawLine : String) : PSt :=
  let l := (stripComment rawLine).trimAscii.toString
  if l == "" then st
  else if st.inData then (if l == "}" then { st with inData := false } else st)
  else if l.startsWith "data " || l == "data" then { st with inData := true }
  else if l.startsWith "function" then
      let st := st.flushFunc
      let nm := unquote ((tokenize l).getD 1 "anon")
      { st with curName := some nm, blocksRev := [], curLbl := none, instrsRev := [] }
  else if l == "{" then st
  else if l == "}" then st.flushFunc
  else if l.endsWith ":" then
      let st := st.flushBlock
      let lbl := unquote ((l.dropEnd 1).toString.trimAscii.toString)
      { st with curLbl := some lbl, instrsRev := [] }
  else { st with instrsRev := parseStmt l :: st.instrsRev }

/-- Parse a whole `.venom` source into its list of functions (entry first). -/
def parseProgram (src : String) : List Function :=
  let st := (src.splitOn "\n").foldl PSt.step {}
  st.flushFunc.funcsRev.reverse

end Parse
end EvmYul.Venom

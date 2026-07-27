import EvmYul.Venom.Semantics

/-!
# M6 — verified Venom → Venom optimization passes

Each pass is a `Function → Function` transform proved to preserve the interpreter
semantics — the property a verified compiler's optimizer needs.

## The generic lifter

Every pass is "apply a block-instruction transform `g` to each block". Two generic
lemmas do all the lifting, so each pass only proves its `execInstr`/`execBlock`
fact and gets the whole-function result for free:

* `execBlock_map` — a per-instruction rewrite that preserves `execInstr`
  preserves `execBlock` (for the `map`-based passes);
* `run_mapBlocks` / `exec_mapBlocks` — a block transform that preserves
  `execBlock` preserves whole-function `run` / `exec` (labels are untouched, so
  `find?` commutes with the transform).

## The passes

* **nop elimination** — drop `nop` instructions (fall-through no-ops);
* **constant folding** (`foldPure`) — fold any pure opcode (`evalPure`) on
  literal operands to an `assign` of the precomputed value;
* **dead-code after a terminator** — terminators never fall through, so the block
  tail is unreachable;
* **algebraic identities** — `add x 0 → x` (an operand-level peephole).
-/

namespace EvmYul.Venom
open EvmYul

/-! ## The generic pass lifter -/

/-- A per-instruction rewrite preserving `execInstr` preserves block execution. -/
theorem execBlock_map (g : Instruction → Instruction)
    (hg : ∀ s i, execInstr s (g i) = execInstr s i) (s : VenomState) (instrs : List Instruction) :
    execBlock s (instrs.map g) = execBlock s instrs := by
  induction instrs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [List.map_cons, execBlock, execBlock, hg]
    cases hstep : execInstr s i with
    | mk s' c => cases c <;> first | exact ih s' | rfl

/-- Apply a block-instruction transform `g` to every block of a function. -/
def Function.mapBlocks (g : List Instruction → List Instruction) (fn : Function) : Function :=
  { fn with blocks := fn.blocks.map (fun bb => { bb with instrs := g bb.instrs }) }

/-- The transform preserves block labels, so `find?` commutes with it. -/
theorem find?_mapBlocks (g : List Instruction → List Instruction) (fn : Function) (lbl : Label) :
    (fn.mapBlocks g).find? lbl = (fn.find? lbl).map (fun bb => { bb with instrs := g bb.instrs }) := by
  unfold Function.mapBlocks Function.find?; rw [List.find?_map]; rfl

/-- **The generic pass lifter.** A block transform preserving block execution
preserves whole-function execution. -/
theorem run_mapBlocks (g : List Instruction → List Instruction)
    (hg : ∀ s instrs, execBlock s (g instrs) = execBlock s instrs)
    (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState) :
    run (fn.mapBlocks g) fuel lbl s = run fn fuel lbl s := by
  induction fuel generalizing lbl s with
  | zero => rfl
  | succ f ih =>
    rw [run, run, find?_mapBlocks]
    cases hf : fn.find? lbl with
    | none => rfl
    | some bb =>
      simp only [Option.map_some]
      rw [show execBlock s (g bb.instrs) = execBlock s bb.instrs from hg s bb.instrs]
      cases hb : execBlock s bb.instrs with
      | mk s' c => cases c <;> simp_all

/-- … and `Function.exec` (run from the entry block). -/
theorem exec_mapBlocks (g : List Instruction → List Instruction)
    (hg : ∀ s instrs, execBlock s (g instrs) = execBlock s instrs)
    (fn : Function) (fuel : Nat) (s : VenomState) :
    (fn.mapBlocks g).exec fuel s = fn.exec fuel s :=
  run_mapBlocks g hg fn fuel fn.entry s

/-! ## Nop elimination

`removeNops` drops every `nop` instruction. Since the interpreter falls through a
`nop` with no effect, removing them preserves block and whole-function execution. -/

/-- Is this opcode a `nop` (a pure no-op the interpreter falls through)? -/
def Op.isNop : Op → Bool
  | .nop => true
  | _    => false

/-- **Pass: nop elimination (block).** Drop every `nop` instruction. -/
def removeNops (instrs : List Instruction) : List Instruction :=
  instrs.filter (fun i => !i.opcode.isNop)

/-- A `nop` steps to a no-op fallthrough (regardless of its operands/output). -/
theorem execInstr_nop (s : VenomState) (i : Instruction) (h : i.opcode = .nop) :
    execInstr s i = (s, .fallthrough) := by
  unfold execInstr; rw [h]

/-- **Nop elimination preserves block execution.** -/
theorem execBlock_removeNops (s : VenomState) (instrs : List Instruction) :
    execBlock s (removeNops instrs) = execBlock s instrs := by
  induction instrs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    show execBlock s ((i :: rest).filter _) = execBlock s (i :: rest)
    rw [List.filter_cons]
    by_cases hn : i.opcode.isNop
    · have hnop : i.opcode = .nop := by cases hop : i.opcode <;> simp_all [Op.isNop]
      simp only [hn, Bool.not_true, Bool.false_eq_true, if_false]
      conv_rhs => rw [execBlock, execInstr_nop s i hnop]
      exact ih s
    · simp only [hn, Bool.not_false, if_true]
      rw [execBlock, execBlock]
      cases hstep : execInstr s i with
      | mk s' c => cases c <;> first | exact ih s' | rfl

/-- **Pass: nop elimination (whole function).** -/
def removeNopsFn : Function → Function := Function.mapBlocks removeNops

theorem run_removeNopsFn (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState) :
    run (removeNopsFn fn) fuel lbl s = run fn fuel lbl s :=
  run_mapBlocks removeNops execBlock_removeNops fn fuel lbl s

theorem exec_removeNopsFn (fn : Function) (fuel : Nat) (s : VenomState) :
    (removeNopsFn fn).exec fuel s = fn.exec fuel s :=
  exec_mapBlocks removeNops execBlock_removeNops fn fuel s

/-! ## Constant folding

`foldPure` folds *every* pure opcode (`evalPure`): an instruction with all-literal
operands becomes an `assign` of the precomputed value, covering all arithmetic /
comparison / bitwise ops (unary or binary). The engine `execInstr_evalPure` shows
any opcode evaluating purely to `v` sets its output to `v`. -/

theorem execInstr_assign_lit (s : VenomState) (out : Option VarName) (v : UInt256) :
    execInstr s { output := out, opcode := .assign, operands := [.lit v] }
      = (s.setOutput out v, .fallthrough) := by
  unfold execInstr; rfl

/-- **Constant-fold engine (value form).** Any instruction interpreted as "set the
output to a constant `v` and fall through" may be replaced by `assign out (lit v)`.
The constant folder supplies `v` by evaluating the instruction at compile time. -/
theorem execInstr_constFold (s : VenomState) (i : Instruction) (v : UInt256)
    (hv : execInstr s i = (s.setOutput i.output v, .fallthrough)) :
    execInstr s i = execInstr s { output := i.output, opcode := .assign, operands := [.lit v] } := by
  rw [hv, execInstr_assign_lit]

/-- **Constant-fold engine (pure form).** Any opcode that evaluates purely
(`evalPure`) to `v` sets its output to `v` and falls through. -/
theorem execInstr_evalPure (s : VenomState) (i : Instruction) (v : UInt256)
    (hv : evalPure i.opcode (i.operands.map (Operand.evalEnv s.env)) = some v) :
    execInstr s i = (s.setOutput i.output v, .fallthrough) := by
  rcases i with ⟨out, op, operands⟩
  cases op <;> simp_all [execInstr, evalPure]

/-- `assign out (lit v)`. -/
def assignLit (out : Option VarName) (v : UInt256) : Instruction :=
  { output := out, opcode := .assign, operands := [.lit v] }

/-- **Pass: constant folding (instruction).** Fold a pure opcode on all-literal
operands to an `assign` of the precomputed value. -/
def foldPure (i : Instruction) : Instruction :=
  match i.operands with
  | [.lit a]         => (evalPure i.opcode [a]).elim i (assignLit i.output)
  | [.lit a, .lit b] => (evalPure i.opcode [a, b]).elim i (assignLit i.output)
  | _                => i

theorem execInstr_foldPure (s : VenomState) (i : Instruction) :
    execInstr s (foldPure i) = execInstr s i := by
  rcases i with ⟨out, op, operands⟩
  unfold foldPure
  split
  · next a heq =>
    subst heq
    cases hev : evalPure op [a] with
    | none => rfl
    | some v =>
      simp only [Option.elim, assignLit, execInstr_assign_lit]
      exact (execInstr_evalPure s ⟨out, op, [.lit a]⟩ v (by simpa [Operand.evalEnv] using hev)).symm
  · next a b heq =>
    subst heq
    cases hev : evalPure op [a, b] with
    | none => rfl
    | some v =>
      simp only [Option.elim, assignLit, execInstr_assign_lit]
      exact (execInstr_evalPure s ⟨out, op, [.lit a, .lit b]⟩ v (by simpa [Operand.evalEnv] using hev)).symm
  · rfl

/-- **Pass: constant folding (block).** -/
def foldPureBlock (instrs : List Instruction) : List Instruction := instrs.map foldPure

theorem execBlock_foldPureBlock (s : VenomState) (instrs : List Instruction) :
    execBlock s (foldPureBlock instrs) = execBlock s instrs :=
  execBlock_map foldPure execInstr_foldPure s instrs

/-- **Pass: constant folding (whole function).** -/
def foldPureFn : Function → Function := Function.mapBlocks foldPureBlock

theorem run_foldPureFn (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState) :
    run (foldPureFn fn) fuel lbl s = run fn fuel lbl s :=
  run_mapBlocks foldPureBlock execBlock_foldPureBlock fn fuel lbl s

theorem exec_foldPureFn (fn : Function) (fuel : Nat) (s : VenomState) :
    (foldPureFn fn).exec fuel s = fn.exec fuel s :=
  exec_mapBlocks foldPureBlock execBlock_foldPureBlock fn fuel s

/-! ## Dead-code elimination after a terminator

`execBlock` stops at the first instruction that does not fall through. A
terminator (`Op.isTerminator`) never falls through whatever its operands, so every
instruction after the first terminator is unreachable. -/

/-- A terminator instruction never falls through (it jumps, branches, or halts),
whatever its operands. -/
theorem execInstr_terminator (s : VenomState) (i : Instruction) (h : i.opcode.isTerminator) :
    (execInstr s i).2 ≠ .fallthrough := by
  rcases i with ⟨out, op, operands⟩
  cases op <;> simp_all [execInstr, Op.isTerminator] <;>
    (first | rfl | (split <;> simp_all))

/-- Once a non-fallthrough instruction is reached, the rest of the block is dead. -/
theorem execBlock_cons_of_ne_fallthrough (s : VenomState) (i : Instruction) (rest : List Instruction)
    (h : (execInstr s i).2 ≠ .fallthrough) :
    execBlock s (i :: rest) = execInstr s i := by
  rw [execBlock]
  cases hstep : execInstr s i with
  | mk s' c =>
    rw [hstep] at h
    cases c <;> simp_all

/-- **Pass: dead-code elimination after a terminator (block).** -/
def truncAtTerminator : List Instruction → List Instruction
  | []        => []
  | i :: rest => if i.opcode.isTerminator then [i] else i :: truncAtTerminator rest

theorem execBlock_truncAtTerminator (s : VenomState) (instrs : List Instruction) :
    execBlock s (truncAtTerminator instrs) = execBlock s instrs := by
  induction instrs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [truncAtTerminator]
    by_cases ht : i.opcode.isTerminator
    · rw [if_pos ht, execBlock_cons_of_ne_fallthrough s i [] (execInstr_terminator s i ht),
        execBlock_cons_of_ne_fallthrough s i rest (execInstr_terminator s i ht)]
    · rw [if_neg ht, execBlock, execBlock]
      cases hstep : execInstr s i with
      | mk s' c => cases c <;> first | exact ih s' | rfl

/-- **Pass: dead-code elimination after a terminator (whole function).** -/
def truncFn : Function → Function := Function.mapBlocks truncAtTerminator

theorem run_truncFn (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState) :
    run (truncFn fn) fuel lbl s = run fn fuel lbl s :=
  run_mapBlocks truncAtTerminator execBlock_truncAtTerminator fn fuel lbl s

theorem exec_truncFn (fn : Function) (fuel : Nat) (s : VenomState) :
    (truncFn fn).exec fuel s = fn.exec fuel s :=
  exec_mapBlocks truncAtTerminator execBlock_truncAtTerminator fn fuel s

/-! ## Algebraic identities

A peephole rewriting instructions by algebraic laws of their operands (not just
constants). Here the additive identity `add x 0 → x`: the operand `x` need not be
a literal — only the `0` is recognized statically. -/

def Op.isAdd : Op → Bool
  | .add => true
  | _    => false

theorem uint256_add_zero (v : UInt256) : UInt256.add v (UInt256.ofNat 0) = v := by
  show (⟨v.val + (UInt256.ofNat 0).val⟩ : UInt256) = v
  have : (UInt256.ofNat 0).val = 0 := by simp [UInt256.ofNat, Id.run, Fin.ofNat]
  rw [this, add_zero]

/-- `assign out [x]` copies operand `x` to the output. -/
theorem execInstr_assign_var (s : VenomState) (out : Option VarName) (x : Operand) :
    execInstr s { output := out, opcode := .assign, operands := [x] }
      = (s.setOutput out (Operand.evalEnv s.env x), .fallthrough) := by
  unfold execInstr; rfl

/-- `add x 0` evaluates to `x` (additive identity). -/
theorem execInstr_add_zero (s : VenomState) (out : Option VarName) (x : Operand) :
    execInstr s { output := out, opcode := .add, operands := [x, .lit (UInt256.ofNat 0)] }
      = (s.setOutput out (Operand.evalEnv s.env x), .fallthrough) := by
  unfold execInstr
  simp only [List.map_cons, List.map_nil]
  rw [show Operand.evalEnv s.env (.lit (UInt256.ofNat 0)) = UInt256.ofNat 0 from rfl]
  show (s.setOutput out (UInt256.add (Operand.evalEnv s.env x) (UInt256.ofNat 0)), Control.fallthrough) = _
  rw [uint256_add_zero]

/-- **Pass: algebraic identity `add x 0 → x` (instruction).** -/
def simplifyInstr (i : Instruction) : Instruction :=
  match i.operands with
  | [x, .lit z] =>
      if i.opcode.isAdd = true ∧ z = UInt256.ofNat 0
      then { output := i.output, opcode := .assign, operands := [x] } else i
  | _ => i

theorem execInstr_simplifyInstr (s : VenomState) (i : Instruction) :
    execInstr s (simplifyInstr i) = execInstr s i := by
  rcases i with ⟨out, op, operands⟩
  unfold simplifyInstr
  split
  · next x z heq =>
    by_cases hc : op.isAdd = true ∧ z = UInt256.ofNat 0
    · rw [if_pos hc, execInstr_assign_var]
      obtain ⟨ha, hz⟩ := hc
      have hop : op = Op.add := by cases op <;> simp_all [Op.isAdd]
      subst heq; subst hop; subst hz
      rw [execInstr_add_zero]
    · rw [if_neg hc]
  · rfl

/-- **Pass: algebraic identities (block).** -/
def simplifyBlock (instrs : List Instruction) : List Instruction := instrs.map simplifyInstr

theorem execBlock_simplifyBlock (s : VenomState) (instrs : List Instruction) :
    execBlock s (simplifyBlock instrs) = execBlock s instrs :=
  execBlock_map simplifyInstr execInstr_simplifyInstr s instrs

/-- **Pass: algebraic identities (whole function).** -/
def simplifyFn : Function → Function := Function.mapBlocks simplifyBlock

theorem run_simplifyFn (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState) :
    run (simplifyFn fn) fuel lbl s = run fn fuel lbl s :=
  run_mapBlocks simplifyBlock execBlock_simplifyBlock fn fuel lbl s

theorem exec_simplifyFn (fn : Function) (fuel : Nat) (s : VenomState) :
    (simplifyFn fn).exec fuel s = fn.exec fuel s :=
  exec_mapBlocks simplifyBlock execBlock_simplifyBlock fn fuel s

end EvmYul.Venom

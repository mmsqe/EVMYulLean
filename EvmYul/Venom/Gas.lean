import EvmYul.Venom.Passes
import EvmYul.EVM.Gas

/-!
# M7 — gas accounting: the optimizer is gas-non-increasing

The Venom interpreter (`Semantics.lean`) tracks no gas; the EVM does (`EVM/Gas.lean`,
the `C'` cost function, `GasConstants`). M7 brings gas to the Venom IR and connects
it to M6: a static per-opcode gas model (`Op.gas`, grounded in the EVM cost classes
`Gverylow = 3`, `Glow = 5`, `Gmid = 8`, …), and the proof that **every M6
optimization pass does not increase gas** — so the optimizer is not just *correct*
(M6) but *beneficial*.

A pass is gas-non-increasing at the block level (`blockGas_*_le`) and, lifted over
the CFG, at the whole-function level (`progGas_*_le`). The map-based passes
(constant folding, algebraic identities) reduce via the per-instruction bound
(folding a pure op to an `assign` cannot cost more, `assign_gas_le_evalPure`);
nop-elimination and dead-code-after-terminator drop instructions, whose gas is
non-negative.
-/

namespace EvmYul.Venom
open EvmYul

/-- A static, state-independent gas charge per Venom opcode, grounded in the EVM
cost classes (`Gverylow = 3`, `Glow = 5`, `Gmid = 8`, …). State-dependent ops
(storage, keccak, calls) take a representative base; the passes never touch them,
so only the relative order among the foldable ops matters. -/
def Op.gas : Op → Nat
  -- pseudo / no-ops
  | .nop | .phi | .param => 0
  -- a copy (DUP/PUSH), Gverylow
  | .assign => 3
  -- arithmetic / comparison / bitwise — the foldable pure ops
  | .add | .sub | .lt | .gt | .slt | .sgt | .eq | .iszero
  | .and | .or | .xor | .not | .shl | .shr | .sar | .byte => 3                  -- Gverylow
  | .mul | .div | .sdiv | .mod | .smod | .signextend => 5                       -- Glow (SIGNEXTEND ∈ Wlow)
  | .addmod | .mulmod => 8                                                      -- Gmid
  | .exp => 10
  -- memory
  | .mload | .mstore | .mstore8 | .mcopy => 3
  | .msize => 2
  -- storage
  | .sload => 2100 | .sstore => 20000 | .tload => 100 | .tstore => 100
  -- hashing / env / logging
  | .keccak256 => 30
  | .calldataload | .calldatasize | .callvalue | .caller | .«address» => 2
  | .calldatacopy => 3 | .«assert» => 3 | .log => 375
  -- control flow
  | .jmp | .djmp => 8 | .jnz => 10
  -- halting terminators
  | .ret | .«return» | .revert | .stop | .invalid | .selfdestruct => 0
  | .unsupported _ => 0

/-- Static gas of an instruction. -/
def instrGas (i : Instruction) : Nat := i.opcode.gas

/-- Static gas of a block. -/
def blockGas (instrs : List Instruction) : Nat := (instrs.map instrGas).sum

/-- A foldable pure opcode costs at least as much as the `assign` it folds to. -/
theorem assign_gas_le_evalPure (op : Op) (vals : List UInt256) (v : UInt256)
    (h : evalPure op vals = some v) : Op.gas .assign ≤ op.gas := by
  cases op <;> simp_all [Op.gas, evalPure]

/-- Generic: a pointwise-`≤` map does not increase the summed image. -/
theorem sum_map_le {α : Type} (f g : α → Nat) (h : ∀ a, f a ≤ g a) (l : List α) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a rest ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih

/-- A `map`-based instruction transform that doesn't increase per-instruction gas
doesn't increase block gas. -/
theorem blockGas_map_le (tf : Instruction → Instruction) (htf : ∀ i, instrGas (tf i) ≤ instrGas i)
    (instrs : List Instruction) : blockGas (instrs.map tf) ≤ blockGas instrs := by
  unfold blockGas; rw [List.map_map]; exact sum_map_le (instrGas ∘ tf) instrGas htf instrs

/-! ## Constant folding does not increase gas -/

theorem instrGas_foldPure_le (i : Instruction) : instrGas (foldPure i) ≤ instrGas i := by
  rcases i with ⟨out, op, operands⟩
  unfold foldPure
  split
  · next a heq =>
    cases hev : evalPure op [a] with
    | none => exact Nat.le_refl _
    | some v => simp only [Option.elim, assignLit, instrGas]; exact assign_gas_le_evalPure op [a] v hev
  · next a b heq =>
    cases hev : evalPure op [a, b] with
    | none => exact Nat.le_refl _
    | some v => simp only [Option.elim, assignLit, instrGas]; exact assign_gas_le_evalPure op [a, b] v hev
  · exact Nat.le_refl _

theorem blockGas_foldPureBlock_le (instrs : List Instruction) :
    blockGas (foldPureBlock instrs) ≤ blockGas instrs :=
  blockGas_map_le foldPure instrGas_foldPure_le instrs

/-! ## Algebraic identities do not increase gas -/

theorem instrGas_simplifyInstr_le (i : Instruction) : instrGas (simplifyInstr i) ≤ instrGas i := by
  rcases i with ⟨out, op, operands⟩
  unfold simplifyInstr
  split
  · next x z heq =>
    by_cases hc : op.isAdd = true ∧ z = UInt256.ofNat 0
    · rw [if_pos hc]
      obtain ⟨ha, _⟩ := hc
      have hop : op = Op.add := by cases op <;> simp_all [Op.isAdd]
      subst hop; simp [instrGas, Op.gas]
    · rw [if_neg hc]
  · exact Nat.le_refl _

theorem blockGas_simplifyBlock_le (instrs : List Instruction) :
    blockGas (simplifyBlock instrs) ≤ blockGas instrs :=
  blockGas_map_le simplifyInstr instrGas_simplifyInstr_le instrs

theorem blockGas_cons (i : Instruction) (rest : List Instruction) :
    blockGas (i :: rest) = instrGas i + blockGas rest := by
  simp [blockGas, List.sum_cons]

/-! ## Nop elimination and dead-code elimination do not increase gas -/

theorem blockGas_removeNops_le (instrs : List Instruction) :
    blockGas (removeNops instrs) ≤ blockGas instrs := by
  induction instrs with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
    by_cases hn : i.opcode.isNop
    · have he : removeNops (i :: rest) = removeNops rest := by simp [removeNops, hn]
      rw [he, blockGas_cons]; omega
    · have he : removeNops (i :: rest) = i :: removeNops rest := by simp [removeNops, hn]
      rw [he, blockGas_cons, blockGas_cons]; omega

theorem blockGas_truncAtTerminator_le (instrs : List Instruction) :
    blockGas (truncAtTerminator instrs) ≤ blockGas instrs := by
  induction instrs with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
    rw [truncAtTerminator, blockGas_cons]
    by_cases ht : i.opcode.isTerminator
    · rw [if_pos ht, blockGas_cons]
      have : blockGas ([] : List Instruction) = 0 := rfl; omega
    · rw [if_neg ht, blockGas_cons]; omega

/-! ## Whole-function: every pass is gas-non-increasing -/

/-- Static gas of a whole function (sum over blocks). -/
def progGas (fn : Function) : Nat := (fn.blocks.map (fun bb => blockGas bb.instrs)).sum

theorem progGas_mapBlocks_le (g : List Instruction → List Instruction)
    (hg : ∀ instrs, blockGas (g instrs) ≤ blockGas instrs) (fn : Function) :
    progGas (fn.mapBlocks g) ≤ progGas fn := by
  unfold progGas Function.mapBlocks
  rw [List.map_map]
  exact sum_map_le _ (fun bb => blockGas bb.instrs) (fun bb => hg bb.instrs) fn.blocks

theorem progGas_removeNopsFn_le (fn : Function) : progGas (removeNopsFn fn) ≤ progGas fn :=
  progGas_mapBlocks_le removeNops blockGas_removeNops_le fn

theorem progGas_foldPureFn_le (fn : Function) : progGas (foldPureFn fn) ≤ progGas fn :=
  progGas_mapBlocks_le foldPureBlock blockGas_foldPureBlock_le fn

theorem progGas_truncFn_le (fn : Function) : progGas (truncFn fn) ≤ progGas fn :=
  progGas_mapBlocks_le truncAtTerminator blockGas_truncAtTerminator_le fn

theorem progGas_simplifyFn_le (fn : Function) : progGas (simplifyFn fn) ≤ progGas fn :=
  progGas_mapBlocks_le simplifyBlock blockGas_simplifyBlock_le fn

/-! ## Faithfulness: `Op.gas` is the real EVM cost `C'`

The static model is not ad-hoc: for the arithmetic / comparison / bitwise opcodes
— the ones the optimizer folds, whose EVM cost is state-independent — `Op.gas`
equals the EVM's actual cost function `C'` for *any* machine state, via the EVM
opcode each lowers to (`evmOpOf`). (`exp` is excluded: its cost depends on the
exponent; storage / memory / call ops are state-dependent and untouched by the
passes, so their `Op.gas` is a representative base.) -/

/-- The EVM opcode a (state-independent foldable) Venom op lowers to. -/
def evmOpOf : Op → Operation .EVM
  | .add => .ADD | .sub => .SUB | .mul => .MUL | .div => .DIV | .sdiv => .SDIV
  | .mod => .MOD | .smod => .SMOD | .signextend => .SIGNEXTEND
  | .lt => .LT | .gt => .GT | .slt => .SLT | .sgt => .SGT | .eq => .EQ | .iszero => .ISZERO
  | .and => .AND | .or => .OR | .xor => .XOR | .not => .NOT
  | .shl => .SHL | .shr => .SHR | .sar => .SAR | .byte => .BYTE
  | .addmod => .ADDMOD | .mulmod => .MULMOD | .exp => .EXP
  | _ => .STOP

/-- The state-independent foldable opcodes (arithmetic / comparison / bitwise,
excluding `exp` whose cost depends on the exponent). -/
def Op.isArith : Op → Bool
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .signextend
  | .lt | .gt | .slt | .sgt | .eq | .iszero | .and | .or | .xor | .not
  | .shl | .shr | .sar | .byte | .addmod | .mulmod => true
  | _ => false

open EvmYul.EVM Operation InstructionGasGroups GasConstants in
/-- **Faithfulness.** For every foldable arithmetic opcode and *any* machine
state, the static `Op.gas` is exactly the EVM cost `C'` of the opcode it lowers
to — so the gas model the optimizer is judged against is the real one. -/
theorem C'_eq_gas (s : EVM.State) (op : Op) (h : op.isArith) : C' s (evmOpOf op) = op.gas := by
  cases op <;> simp_all [Op.isArith, evmOpOf, Op.gas, C', Wcopy, Wextaccount, Wzero, Wbase,
    Wverylow, Wlow, Wmid, Glow, Gmid, Gverylow,
    Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs, Wverylow.swapInstrs]

open EvmYul.EVM in
/-- A foldable instruction's static gas is its real EVM cost. -/
theorem instrGas_eq_C' (s : EVM.State) (i : Instruction) (h : i.opcode.isArith) :
    instrGas i = C' s (evmOpOf i.opcode) := (C'_eq_gas s i.opcode h).symm

/-! ## State-dependent gas, and the optimizer is beneficial in *real* EVM gas

`C'` is state-independent for the `W`-class opcodes (so `C'_eq_gas` covers them
exactly). The genuine state-dependence lives in a few ops; here are their exact
characterizations, plus the payoff — folding a pure op to a constant reduces
*real* EVM gas, not just the static model, even for the state-dependent `exp`.

The other accumulating gas (memory expansion) is the *separate* non-negative
`memoryExpansionCost`, never part of `C'`. -/

open EvmYul.EVM Operation InstructionGasGroups GasConstants

/-- Exact `EXP` cost — the exponent-dependent state cost. -/
theorem C'_exp (s : EVM.State) :
    C' s .EXP = if s.stack[1]! == ⟨0⟩ then Gexp
                else Gexp + Gexpbyte * (1 + Nat.log 256 s.stack[1]!.toNat) := by
  simp [C']

/-- `EXP` costs at least its base `Gexp` (a sound floor, any exponent). -/
theorem Gexp_le_C'_exp (s : EVM.State) : Gexp ≤ C' s .EXP := by
  rw [C'_exp]; split <;> omega

/-- Exact `SLOAD` cost — warm vs cold (the access-list state dependence). -/
theorem C'_sload (s : EVM.State) :
    C' s .SLOAD = if s.substate.accessedStorageKeys.contains (s.executionEnv.codeOwner, s.stack[0]!)
                  then Gwarmaccess else Gcoldsload := by
  simp [C', Csload]

/-- A `PUSH` (what a folded constant becomes) costs `Gverylow`. -/
theorem C'_push (s : EVM.State) : C' s (.Push .PUSH1) = Gverylow := by
  simp [C', Wcopy, Wextaccount, Wzero, Wbase, Wverylow, Gverylow,
    Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs, Wverylow.swapInstrs]

/-- A memory op's `C'` base is state-independent (`Gverylow`); the access's
size-dependent cost is the *separate* `memoryExpansionCost`, never part of `C'`. -/
theorem C'_mload (s : EVM.State) : C' s .MLOAD = Gverylow := by
  simp [C', Wcopy, Wextaccount, Wzero, Wbase, Wverylow, Gverylow,
    Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs, Wverylow.swapInstrs]

/-- **Folding a state-independent arithmetic op reduces real EVM gas.** The folded
constant (a `PUSH`, `Gverylow`) costs no more than the op it replaced. -/
theorem foldArith_C'_le (s : EVM.State) (op : Op) (h : op.isArith) :
    C' s (.Push .PUSH1) ≤ C' s (evmOpOf op) := by
  rw [C'_push, C'_eq_gas s op h]
  cases op <;> simp_all [Op.isArith, Op.gas, Gverylow]

/-- **Folding `exp` reduces real EVM gas** (its base `Gexp = 10` already exceeds a
`PUSH`'s `Gverylow = 3`), despite its cost being state-dependent. -/
theorem foldExp_C'_le (s : EVM.State) : C' s (.Push .PUSH1) ≤ C' s (evmOpOf .exp) := by
  rw [C'_push]; exact le_trans (by decide : Gverylow ≤ Gexp) (Gexp_le_C'_exp s)

/-! ## The composed optimizer — the M6 × M7 capstone

The four verified passes composed into a single `optimizeFn`. Read
right-to-left: constant-fold pure ops, apply the algebraic peephole, drop the
resulting nops, then truncate dead code after each block's terminator. The two
headline theorems tie M6 (each pass preserves semantics) and M7 (each pass is
gas-non-increasing) into the property a verified optimizer needs end to end:
**it preserves whole-function execution exactly and never increases static gas.**
-/

/-- The optimizer: constant folding → algebraic simplification → nop removal →
dead-code truncation, all as `Function.mapBlocks` passes. -/
def optimizeFn : Function → Function :=
  truncFn ∘ removeNopsFn ∘ simplifyFn ∘ foldPureFn

/-- **Semantics preservation, end to end.** Running the optimized function equals
running the original, for any fuel and start state — each pass preserves
`Function.exec` exactly, so the composition does too. -/
theorem exec_optimizeFn (fn : Function) (fuel : Nat) (s : VenomState) :
    (optimizeFn fn).exec fuel s = fn.exec fuel s := by
  unfold optimizeFn Function.comp
  rw [exec_truncFn, exec_removeNopsFn, exec_simplifyFn, exec_foldPureFn]

/-- **Gas non-increasing, end to end.** The optimized function's static gas never
exceeds the original's — each pass is gas-non-increasing, chained by transitivity. -/
theorem progGas_optimizeFn_le (fn : Function) : progGas (optimizeFn fn) ≤ progGas fn := by
  unfold optimizeFn Function.comp
  exact le_trans (progGas_truncFn_le _)
    (le_trans (progGas_removeNopsFn_le _)
      (le_trans (progGas_simplifyFn_le _) (progGas_foldPureFn_le _)))

/-- **The verified-optimizer capstone**: for every function, the optimizer both
preserves execution and does not increase gas — the two properties together. -/
theorem optimizeFn_correct_and_gas (fn : Function) :
    (∀ (fuel : Nat) (s : VenomState), (optimizeFn fn).exec fuel s = fn.exec fuel s)
      ∧ progGas (optimizeFn fn) ≤ progGas fn :=
  ⟨exec_optimizeFn fn, progGas_optimizeFn_le fn⟩

end EvmYul.Venom

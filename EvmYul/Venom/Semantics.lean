import EvmYul.Venom.State
import EvmYul.FFI.ffi

/-!
# Venom IR — execution semantics

A small-step-per-instruction, fuel-bounded interpreter for the Venom IR.

* `Operand.evalEnv` resolves an operand to a value against the SSA
  environment (a label, used as a value, reads as `0`).
* `evalPure` gives the arithmetic / bitwise / comparison opcodes as
  total functions of their operand values, reusing the `UInt256`
  operations. Operand order follows the EVM opcode argument order the
  Venom opcode is named after (e.g. `shl shift, value` = `value <<<
  shift`); this is documented per-op below.
* `execInstr` steps one instruction, returning the new state and a
  `Control` describing the effect on control flow (`fallthrough` for
  ordinary ops, a jump/branch for CFG ops, `halt` for terminators).
* `execBlock` runs a basic block to its terminator; `run` walks the CFG
  block-to-block until it halts, gets stuck, or runs out of fuel,
  threading `prevBlock` so `phi` nodes resolve.

Opcodes outside the modelled set (`call`, `create`, `log`,
`calldataload`, …) appear as `Op.unsupported` and step to a `stuck`
state, so any parsed program is representable and has defined behaviour.
-/

namespace EvmYul.Venom

open EvmYul (fromByteArrayBigEndian)

/-- Resolve an operand to a 256-bit value. A label has no numeric value,
so it reads as `0` (labels only matter as jump targets, handled
structurally in `execInstr`). -/
def Operand.evalEnv (env : VarName → UInt256) : Operand → UInt256
  | .lit n   => n
  | .var x   => env x
  | .label _ => UInt256.ofNat 0

/-! ## Pure opcode evaluation -/

def evalUn (f : UInt256 → UInt256) : List UInt256 → Option UInt256
  | [a] => some (f a)
  | _   => none

def evalBin (f : UInt256 → UInt256 → UInt256) : List UInt256 → Option UInt256
  | [a, b] => some (f a b)
  | _      => none

def evalTern (f : UInt256 → UInt256 → UInt256 → UInt256) : List UInt256 → Option UInt256
  | [a, b, c] => some (f a b c)
  | _         => none

/-- The pure (state-free) opcodes as functions of their evaluated
operands. Returns `none` for non-pure opcodes or an arity mismatch.

Shift opcodes take EVM's `(shift, value)` order; `UInt256.shiftLeft`
takes `(value, shift)`, hence the swap. `sar` already matches. -/
def evalPure : Op → List UInt256 → Option UInt256
  | .add,        vs => evalBin UInt256.add vs
  | .sub,        vs => evalBin UInt256.sub vs
  | .mul,        vs => evalBin UInt256.mul vs
  | .div,        vs => evalBin UInt256.div vs
  | .sdiv,       vs => evalBin UInt256.sdiv vs
  | .mod,        vs => evalBin UInt256.mod vs
  | .smod,       vs => evalBin UInt256.smod vs
  | .exp,        vs => evalBin UInt256.exp vs
  | .signextend, vs => evalBin UInt256.signextend vs
  | .lt,         vs => evalBin UInt256.lt vs
  | .gt,         vs => evalBin UInt256.gt vs
  | .slt,        vs => evalBin UInt256.slt vs
  | .sgt,        vs => evalBin UInt256.sgt vs
  | .eq,         vs => evalBin UInt256.eq vs
  | .iszero,     vs => evalUn  UInt256.isZero vs
  | .and,        vs => evalBin UInt256.land vs
  | .or,         vs => evalBin UInt256.lor vs
  | .xor,        vs => evalBin UInt256.xor vs
  | .not,        vs => evalUn  UInt256.lnot vs
  | .shl,        vs => evalBin (fun shift value => UInt256.shiftLeft value shift) vs
  | .shr,        vs => evalBin (fun shift value => UInt256.shiftRight value shift) vs
  | .sar,        vs => evalBin UInt256.sar vs
  | .byte,       vs => evalBin UInt256.byteAt vs
  | .addmod,     vs => evalTern UInt256.addMod vs
  | .mulmod,     vs => evalTern UInt256.mulMod vs
  | _,           _  => none

/-! ## State-dependent helpers -/

/-- `keccak256 offset, size` over the byte memory (FFI; opaque). -/
def keccak (s : VenomState) (offset size : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      (ffi.KEC (s.memory.readBytes offset.toNat size.toNat).toByteArray))

/-- Resolve a `phi` against the predecessor block label. Operands
alternate `label, value, …`; pick the value paired with `prev`. -/
def resolvePhi (prev : Label) (env : VarName → UInt256) : List Operand → Option UInt256
  | .label l :: v :: rest =>
      if l == prev then some (Operand.evalEnv env v) else resolvePhi prev env rest
  | _ => none

/-! ## Control-flow effect of one instruction -/

/-- The effect an instruction has on control flow. -/
inductive Control where
  /-- Continue to the next instruction in the block. -/
  | fallthrough
  /-- Unconditional jump to a label (`jmp`). -/
  | jump (l : Label)
  /-- Conditional branch (`jnz cond, @t, @f`): go to `t` if `cond ≠ 0`. -/
  | branch (cond : UInt256) (t f : Label)
  /-- Dynamic jump (`djmp dest, @l₀, @l₁, …`): pick candidate `dest`. -/
  | djmp (dest : UInt256) (targets : List Label)
  /-- Halt the whole execution. -/
  | halt (h : Halt)
  /-- Malformed / unsupported instruction. -/
  | stuck
deriving Inhabited

/-- Step a single instruction. -/
def execInstr (s : VenomState) (i : Instruction) : VenomState × Control :=
  let vals := i.operands.map (Operand.evalEnv s.env)
  match i.opcode with
  -- hashing
  | .keccak256 =>
      match vals with
      | [o, sz] => (s.setOutput i.output (keccak s o sz), .fallthrough)
      | _ => (s, .stuck)
  -- memory
  | .mload =>
      match vals with
      | [a] => (s.setOutput i.output (s.mload a), .fallthrough)
      | _ => (s, .stuck)
  | .mstore =>
      match vals with
      | [a, v] => (s.mstore a v, .fallthrough)
      | _ => (s, .stuck)
  | .mstore8 =>
      match vals with
      | [a, v] => (s.mstore8 a v, .fallthrough)
      | _ => (s, .stuck)
  | .msize => (s.setOutput i.output s.msize, .fallthrough)
  | .mcopy =>
      match vals with
      | [dst, src, len] =>
          let bytes := s.memory.readBytes src.toNat len.toNat
          ({ s with memory := s.memory.writeBytes dst.toNat bytes }, .fallthrough)
      | _ => (s, .stuck)
  -- storage
  | .sload =>
      match vals with
      | [k] => (s.setOutput i.output (s.sload k), .fallthrough)
      | _ => (s, .stuck)
  | .sstore =>
      match vals with
      | [k, v] => (s.sstore k v, .fallthrough)
      | _ => (s, .stuck)
  | .tload =>
      match vals with
      | [k] => (s.setOutput i.output (s.tload k), .fallthrough)
      | _ => (s, .stuck)
  | .tstore =>
      match vals with
      | [k, v] => (s.tstore k v, .fallthrough)
      | _ => (s, .stuck)
  -- call environment / calldata
  | .calldataload =>
      match vals with
      | [o] => (s.setOutput i.output (s.calldataload o), .fallthrough)
      | _ => (s, .stuck)
  | .calldatasize => (s.setOutput i.output s.calldatasize, .fallthrough)
  | .calldatacopy =>
      match vals with
      | [dst, o, len] => (s.calldatacopy dst o len, .fallthrough)
      | _ => (s, .stuck)
  | .callvalue => (s.setOutput i.output s.callvalue, .fallthrough)
  | .caller => (s.setOutput i.output s.caller, .fallthrough)
  | .«address» => (s.setOutput i.output s.selfAddr, .fallthrough)
  | .«assert» =>
      -- Vyper `assert cond` reverts (panic) when `cond` is zero.
      match vals with
      | [c] => if c == UInt256.ofNat 0 then (s, .halt (.revert [])) else (s, .fallthrough)
      | _ => (s, .stuck)
  | .log =>
      -- Events have no storage/return effect; modelled as a no-op (the
      -- emitted log data is not part of the differential we check).
      (s, .fallthrough)
  -- SSA / pseudo
  | .assign =>
      match vals with
      | [v] => (s.setOutput i.output v, .fallthrough)
      | _ => (s, .stuck)
  | .phi =>
      match resolvePhi s.prevBlock s.env i.operands with
      | some v => (s.setOutput i.output v, .fallthrough)
      | none => (s, .stuck)
  | .param => (s.setOutput i.output (UInt256.ofNat 0), .fallthrough)
  | .nop => (s, .fallthrough)
  -- control-flow terminators
  | .jmp =>
      match i.operands with
      | [.label l] => (s, .jump l)
      | _ => (s, .stuck)
  | .jnz =>
      match i.operands with
      | [c, .label t, .label f] => (s, .branch (Operand.evalEnv s.env c) t f)
      | _ => (s, .stuck)
  | .djmp =>
      match i.operands with
      | d :: rest => (s, .djmp (Operand.evalEnv s.env d) (rest.filterMap Operand.asLabel?))
      | _ => (s, .stuck)
  -- halting terminators
  | .ret => (s, .halt .stop)            -- internal-function return (invoke not modelled)
  | .«return» =>
      match vals with
      | [o, sz] => (s, .halt (.ret (s.memory.readBytes o.toNat sz.toNat)))
      | _ => (s, .stuck)
  | .revert =>
      match vals with
      | [o, sz] => (s, .halt (.revert (s.memory.readBytes o.toNat sz.toNat)))
      | _ => (s, .stuck)
  | .stop => (s, .halt .stop)
  | .invalid => (s, .halt .invalid)
  | .selfdestruct => (s, .halt .selfdestruct)
  | .unsupported _ => (s, .stuck)
  -- everything else is a pure opcode
  | op =>
      match evalPure op vals with
      | some v => (s.setOutput i.output v, .fallthrough)
      | none => (s, .stuck)

/-- Run a basic block's instructions until one yields a non-`fallthrough`
control effect. Running off the end (no terminator) yields `fallthrough`,
which `run` treats as `stuck`. -/
def execBlock : VenomState → List Instruction → VenomState × Control
  | s, [] => (s, .fallthrough)
  | s, i :: rest =>
      match execInstr s i with
      | (s', .fallthrough) => execBlock s' rest
      | (s', c) => (s', c)

/-! ## Whole-function execution -/

/-- Outcome of running a Venom function. -/
inductive Result where
  | halted (s : VenomState) (h : Halt)
  | stuck (s : VenomState)
  | outOfFuel (s : VenomState)
deriving Inhabited

/-- Walk the CFG from block `lbl`, fuel-bounded, threading `prevBlock`
for `phi` resolution. -/
def run (fn : Function) : Nat → Label → VenomState → Result
  | 0, _, s => .outOfFuel s
  | fuel + 1, lbl, s =>
      match fn.find? lbl with
      | none => .stuck s
      | some bb =>
          match execBlock s bb.instrs with
          | (s', .halt h) => .halted s' h
          | (s', .jump l) => run fn fuel l { s' with prevBlock := lbl }
          | (s', .branch c t f) =>
              run fn fuel (if c == UInt256.ofNat 0 then f else t) { s' with prevBlock := lbl }
          | (s', .djmp d tgts) =>
              match tgts[d.toNat]? with
              | some l => run fn fuel l { s' with prevBlock := lbl }
              | none => .stuck s'
          | (s', _) => .stuck s'

/-- Run a function from its entry block. -/
def Function.exec (fn : Function) (fuel : Nat) (s : VenomState) : Result :=
  run fn fuel fn.entry s

end EvmYul.Venom

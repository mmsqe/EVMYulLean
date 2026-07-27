import EvmYul.Venom.Instruction
import EvmYul.Venom.Memory

/-!
# Venom IR — execution state

Venom is SSA, so there is no operand stack: instruction results are bound
to named variables. The execution state therefore carries

* `env` — the SSA variable environment (`VarName → UInt256`, default `0`
  for unbound names);
* `memory` — byte memory, the reasoning-friendly `Mem` (`List UInt8`);
* `storage` / `transient` — persistent (`SLOAD`/`SSTORE`) and transient
  (`TLOAD`/`TSTORE`) word storage, as total maps `UInt256 → UInt256`;
* `returndata` — the buffer set by a halting `return`/`revert`;
* `prevBlock` — the label of the block we arrived from, needed to resolve
  `phi` nodes (which select a value per predecessor).

Total functions are used for the maps deliberately: they reduce, need no
`DecidableEq` on a key structure, and keep the model proof-friendly in the
same spirit as `Mem`.
-/

namespace EvmYul.Venom

/-- How a message-call execution finished. -/
inductive Halt where
  | stop
  | ret (data : Mem)
  | revert (data : Mem)
  | invalid
  | selfdestruct
deriving Inhabited, Repr

/-- The Venom machine state. -/
structure VenomState where
  /-- SSA variable environment; unbound variables read as `0`. -/
  env       : VarName → UInt256 := fun _ => UInt256.ofNat 0
  /-- Byte-addressed memory. -/
  memory    : Mem := []
  /-- Persistent storage. -/
  storage   : UInt256 → UInt256 := fun _ => UInt256.ofNat 0
  /-- Transient storage (EIP-1153). -/
  transient : UInt256 → UInt256 := fun _ => UInt256.ofNat 0
  /-- Buffer returned/reverted by a halting terminator. -/
  returndata : Mem := []
  /-- Label of the predecessor block (for `phi` resolution). -/
  prevBlock : Label := ""
  /-- Message-call input data (`calldataload`/`calldatasize`/`calldatacopy`). -/
  calldata : Mem := []
  /-- `callvalue` (wei sent with the call). -/
  callvalue : UInt256 := UInt256.ofNat 0
  /-- `caller` (msg.sender). -/
  caller : UInt256 := UInt256.ofNat 0
  /-- `address` (the executing contract). -/
  selfAddr : UInt256 := UInt256.ofNat 0
  /-- Storage keys written during execution, newest first — for observing
  the resulting state (storage itself is a total function). -/
  touchedKeys : List UInt256 := []
deriving Inhabited

namespace VenomState

/-- Read an SSA variable. -/
def get (s : VenomState) (x : VarName) : UInt256 := s.env x

/-- Bind an SSA variable to a value (functional update). -/
def set (s : VenomState) (x : VarName) (v : UInt256) : VenomState :=
  { s with env := fun y => if y = x then v else s.env y }

/-- Bind the optional output variable of an instruction, if present. -/
def setOutput (s : VenomState) : Option VarName → UInt256 → VenomState
  | none,   _ => s
  | some x, v => s.set x v

/-- Load a word from persistent storage. -/
def sload (s : VenomState) (key : UInt256) : UInt256 := s.storage key

/-- Store a word to persistent storage (logging the key for observability). -/
def sstore (s : VenomState) (key val : UInt256) : VenomState :=
  { s with
    storage := fun k => if k = key then val else s.storage k
    touchedKeys := key :: s.touchedKeys }

/-- Load a word from transient storage. -/
def tload (s : VenomState) (key : UInt256) : UInt256 := s.transient key

/-- Store a word to transient storage. -/
def tstore (s : VenomState) (key val : UInt256) : VenomState :=
  { s with transient := fun k => if k = key then val else s.transient k }

/-- `mload`. -/
def mload (s : VenomState) (addr : UInt256) : UInt256 := s.memory.loadWord addr

/-- `mstore`. -/
def mstore (s : VenomState) (addr val : UInt256) : VenomState :=
  { s with memory := s.memory.storeWord addr val }

/-- `mstore8`. -/
def mstore8 (s : VenomState) (addr val : UInt256) : VenomState :=
  { s with memory := s.memory.storeByte addr val }

/-- `msize`, in bytes (32 × words touched). -/
def msize (s : VenomState) : UInt256 := UInt256.ofNat (32 * s.memory.sizeWords)

/-- `calldataload`: 32 big-endian bytes of calldata at `off` (zero-padded). -/
def calldataload (s : VenomState) (off : UInt256) : UInt256 :=
  Mem.fromBytes32 (s.calldata.readBytes off.toNat 32)

/-- `calldatasize`. -/
def calldatasize (s : VenomState) : UInt256 := UInt256.ofNat s.calldata.length

/-- `calldatacopy`: copy `len` calldata bytes from `off` into memory at `dst`. -/
def calldatacopy (s : VenomState) (dst off len : UInt256) : VenomState :=
  { s with memory := s.memory.writeBytes dst.toNat (s.calldata.readBytes off.toNat len.toNat) }

/-! ## Projection lemmas

`mstore`/`set` touch one field; these let `simp` push field projections
(and `sload`/`get`) through them when reducing an execution. -/

@[simp] theorem mstore_memory (s : VenomState) (a v : UInt256) :
    (s.mstore a v).memory = s.memory.storeWord a v := rfl
@[simp] theorem mstore_env (s : VenomState) (a v : UInt256) : (s.mstore a v).env = s.env := rfl
@[simp] theorem mstore_storage (s : VenomState) (a v : UInt256) :
    (s.mstore a v).storage = s.storage := rfl
@[simp] theorem set_storage (s : VenomState) (x : VarName) (v : UInt256) :
    (s.set x v).storage = s.storage := rfl
@[simp] theorem set_memory (s : VenomState) (x : VarName) (v : UInt256) :
    (s.set x v).memory = s.memory := rfl
@[simp] theorem set_env_self (s : VenomState) (x : VarName) (v : UInt256) :
    (s.set x v).env x = v := by simp [VenomState.set]
@[simp] theorem sstore_env (s : VenomState) (key val : UInt256) :
    (s.sstore key val).env = s.env := rfl
@[simp] theorem sstore_storage (s : VenomState) (key val : UInt256) :
    (s.sstore key val).storage = fun k => if k = key then val else s.storage k := rfl

end VenomState

end EvmYul.Venom

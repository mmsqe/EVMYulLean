import EvmYul.Venom.Semantics
import EvmYul.Venom.VenomMemProps

/-!
# Venom balance-slot keccak preimage — proved, not assumed

The evm-smith `add_venom` ERC-20 equivalence demo
(`EquivalenceVyperVenom.lean`) proves the optimized side (`~addr`) fully,
but takes the *original* side — that the keccak block leaves
`keccak256(slot ++ addr)` on the stack — as a hypothesis (`hOrig`),
because the `ByteArray` memory model in `EvmYul.MachineState` does not
reduce.

Here we discharge that hypothesis in the Venom semantics. The Venom
balance access is

```
mstore 0x00, slot      ; mem[0x00] = slot id
mstore 0x20, addr      ; mem[0x20] = addr
%h = keccak256 0x00, 0x40
```

Using the proved memory lemma `readBytes_storeWord_storeWord` (which rests
on `readBytes_two_writes`), we compute the keccak preimage to be *exactly*
`toBytes32 slot ++ toBytes32 addr`, i.e. `slot ++ addr`. The hash itself
(`ffi.KEC`) stays opaque, exactly as in the demo — but the *preimage* is
now a theorem.
-/

namespace EvmYul.Venom

open EvmYul (fromByteArrayBigEndian)

/-! ## The keccak block as Venom IR -/

/-- The 3-instruction Venom balance-slot keccak block:
`mstore 0x00, slot; mstore 0x20, addr; %out = keccak256 0x00, 0x40`. -/
def venomBalanceKeccakBlock (slotOp addrOp : Operand) (out : VarName) : List Instruction :=
  [ { opcode := .mstore,    operands := [.lit (UInt256.ofNat 0x00), slotOp] }
  , { opcode := .mstore,    operands := [.lit (UInt256.ofNat 0x20), addrOp] }
  , { output := some out, opcode := .keccak256,
      operands := [.lit (UInt256.ofNat 0x00), .lit (UInt256.ofNat 0x40)] } ]

/-- The keccak of a preimage, with `ffi.KEC` opaque (as in the demo). -/
def venomKeccakOf (preimage : Mem) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC preimage.toByteArray))

/-- The value the balance-slot keccak block should leave in `out`:
`keccak256(slot ++ addr)`, with `slot`/`addr` the 32-byte big-endian
encodings of the evaluated operands. -/
def venomBalanceSlotValue (s : VenomState) (slotOp addrOp : Operand) : UInt256 :=
  venomKeccakOf (Mem.toBytes32 (slotOp.evalEnv s.env) ++ Mem.toBytes32 (addrOp.evalEnv s.env))

/-! ## Helper: reading an SSA variable just bound -/

@[simp] theorem VenomState.get_set_self (s : VenomState) (x : VarName) (v : UInt256) :
    (s.set x v).get x = v := by
  simp [VenomState.get, VenomState.set]

/-! ## The keccak hashes exactly `slot ++ addr` -/

/-- After the two staging stores, the `keccak256 0x00, 0x40` reads a
preimage equal to `toBytes32 slot ++ toBytes32 addr`. This is the fact the
demo had to assume. -/
theorem keccak_staged (s : VenomState) (slot addr : UInt256) :
    keccak ((s.mstore (UInt256.ofNat 0x00) slot).mstore (UInt256.ofNat 0x20) addr)
            (UInt256.ofNat 0x00) (UInt256.ofNat 0x40)
      = venomKeccakOf (Mem.toBytes32 slot ++ Mem.toBytes32 addr) := by
  unfold keccak venomKeccakOf
  simp only [VenomState.mstore_memory]
  rw [show (UInt256.ofNat 0x00).toNat = 0 from by decide,
      show (UInt256.ofNat 0x40).toNat = 64 from by decide,
      Mem.readBytes_storeWord_storeWord s.memory slot addr
        (UInt256.ofNat 0x00) (UInt256.ofNat 0x20) (by decide) (by decide)]

/-! ## Block-level characterization (discharges `hOrig`) -/

/-- Running the Venom balance-slot keccak block binds `out` to
`keccak256(slot ++ addr)` — proved outright, no hypothesis. The block
falls through (its last instruction is not a terminator). -/
theorem venomBalanceKeccakBlock_value
    (s : VenomState) (slotOp addrOp : Operand) (out : VarName) :
    (execBlock s (venomBalanceKeccakBlock slotOp addrOp out)).1.get out
      = venomBalanceSlotValue s slotOp addrOp := by
  -- The three instructions reduce definitionally to a single staged-then-hashed state.
  -- (`setOutput (some out)` is definitionally `set out`.)
  show ((s.mstore (UInt256.ofNat 0x00) (slotOp.evalEnv s.env)
          |>.mstore (UInt256.ofNat 0x20) (addrOp.evalEnv s.env)).set out
              (keccak
                (s.mstore (UInt256.ofNat 0x00) (slotOp.evalEnv s.env)
                  |>.mstore (UInt256.ofNat 0x20) (addrOp.evalEnv s.env))
                (UInt256.ofNat 0x00) (UInt256.ofNat 0x40))).get out
        = venomBalanceSlotValue s slotOp addrOp
  rw [VenomState.get_set_self, venomBalanceSlotValue]
  exact keccak_staged s (slotOp.evalEnv s.env) (addrOp.evalEnv s.env)

/-! ## End-to-end equivalence: orig keccak load ≡ opt `NOT` load

We now reconstruct the demo's `venomBalanceLoad_relational_equiv` with the
original-side characterization *proved* rather than hypothesised. Both
sides are full load blocks ending in `SLOAD`; the opt side keeps the
staging `mstore 0x20` (the patch is length-preserving on the keccak tail),
reads the address back, and complements it. -/

/-- A single-instruction helper: `execBlock` over an append whose prefix
falls through continues into the suffix. -/
theorem execBlock_append (b₁ b₂ : List Instruction) (s : VenomState) :
    execBlock s (b₁ ++ b₂)
      = match execBlock s b₁ with
        | (s', .fallthrough) => execBlock s' b₂
        | r => r := by
  induction b₁ generalizing s with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.cons_append, execBlock]
      cases execInstr s i with
      | mk s' c => cases c <;> simp [ih]

/-- Original load block: stage `slot`/`addr`, `keccak256(slot ++ addr)`,
then `SLOAD`. -/
def venomBalanceLoadOrigBlock (slotOp addrOp : Operand) (out : VarName) : List Instruction :=
  venomBalanceKeccakBlock slotOp addrOp "%vslot"
    ++ [ { output := some out, opcode := .sload, operands := [.var "%vslot"] } ]

/-- Optimized load block (the patched, length-preserving shape): keep the
staging `mstore 0x20`, read the address back with `mload 0x20`, `NOT` it,
then `SLOAD`. -/
def venomBalanceLoadOptBlock (addrOp : Operand) (out : VarName) : List Instruction :=
  [ { opcode := .mstore,    operands := [.lit (UInt256.ofNat 0x20), addrOp] }
  , { output := some "%vaddr", opcode := .mload, operands := [.lit (UInt256.ofNat 0x20)] }
  , { output := some "%vslot", opcode := .not, operands := [.var "%vaddr"] }
  , { output := some out, opcode := .sload, operands := [.var "%vslot"] } ]

/-- The orig load block loads `storage[keccak256(slot ++ addr)]`. -/
theorem venomBalanceLoadOrigBlock_value
    (s : VenomState) (slotOp addrOp : Operand) (out : VarName) :
    (execBlock s (venomBalanceLoadOrigBlock slotOp addrOp out)).1.get out
      = s.sload (venomBalanceSlotValue s slotOp addrOp) := by
  rw [venomBalanceLoadOrigBlock, execBlock_append]
  simp only [venomBalanceKeccakBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv]
  rw [keccak_staged]
  simp [VenomState.get, VenomState.sload, VenomState.setOutput,
    VenomState.set_env_self, venomBalanceSlotValue, venomKeccakOf, Operand.evalEnv]

/-- The opt load block loads `storage[~addr]`, with `addr` read back from
the staging slot — this is where the codec round-trip
(`loadWord_storeWord_self`) is used. -/
theorem venomBalanceLoadOptBlock_value
    (s : VenomState) (addrOp : Operand) (out : VarName) :
    (execBlock s (venomBalanceLoadOptBlock addrOp out)).1.get out
      = s.sload (UInt256.lnot (addrOp.evalEnv s.env)) := by
  simp only [venomBalanceLoadOptBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalUn, VenomState.setOutput, VenomState.mload, VenomState.get,
    VenomState.sload, VenomState.set_env_self, VenomState.set_storage, VenomState.mstore_storage,
    VenomState.mstore_memory]
  rw [Mem.loadWord_storeWord_self]

/-- Storage relation between an original and an optimized state: the
balance held at orig's `keccak256(slot ++ addr)` slot equals the balance
held at opt's `~addr` slot. -/
def VenomBalEquivRel (σo σp : VenomState) (slotOp addrOp : Operand) : Prop :=
  σo.sload (venomBalanceSlotValue σo slotOp addrOp)
    = σp.sload (UInt256.lnot (addrOp.evalEnv σp.env))

/-- **End-to-end equivalence.** Under the per-address storage relation, the
original keccak load block and the optimized `NOT` load block load the same
value into `out`. Unlike the demo's `venomBalanceLoad_relational_equiv`,
the original-side characterization is *proved* (`venomBalanceLoadOrigBlock_value`,
ultimately `keccak_staged`), not taken as a hypothesis. -/
theorem venomBalanceLoad_orig_opt_equiv
    (s_orig s_opt : VenomState) (slotOp addrOp : Operand) (out : VarName)
    (hRel : VenomBalEquivRel s_orig s_opt slotOp addrOp) :
    (execBlock s_orig (venomBalanceLoadOrigBlock slotOp addrOp out)).1.get out
      = (execBlock s_opt (venomBalanceLoadOptBlock addrOp out)).1.get out := by
  rw [venomBalanceLoadOrigBlock_value, venomBalanceLoadOptBlock_value]
  exact hRel

end EvmYul.Venom

import EvmYul.Venom.AsmTop
import EvmYul.Venom.Backend

/-!
# M5 ↔ M2 — the assembler meets the backend's `Sim` semantics

`Backend.lean` certifies single-op lowering against the `Sim` relation, but its
`sim_*` lemmas step on a *symbolic* instruction `(op, arg)` handed to `EVM.step`.
`AsmTop.lean` produces real bytecode and proves `assemble_decodes`: the bytes at
item `i`'s program counter decode (via the real `EVM.decode`) to that item's
instruction. This file ties the two ends together — the instruction the backend
lowers to is *exactly* what the assembled bytecode decodes to:

* `decode_assemble_op` / `decode_assemble_label` — an `op`/`label` item, fetched
  and decoded from `assemble prog`, is `(op, none)` / `(JUMPDEST, none)`;
* `sim_add_assembled` / `sim_sstore_assembled` / `sim_jumpdest_assembled` —
  stepping the real assembled bytecode's instruction (arithmetic / storage /
  control-flow landing) preserves `Sim`, by composing the decode with the
  corresponding `Backend.sim_*` lemma.

So a backend-certified lowering step now runs over genuine `EVM.decode`d
bytecode, not just a hand-supplied opcode.
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation EvmYul.Venom.Backend

/-- An `op` item, fetched and decoded from the real assembled bytecode, is exactly
the `(opcode, none)` the Backend's lowering lemmas step on. -/
theorem decode_assemble_op (prog : List Item) (i : Nat) (o : Operation .EVM)
    (hi : i < prog.length) (hop : (prog[i]'hi) = .op o) (hwo : argOnNBytesOfInstr o = 0)
    (hpc : itemPC prog i + 33 < 2 ^ 64) :
    decode (assemble prog) (UInt256.ofNat (itemPC prog i)) = some (o, none) := by
  rw [assemble_decodes prog i hi (by rw [hop]; exact hwo) hpc, hop]
  rfl

/-- **Backend ↔ M5 (arithmetic).** Stepping the *real assembled bytecode*'s `ADD`
instruction — decoded from the bytes at its program counter — preserves the
backend `Sim` relation. Composes M5's `decode (assemble …)` with `Backend.sim_add`. -/
theorem sim_add_assembled (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (prog : List Item) (i : Nat) (hi : i < prog.length)
    (hc : c ∉ a :: b :: L) (hop : (prog[i]'hi) = .op .ADD)
    (hpc : itemPC prog i + 33 < 2 ^ 64)
    (hstep : EVM.step (f + 1) cost (decode (assemble prog) (UInt256.ofNat (itemPC prog i))) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.add (vs.env a) (vs.env b))) es' (c :: L) := by
  rw [decode_assemble_op prog i .ADD hi hop rfl hpc] at hstep
  exact sim_add vs es es' L c a b f cost none hc hstep hsim

/-- **Backend ↔ M5 (storage).** Stepping the real assembled bytecode's `SSTORE`
preserves `Sim` — the storage mutation in a verified `transfer`, now over genuine
bytecode. Composes with `Backend.sim_sstore`. -/
theorem sim_sstore_assembled (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (k v : VarName) (f cost : ℕ) (acc : Account .EVM) (prog : List Item) (i : Nat)
    (hi : i < prog.length) (hop : (prog[i]'hi) = .op .SSTORE)
    (hpc : itemPC prog i + 33 < 2 ^ 64)
    (hFind : es.accountMap.find? es.executionEnv.codeOwner = some acc)
    (hval : (vs.env v == default) = false)
    (hstep : EVM.step (f + 1) cost (decode (assemble prog) (UInt256.ofNat (itemPC prog i))) es = .ok es')
    (hsim : Sim vs es (k :: v :: L)) :
    Sim (vs.sstore (vs.env k) (vs.env v)) es' L := by
  rw [decode_assemble_op prog i .SSTORE hi hop rfl hpc] at hstep
  exact sim_sstore vs es es' L k v f cost none acc hFind hval hstep hsim

/-- A `label` item, fetched from the assembled bytecode, decodes to `JUMPDEST`. -/
theorem decode_assemble_label (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hlab : (prog[i]'hi) = .label l) (hpc : itemPC prog i + 33 < 2 ^ 64) :
    decode (assemble prog) (UInt256.ofNat (itemPC prog i)) = some (.JUMPDEST, none) := by
  rw [assemble_decodes prog i hi (by rw [hlab]; trivial) hpc, hlab]; rfl

/-- **Backend ↔ M5 (control flow).** Landing on the assembled bytecode's
`JUMPDEST` (a `.label` site) preserves `Sim` — the jump-target landing of a
verified CFG edge, over genuine bytecode. Composes with `Backend.sim_jumpdest`. -/
theorem sim_jumpdest_assembled (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (f cost : ℕ) (l : Label) (prog : List Item) (i : Nat) (hi : i < prog.length)
    (hlab : (prog[i]'hi) = .label l) (hpc : itemPC prog i + 33 < 2 ^ 64)
    (hstep : EVM.step (f + 1) cost (decode (assemble prog) (UInt256.ofNat (itemPC prog i))) es = .ok es')
    (hsim : Sim vs es L) :
    Sim vs es' L := by
  rw [decode_assemble_label prog i l hi hlab hpc] at hstep
  exact sim_jumpdest vs es es' L f cost none hstep hsim

end EvmYul.Venom.Asm

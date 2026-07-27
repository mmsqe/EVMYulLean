import EvmYul.Venom.AsmTop

/-!
# M5 non-vacuity — a concrete 4-way dense dispatch table, assembled and sound

The whole point of M5 is to handle the case the `venom_run` oracle cannot: a
dispatch with ≥4 selectors, where Vyper emits a dense jump table whose target
offsets are fixed only at assembly time. Here we *concretely* assemble such a
table and discharge the `assemble_dispatch_sound` capstone for every entry — so
the headline claim is not vacuous.

Each `dispatch4_entryK_sound` says: the assembled bytecode, decoded at dispatch
entry `K`'s program counter, pushes (`PUSH32`) a value that is a *valid jump
destination* in the same program. All hypotheses discharge by `decide` (pure
list / arithmetic computation — no `ByteArray` reduction).
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation

/-- A concrete 4-way dense dispatch table: push each handler's (resolved) address,
`JUMP`, then four `JUMPDEST` handler blocks. Exactly the ≥4-selector shape the
oracle cannot execute. -/
def dispatch4 : List Item :=
  [ .pushLabel "h0", .pushLabel "h1", .pushLabel "h2", .pushLabel "h3", .op .JUMP,
    .label "h0", .op .STOP, .label "h1", .op .STOP,
    .label "h2", .op .STOP, .label "h3", .op .STOP ]

/-- The dispatch table is well formed (every item assembles). -/
theorem dispatch4_wf : ∀ a ∈ dispatch4, a.WF := by decide

/-- Dispatch entry 0 pushes a valid jump destination. -/
theorem dispatch4_entry0_sound :
    ∃ v, decode (assemble dispatch4) (UInt256.ofNat (itemPC dispatch4 0))
           = some (.Push .PUSH32, some (v, 32)) ∧
         v.toNat ∈ djScan (emit (labelMap dispatch4) dispatch4) dispatch4.length 0 [] :=
  assemble_dispatch_sound dispatch4 0 "h0"
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) dispatch4.length (by decide)

/-- Dispatch entry 1 pushes a valid jump destination. -/
theorem dispatch4_entry1_sound :
    ∃ v, decode (assemble dispatch4) (UInt256.ofNat (itemPC dispatch4 1))
           = some (.Push .PUSH32, some (v, 32)) ∧
         v.toNat ∈ djScan (emit (labelMap dispatch4) dispatch4) dispatch4.length 0 [] :=
  assemble_dispatch_sound dispatch4 1 "h1"
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) dispatch4.length (by decide)

/-- Dispatch entry 2 pushes a valid jump destination. -/
theorem dispatch4_entry2_sound :
    ∃ v, decode (assemble dispatch4) (UInt256.ofNat (itemPC dispatch4 2))
           = some (.Push .PUSH32, some (v, 32)) ∧
         v.toNat ∈ djScan (emit (labelMap dispatch4) dispatch4) dispatch4.length 0 [] :=
  assemble_dispatch_sound dispatch4 2 "h2"
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) dispatch4.length (by decide)

/-- Dispatch entry 3 pushes a valid jump destination. -/
theorem dispatch4_entry3_sound :
    ∃ v, decode (assemble dispatch4) (UInt256.ofNat (itemPC dispatch4 3))
           = some (.Push .PUSH32, some (v, 32)) ∧
         v.toNat ∈ djScan (emit (labelMap dispatch4) dispatch4) dispatch4.length 0 [] :=
  assemble_dispatch_sound dispatch4 3 "h3"
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) dispatch4.length (by decide)

end EvmYul.Venom.Asm

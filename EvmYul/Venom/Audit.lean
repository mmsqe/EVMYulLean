import EvmYul.Venom

/-!
# Trust-boundary audit: the Venom development's axioms and hypotheses

This file is the canonical, **machine-checked** list of what every headline
result rests on. It is not imported by the library (so it does not spam normal
builds); run it directly:

```
lake env lean EvmYul/Venom/Audit.lean        # prints the axioms of each result
scripts/axiom_audit.sh                        # + asserts no sorry / no surprise axiom
```

Reading the output:

* **`[propext, Classical.choice, Quot.sound]`** — Lean's standard axioms. A result
  printing exactly these is fully rigorous; anything it is *contingent* on is then
  a **hypothesis in its signature** (a `Prop` argument), not an axiom — noted per
  result below.
* **`+ EvmYul.M1.ffi_zeroes_{size,get}`** — the *only* extra axioms, isolated to
  the M1 memory model (the `memset_zero` FFI characterisation). They appear in
  exactly the M1 results and nothing else.

## Hypotheses (interfaces) the contingent results carry — NOT axioms

| interface (`Prop`) | where | what it captures |
|---|---|---|
| `VenomBalEquivRel` | BalanceSlot | orig/opt storages realise the same balance map |
| `Realizes σ B f` | SlotAbstraction | storage `σ` realises abstract map `B` under slot fn `f` |
| `EvmStorageRel` | EvmBytecodeEquiv | the two EVM slots hold equal values (residual of the bytecode lift) |
| `RBMapEraseSpec` | Backend | the two `find?`-after-`erase` facts Batteries lacks (SSTORE zero-write) |
| `Solvent B ts S` | Solvency | `Σ balances = totalSupply` over a finite slot set |
| `DJAuxSpec` | AsmDJ | `EVM.D_J_aux`'s defining recurrence (it is a `partial def`, kernel-opaque) |

The `MemBridge` interface (`MachineMemSpec`) is **gone**: both halves —
`load_agrees` (read) and `store_refines` (write) — are now **proved** (resting
only on the M1 `ffi_zeroes_*` axioms, plus the realistic machine-address bound
`a.toNat < USize.size` on the store), so the `Mem` memory laws transfer to the
real `ByteArray` machine with no interface hypothesis.

These are *visible in the theorem signatures*: an auditor sees exactly where each
boundary is, and discharging them (proving the interface, or supplying realising
states) removes the contingency with no change to the proofs.
-/

namespace EvmYul.Venom.Audit
open EvmYul.Venom EvmYul.Venom.Backend EvmYul.M1

/-! ## 1. Orig ≡ opt balance equivalence (the `keccak(slot++addr) → ~addr` peephole) -/

-- Venom-level orig ≡ opt (contingent on `VenomBalEquivRel`: same realised balance map).
#print axioms venomBalanceLoad_orig_opt_equiv
-- The orig slot provably IS keccak(slot ++ addr) in the reducible List model.
#print axioms balanceKeccak_is_slot_keccak
-- EVM-bytecode lift: SLOAD equivalence on real EVM.step (residual: `EvmStorageRel`).
#print axioms evm_sload_equiv
#print axioms evm_balanceLoad_block_equiv
-- The residual relation derived from abstract realisation (`Realizes`), not assumed.
#print axioms evm_sload_equiv_of_realizes

/-! ## 2. No-aliasing, solvency, conservation -/

#print axioms distinct_addresses_distinct_opt_slots
#print axioms balSumZ_transfer
#print axioms transfer_preserves_solvent

/-! ## 3. Backend lowering (single-block ops, scheduling, control flow) -/

#print axioms sim_sstore                 -- storage write, rigorous (insert branch)
#print axioms sim_jump
#print axioms sim_jumpi
#print axioms reorder_rot3               -- reorder soundness (a 3-cycle)
#print axioms reorder_rot4               -- reorder soundness (a 4-cycle, toward completeness)
#print axioms perm_reaches               -- reorder COMPLETENESS (axiom-free): SWAPk reach any perm
#print axioms step_SWAP16_shape          -- M3: deepest EVM swap shape (SWAP4..16 via the macro)
#print axioms sim_swap_via_shape         -- M3: any StarSwap (0,k) is realized on the EVM under Sim
#print axioms sim_swap4                  -- M3: worked deep SWAP4 realization
#print axioms sim_reload                 -- M4: reload a spilled value into the Sim
#print axioms sim_spill                  -- M4: spill a value, establishing the spill invariant
#print axioms sim_spill_reload           -- M4: the full spill/reload round-trip (capstone)
#print axioms step_MSTORE_shape_active   -- M4: MSTORE expands activeWords = M(old, slot, 32)
#print axioms mstore_slot_active         -- M4: the slot-active guard discharged from mstore's expansion
#print axioms sim_spill_active           -- M4: sim_spill with the slot-active guard auto-discharged
#print axioms MemBridge.machineStore_size_ge -- M4: MSTORE grows memory to cover its slot (size ≥ a+32)
#print axioms sim_spill_full             -- M4: sim_spill with the WHOLE zero-guard discharged

/-! ## 4. Storage combinators and the full transfer -/

#print axioms lowered_rmw
#print axioms lowered_debit
#print axioms lowered_credit
#print axioms lowered_transfer
#print axioms guarded_debit              -- require + debit (8 real EVM.step instrs)

/-! ## 5. Conservation/solvency bridge (transfer keeps Σ balances constant) -/

#print axioms lowered_transfer_conserves
#print axioms lowered_transfer_preserves_solvent
#print axioms lowered_opt_transfer_conserves   -- + no-aliasing discharges slot-distinctness

/-! ## 5b. Complete ERC-20: the allowance layer (approve / transferFrom)

The balance half (transfer / mint / Solvent) is sections 2 & 5; these add the
allowance half and the bundled `Token`. `transferFrom`'s balance effect *is* the
verified `transfer` (`doTransferFrom_bal`), so conservation/solvency are inherited
— no re-proof. Fully rigorous (standard axioms only). -/

#print axioms Token.doApprove_allowance        -- approve sets the allowance exactly
#print axioms Token.doApprove_frame            -- approve touches no other (owner, spender) pair
#print axioms Token.doApprove_solvent          -- approve moves no balance ⇒ solvency preserved
#print axioms Token.doTransfer_isSome_iff      -- transfer precondition: afford + no overflow
#print axioms Token.doTransfer_solvent         -- transfer preserves Σ balances = supply
#print axioms Token.doTransferFrom_isSome_iff  -- transferFrom needs balance AND allowance
#print axioms Token.doTransferFrom_consumes    -- the spender's allowance is debited by amt
#print axioms Token.doTransferFrom_bal         -- transferFrom's balance effect IS `transfer`
#print axioms Token.doTransferFrom_solvent     -- transferFrom preserves solvency (via the above)

/-! ## 6. Contingent on the `RBMapEraseSpec` interface (NOT an axiom — a hypothesis) -/

#print axioms sim_sstore_zero
#print axioms step_SSTORE_shape_strong_zero

/-! ## 7. M1 — the ONLY results carrying the FFI axioms `ffi_zeroes_{size,get}` -/

#print axioms usize_ofNat_toNat          -- pure: [propext] only
#print axioms zeroes_size_nat            -- + ffi_zeroes_size
#print axioms zeroes_get_zero            -- + ffi_zeroes_get

/-! ## 8. Non-vacuity — the relation/lemmas instantiated on real `EVM.step` runs
(`rfl` runs the kernel, so these carry no extra axiom — not `native_decide`).
The single-op lowerings — arithmetic/comparison, scheduling, control-flow
landing, and storage read + write — are each instantiated end to end. -/

#print axioms NonVacuity.sim_satisfiable
#print axioms NonVacuity.not_instantiated
#print axioms NonVacuity.add_instantiated         -- arithmetic
#print axioms NonVacuity.sub_instantiated
#print axioms NonVacuity.lt_instantiated          -- comparison
#print axioms NonVacuity.eq_instantiated
#print axioms NonVacuity.iszero_instantiated
#print axioms NonVacuity.dup1_instantiated        -- scheduling
#print axioms NonVacuity.dup2_instantiated
#print axioms NonVacuity.swap1_instantiated
#print axioms NonVacuity.pop_instantiated
#print axioms NonVacuity.jumpdest_instantiated    -- control-flow landing
#print axioms NonVacuity.sload_instantiated       -- storage read
#print axioms NonVacuity.sstore_instantiated      -- storage write (the transfer mutation)

/-! ## 9. Memory invariant layer (the `Mem`-model byte-function abstraction) -/

#print axioms Mem.writeBytes_getByte       -- a write changes exactly its window
#print axioms Mem.readBytes_getByte
#print axioms Mem.loadWord_storeWord_self'  -- read-after-write (via getByte)
#print axioms Mem.readBytes_writeBytes_disjoint  -- frame / no-aliasing (byte level)
#print axioms Mem.loadWord_storeWord_disjoint    -- no-aliasing (word level)
#print axioms Mem.spill_reload_frame             -- M4: a spill survives a disjoint write
#print axioms Mem.spill_survives_writes          -- M4: a spill survives the whole live range
#print axioms Mem.spillSlot_disjoint             -- M4: allocator keeps distinct slots disjoint

/-! ## 10. ByteArray bridge — Mem laws transferred to the machine, FULLY (no
interface hypothesis). The `ByteArray.toList` keystone and the encoding bridge
(`UInt256.toByteArray` ↔ `Mem.toBytes32`) are proved outright; both the read
(`load_agrees`) and write (`store_refines`) halves are proved, so the machine
read-after-write / no-aliasing carry only the M1 `ffi_zeroes_*` axioms (plus the
machine-address bound on the store). -/

#print axioms MemBridge.refines_empty                  -- base case, proved
#print axioms MemBridge.toList_eq_data                 -- `ByteArray.toList` keystone ([propext])
#print axioms MemBridge.toByteArray_toList_eq_toBytes32 -- encoding bridge ([propext]+M1)
#print axioms MemBridge.readWithPadding_toList         -- machine read realizes `Mem.readBytes`
#print axioms MemBridge.load_agrees_discharged          -- read half, PROVED (was a hypothesis)
#print axioms MemBridge.store_refines_discharged        -- write half, PROVED (was a hypothesis)
#print axioms MemBridge.machine_load_store_self         -- read-after-write on the machine
#print axioms MemBridge.machine_load_store_disjoint     -- no-aliasing on the machine
#print axioms MemBridge.lookupMemory_writeWord_self     -- M4: real EVM MSTORE/MLOAD round-trips

/-! ## 11. Interpreter-level memory laws (the Mem laws on the actual execInstr the
oracle differential-tests). -/

#print axioms execInstr_mstore_mload        -- read-after-write on execInstr
#print axioms execInstr_mstore_mload_frame  -- no-aliasing on execInstr
#print axioms execInstr_mcopy               -- mcopy correctness on execInstr
#print axioms execInstr_mstore8             -- byte store on execInstr

/-! ## 12. M5 — the verified `.venom` → bytecode assembler (foundation)
Pure encode/decode round-trips: the trust that assembled bytes mean what the
backend intended. Standard axioms only (no FFI). -/

#print axioms Asm.parseInstr_serializeInstr  -- every opcode byte parses back
#print axioms Asm.Item.encode1_length        -- the encoding realizes its declared width
#print axioms Asm.decodeAtL_op               -- a single op decodes back to itself
#print axioms Asm.decodeAtL_push32           -- a PUSH32 decodes back, immediate intact
#print axioms Asm.decodeAtL_pushLabel        -- a label push decodes to its resolved PC
#print axioms Asm.decodeAtL_label            -- a label site decodes to JUMPDEST
#print axioms Asm.emit_length                -- layout is label-map independent (two-pass soundness)
#print axioms Asm.decodeAtL_prefix           -- decoding at a prefix boundary sees the suffix
#print axioms Asm.decodeAtL_encode1_append   -- items are self-delimiting
#print axioms Asm.decodeAtL_offset           -- FETCH-DECODE correctness: byte at item i's PC is item i
#print axioms Asm.emit_getElem?_label        -- a label site lands on a real JUMPDEST byte
#print axioms Asm.decodeAtL_offset_pushLabel -- dense dispatch: a table push decodes to the resolved PC

/-! ## 13. M5.4 — bridge to the real `ByteArray` decoder `EVM.decode`.
Lifts the list-level results to the bytecode the `EVM.X` driver fetches. -/

#print axioms Asm.get?_toByteArray           -- ByteArray.get? of an assembled list is list indexing
#print axioms Asm.extract'_toList            -- extract' (fast path) is list slicing
#print axioms Asm.decode_toByteArray         -- DECODE BRIDGE: EVM.decode = decodeAtL on assembled code
#print axioms Asm.decode_emit_offset         -- CAPSTONE: the real decoder fetches the right item at its PC

/-! ## 14. M5.5 — jump-destination alignment (every label is a valid JUMP target).
The byte-scan EVM.D_J runs collects exactly the jump-dest item offsets. -/

#print axioms Asm.djScan_emit                -- the scan collects exactly the jump-dest offsets
#print axioms Asm.offsetOf_mem_djScan        -- a label's PC is a recognized jump destination

/-! ## 15. M5.6 — pass 1: the label resolver (closing the two-pass loop).
The PCs pass 1 computes are valid jump destinations in the self-assembled code. -/

#print axioms Asm.findLabelOffset_mem          -- a resolved offset is a jump-dest offset
#print axioms Asm.labelMap_resolves_to_jumpdest -- pass-1 PC is valid in emit (labelMap prog) prog
#print axioms Asm.dispatch_target_valid_jumpdest -- a dispatch entry pushes a valid jump destination

/-! ## 16. M5 capstone — the top-level `assemble` API.
`assemble : List Item → ByteArray` (pass 1 + pass 2), correct against EVM.decode. -/

#print axioms Asm.assemble_decodes           -- decoding assemble prog at item i's PC yields item i
#print axioms Asm.assemble_dispatch_sound    -- END TO END: a dispatch entry pushes a valid jump dest

/-! ## 17. M5.7 — the general minimal-width PUSH codec (PUSH1..32, not just PUSH32). -/

#print axioms Asm.fromBytes32_beBytesN       -- the k-byte big-endian codec round-trips
#print axioms Asm.decodeAtL_pushN            -- a minimal-width PUSHk decodes back to its immediate

/-! ## 18. M5 non-vacuity — a concrete 4-way dense dispatch table, assembled & sound.
The ≥4-selector case the oracle cannot run, discharged concretely. -/

#print axioms Asm.dispatch4_wf               -- the concrete dispatch table is well formed
#print axioms Asm.dispatch4_entry0_sound     -- entry 0 pushes a valid jump destination
#print axioms Asm.dispatch4_entry3_sound     -- entry 3 pushes a valid jump destination

/-! ## 19. M5.8 — the EVM.D_J correspondence (jumps valid in the real EVM).
Contingent on the `DJAuxSpec` interface (EVM.D_J_aux's recurrence; it is a
`partial def`, opaque to the kernel) — a HYPOTHESIS in the signatures, not an axiom. -/

#print axioms Asm.DJ_aux_eq_djScan           -- partial→total bridge: EVM.D_J_aux = djScan
#print axioms Asm.labelMap_mem_DJ            -- a label's PC ∈ EVM.D_J (assemble prog) 0

/-! ## 20. M5 ↔ M2 — the assembler meets the backend's Sim semantics.
A backend-certified lowering step runs over real EVM.decode'd assembled bytecode. -/

#print axioms Asm.decode_assemble_op         -- an op item decodes (real EVM.decode) to (op, none)
#print axioms Asm.sim_add_assembled          -- assembled ADD preserves Sim (arithmetic)
#print axioms Asm.sim_sstore_assembled       -- assembled SSTORE preserves Sim (storage)
#print axioms Asm.sim_jumpdest_assembled     -- assembled JUMPDEST landing preserves Sim (control flow)

/-! ## 21. M6 — verified Venom→Venom optimization passes (semantics-preserving). -/

#print axioms execBlock_removeNops           -- nop elimination preserves block execution
#print axioms run_removeNopsFn               -- nop elimination preserves whole-function execution
#print axioms exec_removeNopsFn              -- nop elimination preserves Function.exec
#print axioms run_mapBlocks                  -- the generic pass lifter (block→function preservation)
#print axioms execInstr_constFold            -- constant-fold engine (value form: value-producer → assign)
#print axioms execInstr_evalPure             -- constant-fold engine (pure form: pure opcode → its value)
#print axioms run_foldPureFn                 -- constant folding (all pure ops) preserves whole-function run
#print axioms exec_foldPureFn                -- constant folding preserves Function.exec
#print axioms execInstr_terminator           -- a terminator never falls through
#print axioms run_truncFn                    -- dead-code-after-terminator preserves whole-function run
#print axioms exec_truncFn                   -- dead-code elimination preserves Function.exec
#print axioms execInstr_simplifyInstr        -- algebraic identity (add x 0 → x) preserves execInstr
#print axioms run_simplifyFn                 -- algebraic identities preserve whole-function execution
#print axioms exec_simplifyFn                -- algebraic identities preserve Function.exec

/-! ## 22. M7 — gas accounting: every M6 optimization pass is gas-non-increasing. -/

#print axioms progGas_removeNopsFn_le        -- nop elimination does not increase gas
#print axioms progGas_foldPureFn_le          -- constant folding does not increase gas
#print axioms progGas_truncFn_le             -- dead-code elimination does not increase gas
#print axioms progGas_simplifyFn_le          -- algebraic identities do not increase gas
#print axioms C'_eq_gas                      -- FAITHFULNESS: Op.gas IS the EVM cost C' (arith ops, any state)
#print axioms instrGas_eq_C'                 -- a foldable instruction's static gas is its real EVM cost
#print axioms C'_exp                         -- state-dependent: exact EXP cost (exponent-dependent)
#print axioms Gexp_le_C'_exp                 -- EXP costs at least its base, any exponent
#print axioms C'_sload                       -- state-dependent: exact SLOAD cost (warm vs cold)
#print axioms foldArith_C'_le                -- folding an arith op reduces REAL EVM gas
#print axioms foldExp_C'_le                  -- folding exp reduces REAL EVM gas (despite state-dependence)

end EvmYul.Venom.Audit

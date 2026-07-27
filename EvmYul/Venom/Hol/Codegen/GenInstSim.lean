import EvmYul.Venom.Hol.Codegen.GenInstSim.GenLayout

/-!
# Per-instruction simulation (stage 4b ④) — re-export shim

Towards `genBlockSimulation`: a single instruction's generated ops, run on the asm interpreter,
advance the pc by their length and preserve `venomAsmRel` across the Venom instruction step.

Split for navigability (was ~18.3k lines); each part imports the previous:

1. `GenInstSim.ComputeAtoms`  — single-op atoms + per-opcode compute steps
2. `GenInstSim.ReorderLayout` — reorder / stack-swap / JMP plan decomposition / label-freeness
3. `GenInstSim.BinopSim`      — gen support + commutative-binop full execution sim
4. `GenInstSim.JoinProducers` — non-comm/ternary sims, join reconciliation, spilled producers
5. `GenInstSim.GenLayout`     — context-push, remaining non-comm, asm structure, both-spilled store

Importing this module (or any consumer's existing `import …GenInstSim`) transitively pulls all parts.
-/

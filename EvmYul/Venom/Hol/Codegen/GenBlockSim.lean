import EvmYul.Venom.Hol.Codegen.GenBlockSim.WalkJoinsLoops

/-!
# Block / function simulation lemmas -- re-export shim

THE key lemmas for `codegen_correct`: a generated block/function plan, run on the asm interpreter,
simulates the Venom execution and preserves `venomAsmRel`. Split for navigability (was ~7k lines);
each part imports the previous:

1. `GenBlockSim.CfgHfsim`         -- CFG composition + hfsim via the CFG-walk engine
2. `GenBlockSim.HstepCanonical`   -- the canonical per-block hstep family + codegen_correct_canonical
3. `GenBlockSim.HstepGenerations` -- the reach / fuel / clean-stack hstep generations
4. `GenBlockSim.WalkJoinsLoops`   -- shallow-stack, join-agreement, per-block-sim to walk, joins, loops

Importing this module (or any consumer's existing `import ...GenBlockSim`) pulls all parts.
-/

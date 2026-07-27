/-
Concrete, non-vacuous instance of the block simulation (de-vacuification milestone)

`genBlockSimulation` is admitted in general (its proof needs the per-instruction sims for *every*
instruction shape — var operands, memory, phis — plus the block-body fold + CFG composition). This
file discharges a *concrete* instance end to end, with no `sorry`, to validate the whole pipeline
on a real block:

    generateBlockPlan  →  executePlan  →  asmResolve  →  runAsm

for the single-block STOP function `entry: STOP`. It exercises exactly the restated-capstone shape
(resolved program + threaded `offsetToPc`, Halt case) and the control-flow-free composition
(`asmResolve` is the identity on the label-push-free body; each `asmStep` reduces on the concrete
instruction, so the `offsetToPc` is irrelevant here). It is the first checked, non-vacuous block
simulation, de-risking the general proof.

# Roadmap

That opening STOP block is only the start: at ~23k lines the file grew from single-block demos to a
*general* recipe that lifts any reachable block. It is now split for readability into six parts
under `GenBlockSimExample/`; this module re-exports them (importing the terminal part chains them
all), so consumers are unaffected. The file's first half is one `…Codegen.Example` namespace of
concrete instances; the second is one `…Codegen` namespace of general machinery, so the later parts
are each wrapped in `namespace …Codegen` and import the previous — layout only, meaning unchanged.
Read them in order:

  1. `GenBlockSimExample/Demos` — the concrete instances: a body-instruction block, cross-block JMP,
     the two-block `hfsim`, multi-block `codegen_correct`, a JNZ conditional, a SELFDESTRUCT
     terminator, the ABI return block, var-reading store / memory-copy bodies, a genuine join
     reorder, schedule-by-evaluation, and the whole-function environment-push capstone.
  2. `GenBlockSimExample/Dispatch` — internal-return, a terminating loop whose header is a phi, and
     the universal-dispatch / retraction / discriminating-witness setup.
  3. `GenBlockSimExample/RecipeEntry` — the discriminating recipe version and the OK-continuing arm
     with a canonical Entry.
  4. `GenBlockSimExample/RecipeWalk` — canonical Entry, the first `hsupply` slices, and the CFG
     assembly (base + general shape).
  5. `GenBlockSimExample/RecipeSlices` — the `hsupply` slice families and the recipe → walk bridges.
  6. `GenBlockSimExample/RecipeFinal` — the retracted recipe capstones and the closing block.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeMemory

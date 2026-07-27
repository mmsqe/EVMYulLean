/-
Block simulation composition — the assembly layer toward `genBlockSimulation`

`genBlockSimulation` runs the resolved block plan `JUMPDEST :: cleanOps ++ instOps` and must match
the Venom `runBlock`. Its proof composes, over the resolved program:

    leading JUMPDEST (soLabel_sim)  →  body fold (per-inst sims via foldl_inst_sim)  →  terminator

Starting from the reusable *sequencing layer* that glues those segments together at the `runAsm`
level (`runAsm_add_ok` continues past a successful prefix; `runAsm_seq_{halt,revert,fault}` attach a
STOP/REVERT/INVALID terminal step), the file builds all the way up to the whole-function CFG walk.
Concrete end-to-end instances live in `GenBlockSimExample`.

# Roadmap

At ~34k lines this was the largest single module in the codegen stack; it is now split for
readability into six phase-files under `GenBlockSimComp/`, cut horizontally along the phase
boundaries. This module re-exports them (importing the terminal part chains them all), so consumers
importing `GenBlockSimComp` are unaffected. Each part continues the one `EvmYul.Venom.Hol.Codegen`
namespace and imports the previous, so the split changes layout, not meaning. Read them in order:

  1. `GenBlockSimComp/StackDiscipline` — body simulation & stack discipline. The De-Option bridge,
     `execBlock` alignment, per-instruction body steps, and the `StackDisc` / spill-aware
     `StackDiscHS` invariants everything downstream threads.
  2. `GenBlockSimComp/BodyAtoms` — body atoms & reorder. Non-commutative / ternary var-op body
     atoms, the invariant-threading body fold, and the `reorderPlan` / `perm_reaches` positioning
     fold.
  3. `GenBlockSimComp/Producers` — body-fold composition & per-opcode producers. The composition kit
     (`BodyStep` → `BodyStepsReady`) and the producers — env pushes, SLOAD, the 0-output stores
     SSTORE/TSTORE/MSTORE(8), the memory copies CALLDATACOPY/EXTCODECOPY.
  4. `GenBlockSimComp/GrowthFolds` — growth-aware folds & terminator. The varying-growth (`HSV`) and
     peak-aware (`HSVP`) spill folds, then the terminator split and per-arm block-sim discharge.
  5. `GenBlockSimComp/RegularBody` — regular body & entry discharge. The fully general regular body,
     the Gap-B well-formedness route, `htermrun`, the entry-block state invariants, and the first
     fully concrete bare-STOP capstone.
  6. multi-block, CFG walk & phi — the largest phase, itself sub-split into three:
       - `GenBlockSimComp/CfgWalkLayout` — param / return prefixes, non-entry block layout, the JNZ
         order theorem, and JMP-chain recording.
       - `GenBlockSimComp/CfgWalkDischarge` — the `hpreuniq`/`hoff`/`hwdec`/`hlblfree` discharges and
         the universal DFS plan decomposition + Entry invariant.
       - `GenBlockSimComp/CfgWalkPhi` — clean-stack prologues, the DJMP switch, fuel sufficiency, the
         phi-join, `instIdx`-obliviousness, and the fresh-label scheme.

(The spill-matrix body-step families this file used to enumerate by hand now live collapsed in
`BodyStepSpill.lean` as `bodyStepHSV_{binop,sstore,ternop}`; the two consumed originals kept here —
both in `GrowthFolds` — are `bodyStepHSV_nonCommBinop_bothlive` and `bodyStepHSV_ternopVar_yspilled`.)
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimComp.CfgWalkPhi

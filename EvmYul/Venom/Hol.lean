/-
# Vendored Venom formalization (`EvmYul.Venom.Hol`)

This is the execution-equivalence + codegen-correctness proof stack ported from
the upstream `venom` branch (a port of the HOL4 `vyper-hol` Venom semantics). It
lives under the `EvmYul.Venom.Hol` namespace so it coexists with `venom_ir`'s own
`EvmYul.Venom.*` formalization without name collisions (both define `VenomState`,
`Operand`, `Instruction`, `Semantics`, …).

Trust boundary note: the vendored stack carries its own `ByteArray` axioms
(`EvmYul.Venom.Hol.CoreAxioms`), isolated here and not affecting the `venom_ir`
proofs. The stack is otherwise `sorry`-free: both codegen-correctness capstones
(`genBlockSimulation`, `genFnSimulation`) are proved (axioms = `[propext,
Classical.choice, Quot.sound]`, no `sorryAx`), the block one via `genBlockSim_match`
(terminator case-split + per-block asm correspondence `hsim`) and the function one
by the `runBlocks` CFG-walk reduction + per-function `hfsim`. The remaining open
work is *supplying* those `hsim`/`hfsim` hypotheses end to end (the per-instruction
var-operand breadth + the inter-block composition) and de-vacuifying `codegen_correct`
(real `generateContextPlan`).
-/

import EvmYul.Venom.Hol.CoreAxioms

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.Exec
import EvmYul.Venom.Hol.SubEvm

import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.StackModel
import EvmYul.Venom.Hol.Codegen.PlanTypes
import EvmYul.Venom.Hol.Codegen.PlanOps
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.Hol.Codegen.AsmSem

import EvmYul.Venom.Hol.StateEquiv
import EvmYul.Venom.Hol.StateEquivProofs
import EvmYul.Venom.Hol.ExecEquivProofs
import EvmYul.Venom.Hol.VenomExecProps
import EvmYul.Venom.Hol.VenomInstProps
import EvmYul.Venom.Hol.VenomMemProps

import EvmYul.Venom.Hol.Codegen.CodegenRel
import EvmYul.Venom.Hol.Codegen.AsmSpillMem
import EvmYul.Venom.Hol.Codegen.SymbolResolve
import EvmYul.Venom.Hol.Codegen.DfgAnalysis
import EvmYul.Venom.Hol.Codegen.Liveness
import EvmYul.Venom.Hol.Codegen.Cfg
import EvmYul.Venom.Hol.Codegen.Dataflow
import EvmYul.Venom.Hol.Codegen.LivenessAnalysis
import EvmYul.Venom.Hol.Codegen.CodegenPipeline
import EvmYul.Venom.Hol.Codegen.PlanSim
import EvmYul.Venom.Hol.Codegen.GenBlockSimSupport
import EvmYul.Venom.Hol.Codegen.GenBlockSim
import EvmYul.Venom.Hol.Codegen.CodegenCorrectness
import EvmYul.Venom.Hol.Codegen.CodegenGenProps
import EvmYul.Venom.Hol.Codegen.GenInstSim
import EvmYul.Venom.Hol.Codegen.AsmResolveProofs
import EvmYul.Venom.Hol.Codegen.GenBlockSimComp
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample
import EvmYul.Venom.Hol.Codegen.CodegenTest

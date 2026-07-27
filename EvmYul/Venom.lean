import EvmYul.Venom.Operand
import EvmYul.Venom.Instruction
import EvmYul.Venom.Memory
import EvmYul.Venom.VenomMemProps
import EvmYul.Venom.MemInvariant
import EvmYul.Venom.MemBridge
import EvmYul.Venom.State
import EvmYul.Venom.Semantics
import EvmYul.Venom.MemInterp
import EvmYul.Venom.BalanceSlot
import EvmYul.Venom.AbiBridge
import EvmYul.Venom.AbiArrayBridge
import EvmYul.Venom.AbiTupleBridge
import EvmYul.Venom.AbiDispatch
import EvmYul.Venom.AbiDispatchWF
import EvmYul.Venom.AbiSelector
import EvmYul.Venom.AbiEndToEnd
import EvmYul.Venom.AbiReturn
import EvmYul.Venom.AbiBalance
import EvmYul.Venom.AbiTransfer
import EvmYul.Venom.AbiDynKey
import EvmYul.Venom.SlotPacking
import EvmYul.Venom.AbiMultiMap
import EvmYul.Venom.NoAlias
import EvmYul.Venom.SlotAbstraction
import EvmYul.Venom.Solvency
import EvmYul.Venom.EvmBytecodeEquiv
import EvmYul.Venom.Backend
import EvmYul.Venom.Spill
import EvmYul.Venom.Asm
import EvmYul.Venom.AsmBridge
import EvmYul.Venom.AsmJumps
import EvmYul.Venom.AsmResolve
import EvmYul.Venom.AsmTop
import EvmYul.Venom.AsmDJ
import EvmYul.Venom.AsmBackend
import EvmYul.Venom.AsmExample
import EvmYul.Venom.TransferSolvency
import EvmYul.Venom.Erc20
import EvmYul.Venom.FFIMemory
import EvmYul.Venom.NonVacuity
import EvmYul.Venom.Passes
import EvmYul.Venom.Gas

/-!
# Venom IR semantics

A formalization of Vyper's [Venom](https://docs.vyperlang.org/en/latest/venom.html)
SSA-based IR (`vyper --experimental-codegen`):

* `EvmYul/Venom/Operand.lean` — operands (literal / variable / label).
* `EvmYul/Venom/Instruction.lean` — opcodes, instructions, basic blocks,
  functions (CFG).
* `EvmYul/Venom/Memory.lean` — a reasoning-friendly `List UInt8` byte
  memory (so memory facts reduce, unlike `ByteArray`).
* `EvmYul/Venom/VenomMemProps.lean` — proved memory lemmas
  (read-after-write, length, overwrite).
* `EvmYul/Venom/State.lean` — the SSA machine state.
* `EvmYul/Venom/Semantics.lean` — the fuel-bounded CFG interpreter.
-/

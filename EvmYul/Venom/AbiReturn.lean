import EvmYul.Venom.Semantics
import EvmYul.Venom.AbiBridge

/-!
# Venom IR — ABI return-value encode generation

The generator dual of `AbiBridge`'s arg-**decode** bridge: a *provable* link
between the ABI encoding of a primitive return value and the Venom `RETURN`
semantics.

A primitive ABI return (an ERC-20 method returning `uint256`/`bool`/`address`)
is a 32-byte big-endian word — exactly `Abi.encodeUint256` (= `Mem.toBytes32`).
`Abi.returnWord v` is the two-instruction sequence a code generator emits to
return such a value:

    mstore 0, v
    return 0, 32

`execBlock_returnWord` proves that running it halts with returndata =
`Abi.encodeUint256 (s.env v)`, and `run_returnWord` lifts that to the whole-
function `run` interpreter. So the generated code's observable output is exactly
the ABI encoding — the encode half of the primitive ABI wire format, closing the
loop with `AbiBridge` (decode).
-/

namespace EvmYul.Venom

namespace Mem

/-- Reading 32 bytes back at the offset a word was `storeWord`n recovers its
32-byte big-endian encoding. -/
theorem readBytes_storeWord_self (mem : Mem) (addr v : UInt256) :
    (mem.storeWord addr v).readBytes addr.toNat 32 = toBytes32 v := by
  unfold Mem.storeWord
  rw [show (32 : Nat) = (toBytes32 v).length from (toBytes32_length v).symm]
  exact readBytes_writeBytes_self mem addr.toNat (toBytes32 v)

end Mem

namespace Abi

/-- The Venom instruction sequence that ABI-encodes the primitive return value
held in var `v` and returns it: `mstore 0, v; return 0, 32`. Emitting this makes
a method's returndata exactly `encodeUint256 v` (= `Mem.toBytes32 v`). -/
def returnWord (v : VarName) : List Instruction :=
  [ { opcode := .mstore,   operands := [.lit (UInt256.ofNat 0), .var v] },
    { opcode := .«return», operands := [.lit (UInt256.ofNat 0), .lit (UInt256.ofNat 32)] } ]

/-- A basic block that returns the ABI-encoded word in `v`. -/
def returnBlock (lbl : Label) (v : VarName) : BasicBlock :=
  { label := lbl, instrs := returnWord v }

end Abi

namespace VenomState

/-- **ABI return-encode bridge.** Running `Abi.returnWord v` halts the execution
with returndata equal to the ABI encoding `Abi.encodeUint256 (s.env v)` of the
value in `v`. The generator dual of `calldataload_append_toBytes32`. -/
theorem execBlock_returnWord (s : VenomState) (v : VarName) :
    execBlock s (Abi.returnWord v)
      = (s.mstore (UInt256.ofNat 0) (s.env v),
         Control.halt (.ret (Abi.encodeUint256 (s.env v)))) := by
  have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
  have hret : (s.mstore (UInt256.ofNat 0) (s.env v)).memory.readBytes (UInt256.ofNat 0).toNat 32
            = Abi.encodeUint256 (s.env v) :=
    Mem.readBytes_storeWord_self s.memory (UInt256.ofNat 0) (s.env v)
  simp only [Abi.returnWord, execBlock, execInstr, List.map, Operand.evalEnv, h32, hret]

/-- Whole-function version: if the function resolves label `lbl` to the return
block, then `run` from `lbl` halts with returndata = the ABI encoding of `v`. -/
theorem run_returnWord (fn : Function) (fuel : Nat) (lbl : Label) (v : VarName) (s : VenomState)
    (hfind : fn.find? lbl = some (Abi.returnBlock lbl v)) :
    run fn (fuel + 1) lbl s
      = .halted (s.mstore (UInt256.ofNat 0) (s.env v)) (.ret (Abi.encodeUint256 (s.env v))) := by
  simp only [run, hfind, Abi.returnBlock, execBlock_returnWord]

/-- **Primitive echo: decode then encode.** Reading the calldata word at `off`
into a var and returning it with `returnWord` halts with returndata =
`encodeUint256 (s.calldataload off)` — the encode side applied to the decoded
value. (`abi_echo.venom` is the executable witness of this block.) -/
theorem execBlock_echoWord (s : VenomState) (vv : VarName) (off : UInt256) :
    execBlock s
        ({ output := some vv, opcode := .calldataload, operands := [.lit off] } :: Abi.returnWord vv)
      = ((s.set vv (s.calldataload off)).mstore (UInt256.ofNat 0) (s.calldataload off),
         Control.halt (.ret (Abi.encodeUint256 (s.calldataload off)))) := by
  simp only [execBlock, execInstr, List.map, Operand.evalEnv, VenomState.setOutput,
             execBlock_returnWord, VenomState.set_env_self]

/-- **ABI decode∘encode roundtrip at the Venom level.** If the calldata places
the 32-byte encoding of `w` at byte `off`, the echo block returns exactly `w`'s
ABI encoding — decode (`calldataload`, via `AbiBridge`) then encode
(`returnWord`) recovers the input word. -/
theorem execBlock_echoWord_roundtrip (s : VenomState) (vv : VarName)
    (pre suf : Mem) (w : UInt256) (off : UInt256)
    (hcd : s.calldata = pre ++ Mem.toBytes32 w ++ suf)
    (hoff : off.toNat = pre.length) :
    (execBlock s
        ({ output := some vv, opcode := .calldataload, operands := [.lit off] } :: Abi.returnWord vv)).2
      = Control.halt (.ret (Abi.encodeUint256 w)) := by
  rw [execBlock_echoWord, calldataload_append_toBytes32 s pre suf w off hcd hoff]

end VenomState

end EvmYul.Venom

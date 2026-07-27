/-
In-tree ABI selector cross-validation — evm-abi-lean ↔ EVMYulLean.

Now that both projects pin Lean/mathlib v4.31.0, evm-abi-lean is available as an
in-tree `require` (see the project `lakefile.lean`). This closes a gap that was
previously covered only *out of process* by `scripts/abi_crossval.sh`:

  `AbiSelector`/`AbiDispatch` deliberately treat `keccak256` as opaque — they
  prove selector *routing* (`shr 224 (calldataload 0)` recovers the selector and
  the dispatch chain routes it to the right body) but route on pinned selector
  CONSTANTS like `UInt256.ofNat 0xa9059cbb`. Nothing in that build checks those
  constants are the real keccak values.

evm-abi-lean ships a *computable* keccak256 (pure Lean, no FFI/axiom), so here we
recompute the ERC-20 selectors inside this build and machine-check
(`native_decide`) that they equal the constants the dispatcher routes on — an
independent second implementation, in the same `lake` invocation.

This module is built by the dedicated `AbiCrossval` lake target only, so the
default `EvmYul` build stays decoupled from the sibling checkout.
-/
import EvmAbi.Hash
import EvmAbi.Encode
import EvmAbi.Decode
import EvmAbi.Roundtrip
import EvmYul.Venom.AbiDispatch
import EvmYul.Venom.AbiBridge
import EvmYul.Venom.AbiSelector
import EvmYul.Venom.AbiReturn

open EvmYul EvmYul.Venom EvmAbi.ABI

namespace EvmYul.Venom.AbiCrossval

/-- evm-abi-lean's keccak-based function selector, as the big-endian `UInt256`
    the dispatcher compares against (the `shr 224 (calldataload 0)` value). -/
def abiLeanSelector (sig : String) : UInt256 :=
  UInt256.ofNat (fromBytesBigEndian (EvmAbi.Hash.functionSelector sig).toList)

/-! ## The ERC-20 surface

The whole selector table (mirrors `scripts/abi_crossval.sh`'s `ERC20_SELECTORS`)
is checked in one `native_decide` that runs evm-abi-lean's keccak256 for each
signature and compares to the pinned 4-byte value. -/

/-- `signature ↦ pinned selector` for the ERC-20 interface. -/
def erc20Selectors : List (String × Nat) :=
  [ ("totalSupply()",                        0x18160ddd),
    ("balanceOf(address)",                   0x70a08231),
    ("transfer(address,uint256)",            0xa9059cbb),
    ("approve(address,uint256)",             0x095ea7b3),
    ("allowance(address,address)",           0xdd62ed3e),
    ("transferFrom(address,address,uint256)", 0x23b872dd),
    ("mint(address,uint256)",                0x40c10f19) ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- Every ERC-20 selector evm-abi-lean's keccak256 computes equals the pinned
    4-byte value the dispatcher routes on. Proved by `decide +kernel`: abi-lean's keccak
    is pure Lean (no `extern`/`opaque`), so the KERNEL reduces it — no `native_decide`
    axiom, unlike the original. -/
theorem erc20_selectors_match_keccak :
    erc20Selectors.all (fun p => abiLeanSelector p.1 == UInt256.ofNat p.2) := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Cross-validation capstone.** The two selector constants the worked
    dispatcher `EvmYul.Venom.exFn` routes on (`AbiDispatch`) are exactly
    evm-abi-lean's keccak256 values for `transfer`/`balanceOf`. Composed with
    `exFn_routes_transfer` / `exFn_routes_balanceOf`, a call whose selector is the
    *real* `keccak256(sig) >> 224` reaches the correct method body — the keccak
    value now verified in-tree rather than only by the out-of-process harness. -/
theorem exFn_selectors_are_keccak :
    abiLeanSelector "transfer(address,uint256)" = UInt256.ofNat 0xa9059cbb ∧
    abiLeanSelector "balanceOf(address)"        = UInt256.ofNat 0x70a08231 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## Calldata argument cross-validation (encode → decode)

Beyond the selector *values*, this pins the argument *layout*: evm-abi-lean's
`encodeArgs` for a concrete `transfer(address,uint256)` call produces exactly the
bytes EVMYulLean's native encoder lays down (`Abi.encodeAddress`/`encodeUint256`
= `Mem.toBytes32`), and feeding that calldata through EVMYulLean's proved
`AbiBridge` decode (`CALLDATALOAD` at offsets 4 / 36) recovers the original
recipient and amount — the full external-encode ↔ internal-decode loop, in one
`lake` build. -/

/-- A concrete 20-byte recipient address (bytes `01..14`). -/
def recvBytes : ByteArray := ⟨(List.range 20 |>.map (fun i => UInt8.ofNat (i + 1))).toArray⟩

/-- …as the `UInt256` EVMYulLean carries (big-endian, `< 2^160`). -/
def recvU : UInt256 := UInt256.ofNat (fromBytesBigEndian recvBytes.toList)

/-- A concrete transfer amount. -/
def amtU : UInt256 := UInt256.ofNat 1000

/-- evm-abi-lean's ABI-encoded `transfer(address,uint256)` arguments, as bytes. -/
def abiLeanTransferArgs : Option (List UInt8) :=
  (EvmAbi.ABI.Encode.encodeArgs
     [.address, .uint (ByteSize.ofLen 32 (by omega))]
     [.address recvBytes, .uint amtU.toNat]).toOption.map (·.toList)

set_option maxRecDepth 4000000 in
/-- **Encoder agreement.** evm-abi-lean's `encodeArgs` produces byte-for-byte the
    same argument region as EVMYulLean's native `encodeAddress ++ encodeUint256`
    — two independent encoders, checked by one `decide +kernel` (kernel reduction, no
    `native_decide` axiom). -/
theorem abiLeanTransferArgs_eq_native :
    abiLeanTransferArgs = some (Abi.encodeAddress recvU ++ Abi.encodeUint256 amtU) := by
  decide +kernel

/-- `transfer` calldata whose 64-byte argument region is evm-abi-lean's
    `encodeArgs` output, after a 4-byte selector. -/
def abiLeanTransferCalldata (selVal : UInt256) : Mem :=
  Abi.selectorBytes selVal ++ (abiLeanTransferArgs.getD [])

/-- **Encode→decode cross-validation.** Calldata whose argument region is
    evm-abi-lean's `encodeArgs` output decodes — through EVMYulLean's proved
    `AbiBridge` (`calldataload` at 4 / 36) — back to the original recipient and
    amount. Composes `abiLeanTransferArgs_eq_native` (encoders agree) with the
    native decode lemmas: external encode ↔ internal decode, closed in-tree. -/
theorem abiLean_transfer_decodes (s : VenomState) (selVal : UInt256)
    (hcd : s.calldata = abiLeanTransferCalldata selVal) :
    s.calldataload (UInt256.ofNat 4) = recvU ∧ s.calldataload (UInt256.ofNat 36) = amtU := by
  have hargs : abiLeanTransferArgs.getD [] = Abi.encodeAddress recvU ++ Abi.encodeUint256 amtU := by
    rw [abiLeanTransferArgs_eq_native]; rfl
  rw [abiLeanTransferCalldata, hargs] at hcd
  refine ⟨?_, ?_⟩
  · exact VenomState.calldataload_transfer_to s (Abi.selectorBytes selVal) [] recvU amtU
      (Asm.beBytesN_length 4 selVal (by decide)) (by rw [hcd]; simp [List.append_assoc])
  · exact VenomState.calldataload_transfer_amount s (Abi.selectorBytes selVal) [] recvU amtU
      (Asm.beBytesN_length 4 selVal (by decide)) (by rw [hcd]; simp [List.append_assoc])

/-- **Roundtrip capstone, instantiated (generic route).** evm-abi-lean's headline
    `roundtrip_args_wff` — any well-formed argument list decodes back after encoding — applied at
    the transfer signature `(address, uint256)`, well-formedness by constructors. Whatever bytes
    the encoder produced for the transfer arguments, the decoder returns exactly the original
    values. Base axioms (no `native_decide`). -/
theorem abiLean_transferArgs_roundtrip_wff (data : ByteArray)
    (hsz : data.size < 2 ^ 256)
    (henc : EvmAbi.ABI.Encode.encodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))]
        [.address recvBytes, .uint amtU.toNat] = Except.ok data) :
    EvmAbi.ABI.Decode.decodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))] data
      = Except.ok [.address recvBytes, .uint amtU.toNat] :=
  roundtrip_args_wff _ data _
    (by intro t ht
        rcases List.mem_cons.mp ht with rfl | ht2
        · exact .address
        · rcases List.mem_cons.mp ht2 with rfl | h3
          · exact .uint _
          · exact absurd h3 (by simp))
    hsz henc

set_option maxRecDepth 4000000 in
/-- **Roundtrip capstone, computed (concrete route).** Encode → decode → re-encode on the transfer
    arguments is a byte-level fixpoint — the `decide +kernel` cross-check of the roundtrip on the
    same concrete data the encoder-agreement theorems feed (`ABIValue` equality is checked through
    the injective re-encoding, keeping the comparison on decidable `ByteArray`s). -/
theorem abiLean_transferArgs_roundtrip_bytes :
    ((EvmAbi.ABI.Encode.encodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))]
        [.address recvBytes, .uint amtU.toNat]).toOption.bind fun data =>
      (EvmAbi.ABI.Decode.decodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))] data).toOption.bind fun vals =>
      (EvmAbi.ABI.Encode.encodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))] vals).toOption)
      = (EvmAbi.ABI.Encode.encodeArgs
        [.address, .uint (EvmAbi.ABI.ByteSize.ofLen 32 (by omega))]
        [.address recvBytes, .uint amtU.toNat]).toOption := by
  decide +kernel

/-! ## Dynamic-array calldata cross-validation (offset → length → data)

The primitive path above is static (fixed offsets). This checks the DYNAMIC
layout: evm-abi-lean's `encodeArgs` for `sum(uint256[])` with `[10,20,30]`, and
the offset-following decode `EvmYul/Venom/examples/abi_dynarray.venom` performs —
read the ABI pointer `off = calldataload 4`, then elements at `4 + off + 32·(i+1)`
— recovers the elements and sums to `60`, proved over the Venom `calldataload`
semantics (each read via the proved `AbiBridge.calldataload_append_toBytes32`). -/

/-- evm-abi-lean's ABI encoding of `sum(uint256[])`'s `[10,20,30]` argument. -/
def abiLeanSumArgs : Option (List UInt8) :=
  (EvmAbi.ABI.Encode.encodeArgs
     [.array (.uint (ByteSize.ofLen 32 (by omega)))]
     [.array [.uint 10, .uint 20, .uint 30]]).toOption.map (·.toList)

/-- The native ABI head/tail word-chain: offset `0x20`, length `3`, elements. -/
def sumNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3) ++
  Mem.toBytes32 (UInt256.ofNat 10) ++ Mem.toBytes32 (UInt256.ofNat 20) ++
  Mem.toBytes32 (UInt256.ofNat 30)

/-- **Encoder agreement (dynamic).** evm-abi-lean's dynamic-array `encodeArgs`
    lays down exactly the head/tail word-chain (offset ++ length ++ elements). -/
theorem abiLeanSumArgs_eq_native : abiLeanSumArgs = some sumNativeChain := by native_decide

/-- `sum(uint256[])` calldata whose argument region is evm-abi-lean's encoding. -/
def abiLeanSumCalldata (selVal : UInt256) : Mem :=
  Abi.selectorBytes selVal ++ (abiLeanSumArgs.getD [])

/-- **Dynamic offset-following decode.** Mirrors `abi_dynarray.venom`: read the
    ABI pointer `off = calldataload 4`, then the three elements at
    `4 + off + {32,64,96}`; over evm-abi-lean's encoded calldata they are
    `10, 20, 30`, summing to `60` (`0x3c`, venom_run's return) — the dynamic
    offset/length/data layout, cross-validated in-tree over the Venom semantics. -/
theorem abiLean_dynarray_sum (s : VenomState) (selVal : UInt256)
    (hcd : s.calldata = abiLeanSumCalldata selVal) :
    s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 4) + UInt256.ofNat 32)
  + s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 4) + UInt256.ofNat 64)
  + s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 4) + UInt256.ofNat 96)
    = UInt256.ofNat 60 := by
  have hargs : abiLeanSumArgs.getD [] = sumNativeChain := by rw [abiLeanSumArgs_eq_native]; rfl
  rw [abiLeanSumCalldata, hargs] at hcd
  have hsl : (Abi.selectorBytes selVal).length = 4 := Asm.beBytesN_length 4 selVal (by decide)
  have hoff : s.calldataload (UInt256.ofNat 4) = UInt256.ofNat 0x20 := by
    apply VenomState.calldataload_append_toBytes32 s (Abi.selectorBytes selVal)
      (Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10) ++
       Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 0x20)
    · rw [hcd, sumNativeChain]; ac_rfl
    · rw [hsl]; native_decide
  rw [hoff]
  have he0 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 32)
      = UInt256.ofNat 10 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3))
      (Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 10)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  have he1 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 64)
      = UInt256.ofNat 20 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3)
        ++ Mem.toBytes32 (UInt256.ofNat 10))
      (Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 20)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  have he2 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 96)
      = UInt256.ofNat 30 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3)
        ++ Mem.toBytes32 (UInt256.ofNat 10) ++ Mem.toBytes32 (UInt256.ofNat 20))
      [] (UInt256.ofNat 30)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  rw [he0, he1, he2]; native_decide

/-! ## Mixed static+dynamic calldata cross-validation

`mixed(uint256, uint256[])` with `(7, [10,20,30])`: the head is a static word
(inline) followed by an offset pointer — exactly the shape of a struct with one
static and one dynamic field (matches `EvmYul/Venom/examples/abi_dynstruct.venom`).
Decode reads the static uint at 4, follows the pointer at 36 to the array, then its
elements; total `7 + 10 + 20 + 30 = 67` (`0x43`, venom_run's return). -/

/-- evm-abi-lean's ABI encoding of `mixed(uint256, uint256[])`'s `(7,[10,20,30])`. -/
def abiLeanMixedArgs : Option (List UInt8) :=
  (EvmAbi.ABI.Encode.encodeArgs
     [.uint (ByteSize.ofLen 32 (by omega)), .array (.uint (ByteSize.ofLen 32 (by omega)))]
     [.uint 7, .array [.uint 10, .uint 20, .uint 30]]).toOption.map (·.toList)

/-- The native chain: static `7`, offset `0x40`, length `3`, then elements. -/
def mixedNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40) ++
  Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10) ++
  Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)

/-- **Encoder agreement (mixed).** evm-abi-lean lays down static-word ++ pointer ++
    (length ++ elements). -/
theorem abiLeanMixedArgs_eq_native : abiLeanMixedArgs = some mixedNativeChain := by native_decide

/-- `mixed(...)` calldata whose argument region is evm-abi-lean's encoding. -/
def abiLeanMixedCalldata (selVal : UInt256) : Mem :=
  Abi.selectorBytes selVal ++ (abiLeanMixedArgs.getD [])

/-- **Mixed static+dynamic decode.** Reads the static `uint256` at 4, the array
    pointer `off` at 36, then the elements at `4 + off + {32,64,96}`; over
    evm-abi-lean's encoded calldata the total is `7 + 10 + 20 + 30 = 67` — the
    struct-with-dynamic-field head layout, cross-validated over the Venom semantics. -/
theorem abiLean_mixed_sum (s : VenomState) (selVal : UInt256)
    (hcd : s.calldata = abiLeanMixedCalldata selVal) :
    s.calldataload (UInt256.ofNat 4)
  + s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 36) + UInt256.ofNat 32)
  + s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 36) + UInt256.ofNat 64)
  + s.calldataload (UInt256.ofNat 4 + s.calldataload (UInt256.ofNat 36) + UInt256.ofNat 96)
    = UInt256.ofNat 67 := by
  have hargs : abiLeanMixedArgs.getD [] = mixedNativeChain := by rw [abiLeanMixedArgs_eq_native]; rfl
  rw [abiLeanMixedCalldata, hargs] at hcd
  have hsl : (Abi.selectorBytes selVal).length = 4 := Asm.beBytesN_length 4 selVal (by decide)
  have hst : s.calldataload (UInt256.ofNat 4) = UInt256.ofNat 7 := by
    apply VenomState.calldataload_append_toBytes32 s (Abi.selectorBytes selVal)
      (Mem.toBytes32 (UInt256.ofNat 0x40) ++ Mem.toBytes32 (UInt256.ofNat 3) ++
       Mem.toBytes32 (UInt256.ofNat 10) ++ Mem.toBytes32 (UInt256.ofNat 20) ++
       Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 7)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · rw [hsl]; native_decide
  have hoff : s.calldataload (UInt256.ofNat 36) = UInt256.ofNat 0x40 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7))
      (Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10) ++
       Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 0x40)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  rw [hst, hoff]
  have he0 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 32)
      = UInt256.ofNat 10 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3))
      (Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 10)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  have he1 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 64)
      = UInt256.ofNat 20 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10))
      (Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 20)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  have he2 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 96)
      = UInt256.ofNat 30 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10)
        ++ Mem.toBytes32 (UInt256.ofNat 20))
      [] (UInt256.ofNat 30)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; native_decide
  rw [he0, he1, he2]; native_decide

/-! ## Return-value cross-validation (encode → decode)

The calldata paths above are the DECODE direction (evm-abi-lean encodes, EVMYulLean
decodes). This is the ENCODE direction: EVMYulLean's `Abi.returnWord` execution
halts with returndata `Abi.encodeUint256 v` (`execBlock_returnWord`), and
evm-abi-lean's `decode` recovers the original value from those bytes — closing the
other half of the loop (external-decode ↔ internal-encode). -/

/-- **Return-side cross-validation.** For any state whose var `v` holds the
    concrete value `amtU`, running `Abi.returnWord v` halts with returndata
    `Abi.encodeUint256 amtU`, and evm-abi-lean's `decode` reads that back as
    `amtU` — the encode-direction complement of `abiLean_transfer_decodes`. -/
theorem abiLean_decodes_returnWord (s : VenomState) (v : VarName) (hv : s.env v = amtU) :
    (execBlock s (Abi.returnWord v)).2 = Control.halt (.ret (Abi.encodeUint256 amtU))
  ∧ ((EvmAbi.ABI.Decode.decode (.uint (ByteSize.ofLen 32 (by omega)))
        ⟨(Abi.encodeUint256 amtU).toArray⟩ 0).toOption.map (·.1)
      == some (ABIValue.uint amtU.toNat)) := by
  refine ⟨?_, by native_decide⟩
  simp only [VenomState.execBlock_returnWord, hv]

end EvmYul.Venom.AbiCrossval

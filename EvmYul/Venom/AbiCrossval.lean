/-
In-tree ABI selector cross-validation — evm-abi-lean ↔ EVMYulLean.

Now that both projects pin Lean/mathlib v4.32.0, evm-abi-lean is available as an
in-tree `require` (see the project `lakefile.lean`). This closes a gap that was
previously covered only *out of process* by `scripts/abi_crossval.sh`:

  `AbiSelector`/`AbiDispatch` deliberately treat `keccak256` as opaque — they
  prove selector *routing* (`shr 224 (calldataload 0)` recovers the selector and
  the dispatch chain routes it to the right body) but route on pinned selector
  CONSTANTS like `UInt256.ofNat 0xa9059cbb`. Nothing in that build checks those
  constants are the real keccak values.

`AbiLean.Hash` supplies a *computable* keccak256 (pure Lean, no FFI/axiom), so here
we recompute the ERC-20 selectors inside this build and machine-check
(`decide +kernel`) that they equal the constants the dispatcher routes on — an
independent second implementation, in the same `lake` invocation. (Our own `ffi.KEC`
is opaque to the kernel, which is why a pure-Lean keccak is needed.)

Trust footing: **every result here is proved on base axioms only** (kernel
reduction / structural proof — `[propext, Quot.sound]`, at most `Classical.choice`),
with **zero `native_decide`**, matching the Venom codegen stack's footing. By section:

  * Selector values (`erc20_selectors_match_keccak`, `exFn_selectors_are_keccak`)
    — `decide +kernel`: `AbiLean.Hash`'s keccak256 is pure Lean with no `extern`/`opaque`,
    so the KERNEL reduces it. The headline check — the constants the dispatcher
    routes on ARE the real keccak256 values.

  * Encoder/decoder agreement (`abiLeanTransferArgs_eq_native`, `abiLeanSumArgs_eq_native`,
    `abiLeanMixedArgs_eq_native`, and the additional type-surface checks
    `abiLeanBytesArgs_eq_native` / `..StringArgs..` / `..Bytes4Args..` / `..NegIntArgs..`)
    — `decide +kernel`. The Ty-indexed `AbiLean.encodeArgs` is well-founded-recursive over
    `Ty` (`termination_by`, so `Acc.rec`, kernel-opaque), so `AbiLean.CodecEval` adds a
    kernel-reducible mirror `AbiLean.encodeF` (fuel-indexed, structural) with the bridge
    `AbiLean.encodeArgs_eq_encodeF`: rewriting the wf `encodeArgs` to `encodeF` at a
    concrete fuel lets the kernel evaluate it. The type-surface checks cover the layout
    mechanisms the core sections don't: dynamic `bytes`/`string` (padded raw data),
    static `bytesN` (left-aligned), and negative `int` (two's-complement sign extension).

  * Roundtrips (`abiLean_transferArgs_roundtrip`, `..._roundtrip_bytes`) and the
    return decode (`abiLean_decodes_returnWord`) — the library's own `roundtrip` /
    `roundtrip_args` (base axioms) discharges `decode ∘ encode` abstractly, so the
    wf-opaque `decode` is never evaluated; the `hb` length side-goal reduces via the
    `encodeF` bridge. No `decodeF` mirror is needed — see `AbiLean/CodecEval.lean`.

  * Venom-semantics decode (`abiLean_transfer_decodes`, `abiLean_dynarray_sum`,
    `abiLean_mixed_sum`) — kernel rewriting over the proved `AbiBridge` `calldataload`
    lemmas, composed with the `*_eq_native` agreement facts (all base axioms).

Design note: the sibling `crossval-kernel` branch reached `decide +kernel` on the
encoder theorems by making the ABIType encoder's `headSize` kernel-reducible. The
Ty-indexed `main` design keeps a small, type-indexed wf-recursive codec AND regains
kernel evaluation via the additive `AbiLean.encodeF` bridge (`AbiLean/CodecEval.lean`).
Two things closed the last `native_decide` gaps: (1) the bridge for the encoder, and
(2) defining the concrete address `recvU` from a pure byte `List` rather than a
`ByteArray` (whose `@[extern]` `toList` was kernel-opaque) — so `recvU.toNat` reduces
and the transfer checks join the rest on base axioms.

Layout note: the selector/keccak (`AbiLean.Hash`), the function-argument level
(`AbiLean.Args`) and the kernel-reducible mirror (`AbiLean.CodecEval`) live in THIS
repo under `EvmYul/Venom/AbiLean/`, not in evm-abi-lean — that library's scope is the
codec roundtrip, a hash is a separate primitive, and the argument level is
definitionally the tuple level. Keeping them here leaves the dependency plain
upstream, so it is pinned to a commit rather than a sibling path.

This module is built by the dedicated `AbiCrossval` lake target only, so the
default `EvmYul` build stays decoupled from the ABI dependency.
-/
import EvmYul.Venom.AbiLean.Hash
import EvmAbi.Codec
import EvmAbi.Codec.Strict
import EvmYul.Venom.AbiLean.CodecEval
import EvmYul.Venom.AbiDispatch
import EvmYul.Venom.AbiBridge
import EvmYul.Venom.AbiSelector
import EvmYul.Venom.AbiReturn

open EvmYul EvmYul.Venom EvmAbi

namespace EvmYul.Venom.AbiCrossval

/-- evm-abi-lean's keccak-based function selector, as the big-endian `UInt256`
    the dispatcher compares against (the `shr 224 (calldataload 0)` value). -/
def abiLeanSelector (sig : String) : UInt256 :=
  UInt256.ofNat (fromBytesBigEndian (AbiLean.Hash.functionSelector sig).toList)

/-! ## The ERC-20 surface

The whole selector table (mirrors `scripts/abi_crossval.sh`'s `ERC20_SELECTORS`)
is checked in one `decide +kernel` that runs evm-abi-lean's keccak256 for each
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

/-- A concrete 20-byte recipient address (bytes `01..14`), as a plain byte `List`
    — NOT a `ByteArray`, whose `@[extern]` `toList` is kernel-opaque — so that
    `recvU.toNat` reduces in the kernel and the transfer checks stay on base axioms. -/
def recvBytes : List UInt8 := List.range 20 |>.map (fun i => UInt8.ofNat (i + 1))

/-- …as the `UInt256` EVMYulLean carries (big-endian, `< 2^160`). -/
def recvU : UInt256 := UInt256.ofNat (fromBytesBigEndian recvBytes)

/-- A concrete transfer amount. -/
def amtU : UInt256 := UInt256.ofNat 1000

set_option maxRecDepth 100000 in
/-- `recvU`'s underlying `Nat` is a 160-bit address value.  Base axioms
    (`decide +kernel`): `recvBytes` is a pure `List`, so `recvU.toNat` reduces
    (`fromBytesBigEndian` is pure Lean; only the old `ByteArray` path was opaque). -/
theorem recvU_toNat_lt : recvU.toNat < 2 ^ 160 := by decide +kernel

/-- `amtU`'s underlying `Nat` is in `uint256` range (base axioms:
    `uint256_ofNat_toNat` + `omega`). -/
theorem amtU_toNat_lt : amtU.toNat < 2 ^ 256 := by
  show (UInt256.ofNat 1000).toNat < 2 ^ 256
  rw [uint256_ofNat_toNat]; omega

/-- evm-abi-lean's ABI-encoded `transfer(address,uint256)` arguments, as bytes. -/
def abiLeanTransferArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.address, .uint 256]
     (⟨recvU.toNat, recvU_toNat_lt⟩, ⟨amtU.toNat, amtU_toNat_lt⟩, ⟨⟩))

set_option maxRecDepth 100000 in
/-- **Encoder agreement.** evm-abi-lean's `encodeArgs` produces byte-for-byte the
    same argument region as EVMYulLean's native `encodeAddress ++ encodeUint256`
    — two independent encoders, checked by `decide +kernel` (base axioms) via the
    `AbiLean.encodeArgs_eq_encodeF` bridge.  `recvU` is `List`-based, so its address
    bytes reduce in the kernel (the old `ByteArray` value was what forced `native_decide`). -/
theorem abiLeanTransferArgs_eq_native :
    abiLeanTransferArgs = some (Abi.encodeAddress recvU ++ Abi.encodeUint256 amtU) := by
  unfold abiLeanTransferArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]
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

set_option maxRecDepth 100000 in
/-- **Roundtrip, instantiated.** evm-abi-lean's argument roundtrip at the transfer signature
    `(address, uint256)`: the encoded arguments decode back to exactly the original values.
    Base axioms — an instance of the library's `roundtrip_args`; `decode` stays wf-opaque
    (proved abstractly, not evaluated), and the `hb` length side-goal reduces via the
    `encodeArgs_eq_encodeF` bridge. -/
theorem abiLean_transferArgs_roundtrip :
    AbiLean.decodeArgs [.address, .uint 256]
        (AbiLean.encodeArgs [.address, .uint 256]
          (⟨recvU.toNat, recvU_toNat_lt⟩, ⟨amtU.toNat, amtU_toNat_lt⟩, ⟨⟩))
      = some (⟨recvU.toNat, recvU_toNat_lt⟩, ⟨amtU.toNat, amtU_toNat_lt⟩, ⟨⟩) := by
  apply AbiLean.roundtrip_args [.address, .uint 256] (by decide) _
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]; decide +kernel

set_option maxRecDepth 100000 in
/-- **Roundtrip capstone, computed (concrete route).** Encode → decode → re-encode on the transfer
    arguments is a byte-level fixpoint — base axioms, by rewriting with the roundtrip above. -/
theorem abiLean_transferArgs_roundtrip_bytes :
    ((AbiLean.decodeArgs [.address, .uint 256]
        (AbiLean.encodeArgs [.address, .uint 256]
          (⟨recvU.toNat, recvU_toNat_lt⟩, ⟨amtU.toNat, amtU_toNat_lt⟩, ⟨⟩))).map
        (AbiLean.encodeArgs [.address, .uint 256]))
      = some (AbiLean.encodeArgs [.address, .uint 256]
          (⟨recvU.toNat, recvU_toNat_lt⟩, ⟨amtU.toNat, amtU_toNat_lt⟩, ⟨⟩)) := by
  rw [abiLean_transferArgs_roundtrip]; rfl

/-! ## Dynamic-array calldata cross-validation (offset → length → data)

The primitive path above is static (fixed offsets). This checks the DYNAMIC
layout: evm-abi-lean's `encodeArgs` for `sum(uint256[])` with `[10,20,30]`, and
the offset-following decode `EvmYul/Venom/examples/abi_dynarray.venom` performs —
read the ABI pointer `off = calldataload 4`, then elements at `4 + off + 32·(i+1)`
— recovers the elements and sums to `60`, proved over the Venom `calldataload`
semantics (each read via the proved `AbiBridge.calldataload_append_toBytes32`). -/

/-- evm-abi-lean's ABI encoding of `sum(uint256[])`'s `[10,20,30]` argument. -/
def abiLeanSumArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.array (.uint 256)]
     (⟨[⟨10, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩], by decide⟩, ⟨⟩))

/-- The native ABI head/tail word-chain: offset `0x20`, length `3`, elements. -/
def sumNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3) ++
  Mem.toBytes32 (UInt256.ofNat 10) ++ Mem.toBytes32 (UInt256.ofNat 20) ++
  Mem.toBytes32 (UInt256.ofNat 30)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (dynamic).** evm-abi-lean's dynamic-array `encodeArgs`
    lays down exactly the head/tail word-chain (offset ++ length ++ elements).
    Proved by `decide +kernel` (base axioms): the `AbiLean.encodeArgs_eq_encodeF`
    bridge swaps the wf-recursive `encodeArgs` for the kernel-reducible `encodeF`
    at a concrete fuel, which the kernel then evaluates. -/
theorem abiLeanSumArgs_eq_native : abiLeanSumArgs = some sumNativeChain := by
  unfold abiLeanSumArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by decide)]
  decide +kernel

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
    · rw [hsl]; decide
  rw [hoff]
  have he0 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 32)
      = UInt256.ofNat 10 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3))
      (Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 10)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  have he1 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 64)
      = UInt256.ofNat 20 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3)
        ++ Mem.toBytes32 (UInt256.ofNat 10))
      (Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 20)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  have he2 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x20 + UInt256.ofNat 96)
      = UInt256.ofNat 30 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3)
        ++ Mem.toBytes32 (UInt256.ofNat 10) ++ Mem.toBytes32 (UInt256.ofNat 20))
      [] (UInt256.ofNat 30)
    · rw [hcd, sumNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  rw [he0, he1, he2]; decide

/-! ## Mixed static+dynamic calldata cross-validation

`mixed(uint256, uint256[])` with `(7, [10,20,30])`: the head is a static word
(inline) followed by an offset pointer — exactly the shape of a struct with one
static and one dynamic field (matches `EvmYul/Venom/examples/abi_dynstruct.venom`).
Decode reads the static uint at 4, follows the pointer at 36 to the array, then its
elements; total `7 + 10 + 20 + 30 = 67` (`0x43`, venom_run's return). -/

/-- evm-abi-lean's ABI encoding of `mixed(uint256, uint256[])`'s `(7,[10,20,30])`. -/
def abiLeanMixedArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.uint 256, .array (.uint 256)]
     (⟨7, by decide⟩, ⟨[⟨10, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩], by decide⟩, ⟨⟩))

/-- The native chain: static `7`, offset `0x40`, length `3`, then elements. -/
def mixedNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40) ++
  Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10) ++
  Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (mixed).** evm-abi-lean lays down static-word ++ pointer ++
    (length ++ elements).  `decide +kernel` (base axioms) via the
    `AbiLean.encodeArgs_eq_encodeF` bridge to the kernel-reducible `encodeF`. -/
theorem abiLeanMixedArgs_eq_native : abiLeanMixedArgs = some mixedNativeChain := by
  unfold abiLeanMixedArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by decide)]
  decide +kernel

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
    · rw [hsl]; decide
  have hoff : s.calldataload (UInt256.ofNat 36) = UInt256.ofNat 0x40 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7))
      (Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10) ++
       Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 0x40)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  rw [hst, hoff]
  have he0 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 32)
      = UInt256.ofNat 10 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3))
      (Mem.toBytes32 (UInt256.ofNat 20) ++ Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 10)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  have he1 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 64)
      = UInt256.ofNat 20 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10))
      (Mem.toBytes32 (UInt256.ofNat 30)) (UInt256.ofNat 20)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  have he2 : s.calldataload (UInt256.ofNat 4 + UInt256.ofNat 0x40 + UInt256.ofNat 96)
      = UInt256.ofNat 30 := by
    apply VenomState.calldataload_append_toBytes32 s
      (Abi.selectorBytes selVal ++ Mem.toBytes32 (UInt256.ofNat 7) ++ Mem.toBytes32 (UInt256.ofNat 0x40)
        ++ Mem.toBytes32 (UInt256.ofNat 3) ++ Mem.toBytes32 (UInt256.ofNat 10)
        ++ Mem.toBytes32 (UInt256.ofNat 20))
      [] (UInt256.ofNat 30)
    · rw [hcd, mixedNativeChain]; ac_rfl
    · simp only [List.length_append, Mem.toBytes32_length, hsl]; decide
  rw [he0, he1, he2]; decide

/-! ## Return-value cross-validation (encode → decode)

The calldata paths above are the DECODE direction (evm-abi-lean encodes, EVMYulLean
decodes). This is the ENCODE direction: EVMYulLean's `Abi.returnWord` execution
halts with returndata `Abi.encodeUint256 v` (`execBlock_returnWord`), and
evm-abi-lean's `decode` recovers the original value from those bytes — closing the
other half of the loop (external-decode ↔ internal-encode). -/

set_option maxRecDepth 100000 in
/-- **Return-side cross-validation.** For any state whose var `v` holds the
    concrete value `amtU`, running `Abi.returnWord v` halts with returndata
    `Abi.encodeUint256 amtU`, and evm-abi-lean's `decode` reads that back as
    `amtU` — the encode-direction complement of `abiLean_transfer_decodes`.
    Proved on base axioms (no `native_decide`): the amount `amtU` is a literal, so
    the `CodecEval` bridge rewrites `Abi.encodeUint256 amtU` (= `Mem.toBytes32`) to
    evm-abi-lean's `encode (.uint 256) …` (checked by `decide +kernel`), and the
    library's own `decodeStrict_encode` closes `decodeStrict ∘ encode`.  Return
    data is a whole buffer, so the strict decoder is the right one: it also
    pins that the word consumes the buffer exactly. -/
theorem abiLean_decodes_returnWord (s : VenomState) (v : VarName) (hv : s.env v = amtU) :
    (execBlock s (Abi.returnWord v)).2 = Control.halt (.ret (Abi.encodeUint256 amtU))
  ∧ ((EvmAbi.decodeStrict (.uint 256) (Abi.encodeUint256 amtU)).map (·.val)
      == some amtU.toNat) := by
  refine ⟨by simp only [VenomState.execBlock_returnWord, hv], ?_⟩
  have henc : Abi.encodeUint256 amtU = EvmAbi.encode (.uint 256) ⟨amtU.toNat, amtU_toNat_lt⟩ := by
    rw [← AbiLean.encodeF_eq_encode 5 (.uint 256) ⟨amtU.toNat, amtU_toNat_lt⟩ (by rfl)]; decide +kernel
  have hlen : (EvmAbi.encode (.uint 256) ⟨amtU.toNat, amtU_toNat_lt⟩).length < 2 ^ 256 := by
    rw [← AbiLean.encodeF_eq_encode 5 (.uint 256) ⟨amtU.toNat, amtU_toNat_lt⟩ (by rfl)]; decide +kernel
  rw [henc, EvmAbi.decodeStrict_encode (.uint 256) (by decide) ⟨amtU.toNat, amtU_toNat_lt⟩ hlen]
  rfl

/-! ## Additional type-surface cross-validation

The sections above exercise the core layout mechanisms (static words, dynamic
arrays, mixed static+dynamic). These pin the remaining *distinct* ABI encodings
against EVMYulLean's byte layout — each `decide +kernel` (base axioms) through the
`AbiLean.encodeArgs_eq_encodeF` bridge:

  * dynamic `bytes` / `string` — `offset ++ length ++ right-zero-padded data`
    (distinct from arrays, which lay one 32-byte word *per element*);
  * static `bytesN` — data LEFT-aligned, zero-padded on the right (the opposite of
    `uint`/`int`, which are right-aligned, zero-padded on the left);
  * signed `int` at a negative value — two's-complement sign extension (all-`0xff`),
    which the non-negative `uint` cases never exercise. -/

/-- `foo(bytes)` with the 3-byte value `0xaabbcc`. -/
def abiLeanBytesArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.bytes] (⟨[0xaa, 0xbb, 0xcc], by decide⟩, ⟨⟩))

/-- The native chain: offset `0x20`, length `3`, then the data right-padded to 32. -/
def bytesNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3) ++
  ([0xaa, 0xbb, 0xcc] : List UInt8) ++ List.replicate 29 (0 : UInt8)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (dynamic bytes).** evm-abi-lean lays down offset ++ length ++
    the raw bytes right-padded to a 32-byte boundary. -/
theorem abiLeanBytesArgs_eq_native : abiLeanBytesArgs = some bytesNativeChain := by
  unfold abiLeanBytesArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]
  decide +kernel

/-- `greet(string)` with `"abc"` (UTF-8 `0x61 0x62 0x63`). -/
def abiLeanStringArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.string] (⟨"abc", by decide⟩, ⟨⟩))

/-- The native chain: offset `0x20`, length `3`, UTF-8 bytes right-padded to 32. -/
def stringNativeChain : Mem :=
  Mem.toBytes32 (UInt256.ofNat 0x20) ++ Mem.toBytes32 (UInt256.ofNat 3) ++
  ([0x61, 0x62, 0x63] : List UInt8) ++ List.replicate 29 (0 : UInt8)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (dynamic string).** `string` encodes exactly like `bytes`
    over its UTF-8 octets — same offset/length/right-padded-data layout. -/
theorem abiLeanStringArgs_eq_native : abiLeanStringArgs = some stringNativeChain := by
  unfold abiLeanStringArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]
  decide +kernel

/-- `tag(bytes4)` with `0xdeadbeef`. -/
def abiLeanBytes4Args : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.bytesN 4] (⟨[0xde, 0xad, 0xbe, 0xef], by decide⟩, ⟨⟩))

/-- The native word: the 4 bytes LEFT-aligned, then 28 zero bytes. -/
def bytes4NativeChain : Mem :=
  ([0xde, 0xad, 0xbe, 0xef] : List UInt8) ++ List.replicate 28 (0 : UInt8)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (static `bytesN`).** `bytesN` sits LEFT-aligned in its word
    (right-zero-padded) — the mirror image of `uint`/`address`, which are
    right-aligned (left-zero-padded). -/
theorem abiLeanBytes4Args_eq_native : abiLeanBytes4Args = some bytes4NativeChain := by
  unfold abiLeanBytes4Args
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]
  decide +kernel

/-- `setDelta(int256)` with `-1`. -/
def abiLeanNegIntArgs : Option (List UInt8) :=
  some (AbiLean.encodeArgs [.int 256] (⟨-1, by decide⟩, ⟨⟩))

/-- The native word: two's-complement `-1` is all-`0xff` (32 bytes). -/
def negIntNativeChain : Mem := List.replicate 32 (0xff : UInt8)

set_option maxRecDepth 100000 in
/-- **Encoder agreement (negative `int`).** A negative signed integer is sign-extended
    to two's complement — `-1` fills the whole word with `0xff`. The non-negative
    `uint` cases never touch this path. -/
theorem abiLeanNegIntArgs_eq_native : abiLeanNegIntArgs = some negIntNativeChain := by
  unfold abiLeanNegIntArgs
  rw [AbiLean.encodeArgs_eq_encodeF 100 _ _ (by rfl)]
  decide +kernel

end EvmYul.Venom.AbiCrossval

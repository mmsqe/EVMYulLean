#!/usr/bin/env bash
#
# ABI cross-validation:  evm-abi-lean  vs  EVMYulLean, out-of-process.
#
# Two independent Lean projects (both on v4.32.0; abi-lean is ALSO an in-tree
# lake dependency checked by the `AbiCrossval` target) are cross-checked on the
# ERC-20 wire format by shuttling raw bytes between them — this script is the
# out-of-process, executable-oracle complement to the in-tree proofs (it runs
# the compiled `venom_run` binary on real calldata, which no lake target does):
#
#   selectors — for the whole ERC-20 interface, EVMYulLean's keccak (venom_run's
#               sha3) computes keccak256(signature) >> 224 and must equal the
#               pinned selector. (The pure-Lean keccak it is checked against now
#               lives in-tree as `AbiLean.Hash`, and `AbiCrossval` *proves* the
#               two agree; abi-lean itself no longer ships a hash.)
#   argument  — the pinned calldata's argument region is re-derived by abi-lean's
#               codec (`encode` at `.tuple`); EVMYulLean's venom_run then decodes
#               it (CALLDATALOAD at offset 36) and must return `amount`.
#   dynamic   — abi-lean encodes sum(uint256[]) and mixed(uint256,uint256[])
#               (its dynamic array/tuple roundtrips are now proved, sorry-free);
#               venom_run follows the ABI offset pointer(s) to the length+data
#               region and must return the expected sum, cross-validating the
#               dynamic offset/length/data layout and the head-area (struct) shape.
#
# Usage:   scripts/abi_crossval.sh                     # use pinned references
#
#   Drift-guard modes (re-derive the calldata *argument regions* with abi-lean's
#   codec and check them against the pinned references — the selector, argument
#   level and mapping slot moved in-tree to `EvmYul/Venom/AbiLean/`, so they are
#   covered by `AbiCrossval` instead) — pick ONE source for abi-lean:
#     ABI_LEAN=/path/to/evm-abi-lean scripts/abi_crossval.sh       # local checkout
#     ABI_LEAN_GIT=<url> scripts/abi_crossval.sh                   # clone from git
#         + ABI_LEAN_REF=<branch|tag>   (default: main)
#         + ABI_LEAN_CACHE=<dir>        (default: $XDG_CACHE_HOME/evmyullean/abi-lean)
#
# The drift-guard checkout is built with its own toolchain (elan reads the
# checkout's lean-toolchain), independent of this repo's lake dependency pin —
# so it also catches drift between the pinned rev and abi-lean's moving main.
# First git run materializes abi-lean's lake deps (mathlib et al.); the cache
# dir makes subsequent runs cheap.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"     # EVMYulLean root
EXAMPLES="$HERE/EvmYul/Venom/examples"

# ERC-20 interface: "<signature>|<keccak256(sig)[:4]>".  All-primitive args, so
# abi-lean's (sorry-free) primitive roundtrips cover the whole surface.
ERC20_SELECTORS=(
  "totalSupply()|18160ddd"
  "balanceOf(address)|70a08231"
  "transfer(address,uint256)|a9059cbb"
  "approve(address,uint256)|095ea7b3"
  "allowance(address,address)|dd62ed3e"
  "transferFrom(address,address,uint256)|23b872dd"
  "mint(address,uint256)|40c10f19"
)

# transfer(recipient = 0x…01, amount = 100)
ADDR_WORD="0000000000000000000000000000000000000000000000000000000000000001"
AMT_WORD="0000000000000000000000000000000000000000000000000000000000000064"
CALLDATA="0xa9059cbb${ADDR_WORD}${AMT_WORD}"
# balanceOf[0x…01] Solidity mapping slot at storage slot 0: keccak256(addr32 ++ 0)
SLOT="ada5013122d395ba3c54772283fb069b10426056ef8ca54750cb9bb552a59e7d"

# Dynamic-argument calldata — exercises abi-lean's (now proved, sorry-free)
# dynamic array / tuple roundtrips, which the all-primitive ERC-20 surface above
# does not. Layout: a dynamic argument's ABI head is a 32-byte POINTER (offset
# relative to the args) to a length-prefixed data region.
#   sum(uint256[])           with [10,20,30]        — a bare dynamic array
#   mixed(uint256,uint256[]) with (7,[10,20,30])    — a static field beside a
#                                                     dynamic-field pointer (the
#                                                     head-area / struct shape)
DYNARR_CALLDATA="0x0194db8e00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000001e"
MIXED_CALLDATA="0x89dc1d0f000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000001e"
DYNARR_RET="000000000000000000000000000000000000000000000000000000000000003c"  # sum([10,20,30]) = 60
MIXED_RET="0000000000000000000000000000000000000000000000000000000000000043"   # 7 + 60 = 67

echo "== building venom_run oracle =="
( cd "$HERE" && lake build venom_run )
BIN="$HERE/.lake/build/bin/venom_run"
[ -x "$BIN" ] || { echo "FATAL: venom_run not built at $BIN" >&2; exit 1; }

# EVMYulLean's *own* ABI encoder (Abi.encodeUint256/encodeAddress = the 32-byte
# big-endian word Mem.toBytes32) is the one the bridge lemma is proved over:
#   VenomState.calldataload_transfer_{to,amount} prove CALLDATALOAD inverts it.
# Check its bytes match the pinned words, so the *proved* encoder is tied to the
# same reference abi-lean is checked against (native == pinned == abi-lean).
echo "== EVMYulLean native ABI encoder (proved via the calldataload bridge) =="
( cd "$HERE" && lake build EvmYul.Venom.AbiBridge >/dev/null )
NGEN="$(mktemp -t abi_native.XXXXXX.lean)"
cat > "$NGEN" <<'LEAN'
import EvmYul.Venom.AbiBridge
open EvmYul EvmYul.Venom
def hexWord (bs : List UInt8) : String :=
  String.join (bs.map (fun b =>
    let s := Nat.toDigits 16 b.toNat
    (if s.length == 1 then "0" else "") ++ String.ofList s))
#eval IO.println (hexWord (Abi.encodeAddress (UInt256.ofNat 1)))
#eval IO.println (hexWord (Abi.encodeUint256 (UInt256.ofNat 100)))
LEAN
# keep only the 64-hex-char words, so any (deprecation) diagnostics on the
# lean output stream can't corrupt the line-based parsing below.
NAT_OUT="$( cd "$HERE" && lake env lean "$NGEN" | grep -E '^[0-9a-f]{64}$' )"
rm -f "$NGEN"
echo "  encodeAddress 1   => 0x$(echo "$NAT_OUT" | sed -n 1p)"
echo "  encodeUint256 100 => 0x$(echo "$NAT_OUT" | sed -n 2p)"
echo "$NAT_OUT" | sed -n 1p | grep -qx "$ADDR_WORD" || {
  echo "FATAL: native encodeAddress != pinned ADDR_WORD" >&2; exit 1; }
echo "$NAT_OUT" | sed -n 2p | grep -qx "$AMT_WORD" || {
  echo "FATAL: native encodeUint256 != pinned AMT_WORD" >&2; exit 1; }
echo "  OK: matches pinned words (decode side proved, not just checked)"

# Resolve the abi-lean checkout for the drift guard: an explicit local path
# (ABI_LEAN) wins; otherwise clone/fetch from ABI_LEAN_GIT into a persistent
# cache (built later with its own v4.31.0 toolchain via elan).
if [ -z "${ABI_LEAN:-}" ] && [ -n "${ABI_LEAN_GIT:-}" ]; then
  REF="${ABI_LEAN_REF:-main}"
  CACHE="${ABI_LEAN_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/evmyullean/abi-lean}"
  if [ -d "$CACHE/.git" ]; then
    echo "== update evm-abi-lean cache ($REF) at $CACHE =="
    git -C "$CACHE" fetch --depth 1 origin "$REF"
    git -C "$CACHE" checkout -q --detach FETCH_HEAD
  else
    echo "== clone evm-abi-lean ($ABI_LEAN_GIT @ $REF) into $CACHE =="
    mkdir -p "$(dirname "$CACHE")"
    git clone --depth 1 --branch "$REF" "$ABI_LEAN_GIT" "$CACHE"
  fi
  ABI_LEAN="$CACHE"
fi

# Optional drift guard: re-derive the calldata *argument regions* with the
# abi-lean checkout under test and compare against the pinned references.
#
# Scope note: this checks what abi-lean still owns -- the codec. The 4-byte
# selector, the function-argument level and the keccak mapping slot moved into
# THIS repo (EvmYul/Venom/AbiLean/{Hash,Args,CodecEval}), because a hash is a
# separate primitive from the codec and `encodeArgs` is definitionally the tuple
# level. Those are covered in-build by `AbiCrossval` (proved, not merely checked)
# and by the venom_run selector pass below, so the snippet here uses upstream API
# only -- the specification codec at `.tuple` -- and therefore runs against any
# abi-lean rev that still has it. That is the point: built with the checkout's
# own toolchain, it catches drift between this repo's pinned rev and abi-lean's
# moving main.
#
# `Spec.encode`/`Spec.decodeStrict`, not the unsuffixed pair: since the codec
# grew a runtime layer, `encode`/`decode` are the `ValBA`/`ByteArray` ones and
# the `List UInt8` API this harness compares against lives in `EvmAbi.Spec`.
if [ -n "${ABI_LEAN:-}" ]; then
  echo "== re-derive argument regions via evm-abi-lean ($ABI_LEAN) =="
  [ -d "$ABI_LEAN" ] || { echo "FATAL: ABI_LEAN dir not found: $ABI_LEAN" >&2; exit 1; }
  GEN="$(mktemp -t abi_calldata.XXXXXX.lean)"
  trap 'rm -f "$GEN"' EXIT
  cat > "$GEN" <<'LEAN'
import EvmAbi.Codec
import EvmAbi.Codec.Strict
open EvmAbi

def u256 : Ty := .uint 256
def u (n : Nat) (h : n < 2 ^ 256 := by decide) : Ty.Val u256 := ⟨n, h⟩
def recipient : Ty.Val .address := ⟨1, by decide⟩

-- Since C4 ("bounds are intrinsic to decoding") an array value is a subtype
-- carrying its own `< 2 ^ 256` length proof, not a bare `List`.
def arr (vs : List (Ty.Val u256)) (h : vs.length < 2 ^ 256 := by decide) :
    Ty.Val (.array u256) := ⟨vs, h⟩

def hexBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := Nat.toDigits 16 b.toNat
    (if s.length == 1 then "0" else "") ++ String.ofList s)

-- An argument list is exactly the tuple of its types, so the argument region is
-- `encode (.tuple ts)` -- no argument-level wrapper needed from the library.
#eval IO.println ("ARGS "   ++ hexBytes (Spec.encode (.tuple [.address, u256]) (recipient, u 100, ⟨⟩)))
#eval IO.println ("DYNARR " ++ hexBytes (Spec.encode (.tuple [.array u256]) (arr [u 10, u 20, u 30], ⟨⟩)))
#eval IO.println ("MIXED "  ++ hexBytes (Spec.encode (.tuple [u256, .array u256]) (u 7, arr [u 10, u 20, u 30], ⟨⟩)))

-- Roundtrip drift guard: encode -> decode -> re-encode is a byte fixpoint.
#eval do
  let t : Ty := .tuple [.address, u256]
  let v : Ty.Val t := (recipient, u 100, ⟨⟩)
  let args := Spec.encode t v
  -- calldata is a whole buffer, so the strict decoder is the right one here
  match Spec.decodeStrict t args with
  | some v' => if Spec.encode t v' == args then IO.println "ROUNDTRIP OK"
               else IO.eprintln "roundtrip re-encode mismatch"
  | none    => IO.eprintln "roundtrip decode failed"
LEAN
  ( cd "$ABI_LEAN" && lake build EvmAbi.Codec EvmAbi.Codec.Strict >/dev/null )
  ABI_OUT="$( cd "$ABI_LEAN" && lake env lean "$GEN" )"
  # The pinned references carry a 4-byte selector prefix ("0x" + 8 hex chars);
  # the library re-derives only the argument region, so compare the suffix.
  for pair in "ARGS|${CALLDATA}" "DYNARR|${DYNARR_CALLDATA}" "MIXED|${MIXED_CALLDATA}"; do
    tag="${pair%%|*}"; ref="${pair#*|}"
    echo "$ABI_OUT" | grep -qF "${tag} ${ref:10}" || {
      echo "FATAL: abi-lean ${tag} argument region drifted from pinned reference" >&2
      echo "  expected suffix: ${ref:10}" >&2; echo "$ABI_OUT" >&2; exit 1; }
  done
  echo "$ABI_OUT" | grep -qF "ROUNDTRIP OK" || {
    echo "FATAL: abi-lean encode->decode->re-encode roundtrip drifted" >&2; exit 1; }
  echo "  OK: abi-lean argument regions (static + dynamic array + mixed) + roundtrip match pinned references"
fi

echo "== selectors: EVMYulLean keccak(sig)>>224 vs pinned =="
for entry in "${ERC20_SELECTORS[@]}"; do
  sig="${entry%|*}"; want="${entry#*|}"
  hex="0x$(printf '%s' "$sig" | xxd -p | tr -d '\n')"
  word="$(printf '%064s' "$want" | tr ' ' 0)"
  out="$(printf '{"calldata":"%s"}' "$hex" | "$BIN" "$EXAMPLES/abi_selector.venom")"
  echo "$out" | grep -q "\"return\":\"0x${word}\"" || {
    echo "FATAL: venom_run selector for $sig != 0x$want" >&2; echo "  $out" >&2; exit 1; }
  printf '  %-40s %s  OK\n' "$sig" "$want"
done

echo "== argument: decode abi-lean transfer calldata via venom_run =="
ARG_OUT="$(printf '{"calldata":"%s"}' "$CALLDATA" | "$BIN" "$EXAMPLES/abi_echo.venom")"
echo "  venom_run => $ARG_OUT"
echo "$ARG_OUT" | grep -q "\"return\":\"0x${AMT_WORD}\"" || {
  echo "FATAL: venom_run did not return the encoded amount (0x…64)" >&2
  exit 1
}

echo "== execute: balanceOf[addr]=amount from abi-lean calldata via venom_run =="
EXE_OUT="$(printf '{"calldata":"%s"}' "$CALLDATA" | "$BIN" "$EXAMPLES/abi_balance.venom")"
echo "  venom_run => $EXE_OUT"
# storage[keccak(addr‖0)] must hold the decoded amount (0x64) and the run returns it
echo "$EXE_OUT" | grep -qF "[\"0x${SLOT}\",\"0x64\"]" || {
  echo "FATAL: venom_run did not store the amount at balanceOf[addr] (slot 0x${SLOT})" >&2
  exit 1
}
echo "$EXE_OUT" | grep -q "\"return\":\"0x${AMT_WORD}\"" || {
  echo "FATAL: venom_run did not return the stored balance" >&2
  exit 1
}

echo "== dynamic array: decode abi-lean sum(uint256[]) calldata via venom_run =="
# abi_dynarray.venom follows the ABI offset pointer at calldata[4] to the array's
# length+data region and returns the sum of the 3 elements (60 = 0x3c).
DA_OUT="$(printf '{"calldata":"%s"}' "$DYNARR_CALLDATA" | "$BIN" "$EXAMPLES/abi_dynarray.venom")"
echo "  venom_run => $DA_OUT"
echo "$DA_OUT" | grep -q "\"return\":\"0x${DYNARR_RET}\"" || {
  echo "FATAL: venom_run did not return sum([10,20,30]) = 0x…3c (dynamic-array layout)" >&2
  exit 1
}

echo "== mixed static+dynamic: decode abi-lean mixed(uint256,uint256[]) calldata via venom_run =="
# abi_dynstruct.venom reads the inline static field AND follows the dynamic-field
# pointer (the head-area / struct shape), returning x + sum(arr) (67 = 0x43).
MX_OUT="$(printf '{"calldata":"%s"}' "$MIXED_CALLDATA" | "$BIN" "$EXAMPLES/abi_dynstruct.venom")"
echo "  venom_run => $MX_OUT"
echo "$MX_OUT" | grep -q "\"return\":\"0x${MIXED_RET}\"" || {
  echo "FATAL: venom_run did not return x+sum = 0x…43 (mixed head-area layout)" >&2
  exit 1
}

echo "== OK: abi-lean and EVMYulLean agree on selectors + arguments (primitive + dynamic array + mixed) + stateful execution =="

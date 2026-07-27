#!/usr/bin/env bash
#
# One-shot reproducible runner for the Venom differential test suite:
#
#   Lean `venom_run` oracle  vs  titanoboa (a production EVM)  on real
#   `vyper --experimental-codegen` output.
#
# Builds the `venom_run` oracle, points the pydefi tests at it, and runs the
# whole differential suite (storage-slot keccak derivation + the memory ops
# calldatacopy/mcopy/mload/mstore/sha3 + the corpus sweep).
#
# Usage:   scripts/venom_differential.sh            # build + run everything
#          PYDEFI=/path/to/pydefi scripts/venom_differential.sh
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"     # EVMYulLean root
PYDEFI="${PYDEFI:-$(cd "$HERE/../pydefi" && pwd)}"
VENV_PY="$PYDEFI/.venv/bin/python"

echo "== building venom_run oracle =="
( cd "$HERE" && lake build venom_run )
BIN="$HERE/.lake/build/bin/venom_run"
[ -x "$BIN" ] || { echo "FATAL: venom_run not built at $BIN" >&2; exit 1; }

echo "== sanity: run the balance examples =="
for ex in balance_orig balance_opt; do
  out="$("$BIN" "$HERE/EvmYul/Venom/examples/$ex.venom" < /dev/null)"
  echo "  $ex => $out"
  echo "$out" | grep -q '"return":"0x.*63"' || { echo "FATAL: $ex did not RETURN 99" >&2; exit 1; }
done

echo "== differential suite (Lean venom_run vs titanoboa) =="
[ -x "$VENV_PY" ] || { echo "FATAL: pydefi venv not found at $VENV_PY" >&2; exit 1; }
cd "$PYDEFI"
VENOM_RUN_BIN="$BIN" "$VENV_PY" -m pytest \
  tests/test_venom_lean_differential.py \
  tests/test_venom_memory_differential.py \
  tests/test_venom_corpus_sweep.py \
  -q "$@"

echo "== OK: venom differential suite green =="

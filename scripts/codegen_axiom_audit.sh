#!/usr/bin/env bash
#
# Machine-checked trust-boundary guard for the Venom -> EVM CODEGEN stack.
#
# `scripts/axiom_audit.sh` covers the M1-M7 Venom/optimizer results; it has no `Hol` import,
# so the ~124 `codegen_correct` results were outside the guard. This closes that hole.
#
# Asserts, over every result in EvmYul/Venom/Hol/CodegenAudit.lean:
#   * none depends on `sorry` (sorryAx) or `Lean.ofReduceBool` (i.e. `native_decide`), and
#   * every axiom is standard [propext, Classical.choice, Quot.sound] or the isolated
#     M1 FFI pair (ffi_zeroes_size / ffi_zeroes_get), which the capstones legitimately
#     inherit through memoryRel / readWithPadding.
#
# Exit non-zero (CI-friendly) on any surprise. Usage: scripts/codegen_axiom_audit.sh
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$HERE"

OUT="$(lake env lean EvmYul/Venom/Hol/CodegenAudit.lean 2>&1)"

# Collapse each wrapped `'name' depends on axioms: [ ... ]` record onto one line.
NORM="$(echo "$OUT" | awk '
  /depends on axioms:/ { buf=$0; c=1; if ($0 ~ /]/){ print buf; c=0; buf="" }; next }
  c                    { buf=buf " " $0; if ($0 ~ /]/){ print buf; c=0; buf="" } }
')"

TOTAL="$(echo "$NORM" | grep -c 'depends on axioms:' || true)"
if [ "$TOTAL" -eq 0 ]; then
  echo "FAIL: no results audited — did CodegenAudit.lean fail to elaborate?" >&2
  echo "$OUT" | tail -20 >&2; exit 1
fi

if echo "$OUT" | grep -q 'sorryAx'; then
  echo "FAIL: a codegen result depends on sorryAx (a hole)." >&2
  echo "$NORM" | grep 'sorryAx' >&2; exit 1
fi
if echo "$OUT" | grep -q 'ofReduceBool'; then
  echo "FAIL: a codegen result depends on Lean.ofReduceBool (native_decide)." >&2
  echo "$NORM" | grep 'ofReduceBool' >&2; exit 1
fi

# `#print axioms` renders the FFI pair as `EvmYul.M1.…`, `M1.…`, or bare, depending on the
# ambient `open`; allow all three spellings.
ALLOW='propext|Classical\.choice|Quot\.sound|(EvmYul\.)?(M1\.)?ffi_zeroes_size|(EvmYul\.)?(M1\.)?ffi_zeroes_get'
BAD="$(echo "$NORM" | grep -oE 'axioms: \[[^]]*\]' | grep -oE '[A-Za-z][A-Za-z0-9._]*' \
       | grep -vxE "axioms|$ALLOW" | sort -u || true)"
if [ -n "$BAD" ]; then
  echo "FAIL: unexpected axiom(s) in the codegen trust boundary:" >&2
  echo "$BAD" >&2; exit 1
fi

BASE_ONLY="$(echo "$NORM" | grep -c -v 'ffi_zeroes' || true)"
WITH_FFI="$(echo "$NORM" | grep -c 'ffi_zeroes' || true)"
echo "----------------------------------------------------------------------"
echo "CODEGEN AXIOM REPORT — $TOTAL codegen_correct results audited"
echo "  standard axioms only:                        $BASE_ONLY"
echo "  + the isolated M1 FFI pair (memory-touching): $WITH_FFI"
echo "  depend on sorry / native_decide:              0"
echo "----------------------------------------------------------------------"
echo "OK: codegen trust boundary intact — standard axioms everywhere, the M1 FFI"
echo "    pair only, 0 sorry, 0 native_decide."

#!/usr/bin/env bash
#
# Machine-checked trust-boundary guard for the Venom development.
#
# Runs EvmYul/Venom/Audit.lean (which #print axioms every headline result) and
# asserts the boundary has not drifted:
#   * no result depends on `sorry` (sorryAx), and
#   * the only axioms are Lean's standard [propext, Classical.choice, Quot.sound]
#     plus the two isolated M1 FFI axioms (ffi_zeroes_size / ffi_zeroes_get),
#     and the FFI axioms appear on the M1 results ONLY.
#
# Exit non-zero (CI-friendly) on any surprise. Usage: scripts/axiom_audit.sh
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$HERE"

OUT="$(lake env lean EvmYul/Venom/Audit.lean 2>&1)"
echo "$OUT"
echo "----------------------------------------------------------------------"

# Normalize: `#print axioms` wraps long axiom lists across lines. Collapse each
# `'name' depends on axioms: [ ... ]` record onto a single line so the per-result
# checks below are robust to wrapping.
NORM="$(echo "$OUT" | awk '
  /depends on axioms:/ { buf=$0; collecting=1; if ($0 ~ /]/){ print buf; collecting=0; buf="" }; next }
  collecting         { buf=buf " " $0; if ($0 ~ /]/){ print buf; collecting=0; buf="" } }
')"

# 1. no sorry
if echo "$OUT" | grep -q 'sorryAx'; then
  echo "FAIL: a result depends on sorryAx (a hole)." >&2; exit 1
fi

# 2. no axiom outside the allowlist
ALLOW='propext|Classical\.choice|Quot\.sound|EvmYul\.M1\.ffi_zeroes_size|EvmYul\.M1\.ffi_zeroes_get'
BAD="$(echo "$NORM" \
  | grep -oE 'axioms: \[[^]]*\]' \
  | grep -oE '[A-Za-z][A-Za-z0-9._]*' \
  | grep -vxE "axioms|$ALLOW" | sort -u || true)"
if [ -n "$BAD" ]; then
  echo "FAIL: unexpected axiom(s) in the trust boundary:" >&2
  echo "$BAD" >&2; exit 1
fi

# 3. the FFI axioms must stay isolated to the M1 results and the machine-memory
#    bridge results that legitimately build on the M1 zero-padding (the proved
#    read half: readWithPadding_toList / load_agrees_discharged and the machine
#    read-after-write / no-aliasing that go through it).
M1_OK="zeroes_(size_nat|get_zero)|readWithPadding_toList|load_agrees_discharged|store_refines_discharged|toByteArray_toList_eq_toBytes32|machine_load_store_(self|disjoint)|machineStore_size_ge|lookupMemory_writeWord_(self|frame)|sim_spill(_reload|_active|_full)?"
if echo "$NORM" | grep 'ffi_zeroes' | grep -vqE "($M1_OK)' depends"; then
  echo "FAIL: an M1 FFI axiom leaked outside the M1 / machine-memory results." >&2; exit 1
fi

# --- the clear axiom report (categorise every audited result) ----------------
AXTMP="$(mktemp)"; trap 'rm -f "$AXTMP"' EXIT
printf '%s' "$OUT" > "$AXTMP"
python3 - "$AXTMP" <<'PY'
import sys, re
text = re.sub(r"\s+", " ", open(sys.argv[1]).read())
recs = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
# axiom-free results (the strongest rigor — not even propext) print differently.
free = re.findall(r"'([^']+)' does not depend on any axioms", text)
STD = {"propext", "Classical.choice", "Quot.sound"}
M1  = {"EvmYul.M1.ffi_zeroes_size", "EvmYul.M1.ffi_zeroes_get"}
rig, m1, srr, oth = [], [], [], []
for name in free:
    rig.append(name.replace("EvmYul.Venom.", "").replace("EvmYul.", ""))
nfree = len(rig)
for name, ax in recs:
    s = {a.strip() for a in ax.split(",") if a.strip()}
    short = name.replace("EvmYul.Venom.", "").replace("EvmYul.", "")
    if "sorryAx" in s: srr.append(short)
    elif s <= STD:     rig.append(short)
    elif s <= STD | M1: m1.append(short)
    else:              oth.append((short, sorted(s)))
print(f"AXIOM REPORT — {len(recs) + len(free)} headline results audited")
print(f"  fully rigorous (standard axioms only; incl. {nfree} axiom-free):              {len(rig)}")
print(f"  + the isolated M1 FFI axioms ONLY (memset_zero: ffi_zeroes_size/get):        {len(m1)}")
print(f"  depend on sorry (a hole):                                                    {len(srr)}")
if oth:
    print(f"  !! UNEXPECTED footprints: {oth}")
print()
print("  the M1 FFI axioms appear on exactly these results — the whole trust boundary:")
for n in m1:
    print(f"    - {n}")
print()
print("  Contingent results carry their interface as a HYPOTHESIS (a Prop argument in")
print("  the signature), NOT an axiom — discharging it removes the contingency:")
print("    VenomBalEquivRel, Realizes, EvmStorageRel, RBMapEraseSpec, Solvent, DJAuxSpec.")
PY
echo "----------------------------------------------------------------------"
echo "OK: trust boundary intact — standard axioms everywhere, ffi_zeroes_{size,get}"
echo "    isolated to the M1 / machine-memory results, 0 sorry."

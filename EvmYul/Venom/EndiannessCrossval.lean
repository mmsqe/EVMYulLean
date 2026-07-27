/-
Endianness cross-validation: lean-endianness vs EVMYulLean, in-build.

EVMYulLean hand-rolls its byte-order codecs — `fromBytes'`/`fromBytesBigEndian`
(the 46-use-site decoder under every word read), `encodeNumBytes` (the PUSH-literal
encoder, 91 use sites, which every codegen layout fact rests on) and `Mem.toBytes32`
(the 32-byte EVM-word encoder behind `Abi.encodeUint256`). lean-endianness
(github.com/yihuang/lean-endianness, pinned in the lakefile) is an independently
written, mathlib-free codec library with machine-checked roundtrips.

This file proves the two agree — as ∀-theorems, not samples:

* `fromBytes'_eq_decodeLEU` / `fromBytesBigEndian_eq_decodeBEU` — the decoders are
  extensionally equal.
* `decodeBEU_encodeNumBytes` — the PUSH-literal encoder round-trips through the
  EXTERNAL verified decoder: `decodeBEU (encodeNumBytes n) = n`.
* `encodeNumBytes_eq_encodeBEMinU` — STRONGER than that roundtrip: the PUSH-literal
  encoder IS the verified minimal-length codec, `encodeNumBytes n = encodeBEMinU n`,
  as a list equality rather than an agreement on decoded values. Holds for `n ≠ 0`;
  `encodeNumBytes_zero` records the sole divergence, `[]` here versus `[0x00]` there
  (that codec encodes zero as one byte, per the EVM word convention).
* `toBytes32_eq_encodeBEU` — the EVM-word encoder IS the verified fixed-width codec:
  `Mem.toBytes32 v = Binary.encodeBEU 32 v.toNat` (via `encodeBEU_decodeBEU`
  injectivity + the in-tree `fromBytesBigEndian_toBytes32` roundtrip).

No `native_decide`, no FFI axiom; the axiom footprint is
[propext, Classical.choice, Quot.sound].

⚠️ Toolchain note: lean-endianness declares lean4:v4.32.0 but compiles clean under
this project's v4.31.0 (verified). `lake update` SILENTLY BUMPS the root
lean-toolchain to a dependency's newer one — if you re-run `lake update`, check
`git diff lean-toolchain` afterwards.
-/
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.VenomMemProps
import Binary

set_option maxHeartbeats 1000000

namespace EvmYul.Venom.EndiannessCrossval
open EvmYul EvmYul.Venom EvmYul.Venom.Hol.Codegen

/- The decoder-agreement lemmas (`fromBytes'_eq_decodeLEU`,
`fromBytesBigEndian_eq_decodeBEU`) moved to `EvmYul.Venom.BinaryBridge`, early in
the import graph — `Mem`'s word codec is now *defined* via the library, so the
memory lemma layer needs them. They resolve here unqualified as before. -/

/-- The codegen's PUSH-literal encoder round-trips through lean-endianness' verified
    big-endian decoder. -/
theorem decodeBEU_encodeNumBytes (n : Nat) : Binary.decodeBEU (encodeNumBytes n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold encodeNumBytes
    split
    · subst ‹n = 0›; rfl
    · rename_i hn
      show Binary.decodeBEU (encodeNumBytes (n / 256) ++ [UInt8.ofNat (n % 256)]) = n
      have hsnoc : Binary.decodeBEU (encodeNumBytes (n / 256) ++ [UInt8.ofNat (n % 256)])
          = Binary.decodeBEU (encodeNumBytes (n / 256)) * 256 + (UInt8.ofNat (n % 256)).toNat := by
        simp [Binary.decodeBEU, Binary.uint8ToNats, Binary.decodeBE_snoc]
      rw [hsnoc, ih (n / 256) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega))]
      have hb : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
        UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by omega))
      rw [hb]
      omega

/-- **The EVM-word encoder IS the verified fixed-width codec** — by definition,
    since `Mem.toBytes32` is now backed by it. Kept as the regression guard: if the
    definition ever drifts back to a hand-rolled encoder, this stops being `rfl`
    and must be re-proved, making the divergence loud. -/
theorem toBytes32_eq_encodeBEU (v : UInt256) :
    Mem.toBytes32 v = Binary.encodeBEU 32 v.toNat := rfl

/-! ## The PUSH-literal encoder IS the minimal-length codec

`decodeBEU_encodeNumBytes` says the encoder agrees with the external decoder on the
value it decodes to. That is weaker than it sounds: many encodings decode to the same
value. These pin the BYTES.

The route is the library's minimality spec: `encodeNumBytes`'s width follows the
base-256 recursion, `minBytes` provably follows the same one (`minBytes_div`), so the
two widths coincide — and equal widths plus equal decoded values force equal bytes, by
`encodeBEU_decodeBEU` injectivity. -/

/-- The PUSH-literal encoder's width is the library's minimal width, for `n ≠ 0`. -/
theorem encodeNumBytes_length {n : Nat} (h : n ≠ 0) :
    (encodeNumBytes n).length = Binary.minBytes n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encodeNumBytes, if_neg h]
    rcases Nat.lt_or_ge n 256 with hlt | hge
    · have hz : n / 256 = 0 := by omega
      rw [hz]
      simp [encodeNumBytes, Binary.minBytes_eq_one hlt]
    · have hd : n / 256 ≠ 0 := by
        have : 0 < n / 256 := Nat.div_pos hge (by omega)
        omega
      rw [List.length_append, ih (n / 256) (by omega) hd, Binary.minBytes_div hge]
      simp

/-- **The PUSH-literal encoder IS the verified minimal-length codec**, byte for byte
    (`n ≠ 0`). Every codegen layout fact rests on this encoder; this says it is not
    merely value-compatible with an independently written codec, but identical to it. -/
theorem encodeNumBytes_eq_encodeBEMinU {n : Nat} (h : n ≠ 0) :
    encodeNumBytes n = Binary.encodeBEMinU n := by
  calc encodeNumBytes n
      = Binary.encodeBEU (encodeNumBytes n).length
          (Binary.decodeBEU (encodeNumBytes n)) := (Binary.encodeBEU_decodeBEU _).symm
    _ = Binary.encodeBEU (Binary.minBytes n) n := by
        rw [encodeNumBytes_length h, decodeBEU_encodeNumBytes n]
    _ = Binary.encodeBEMinU n := rfl

/-- The sole divergence, recorded rather than hidden: this encoder emits nothing for
    `0`, where the library's codec emits one zero byte (`encodeBEMinU 0 = [0x00]`).
    That is why `encodeNumBytes_eq_encodeBEMinU` is hypothesised on `n ≠ 0`. -/
theorem encodeNumBytes_zero : encodeNumBytes 0 = [] := by rw [encodeNumBytes]; simp

end EvmYul.Venom.EndiannessCrossval

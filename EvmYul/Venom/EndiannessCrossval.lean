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
* `toSigned_eq_twosRep` / `fromSigned_eq_ofTwosNat` — the signed word, both ways:
  what SDIV, SMOD and SIGNEXTEND produce and read is `Binary.twosRep` /
  `Binary.ofTwosNat`.  Unconditionally, out of range included, where the two
  constructions diverge in form but not in value.  The decoding direction needs
  `xor_two_pow_sub_one`, complement-is-subtraction, which Mathlib does not have
  and which is proved here through `BitVec.toNat_not`.

No `native_decide`, no FFI axiom; the axiom footprint is
[propext, Classical.choice, Quot.sound].

⚠️ `lake update` SILENTLY BUMPS the root lean-toolchain to a dependency's newer
one — if you re-run it, check `git diff lean-toolchain` afterwards.  (Both this
project and lean-endianness are on v4.32.0, so there is no skew to absorb today.)
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

/-! ## the signed word, cross-validated

`toSigned` is what SDIV, SMOD and the other signed opcodes produce: an EVM word
from a mathematical integer, two's complement, hand-rolled here as a match on
`Int`'s constructors.  `Binary.twosRep` is the library's version of the same
map, and the two agree.

Unconditionally, which is the interesting part: out of range the constructions
diverge in *form* but not in value, `toSigned` truncating `size - 1 - n` to `0`
where `twosRep` takes `.toNat` of a negative and gets `0` too.  So no
`InTwosRange` hypothesis is needed. -/

/-- Stated over an abstract `S` so `omega` never meets `UInt256.size`'s
    seventy-eight-digit literal. -/
private theorem toNat_add_negSucc (S n : ℕ) :
    ((S : ℤ) + Int.negSucc n).toNat = S - 1 - n := by omega

/-- Bitwise complement within `n` bits is subtraction from all-ones.  Mathlib
    has neither this nor the `testBit` rule for a truncated subtraction that the
    direct proof would need; `BitVec.toNat_not` states exactly it, so the proof
    goes through `BitVec` and comes back. -/
theorem xor_two_pow_sub_one {n u : ℕ} (h : u < 2 ^ n) :
    Nat.xor (2 ^ n - 1) u = 2 ^ n - 1 - u := by
  have hu : (BitVec.ofNat n u).toNat = u := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  calc Nat.xor (2 ^ n - 1) u
      = (BitVec.allOnes n).toNat ^^^ (BitVec.ofNat n u).toNat := by
        rw [BitVec.toNat_allOnes, hu]; rfl
    _ = (BitVec.allOnes n ^^^ BitVec.ofNat n u).toNat := by rw [BitVec.toNat_xor]
    _ = (~~~ BitVec.ofNat n u).toNat := by rw [BitVec.allOnes_xor]
    _ = 2 ^ n - 1 - u := by rw [BitVec.toNat_not, hu]

/-- Stated over an abstract `S`, as `toNat_add_negSucc` is and for the same
    reason. -/
private theorem neg_complement_cast {S u : ℕ} (h : u < S) :
    -((S - 1 - u : ℕ) : ℤ) - 1 = (u : ℤ) - (S : ℤ) := by omega

/-- **The decoding direction**: EVMYulLean reads a signed word by complementing
    with `xor`, the library by subtracting the modulus.  Same function. -/
theorem fromSigned_eq_ofTwosNat (a : UInt256) :
    UInt256.fromSigned a = Binary.ofTwosNat 32 a.toNat := by
  have hsize : (256 ^ 32 : ℕ) = 2 ^ 256 := by rfl
  have hsz : UInt256.size = 2 ^ 256 := by rfl
  have hlt : a.toNat < 2 ^ 256 := lt_of_lt_of_eq a.val.isLt hsz
  by_cases h : a.toNat < 2 ^ 255
  · have h2 : 2 * a.toNat < 256 ^ 32 := by rw [hsize]; omega
    rw [UInt256.fromSigned, if_pos h, Binary.ofTwosNat, if_pos h2]
    rfl
  · have h2 : ¬ (2 * a.toNat < 256 ^ 32) := by rw [hsize]; omega
    -- `↑a.val` must go before `hsz`: `a.val : Fin UInt256.size` mentions the
    -- very constant being rewritten, so the motive is otherwise ill-typed.
    rw [UInt256.fromSigned, if_neg h, Binary.ofTwosNat, if_neg h2, hsize,
      show ((a.val : ℕ)) = a.toNat from rfl, hsz, xor_two_pow_sub_one hlt,
      neg_complement_cast hlt]

theorem toSigned_eq_twosRep (i : ℤ) :
    UInt256.toSigned i = UInt256.ofNat (Binary.twosRep 32 i) := by
  have hsize : (256 ^ 32 : ℕ) = UInt256.size := by rfl
  cases i with
  | ofNat n => simp [UInt256.toSigned, Binary.twosRep]
  | negSucc n =>
      simp only [UInt256.toSigned, Binary.twosRep, hsize, Int.negSucc_not_nonneg,
        if_false, toNat_add_negSucc]

end EvmYul.Venom.EndiannessCrossval

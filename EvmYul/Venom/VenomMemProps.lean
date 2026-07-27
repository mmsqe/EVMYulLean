import EvmYul.Venom.Memory
import EvmYul.Venom.BinaryBridge

/-!
# Venom IR — memory model properties

Equational lemmas about the `List`-based `Mem` model
(`EvmYul/Venom/Memory.lean`). The point of the list representation is that
these *reduce* and are provable, unlike the `ByteArray` ops in
`EvmYul.MachineState`. The headline result is `readBytes_writeBytes_self`
(read back exactly what you wrote), which is what lets a Venom proof
characterize a keccak preimage instead of assuming it.

All proofs are closed (no `sorry`); the only axioms used are Lean's
standard `propext`/`Classical.choice`/`Quot.sound`.
-/

-- These two helpers are most cleanly proved by `simpa using ih`; the
-- `unnecessarySimpa` linter would rather we inline, but the `using` form
-- is the clearest here.
set_option linter.unnecessarySimpa false

namespace EvmYul.Venom
namespace Mem

/-! ## Generic `take`/`drop` over append

Proved by induction so we do not depend on the exact spelling of the
corresponding `List` lemmas (which has drifted across toolchains). -/

variable {α : Type}

/-- `(l₁ ++ l₂).take l₁.length = l₁`. -/
theorem take_length_append (l₁ l₂ : List α) :
    (l₁ ++ l₂).take l₁.length = l₁ := by
  induction l₁ with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
theorem drop_length_append (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- `take` of an append at an index equal to the left length. -/
theorem take_append_length_eq (l₁ l₂ : List α) (n : Nat) (h : n = l₁.length) :
    (l₁ ++ l₂).take n = l₁ := by
  subst h; exact take_length_append l₁ l₂

/-- `drop` of an append at an index equal to the left length. -/
theorem drop_append_length_eq (l₁ l₂ : List α) (n : Nat) (h : n = l₁.length) :
    (l₁ ++ l₂).drop n = l₂ := by
  subst h; exact drop_length_append l₁ l₂

/-! ## `expand` -/

/-- Expansion sets the length to `max` of the old length and the target. -/
@[simp] theorem expand_length (mem : Mem) (len : Nat) :
    (mem.expand len).length = max mem.length len := by
  unfold Mem.expand
  rw [List.length_append, List.length_replicate]
  omega

/-- The target length is reached. -/
theorem le_expand_length (mem : Mem) (len : Nat) :
    len ≤ (mem.expand len).length := by
  rw [expand_length]; omega

/-- Expanding to a length already covered is a no-op. -/
theorem expand_of_length_le (mem : Mem) (len : Nat) (h : len ≤ mem.length) :
    mem.expand len = mem := by
  unfold Mem.expand
  rw [Nat.sub_eq_zero_of_le h, List.replicate_zero, List.append_nil]

/-! ## `writeBytes` -/

/-- Writing `bytes` at `offset` extends the length to cover the written
window (or leaves it, if memory already reached past it). -/
@[simp] theorem writeBytes_length (mem : Mem) (offset : Nat) (bytes : Mem) :
    (mem.writeBytes offset bytes).length
      = max mem.length (offset + bytes.length) := by
  have he := expand_length mem (offset + bytes.length)
  simp only [Mem.writeBytes, List.length_append, List.length_take, List.length_drop]
  omega

/-- `writeBytes` unfolded to its splice over the on-demand-expanded
memory (definitional; lets us rewrite away the `let`). -/
theorem writeBytes_eq (mem : Mem) (offset : Nat) (bytes : Mem) :
    mem.writeBytes offset bytes
      = (mem.expand (offset + bytes.length)).take offset ++ bytes
        ++ (mem.expand (offset + bytes.length)).drop (offset + bytes.length) := rfl

/-- When the region already fits, `writeBytes` does not expand and is just
a splice over the existing bytes. -/
theorem writeBytes_of_length_le (mem : Mem) (offset : Nat) (bytes : Mem)
    (h : offset + bytes.length ≤ mem.length) :
    mem.writeBytes offset bytes
      = mem.take offset ++ bytes ++ mem.drop (offset + bytes.length) := by
  rw [writeBytes_eq, expand_of_length_le mem (offset + bytes.length) h]

/-! ## Read-after-write

The fundamental correctness property: reading the window you just wrote
returns exactly the bytes written. -/

theorem readBytes_writeBytes_self (mem : Mem) (offset : Nat) (bytes : Mem) :
    (mem.writeBytes offset bytes).readBytes offset bytes.length = bytes := by
  have hWlen : (mem.writeBytes offset bytes).length
      = max mem.length (offset + bytes.length) := writeBytes_length mem offset bytes
  have hElen : (mem.expand (offset + bytes.length)).length
      = max mem.length (offset + bytes.length) := expand_length mem (offset + bytes.length)
  -- the outer read does not need to expand again
  simp only [Mem.readBytes,
    expand_of_length_le (mem.writeBytes offset bytes) (offset + bytes.length)
      (by rw [hWlen]; omega)]
  -- now: ((writeBytes …).drop offset).take bytes.length = bytes
  have hTakeLen :
      ((mem.expand (offset + bytes.length)).take offset).length = offset := by
    rw [List.length_take]; omega
  simp only [Mem.writeBytes, List.append_assoc]
  rw [drop_append_length_eq _ _ offset hTakeLen.symm,
      take_append_length_eq bytes _ bytes.length rfl]

/-! ## Overwrite

Writing a region twice (same offset, same width) keeps only the second
write — the "double write, second won't expand" shape. -/

theorem writeBytes_overwrite (mem : Mem) (offset : Nat) (b₁ b₂ : Mem)
    (hlen : b₁.length = b₂.length) :
    (mem.writeBytes offset b₁).writeBytes offset b₂ = mem.writeBytes offset b₂ := by
  -- `E` is `mem` expanded to the (common) written width.
  set E := mem.expand (offset + b₁.length) with hEdef
  have hElen : E.length = max mem.length (offset + b₁.length) := by
    rw [hEdef]; exact expand_length mem (offset + b₁.length)
  have hTakeLen : (E.take offset).length = offset := by
    rw [List.length_take, hElen]; omega
  have hTake2Len : (E.take offset ++ b₁).length = offset + b₁.length := by
    rw [List.length_append, hTakeLen]
  -- The two single writes, as explicit splices over `E`.
  have hW1 : mem.writeBytes offset b₁ = E.take offset ++ b₁ ++ E.drop (offset + b₁.length) := by
    rw [writeBytes_eq mem offset b₁, ← hEdef]
  have hW2 : mem.writeBytes offset b₂ = E.take offset ++ b₂ ++ E.drop (offset + b₁.length) := by
    rw [writeBytes_eq mem offset b₂, show offset + b₂.length = offset + b₁.length from by omega,
        ← hEdef]
  -- The outer write does not expand: `W₁` already reaches past `offset + b₂.length`.
  have hW1len : (mem.writeBytes offset b₁).length = max mem.length (offset + b₁.length) :=
    writeBytes_length mem offset b₁
  rw [writeBytes_of_length_le (mem.writeBytes offset b₁) offset b₂ (by rw [hW1len]; omega)]
  -- Rewrite `W₁` to its splice form and the drop index to the common width.
  rw [hW1, show offset + b₂.length = offset + b₁.length from by omega]
  -- `(E.take offset ++ b₁ ++ E.drop d).take offset = E.take offset`
  have hTakePart :
      (E.take offset ++ b₁ ++ E.drop (offset + b₁.length)).take offset = E.take offset := by
    rw [List.append_assoc, take_append_length_eq _ _ offset hTakeLen.symm]
  -- `(E.take offset ++ b₁ ++ E.drop d).drop d = E.drop d`
  have hDropPart :
      (E.take offset ++ b₁ ++ E.drop (offset + b₁.length)).drop (offset + b₁.length)
        = E.drop (offset + b₁.length) :=
    drop_append_length_eq (E.take offset ++ b₁) (E.drop (offset + b₁.length))
      (offset + b₁.length) hTake2Len.symm
  rw [hTakePart, hDropPart, hW2]

/-! ## Two adjacent writes — the keccak-preimage shape

`mstore 0 b₁; mstore b₁.length b₂; read [0, b₁.length + b₂.length)` returns
`b₁ ++ b₂`. This is exactly the Venom balance-slot keccak preimage
(`mstore 0x00 slot; mstore 0x20 addr; keccak256 0x00 0x40`), so it lets a
proof *compute* the preimage instead of assuming it. -/

theorem readBytes_two_writes (mem : Mem) (b₁ b₂ : Mem) :
    ((mem.writeBytes 0 b₁).writeBytes b₁.length b₂).readBytes 0 (b₁.length + b₂.length)
      = b₁ ++ b₂ := by
  -- `W₁` is `b₁` followed by whatever was past it.
  have hW1 : mem.writeBytes 0 b₁ = b₁ ++ (mem.expand b₁.length).drop b₁.length := by
    rw [writeBytes_eq mem 0 b₁, Nat.zero_add, List.take_zero, List.nil_append]
  have hW1len : (mem.writeBytes 0 b₁).length = max mem.length b₁.length := by
    rw [writeBytes_length mem 0 b₁, Nat.zero_add]
  -- `E₂` = `W₁` expanded to the full window; its first `b₁.length` bytes are `b₁`.
  set E₂ := (mem.writeBytes 0 b₁).expand (b₁.length + b₂.length) with hE2def
  have hE2 : E₂ = b₁ ++ ((mem.expand b₁.length).drop b₁.length
      ++ List.replicate (b₁.length + b₂.length - (mem.writeBytes 0 b₁).length) 0) := by
    rw [hE2def, Mem.expand, hW1, List.append_assoc]
  have hE2take : E₂.take b₁.length = b₁ := by
    rw [hE2, take_length_append]
  -- `W₂` as an explicit splice; the leading `E₂.take b₁.length` collapses to `b₁`.
  have hW2 : (mem.writeBytes 0 b₁).writeBytes b₁.length b₂
      = (b₁ ++ b₂) ++ E₂.drop (b₁.length + b₂.length) := by
    rw [writeBytes_eq (mem.writeBytes 0 b₁) b₁.length b₂, ← hE2def, hE2take]
  have hW2len : ((mem.writeBytes 0 b₁).writeBytes b₁.length b₂).length
      = max (max mem.length b₁.length) (b₁.length + b₂.length) := by
    rw [writeBytes_length (mem.writeBytes 0 b₁) b₁.length b₂, hW1len]
  -- Read the full window: no re-expansion, and the prefix is `b₁ ++ b₂`.
  simp only [Mem.readBytes, Nat.zero_add, List.drop_zero]
  rw [expand_of_length_le _ _ (by rw [hW2len]; omega), hW2,
      take_append_length_eq (b₁ ++ b₂) _ (b₁.length + b₂.length) (by rw [List.length_append])]

/-! ## 32-byte word codec length -/

/-- The big-endian 32-byte encoding always has length 32. -/
@[simp] theorem toBytes32_length (v : UInt256) : (toBytes32 v).length = 32 := by
  simp [Mem.toBytes32]

/-- Reading the 64-byte window after two adjacent word stores (`storeWord
a₀ w₀; storeWord (a₀+32) w₁`) returns the big-endian concatenation
`toBytes32 w₀ ++ toBytes32 w₁` — the Venom `keccak(slot ++ addr)`
preimage, as a fact rather than a hypothesis. -/
theorem readBytes_storeWord_storeWord
    (mem : Mem) (w₀ w₁ : UInt256)
    (a₀ a₁ : UInt256) (ha₀ : a₀.toNat = 0) (ha₁ : a₁.toNat = 32) :
    ((mem.storeWord a₀ w₀).storeWord a₁ w₁).readBytes 0 64
      = toBytes32 w₀ ++ toBytes32 w₁ := by
  unfold Mem.storeWord
  rw [ha₀, ha₁]
  have h32 : (toBytes32 w₀).length = 32 := toBytes32_length w₀
  rw [show (32 : Nat) = (toBytes32 w₀).length from h32.symm]
  rw [show (64 : Nat) = (toBytes32 w₀).length + (toBytes32 w₁).length from by
        rw [h32, toBytes32_length]]
  exact readBytes_two_writes mem (toBytes32 w₀) (toBytes32 w₁)

/-! ## Word codec round-trip

`fromBytes32 (toBytes32 v) = v`, hence `loadWord (storeWord mem a v) a =
v`. This closes the opt side of the Venom equivalence: the patched
`mload 0x20; NOT` reads back exactly the address that the staging
`mstore 0x20` wrote. The proof is the base-256 digit-expansion identity
plus `UInt256.ofNat ∘ toNat = id`. -/

/-- `fromBytes'` of the little-endian base-256 digit list of `n` (the first
`m` digits) is `n % 256 ^ m`. -/
private theorem fromBytes_digits : ∀ (m n : Nat),
    fromBytes' ((List.range m).map (fun j => UInt8.ofNat (n / 256 ^ j % 256))) = n % 256 ^ m
  | 0, n => by simp [fromBytes', Nat.mod_one]
  | m + 1, n => by
      rw [List.range_succ_eq_map, List.map_cons, fromBytes', List.map_map]
      have hbyte : (UInt8.ofNat (n / 256 ^ 0 % 256)).toFin.val = n % 256 := by simp
      have htail :
          (List.map ((fun j => UInt8.ofNat (n / 256 ^ j % 256)) ∘ fun x => x + 1) (List.range m))
            = (List.range m).map (fun j => UInt8.ofNat (n / 256 / 256 ^ j % 256)) := by
        apply List.map_congr_left
        intro j _
        simp only [Function.comp_apply]
        congr 2
        rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
      rw [hbyte, htail, fromBytes_digits m (n / 256), show (2 : Nat) ^ 8 = 256 from by norm_num,
          ← Nat.mod_mul, ← pow_succ']

/-- Reversing a range-map with a flipped index undoes the flip. -/
private theorem reverse_map_range (n : Nat) (g : Nat → UInt8) :
    ((List.range n).map (fun i => g (n - 1 - i))).reverse = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_map, List.getElem_map, List.getElem_range,
        List.getElem_range]
    rw [List.length_map, List.length_range] at *
    congr 1
    omega

/-- Every `UInt256` value fits 32 base-256 digits — the bound the word codec's
roundtrips hang on. -/
theorem toNat_lt_pow32 (v : UInt256) : v.toNat < 256 ^ 32 := by
  have := v.val.isLt
  simpa [UInt256.toNat, UInt256.size] using this

/-- Decoding the 32-byte big-endian encoding recovers the underlying `Nat`.
Stated for the project's older decoder; it now follows from the library's
roundtrip through the `BinaryBridge` agreement. -/
theorem fromBytesBigEndian_toBytes32 (v : UInt256) :
    fromBytesBigEndian (toBytes32 v) = v.toNat := by
  rw [fromBytesBigEndian_eq_decodeBEU]
  exact Binary.decodeBEU_encodeBEU (toNat_lt_pow32 v)

/-- The old shape of `fromBytes32`, as a lemma: decode via the project's own
big-endian decoder. Call sites written against the previous definition rewrite
with this where they used to close by `rfl`. -/
theorem fromBytes32_eq (bytes : Mem) :
    fromBytes32 bytes = UInt256.ofNat (fromBytesBigEndian bytes) := by
  rw [fromBytes32, fromBytesBigEndian_eq_decodeBEU]

/-- The old shape of `toBytes32`, as a lemma: byte `i` is the `(31 - i)`-th
base-256 digit. Derived from the library codec by `encodeBEU_decodeBEU`
injectivity — the digit list has length 32 and decodes to `v.toNat`, so it IS
the width-32 encoding. -/
theorem toBytes32_digits (v : UInt256) :
    toBytes32 v
      = (List.range 32).map (fun i => UInt8.ofNat (v.toNat / 256 ^ (31 - i) % 256)) := by
  have hdec : Binary.decodeBEU
      ((List.range 32).map (fun i => UInt8.ofNat (v.toNat / 256 ^ (31 - i) % 256)))
      = v.toNat := by
    rw [← fromBytesBigEndian_eq_decodeBEU]
    show fromBytes' _ = v.toNat
    rw [reverse_map_range 32 (fun j => UInt8.ofNat (v.toNat / 256 ^ j % 256)),
        fromBytes_digits 32 v.toNat]
    exact Nat.mod_eq_of_lt (toNat_lt_pow32 v)
  calc toBytes32 v
      = Binary.encodeBEU 32 v.toNat := rfl
    _ = Binary.encodeBEU
          ((List.range 32).map (fun i => UInt8.ofNat (v.toNat / 256 ^ (31 - i) % 256))).length
          (Binary.decodeBEU
            ((List.range 32).map (fun i => UInt8.ofNat (v.toNat / 256 ^ (31 - i) % 256)))) := by
        rw [hdec, List.length_map, List.length_range]
    _ = _ := Binary.encodeBEU_decodeBEU _

/-- The 32-byte word codec is a round-trip. -/
theorem fromBytes32_toBytes32 (v : UInt256) : fromBytes32 (toBytes32 v) = v := by
  unfold fromBytes32 toBytes32
  rw [Binary.decodeBEU_encodeBEU (toNat_lt_pow32 v)]
  cases v with | mk fv => simp [UInt256.ofNat, UInt256.toNat, Id.run]

/-- **Opt-side round-trip**: loading a word from where it was just stored
returns it. -/
theorem loadWord_storeWord_self (mem : Mem) (a v : UInt256) :
    (mem.storeWord a v).loadWord a = v := by
  unfold loadWord storeWord
  rw [show (32 : Nat) = (toBytes32 v).length from (toBytes32_length v).symm,
      readBytes_writeBytes_self, fromBytes32_toBytes32]

end Mem
end EvmYul.Venom

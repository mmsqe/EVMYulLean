import EvmYul.Venom.NoAlias
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators

/-!
# Venom IR — multi-map slot packing, and the limits of de-hashing

The `~addr` peephole optimizes ONE map per contract: `~key` erases the slot
input, so a second optimized map would alias deterministically. This file
formalizes both sides of that boundary.

**The positive side** (`packSlot`): address-style keys leave 96 spare high
bits, enough to host a map id. `packSlot id key = ~(id·2^160 + key)` is
jointly injective (`packSlot_injective`), keeps distinct maps disjoint
(`packSlot_cross_map`), stays above every named low slot
(`packSlot_above_named_slot`), and degenerates to today's scheme at `id = 0`
(`packSlot_zero`) — the verified slot layout for a future multi-map IR-level
pass.

**The impossible side**, machine-checked pigeonhole instead of prose:

* `two_fullword_maps_must_alias` — ANY slot assignment for two maps over
  full-word keys has a collision: there is no injection
  `Bool × UInt256 ↪ UInt256`. Optimizing two `bytes32`-keyed maps in one
  contract is not risky; it is impossible.
* `long_keys_must_alias` — ANY slot assignment for 33-byte keys has a
  collision, so keys longer than a word can never be fully de-hashed; the
  inner keccak of the two-stage derivation (see `AbiDynKey`) is here to stay,
  and eliminating the outer keccak is the information-theoretic maximum.
-/

namespace EvmYul.UInt256

open EvmYul

theorem size_eq_two_pow : UInt256.size = 2 ^ 256 := by
  unfold UInt256.size
  norm_num

/-- `toNat` determines the value. -/
theorem toNat_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨⟨av, hav⟩⟩ := a
  obtain ⟨⟨bv, hbv⟩⟩ := b
  congr 1
  exact Fin.ext h

/-- `ofNat` inverts `toNat`. -/
theorem ofNat_toNat_self (a : UInt256) : UInt256.ofNat a.toNat = a := by
  refine toNat_inj ?_
  rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt (size_eq_two_pow ▸ a.val.isLt)]

/-! ## The multi-map slot packing -/

/-- Pack a map id into the spare high bits of an address-style key:
`~(id·2^160 + key)`. With `id < 2^88` and `key < 2^160` the sum never
overflows, every map gets a disjoint `2^160`-sized window, and the complement
keeps the whole family far above the named low slots. `id = 0` is exactly the
current single-map scheme (`packSlot_zero`). -/
def packSlot (mapId key : UInt256) : UInt256 :=
  UInt256.lnot (UInt256.ofNat (mapId.toNat * 2 ^ 160 + key.toNat))

theorem packSlot_toNat {mapId key : UInt256}
    (hid : mapId.toNat < 2 ^ 88) (hkey : key.toNat < 2 ^ 160) :
    (packSlot mapId key).toNat
      = 2 ^ 256 - 1 - (mapId.toNat * 2 ^ 160 + key.toNat) := by
  unfold packSlot
  rw [lnot_toNat, uint256_ofNat_toNat, Nat.mod_eq_of_lt (by omega), size_eq_two_pow]

/-- **Joint injectivity**: equal packed slots force equal map ids AND equal
keys — the multi-map no-aliasing core. -/
theorem packSlot_injective {id id' k k' : UInt256}
    (hid : id.toNat < 2 ^ 88) (hid' : id'.toNat < 2 ^ 88)
    (hk : k.toNat < 2 ^ 160) (hk' : k'.toNat < 2 ^ 160)
    (h : packSlot id k = packSlot id' k') : id = id' ∧ k = k' := by
  have h1 := congrArg UInt256.toNat h
  rw [packSlot_toNat hid hk, packSlot_toNat hid' hk'] at h1
  exact ⟨toNat_inj (by omega), toNat_inj (by omega)⟩

/-- **Cross-map disjointness**: distinct map ids give disjoint slot families,
whatever the keys. -/
theorem packSlot_cross_map {id id' k k' : UInt256}
    (hid : id.toNat < 2 ^ 88) (hid' : id'.toNat < 2 ^ 88)
    (hk : k.toNat < 2 ^ 160) (hk' : k'.toNat < 2 ^ 160)
    (hne : id ≠ id') : packSlot id k ≠ packSlot id' k' :=
  fun habs => hne (packSlot_injective hid hid' hk hk' habs).1

/-- Packed slots land at or above `2^256 - 2^248`, so they never collide with
a named low slot (`owner`, `totalSupply`, …) — the `packSlot` analogue of
`lnot_above_named_slot`. -/
theorem packSlot_above_named_slot {mapId key slot : UInt256}
    (hid : mapId.toNat < 2 ^ 88) (hkey : key.toNat < 2 ^ 160)
    (hslot : slot.toNat < 2 ^ 256 - 2 ^ 248) :
    packSlot mapId key ≠ slot := by
  intro habs
  have h := congrArg UInt256.toNat habs
  rw [packSlot_toNat hid hkey] at h
  omega

/-- Map id `0` is the current single-map scheme: `packSlot 0 key = ~key`. -/
theorem packSlot_zero (key : UInt256) :
    packSlot (UInt256.ofNat 0) key = UInt256.lnot key := by
  unfold packSlot
  rw [show (UInt256.ofNat 0).toNat = 0 from by rw [uint256_ofNat_toNat]; omega]
  rw [Nat.zero_mul, Nat.zero_add, ofNat_toNat_self]

/-! ## Multi-slot values: stride packing

A map value spanning `stride` storage words (a struct, a `String[..]`, …)
lives at consecutive slots. Plain `~key + off` interleaves neighbours
(`~(k+1) = ~k - 1`), corrupting adjacent keys deterministically; packing the
offset *inside* the complement — `~(key·stride + off)` — makes the windows
abut instead. -/

/-- Field `off` of `key`'s multi-slot value: `~(key·stride + off)`. -/
def strideSlot (stride key off : UInt256) : UInt256 :=
  UInt256.lnot (UInt256.ofNat (key.toNat * stride.toNat + off.toNat))

/-- `packSlot` is the `stride = 2^160` instance (map id as key, key as offset). -/
theorem packSlot_eq_strideSlot (mapId key : UInt256) :
    packSlot mapId key = strideSlot (UInt256.ofNat (2 ^ 160)) mapId key := by
  unfold packSlot strideSlot
  rw [uint256_ofNat_toNat, Nat.mod_eq_of_lt (by norm_num)]

/-- **Window bound.** With `key < 2^160` and `off < stride ≤ 2^b`, the affine
index `key·stride + off` stays below `2^(160+b)`. The one nonlinear fact both
`strideSlot` results rest on (`stride` is a variable, so `omega` alone cannot
bound `key·stride`; the `(key+1)·stride` step supplies it). -/
theorem stride_window_lt {b : ℕ} {stride key off : UInt256}
    (hk : key.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ b) (ho : off.toNat < stride.toNat) :
    key.toNat * stride.toNat + off.toNat < 2 ^ (160 + b) := by
  have h1 : key.toNat * stride.toNat + off.toNat < (key.toNat + 1) * stride.toNat := by
    rw [Nat.succ_mul]; omega
  have h2 : (key.toNat + 1) * stride.toNat ≤ 2 ^ 160 * 2 ^ b := Nat.mul_le_mul (by omega) hs
  rw [← pow_add] at h2
  omega

theorem strideSlot_toNat {stride key off : UInt256}
    (hk : key.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 96) (ho : off.toNat < stride.toNat) :
    (strideSlot stride key off).toNat
      = 2 ^ 256 - 1 - (key.toNat * stride.toNat + off.toNat) := by
  have hlt := stride_window_lt hk hs ho  -- < 2^(160+96) = 2^256
  unfold strideSlot
  rw [lnot_toNat, uint256_ofNat_toNat, Nat.mod_eq_of_lt (by omega), size_eq_two_pow]

/-- **Joint injectivity**: equal stride slots force equal keys AND equal field
offsets — adjacent keys' value windows never overlap. -/
theorem strideSlot_injective {stride key key' off off' : UInt256}
    (hk : key.toNat < 2 ^ 160) (hk' : key'.toNat < 2 ^ 160)
    (hs : stride.toNat ≤ 2 ^ 96)
    (ho : off.toNat < stride.toNat) (ho' : off'.toNat < stride.toNat)
    (h : strideSlot stride key off = strideSlot stride key' off') :
    key = key' ∧ off = off' := by
  have h1 := congrArg UInt256.toNat h
  rw [strideSlot_toNat hk hs ho, strideSlot_toNat hk' hs ho'] at h1
  have hs0 : 0 < stride.toNat := by omega
  have hlt := stride_window_lt hk hs ho
  have hlt' := stride_window_lt hk' hs ho'
  have hsum : key.toNat * stride.toNat + off.toNat
      = key'.toNat * stride.toNat + off'.toNat := by omega
  have hkey : key.toNat = key'.toNat := by
    have e1 : (key.toNat * stride.toNat + off.toNat) / stride.toNat = key.toNat := by
      rw [Nat.mul_comm key.toNat, Nat.mul_add_div hs0, Nat.div_eq_of_lt ho, Nat.add_zero]
    have e2 : (key'.toNat * stride.toNat + off'.toNat) / stride.toNat = key'.toNat := by
      rw [Nat.mul_comm key'.toNat, Nat.mul_add_div hs0, Nat.div_eq_of_lt ho', Nat.add_zero]
    rw [← e1, ← e2, hsum]
  exact ⟨toNat_inj hkey, toNat_inj (by rw [hkey] at hsum; omega)⟩

/-- Stride slots stay above every named low slot (for realistic strides). -/
theorem strideSlot_above_named_slot {stride key off slot : UInt256}
    (hk : key.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 32)
    (ho : off.toNat < stride.toNat)
    (hslot : slot.toNat < 2 ^ 256 - 2 ^ 192) :
    strideSlot stride key off ≠ slot := by
  intro habs
  have h := congrArg UInt256.toNat habs
  have hs96 : stride.toNat ≤ 2 ^ 96 := le_trans hs (Nat.pow_le_pow_right (by omega) (by omega))
  have hcap := stride_window_lt hk hs ho  -- < 2^(160+32) = 2^192
  rw [strideSlot_toNat hk hs96 ho] at h
  omega

/-! ## `UInt256` cardinality -/

/-- `UInt256` is in bijection with `Fin UInt256.size`. -/
def equivFin : UInt256 ≃ Fin UInt256.size where
  toFun := UInt256.val
  invFun := UInt256.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype UInt256 := Fintype.ofEquiv _ equivFin.symm

theorem card_eq_size : Fintype.card UInt256 = UInt256.size := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]

end EvmYul.UInt256

namespace EvmYul.Venom

open EvmYul

/-- **Two full-word-key maps cannot both be de-hashed.** Any slot assignment
for two maps over full 256-bit keys (`bytes32`, inner hashes, …) collides —
pigeonhole, not a cryptographic assumption. The one-optimized-map-per-contract
restriction is mathematically forced. -/
theorem two_fullword_maps_must_alias (f : Bool × UInt256 → UInt256) :
    ∃ x y, x ≠ y ∧ f x = f y := by
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [Fintype.card_prod, Fintype.card_bool, UInt256.card_eq_size,
    UInt256.size_eq_two_pow]
  have : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  omega

set_option exponentiation.threshold 300 in
/-- **Keys longer than a word can never be fully de-hashed.** Any slot
assignment for 33-byte keys (`Fin 33 → Fin 256`) collides — `2^264 > 2^256`.
The inner keccak of the two-stage dynamic-key derivation is unavoidable;
eliminating the outer keccak (`AbiDynKey`) is the information-theoretic
maximum. -/
theorem long_keys_must_alias (f : (Fin 33 → Fin 256) → UInt256) :
    ∃ k₁ k₂, k₁ ≠ k₂ ∧ f k₁ = f k₂ := by
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [UInt256.card_eq_size, UInt256.size_eq_two_pow, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin,
    show (256 : ℕ) ^ 33 = 2 ^ 264 from by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]]
  exact Nat.pow_lt_pow_right (by omega) (by omega)

end EvmYul.Venom

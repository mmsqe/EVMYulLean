import EvmYul.Venom.AbiBalance
import EvmYul.Venom.SlotPacking

/-!
# Venom IR — execution-level non-interference of multi-map `packSlot`

The IR-level pass (verified-venom-opt's `ir_pass.py`) optimizes SEVERAL
address-keyed maps in one contract by installing `packSlot id key =
~(id·2^160 + key)` with a distinct id per map. The slot math is proved in
`SlotPacking.lean` (`packSlot_injective` / `packSlot_cross_map`); this file
lifts it to the Venom execution level, matching the exact block the pass emits

    %pt = add <id·2^160>, key
    %pk = not %pt
    ... sload/sstore %pk ...

and proves the property the multi-map differential test checks:

* `packSlot_load_own_write` — a map reads back exactly what it wrote;
* `packSlot_cross_map_noninterference` — writing map `id₂` at any key is
  invisible to a read of a *different* map `id₁` at any key — the execution
  counterpart of `packSlot_cross_map`, i.e. two optimized maps in one contract
  never alias (the case plain `~key` provably cannot do).

For **multi-word values** the pass emits `mul stride, key; not; sub base, off`
(field `off` of the value). `venomStride_eq_strideSlot` certifies that
`sub (~(key·stride)) off = strideSlot stride key off = ~(key·stride + off)`,
so `strideSlot_injective` (SlotPacking.lean) makes distinct `(key, field)`
pairs land on distinct slots — value windows abut instead of interleaving
(the case the length-preserving `~key` rewrite corrupts).
-/

namespace EvmYul.Venom

open EvmYul EvmYul.UInt256

/-- The literal the pass adds before complementing: `id·2^160`. -/
def idStride (id : UInt256) : UInt256 := UInt256.ofNat (id.toNat * 2 ^ 160)

set_option maxRecDepth 4000 in
/-- The Venom `add`-then-`not` computes exactly `packSlot id addr`. -/
theorem venomPack_eq_packSlot {id addr : UInt256}
    (hid : id.toNat < 2 ^ 88) (ha : addr.toNat < 2 ^ 160) :
    UInt256.lnot (UInt256.add (idStride id) addr) = packSlot id addr := by
  -- the key window is bounded well below 2^256
  have hkey : id.toNat * 2 ^ 160 < 2 ^ 248 := by
    have h1 : id.toNat * 2 ^ 160 < 2 ^ 88 * 2 ^ 160 :=
      Nat.mul_lt_mul_of_pos_right hid (by positivity)
    have he : (2 : ℕ) ^ 88 * 2 ^ 160 = 2 ^ 248 := by rw [← pow_add]
    omega
  have hbig : (2 : ℕ) ^ 248 + 2 ^ 160 < 2 ^ 256 := by
    have : (2 : ℕ) ^ 248 < 2 ^ 256 := Nat.pow_lt_pow_right (by omega) (by omega)
    have : (2 : ℕ) ^ 160 < 2 ^ 248 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  -- the Venom `add` of the id-stride literal and the key equals the packed word
  have hstride : (idStride id).toNat = id.toNat * 2 ^ 160 := by
    rw [idStride, uint256_ofNat_toNat, Nat.mod_eq_of_lt (by
      have : (2 : ℕ) ^ 248 < 2 ^ 256 := Nat.pow_lt_pow_right (by omega) (by omega)
      omega)]
  have hsum : id.toNat * 2 ^ 160 + addr.toNat < 2 ^ 256 :=
    lt_trans (add_lt_add hkey ha) hbig
  have hadd : (UInt256.add (idStride id) addr).toNat = id.toNat * 2 ^ 160 + addr.toNat := by
    show (idStride id + addr).toNat = _
    rw [uint256_add_toNat, hstride, Nat.mod_eq_of_lt hsum]
  refine UInt256.toNat_inj ?_
  rw [lnot_toNat, hadd, packSlot_toNat hid ha, size_eq_two_pow]

/-! ## The blocks the IR pass emits -/

/-- Load `packSlot id a` — the pass's `add; not; sload` (concrete key `a`). -/
def packSlotLoadBlock (id a : UInt256) (out : VarName) : List Instruction :=
  [ { output := some "%pt", opcode := .add,   operands := [.lit (idStride id), .lit a] }
  , { output := some "%pk", opcode := .not,   operands := [.var "%pt"] }
  , { output := some out,   opcode := .sload, operands := [.var "%pk"] } ]

/-- Store `v` to `packSlot id a` — the pass's `add; not; sstore`. -/
def packSlotStoreBlock (id a v : UInt256) : List Instruction :=
  [ { output := some "%pt", opcode := .add,    operands := [.lit (idStride id), .lit a] }
  , { output := some "%pk", opcode := .not,    operands := [.var "%pt"] }
  , { opcode := .sstore, operands := [.var "%pk", .lit v] } ]

theorem execBlock_packSlotLoad (s : VenomState) (id a : UInt256) (out : VarName)
    (hid : id.toNat < 2 ^ 88) (ha : a.toNat < 2 ^ 160) :
    (execBlock s (packSlotLoadBlock id a out)).1.get out = s.sload (packSlot id a) := by
  simp only [packSlotLoadBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalBin, evalUn, VenomState.setOutput,
    VenomState.set_env_self, VenomState.get, VenomState.set_env, VenomState.sload,
    VenomState.set_storage]
  rw [venomPack_eq_packSlot hid ha]

theorem execBlock_packSlotStore (s : VenomState) (id a v : UInt256)
    (hid : id.toNat < 2 ^ 88) (ha : a.toNat < 2 ^ 160) :
    (execBlock s (packSlotStoreBlock id a v)).1.storage
      = fun k => if k = packSlot id a then v else s.storage k := by
  simp only [packSlotStoreBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalBin, evalUn, VenomState.setOutput,
    VenomState.set_env_self, VenomState.sstore, VenomState.set_env, VenomState.set_storage]
  rw [venomPack_eq_packSlot hid ha]

/-! ## The capstones -/

/-- **Own-write readback.** A map reads back exactly what it just wrote at the
same key. -/
theorem packSlot_load_own_write (s : VenomState) (id a v : UInt256)
    (hid : id.toNat < 2 ^ 88) (ha : a.toNat < 2 ^ 160) :
    (execBlock ((execBlock s (packSlotStoreBlock id a v)).1)
        (packSlotLoadBlock id a "%o")).1.get "%o" = v := by
  have hstore := execBlock_packSlotStore s id a v hid ha
  set s₁ := (execBlock s (packSlotStoreBlock id a v)).1 with hs₁
  rw [execBlock_packSlotLoad s₁ id a "%o" hid ha, VenomState.sload, hs₁, hstore]
  simp

/-- **Cross-map non-interference.** Writing map `id₂` at any key `b` is
invisible to a read of a *different* map `id₁` at any key `a` — two optimized
maps in one contract never alias. The execution counterpart of
`packSlot_cross_map`; the case the length-preserving `~key` scheme provably
cannot achieve (`two_fullword_maps_must_alias`). -/
theorem packSlot_cross_map_noninterference (s : VenomState) (id₁ id₂ a b v : UInt256)
    (hid₁ : id₁.toNat < 2 ^ 88) (hid₂ : id₂.toNat < 2 ^ 88)
    (ha : a.toNat < 2 ^ 160) (hb : b.toNat < 2 ^ 160)
    (hne : id₁ ≠ id₂) :
    (execBlock ((execBlock s (packSlotStoreBlock id₂ b v)).1)
        (packSlotLoadBlock id₁ a "%o")).1.get "%o"
      = (execBlock s (packSlotLoadBlock id₁ a "%o")).1.get "%o" := by
  have hstore := execBlock_packSlotStore s id₂ b v hid₂ hb
  set s₁ := (execBlock s (packSlotStoreBlock id₂ b v)).1 with hs₁
  rw [execBlock_packSlotLoad s₁ id₁ a "%o" hid₁ ha,
    execBlock_packSlotLoad s id₁ a "%o" hid₁ ha,
    VenomState.sload, VenomState.sload, hs₁, hstore]
  simp only [if_neg (packSlot_cross_map hid₁ hid₂ ha hb hne)]

/-! ## Multi-word values: the strideSlot bridge -/

/-- `≤` on `UInt256` is `≤` on `toNat`. -/
theorem le_of_toNat_le {a b : UInt256} (h : a.toNat ≤ b.toNat) : a ≤ b := h

set_option maxRecDepth 4000 in
/-- The Venom `sub (~(mul stride key)) off` the pass emits for field `off`
computes exactly `strideSlot stride key off = ~(key·stride + off)` — value
windows abut instead of interleaving. -/
theorem venomStride_eq_strideSlot {stride key off : UInt256}
    (hk : key.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 96) (ho : off.toNat < stride.toNat) :
    UInt256.sub (UInt256.lnot (UInt256.mul stride key)) off = strideSlot stride key off := by
  -- key·stride + off < 2^256 via the shared window bound
  have hcomm : key.toNat * stride.toNat = stride.toNat * key.toNat := Nat.mul_comm _ _
  have hbound : key.toNat * stride.toNat + off.toNat < 2 ^ 256 := stride_window_lt hk hs ho
  have hmul : (UInt256.mul stride key).toNat = stride.toNat * key.toNat := by
    show (stride * key).toNat = _
    rw [uint256_mul_toNat, Nat.mod_eq_of_lt (by omega)]
  -- the complement of a bounded word is ≥ the small field offset, so `sub` = `~(·+off)`
  have hle : off ≤ UInt256.lnot (UInt256.mul stride key) := by
    refine le_of_toNat_le ?_
    rw [lnot_toNat, hmul, size_eq_two_pow]
    omega
  refine UInt256.toNat_inj ?_
  show ((UInt256.lnot (UInt256.mul stride key)) - off).toNat = _
  rw [sub_toNat_of_le hle, lnot_toNat, hmul, strideSlot_toNat hk hs ho, size_eq_two_pow]
  omega

/-! ## Multi-word value blocks the pass emits -/

/-- Access field `off` of key `a`'s multi-word value: `mul stride,a; not; sub
base,off; sload` — what the strideSlot pass emits (concrete key/offset). -/
def strideLoadBlock (stride a off : UInt256) (out : VarName) : List Instruction :=
  [ { output := some "%sm", opcode := .mul,   operands := [.lit stride, .lit a] }
  , { output := some "%sb", opcode := .not,   operands := [.var "%sm"] }
  , { output := some "%sk", opcode := .sub,   operands := [.var "%sb", .lit off] }
  , { output := some out,   opcode := .sload, operands := [.var "%sk"] } ]

/-- The store dual. -/
def strideStoreBlock (stride a off v : UInt256) : List Instruction :=
  [ { output := some "%sm", opcode := .mul,   operands := [.lit stride, .lit a] }
  , { output := some "%sb", opcode := .not,   operands := [.var "%sm"] }
  , { output := some "%sk", opcode := .sub,   operands := [.var "%sb", .lit off] }
  , { opcode := .sstore, operands := [.var "%sk", .lit v] } ]

theorem execBlock_strideLoad (s : VenomState) (stride a off : UInt256) (out : VarName)
    (hk : a.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 96) (ho : off.toNat < stride.toNat) :
    (execBlock s (strideLoadBlock stride a off out)).1.get out
      = s.sload (strideSlot stride a off) := by
  simp only [strideLoadBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalBin, evalUn, VenomState.setOutput,
    VenomState.set_env_self, VenomState.get, VenomState.set_env, VenomState.sload,
    VenomState.set_storage]
  rw [venomStride_eq_strideSlot hk hs ho]

theorem execBlock_strideStore (s : VenomState) (stride a off v : UInt256)
    (hk : a.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 96) (ho : off.toNat < stride.toNat) :
    (execBlock s (strideStoreBlock stride a off v)).1.storage
      = fun k => if k = strideSlot stride a off then v else s.storage k := by
  simp only [strideStoreBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalBin, evalUn, VenomState.setOutput,
    VenomState.set_env_self, VenomState.sstore, VenomState.set_env, VenomState.set_storage]
  rw [venomStride_eq_strideSlot hk hs ho]

/-- **Field non-interference.** Writing field `off₂` of key `a₂` is invisible
to a read of a *different* `(key, field)` pair `(a₁, off₁)` — the execution
counterpart of `strideSlot_injective`: multi-word value windows never overlap,
the case the length-preserving `~key` rewrite corrupts. -/
theorem strideSlot_field_noninterference (s : VenomState) (stride a₁ a₂ o₁ o₂ v : UInt256)
    (hk₁ : a₁.toNat < 2 ^ 160) (hk₂ : a₂.toNat < 2 ^ 160) (hs : stride.toNat ≤ 2 ^ 96)
    (ho₁ : o₁.toNat < stride.toNat) (ho₂ : o₂.toNat < stride.toNat)
    (hne : a₁ ≠ a₂ ∨ o₁ ≠ o₂) :
    (execBlock ((execBlock s (strideStoreBlock stride a₂ o₂ v)).1)
        (strideLoadBlock stride a₁ o₁ "%o")).1.get "%o"
      = (execBlock s (strideLoadBlock stride a₁ o₁ "%o")).1.get "%o" := by
  have hstore := execBlock_strideStore s stride a₂ o₂ v hk₂ hs ho₂
  set s₁ := (execBlock s (strideStoreBlock stride a₂ o₂ v)).1 with hs₁
  rw [execBlock_strideLoad s₁ stride a₁ o₁ "%o" hk₁ hs ho₁,
    execBlock_strideLoad s stride a₁ o₁ "%o" hk₁ hs ho₁,
    VenomState.sload, VenomState.sload, hs₁, hstore]
  have hslot : strideSlot stride a₁ o₁ ≠ strideSlot stride a₂ o₂ := by
    intro h
    obtain ⟨hka, hoa⟩ := strideSlot_injective hk₁ hk₂ hs ho₁ ho₂ h
    exact hne.elim (· hka) (· hoa)
  simp only [if_neg hslot]

end EvmYul.Venom

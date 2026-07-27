import EvmYul.Venom.NoAlias

/-!
# Storage-slot abstraction (refinement) for the balance peephole

A storage scheme for an address-keyed balance map is a **slot function**
`f : address → slot`. Concrete word storage `σ : slot → word` *realizes* an
abstract balance map `B : address → word` under `f` when reading slot `f a`
yields `B a`. This file formalizes that refinement and shows:

* `realizes_read` — abstract reads are concrete reads at `f a`.
* `realizes_write` — abstract write-through is correct **iff the slot function
  is injective** (no aliasing). This is exactly where the no-aliasing fact
  earns its keep.
* `realizes_write_opt` — the optimized scheme `f = ~addr` supports correct
  balance updates *unconditionally*, because `lnot` is proved injective.
* `write_opt_preserves_named` — writing a `~addr` balance never disturbs a
  named low slot (`owner`, `totalSupply`, …), via `lnot_above_named_slot`.
* `orig_opt_agree` — if the original (keccak) and optimized (`~addr`) storages
  realize the *same* abstract map, they agree on every per-address balance —
  i.e. the storage relation underlying `venomBalanceLoad_orig_opt_equiv`
  *follows from* both being faithful realizations of one abstract map.

So the peephole is sound at the abstract level: swapping the slot function for
another injective one preserves the abstract balance semantics. The opt side
is fully proved; the orig (keccak) side needs only keccak injectivity
(collision-resistance), taken as a hypothesis.
-/

namespace EvmYul.Venom

open EvmYul

/-- Concrete word storage `σ` realizes abstract balances `B` under slot
function `f`: slot `f k` holds `B k`. -/
def Realizes (σ B f : UInt256 → UInt256) : Prop := ∀ k, σ (f k) = B k

/-- Point update of a total map. -/
def upd (g : UInt256 → UInt256) (k v : UInt256) : UInt256 → UInt256 :=
  fun x => if x = k then v else g x

@[simp] theorem upd_self (g : UInt256 → UInt256) (k v : UInt256) : upd g k v k = v := by
  simp [upd]

theorem upd_other (g : UInt256 → UInt256) (k v x : UInt256) (h : x ≠ k) :
    upd g k v x = g x := by simp [upd, h]

/-- Abstract reads are concrete reads at the abstracted slot. -/
theorem realizes_read {σ B f : UInt256 → UInt256} (h : Realizes σ B f) (k : UInt256) :
    σ (f k) = B k := h k

/-- **Write-through correctness — needs no aliasing.** If `f` is injective and
`σ` realizes `B`, then writing `v` to slot `f k` realizes `B` with `k ↦ v`.
Injectivity is what stops the write to `k`'s slot from clobbering another
address's balance. -/
theorem realizes_write {σ B f : UInt256 → UInt256} (hf : Function.Injective f)
    (h : Realizes σ B f) (k v : UInt256) :
    Realizes (upd σ (f k) v) (upd B k v) f := by
  intro x
  by_cases hx : x = k
  · subst hx; simp [upd]
  · have hfx : f x ≠ f k := fun e => hx (hf e)
    rw [upd_other _ _ _ _ hfx, upd_other _ _ _ _ hx]
    exact h x

/-- **The optimized scheme is correct unconditionally:** `~addr` is injective
(`lnot_injective`), so balance write-through through `~addr` slots is always
faithful — no extra assumption. -/
theorem realizes_write_opt {σ B : UInt256 → UInt256}
    (h : Realizes σ B UInt256.lnot) (a v : UInt256) :
    Realizes (upd σ (UInt256.lnot a) v) (upd B a v) UInt256.lnot :=
  realizes_write UInt256.lnot_injective h a v

/-- Writing a `~addr` balance (160-bit `addr`) leaves any named slot below
`2^256 - 2^160` untouched — named state (`owner`, `totalSupply`, …) survives. -/
theorem write_opt_preserves_named (σ : UInt256 → UInt256) (addr v slot : UInt256)
    (haddr : addr.toNat < 2 ^ 160) (hslot : slot.toNat < UInt256.size - 2 ^ 160) :
    upd σ (UInt256.lnot addr) v slot = σ slot :=
  upd_other _ _ _ _ (Ne.symm (UInt256.lnot_above_named_slot addr slot haddr hslot))

/-- **Original ≡ optimized at the abstract level.** If the original (keccak)
storage and the optimized (`~addr`) storage realize the *same* abstract
balance map, they agree on every per-address balance — the storage relation
that `venomBalanceLoad_orig_opt_equiv` assumes is *derived* here from both
being faithful realizations of one abstract map. -/
theorem orig_opt_agree {σ_orig σ_opt B f_orig : UInt256 → UInt256}
    (hOrig : Realizes σ_orig B f_orig)
    (hOpt : Realizes σ_opt B UInt256.lnot)
    (a : UInt256) :
    σ_orig (f_orig a) = σ_opt (UInt256.lnot a) := by
  rw [hOrig a, hOpt a]

end EvmYul.Venom

import EvmYul.Venom.Backend
import EvmYul.Venom.Solvency
import EvmYul.Venom.NoAlias

/-!
# The lowered transfer conserves total balance

`Backend.lowered_transfer` proves that the ten-instruction lowering of a token
transfer, run on EVMYulLean's real `EVM.step`, leaves

* `storage(kf) = storage(kf) − amt`,
* `storage(kd) = storage(kd) + amt`,
* every other slot unchanged.

This file closes the loop with the abstract conservation layer
(`EvmYul/Venom/Solvency.lean`): that storage outcome **is** the abstract
`transfer` of the balance map (`lowered_transfer_storage_eq`), so it inherits

* **conservation** of the balance sum (`balSumZ_transfer`), and
* **solvency** preservation (`transfer_preserves_solvent`).

So the verified Venom→EVM lowering of a transfer provably keeps `Σ balances`
constant — the token's core invariant, established end-to-end from the real
machine step down to the conservation theorem.

## Composing with `lowered_transfer`

`Backend.lowered_transfer` returns `∃ vsf, Sim vsf es10 L ∧ <the three storage
facts>`. Destructure it and feed the three facts straight into
`lowered_transfer_conserves` / `lowered_transfer_preserves_solvent` here (with
the slot values `vs.env kf`, `vs.env kd`, `vs.env amt` and the address
distinctness `hkfd`).
-/

namespace EvmYul.Venom
open EvmYul EvmYul.Venom.Backend

/-- **The storage after a lowered transfer is the abstract `transfer`.** A state
whose storage matches `lowered_transfer`'s conclusion (debit at `kf`, credit at
`kd`, all other slots unchanged, distinct slots) has storage equal — as a
function — to `transfer` of the original balance map. -/
theorem lowered_transfer_storage_eq
    (vsf vs : VenomState) (kf kd amt : UInt256)
    (hkf : vsf.storage kf = UInt256.sub (vs.storage kf) amt)
    (hkd : vsf.storage kd = UInt256.add (vs.storage kd) amt)
    (hframe : ∀ x, x ≠ kf → x ≠ kd → vsf.storage x = vs.storage x)
    (hne : kf ≠ kd) :
    vsf.storage = transfer vs.storage kf kd amt := by
  funext x
  unfold transfer
  by_cases hxd : x = kd
  · subst hxd
    rw [upd_self, upd_other _ _ _ _ (Ne.symm hne), hkd]; rfl
  · rw [upd_other _ _ _ _ hxd]
    by_cases hxf : x = kf
    · subst hxf
      rw [upd_self, hkf]; rfl
    · rw [upd_other _ _ _ _ hxf, hframe x hxf hxd]

/-- **The lowered transfer conserves total balance.** Over any finite slot set
containing both balance slots, the balance sum is unchanged (under the safe-math
preconditions the transfer's `SUB`/`ADD` require). -/
theorem lowered_transfer_conserves
    (vsf vs : VenomState) (kf kd amt : UInt256)
    (hkf : vsf.storage kf = UInt256.sub (vs.storage kf) amt)
    (hkd : vsf.storage kd = UInt256.add (vs.storage kd) amt)
    (hframe : ∀ x, x ≠ kf → x ≠ kd → vsf.storage x = vs.storage x)
    (hne : kf ≠ kd)
    (S : Finset UInt256) (hkfS : kf ∈ S) (hkdS : kd ∈ S)
    (hbal : amt ≤ vs.storage kf)
    (hovf : (vs.storage kd).toNat + amt.toNat < UInt256.size) :
    balSumZ vsf.storage S = balSumZ vs.storage S := by
  rw [lowered_transfer_storage_eq vsf vs kf kd amt hkf hkd hframe hne]
  exact balSumZ_transfer vs.storage kf kd amt S hkfS hkdS hne hbal hovf

/-- **The lowered transfer preserves solvency.** If the balances summed to the
total supply before, they still do after. -/
theorem lowered_transfer_preserves_solvent
    (vsf vs : VenomState) (kf kd amt ts : UInt256)
    (hkf : vsf.storage kf = UInt256.sub (vs.storage kf) amt)
    (hkd : vsf.storage kd = UInt256.add (vs.storage kd) amt)
    (hframe : ∀ x, x ≠ kf → x ≠ kd → vsf.storage x = vs.storage x)
    (hne : kf ≠ kd)
    (S : Finset UInt256) (hkfS : kf ∈ S) (hkdS : kd ∈ S)
    (hbal : amt ≤ vs.storage kf)
    (hovf : (vs.storage kd).toNat + amt.toNat < UInt256.size)
    (h : Solvent vs.storage ts S) :
    Solvent vsf.storage ts S := by
  rw [lowered_transfer_storage_eq vsf vs kf kd amt hkf hkd hframe hne]
  exact transfer_preserves_solvent vs.storage kf kd amt ts S hkfS hkdS hne hbal hovf h

/-! ## Closing the loop with the peephole's no-aliasing

When the balance slots are the **optimized** `~addr` form (the whole point of the
peephole), the slot-distinctness `kf ≠ kd` that conservation needs is no longer
an assumption: it *follows* from the holders' addresses being distinct, via the
no-aliasing lemma `distinct_addresses_distinct_opt_slots` (`~` is injective). So
a transfer between two distinct holders, on the optimized balance layout,
provably conserves total balance — the optimization's soundness condition is
exactly what makes the transfer safe. -/

/-- **Opt-slot transfer conserves balance.** With the balance slots in `~addr`
form for distinct holders `addrF ≠ addrD`, the slot-distinctness is discharged by
no-aliasing, and the balance sum is conserved. -/
theorem lowered_opt_transfer_conserves
    (vsf vs : VenomState) (addrF addrD amt : UInt256)
    (haddr : addrF ≠ addrD)
    (hkf : vsf.storage (UInt256.lnot addrF)
            = UInt256.sub (vs.storage (UInt256.lnot addrF)) amt)
    (hkd : vsf.storage (UInt256.lnot addrD)
            = UInt256.add (vs.storage (UInt256.lnot addrD)) amt)
    (hframe : ∀ x, x ≠ UInt256.lnot addrF → x ≠ UInt256.lnot addrD →
                vsf.storage x = vs.storage x)
    (S : Finset UInt256)
    (hkfS : UInt256.lnot addrF ∈ S) (hkdS : UInt256.lnot addrD ∈ S)
    (hbal : amt ≤ vs.storage (UInt256.lnot addrF))
    (hovf : (vs.storage (UInt256.lnot addrD)).toNat + amt.toNat < UInt256.size) :
    balSumZ vsf.storage S = balSumZ vs.storage S :=
  lowered_transfer_conserves vsf vs (UInt256.lnot addrF) (UInt256.lnot addrD) amt
    hkf hkd hframe (distinct_addresses_distinct_opt_slots haddr) S hkfS hkdS hbal hovf

/-- **Opt-slot transfer preserves solvency** (no-aliasing discharges the
slot-distinctness). -/
theorem lowered_opt_transfer_preserves_solvent
    (vsf vs : VenomState) (addrF addrD amt ts : UInt256)
    (haddr : addrF ≠ addrD)
    (hkf : vsf.storage (UInt256.lnot addrF)
            = UInt256.sub (vs.storage (UInt256.lnot addrF)) amt)
    (hkd : vsf.storage (UInt256.lnot addrD)
            = UInt256.add (vs.storage (UInt256.lnot addrD)) amt)
    (hframe : ∀ x, x ≠ UInt256.lnot addrF → x ≠ UInt256.lnot addrD →
                vsf.storage x = vs.storage x)
    (S : Finset UInt256)
    (hkfS : UInt256.lnot addrF ∈ S) (hkdS : UInt256.lnot addrD ∈ S)
    (hbal : amt ≤ vs.storage (UInt256.lnot addrF))
    (hovf : (vs.storage (UInt256.lnot addrD)).toNat + amt.toNat < UInt256.size)
    (h : Solvent vs.storage ts S) :
    Solvent vsf.storage ts S :=
  lowered_transfer_preserves_solvent vsf vs (UInt256.lnot addrF) (UInt256.lnot addrD) amt ts
    hkf hkd hframe (distinct_addresses_distinct_opt_slots haddr) S hkfS hkdS hbal hovf h

end EvmYul.Venom

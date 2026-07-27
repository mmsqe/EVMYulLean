import EvmYul.Data.RBMap
import EvmYul.Data.RBMap.Lemmas

import EvmYul.Frame.Projection
import EvmYul.State.AccountOps
import EvmYul.Maps.AccountMap
import EvmYul.Maps.StorageMap

/-!
# Storage-sum primitives — `storageSum` (Solvency §1.4)

`storageSum σ C` is the `ℕ`-valued sum of all `UInt256` values stored
at address `C`'s persistent-storage map. It powers any relational
solvency-style invariant of the form
`storageSum σ C ≤ balanceOf σ C` — i.e. "the contract's ETH balance
is at least as large as the sum of token-balance entries it tracks
in storage".

This file establishes:

* The definition of `storageSum`.
* `storageSum_unchanged_at_other_account` — `find?`-equality framing.
* `storageSum_of_storage_proj_eq` — projection-equality framing
  (used by §1.5's storage-only-at-codeOwner lifter).
* `storageSum_old_le` — single-slot bound via `List.le_sum_of_mem`.

The remaining storage-sum delta lemmas (`storageSum_sstore_decrement`,
`storageSum_sstore_increment`) characterise the post-SSTORE storage
sum at the codeOwner's account: the only slot whose value changes is
`spos`, and the per-slot delta dominates the sum delta. These are
the workhorses for the SSTORE-decrement and SSTORE-increment arms of
any relational-solvency bytecode walk (consumer side; not depended on
by the framework's mutual closure today).

Their proofs require multiset-permutation reasoning over
`acc.storage.toList` to relate the RBMap pre/post toList (with `slot`
overwritten or erased), which Batteries' `mem_toList_insert` /
`mem_toList_erase` only gives at the membership level. A clean
proof routes through a `Multiset` view; lifting to that form is the
remaining task. Until then, consumer Ξ-closure dischargers consume
these as per-state hypotheses on whatever per-PC predicate captures
their SSTORE / CALL slack data.
-/

namespace EvmYul
namespace Frame

open Batteries

/-! ## UInt256 `compare` order-class instances

`UInt256` is `Ord`-derived but not `TransCmp`/`OrientedCmp`/`ReflCmp` —
these are needed throughout this file's RBMap-level reasoning. The
`EvmSmith.Lemmas.UInt256Order` file proves equivalent instances at
the EvmSmith layer; we re-derive them here so this file (which lives
in `EvmYul`) is self-contained. -/

namespace UInt256Cmp

private theorem compare_eq_val (a b : EvmYul.UInt256) :
    compare a b = compare a.val b.val := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  show (compare a b).then Ordering.eq = compare a b
  cases compare a b <;> rfl

instance : Std.OrientedCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  eq_swap {x y} := by
    rw [compare_eq_val, compare_eq_val]
    exact Std.OrientedCmp.eq_swap

instance : Std.TransCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  isLE_trans {x y z} h1 h2 := by
    rw [compare_eq_val] at h1 h2 ⊢
    exact Std.TransCmp.isLE_trans h1 h2

instance : Std.ReflCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  compare_self {x} := by
    rw [compare_eq_val]
    exact Std.ReflCmp.compare_self

end UInt256Cmp

/-- `Std.TransCmp` for the pair-level key comparator on
`UInt256 × UInt256`. Required by `RBMap.mem_toList_unique` and
`del_toList_filter_pair`. -/
private instance pair_keyCmp_TransCmp :
    Std.TransCmp (fun (x y : EvmYul.UInt256 × EvmYul.UInt256) => compare x.1 y.1) :=
  inferInstanceAs (Std.TransCmp (Ordering.byKey Prod.fst compare))

/-- `storageSum σ C` is `Σ_slot σ[C].storage[slot]` cast to `ℕ`.

When `C` has no account, the sum is `0` (consistent with
`balanceOf`'s "absent → 0" convention). -/
def storageSum (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  match σ.find? C with
  | none => 0
  | some acc => acc.storage.foldl (fun acc _ v => acc + v.toNat) 0

/-- If `σ` and `σ'` agree on `find? C`, they agree on `storageSum`. -/
theorem storageSum_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) :
    storageSum σ' C = storageSum σ C := by
  unfold storageSum; rw [h]

/-- Inserting at `a ≠ C` leaves `storageSum σ C` unchanged.

Direct corollary of `find?_insert_ne`: at the projection level the
two maps agree on `find? C`, so their storageSum's coincide. -/
theorem storageSum_unchanged_at_other_account
    (σ : AccountMap .EVM) (C a : AccountAddress) (acc' : Account .EVM)
    (h : a ≠ C) :
    storageSum (σ.insert a acc') C = storageSum σ C := by
  apply storageSum_of_find?_eq
  exact find?_insert_ne σ a C acc' h

/-- The empty storage's sum is `0` (when `C` has no account). -/
theorem storageSum_none (σ : AccountMap .EVM) (C : AccountAddress)
    (h : σ.find? C = none) :
    storageSum σ C = 0 := by
  unfold storageSum; rw [h]

/-- If `σ.find? C = some acc`, then `storageSum σ C` is the foldl-sum
of `acc.storage`'s values. Useful for unfolding `storageSum` once the
account is in hand. -/
theorem storageSum_of_find?_some
    (σ : AccountMap .EVM) (C : AccountAddress) (acc : Account .EVM)
    (h : σ.find? C = some acc) :
    storageSum σ C
      = acc.storage.foldl (fun acc _ v => acc + v.toNat) 0 := by
  unfold storageSum; rw [h]

/-- If two states agree on the *storage projection* `find? C ↦ storage`
— i.e. on the `Option (StorageMap)` derived from `find? C` — then they
agree on `storageSum σ C`.

This is the lemma used to lift step-level storage-projection-equality
(provided by `EvmYul.step_modifies_storage_only_at_codeOwner` at
non-codeOwner addresses) to `storageSum` equality. -/
theorem storageSum_of_storage_proj_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : ((σ'.find? C).map (·.storage)) = ((σ.find? C).map (·.storage))) :
    storageSum σ' C = storageSum σ C := by
  unfold storageSum
  -- Case-split on σ.find? C and σ'.find? C; the hypothesis forces the
  -- two lookups to have the same option-shape, and storage values agree
  -- when both are `some`.
  cases hσ : σ.find? C with
  | none =>
    -- σ-side: 0. σ'-side must also be `none` (else `(some ?).map …` ≠ `none`).
    rw [hσ] at h
    cases hσ' : σ'.find? C with
    | none => rfl
    | some acc' =>
      rw [hσ'] at h
      -- h : (some acc').map (·.storage) = (none).map (·.storage)
      -- i.e. some acc'.storage = none — contradiction.
      simp only [Option.map_some, Option.map_none] at h
      cases h
  | some acc =>
    rw [hσ] at h
    cases hσ' : σ'.find? C with
    | none =>
      rw [hσ'] at h
      simp only [Option.map_some, Option.map_none] at h
      cases h
    | some acc' =>
      rw [hσ'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

/-! ## §1.4 — `storageSum_old_le`

The "old slot value is bounded by the storage-sum" bound. Used by
the at-`C` SSTORE step lemma: if the slot's old value is `oldVal`,
then `oldVal.toNat ≤ storageSum σ C`. The proof reduces `storageSum`
to `List.sum`-over-`toList` and uses `List.le_sum_of_mem` after
extracting the `(slot, oldVal)` pair from the `find?` hypothesis. -/

/-- Fold ↔ `List.sum` bridge for storage values. Mirror of
`Projection.totalETH_eq_sum`. -/
private theorem storageSum_acc_eq_sum
    (acc : Account .EVM) :
    acc.storage.foldl (fun a _ v => a + v.toNat) 0
      = (acc.storage.toList.map (fun p => p.2.toNat)).sum := by
  rw [Batteries.RBMap.foldl_eq_foldl_toList]
  generalize acc.storage.toList = L
  clear acc
  suffices h : ∀ (init : ℕ),
      L.foldl (fun init p => init + p.2.toNat) init
        = init + (L.map (fun p => p.2.toNat)).sum by
    simpa using h 0
  intro init
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- If `σ.find? C = some acc` and `acc.storage.find? slot = some oldVal`,
then `oldVal.toNat ≤ storageSum σ C`. Mirror of `balance_toNat_le_totalETH`
for the storage map. -/
theorem storageSum_old_le
    (σ : AccountMap .EVM) (C : AccountAddress) (slot oldVal : UInt256)
    (h : ((σ.find? C).map (·.storage)).bind (·.find? slot) = some oldVal) :
    oldVal.toNat ≤ storageSum σ C := by
  -- Decompose h into σ.find? C = some acc and acc.storage.find? slot = some oldVal.
  cases hσ : σ.find? C with
  | none =>
    rw [hσ] at h
    simp only [Option.map_none, Option.bind_none] at h
    cases h
  | some acc =>
    rw [hσ] at h
    simp only [Option.map_some] at h
    -- h : (acc.storage).find? slot |>.bind … = some oldVal but already at the
    -- `bind` level via Option.some_bind: bind some f = f acc.storage.
    -- Actually: (some acc.storage).bind (·.find? slot) = some oldVal
    -- ⇒ acc.storage.find? slot = some oldVal.
    have h_find : acc.storage.find? slot = some oldVal := by
      simpa using h
    -- Reduce storageSum σ C to the foldl over acc.storage.
    rw [storageSum_of_find?_some σ C acc hσ, storageSum_acc_eq_sum acc]
    -- Use find?_some_mem_toList: ∃ slot' ∈ toList with compare-eq.
    obtain ⟨slot', hMem, _⟩ := Batteries.RBMap.find?_some_mem_toList h_find
    -- oldVal.toNat ∈ mapped list of values.
    have hIn : oldVal.toNat ∈ acc.storage.toList.map (fun p => p.2.toNat) :=
      List.mem_map.mpr ⟨(slot', oldVal), hMem, rfl⟩
    exact List.le_sum_of_mem hIn

/-! ## §1.5 — `storageSum`-delta laws (SSTORE-replace / SSTORE-erase)

The single-slot delta of `storageSum` under `Account.updateStorage`.
Two cases match `updateStorage`'s `if v == default then erase else
insert` shape:

* `storageSum_sstore_replace_eq` — replacing slot `k`'s value `oldVal`
  with `newVal ≠ 0`: `new_sum + oldVal.toNat = old_sum + newVal.toNat`.
* `storageSum_sstore_erase_eq` — erasing a present slot `k`:
  `new_sum + oldVal.toNat = old_sum`.

The proofs route through Batteries' `exists_insert_toList_zoom_node`
(insert) / a custom `del_toList_filter` (erase) at the `RBNode`
level, lifted via list-`sum`. Direct structural induction over
`RBNode`'s cases (red/black/leaf + balance branches) is bundled
inside Batteries' / our toList-level lemmas. -/

/-- Helper: the `Storage` foldl over `(fun acc _k v => acc + v.toNat)`
equals `(toList.map (·.2.toNat)).sum`. Uniform for all `RBMap UInt256
UInt256 compare`. -/
private theorem storageSum_foldl_eq_sum
    (m : Storage) :
    m.foldl (fun a _ v => a + v.toNat) 0
      = (m.toList.map (fun p => p.2.toNat)).sum := by
  rw [Batteries.RBMap.foldl_eq_foldl_toList]
  generalize m.toList = L
  suffices h : ∀ (init : ℕ),
      L.foldl (fun init p => init + p.2.toNat) init
        = init + (L.map (fun p => p.2.toNat)).sum by
    simpa using h 0
  intro init
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- A list factored as `L = L₁ ++ x :: L₂` and reformed as `L₁ ++ y :: L₂`
shifts the value-sum: `new_sum + g x.2 = old_sum + g y.2`. Used by
the SSTORE-replace branch. -/
private theorem list_sum_factor_replace
    {α β : Type*} (L₁ L₂ : List (α × β)) (x y : α × β) (g : β → ℕ) :
    ((L₁ ++ y :: L₂).map (fun p => g p.2)).sum + g x.2
      = ((L₁ ++ x :: L₂).map (fun p => g p.2)).sum + g y.2 := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-- A list factored as `L = L₁ ++ x :: L₂` reformed as `L₁ ++ L₂`
loses `g x.2`: `new_sum + g x.2 = old_sum`. Used by SSTORE-erase. -/
private theorem list_sum_factor_remove
    {α β : Type*} (L₁ L₂ : List (α × β)) (x : α × β) (g : β → ℕ) :
    ((L₁ ++ L₂).map (fun p => g p.2)).sum + g x.2
      = ((L₁ ++ x :: L₂).map (fun p => g p.2)).sum := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-- Inserting at a present key in a `Storage` shifts the foldl-sum
by `newVal.toNat - oldVal.toNat` (additive form):
`new_sum + oldVal.toNat = old_sum + newVal.toNat`.

Routes through Batteries' `exists_insert_toList_zoom_node`. -/
theorem storageSum_storage_insert_replace_eq
    (s : Storage) (k oldVal newVal : UInt256)
    (h_find : s.find? k = some oldVal) :
    (s.insert k newVal).foldl (fun a _ v => a + v.toNat) 0
        + oldVal.toNat
      = s.foldl (fun a _ v => a + v.toNat) 0
        + newVal.toNat := by
  rw [storageSum_foldl_eq_sum s, storageSum_foldl_eq_sum (s.insert k newVal)]
  -- Extract balanced witness and orderedness from `s.2 : RBSet.WF`.
  obtain ⟨hOrd, _, _, hBal⟩ := s.2.out
  -- Zoom with cut = `Ordering.byKey Prod.fst compare (k, newVal)` (i.e. the
  -- exact cut used by `RBSet.insert (k, newVal)`).
  match e : Batteries.RBNode.zoom (Ordering.byKey Prod.fst compare (k, newVal))
            s.1 with
  | (.nil, _p) =>
    -- nil case: contradicts `find? k = some oldVal`.
    exfalso
    have hzn : Batteries.RBNode.find?
        (Ordering.byKey Prod.fst compare (k, newVal)) s.1 = none := by
      rw [Batteries.RBNode.find?_eq_zoom, e]; rfl
    have h_find' : s.find? k = none := by
      show (s.1.find? (fun p => compare k p.1)).map (·.2) = none
      -- The cut `Ordering.byKey Prod.fst compare (k, newVal)` is
      -- definitionally `fun p => compare (k, newVal).1 p.1 = compare k p.1`.
      have : Batteries.RBNode.find?
              (fun p => compare k p.1) s.1 = none := hzn
      rw [this]; rfl
    rw [h_find'] at h_find
    cases h_find
  | (.node c l (kE, vE) r, p) =>
    obtain ⟨L₁, L₂, hToL_orig, hToL_ins⟩ :=
      Batteries.RBNode.exists_insert_toList_zoom_node hBal e (v := (k, newVal))
    -- The `OnRoot` form of `zoom_zoomed₁` says cut (kE, vE) = .eq.
    have hCutEq : Ordering.byKey Prod.fst compare (k, newVal) (kE, vE) = .eq :=
      (Batteries.RBNode.Path.zoom_zoomed₁ e :
        (Batteries.RBNode.node c l (kE, vE) r :
            Batteries.RBNode (UInt256 × UInt256)).OnRoot _)
    -- Bridge `s.toList` and `(s.insert k newVal).toList` to the underlying
    -- `s.1.toList` form.
    have hsToList : s.toList = s.1.toList := rfl
    have hsInsToList :
        (s.insert k newVal).toList
          = (s.1.insert (Ordering.byKey Prod.fst compare)
              (k, newVal)).toList := rfl
    rw [hsToList, hsInsToList, hToL_orig, hToL_ins]
    -- Identify vE with oldVal via `mem_toList_unique` + `find?_some_mem_toList`.
    have hMemSetToList : (kE, vE) ∈ s.toList := by
      change (kE, vE) ∈ s.1.toList
      rw [hToL_orig]
      exact List.mem_append.mpr (.inr (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨y, hMemY, hYeq⟩ := Batteries.RBMap.find?_some_mem_toList h_find
    -- `compare k kE = .eq` (from hCutEq) and `compare k y = .eq` ⇒ `compare kE y = .eq`.
    have hKeyEq : compare kE y = .eq := by
      have h1 : compare k kE = .eq := hCutEq
      have h2 : compare k y = .eq := hYeq
      have h1' : compare kE k = .eq := (Std.OrientedCmp.eq_comm (cmp := compare)).mp h1
      exact Std.TransCmp.eq_trans h1' h2
    have hPairUniq : (kE, vE) = (y, oldVal) :=
      Batteries.RBMap.mem_toList_unique hMemSetToList hMemY hKeyEq
    have hVEeq : vE = oldVal := by
      simp only [Prod.mk.injEq] at hPairUniq
      exact hPairUniq.2
    -- Apply the list-level factor; replace vE by oldVal in the goal explicitly.
    rw [hVEeq]
    exact list_sum_factor_replace L₁ L₂ (kE, oldVal) (k, newVal) (fun v => v.toNat)

/-! ### Erase branch — needs an RBNode-level `del_toList_filter`

`del_toList_filter` (used in `EvmYul/Frame/UpsilonFrame.lean`'s
`erase_toList_filter`) characterizes `(t.del cut).toList` as the
`toList`-filter that drops compare-eq entries. Mirror the proof here. -/

private theorem filter_eq_self_of_all
    {α} {L : List α} {Q : α → Bool}
    (h : ∀ x ∈ L, Q x = true) : L.filter Q = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha : Q a = true := h a (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp [ha, ih']

/-- `RBNode.append` distributes over `toList`. Mirror of
`Layer1.append_toList`. -/
private theorem append_toList_storage :
    ∀ (l r : Batteries.RBNode (UInt256 × UInt256)),
      (l.append r).toList = l.toList ++ r.toList
  | .nil, r => by simp [Batteries.RBNode.append]
  | .node _ _ _ _, .nil => by simp [Batteries.RBNode.append]
  | .node .red a x b, .node .red c y d => by
    have ih := append_toList_storage b c
    unfold Batteries.RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' :
          (Batteries.RBNode.node .black a' x' b' :
              Batteries.RBNode (UInt256 × UInt256)).toList
            = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [Batteries.RBNode.toList_node]
      have : (Batteries.RBNode.node .black a' x' b' :
                Batteries.RBNode (UInt256 × UInt256)).toList
              ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by rw [ih']
      simp only [Batteries.RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .black c y d => by
    have ih := append_toList_storage b c
    unfold Batteries.RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node, Batteries.RBNode.balLeft_toList]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' :
          (Batteries.RBNode.node .black a' x' b' :
              Batteries.RBNode (UInt256 × UInt256)).toList
            = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [Batteries.RBNode.toList_node, Batteries.RBNode.balLeft_toList]
      have : (Batteries.RBNode.node .black a' x' b' :
                Batteries.RBNode (UInt256 × UInt256)).toList
              ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by rw [ih']
      simp only [Batteries.RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .red c y d => by
    unfold Batteries.RBNode.append
    have ih := append_toList_storage (Batteries.RBNode.node .black a x b) c
    simp [Batteries.RBNode.toList_node, ih]
  | .node .red a x b, .node .black c y d => by
    unfold Batteries.RBNode.append
    have ih := append_toList_storage b (Batteries.RBNode.node .black c y d)
    simp [Batteries.RBNode.toList_node, ih]
  termination_by l r => l.size + r.size
  decreasing_by
    all_goals (simp only [Batteries.RBNode.size]; omega)

/-- `del cut` removes exactly the entries with `cut = .eq`. Mirror of
`Layer1.del_toList_filter`. -/
private theorem del_toList_filter_pair
    {cmp : UInt256 × UInt256 → UInt256 × UInt256 → Ordering}
    {cut : UInt256 × UInt256 → Ordering}
    [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    (t : Batteries.RBNode (UInt256 × UInt256)) (ht : t.Ordered cmp) :
    (t.del cut).toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq)) := by
  induction t with
  | nil => simp [Batteries.RBNode.del]
  | node c a y b iha ihb =>
    obtain ⟨ay, yb, hoa, hob⟩ := ht
    have iha' := iha hoa
    have ihb' := ihb hob
    have hAll_a_lt_y : ∀ z ∈ a.toList, cmp z y = .lt := by
      intro z hz
      have hmem := Batteries.RBNode.mem_toList.mp hz
      have := Batteries.RBNode.All_def.1 ay z hmem
      obtain ⟨h⟩ := this
      exact h
    have hAll_y_lt_b : ∀ z ∈ b.toList, cmp y z = .lt := by
      intro z hz
      have hmem := Batteries.RBNode.mem_toList.mp hz
      have := Batteries.RBNode.All_def.1 yb z hmem
      obtain ⟨h⟩ := this
      exact h
    unfold Batteries.RBNode.del
    simp only [Batteries.RBNode.toList_node, List.filter_append, List.filter_cons]
    match hcy : cut y with
    | .lt =>
      have hbFilter :
          b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt :=
          Batteries.RBNode.IsCut.lt_trans (hAll_y_lt_b z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only []
      split
      all_goals
        simp only [Batteries.RBNode.balLeft_toList,
                   Batteries.RBNode.toList_node, hbFilter, iha']
        simp
    | .gt =>
      have haFilter :
          a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt :=
          Batteries.RBNode.IsCut.gt_trans (hAll_a_lt_y z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only []
      split
      all_goals
        simp only [Batteries.RBNode.balRight_toList,
                   Batteries.RBNode.toList_node, haFilter, ihb']
        simp
    | .eq =>
      have haFilter :
          a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt := by
          have hE := Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hzy : cmp z y = .lt := hAll_a_lt_y z hz
          have hyz : cmp y z = .gt := Std.OrientedCmp.gt_iff_lt.mpr hzy
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hbFilter :
          b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt := by
          have hE := Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hyz : cmp y z = .lt := hAll_y_lt_b z hz
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = false := by simp [hcy]
      simp only [append_toList_storage, haFilter, hbFilter]
      simp

/-- `RBMap UInt256 UInt256 compare`-level erase characterisation: the
post-erase `toList` is the pre-erase `toList` with compare-eq entries
filtered out. -/
private theorem storage_erase_toList_filter
    (s : Storage) (k : UInt256) :
    (s.erase k).toList
      = s.toList.filter (fun p => decide (compare k p.1 ≠ .eq)) := by
  show (s.1.erase (fun p => compare k p.1)).toList
       = s.1.toList.filter _
  rw [show
        ((s.1.erase (fun p => compare k p.1)) :
            Batteries.RBNode (UInt256 × UInt256)) =
          (s.1.del (fun p => compare k p.1)).setBlack from rfl,
      Batteries.RBNode.setBlack_toList]
  exact del_toList_filter_pair (cmp := Ordering.byKey Prod.fst compare)
    (cut := fun p => compare k p.1) s.1 s.2.out.1

/-- For `Storage`, `toList` is `Nodup` (implied by sortedness +
reflexive cmp). Used by erase-of-mem to factor out the unique
removed entry. -/
private theorem storage_toList_nodup (s : Storage) : s.toList.Nodup := by
  have hp := Batteries.RBMap.toList_sorted (t := s)
  have : s.toList.Pairwise (fun p q => p ≠ q) := by
    refine hp.imp ?_
    intro a b hab heq
    subst heq
    obtain ⟨hab'⟩ := hab
    have hv : compare a.1 a.1 = .lt := hab'
    have hrefl : compare a.1 a.1 = .eq := Std.ReflCmp.compare_self
    rw [hrefl] at hv; cases hv
  exact this

/-- Erasing a present key in a `Storage` decreases the foldl-sum by
exactly that key's value: `new_sum + oldVal.toNat = old_sum`.

This is the SSTORE-`v=0`-erase branch of `Account.updateStorage`. -/
theorem storageSum_storage_erase_eq
    (s : Storage) (k oldVal : UInt256)
    (h_find : s.find? k = some oldVal) :
    (s.erase k).foldl (fun a _ v => a + v.toNat) 0
        + oldVal.toNat
      = s.foldl (fun a _ v => a + v.toNat) 0 := by
  rw [storageSum_foldl_eq_sum s, storageSum_foldl_eq_sum (s.erase k)]
  -- s.toList factors as `L ++ (k', oldVal) :: R` for some k' compare-eq to k.
  obtain ⟨y, hMemY, hKeq⟩ := Batteries.RBMap.find?_some_mem_toList h_find
  obtain ⟨L, R, hSplit⟩ := List.append_of_mem hMemY
  -- (s.erase k).toList = (L ++ (y, oldVal) :: R).filter (compare k ·.1 ≠ .eq).
  rw [storage_erase_toList_filter, hSplit]
  -- Show the filter drops only the (y, oldVal) entry.
  -- Step 1: every element in L ++ R has compare k ·.1 ≠ .eq (else by Nodup
  -- + uniqueness, it would coincide with (y, oldVal)).
  have hNoEq : ∀ p ∈ L ++ R, compare k p.1 ≠ .eq := by
    intro p hp hpEq
    have hpIn : p ∈ s.toList := by
      rw [hSplit]
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right L (List.mem_cons_of_mem _ h)
    have h2 : compare p.1 k = .eq := by
      rw [Std.OrientedCmp.eq_comm]; exact hpEq
    have hpk : compare p.1 y = .eq := Std.TransCmp.eq_trans h2 hKeq
    have hpEq2 : p = (y, oldVal) :=
      Batteries.RBMap.mem_toList_unique hpIn hMemY hpk
    have hNodup := storage_toList_nodup s
    rw [hSplit] at hNodup
    have hNotInLR : (y, oldVal) ∉ L ++ R := by
      rw [List.nodup_append] at hNodup
      obtain ⟨_, hndR, hdisj⟩ := hNodup
      simp only [List.nodup_cons] at hndR
      intro hmem
      rcases List.mem_append.mp hmem with hL | hR
      · exact hdisj (y, oldVal) hL (y, oldVal) (by simp) rfl
      · exact hndR.1 hR
    apply hNotInLR; rw [← hpEq2]; exact hp
  -- Step 2: filter drops the middle (y, oldVal) and keeps L ++ R intact.
  have hKeyDec : decide (compare k y ≠ .eq) = false := by simp [hKeq]
  have hL_ok : L.filter (fun p => decide (compare k p.1 ≠ .eq)) = L := by
    apply filter_eq_self_of_all
    intro p hp
    have := hNoEq p (List.mem_append_left R hp)
    simp [this]
  have hR_ok : R.filter (fun p => decide (compare k p.1 ≠ .eq)) = R := by
    apply filter_eq_self_of_all
    intro p hp
    have := hNoEq p (List.mem_append_right L hp)
    simp [this]
  rw [show (L ++ (y, oldVal) :: R) = (L ++ [(y, oldVal)]) ++ R from by simp,
      List.filter_append, List.filter_append, List.filter_cons]
  simp only [hKeyDec, List.filter_nil, hL_ok, hR_ok]
  -- Goal: ((L ++ (if false ... else []) ++ R).map ...).sum + oldVal.toNat
  --     = ((L ++ (y, oldVal) :: R).map ...).sum.
  -- The remaining `if false = true then [...] else []` reduces to `[]`.
  simp only [show (false = true) = False from by simp, if_false]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
             List.append_nil, List.map_nil, List.sum_nil]
  ring

/-! ### `Account.updateStorage`-shape lifters at the `AccountMap` level

These thread the `Storage`-level delta lemmas through to `storageSum
σ C` for the post-`sstore` state. -/

/-- The `storageSum` of `σ.insert C { acc with storage := s' }` equals
the foldl-sum of `s'`. The container update is at the codeOwner
address `C`, so `storageSum` reads the new account's storage map. -/
theorem storageSum_insert_at_C
    (σ : AccountMap .EVM) (C : AccountAddress) (acc : Account .EVM) :
    storageSum (σ.insert C acc) C
      = acc.storage.foldl (fun a _ v => a + v.toNat) 0 := by
  unfold storageSum
  rw [find?_insert_self]

/-- `Account.updateStorage` on a `slot ≠ 0` post-state: the new
storage is `acc.storage.insert slot newVal`. -/
private theorem updateStorage_storage_of_ne_zero
    {τ} (acc : Account τ) (slot newVal : UInt256) (h : (newVal == default) = false) :
    (acc.updateStorage slot newVal).storage = acc.storage.insert slot newVal := by
  unfold Account.updateStorage
  simp [h]

/-- `Account.updateStorage` on a `slot = 0` post-state: the new
storage is `acc.storage.erase slot`. -/
private theorem updateStorage_storage_of_zero
    {τ} (acc : Account τ) (slot : UInt256) :
    (acc.updateStorage slot ⟨0⟩).storage = acc.storage.erase slot := by
  unfold Account.updateStorage
  have h : ((⟨0⟩ : UInt256) == default) = true := by decide
  simp [h]

/-- **SSTORE-replace at C** (insert branch, `newVal ≠ 0`): the
post-storage-sum at `C` equals the pre-storage-sum at `C` shifted by
`newVal.toNat - oldVal.toNat` (additive form).

`new_sum + oldVal.toNat = old_sum + newVal.toNat`. -/
theorem storageSum_sstore_replace_eq
    (σ : AccountMap .EVM) (C : AccountAddress) (slot newVal oldVal : UInt256)
    (h_newVal : (newVal == default) = false)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal) :
    storageSum (σ.insert C (acc.updateStorage slot newVal)) C + oldVal.toNat
      = storageSum σ C + newVal.toNat := by
  rw [storageSum_insert_at_C, storageSum_of_find?_some σ C acc h_find,
      updateStorage_storage_of_ne_zero acc slot newVal h_newVal]
  exact storageSum_storage_insert_replace_eq acc.storage slot oldVal newVal h_old

/-- **SSTORE-erase at C** (erase branch, `newVal = 0`): the
post-storage-sum at `C` equals the pre-storage-sum at `C` minus the
old slot value.

`new_sum + oldVal.toNat = old_sum`. -/
theorem storageSum_sstore_erase_eq
    (σ : AccountMap .EVM) (C : AccountAddress) (slot oldVal : UInt256)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal) :
    storageSum (σ.insert C (acc.updateStorage slot ⟨0⟩)) C + oldVal.toNat
      = storageSum σ C := by
  rw [storageSum_insert_at_C, storageSum_of_find?_some σ C acc h_find,
      updateStorage_storage_of_zero acc slot]
  exact storageSum_storage_erase_eq acc.storage slot oldVal h_old

/-! ### `findD`-flavored bridge — matches SLOAD-strong's pushed-value shape

The SLOAD-strong wrapper exposes the pushed value as
`acc.storage.findD slot ⟨0⟩` (the EVM SSTORE-after-SLOAD semantics
where SLOAD-of-missing returns `0`). The cascade-fact predicates that
flow from a strong-walk SLOAD therefore carry a `findD slot ⟨0⟩ =
oldVal` shape rather than the strict `find? slot = some oldVal` form.

`storageSum_sstore_replace_eq_findD` is the `findD`-flavored sibling
of `storageSum_sstore_replace_eq` / `storageSum_sstore_erase_eq`,
proving the **`≤`-form** (sufficient for invariant preservation) under
a `findD slot ⟨0⟩ = oldVal` hypothesis and the bound `newVal ≤ oldVal`.

The proof case-splits on `find? slot`:

* `some oldVal'`: `findD = oldVal'`, so `oldVal' = oldVal`. Reduces to
  the strict `_replace_eq` / `_erase_eq` law (depending on `newVal == 0`).
* `none`: `findD = ⟨0⟩`, so `oldVal = ⟨0⟩` and the bound forces `newVal
  = ⟨0⟩`. The SSTORE-erase post-state's storage is `acc.storage.erase
  slot`; with `slot` absent, the erase is a `toList`-no-op, so
  `storageSum` is preserved (`new = old`). -/

/-- Erase-of-absent-slot preserves the storage foldl-sum: when `slot`
is not present, the `toList`-filter drops nothing. Used for the
`find? slot = none` case in the `findD`-flavored bridge. -/
theorem storageSum_storage_erase_eq_of_find?_none
    (s : Storage) (k : UInt256)
    (h : s.find? k = none) :
    (s.erase k).foldl (fun a _ v => a + v.toNat) 0
      = s.foldl (fun a _ v => a + v.toNat) 0 := by
  rw [storageSum_foldl_eq_sum s, storageSum_foldl_eq_sum (s.erase k)]
  rw [storage_erase_toList_filter]
  -- Show the filter keeps the entire list (no entry has compare k ·.1 = .eq).
  have hAll : ∀ p ∈ s.toList,
      decide (compare k p.1 ≠ .eq) = true := by
    intro p hp
    have hpEq : compare k p.1 ≠ .eq := by
      intro hkp
      -- compare k p.1 = .eq means key compare-eq, so find? k must succeed.
      -- Use the storage's order/sortedness to derive a contradiction.
      have hpIn : p ∈ s.toList := hp
      have hpkey : compare p.1 k = .eq := by
        rw [Std.OrientedCmp.eq_comm]; exact hkp
      -- find? k goes through the underlying RBMap via `findCore?`; with the
      -- key ordering and a member with cmp-eq, find? returns `some _`.
      have hp_find : s.find? k = some p.2 := by
        -- `find?_some` characterizes find? = some at the RBSet level.
        -- We use Batteries.RBMap.findEntry?_eq_some (which is equivalent).
        -- Construct via mem_toList → mem and ordered + eq key.
        unfold Batteries.RBMap.find?
        unfold Batteries.RBMap.findEntry?
        -- Reduce to RBSet.findP?; need to find a unique element with cmp-eq.
        -- `RBSet.find?_some` is the cleanest tool here, but findEntry?
        -- is easier: it returns the first matching entry by cut.
        -- Strategy: use Batteries.RBMap.find?_some_iff via the ordered set.
        have hSorted := Batteries.RBMap.toList_sorted (t := s)
        -- Build the find? = some using the ordered uniqueness. Use the
        -- simpler `find?_some_iff_findCore?_some` chain.
        -- Actually: use Ordered.find?_some on the underlying RBSet.
        have hOrd : s.1.Ordered (Ordering.byKey Prod.fst compare) := s.2.out.1
        have hMem : p ∈ s.1 := Batteries.RBNode.mem_toList.mp hpIn
        have hCut_eq :
            (Ordering.byKey Prod.fst compare (p.1, p.2) p) = .eq := by
          unfold Ordering.byKey; simp
        -- The cut for `find? k` is `fun e => compare k e.1`. We need to
        -- show `find? (cut := compare k ·.1) s.1 = some p`.
        have hCut_p : (fun e : UInt256 × UInt256 => compare k e.1) p = .eq := by
          show compare k p.1 = .eq; exact hkp
        have h_findR :
            (s.1.find? (fun e : UInt256 × UInt256 => compare k e.1)) = some p := by
          apply (hOrd.find?_some
            (cut := fun e : UInt256 × UInt256 => compare k e.1)).mpr
          exact ⟨hMem, hCut_p⟩
        show (s.1.find? (fun e : UInt256 × UInt256 => compare k e.1)).map _
              = some p.2
        rw [h_findR]
        rfl
      rw [h] at hp_find
      cases hp_find
    simp [hpEq]
  -- Filter with all-true predicate equals the original list.
  rw [filter_eq_self_of_all hAll]

/-- **`findD`-flavored SSTORE bridge** (`≤`-form). Given the
`findD slot ⟨0⟩ = oldVal` shape produced by SLOAD-strong walks,
plus the bound `newVal ≤ oldVal`, the post-SSTORE storage-sum is
bounded by the pre-SSTORE storage-sum at `C`. Uniform in the
`newVal == 0` branch (erase) and `newVal ≠ 0` branch (replace). -/
theorem storageSum_sstore_replace_eq_findD
    (σ : AccountMap .EVM) (C : AccountAddress) (slot newVal oldVal : UInt256)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_findD : acc.storage.findD slot ⟨0⟩ = oldVal)
    (h_le : newVal.toNat ≤ oldVal.toNat) :
    storageSum (σ.insert C (acc.updateStorage slot newVal)) C
      ≤ storageSum σ C := by
  -- Case-split on `find? slot`.
  unfold Batteries.RBMap.findD at h_findD
  cases h_find_slot : acc.storage.find? slot with
  | some oldVal' =>
    rw [h_find_slot, Option.getD] at h_findD
    subst h_findD
    -- Decide on newVal == 0.
    by_cases hNewZero : (newVal == default) = true
    · -- Erase branch: post-storage is `acc.storage.erase slot`.
      have h_post_storage :
          (acc.updateStorage slot newVal).storage = acc.storage.erase slot := by
        unfold Account.updateStorage; simp [hNewZero]
      rw [storageSum_insert_at_C, h_post_storage,
          storageSum_of_find?_some σ C acc h_find]
      have h_delta := storageSum_storage_erase_eq acc.storage slot oldVal' h_find_slot
      omega
    · -- Replace branch.
      have hNonZero : (newVal == default) = false := by
        cases h : (newVal == default) with
        | true => exact absurd h hNewZero
        | false => rfl
      have h_delta := storageSum_sstore_replace_eq σ C slot newVal oldVal' hNonZero
                        acc h_find h_find_slot
      omega
  | none =>
    rw [h_find_slot, Option.getD] at h_findD
    -- h_findD : (⟨0⟩ : UInt256) = oldVal.
    subst h_findD
    -- newVal.toNat ≤ ⟨0⟩.toNat = 0, so newVal = ⟨0⟩.
    have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
    rw [h0] at h_le
    have hNewZero : newVal.toNat = 0 := Nat.le_zero.mp h_le
    have hNewVal_zero : newVal = ⟨0⟩ := by
      cases newVal with
      | mk v =>
        simp [UInt256.toNat] at hNewZero
        cases v
        simp_all
    subst hNewVal_zero
    -- Post-state storage is `acc.storage.erase slot`; with slot absent,
    -- the storage foldl-sum is preserved.
    rw [storageSum_insert_at_C, storageSum_of_find?_some σ C acc h_find,
        updateStorage_storage_of_zero acc slot]
    rw [storageSum_storage_erase_eq_of_find?_none acc.storage slot h_find_slot]

/-! ### `findD`-flavored insert-absent helper for the deposit slack form

Inserting at a key absent in the storage shifts the foldl-sum by
`+ newVal.toNat`. Used by the PC 40 deposit SSTORE discharger for the
absent-slot case (first-time depositors). -/

theorem storageSum_storage_insert_absent_eq
    (s : Storage) (k newVal : UInt256)
    (h_find : s.find? k = none) :
    (s.insert k newVal).foldl (fun a _ v => a + v.toNat) 0
      = s.foldl (fun a _ v => a + v.toNat) 0 + newVal.toNat := by
  rw [storageSum_foldl_eq_sum s, storageSum_foldl_eq_sum (s.insert k newVal)]
  obtain ⟨hOrd, _, _, hBal⟩ := s.2.out
  set cut : UInt256 × UInt256 → Ordering :=
    Ordering.byKey Prod.fst compare (k, newVal) with hcut_def
  match e : Batteries.RBNode.zoom cut s.1 with
  | (.nil, _p) =>
    obtain ⟨L₁, L₂, hToL_orig, hToL_ins⟩ :=
      Batteries.RBNode.exists_insert_toList_zoom_nil
        (cmp := Ordering.byKey Prod.fst compare) hBal e (v := (k, newVal))
    have hsToList : s.toList = s.1.toList := rfl
    have hsInsToList :
        (s.insert k newVal).toList
          = (s.1.insert (cmp := Ordering.byKey Prod.fst compare) (k, newVal)).toList := rfl
    rw [hsToList, hToL_orig, hsInsToList, hToL_ins]
    rw [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
        List.map_append, List.sum_append]
    ring
  | (.node _c _l ⟨kE, vE⟩ _r, _p) =>
    -- Node case: contradicts `find? k = none`.
    exfalso
    have hroot : s.1.find? cut = some (kE, vE) := by
      rw [Batteries.RBNode.find?_eq_zoom (p := .root), e]; rfl
    have h_find' : s.find? k = some vE := by
      show (s.1.find? (fun p => compare k p.1)).map (·.2) = some vE
      have hroot' : s.1.find? (fun p => compare k p.1) = some (kE, vE) := hroot
      rw [hroot']; rfl
    rw [h_find'] at h_find
    cases h_find

end Frame
end EvmYul

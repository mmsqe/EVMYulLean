import EvmYul.Venom.AbiLean.Args

/-!
# Kernel-reducible encoder (`CodecEval`)

`EvmAbi.encode`/`decode` (see `Codec.lean`, §3.3/§4.4 of the design report) are
defined by **well-founded** recursion over `Ty` (`termination_by`).  That keeps the
codec small and type-directed, but it compiles through `WellFounded.fix`/`Acc.rec`,
which the **kernel does not reduce** — so a concrete evaluation like
`encode (.uint 8) ⟨10, _⟩ = …` gets stuck under `decide`/`decide +kernel` and can
only be discharged by `native_decide` (adding a compiler-trust axiom).

This module provides a **fuel-indexed structural mirror** `encodeF` that recurses
on a `Nat` fuel argument, so it *does* reduce in the kernel.  The bridge theorem
`encodeF_eq_encode` proves that with enough fuel (`enoughE`) the mirror agrees with
`encode`.  Downstream, a concrete `encode` fact is proved on base axioms only by

```
rw [← encodeF_eq_encode F _ _ (by decide)]   -- swap encode for encodeF F (fuel ok by decide)
decide +kernel                                -- encodeF F reduces in the kernel
```

None of the verified roundtrip stack (`Codec.lean`) is touched: this is additive.
See design report §6.3.
-/

namespace EvmYul.Venom.AbiLean
open EvmAbi EvmAbi.Ty Binary

/-! ## Fuel-structural encoder

Every function in the block recurses structurally on the `fuel : Nat` argument
(decrementing on each recursive call), so the mutual block is accepted as
structural recursion — no `termination_by`, hence kernel-reducible.  The bytes
produced match `encode` exactly whenever the fuel suffices (`enoughE`, below). -/
mutual
/-- Fuel-indexed mirror of `encode`. -/
def encodeF : (fuel : Nat) → (t : Ty) → t.Val → List UInt8
  | 0, _, _ => []
  | f+1, t, v =>
    match t, v with
    | .uint _, ⟨n, _⟩ => encodeUint n
    | .int _, ⟨i, _⟩ => encodeInt i
    | .bool, b => encodeBool b
    | .address, ⟨n, _⟩ => encodeAddress n
    | .bytesN _, ⟨bs, _⟩ => encodeBytesN bs
    | .bytes, ⟨bs, _⟩ => encodeBytes bs
    | .string, ⟨s, _⟩ => encodeString s
    | .array t', ⟨vs, _⟩ => encodeUint vs.length ++ encodeParts (partsArrF f t' vs)
    | .fixedArray t' _, ⟨vs, _⟩ => encodeParts (partsArrF f t' vs)
    | .tuple ts, vs => encodeParts (partsTupF f ts vs)
/-- Fuel-indexed mirror of `vs.map (partOf t)` (array/fixed-array elements). -/
def partsArrF : (fuel : Nat) → (t : Ty) → List t.Val → List Part
  | 0, _, _ => []
  | _+1, _, [] => []
  | f+1, t, v :: vs => partOfF f t v :: partsArrF f t vs
/-- Fuel-indexed mirror of `partsOfTuple`. -/
def partsTupF : (fuel : Nat) → (ts : List Ty) → TupleVal ts → List Part
  | 0, _, _ => []
  | _+1, [], _ => []
  | f+1, t :: ts, (v, vs) => partOfF f t v :: partsTupF f ts vs
/-- Fuel-indexed mirror of `partOf`. -/
def partOfF : (fuel : Nat) → (t : Ty) → t.Val → Part
  | 0, _, _ => ⟨[], [], false⟩
  | f+1, t, v => match t.IsStatic with
    | true => ⟨encodeF f t v, [], false⟩
    | false => ⟨[], encodeF f t v, true⟩
end

/-! ## Fuel sufficiency

`enoughE f t v = true` exactly when `f` is large enough for `encodeF f t v` to
reach the same result as `encode t v`.  Aligned arm-for-arm with the encoder
above; itself fuel-structural, hence kernel-decidable (`by decide`). -/
mutual
/-- Fuel `f` suffices to encode `v : t.Val`. -/
def enoughE : (fuel : Nat) → (t : Ty) → t.Val → Bool
  | 0, _, _ => false
  | f+1, t, v =>
    match t, v with
    | .array t', ⟨vs, _⟩ => enoughArrE f t' vs
    | .fixedArray t' _, ⟨vs, _⟩ => enoughArrE f t' vs
    | .tuple ts, vs => enoughTupE f ts vs
    | _, _ => true
/-- Fuel `f` suffices for a list of array elements. -/
def enoughArrE : (fuel : Nat) → (t : Ty) → List t.Val → Bool
  | 0, _, [] => true
  | 0, _, _ :: _ => false
  | _+1, _, [] => true
  | f+1, t, v :: vs => enoughPartE f t v && enoughArrE f t vs
/-- Fuel `f` suffices for a tuple value. -/
def enoughTupE : (fuel : Nat) → (ts : List Ty) → TupleVal ts → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | _+1, [], _ => true
  | f+1, t :: ts, (v, vs) => enoughPartE f t v && enoughTupE f ts vs
/-- Fuel `f` suffices to place `v : t.Val` as a part. -/
def enoughPartE : (fuel : Nat) → (t : Ty) → t.Val → Bool
  | 0, _, _ => false
  | f+1, t, v => enoughE f t v
end

/-! ## Bridge

With enough fuel the fuel-encoder equals the well-founded encoder.  Proved by the
mutual structural induction principle `encodeF.induct` (four motives, one per
member of the fuel-encoder block). -/

/-- **Encoder bridge.** When `enoughE f t v`, the kernel-reducible `encodeF`
produces exactly `encode`'s bytes.  Additive: `encode` is unchanged. -/
theorem encodeF_eq_encode :
    ∀ (f : Nat) (t : Ty) (v : t.Val), enoughE f t v = true → encodeF f t v = encode t v := by
  apply encodeF.induct
    (motive_1 := fun f t v => enoughE f t v = true → encodeF f t v = encode t v)
    (motive_2 := fun f ts vs => enoughTupE f ts vs = true → partsTupF f ts vs = partsOfTuple ts vs)
    (motive_3 := fun f t v => enoughPartE f t v = true → partOfF f t v = partOf t v)
    (motive_4 := fun f t vs => enoughArrE f t vs = true → partsArrF f t vs = vs.map (partOf t))
  · intro t v h; simp [enoughE] at h
  · intro f m n hp _; simp only [encodeF, encode]
  · intro f m i hp _; simp only [encodeF, encode]
  · intro f v _; simp only [encodeF, encode]
  · intro f n hp _; simp only [encodeF, encode]
  · intro f bs _; simp only [encodeF, encode]
  · intro f v hp h; simp only [encodeF, encode]
  · intro f v hp h; simp only [encodeF, encode]
  · intro f t' v hp ih h
    simp only [enoughE] at h; simp only [encodeF, encode]; rw [ih h]
  · intro f t' vs ih h
    simp only [enoughE] at h; simp only [encodeF, encode]; rw [ih h]
  · intro f ts v ih h
    simp only [enoughE] at h; simp only [encodeF, encode]; rw [ih h]
  · intro ts vs h
    cases ts with
    | nil => simp only [partsTupF, partsOfTuple]
    | cons t ts => simp [enoughTupE] at h
  · intro n vs _; simp only [partsTupF, partsOfTuple]
  · intro f t ts v vs ih3 ih2 h
    simp only [enoughTupE, Bool.and_eq_true] at h
    simp only [partsTupF, partsOfTuple]; rw [ih3 h.1, ih2 h.2]
  · intro t v h; simp [enoughPartE] at h
  · intro f t v hs ih h
    simp only [enoughPartE] at h; simp only [partOfF, partOf, hs]; rw [ih h]
  · intro f t v hs ih h
    simp only [enoughPartE] at h; simp only [partOfF, partOf, hs]; rw [ih h]
  · intro t vs h
    cases vs with
    | nil => simp only [partsArrF, List.map_nil]
    | cons v vs => simp [enoughArrE] at h
  · intro n t _; simp only [partsArrF, List.map_nil]
  · intro f t v vs ih3 ih4 h
    simp only [enoughArrE, Bool.and_eq_true] at h
    simp only [partsArrF, List.map_cons]; rw [ih3 h.1, ih4 h.2]

/-- **Argument-level bridge.** Specialisation of `encodeF_eq_encode` to the
function-argument level (`encodeArgs = encode (.tuple ts)`), so a concrete
`encodeArgs` call rewrites to a kernel-reducible `encodeF`. -/
theorem encodeArgs_eq_encodeF (f : Nat) (ts : List Ty) (vs : TupleVal ts)
    (h : enoughE f (.tuple ts) vs = true) :
    encodeArgs ts vs = encodeF f (.tuple ts) vs := by
  rw [encodeArgs, encodeF_eq_encode f (.tuple ts) vs h]

end EvmYul.Venom.AbiLean

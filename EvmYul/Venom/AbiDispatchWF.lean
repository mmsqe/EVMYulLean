import EvmYul.Venom.AbiDispatch
import Mathlib.Tactic.IntervalCases

/-!
# Venom IR — ABI dispatcher well-formedness (symbolic `find?`)

Closes the last gap in the ABI front-end generator: for an *arbitrary* `cases`
list, the generated function resolves each dispatch block. The concrete case
computes by `rfl` (see `AbiDispatch.exFn_routes_*`); the symbolic case needs
the labels `dispLabel i = "__abidispatch" ++ toString i` to be distinct, i.e.
`Nat.toString` injective — proved here from the Batteries `toDigits`
recursion. Composing with `run_dispatch_routes` then gives an end-to-end
routing theorem `genABIFrontEnd_routes` for any method table.
-/

namespace Nat

/-- The digit characters `0`–`9` are distinct. -/
theorem digitChar_inj {a b : Nat} (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [Nat.digitChar]

/-- Base-10 digits of `n ≥ 10`: all but the last, then the last. -/
theorem toDigits_succ {n : Nat} (h : 10 ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [Nat.digitChar (n % 10)] := by
  have hq : 0 < n / 10 := Nat.div_pos h (by norm_num)
  have hd : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hkey := toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10) (by norm_num) hq hd
  rw [toDigits_of_lt_base hd] at hkey
  rw [hkey]; congr 1; omega

/-- Base-10 digit lists are injective. -/
theorem toDigits10_inj : ∀ a b, Nat.toDigits 10 a = Nat.toDigits 10 b → a = b := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hab
    rcases lt_or_ge a 10 with ha | ha <;> rcases lt_or_ge b 10 with hb | hb
    · rw [toDigits_of_lt_base ha, toDigits_of_lt_base hb] at hab
      exact digitChar_inj ha hb (by simpa using hab)
    · exfalso
      rw [toDigits_of_lt_base ha, toDigits_succ hb] at hab
      have hlen := congrArg List.length hab
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have hpos : 0 < (Nat.toDigits 10 (b / 10)).length := List.length_pos_iff.mpr Nat.toDigits_ne_nil; omega
    · exfalso
      rw [toDigits_succ ha, toDigits_of_lt_base hb] at hab
      have hlen := congrArg List.length hab
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have hpos : 0 < (Nat.toDigits 10 (a / 10)).length := List.length_pos_iff.mpr Nat.toDigits_ne_nil; omega
    · rw [toDigits_succ ha, toDigits_succ hb] at hab
      have hrev := congrArg List.reverse hab
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq] at hrev
      obtain ⟨hlast, hpre⟩ := hrev
      have hd : a % 10 = b % 10 :=
        digitChar_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hlast
      have hq : a / 10 = b / 10 :=
        ih (a / 10) (by omega) (b / 10) (by simpa using congrArg List.reverse hpre)
      omega

/-- `Nat.toString` is injective. -/
theorem toString_inj (a b : Nat) (h : toString a = toString b) : a = b :=
  toDigits10_inj a b (String.ofList_inj.mp h)

end Nat

namespace EvmYul.Venom.Abi

/-- Dispatch labels are distinct: `dispLabel` is injective. -/
theorem dispLabel_inj {i j : Nat} (h : dispLabel i = dispLabel j) : i = j := by
  apply Nat.toString_inj
  have hd := congrArg String.toList h
  simp only [dispLabel, String.toList_append] at hd
  exact String.toList_inj.mp (List.append_cancel_left hd)

/-- The dispatch chain resolves its `i`-th block by label. -/
theorem dispatchBlocks_find? : ∀ (cs : List (UInt256 × Label)) (start i : Nat) (hi : i < cs.length),
    (dispatchBlocks start cs).find? (fun bb => bb.label == dispLabel (start + i))
      = some (dispatchBlock (start + i) (cs[i].1) (cs[i].2)) := by
  intro cs
  induction cs with
  | nil => intro start i hi; simp at hi
  | cons c rest ih =>
    intro start i hi
    obtain ⟨sel, body⟩ := c
    rw [dispatchBlocks, List.find?_cons]
    cases i with
    | zero => simp [dispatchBlock]
    | succ k =>
      have hik : k < rest.length := by simp only [List.length_cons] at hi; omega
      have hne : dispLabel start ≠ dispLabel (start + (k + 1)) := fun heq => by
        have := dispLabel_inj heq; omega
      have hfalse : ((dispatchBlock start sel body).label == dispLabel (start + (k + 1))) = false := by
        simp only [dispatchBlock]; exact beq_eq_false_iff_ne.mpr hne
      simp only [hfalse]
      rw [show start + (k + 1) = (start + 1) + k from by omega]
      simpa using ih (start + 1) k hik

/-- **Symbolic `find?` well-formedness.** For any `cases`, the generated
function resolves the `i`-th dispatch block (given the entry label isn't a
dispatch label). This discharges the hypotheses `run_dispatch_routes` takes. -/
theorem genABIFrontEnd_find_dispatch (entryLbl : Label) (cs : List (UInt256 × Label))
    (bodies : List BasicBlock) (i : Nat) (hi : i < cs.length) (hentry : entryLbl ≠ dispLabel i) :
    (genABIFrontEnd entryLbl cs bodies).find? (dispLabel i)
      = some (dispatchBlock i (cs[i].1) (cs[i].2)) := by
  unfold genABIFrontEnd Function.find?
  simp only [List.find?_cons]
  have hentryfalse : ((entryBlock entryLbl).label == dispLabel i) = false := by
    simp only [entryBlock]; exact beq_eq_false_iff_ne.mpr hentry
  simp only [hentryfalse]
  rw [List.find?_append]
  have hdb := dispatchBlocks_find? cs 0 i hi
  simp only [Nat.zero_add] at hdb
  rw [hdb]; rfl

/-- **End-to-end routing for any method table.** With calldata's selector `V`
in `selVar`, a method table `before ++ (V, body) :: after` whose earlier
entries all differ from `V`, and an entry label distinct from every dispatch
label, `run` on the generated function routes from the dispatch head to the
matching `body` (with `selVar` + calldata preserved). -/
theorem genABIFrontEnd_routes (entryLbl : Label) (before after : List (UInt256 × Label))
    (V : UInt256) (body : Label) (bodies : List BasicBlock) (s : VenomState) (fuel : Nat)
    (hsel : s.env selVar = V)
    (hmiss : ∀ p ∈ before, p.1 ≠ V)
    (hfuel : before.length < fuel)
    (hentry : ∀ i, i < (before ++ (V, body) :: after).length → entryLbl ≠ dispLabel i) :
    ∃ s',
      run (genABIFrontEnd entryLbl (before ++ (V, body) :: after) bodies) fuel (dispLabel 0) s
        = run (genABIFrontEnd entryLbl (before ++ (V, body) :: after) bodies)
            (fuel - before.length - 1) body s'
        ∧ s'.env selVar = V ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage
        ∧ s'.caller = s.caller := by
  refine run_dispatch_routes _ V body before 0 s fuel hsel hmiss hfuel ?_ ?_
  · intro j hj
    have hjc : j < (before ++ (V, body) :: after).length := by
      rw [List.length_append, List.length_cons]; omega
    have hb := genABIFrontEnd_find_dispatch entryLbl (before ++ (V, body) :: after) bodies j hjc
      (hentry j hjc)
    rw [Nat.zero_add]
    rw [List.getElem_append_left hj] at hb
    exact hb
  · have hblt : before.length < (before ++ (V, body) :: after).length := by
      rw [List.length_append, List.length_cons]; omega
    have hb := genABIFrontEnd_find_dispatch entryLbl (before ++ (V, body) :: after) bodies
      before.length hblt (hentry before.length hblt)
    rw [Nat.zero_add]
    rw [List.getElem_append_right (Nat.le_refl _)] at hb
    simp only [Nat.sub_self, List.getElem_cons_zero] at hb
    exact hb

end EvmYul.Venom.Abi

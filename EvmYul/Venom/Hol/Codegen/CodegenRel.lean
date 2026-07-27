/-
Codegen Correctness Relations — Property Definitions

Port of vyper-hol/venom/codegen/defs/codegenRelScript.sml

Defines the three-layer correctness bridge:
  1. plan_state ↔ asm stack (plan_stack_rel, plan_spill_rel)
  2. VenomState ↔ AsmState (venom_asm_rel — THE LOOP INVARIANT)
  3. AsmState ↔ EVM bytecode (asm_evm_rel — simplified for our model)
  4. Result correspondence (asm_venom_result_rel, asm_evm_result_rel)

NO proofs — property definitions only.
-/

import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.Codegen.AsmIR
import EvmYul.Venom.Hol.Codegen.StackModel
import EvmYul.Venom.Hol.Codegen.PlanTypes
import EvmYul.Venom.Hol.Codegen.PlanOps
import EvmYul.Venom.Hol.Codegen.PlanExec
import EvmYul.Venom.Hol.Codegen.AsmSem
import EvmYul.UInt256
import EvmYul.Wheels
import Mathlib.Data.List.GetD
open EvmYul.Venom.Hol
open EvmYul.Venom.Hol.Codegen
open EvmYul (UInt256 AccountAddress)

namespace EvmYul.Venom.Hol.Codegen

/- ===== Operand Evaluation in Context ===== -/

/-- Evaluate an operand to bytes32, given venom vars and label offsets.
    Labels resolve to byte offsets from assembly (Nat → UInt256). -/
def operandVal (vs : VenomState) (labelOffsets : AssocList String Nat) : Operand → Option bytes32
  | Operand.Var v   => lookupVar v vs
  | Operand.Lit w   => some w
  | Operand.Label l =>
    match AssocList.lookup String Nat labelOffsets l with
    | some off => some (UInt256.ofNat off)
    | none => none

/-! ### `getElem!` bridge to `getElem?`

Lean's stdlib lacks an equation `l[i]! = (l[i]?).getD default` usable by
`simp only` (the `getElem!` instance doesn't unfold under `simp only`).
This bridge lets us rewrite `get!` into `getElem?` form so the
`getElem?_reverse` / `getElem?_set'` lemmas apply. -/

theorem getElem!_eq_getElem?_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = (l[i]?).getD default := by
  cases h : l[i]?
  · simp [h]
  · simp [h]

/-- Bridge for the (deprecated) `List.get!` used by `planStackRel`:
    `l[i]! = l.getD i default = (l[i]?).getD default`. -/
theorem List_get!_eq_getElem?_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = (l[i]?).getD default := by
  cases h : l[i]?
  · simp [getElem!_def, h]
  · simp [getElem!_def, h]

/-- Bridge: `l.getD i default = (l[i]?).getD default` (definitional). -/
theorem getD_eq_getElem?_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l.getD i default = (l[i]?).getD default := rfl

/-- Direct bridge `l[i]! = l.getD i default` (the v4.31 replacement for the old
    `List.get!_eq_getD`; `getElem!_def` unfolds to a `match`, not `getD`). -/
theorem getElem!_eq_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = l.getD i default := by
  rw [getElem!_eq_getElem?_getD, getD_eq_getElem?_getD]

lemma getD_set_at_otherpos {α : Type} [Inhabited α] (l : List α) (i j : Nat) (a : α)
    (hne : i ≠ j) (hj : j < l.length) : (l.set i a).getD j default = l.getD j default := by
  rw [getD_eq_getElem?_getD, List.getElem?_set', if_neg hne, getD_eq_getElem?_getD]

lemma getD_set_at_setpos {α : Type} [Inhabited α] (l : List α) (i : Nat) (a : α) (hj : i < l.length) :
    (l.set i a).getD i default = a := by
  rw [getD_eq_getElem?_getD, List.getElem?_set', List.getElem?_eq_getElem (h := hj)]
  simp

/- ===== Plan State ↔ Concrete Stack ===== -/

/-- `psStack` (LAST=TOS) matches `asmStack` (HD=TOS).
    Full version (mirrors HOL `plan_stack_rel`): the stacks have equal length
    and, for every position `i` measured from TOS, the operand
    `psStack.reverse[i]!` (venom stack is LAST=TOS, so reversing puts TOS at
    index 0, aligning with `asmStack[i]!` where HD=TOS) evaluates under
    `operandVal` to the value `asmStack[i]!`. Using `get!` (default on OOB)
    avoids embedding `Fin` proof terms in the definition; the `i < length`
    binder makes `get!` return the real element. -/
def planStackRel (labelOffsets : AssocList String Nat) (vs : VenomState)
    (psStack : List Operand) (asmStack : List bytes32) : Prop :=
  psStack.length = asmStack.length ∧
  ∀ i, i < psStack.length →
    operandVal vs labelOffsets (psStack.reverse[i]!) = some (asmStack[i]!)

/-- `planStackRel` implies equal lengths. -/
theorem planStackRel_length {labelOffsets vs psStack asmStack}
    (h : planStackRel labelOffsets vs psStack asmStack) :
    psStack.length = asmStack.length :=
  h.1

/-- `planStackRel` gives the element at distance `dist` from TOS in `stackPeek`
    / `get!` form. `stackPeek dist psStack = psStack.reverse[dist]!` (TOS is
    last), and the corresponding asm entry is `asmStack[dist]!` (HD=TOS). -/
theorem planStackRel_peek {labelOffsets vs psStack asmStack dist}
    (h : planStackRel labelOffsets vs psStack asmStack) (hdist : dist < psStack.length) :
    operandVal vs labelOffsets (stackPeek dist psStack) = some (asmStack[dist]!) := by
  have hlen := h.1
  have hrel := h.2 dist hdist
  -- stackPeek dist psStack = psStack[psStack.length - 1 - dist]!
  -- psStack.reverse[dist]! = psStack[psStack.length - 1 - dist]!  (by reverse indexing)
  have heq : stackPeek dist psStack = psStack.reverse[dist]! := by
    simp only [stackPeek]
    rw [getElem!_pos psStack.reverse dist (by simpa using hdist),
        getElem!_pos psStack _ (by omega), List.getElem_reverse]
  rw [heq]
  exact hrel

/-! ### The phi's poke, and why a join may be compiled against one predecessor

A join with two or more predecessors gets no stack reconciliation and is compiled against whichever
predecessor the plan DFS reached first. Entering it from a *different* predecessor, `planStackRel`
genuinely **fails** at the phi slot: the recorded plan stack names the compiled-against edge's source
(say `a`), and on this path `a` was never assigned, so `operandVal` there is `none` — not the value in
the asm slot.

The phi is what repairs it, and the repair is exact. Its plan emits no EVM code (`SOPoke` is a
plan-only rename), so the asm stack is untouched; the Venom side binds the phi output `p` to the value
arriving on *this* edge — which is precisely the value already sitting in that asm slot, because every
predecessor delivers its own source at the same depth (`stackGetPhiDepth_congr`). Poking the slot to
`p` therefore makes the two sides agree there, and everywhere else the relation already held and is
undisturbed.

So the relation to carry *into* a join is the one **after** the phis, not before: pre-phi it is false
on every edge except the compiled-against one; post-phi it is true on all of them.

`planStackRel_phi_poke` (in `GenBlockSimComp`) already carries the rename through on the
compiled-against edge, but it *assumes* the relation holds beforehand, so it says nothing about the
other edges. `planStackRel_phi_poke_offSlot` below asks only for what is true on all of them. -/

/-- Poking at depth `d` sets exactly index `d` of the TOS-first view. -/
theorem stackPoke_reverse {s : List Operand} {d : Nat} {op : Operand} (hd : d < s.length) :
    (stackPoke d op s).reverse = s.reverse.set d op := by
  unfold stackPoke
  dsimp only
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_reverse, List.length_set] at h1 h2
    rw [List.getElem_reverse, List.getElem_set, List.getElem_set]
    simp only [List.length_set]
    rcases eq_or_ne i d with rfl | h
    · simp
    · have hne : s.length - 1 - d ≠ s.length - 1 - i := by
        intro heq; exact h (by omega)
      rw [if_neg hne, if_neg (Ne.symm h), List.getElem_reverse]

/-- Reading the TOS-first view of a poked stack: depth `d` reads the new operand, every other depth is
unchanged. -/
theorem stackPoke_reverse_getElem! {s : List Operand} {d i : Nat} {op : Operand}
    (hd : d < s.length) (hi : i < s.length) :
    (stackPoke d op s).reverse[i]! = if i = d then op else s.reverse[i]! := by
  rw [stackPoke_reverse hd]
  rcases eq_or_ne i d with rfl | h
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_set_self, if_pos rfl]
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_set_ne (Ne.symm h), if_neg h,
        ← getElem!_pos _ _ (by simpa using hi)]

/-- **A block's whole phi prologue establishes `planStackRel`** — on the arrival of a predecessor the
join was *not* compiled against, where the relation does **not** hold beforehand.

`planStackRel_phi_poke` (in `GenBlockSimComp`) handles the compiled-against edge: it *assumes* the full
relation already holds, with that edge's own source named in the slot, and carries it through the
rename. On any other edge that assumption is false — the slot names a variable this path never assigned
— so that lemma does not apply.

It also matters that this is stated for **all** the phis at once. A join may carry several, each owning
one slot, and on the other edge the relation fails at *every* one of them simultaneously. So a
single-phi lemma cannot simply be iterated: its "relation holds off *the* slot" hypothesis is still
false while any other phi slot is unrepaired. The phis have to be taken together — assume the relation
off the whole set of phi slots, and that each phi binds its output to the value that slot actually
received; poking them all then restores the relation everywhere.

No distinctness of the depths is needed: if two phis named the same slot the later poke simply wins,
and that phi's hypothesis is the one that has to hold.

This is the semantic reason a join can be compiled once and still be correct on every incoming edge. -/
theorem planStackRel_phi_pokes {labelOffsets : AssocList String Nat} {vs : VenomState}
    {asmStack : List bytes32} :
    ∀ (dps : List (Nat × String)) (psStack : List Operand),
      psStack.length = asmStack.length →
      (∀ dp ∈ dps, dp.1 < psStack.length) →
      (∀ i, i < psStack.length → (∀ dp ∈ dps, i ≠ dp.1) →
          operandVal vs labelOffsets (psStack.reverse[i]!) = some (asmStack[i]!)) →
      (∀ dp ∈ dps, operandVal vs labelOffsets (Operand.Var dp.2) = some (asmStack[dp.1]!)) →
      planStackRel labelOffsets vs
        (dps.foldl (fun s dp => stackPoke dp.1 (Operand.Var dp.2) s) psStack) asmStack := by
  intro dps
  induction dps with
  | nil =>
    intro psStack hlen _ hoff _
    exact ⟨hlen, fun i hi => hoff i hi (by simp)⟩
  | cons dp rest ih =>
    intro psStack hlen hdlt hoff hp
    simp only [List.foldl_cons]
    have hd : dp.1 < psStack.length := hdlt dp (by simp)
    have hlen' : (stackPoke dp.1 (Operand.Var dp.2) psStack).length = psStack.length := by
      simp [stackPoke]
    refine ih (stackPoke dp.1 (Operand.Var dp.2) psStack) (by rw [hlen']; exact hlen)
      (fun q hq => by rw [hlen']; exact hdlt q (List.mem_cons_of_mem _ hq)) ?_ ?_
    · -- the relation now holds off the *remaining* phi slots: this phi's slot is repaired
      intro i hi hne
      rw [hlen'] at hi
      rw [stackPoke_reverse_getElem! hd hi]
      rcases eq_or_ne i dp.1 with rfl | hid
      · rw [if_pos rfl]; exact hp dp (by simp)
      · rw [if_neg hid]
        refine hoff i hi ?_
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hqr
        · exact hid
        · exact hne q hqr
    · intro q hq; exact hp q (List.mem_cons_of_mem _ hq)

/-- The single-phi case — the one-element instance of `planStackRel_phi_pokes`. -/
theorem planStackRel_phi_poke_offSlot {labelOffsets : AssocList String Nat} {vs : VenomState}
    {psStack : List Operand} {asmStack : List bytes32} {d : Nat} {p : String}
    (hlen : psStack.length = asmStack.length)
    (hd : d < psStack.length)
    (hoff : ∀ i, i < psStack.length → i ≠ d →
        operandVal vs labelOffsets (psStack.reverse[i]!) = some (asmStack[i]!))
    (hp : operandVal vs labelOffsets (Operand.Var p) = some (asmStack[d]!)) :
    planStackRel labelOffsets vs (stackPoke d (Operand.Var p) psStack) asmStack := by
  have := planStackRel_phi_pokes (labelOffsets := labelOffsets) (vs := vs) (asmStack := asmStack)
    [(d, p)] psStack hlen (by simpa using hd)
    (fun i hi hne => hoff i hi (by simpa using hne (d, p) (by simp)))
    (by simpa using hp)
  simpa using this

/-- `planStackRel` is preserved by a swap of TOS with the element at distance
    `dist`: venom `stackSwap dist psStack` (LAST=TOS) corresponds to asm
    swapping `asStack[0]` (HD=TOS) with `asStack[dist]`. The two swapped
    positions stay in correspondence; all other positions are untouched. -/
theorem planStackRel_swap {labelOffsets vs psStack asmStack dist}
    (h : planStackRel labelOffsets vs psStack asmStack)
    (hdist : 0 < dist) (hdist' : dist < psStack.length) :
    planStackRel labelOffsets vs (stackSwap dist psStack)
      ((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!)) := by
  have hlen := h.1
  refine ⟨?_, ?_⟩
  · -- stackSwap doesn't change length; asm set 0 / set dist preserve length
    rw [stackSwap, List.length_set, List.length_set, List.length_set, List.length_set, hlen]
  · intro i hi
    -- (stackSwap dist psStack).reverse[i]!  vs  ((asmStack.set 0 ..).set dist ..)[i]!
    -- swap exchanges TOS (index 0 from TOS) with position dist. Three cases.
    have hlen' : (stackSwap dist psStack).length = psStack.length := by
      rw [stackSwap, List.length_set, List.length_set]
    have hi0 : i < psStack.length := by rw [← hlen']; exact hi
    have hiA : i < asmStack.length := by omega
    have horig : operandVal vs labelOffsets (psStack.reverse[i]!) = some (asmStack[i]!) :=
      h.2 i hi0
    by_cases h0 : i = 0
    · -- i = 0: new TOS = old dist
      have h0A : 0 < asmStack.length := by omega
      have hdA : dist < asmStack.length := by omega
      have h0p : 0 < psStack.length := by omega
      have hdp : dist < psStack.length := hdist'
      have hpeA : ((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[0]! =
                  asmStack[dist]! := by
        have hne : 0 ≠ dist := by omega
        have hne' : dist ≠ 0 := by omega
        simp [List.getElem?_set', h0, hne, hne',
          List.getElem?_eq_getElem (h := h0A), List.getElem?_eq_getElem (h := hdA)]
      have hpeV : (stackSwap dist psStack).reverse[0]! = psStack.reverse[dist]! := by
        rw [List_get!_eq_getElem?_getD, List_get!_eq_getElem?_getD, stackSwap]
        -- LHS: ((set (len-1) X).set (len-1-dist) Y).reverse[0]?
        --   = ((set/set))[(set/set).length - 1]?   by getElem?_reverse
        --   = ((set/set))[len-1]?                   since (set/set).length = len
        have hLm : (psStack.length - 1 - dist) < psStack.length := by omega
        have hL : (psStack.length - 1) < psStack.length := by omega
        have hne1 : (psStack.length - 1 - dist) ≠ (psStack.length - 1) := by omega
        have hne1' : (psStack.length - 1) ≠ (psStack.length - 1 - dist) := by omega
        have hlenSS : ((psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!)).set
                        (psStack.length - 1 - dist) (psStack[psStack.length - 1]!)).length =
                      psStack.length := by rw [List.length_set, List.length_set]
        rw [List.getElem?_reverse (h := by rw [hlenSS]; exact h0p)]
        -- index: ((set/set).length - 1 - 0) = (psStack.length - 1)
        rw [hlenSS]
        -- now LHS: ((set (len-1) X).set (len-1-dist) Y)[psStack.length - 1]?
        -- outer set at (len-1-dist): (len-1-dist) ≠ (len-1) → else
        rw [List.getElem?_set']
        simp [if_neg hne1, hne1']
        -- inner (set (len-1) X)[len-1]? → if (len-1)=(len-1) then some X else ...
        rw [List.getElem?_set',
          if_pos (show (psStack.length - 1) = (psStack.length - 1) from rfl),
          List.getElem?_eq_getElem (h := hL)]
        -- now: (Function.const X <$> some psStack[len-1]).getD default
        -- X = (some psStack[len-1-dist]).getD default = psStack[len-1-dist]
        simp [Function.const, Option.getD]
        -- RHS: psStack.reverse[dist]? → psStack[len-1-dist]?  (by getElem?_reverse)
        rw [List.getElem?_reverse (h := hdist')]
      rw [h0, hpeV, hpeA]; exact h.2 dist hdist'
    · by_cases hd : i = dist
      · have h0A : 0 < asmStack.length := by omega
        have hdA : dist < asmStack.length := by omega
        have h0p : 0 < psStack.length := by omega
        have hdp : dist < psStack.length := hdist'
        have hpeA : ((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[dist]! =
                    asmStack[0]! := by
          have hne : 0 ≠ dist := by omega
          have hne' : dist ≠ 0 := by omega
          simp [List.getElem?_set', hd, hne, hne',
            List.getElem?_eq_getElem (h := h0A), List.getElem?_eq_getElem (h := hdA)]
        have hpeV : (stackSwap dist psStack).reverse[dist]! = psStack.reverse[0]! := by
          have hLenSwap : (stackSwap dist psStack).length = psStack.length := by
            rw [stackSwap, List.length_set, List.length_set]
          have hDRevLHS : (stackSwap dist psStack).reverse[dist]! = 
                          (stackSwap dist psStack)[psStack.length - 1 - dist]! := by
            calc
              (stackSwap dist psStack).reverse[dist]!
                  = (stackSwap dist psStack).reverse.getD dist default := by rw [getElem!_eq_getD]
              _ = (stackSwap dist psStack).getD ((stackSwap dist psStack).length - 1 - dist) default :=
                congrArg (· default) (List.getD_reverse (i := dist) (h := by rw [hLenSwap]; exact hdp)
                  (l := (stackSwap dist psStack)))
              _ = (stackSwap dist psStack).getD (psStack.length - 1 - dist) default := by rw [hLenSwap]
              _ = (stackSwap dist psStack)[psStack.length - 1 - dist]! := by rw [getElem!_eq_getD]
          have hDRevRHS : psStack.reverse[0]! = psStack[psStack.length - 1]! := by
            calc
              psStack.reverse[0]!
                  = psStack.reverse.getD 0 default := by rw [getElem!_eq_getD]
              _ = psStack.getD (psStack.length - 1 - 0) default :=
                congrArg (· default) (List.getD_reverse (i := 0) (h := h0p) (l := psStack))
              _ = psStack.getD (psStack.length - 1) default := by
                rw [show psStack.length - 1 - 0 = psStack.length - 1 from by omega]
              _ = psStack[psStack.length - 1]! := by rw [getElem!_eq_getD]
          rw [hDRevLHS, getElem!_eq_getD, show (stackSwap dist psStack).getD (psStack.length - 1 - dist) default = 
            ((psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!)).set
              (psStack.length - 1 - dist) (psStack[psStack.length - 1]!)).getD
              (psStack.length - 1 - dist) default by
              unfold stackSwap; simp,]
          -- Prove directly: (set (len-1-dist) Y).getD (len-1-dist) default = Y = psStack[len-1]!
          have hSetAt : ((psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!)).set
                          (psStack.length - 1 - dist) (psStack[psStack.length - 1]!)).getD
                          (psStack.length - 1 - dist) default = psStack[psStack.length - 1]! :=
            getD_set_at_setpos (psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!))
              (psStack.length - 1 - dist) (psStack[psStack.length - 1]!)
              (by
                have hL : (psStack.length - 1 - dist) < (psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!)).length := by
                  rw [List.length_set]; omega
                exact hL)
          rw [hSetAt, hDRevRHS.symm]
        calc
          operandVal vs labelOffsets ((stackSwap dist psStack).reverse[i]!)
              = operandVal vs labelOffsets ((stackSwap dist psStack).reverse[dist]!) := by rw [hd]
          _ = operandVal vs labelOffsets (psStack.reverse[0]!) := by rw [hpeV]
          _ = some (asmStack[0]!) := h.2 0 h0p
          _ = some (((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[dist]!) := by rw [hpeA]
          _ = some (((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[i]!) := by rw [hd]
      · have h0A : 0 < asmStack.length := by omega
        have hdA : dist < asmStack.length := by omega
        have h0p : 0 < psStack.length := by omega
        have hpeA : ((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[i]! =
                    asmStack[i]! := by
          have hne : 0 ≠ dist := by omega
          have hne' : dist ≠ 0 := by omega
          have hne_di : dist ≠ i := by omega
          have hne_0i : 0 ≠ i := by omega
          simp [List.getElem?_set', h0, hd, hne, hne', hne_di, hne_0i,
            List.getElem?_eq_getElem (h := h0A), List.getElem?_eq_getElem (h := hdA),
            List.getElem?_eq_getElem (h := hiA)]
        have hpeV : (stackSwap dist psStack).reverse[i]! = psStack.reverse[i]! := by
          rw [getElem!_eq_getD, getElem!_eq_getD,
            congrArg (· default) (List.getD_reverse (i := i) (h := by
                rw [hlen']; exact hi0) (l := (stackSwap dist psStack))),
            congrArg (· default) (List.getD_reverse (i := i) (h := hi0) (l := psStack)),
            hlen']
          have hiL : psStack.length - 1 - i < psStack.length := by omega
          have hne1 : (psStack.length - 1) ≠ (psStack.length - 1 - i) := by omega
          have hne2 : (psStack.length - 1 - dist) ≠ (psStack.length - 1 - i) := by omega
          unfold stackSwap
          rw [getD_set_at_otherpos (psStack.set (psStack.length - 1) (psStack[psStack.length - 1 - dist]!))
          (psStack.length - 1 - dist) (psStack.length - 1 - i) (psStack[psStack.length - 1]!) hne2
          (by rw [List.length_set]; exact hiL),
            getD_set_at_otherpos psStack (psStack.length - 1) (psStack.length - 1 - i)
            (psStack[psStack.length - 1 - dist]!) hne1 hiL]
        calc
          operandVal vs labelOffsets ((stackSwap dist psStack).reverse[i]!)
              = operandVal vs labelOffsets (psStack.reverse[i]!) := congrArg _ hpeV
          _ = some (asmStack[i]!) := horig
          _ = some (((asmStack.set 0 (asmStack[dist]!)).set dist (asmStack[0]!))[i]!) := by rw [← hpeA]

/-- Each spilled operand's value is stored at its memory offset (32-byte big-endian). -/
def planSpillRel (labelOffsets : AssocList String Nat) (vs : VenomState)
    (psSpilled : SpilledMap) (asmMemory : ByteArray) : Prop :=
  ∀ op off, AssocList.lookup Operand Nat psSpilled op = some off →
    ∃ v, operandVal vs labelOffsets op = some v ∧
         wordOfBytes (asmMemory.readWithPadding off 32) = v

/- ===== Memory Relations ===== -/

/-- Read byte with implicit zero-padding (EVM memory is zero-initialized). -/
def readByte (i : Nat) (mem : ByteArray) : byte :=
  if h : i < mem.size then mem.get i h else 0

/-- Memories agree outside the spill region [fnEom, nextOffset).
    The spill allocator starts at fn_eom and grows upward.
    MEMTOP is excluded from correspondence — asm memory may be longer. -/
def memoryRel (alloc : SpillAlloc) (venomMem asmMem : ByteArray) : Prop :=
  ∀ i, ¬(alloc.fnEom ≤ i ∧ i < alloc.nextOffset) →
    readByte i venomMem = readByte i asmMem

/- ===== Spill Safety Conditions ===== -/

/-- A Venom step doesn't modify memory in the spill region.
    Required per-instruction so plan_spill_rel is maintained.
    For Vyper-generated code: user allocations below fn_eom, holds by construction. -/
def stepMemSafe (alloc : SpillAlloc) (vs vs' : VenomState) : Prop :=
  ∀ i, alloc.fnEom ≤ i ∧ i < alloc.nextOffset →
    readByte i vs.memory = readByte i vs'.memory

/-- Memory is pre-expanded to cover the spill high-water mark. -/
def spillMemCovered (spillHwm : Nat) (mem : ByteArray) : Prop :=
  spillHwm ≤ mem.size

/- ===== THE LOOP INVARIANT: VenomState ↔ AsmState ===== -/

/--
Full Venom ↔ asm state relation. This is the LOOP INVARIANT for
block-by-block simulation. Parameterized by plan_state which tracks
stack layout. NOT used for terminal states — see venom_asm_terminal_rel.
-/
def venomAsmRel (labelOffsets : AssocList String Nat) (ps : PlanState)
    (vs : VenomState) (as : AsmState) : Prop :=
  planStackRel labelOffsets vs ps.stack as.stack ∧
  planSpillRel labelOffsets vs ps.spilled as.memory ∧
  memoryRel ps.alloc vs.memory as.memory ∧
  -- Shared mutable state
  as.accounts = vs.accounts ∧
  as.transient = vs.transient ∧
  as.returndata = vs.returndata ∧
  as.logs = vs.logs ∧
  -- Shared environment
  as.callCtx = vs.callCtx ∧
  as.txCtx = vs.txCtx ∧
  as.blockCtx = vs.blockCtx ∧
  as.code = vs.code ∧
  as.prevHashes = vs.prevHashes

/-- Terminal state: observable effects match at halt/revert.
    No plan_state, no stack layout, no memory details. -/
def venomAsmTerminalRel (vs : VenomState) (as : AsmState) : Prop :=
  as.accounts = vs.accounts ∧
  as.transient = vs.transient ∧
  as.returndata = vs.returndata ∧
  as.logs = vs.logs

/-- venom_asm_rel implies venom_asm_terminal_rel. -/
theorem venomAsmRel_terminal (lo ps vs as) (h : venomAsmRel lo ps vs as) : venomAsmTerminalRel vs as := by
  rcases h with ⟨_, _, _, hacc, htr, hrd, hlog, _, _, _, _, _⟩
  exact ⟨hacc, htr, hrd, hlog⟩

/- ===== Function Entry ===== -/

/-- Initial plan state with function parameters pre-loaded on ps_stack.
    At function entry, asm stack has args (first param deepest, last param TOS). -/
def fnInitPs (fn : IrFunction) (fnEom : Nat) : PlanState :=
  initPlanState fnEom

/- ===== Result Correspondence ===== -/

/-- asm_result corresponds to Venom exec_result.
    Uses terminal_rel: at halt/revert, only observable effects matter. -/
def asmVenomResultRel (ar : AsmResult) (vr : ExecResult) : Prop :=
  match ar, vr with
  | AsmResult.AsmHalt as, ExecResult.Halt vs =>
      venomAsmTerminalRel vs as
  | AsmResult.AsmRevert as, ExecResult.Abort AbortType.RevertAbort vs =>
      venomAsmTerminalRel vs as
  | AsmResult.AsmFault as, ExecResult.Abort AbortType.ExHaltAbort vs =>
      venomAsmTerminalRel vs as
  | _, _ => False

/-- asm_result corresponds to EVM execution result (simplified).
    In our model, asm execution IS the EVM execution — no separate bridge needed.
    ar corresponds to some AsmResult from runAsm. -/
def asmEvmResultRel (_prog : List AsmInst) (ar : AsmResult) : Prop :=
  match ar with
  | AsmResult.AsmHalt _ => True
  | AsmResult.AsmRevert _ => True
  | AsmResult.AsmFault _ => True
  | _ => False

end EvmYul.Venom.Hol.Codegen

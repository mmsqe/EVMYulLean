import EvmYul.Venom.Semantics
import EvmYul.Venom.AbiBridge

/-!
# Venom IR — ABI front-end generator (selector dispatch)

The long-term half of the ABI integration: generate the entry prologue every
real ERC-20-style contract has — read the 4-byte selector from calldata,
compare it against each method's selector, and route to that method's body —
and prove the routing correct against the real `run` semantics.

`genABIFrontEnd` assembles
* an **entry block** that extracts `selVar := shr 224 (calldataload 0)` and
  jumps into the dispatch chain (`entryBlock`);
* a **dispatch chain** `dispatchBlocks`: one block per method comparing
  `selVar` to the method's selector and branching to its body or the next
  case, ending in a revert **fallback**;
* the **method bodies** (given), each of which decodes its arguments via the
  proved `AbiBridge` bridge lemmas (`calldataload_transfer_*`).

Correctness factors into three independent pieces:
1. **selector extraction** — `shr 224 (calldataload 0)` recovers the selector
   from `beBytesN 4 sel ++ args` (`AbiSelector.calldataSelector_selectorBytes`);
2. **routing** — the dispatch chain routes `selVar = V` to the matching body
   (`run_dispatchBlock_match` / `_miss` → `run_dispatch_routes`, proved here);
3. **arg decode** — the body reads its arguments (`AbiBridge`, proved).

This file proves piece 2 (the per-block routing recurrences and their
whole-chain induction); `AbiDispatchWF` discharges `find?` for symbolic method
tables, and `AbiEndToEnd` joins the entry block to piece 1.
-/

namespace EvmYul.Venom

namespace Abi

/-- Variable holding the word read from calldata offset 0. -/
def cd0Var : VarName := "%__abicd0"
/-- Variable holding the extracted 4-byte selector. -/
def selVar : VarName := "%__abisel"
/-- Comparison-result variable for dispatch case `i`. -/
def cmpVar (i : Nat) : VarName := "%__abicmp" ++ toString i
/-- Label of dispatch block `i` (case `i`, or the fallback when `i` is the
number of cases). -/
def dispLabel (i : Nat) : Label := "__abidispatch" ++ toString i

/-- The entry prologue: extract the selector and jump into the chain. -/
def entryBlock (entryLbl : Label) : BasicBlock :=
  { label := entryLbl,
    instrs :=
      [ { output := some cd0Var, opcode := .calldataload, operands := [.lit (UInt256.ofNat 0)] },
        { output := some selVar, opcode := .shr, operands := [.lit (UInt256.ofNat 224), .var cd0Var] },
        { opcode := .jmp, operands := [.label (dispLabel 0)] } ] }

/-- One dispatch block for case `i`: `cmp = eq selVar sel; jnz cmp, @body,
@dispLabel(i+1)`. -/
def dispatchBlock (i : Nat) (sel : UInt256) (body : Label) : BasicBlock :=
  { label := dispLabel i,
    instrs :=
      [ { output := some (cmpVar i), opcode := .eq, operands := [.var selVar, .lit sel] },
        { opcode := .jnz, operands := [.var (cmpVar i), .label body, .label (dispLabel (i + 1))] } ] }

/-- The dispatch chain: one block per case, ending in a revert fallback at
`dispLabel n`. -/
def dispatchBlocks : Nat → List (UInt256 × Label) → List BasicBlock
  | i, [] =>
      [ { label := dispLabel i,
          instrs := [ { opcode := .revert,
                        operands := [.lit (UInt256.ofNat 0), .lit (UInt256.ofNat 0)] } ] } ]
  | i, (sel, body) :: rest => dispatchBlock i sel body :: dispatchBlocks (i + 1) rest

/-- Assemble the ABI front end: entry prologue ++ dispatch chain ++ bodies. -/
def genABIFrontEnd (entryLbl : Label) (cases : List (UInt256 × Label))
    (bodies : List BasicBlock) : Function :=
  { entry := entryLbl,
    blocks := entryBlock entryLbl :: (dispatchBlocks 0 cases ++ bodies) }

/-! ## Dispatch-block correctness -/

/-- Running a generated dispatch block computes the selector comparison and
branches to `body` on a match, else to the next case. -/
theorem execBlock_dispatchBlock (s : VenomState) (i : Nat) (sel : UInt256) (body : Label) :
    execBlock s (dispatchBlock i sel body).instrs
      = (s.set (cmpVar i) (UInt256.eq (s.env selVar) sel),
         Control.branch (UInt256.eq (s.env selVar) sel) body (dispLabel (i + 1))) := by
  simp only [dispatchBlock, execBlock, execInstr, evalPure, evalBin, Operand.evalEnv,
    VenomState.setOutput, List.map, VenomState.set_env_self]

/-- `eq a a` is the truthy word (1), so it is not zero. -/
theorem eq_self_ne_zero (a : UInt256) : (UInt256.eq a a == UInt256.ofNat 0) = false := by
  have : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq]
  rw [this]; decide

/-- `eq a b` with `a ≠ b` is zero. -/
theorem eq_ne_zero {a b : UInt256} (h : a ≠ b) : (UInt256.eq a b == UInt256.ofNat 0) = true := by
  have : UInt256.eq a b = UInt256.ofNat 0 := by simp [UInt256.eq, h]
  rw [this]; decide

/-! ## Routing recurrences (over the real `run` interpreter) -/

/-- **Dispatch match.** When `selVar` holds the case's selector and the
function resolves this block, `run` steps into the method body. -/
theorem run_dispatchBlock_match (fn : Function) (fuel i : Nat) (sel : UInt256)
    (body : Label) (s : VenomState)
    (hfind : fn.find? (dispLabel i) = some (dispatchBlock i sel body))
    (hmatch : s.env selVar = sel) :
    run fn (fuel + 1) (dispLabel i) s
      = run fn fuel body
          { s.set (cmpVar i) (UInt256.eq (s.env selVar) sel) with prevBlock := dispLabel i } := by
  simp only [run, hfind, execBlock_dispatchBlock, hmatch, eq_self_ne_zero, Bool.false_eq_true,
    if_false]

/-- **Dispatch miss.** When `selVar` does not hold the case's selector, `run`
falls through to the next case. -/
theorem run_dispatchBlock_miss (fn : Function) (fuel i : Nat) (sel : UInt256)
    (body : Label) (s : VenomState)
    (hfind : fn.find? (dispLabel i) = some (dispatchBlock i sel body))
    (hmiss : s.env selVar ≠ sel) :
    run fn (fuel + 1) (dispLabel i) s
      = run fn fuel (dispLabel (i + 1))
          { s.set (cmpVar i) (UInt256.eq (s.env selVar) sel) with prevBlock := dispLabel i } := by
  simp only [run, hfind, execBlock_dispatchBlock, eq_ne_zero hmiss, if_true]

/-! ## Whole-chain routing

The dispatch variable `selVar` is disjoint from every comparison variable
`cmpVar i`, so it survives the writes a run of misses makes; iterating the two
recurrences then routes the chain head to the matching case's body. -/

/-- The selector variable is never a comparison variable (different fixed
prefix, so the strings differ regardless of the index). -/
theorem selVar_ne_cmpVar (i : Nat) : selVar ≠ cmpVar i := by
  intro h
  have hd : selVar.toList = ("%__abicmp" ++ toString i).toList := congrArg String.toList h
  rw [String.toList_append] at hd
  have hlen := congrArg List.length hd
  simp only [List.length_append,
             show ("%__abisel" : String).toList.length = 9 from by decide,
             show ("%__abicmp" : String).toList.length = 9 from by decide, selVar] at hlen
  have h0 : (toString i).toList = [] := by rw [← List.length_eq_zero_iff]; omega
  rw [h0, List.append_nil] at hd
  exact absurd hd (by decide)

/-- Writing a comparison variable leaves `selVar` unchanged. -/
theorem set_cmpVar_selVar (s : VenomState) (i : Nat) (v : UInt256) :
    (s.set (cmpVar i) v).env selVar = s.env selVar := by
  simp only [VenomState.set]
  exact if_neg (selVar_ne_cmpVar i)

/-- **Whole-chain dispatch routing.** If `selVar` holds `V`, the function
resolves each dispatch block, and case `misses.length` (selector `V`) is the
first match (the `misses` before it all differ from `V`), then `run` from the
chain head `dispLabel start` reaches the matching body — with `selVar`, the
calldata (so the body can still decode its arguments), and the storage (so the
body observes the caller's state) preserved. -/
theorem run_dispatch_routes (fn : Function) (V : UInt256) (mBody : Label) :
    ∀ (misses : List (UInt256 × Label)) (start : Nat) (s : VenomState) (fuel : Nat),
      s.env selVar = V →
      (∀ p ∈ misses, p.1 ≠ V) →
      misses.length < fuel →
      (∀ j, (hj : j < misses.length) →
        fn.find? (dispLabel (start + j))
          = some (dispatchBlock (start + j) (misses[j].1) (misses[j].2))) →
      fn.find? (dispLabel (start + misses.length))
        = some (dispatchBlock (start + misses.length) V mBody) →
      ∃ s', run fn fuel (dispLabel start) s = run fn (fuel - misses.length - 1) mBody s'
            ∧ s'.env selVar = V ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage
            ∧ s'.caller = s.caller := by
  intro misses
  induction misses with
  | nil =>
    intro start s fuel hsel _ hfuel _ hfindm
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [List.length_nil] at hfuel; omega⟩
    simp only [List.length_nil, Nat.add_zero] at hfindm
    refine ⟨{ s.set (cmpVar start) (UInt256.eq (s.env selVar) V) with prevBlock := dispLabel start },
            ?_, ?_, rfl, rfl, rfl⟩
    · rw [show f + 1 - ([] : List (UInt256 × Label)).length - 1 = f from rfl,
         run_dispatchBlock_match fn f start V mBody s hfindm hsel]
    · show (s.set (cmpVar start) (UInt256.eq (s.env selVar) V)).env selVar = V
      rw [set_cmpVar_selVar]; exact hsel
  | cons p ps ih =>
    intro start s fuel hsel hmiss hfuel hfindj hfindm
    have hp : p.1 ≠ V := hmiss p (List.mem_cons_self ..)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by simp only [List.length_cons] at hfuel; omega⟩
    have hfind0 : fn.find? (dispLabel start) = some (dispatchBlock start p.1 p.2) := by
      have := hfindj 0 (by simp)
      simpa using this
    rw [run_dispatchBlock_miss fn f start p.1 p.2 s hfind0 (by rw [hsel]; exact hp.symm)]
    set s₁ := { s.set (cmpVar start) (UInt256.eq (s.env selVar) p.1) with
                prevBlock := dispLabel start } with hs₁
    have hs₁sel : s₁.env selVar = V := by
      show (s.set (cmpVar start) (UInt256.eq (s.env selVar) p.1)).env selVar = V
      rw [set_cmpVar_selVar]; exact hsel
    obtain ⟨s', hrun, hsel', hcd', hst', hcal'⟩ :=
      ih (start + 1) s₁ f hs₁sel
        (fun q hq => hmiss q (List.mem_cons_of_mem _ hq))
        (by simp only [List.length_cons] at hfuel; omega)
        (fun j hj => by
          have := hfindj (j + 1) (by simp only [List.length_cons]; omega)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)
        (by
          have := hfindm
          simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)
    refine ⟨s', ?_, hsel', ?_, ?_, ?_⟩
    · rw [show f + 1 - (p :: ps).length - 1 = f - ps.length - 1 by
            simp only [List.length_cons]; omega, hrun]
    · rw [hcd', hs₁]; rfl
    · rw [hst', hs₁]; rfl
    · rw [hcal', hs₁]; rfl

/-! ## Worked example: a concrete two-method dispatcher

For a concrete `cases` list the block labels are concrete strings, so the
`find?` well-formedness `run_dispatch_routes` needs is discharged by
computation (`rfl`) — no general `dispLabel`-injectivity lemma required. This
demonstrates `genABIFrontEnd` routing end-to-end for an ERC-20-style
`transfer`/`balanceOf` dispatcher. -/

/-- A concrete dispatcher over `transfer` (a9059cbb) and `balanceOf` (70a08231). -/
def exFn : Function :=
  genABIFrontEnd "entry"
    [(UInt256.ofNat 0xa9059cbb, "body_transfer"), (UInt256.ofNat 0x70a08231, "body_balanceOf")] []

/-- The `transfer` selector matches the first case: `run` reaches its body in
one dispatch step. -/
theorem exFn_routes_transfer (s : VenomState) (fuel : Nat)
    (hsel : s.env selVar = UInt256.ofNat 0xa9059cbb) (hfuel : 0 < fuel) :
    ∃ s', run exFn fuel (dispLabel 0) s = run exFn (fuel - 1) "body_transfer" s'
          ∧ s'.env selVar = UInt256.ofNat 0xa9059cbb ∧ s'.calldata = s.calldata
          ∧ s'.storage = s.storage ∧ s'.caller = s.caller :=
  run_dispatch_routes exFn (UInt256.ofNat 0xa9059cbb) "body_transfer"
    [] 0 s fuel hsel (by simp) (by simpa using hfuel)
    (by intro j hj; simp only [List.length_nil] at hj; omega) (by rfl)

/-- The `balanceOf` selector misses `transfer` then matches: `run` reaches its
body in two dispatch steps. -/
theorem exFn_routes_balanceOf (s : VenomState) (fuel : Nat)
    (hsel : s.env selVar = UInt256.ofNat 0x70a08231) (hfuel : 1 < fuel) :
    ∃ s', run exFn fuel (dispLabel 0) s = run exFn (fuel - 2) "body_balanceOf" s'
          ∧ s'.env selVar = UInt256.ofNat 0x70a08231 ∧ s'.calldata = s.calldata
          ∧ s'.storage = s.storage ∧ s'.caller = s.caller :=
  run_dispatch_routes exFn (UInt256.ofNat 0x70a08231) "body_balanceOf"
    [(UInt256.ofNat 0xa9059cbb, "body_transfer")] 0 s fuel hsel
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; decide)
    (by simpa using hfuel)
    (by intro j hj; have : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
        subst this; rfl)
    (by rfl)

end Abi

end EvmYul.Venom

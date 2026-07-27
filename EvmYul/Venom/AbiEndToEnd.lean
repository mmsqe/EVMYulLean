import EvmYul.Venom.AbiDispatchWF
import EvmYul.Venom.AbiSelector
import EvmYul.Venom.AbiReturn

/-!
# Venom IR — ABI front end, contract entry to method body

The execution-level capstone joining the two halves of the generated ABI
front end: the **entry block** (which reads the 4-byte selector from calldata,
`selVar := shr 224 (calldataload 0)`) and the **dispatch chain** (which routes
on `selVar`). Earlier the routing theorems started at `dispLabel 0` *assuming*
`selVar` was already set; here the entry block's execution supplies exactly
that, via `AbiSelector.calldataSelector_selectorBytes`.

`genABIFrontEnd_entry_routes` is the end-to-end statement: run the generated
function from its entry label on calldata `selectorBytes sel ++ args` and it
reaches the body of the method whose selector is `sel` — extract selector →
route → (body then decodes its arguments via `AbiBridge`). Calldata is
preserved throughout, so the body can still decode.
-/

namespace EvmYul.Venom.Abi

/-- The entry block executes `cd0 := calldataload 0`, `selVar := shr 224 cd0`
(= `calldataSelector`), then jumps to the dispatch head. -/
theorem execBlock_entryBlock (s : VenomState) (entryLbl : Label) :
    execBlock s (entryBlock entryLbl).instrs
      = ((s.set cd0Var (s.calldataload (UInt256.ofNat 0))).set selVar (calldataSelector s),
         Control.jump (dispLabel 0)) := by
  simp only [entryBlock, execBlock, execInstr, evalPure, evalBin, Operand.evalEnv,
    VenomState.setOutput, List.map, VenomState.set_env_self, calldataSelector]

/-- The generated function resolves its entry label (the entry block is first). -/
theorem genABIFrontEnd_find_entry (entryLbl : Label) (cs : List (UInt256 × Label))
    (bodies : List BasicBlock) :
    (genABIFrontEnd entryLbl cs bodies).find? entryLbl = some (entryBlock entryLbl) := by
  unfold genABIFrontEnd Function.find?
  simp only [List.find?_cons]
  rw [show ((entryBlock entryLbl).label == entryLbl) = true from by simp [entryBlock]]

/-- One `run` step through the entry block: extract the selector into `selVar`
and step to the dispatch head. -/
theorem run_entryBlock (fn : Function) (fuel : Nat) (entryLbl : Label) (s : VenomState)
    (hfind : fn.find? entryLbl = some (entryBlock entryLbl)) :
    run fn (fuel + 1) entryLbl s
      = run fn fuel (dispLabel 0)
          { (s.set cd0Var (s.calldataload (UInt256.ofNat 0))).set selVar (calldataSelector s)
              with prevBlock := entryLbl } := by
  simp only [run, hfind, execBlock_entryBlock]

/-- **Contract entry to method body.** Running the generated function from its
entry label on calldata `selectorBytes sel ++ args` (`sel` fitting 4 bytes, at
least one 32-byte argument word) routes to the body of the method whose
selector is `sel`, when that method sits after the (non-matching) `before`
entries — one entry step plus the dispatch steps. Calldata and storage are
preserved (the body decodes the caller's args and observes its state). -/
theorem genABIFrontEnd_entry_routes
    (entryLbl : Label) (before after : List (UInt256 × Label)) (body : Label)
    (bodies : List BasicBlock) (sel : UInt256) (args : Mem) (s : VenomState) (fuel : Nat)
    (hbits : sel.toNat < 2 ^ 32) (hargs : 28 ≤ args.length)
    (hcd : s.calldata = selectorBytes sel ++ args)
    (hmiss : ∀ p ∈ before, p.1 ≠ sel)
    (hfuel : before.length + 1 < fuel)
    (hentry : ∀ i, i < (before ++ (sel, body) :: after).length → entryLbl ≠ dispLabel i) :
    ∃ s',
      run (genABIFrontEnd entryLbl (before ++ (sel, body) :: after) bodies) fuel entryLbl s
        = run (genABIFrontEnd entryLbl (before ++ (sel, body) :: after) bodies)
            (fuel - before.length - 2) body s'
        ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage ∧ s'.caller = s.caller := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [run_entryBlock _ f entryLbl s
        (genABIFrontEnd_find_entry entryLbl (before ++ (sel, body) :: after) bodies)]
  set s2 := { (s.set cd0Var (s.calldataload (UInt256.ofNat 0))).set selVar (calldataSelector s)
                with prevBlock := entryLbl } with hs2
  have hs2sel : s2.env selVar = sel := by
    rw [hs2]
    show ((s.set cd0Var (s.calldataload (UInt256.ofNat 0))).set selVar
            (calldataSelector s)).env selVar = sel
    rw [VenomState.set_env_self]
    exact calldataSelector_selectorBytes s sel args hbits hargs hcd
  have hs2cd : s2.calldata = s.calldata := rfl
  have hs2st : s2.storage = s.storage := rfl
  have hs2cal : s2.caller = s.caller := rfl
  obtain ⟨s', hrun, _, hcd', hst', hcal'⟩ := genABIFrontEnd_routes entryLbl before after sel body bodies s2 f
    hs2sel hmiss (by omega) hentry
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · rw [hrun, show f + 1 - before.length - 2 = f - before.length - 1 from by omega]
  · rw [hcd', hs2cd]
  · rw [hst', hs2st]
  · rw [hcal', hs2cal]

/-- **Entry → dispatch → return (full ABI front-end pipeline).** Composes
`genABIFrontEnd_entry_routes` (entry extracts the selector and routes to the
method body) with `run_returnWord` (a `returnWord` body ABI-encodes and returns):
running from the contract entry on `sel`'s calldata `selectorBytes sel ++ args`,
when `sel`'s body is the `returnWord` block for `v`, halts with returndata =
`encodeUint256 (s'.env v)` — the whole path from raw calldata to ABI-encoded
return value, with calldata preserved to the body. -/
theorem genABIFrontEnd_entry_returns
    (entryLbl : Label) (before after : List (UInt256 × Label)) (body : Label) (v : VarName)
    (bodies : List BasicBlock) (sel : UInt256) (args : Mem) (s : VenomState) (fuel : Nat)
    (hbits : sel.toNat < 2 ^ 32) (hargs : 28 ≤ args.length)
    (hcd : s.calldata = selectorBytes sel ++ args)
    (hmiss : ∀ p ∈ before, p.1 ≠ sel)
    (hfuel : before.length + 2 < fuel)
    (hentry : ∀ i, i < (before ++ (sel, body) :: after).length → entryLbl ≠ dispLabel i)
    (hfind : (genABIFrontEnd entryLbl (before ++ (sel, body) :: after) bodies).find? body
             = some (returnBlock body v)) :
    ∃ s' : VenomState,
        run (genABIFrontEnd entryLbl (before ++ (sel, body) :: after) bodies) fuel entryLbl s
            = .halted (s'.mstore (UInt256.ofNat 0) (s'.env v)) (.ret (encodeUint256 (s'.env v)))
          ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage ∧ s'.caller = s.caller := by
  obtain ⟨s', hrun, hcd', hst', hcal'⟩ := genABIFrontEnd_entry_routes entryLbl before after body bodies sel args s
    fuel hbits hargs hcd hmiss (by omega) hentry
  refine ⟨s', ?_, hcd', hst', hcal'⟩
  rw [hrun, show fuel - before.length - 2 = (fuel - before.length - 3) + 1 from by omega,
      VenomState.run_returnWord _ (fuel - before.length - 3) body v s' hfind]

/-- `genABIFrontEnd_entry_routes` specialized to a single-method table
(`"entry"` / `"body"` labels), with the label and fuel side conditions
discharged and the remaining fuel pre-split for a following body-run lemma —
the routing step every worked capstone starts with. -/
theorem entry_routes_single {fn : Function} (sel : UInt256) (bodies : List BasicBlock)
    (args : Mem) (s : VenomState) (fuel : Nat)
    (hfn : fn = genABIFrontEnd "entry" [(sel, "body")] bodies)
    (hbits : sel.toNat < 2 ^ 32) (hargs : 28 ≤ args.length)
    (hcd : s.calldata = selectorBytes sel ++ args)
    (hfuel : 2 < fuel) :
    ∃ (f : Nat) (s' : VenomState),
      run fn fuel "entry" s = run fn (f + 1) "body" s'
      ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage ∧ s'.caller = s.caller := by
  subst hfn
  have hentry : ∀ i, i < ([] ++ (sel, "body") :: []).length → "entry" ≠ dispLabel i := by
    intro i hi
    have h0 : i = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hi)
    subst h0
    decide
  obtain ⟨s', hrun, hcd', hst', hcal'⟩ :=
    genABIFrontEnd_entry_routes "entry" [] [] "body" bodies sel args s fuel hbits hargs hcd
      (by simp) (by simp only [List.length_nil]; omega) hentry
  simp only [List.nil_append] at hrun
  refine ⟨fuel - 3, s', ?_, hcd', hst', hcal'⟩
  rw [hrun, show fuel - List.length ([] : List (UInt256 × Label)) - 2 = (fuel - 3) + 1
        from by simp only [List.length_nil]; omega]

/-- A concrete `transfer` dispatcher whose body ABI-encodes and returns var `r`
    (the worked companion of `exFn`, now including the return block). -/
def exFnRet : Function :=
  genABIFrontEnd "entry" [(UInt256.ofNat 0xa9059cbb, "body")] [returnBlock "body" "r"]

/-- **Worked entry→dispatch→return.** A `transfer` call on `exFnRet` extracts the
    selector, routes to the body, and halts with returndata = the ABI encoding of
    `r` — the whole ABI front-end pipeline on a concrete dispatcher, all
    side-conditions discharged by `decide`/`rfl`. -/
theorem exFnRet_transfer_returns (s : VenomState) (args : Mem) (fuel : Nat)
    (hargs : 28 ≤ args.length)
    (hcd : s.calldata = selectorBytes (UInt256.ofNat 0xa9059cbb) ++ args)
    (hfuel : 2 < fuel) :
    ∃ s' : VenomState,
      run exFnRet fuel "entry" s
        = .halted (s'.mstore (UInt256.ofNat 0) (s'.env "r")) (.ret (encodeUint256 (s'.env "r")))
      ∧ s'.calldata = s.calldata ∧ s'.storage = s.storage ∧ s'.caller = s.caller :=
  genABIFrontEnd_entry_returns "entry" [] [] "body" "r" [returnBlock "body" "r"]
    (UInt256.ofNat 0xa9059cbb) args s fuel (by decide) hargs hcd
    (by simp) (by omega) (by decide) (by rfl)

end EvmYul.Venom.Abi

import EvmYul.Venom.AbiEndToEnd
import EvmYul.Venom.BalanceSlot

/-!
# Venom IR — ABI-observable equivalence of the balance-slot peephole

Composes the two verified pillars into one external-behaviour statement:

* the **ABI front-end** chain (`AbiEndToEnd`): contract entry → selector
  extraction → dispatch → method body, calldata *and storage* preserved;
* the **balance-slot** chain (`BalanceSlot`): the original keccak slot load
  and the patched `~addr` load agree under the per-address storage relation.

`abi_balanceOf_orig_opt_returndata_eq` is the capstone: a `balanceOf(a)`
*call* — raw calldata in, ABI-encoded returndata out — halts with the **same
returndata** on the original dispatcher (keccak slot body) and the patched
dispatcher (`~addr` body), provided orig's keccak slot holds what opt's `~a`
slot holds. This is the "optimized contract is ABI-observably identical"
statement the balance-patch tooling's differential tests check executably.
-/

namespace EvmYul.Venom

open Abi

/-- `balanceOf(address)` selector (`keccak256("balanceOf(address)")[:4]`). -/
def balanceOfSel : UInt256 := UInt256.ofNat 0x70a08231

/-- Method body, original: decode the address argument from calldata offset 4,
derive the balance slot with the keccak block, `SLOAD` it, ABI-return it. -/
def balanceRetOrigBlock (lbl : Label) (slotOp : Operand) : BasicBlock :=
  { label := lbl
  , instrs :=
      { output := some "%a", opcode := .calldataload, operands := [.lit (UInt256.ofNat 4)] }
        :: (venomBalanceLoadOrigBlock slotOp (.var "%a") "%bal" ++ Abi.returnWord "%bal") }

/-- Method body, patched: same decode, `~addr` slot, `SLOAD`, ABI-return —
the body shape the length-preserving peephole leaves behind. -/
def balanceRetOptBlock (lbl : Label) : BasicBlock :=
  { label := lbl
  , instrs :=
      { output := some "%a", opcode := .calldataload, operands := [.lit (UInt256.ofNat 4)] }
        :: (venomBalanceLoadOptBlock (.var "%a") "%bal" ++ Abi.returnWord "%bal") }

/-- Running the original body from its label: decode `a` at offset 4, load
`storage[keccak256(slot ++ a)]`, halt with its ABI encoding as returndata. -/
theorem run_balanceRetOrig (fn : Function) (fuel : Nat) (lbl : Label)
    (slot : UInt256) (s : VenomState)
    (hfind : fn.find? lbl = some (balanceRetOrigBlock lbl (.lit slot))) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s
        = .halted s' (.ret (Abi.encodeUint256
            (s.storage (venomKeccakOf
              (Mem.toBytes32 slot ++ Mem.toBytes32 (s.calldataload (UInt256.ofNat 4))))))) := by
  simp only [run, hfind, balanceRetOrigBlock, venomBalanceLoadOrigBlock,
    venomBalanceKeccakBlock, List.cons_append, List.nil_append,
    execBlock, execInstr, List.map_cons, List.map_nil, Operand.evalEnv,
    VenomState.setOutput, VenomState.set_env_self, VenomState.mstore_env,
    VenomState.sload, VenomState.set_storage, VenomState.mstore_storage,
    VenomState.execBlock_returnWord]
  rw [keccak_staged]
  exact ⟨_, rfl⟩

/-- Running the patched body from its label: decode `a` at offset 4, load
`storage[~a]`, halt with its ABI encoding as returndata. -/
theorem run_balanceRetOpt (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState)
    (hfind : fn.find? lbl = some (balanceRetOptBlock lbl)) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s
        = .halted s' (.ret (Abi.encodeUint256
            (s.storage (UInt256.lnot (s.calldataload (UInt256.ofNat 4)))))) := by
  simp only [run, hfind, balanceRetOptBlock, venomBalanceLoadOptBlock,
    List.cons_append, List.nil_append,
    execBlock, execInstr, List.map_cons, List.map_nil, Operand.evalEnv,
    evalPure, evalUn, VenomState.setOutput, VenomState.set_env_self,
    VenomState.mstore_env, VenomState.mload, VenomState.mstore_memory,
    VenomState.sload, VenomState.set_storage, VenomState.mstore_storage,
    VenomState.execBlock_returnWord]
  rw [Mem.loadWord_storeWord_self]
  exact ⟨_, rfl⟩

/-- The original single-method `balanceOf` dispatcher (keccak slot body). -/
def balanceOfFnOrig (slot : UInt256) : Function :=
  genABIFrontEnd "entry" [(balanceOfSel, "body")] [balanceRetOrigBlock "body" (.lit slot)]

/-- The patched single-method `balanceOf` dispatcher (`~addr` body). -/
def balanceOfFnOpt : Function :=
  genABIFrontEnd "entry" [(balanceOfSel, "body")] [balanceRetOptBlock "body"]

/-- **ABI-observable equivalence of the balance-slot peephole.** Call
`balanceOf(a)` — calldata `selectorBytes ++ encodeUint256 a ++ suf` — on both
the original dispatcher (keccak slot body) and the patched one (`~a` body).
Under the storage relation (orig's `keccak256(slot ++ a)` slot holds what
opt's `~a` slot holds — `VenomBalEquivRel` at the decoded address), both runs
halt with the **same ABI-encoded returndata**: the whole path raw calldata →
selector → dispatch → decode → slot load → ABI return is observably
unchanged by the rewrite. -/
theorem abi_balanceOf_orig_opt_returndata_eq
    {slot a : UInt256} {suf : Mem} {s_orig s_opt : VenomState} {fuel : Nat}
    (hcd_o : s_orig.calldata = selectorBytes balanceOfSel ++ (Mem.toBytes32 a ++ suf))
    (hcd_p : s_opt.calldata = selectorBytes balanceOfSel ++ (Mem.toBytes32 a ++ suf))
    (hRel : s_orig.storage (venomKeccakOf (Mem.toBytes32 slot ++ Mem.toBytes32 a))
              = s_opt.storage (UInt256.lnot a))
    (hfuel : 2 < fuel) :
    ∃ (s₁ s₂ : VenomState) (ret : Mem),
      run (balanceOfFnOrig slot) fuel "entry" s_orig = .halted s₁ (.ret ret)
      ∧ run balanceOfFnOpt fuel "entry" s_opt = .halted s₂ (.ret ret) := by
  have hsel4 : (selectorBytes balanceOfSel).length = 4 :=
    Asm.beBytesN_length 4 balanceOfSel (by decide)
  have hargs : 28 ≤ (Mem.toBytes32 a ++ suf).length := by
    rw [List.length_append, Mem.toBytes32_length]; omega
  obtain ⟨f₁, s₁', hrun₁, hcd₁, hst₁, -⟩ :=
    entry_routes_single (fn := balanceOfFnOrig slot) balanceOfSel _
      (Mem.toBytes32 a ++ suf) s_orig fuel rfl (by decide) hargs hcd_o hfuel
  obtain ⟨f₂, s₂', hrun₂, hcd₂, hst₂, -⟩ :=
    entry_routes_single (fn := balanceOfFnOpt) balanceOfSel _
      (Mem.toBytes32 a ++ suf) s_opt fuel rfl (by decide) hargs hcd_p hfuel
  -- the decoded argument is `a` on both sides
  have ha₁ : s₁'.calldataload (UInt256.ofNat 4) = a :=
    VenomState.calldataload_append_toBytes32 s₁' (selectorBytes balanceOfSel) suf a
      (UInt256.ofNat 4) (by rw [hcd₁, hcd_o, List.append_assoc]) (by rw [hsel4]; decide)
  have ha₂ : s₂'.calldataload (UInt256.ofNat 4) = a :=
    VenomState.calldataload_append_toBytes32 s₂' (selectorBytes balanceOfSel) suf a
      (UInt256.ofNat 4) (by rw [hcd₂, hcd_p, List.append_assoc]) (by rw [hsel4]; decide)
  obtain ⟨t₁, hhalt₁⟩ :=
    run_balanceRetOrig (balanceOfFnOrig slot) f₁ "body" slot s₁' (by rfl)
  obtain ⟨t₂, hhalt₂⟩ :=
    run_balanceRetOpt balanceOfFnOpt f₂ "body" s₂' (by rfl)
  refine ⟨t₁, t₂,
    Abi.encodeUint256 (s_orig.storage (venomKeccakOf (Mem.toBytes32 slot ++ Mem.toBytes32 a))),
    ?_, ?_⟩
  · rw [hrun₁, hhalt₁, ha₁, hst₁]
  · rw [hrun₂, hhalt₂, ha₂, hst₂, hRel]

end EvmYul.Venom

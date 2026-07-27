import EvmYul.Venom.AbiBalance
import EvmYul.Venom.NoAlias

/-!
# Venom IR — ABI-observable equivalence of the peephole on the WRITE path

`AbiBalance` covered the read path: a `balanceOf` call returns identical
bytes. This file covers the **write path**: a `transfer(to, amt)` *call* —
decode both arguments, debit `balanceOf[msg.sender]`, credit `balanceOf[to]`,
ABI-return `true` — on the original dispatcher (keccak slot derivations) and
the patched one (`~addr`) halts with the same returndata **and leaves the two
storages related again** (`transferStorage_rel`). The relation being an
invariant is what makes multi-call traces equal: after any number of
transfers, every subsequent `balanceOf` still returns identical bytes
(`abi_balanceOf_orig_opt_returndata_eq`).

The one asymmetric hypothesis is `hinj`: the *original* slot function
`keccak256(slot ++ addr)` is collision-free on addresses — the assumption the
original contract's correctness silently rests on anyway. The patched side
needs nothing: `~` is provably injective (`UInt256.lnot_injective`).

The body is 16 instructions, so the run lemmas are proved compositionally:
one exec equation per sub-block (each with a *compact* output state), chained
by `execBlock_append_ft` — a one-shot `simp` over the whole block duplicates
the state per environment lookup and blows up.
-/

namespace EvmYul.Venom

open Abi

/-- `execBlock` over an append whose prefix falls through continues into the
suffix — the rewrite-friendly corollary of `execBlock_append`. -/
theorem execBlock_append_ft (b₁ b₂ : List Instruction) (s s₁ : VenomState)
    (h : execBlock s b₁ = (s₁, .fallthrough)) :
    execBlock s (b₁ ++ b₂) = execBlock s₁ b₂ := by
  rw [execBlock_append, h]

/-- Collapse `VenomState` projections and env lookups (through intervening
`set`s / `mstore`s / `sstore`s / copies) after a step rewrite, and normalize
list appends so the next block head is exposed. -/
macro "venom_norm" : tactic =>
  `(tactic| simp only [Operand.evalEnv, VenomState.set_env, VenomState.set_env_self,
      VenomState.mstore_env, VenomState.sstore_env, VenomState.calldatacopy_env,
      VenomState.set_calldataload, VenomState.mstore_calldataload,
      VenomState.sstore_calldataload, VenomState.set_caller, VenomState.mstore_caller,
      VenomState.sstore_caller, VenomState.set_storage, VenomState.mstore_storage,
      VenomState.sstore_storage_apply, VenomState.calldatacopy_storage,
      VenomState.calldatacopy_caller, VenomState.calldatacopy_calldata,
      String.reduceEq, reduceIte, List.cons_append, List.nil_append])

/-- The original mapping-slot function: `keccak256(slot ++ addr)`. -/
def kecSlot (slot a : UInt256) : UInt256 :=
  venomKeccakOf (Mem.toBytes32 slot ++ Mem.toBytes32 a)

/-- `transfer(address,uint256)` selector. -/
def transferSel : UInt256 := UInt256.ofNat 0xa9059cbb

/-! ## The blocks -/

/-- Store block, original: stage `slot`/`addr`, keccak the slot, `SSTORE` the
value held in `valVar` — the write-side dual of `venomBalanceLoadOrigBlock`. -/
def venomBalanceStoreOrigBlock (slotOp addrOp : Operand) (valVar : VarName) : List Instruction :=
  venomBalanceKeccakBlock slotOp addrOp "%wslot"
    ++ [ { opcode := .sstore, operands := [.var "%wslot", .var valVar] } ]

/-- Store block, patched: stage the addr, read it back, complement, `SSTORE`. -/
def venomBalanceStoreOptBlock (addrOp : Operand) (valVar : VarName) : List Instruction :=
  [ { opcode := .mstore, operands := [.lit (UInt256.ofNat 0x20), addrOp] }
  , { output := some "%waddr", opcode := .mload, operands := [.lit (UInt256.ofNat 0x20)] }
  , { output := some "%wslot", opcode := .not, operands := [.var "%waddr"] }
  , { opcode := .sstore, operands := [.var "%wslot", .var valVar] } ]

/-- Shared decode prefix: `to` at calldata 4, `amt` at 36, `msg.sender`. -/
def transferBodyPrefix : List Instruction :=
  [ { output := some "%to",  opcode := .calldataload, operands := [.lit (UInt256.ofNat 4)] }
  , { output := some "%amt", opcode := .calldataload, operands := [.lit (UInt256.ofNat 36)] }
  , { output := some "%cal", opcode := .caller, operands := [] } ]

/-- `%x2 := op %x %amt` — the debit (`sub`) / credit (`add`) instruction. -/
def arithInstr (op : Op) (x x2 : VarName) : Instruction :=
  { output := some x2, opcode := op, operands := [.var x, .var "%amt"] }

/-- Execute the plain (pure / assign / return) instructions at the head of the
block — including the ABI return tail — normalizing lookups as it goes. Stops
at the next block-definition application. -/
macro "venom_step" : tactic =>
  `(tactic| simp only [arithInstr, execBlock, execInstr, List.map_cons, List.map_nil,
      Operand.evalEnv, evalPure, evalBin, evalUn, VenomState.setOutput,
      VenomState.set_env, VenomState.set_env_self, VenomState.mstore_env,
      VenomState.sstore_env, VenomState.calldatacopy_env,
      VenomState.execBlock_returnWord, String.reduceEq, reduceIte])


/-- Method body, original: decode, keccak-load sender balance, debit,
keccak-store it, keccak-load receiver balance, credit, keccak-store it,
ABI-return `true`. (Right-nested appends: the step lemmas consume the head.) -/
def transferRetOrigBlock (lbl : Label) (slotOp : Operand) : BasicBlock :=
  { label := lbl
  , instrs := transferBodyPrefix
      ++ (venomBalanceLoadOrigBlock slotOp (.var "%cal") "%sb"
      ++ ([arithInstr .sub "%sb" "%sb2"]
      ++ (venomBalanceStoreOrigBlock slotOp (.var "%cal") "%sb2"
      ++ (venomBalanceLoadOrigBlock slotOp (.var "%to") "%tb"
      ++ ([arithInstr .add "%tb" "%tb2"]
      ++ (venomBalanceStoreOrigBlock slotOp (.var "%to") "%tb2"
      ++ ({ output := some "%r", opcode := .assign,
            operands := [.lit (UInt256.ofNat 1)] } :: Abi.returnWord "%r"))))))) }

/-- Method body, patched: same dataflow through `~addr` loads/stores. -/
def transferRetOptBlock (lbl : Label) : BasicBlock :=
  { label := lbl
  , instrs := transferBodyPrefix
      ++ (venomBalanceLoadOptBlock (.var "%cal") "%sb"
      ++ ([arithInstr .sub "%sb" "%sb2"]
      ++ (venomBalanceStoreOptBlock (.var "%cal") "%sb2"
      ++ (venomBalanceLoadOptBlock (.var "%to") "%tb"
      ++ ([arithInstr .add "%tb" "%tb2"]
      ++ (venomBalanceStoreOptBlock (.var "%to") "%tb2"
      ++ ({ output := some "%r", opcode := .assign,
            operands := [.lit (UInt256.ofNat 1)] } :: Abi.returnWord "%r"))))))) }

/-! ## Step lemmas: one exec equation per sub-block, compact output states -/

theorem execBlock_transferPrefix (s : VenomState) :
    execBlock s transferBodyPrefix
      = (((s.set "%to" (s.calldataload (UInt256.ofNat 4))).set "%amt"
            (s.calldataload (UInt256.ofNat 36))).set "%cal" s.caller, .fallthrough) := by
  simp [transferBodyPrefix, execBlock, execInstr, Operand.evalEnv, VenomState.setOutput]

theorem execBlock_loadOrig (s : VenomState) (slot : UInt256) (addrOp : Operand) (out : VarName) :
    execBlock s (venomBalanceLoadOrigBlock (.lit slot) addrOp out)
      = ((((s.mstore (UInt256.ofNat 0x00) slot).mstore (UInt256.ofNat 0x20)
              (addrOp.evalEnv s.env)).set "%vslot"
              (kecSlot slot (addrOp.evalEnv s.env))).set out
              (s.storage (kecSlot slot (addrOp.evalEnv s.env))), .fallthrough) := by
  simp only [venomBalanceLoadOrigBlock, venomBalanceKeccakBlock, List.cons_append,
    List.nil_append, execBlock, execInstr, List.map_cons, List.map_nil, Operand.evalEnv,
    VenomState.setOutput, VenomState.mstore_env, VenomState.set_env_self,
    VenomState.sload, VenomState.set_storage, VenomState.mstore_storage]
  rw [keccak_staged]
  rfl

theorem execBlock_storeOrig (s : VenomState) (slot : UInt256) (addrOp : Operand)
    (valVar : VarName) (hv : valVar ≠ "%wslot") :
    execBlock s (venomBalanceStoreOrigBlock (.lit slot) addrOp valVar)
      = ((((s.mstore (UInt256.ofNat 0x00) slot).mstore (UInt256.ofNat 0x20)
              (addrOp.evalEnv s.env)).set "%wslot"
              (kecSlot slot (addrOp.evalEnv s.env))).sstore
              (kecSlot slot (addrOp.evalEnv s.env)) (s.env valVar), .fallthrough) := by
  simp only [venomBalanceStoreOrigBlock, venomBalanceKeccakBlock, List.cons_append,
    List.nil_append, execBlock, execInstr, List.map_cons, List.map_nil, Operand.evalEnv,
    VenomState.setOutput, VenomState.mstore_env, VenomState.set_env_self,
    VenomState.set_env, if_neg hv]
  rw [keccak_staged]
  rfl

theorem execBlock_loadOpt (s : VenomState) (addrOp : Operand) (out : VarName) :
    execBlock s (venomBalanceLoadOptBlock addrOp out)
      = ((((s.mstore (UInt256.ofNat 0x20) (addrOp.evalEnv s.env)).set "%vaddr"
              (addrOp.evalEnv s.env)).set "%vslot"
              (UInt256.lnot (addrOp.evalEnv s.env))).set out
              (s.storage (UInt256.lnot (addrOp.evalEnv s.env))), .fallthrough) := by
  simp only [venomBalanceLoadOptBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalUn, VenomState.setOutput, VenomState.mstore_env,
    VenomState.set_env_self, VenomState.mload, VenomState.mstore_memory,
    Mem.loadWord_storeWord_self, VenomState.sload, VenomState.set_storage,
    VenomState.mstore_storage]

theorem execBlock_storeOpt (s : VenomState) (addrOp : Operand)
    (valVar : VarName) (hv1 : valVar ≠ "%wslot") (hv2 : valVar ≠ "%waddr") :
    execBlock s (venomBalanceStoreOptBlock addrOp valVar)
      = ((((s.mstore (UInt256.ofNat 0x20) (addrOp.evalEnv s.env)).set "%waddr"
              (addrOp.evalEnv s.env)).set "%wslot"
              (UInt256.lnot (addrOp.evalEnv s.env))).sstore
              (UInt256.lnot (addrOp.evalEnv s.env)) (s.env valVar), .fallthrough) := by
  simp only [venomBalanceStoreOptBlock, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, evalPure, evalUn, VenomState.setOutput, VenomState.mstore_env,
    VenomState.set_env_self, VenomState.mload, VenomState.mstore_memory,
    Mem.loadWord_storeWord_self, VenomState.set_env, if_neg hv1, if_neg hv2]

/-! ## The transfer semantics and relation preservation -/

/-- The storage a transfer body leaves behind: debit slot `kc`, credit slot
`kt`, the credit reading the post-debit balance (self-transfer safe). -/
def transferStorage (σ : UInt256 → UInt256) (kc kt amt : UInt256) : UInt256 → UInt256 :=
  fun k =>
    if k = kt then (if kt = kc then σ kc - amt else σ kt) + amt
    else if k = kc then σ kc - amt
    else σ k

/-- **Relation preservation.** If two storages agree balance-for-balance
(orig's keccak slot vs opt's `~addr` slot), they still do after both perform
the same transfer — keccak collision-freedom hypothesised on the orig side,
`~`-injectivity proved on the opt side. -/
theorem transferStorage_rel (σo σp : UInt256 → UInt256) (slot c tgt amt : UInt256)
    (hRel : ∀ a, σo (kecSlot slot a) = σp (UInt256.lnot a))
    (hinj : ∀ x y : UInt256, kecSlot slot x = kecSlot slot y → x = y) :
    ∀ a, transferStorage σo (kecSlot slot c) (kecSlot slot tgt) amt (kecSlot slot a)
       = transferStorage σp (UInt256.lnot c) (UInt256.lnot tgt) amt (UInt256.lnot a) := by
  intro a
  have hk : ∀ x y : UInt256, (kecSlot slot x = kecSlot slot y) ↔ x = y :=
    fun x y => ⟨hinj x y, fun h => h ▸ rfl⟩
  have hl : ∀ x y : UInt256, (UInt256.lnot x = UInt256.lnot y) ↔ x = y :=
    fun x y => ⟨fun h => UInt256.lnot_injective h, fun h => h ▸ rfl⟩
  simp only [transferStorage, hk, hl]
  grind

/-! ## Running the bodies -/

set_option linter.unusedSimpArgs false in
/-- Running the original transfer body: halts returning the ABI encoding of
`true`, leaving exactly the debit/credit double update on the keccak slots.
(The chained normalization `simp`s share one lemma list; per-site unused
arguments are expected.) -/
theorem run_transferRetOrig (fn : Function) (fuel : Nat) (lbl : Label)
    (slot : UInt256) (s : VenomState)
    (hfind : fn.find? lbl = some (transferRetOrigBlock lbl (.lit slot))) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s = .halted s' (.ret (Abi.encodeUint256 (UInt256.ofNat 1)))
      ∧ s'.storage = transferStorage s.storage
          (kecSlot slot s.caller)
          (kecSlot slot (s.calldataload (UInt256.ofNat 4)))
          (s.calldataload (UInt256.ofNat 36)) := by
  simp only [run, hfind, transferRetOrigBlock]
  rw [execBlock_append_ft _ _ _ _ (execBlock_transferPrefix s)]
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOrig _ slot _ _)]
  venom_norm
  venom_step
  rw [execBlock_append_ft _ _ _ _ (execBlock_storeOrig _ slot _ _ (by decide))]
  venom_norm
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOrig _ slot _ _)]
  venom_norm
  venom_step
  rw [execBlock_append_ft _ _ _ _ (execBlock_storeOrig _ slot _ _ (by decide))]
  venom_step
  refine ⟨_, rfl, ?_⟩
  funext k
  simp only [transferStorage, kecSlot]
  venom_norm
  rfl

set_option linter.unusedSimpArgs false in
/-- Running the patched transfer body: same returndata, same double update on
the `~addr` slots. -/
theorem run_transferRetOpt (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState)
    (hfind : fn.find? lbl = some (transferRetOptBlock lbl)) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s = .halted s' (.ret (Abi.encodeUint256 (UInt256.ofNat 1)))
      ∧ s'.storage = transferStorage s.storage
          (UInt256.lnot s.caller)
          (UInt256.lnot (s.calldataload (UInt256.ofNat 4)))
          (s.calldataload (UInt256.ofNat 36)) := by
  simp only [run, hfind, transferRetOptBlock]
  rw [execBlock_append_ft _ _ _ _ (execBlock_transferPrefix s)]
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOpt _ _ _)]
  venom_norm
  venom_step
  rw [execBlock_append_ft _ _ _ _ (execBlock_storeOpt _ _ _ (by decide) (by decide))]
  venom_norm
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOpt _ _ _)]
  venom_norm
  venom_step
  rw [execBlock_append_ft _ _ _ _ (execBlock_storeOpt _ _ _ (by decide) (by decide))]
  venom_step
  refine ⟨_, rfl, ?_⟩
  funext k
  simp only [transferStorage]
  venom_norm
  rfl

/-! ## The dispatchers and the capstone -/

/-- The original single-method `transfer` dispatcher. -/
def transferFnOrig (slot : UInt256) : Function :=
  genABIFrontEnd "entry" [(transferSel, "body")] [transferRetOrigBlock "body" (.lit slot)]

/-- The patched single-method `transfer` dispatcher. -/
def transferFnOpt : Function :=
  genABIFrontEnd "entry" [(transferSel, "body")] [transferRetOptBlock "body"]

/-- **ABI-observable equivalence of the peephole on the write path.** Call
`transfer(tgt, amt)` from `caller = c` on both dispatchers. Under the
balance-for-balance storage relation (and keccak collision-freedom on the
orig side), both runs halt with the **same returndata**, and the final
storages satisfy the relation **again** — so the equivalence survives any
number of transfers, and `abi_balanceOf_orig_opt_returndata_eq` applies to
every subsequent read. -/
theorem abi_transfer_orig_opt_equiv
    {slot tgt amt c : UInt256} {suf : Mem} {s_orig s_opt : VenomState} {fuel : Nat}
    (hcal_o : s_orig.caller = c) (hcal_p : s_opt.caller = c)
    (hcd_o : s_orig.calldata
      = selectorBytes transferSel ++ (Mem.toBytes32 tgt ++ (Mem.toBytes32 amt ++ suf)))
    (hcd_p : s_opt.calldata
      = selectorBytes transferSel ++ (Mem.toBytes32 tgt ++ (Mem.toBytes32 amt ++ suf)))
    (hRel : ∀ a, s_orig.storage (kecSlot slot a) = s_opt.storage (UInt256.lnot a))
    (hinj : ∀ x y : UInt256, kecSlot slot x = kecSlot slot y → x = y)
    (hfuel : 2 < fuel) :
    ∃ (s₁ s₂ : VenomState) (ret : Mem),
      run (transferFnOrig slot) fuel "entry" s_orig = .halted s₁ (.ret ret)
      ∧ run transferFnOpt fuel "entry" s_opt = .halted s₂ (.ret ret)
      ∧ ∀ a, s₁.storage (kecSlot slot a) = s₂.storage (UInt256.lnot a) := by
  have hsel4 : (selectorBytes transferSel).length = 4 :=
    Asm.beBytesN_length 4 transferSel (by decide)
  have hargs : 28 ≤ (Mem.toBytes32 tgt ++ (Mem.toBytes32 amt ++ suf)).length := by
    rw [List.length_append, Mem.toBytes32_length]; omega
  obtain ⟨f₁, s₁', hrun₁, hcd₁, hst₁, hcal₁⟩ :=
    entry_routes_single (fn := transferFnOrig slot) transferSel _
      (Mem.toBytes32 tgt ++ (Mem.toBytes32 amt ++ suf)) s_orig fuel rfl (by decide)
      hargs hcd_o hfuel
  obtain ⟨f₂, s₂', hrun₂, hcd₂, hst₂, hcal₂⟩ :=
    entry_routes_single (fn := transferFnOpt) transferSel _
      (Mem.toBytes32 tgt ++ (Mem.toBytes32 amt ++ suf)) s_opt fuel rfl (by decide)
      hargs hcd_p hfuel
  -- both args decode identically on both sides
  have hto₁ : s₁'.calldataload (UInt256.ofNat 4) = tgt :=
    VenomState.calldataload_append_toBytes32 s₁' (selectorBytes transferSel)
      (Mem.toBytes32 amt ++ suf) tgt (UInt256.ofNat 4)
      (by rw [hcd₁, hcd_o, List.append_assoc]) (by rw [hsel4]; decide)
  have hto₂ : s₂'.calldataload (UInt256.ofNat 4) = tgt :=
    VenomState.calldataload_append_toBytes32 s₂' (selectorBytes transferSel)
      (Mem.toBytes32 amt ++ suf) tgt (UInt256.ofNat 4)
      (by rw [hcd₂, hcd_p, List.append_assoc]) (by rw [hsel4]; decide)
  have hpre36 : ((selectorBytes transferSel ++ Mem.toBytes32 tgt).length) = 36 := by
    rw [List.length_append, hsel4, Mem.toBytes32_length]
  have hamt₁ : s₁'.calldataload (UInt256.ofNat 36) = amt :=
    VenomState.calldataload_append_toBytes32 s₁' (selectorBytes transferSel ++ Mem.toBytes32 tgt)
      suf amt (UInt256.ofNat 36)
      (by rw [hcd₁, hcd_o]; simp [List.append_assoc]) (by rw [hpre36]; decide)
  have hamt₂ : s₂'.calldataload (UInt256.ofNat 36) = amt :=
    VenomState.calldataload_append_toBytes32 s₂' (selectorBytes transferSel ++ Mem.toBytes32 tgt)
      suf amt (UInt256.ofNat 36)
      (by rw [hcd₂, hcd_p]; simp [List.append_assoc]) (by rw [hpre36]; decide)
  obtain ⟨t₁, hhalt₁, hstor₁⟩ :=
    run_transferRetOrig (transferFnOrig slot) f₁ "body" slot s₁' (by rfl)
  obtain ⟨t₂, hhalt₂, hstor₂⟩ :=
    run_transferRetOpt transferFnOpt f₂ "body" s₂' (by rfl)
  refine ⟨t₁, t₂, Abi.encodeUint256 (UInt256.ofNat 1), ?_, ?_, ?_⟩
  · rw [hrun₁, hhalt₁]
  · rw [hrun₂, hhalt₂]
  · intro a
    rw [hstor₁, hstor₂, hto₁, hto₂, hamt₁, hamt₂, hcal₁, hcal₂, hcal_o, hcal_p, hst₁, hst₂]
    exact transferStorage_rel s_orig.storage s_opt.storage slot c tgt amt hRel hinj a

end EvmYul.Venom

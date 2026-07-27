import EvmYul.Venom.AbiTransfer

/-!
# Venom IR — the peephole on DYNAMIC-keyed mappings (outer-keccak elimination)

Venom derives a `String[..]`/`Bytes[..]`-keyed mapping slot in **two stages**:
an inner *variable-size* keccak of the key bytes, then the same 64-byte outer
keccak over `slot ++ innerHash` that the balance map uses. The peephole
rewrites only the outer stage to `~innerHash`, dropping one KECCAK256 per
access.

`abi_dynKeyGet_orig_opt_returndata_eq` is the capstone: a getter *call* on a
dynamic-keyed map — copy the key bytes from calldata, inner-hash them, load
through the outer derivation, ABI-return — halts with the **same returndata**
on the original and patched dispatchers, under the storage relation quantified
over the *inner-hash value*. That quantification is the honest statement of
"no new assumptions": keys whose inner hashes collide already collide in the
original derivation, so the rewrite is equivalence-preserving relative to the
original outright (contrast the balance capstones, where the orig side
hypothesises keccak collision-freedom on addresses).

The inner hash is a pure function of calldata (`dynKeyHash`): `calldatacopy`
writes a calldata slice and the keccak reads exactly that region
(`readBytes_writeBytes_self`), so equal calldata gives equal inner hashes on
both sides — no argument-layout hypotheses are needed at all.
-/

namespace EvmYul.Venom

open Abi

namespace Mem

/-- `readBytes` returns exactly `len` bytes (zero-padded past the end). -/
theorem readBytes_length (mem : Mem) (offset len : Nat) :
    (mem.readBytes offset len).length = len := by
  unfold Mem.readBytes
  simp only [List.length_take, List.length_drop, expand_length]
  omega

/-- `readBytes_writeBytes_self`, stated for any read length equal to the
written length. -/
theorem readBytes_writeBytes_of_length (mem : Mem) (offset n : Nat) (bs : Mem)
    (h : bs.length = n) :
    (mem.writeBytes offset bs).readBytes offset n = bs :=
  h ▸ readBytes_writeBytes_self mem offset bs

end Mem

/-- The inner key hash as a pure function of the calldata: keccak over the
key bytes (`len` at word 36, data from byte 68 — the standard single-dynamic-
argument layout). -/
def dynKeyHash (cd : Mem) : UInt256 :=
  venomKeccakOf (cd.readBytes 68 (Mem.fromBytes32 (cd.readBytes 36 32)).toNat)

/-- The inner-hash prefix: `%len := calldataload 36`, copy the key bytes to
`mem[0x40..]`, `%kh := keccak256 0x40 %len` — the variable-size inner hash the
patcher never touches. -/
def dynKeyPrefix : List Instruction :=
  [ { output := some "%len", opcode := .calldataload, operands := [.lit (UInt256.ofNat 36)] }
  , { opcode := .calldatacopy
    , operands := [.lit (UInt256.ofNat 0x40), .lit (UInt256.ofNat 68), .var "%len"] }
  , { output := some "%kh", opcode := .keccak256
    , operands := [.lit (UInt256.ofNat 0x40), .var "%len"] } ]

/-- The copied-then-hashed key bytes are a pure function of calldata. -/
theorem keccak_calldatacopy (s : VenomState) (len : UInt256) :
    keccak (s.calldatacopy (UInt256.ofNat 0x40) (UInt256.ofNat 68) len)
           (UInt256.ofNat 0x40) len
      = venomKeccakOf (s.calldata.readBytes 68 len.toNat) := by
  unfold keccak venomKeccakOf VenomState.calldatacopy
  rw [show (UInt256.ofNat 0x40).toNat = 64 from by decide,
      show (UInt256.ofNat 68).toNat = 68 from by decide]
  rw [Mem.readBytes_writeBytes_of_length _ _ _ _ (Mem.readBytes_length _ _ _)]

set_option linter.unusedSimpArgs false in
/-- Executing the prefix binds `%kh` to `dynKeyHash s.calldata`. -/
theorem execBlock_dynKeyPrefix (s : VenomState) :
    execBlock s dynKeyPrefix
      = (((s.set "%len" (s.calldataload (UInt256.ofNat 36))).calldatacopy
            (UInt256.ofNat 0x40) (UInt256.ofNat 68)
            (s.calldataload (UInt256.ofNat 36))).set "%kh" (dynKeyHash s.calldata),
         .fallthrough) := by
  simp only [dynKeyPrefix, execBlock, execInstr, List.map_cons, List.map_nil,
    Operand.evalEnv, VenomState.setOutput, VenomState.set_env_self,
    VenomState.calldatacopy_env, VenomState.set_calldataload,
    keccak_calldatacopy]
  rw [show (s.set "%len" (s.calldataload (UInt256.ofNat 36))).calldata = s.calldata from rfl]
  rfl

/-- Getter body, original: inner-hash the key, keccak-load through the outer
derivation, ABI-return the value. -/
def dynKeyRetOrigBlock (lbl : Label) (slotOp : Operand) : BasicBlock :=
  { label := lbl
  , instrs := dynKeyPrefix
      ++ (venomBalanceLoadOrigBlock slotOp (.var "%kh") "%bal"
      ++ Abi.returnWord "%bal") }

/-- Getter body, patched: same inner hash, `~innerHash` slot load. -/
def dynKeyRetOptBlock (lbl : Label) : BasicBlock :=
  { label := lbl
  , instrs := dynKeyPrefix
      ++ (venomBalanceLoadOptBlock (.var "%kh") "%bal"
      ++ Abi.returnWord "%bal") }

set_option linter.unusedSimpArgs false in
/-- Running the original getter body: returndata = the ABI encoding of the
value at the outer keccak slot of the inner key hash. -/
theorem run_dynKeyRetOrig (fn : Function) (fuel : Nat) (lbl : Label)
    (slot : UInt256) (s : VenomState)
    (hfind : fn.find? lbl = some (dynKeyRetOrigBlock lbl (.lit slot))) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s
        = .halted s' (.ret (Abi.encodeUint256
            (s.storage (kecSlot slot (dynKeyHash s.calldata))))) := by
  simp only [run, hfind, dynKeyRetOrigBlock]
  rw [execBlock_append_ft _ _ _ _ (execBlock_dynKeyPrefix s)]
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOrig _ slot _ _)]
  venom_norm
  venom_step
  exact ⟨_, rfl⟩

set_option linter.unusedSimpArgs false in
/-- Running the patched getter body: returndata = the ABI encoding of the
value at `~innerHash`. -/
theorem run_dynKeyRetOpt (fn : Function) (fuel : Nat) (lbl : Label) (s : VenomState)
    (hfind : fn.find? lbl = some (dynKeyRetOptBlock lbl)) :
    ∃ s' : VenomState,
      run fn (fuel + 1) lbl s
        = .halted s' (.ret (Abi.encodeUint256
            (s.storage (UInt256.lnot (dynKeyHash s.calldata))))) := by
  simp only [run, hfind, dynKeyRetOptBlock]
  rw [execBlock_append_ft _ _ _ _ (execBlock_dynKeyPrefix s)]
  rw [execBlock_append_ft _ _ _ _ (execBlock_loadOpt _ _ _)]
  venom_norm
  venom_step
  exact ⟨_, rfl⟩

/-- The original dynamic-key getter dispatcher (any 4-byte selector). -/
def dynKeyFnOrig (sel slot : UInt256) : Function :=
  genABIFrontEnd "entry" [(sel, "body")] [dynKeyRetOrigBlock "body" (.lit slot)]

/-- The patched dynamic-key getter dispatcher. -/
def dynKeyFnOpt (sel : UInt256) : Function :=
  genABIFrontEnd "entry" [(sel, "body")] [dynKeyRetOptBlock "body"]

/-- **The peephole is ABI-observably invisible on dynamic-keyed maps.** Call
the getter with the same calldata on the original (two keccaks) and patched
(inner keccak + `~`) dispatchers: both halt with the **same returndata**,
under the storage relation quantified over the inner-hash value — keys whose
inner hashes collide already collide in the original derivation, so no
collision-freedom hypothesis is needed at all. -/
theorem abi_dynKeyGet_orig_opt_returndata_eq
    {sel slot : UInt256} {args : Mem} {s_orig s_opt : VenomState} {fuel : Nat}
    (hbits : sel.toNat < 2 ^ 32) (hargs : 28 ≤ args.length)
    (hcd_o : s_orig.calldata = selectorBytes sel ++ args)
    (hcd_p : s_opt.calldata = selectorBytes sel ++ args)
    (hRel : ∀ h, s_orig.storage (kecSlot slot h) = s_opt.storage (UInt256.lnot h))
    (hfuel : 2 < fuel) :
    ∃ (s₁ s₂ : VenomState) (ret : Mem),
      run (dynKeyFnOrig sel slot) fuel "entry" s_orig = .halted s₁ (.ret ret)
      ∧ run (dynKeyFnOpt sel) fuel "entry" s_opt = .halted s₂ (.ret ret) := by
  obtain ⟨f₁, s₁', hrun₁, hcd₁, hst₁, -⟩ :=
    entry_routes_single (fn := dynKeyFnOrig sel slot) sel _ args s_orig fuel rfl
      hbits hargs hcd_o hfuel
  obtain ⟨f₂, s₂', hrun₂, hcd₂, hst₂, -⟩ :=
    entry_routes_single (fn := dynKeyFnOpt sel) sel _ args s_opt fuel rfl
      hbits hargs hcd_p hfuel
  obtain ⟨t₁, hhalt₁⟩ := run_dynKeyRetOrig (dynKeyFnOrig sel slot) f₁ "body" slot s₁' (by rfl)
  obtain ⟨t₂, hhalt₂⟩ := run_dynKeyRetOpt (dynKeyFnOpt sel) f₂ "body" s₂' (by rfl)
  -- equal calldata gives equal inner hashes; the relation at that hash closes it
  have hkh : dynKeyHash s₁'.calldata = dynKeyHash s₂'.calldata := by
    rw [hcd₁, hcd_o, hcd₂, hcd_p]
  refine ⟨t₁, t₂,
    Abi.encodeUint256 (s_orig.storage (kecSlot slot (dynKeyHash (selectorBytes sel ++ args)))),
    ?_, ?_⟩
  · rw [hrun₁, hhalt₁, hst₁, hcd₁, hcd_o]
  · rw [hrun₂, hhalt₂, hst₂, hcd₂, hcd_p, ← hRel (dynKeyHash (selectorBytes sel ++ args))]

end EvmYul.Venom

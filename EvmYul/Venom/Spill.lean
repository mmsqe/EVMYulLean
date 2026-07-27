import EvmYul.Venom.Backend
import EvmYul.Venom.MemBridge

/-!
# M4: register spilling at the `Sim` level

When the SSA stack exceeds the EVM's `SWAP16` reach, the scheduler spills a live
value to memory and reloads it later. This file lifts that to the `Sim` relation:
the connecting predicate is the **spill invariant** — the spill slot holds the
spilled variable's value (`lookupMemory spill = vs.env a`).

* `sim_spill`  — `PUSH spill; MSTORE` moves `%a` from the stack into the slot,
  dropping the layout from `a :: L` to `L` and *establishing* the invariant.
* `sim_reload` — `PUSH spill; MLOAD` reads the slot back, extending the layout
  from `L` to `a :: L`, *using* the invariant.

The value preservation is the discharged machine memory law
(`MemBridge.machine_load_store_self`); the EVM step ↔ memory-op connection is the
strong `MSTORE`/`MLOAD` shapes below. The spill addressing carries two realistic
preconditions — the address fits a machine word, and the slot is *active* after
the store (which `MSTORE` ensures by expanding `activeWords`; here a hypothesis,
to be discharged from the allocator's invariant). The remaining M4 work is the
slot allocator that keeps spill slots mutually disjoint (the frame side is
`Mem.spill_survives_writes`).
-/

set_option maxHeartbeats 1000000

namespace EvmYul.Venom.Backend
open EvmYul EvmYul.EVM EvmYul.Frame EvmYul.Venom.MemBridge

/-! ## Strong memory step-shapes (expose the memory effect the weak shapes hide) -/

/-- **Strong `MLOAD` shape.** Pops the address and pushes `lookupMemory addr` (the
value, named — the weak shape only gives `∃ v`); memory contents unchanged. -/
theorem step_MLOAD_shape_strong (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MLOAD, arg)) s = .ok s') :
    s'.stack = s.toMachineState.lookupMemory hd :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- **Strong `MSTORE` shape.** Pops `[addr, val]`, writes `val` at `addr`
(`writeWord` = `machineStore`), stack drops to `tl`. -/
theorem step_MSTORE_shape_strong (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE, arg)) s = .ok s') :
    s'.stack = tl ∧
    s'.toMachineState.memory = (s.toMachineState.writeWord hd1 hd2).memory ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `PUSH1` preserves the memory and active-word count (so `lookupMemory` is
unchanged across it) and the account map. -/
theorem step_PUSH1_mem (s s' : EVM.State) (f' cost : ℕ) (v : UInt256)
    (hStep : EVM.step (f' + 1) cost (some (.Push .PUSH1, some (v, 1))) s = .ok s') :
    s'.stack = v :: s.stack ∧ s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `lookupMemory` depends only on memory + active words. -/
theorem lookupMemory_congr {a b : MachineState} (hm : a.memory = b.memory)
    (hw : a.activeWords = b.activeWords) (addr : UInt256) :
    a.lookupMemory addr = b.lookupMemory addr := by
  simp only [MachineState.lookupMemory, hm, hw]

/-- Off its zero-guard, `lookupMemory` is `machineLoad` of the memory. -/
theorem lookupMemory_eq_machineLoad (self : MachineState) (addr : UInt256)
    (hguard : ¬ (addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩)) :
    self.lookupMemory addr = machineLoad self.memory addr := by
  rw [MachineState.lookupMemory, if_neg hguard]; rfl

/-! ## Spill and reload at the `Sim` level -/

/-- **Spill a value.** `PUSH spill; MSTORE` writes `%a`'s value to the spill slot:
`Sim` drops from `a :: L` to `L` (`%a` off the stack), and the spill invariant
`lookupMemory spill = vs.env a` is established — given the address fits a machine
word and the slot is active after the store. -/
theorem sim_spill (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (a : VarName) (spill : UInt256) (f cost : ℕ) (argM : Option (UInt256 × Nat))
    (haddr : spill.toNat < USize.size)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es = .ok es1)
    (hmstore : EVM.step (f + 1) cost (some (.MSTORE, argM)) es1 = .ok es2)
    (hguard : ¬ (spill.toNat ≥ es2.toMachineState.memory.size
                 ∨ spill ≥ es2.toMachineState.activeWords * ⟨32⟩))
    (hsim : Sim vs es (a :: L)) :
    Sim vs es2 L ∧ es2.toMachineState.lookupMemory spill = vs.env a := by
  obtain ⟨hpstk, hpmem, hpaw, hpenv, hpacc⟩ := step_PUSH1_mem es es1 f cost spill hpush
  have hstk1 : es1.stack = spill :: vs.env a :: L.map vs.env := by rw [hpstk, hsim.1, List.map_cons]
  obtain ⟨hmstk, hmmem, hmenv, hmacc⟩ :=
    step_MSTORE_shape_strong es1 es2 f cost argM spill (vs.env a) (L.map vs.env) hstk1 hmstore
  refine ⟨⟨hmstk, fun x => ?_⟩, ?_⟩
  · rw [show sloadVal es2 x = sloadVal es x from by
          simp only [sloadVal, EvmYul.State.lookupAccount, hmacc, hpacc, hmenv, hpenv]]
    exact hsim.2 x
  · rw [lookupMemory_eq_machineLoad _ spill hguard, hmmem, writeWord_memory]
    exact machine_load_store_self spill (vs.env a) haddr (memRefines_self es1.toMachineState.memory)

/-- **Reload a value.** When the spill slot holds `%a`'s value (the invariant
`lookupMemory spill = vs.env a`), `PUSH spill; MLOAD` recovers `%a` onto the
stack — `Sim` extends from `L` to `a :: L`. -/
theorem sim_reload (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (a : VarName) (spill : UInt256) (f cost : ℕ) (argM : Option (UInt256 × Nat))
    (hspill : es.toMachineState.lookupMemory spill = vs.env a)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es = .ok es1)
    (hmload : EVM.step (f + 1) cost (some (.MLOAD, argM)) es1 = .ok es2)
    (hsim : Sim vs es L) :
    Sim vs es2 (a :: L) := by
  obtain ⟨hpstk, hpmem, hpaw, hpenv, hpacc⟩ := step_PUSH1_mem es es1 f cost spill hpush
  have hstk1 : es1.stack = spill :: L.map vs.env := by rw [hpstk, hsim.1]
  obtain ⟨hmstk, hmenv, hmacc⟩ :=
    step_MLOAD_shape_strong es1 es2 f cost argM spill (L.map vs.env) hstk1 hmload
  refine ⟨?_, fun x => ?_⟩
  · show es2.stack = (a :: L).map vs.env
    rw [hmstk, List.map_cons]
    congr 1
    rw [lookupMemory_congr hpmem hpaw spill]; exact hspill
  · rw [show sloadVal es2 x = sloadVal es x from by
          simp only [sloadVal, EvmYul.State.lookupAccount, hmacc, hpacc, hmenv, hpenv]]
    exact hsim.2 x

/-- **Full spill / reload round-trip (M4 capstone).** `%a` is spilled to the slot
(`PUSH; MSTORE`) and, with no intervening clobber, reloaded (`PUSH; MLOAD`): `Sim`
returns to `a :: L` with `%a`'s value intact — the complete register-spill cycle,
composing `sim_spill` then `sim_reload` (the spill invariant carries across the
reload's `PUSH`, which preserves memory). -/
theorem sim_spill_reload (vs : VenomState) (es0 es1 es2 es3 es4 : EVM.State) (L : Layout)
    (a : VarName) (spill : UInt256) (f cost : ℕ) (argM1 argM2 : Option (UInt256 × Nat))
    (haddr : spill.toNat < USize.size)
    (hpush1 : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es0 = .ok es1)
    (hmstore : EVM.step (f + 1) cost (some (.MSTORE, argM1)) es1 = .ok es2)
    (hguard : ¬ (spill.toNat ≥ es2.toMachineState.memory.size
                 ∨ spill ≥ es2.toMachineState.activeWords * ⟨32⟩))
    (hpush2 : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es2 = .ok es3)
    (hmload : EVM.step (f + 1) cost (some (.MLOAD, argM2)) es3 = .ok es4)
    (hsim : Sim vs es0 (a :: L)) :
    Sim vs es4 (a :: L) := by
  obtain ⟨hsim2, hinv⟩ :=
    sim_spill vs es0 es1 es2 L a spill f cost argM1 haddr hpush1 hmstore hguard hsim
  exact sim_reload vs es2 es3 es4 L a spill f cost argM2 hinv hpush2 hmload hsim2

/-! ## Discharging the slot-active guard (M4 remaining)

`sim_spill`'s `hguard` has two halves: the *physical* `memory.size` bound (a
residual `ByteArray` size fact, M1 territory) and the *logical* slot-active bound
on `activeWords`. The latter — the one that says the `MSTORE` made the slot live —
is discharged here from the EVM's own `mstore` semantics (it expands `activeWords`
to `M(old, spill, 32)`), so `sim_spill_active` carries only the physical bound. -/

/-- **Strong MSTORE shape, with activeWords.** Beyond the memory effect, `MSTORE`
expands the active-word count to cover the written slot (`mstore`'s `M`). -/
theorem step_MSTORE_shape_active (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE, arg)) s = .ok s') :
    s'.toMachineState.activeWords
      = .ofNat (MachineState.M s.toMachineState.activeWords.toNat hd1.toNat 32) := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- **The spill slot is active after `MSTORE`** — the active-words disjunct of the
zero-guard is discharged: `mstore` expands `activeWords` past `spill`. Needs the
realistic bounds that the slot address and the prior active memory fit a machine
word (active memory is gas-bounded). -/
theorem mstore_slot_active (s s' : EVM.State) (spill : UInt256) (f' cost : ℕ)
    (arg : Option (UInt256 × Nat)) (hd2 : UInt256) (tl : Stack UInt256)
    (haddr : spill.toNat < USize.size)
    (hawbound : s.toMachineState.activeWords.toNat * 32 < 2 ^ 256)
    (hStk : s.stack = spill :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE, arg)) s = .ok s') :
    ¬ (spill ≥ s'.toMachineState.activeWords * ⟨32⟩) := by
  have haw := step_MSTORE_shape_active s s' f' cost arg spill hd2 tl hStk hStep
  have husize : USize.size ≤ 2 ^ 64 := by
    rcases USize.size_eq with h | h <;> rw [h] <;> norm_num
  have h264 : (2 : ℕ) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  show ¬ (s'.toMachineState.activeWords * ⟨32⟩).toNat ≤ spill.toNat
  rw [uint256_mul_toNat, haw, uint256_ofNat_toNat]
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by show (32 : Fin (2^256)).val = 32; decide
  rw [h32]
  set M := MachineState.M s.toMachineState.activeWords.toNat spill.toNat 32 with hMdef
  have hMlt : M < 2 ^ 256 := by
    rw [hMdef]; unfold MachineState.M; simp only; omega
  have hbig : spill.toNat + 32 ≤ M * 32 := by
    rw [hMdef]; unfold MachineState.M; simp only
    have : spill.toNat < 2 ^ 64 := lt_of_lt_of_le haddr husize
    omega
  rw [Nat.mod_eq_of_lt hMlt, Nat.mod_eq_of_lt (by
    rw [hMdef]; unfold MachineState.M; simp only; omega)]
  omega

/-- **Spill with the slot-active guard discharged.** Strengthens `sim_spill`:
the active-words half of the zero-guard is now *derived* from the `MSTORE`
(`mstore_slot_active`), so the only remaining side conditions are the address
bound, a realistic prior-active-memory bound, and the physical `memory.size`
bound (the residual `ByteArray` size fact, M1 territory). -/
theorem sim_spill_active (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (a : VarName) (spill : UInt256) (f cost : ℕ) (argM : Option (UInt256 × Nat))
    (haddr : spill.toNat < USize.size)
    (hawbound : es1.toMachineState.activeWords.toNat * 32 < 2 ^ 256)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es = .ok es1)
    (hmstore : EVM.step (f + 1) cost (some (.MSTORE, argM)) es1 = .ok es2)
    (hmem : spill.toNat < es2.toMachineState.memory.size)
    (hsim : Sim vs es (a :: L)) :
    Sim vs es2 L ∧ es2.toMachineState.lookupMemory spill = vs.env a := by
  obtain ⟨hpstk, _, _, _, _⟩ := step_PUSH1_mem es es1 f cost spill hpush
  have hstk1 : es1.stack = spill :: vs.env a :: L.map vs.env := by
    rw [hpstk, hsim.1, List.map_cons]
  have hslot := mstore_slot_active es1 es2 spill f cost argM (vs.env a) (L.map vs.env)
    haddr hawbound hstk1 hmstore
  have hguard : ¬ (spill.toNat ≥ es2.toMachineState.memory.size
                   ∨ spill ≥ es2.toMachineState.activeWords * ⟨32⟩) := by
    push Not; exact ⟨hmem, hslot⟩
  exact sim_spill vs es es1 es2 L a spill f cost argM haddr hpush hmstore hguard hsim

/-- **Spill with the whole zero-guard discharged.** Both halves of `sim_spill`'s
`hguard` are now derived from the `MSTORE` itself — the logical slot-active bound
(`mstore_slot_active`) and the physical `memory.size` bound (`MSTORE` grows memory
to cover the slot, `machineStore_size_ge`). The only side conditions left are the
two realistic machine-word bounds. (Carries the M1 FFI axiom via the size fact.) -/
theorem sim_spill_full (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (a : VarName) (spill : UInt256) (f cost : ℕ) (argM : Option (UInt256 × Nat))
    (haddr : spill.toNat < USize.size)
    (hawbound : es1.toMachineState.activeWords.toNat * 32 < 2 ^ 256)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (spill, 1))) es = .ok es1)
    (hmstore : EVM.step (f + 1) cost (some (.MSTORE, argM)) es1 = .ok es2)
    (hsim : Sim vs es (a :: L)) :
    Sim vs es2 L ∧ es2.toMachineState.lookupMemory spill = vs.env a := by
  obtain ⟨hpstk, _, _, _, _⟩ := step_PUSH1_mem es es1 f cost spill hpush
  have hstk1 : es1.stack = spill :: vs.env a :: L.map vs.env := by
    rw [hpstk, hsim.1, List.map_cons]
  obtain ⟨_, hmmem, _, _⟩ :=
    step_MSTORE_shape_strong es1 es2 f cost argM spill (vs.env a) (L.map vs.env) hstk1 hmstore
  have hmem : spill.toNat < es2.toMachineState.memory.size := by
    rw [hmmem, writeWord_memory]
    have := machineStore_size_ge es1.toMachineState.memory spill (vs.env a) haddr
    omega
  exact sim_spill_active vs es es1 es2 L a spill f cost argM haddr hawbound hpush hmstore hmem hsim

end EvmYul.Venom.Backend

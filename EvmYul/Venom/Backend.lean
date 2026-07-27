import EvmYul.Frame.StepShapes
import EvmYul.Venom.State
import EvmYul.Venom.EvmBytecodeEquiv

/-!
# Venom → EVM backend, verification scaffolding (M2 kernel)

The first foundation toward a *verified* Venom→EVM lowering: the simulation
relation between a Venom SSA state and an EVM stack-machine state, and the
instruction-selection correctness lemmas (each Venom op, lowered to its EVM
opcode(s), preserves the relation under EVMYulLean's real `EVM.step`).

`StackSim vs es L` says the EVM stack is exactly the values of the SSA
variables listed in the layout `L` (top-first) — the heart of SSA-to-stack
lowering. SSA's single-assignment discipline appears as freshness side
conditions (`c ∉ L`).

Scope of this file (M2 start): single basic block, straight-line, no `phi`,
stack within the `SWAP16` window, and only ops whose value the `Frame` step
lemmas already expose strongly (here: `PUSH`, `JUMPDEST`). Storage/memory
correspondence, stack scheduling (`DUP`/`SWAP`/spill), `phi`/CFG reconciliation,
and jump resolution are later milestones (see `draft_zh.md` M1–M7).
-/

set_option maxRecDepth 4096

namespace EvmYul.Venom.Backend
open EvmYul EvmYul.EVM EvmYul.Frame

/-- A stack layout: the SSA variables whose values occupy the EVM stack,
top-first. -/
abbrev Layout := List VarName

/-- The EVM stack realizes the Venom SSA environment under a layout: the stack
holds exactly the layout variables' values (top-first). This relation is what a
verified SSA-to-stack lowering must preserve at every step. -/
def StackSim (vs : VenomState) (es : EVM.State) (L : Layout) : Prop :=
  es.stack = L.map vs.env

/-- **Instruction selection — literal push.** Lowering `assign %c = n` (a
literal SSA copy) to `PUSH n` preserves the stack simulation, pushing `c` onto
the layout. `c` is fresh (SSA assigns each variable once), captured by `c ∉ L`. -/
theorem stackSim_push_lit (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c : VarName) (n : UInt256) (f cost : ℕ)
    (hc : c ∉ L)
    (hstep : EVM.step (f + 1) cost (some (.Push .PUSH1, some (n, 1))) es = .ok es')
    (h : StackSim vs es L) :
    StackSim (vs.set c n) es' (c :: L) := by
  obtain ⟨_, hstk, _⟩ := step_PUSH1_shape es es' f cost n hstep
  unfold StackSim at *
  rw [hstk, h, List.map_cons]
  congr 1
  · simp [VenomState.set]
  · apply List.map_congr_left
    intro x hx
    have hxc : x ≠ c := fun e => hc (e ▸ hx)
    simp [VenomState.set, hxc]

/-- **Instruction selection — `nop`/label.** A `JUMPDEST` (the lowering of a
basic-block label / `nop`) leaves the stack — and so the simulation — unchanged. -/
theorem stackSim_jumpdest (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.JUMPDEST, arg)) es = .ok es')
    (h : StackSim vs es L) :
    StackSim vs es' L := by
  obtain ⟨_, hstk, _⟩ := step_JUMPDEST_shape es es' f cost arg hstep
  unfold StackSim at *
  rw [hstk]; exact h

/-- A *strong* shape for `NOT`: exposes the pushed value as `~hd` (the `NOT`
opcode dispatches to `UInt256.lnot`). The `Frame` library only proves the weak
`∃ v` shape; instruction selection for a computing op needs the value. -/
theorem step_NOT_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f + 1) cost (some (.NOT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.lnot hd :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Instruction selection — `NOT`.** Lowering `%c = not %a` (with `%a` on top
of the stack) to the `NOT` opcode preserves the simulation: it pops `a` and
pushes `c = ~a`. `c` is fresh (`c ∉ a :: L`). This is the opt-side slot
computation of the balance peephole, now at the lowering level. -/
theorem stackSim_not (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (hstep : EVM.step (f + 1) cost (some (.NOT, arg)) es = .ok es')
    (h : StackSim vs es (a :: L)) :
    StackSim (vs.set c (UInt256.lnot (vs.env a))) es' (c :: L) := by
  have hStk : es.stack = vs.env a :: L.map vs.env := by rw [h, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_NOT_shape_strong es es' f cost arg (vs.env a) (L.map vs.env) hStk hstep
  unfold StackSim
  rw [hstk', List.map_cons, VenomState.set_env_self]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxc : x ≠ c := fun e => hc (List.mem_cons_of_mem a (e ▸ hx))
  simp [VenomState.set, hxc]

/-- **Generic binary-op instruction selection.** Any op whose post-state stack
is `g (env a) (env b) :: rest` (both inputs popped, result pushed) lowers
`%c = op %a, %b` preserving StackSim. The per-op work is then just a strong
shape; this captures the `StackSim` bookkeeping once. -/
theorem stackSim_binop_of_shape (vs : VenomState) (es' : EVM.State) (L : Layout)
    (c a b : VarName) (g : UInt256 → UInt256 → UInt256)
    (hc : c ∉ a :: b :: L)
    (hshape : es'.stack = g (vs.env a) (vs.env b) :: L.map vs.env) :
    StackSim (vs.set c (g (vs.env a) (vs.env b))) es' (c :: L) := by
  unfold StackSim
  rw [hshape, List.map_cons, VenomState.set_env_self]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxc : x ≠ c := fun e => hc (List.mem_cons_of_mem a (List.mem_cons_of_mem b (e ▸ hx)))
  simp [VenomState.set, hxc]

/-- Shared proof of the strong binary-op shapes (ADD/SUB/LT/GT/EQ): each
dispatches through `dispatchBinary`/`execBinOp`, so the `.ok` reduction is one
template — only the opcode and the pushed operation differ. -/
local macro "solve_binop_shape" hs:ident hk:ident : tactic => `(tactic|
  (unfold EVM.step at $hs:ident
   simp only [bind, Except.bind, pure, Except.pure] at $hs:ident
   unfold EvmYul.step at $hs:ident
   simp only [Id.run] at $hs:ident
   unfold dispatchBinary EVM.execBinOp at $hs:ident
   rw [$hk:ident] at $hs:ident
   simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at $hs:ident
   subst $hs:ident
   refine ⟨rfl, rfl, rfl, rfl⟩))

/-- Strong `ADD` shape: exposes the pushed value as `add hd1 hd2` (ADD
dispatches to `UInt256.add`). -/
theorem step_ADD_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.ADD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.add hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  solve_binop_shape hStep hStk

/-- **Instruction selection — ADD.** Lowering `%c = add %a, %b` (with `%a, %b`
on top) to the `ADD` opcode preserves StackSim. `SUB`/`MUL`/… are identical
once their strong shape is in hand. -/
theorem stackSim_add (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.ADD, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: L)) :
    StackSim (vs.set c (UInt256.add (vs.env a) (vs.env b))) es' (c :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_ADD_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hStk hstep
  exact stackSim_binop_of_shape vs es' L c a b UInt256.add hc hstk'

/-! ## Stack scheduling primitives

`DUP`/`SWAP` are pure stack rearrangements with **no SSA-state change** — they
realize the scheduler's job of placing each live value where the next consumer
expects it. These are the building blocks of `_stack_reorder`. -/

/-- **DUP1.** Duplicate the top live value: layout `a :: L` becomes
`a :: a :: L`. (Makes a value available for a later consumer.) -/
theorem stackSim_dup1 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP1, arg)) es = .ok es')
    (h : StackSim vs es (a :: L)) :
    StackSim vs es' (a :: a :: L) := by
  obtain ⟨_, hstk', _⟩ :=
    step_DUP1_shape es es' f cost arg (vs.env a) (L.map vs.env) (by rw [h, List.map_cons]) hstep
  unfold StackSim at h ⊢
  rw [hstk', h]
  simp only [List.map_cons]

/-- **SWAP1.** Reorder the top two live values: layout `a :: b :: L` becomes
`b :: a :: L`. -/
theorem stackSim_swap1 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP1, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: L)) :
    StackSim vs es' (b :: a :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _⟩ :=
    step_SWAP1_shape es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hStk hstep
  unfold StackSim
  rw [hstk']
  simp only [List.map_cons]

/-! ## More pure ops (unary core + further instances)

The generic cores make each extra pure op a strong shape plus a one-liner. -/

/-- Generic unary-op instruction selection (the `StackSim` bookkeeping, once). -/
theorem stackSim_unop_of_shape (vs : VenomState) (es' : EVM.State) (L : Layout)
    (c a : VarName) (g : UInt256 → UInt256)
    (hc : c ∉ a :: L)
    (hshape : es'.stack = g (vs.env a) :: L.map vs.env) :
    StackSim (vs.set c (g (vs.env a))) es' (c :: L) := by
  unfold StackSim
  rw [hshape, List.map_cons, VenomState.set_env_self]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxc : x ≠ c := fun e => hc (List.mem_cons_of_mem a (e ▸ hx))
  simp [VenomState.set, hxc]

/-- Strong `ISZERO` shape (dispatches to `UInt256.isZero`). -/
theorem step_ISZERO_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.stack = UInt256.isZero hd :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Instruction selection — ISZERO.** -/
theorem stackSim_iszero (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (hstep : EVM.step (f + 1) cost (some (.ISZERO, arg)) es = .ok es')
    (h : StackSim vs es (a :: L)) :
    StackSim (vs.set c (UInt256.isZero (vs.env a))) es' (c :: L) := by
  obtain ⟨_, hstk', _, _⟩ := step_ISZERO_shape_strong es es' f cost arg (vs.env a) (L.map vs.env)
    (by rw [h, List.map_cons]) hstep
  exact stackSim_unop_of_shape vs es' L c a UInt256.isZero hc hstk'

/-- Strong `SUB` shape (dispatches to `UInt256.sub`). -/
theorem step_SUB_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.SUB, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.stack = UInt256.sub hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  solve_binop_shape hStep hStk

/-- **Instruction selection — SUB.** -/
theorem stackSim_sub (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.SUB, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: L)) :
    StackSim (vs.set c (UInt256.sub (vs.env a) (vs.env b))) es' (c :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_SUB_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hStk hstep
  exact stackSim_binop_of_shape vs es' L c a b UInt256.sub hc hstk'

/-! ## Storage-reading op (SLOAD)

Unlike memory ops (which wait on the `ByteArray` FFI wall, M1), `SLOAD` only
*reads* storage. With the storage half of the simulation (agreement between the
EVM state's storage and the Venom `storage`), its lowering is verified now —
this is the balance *load* of the peephole, at the lowering level. -/

/-- **Instruction selection — SLOAD.** Lowering `%c = sload %k` (with `%k` on
top) to the `SLOAD` opcode pops `k` and pushes `c = storage[k]`, given storage
agreement between the EVM state and the Venom `storage`. -/
theorem stackSim_sload (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c k : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ k :: L)
    (hsto : ∀ x, sloadVal es x = vs.storage x)
    (hstep : EVM.step (f + 1) cost (some (.SLOAD, arg)) es = .ok es')
    (h : StackSim vs es (k :: L)) :
    StackSim (vs.set c (vs.storage (vs.env k))) es' (c :: L) := by
  have hStk : es.stack = vs.env k :: L.map vs.env := by rw [h, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_SLOAD_shape_strong es es' f cost arg (vs.env k) (L.map vs.env) hStk hstep
  have hstk2 : es'.stack = sloadVal es (vs.env k) :: L.map vs.env := hstk'
  rw [hsto] at hstk2
  exact stackSim_unop_of_shape vs es' L c k (fun _ => vs.storage (vs.env k)) hc hstk2

/-! ## Full (stack + storage) simulation

Bundling the stack relation with storage agreement lets storage ops be tracked
end-to-end. `SLOAD` preserves the whole relation (it only reads). -/

/-- The full single-block simulation: the stack realizes the SSA layout, and the
EVM storage agrees with the Venom `storage`. -/
def Sim (vs : VenomState) (es : EVM.State) (L : Layout) : Prop :=
  StackSim vs es L ∧ ∀ x, sloadVal es x = vs.storage x

/-- **SLOAD preserves the full simulation.** Reading storage keeps the storage
agreement (SLOAD never writes) and updates the stack/layout — the balance load
of the peephole, tracked through the full state relation. -/
theorem sim_sload (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c k : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ k :: L)
    (hstep : EVM.step (f + 1) cost (some (.SLOAD, arg)) es = .ok es')
    (hsim : Sim vs es (k :: L)) :
    Sim (vs.set c (vs.storage (vs.env k))) es' (c :: L) := by
  obtain ⟨hstack, hsto⟩ := hsim
  refine ⟨stackSim_sload vs es es' L c k f cost arg hc hsto hstep hstack, ?_⟩
  intro x
  obtain ⟨_, _, henv, hacc⟩ :=
    step_SLOAD_shape_strong es es' f cost arg (vs.env k) (L.map vs.env)
      (by rw [hstack, List.map_cons]) hstep
  rw [VenomState.set_storage]
  rw [show sloadVal es' x = sloadVal es x from by
        simp only [sloadVal, EvmYul.State.lookupAccount, hacc, henv]]
  exact hsto x

/-! ## Storage-writing op (SSTORE)

The store companion to `SLOAD`. Unlike `SLOAD`, this *mutates* persistent
storage, so its correctness rests on a strong shape that exposes the storage
update as a pointwise function update of `sloadVal`. The account-map nesting
(`accountMap.find?` of the codeOwner, then `Account.updateStorage`) is threaded
through the existing `Frame`-level reasoning.

**Scope.** The shape covers the *nonzero-value* (insert) branch. The zero-write
case erases the slot, whose `findD` characterization needs RBMap `find?_erase`
lemmas that Batteries does not provide — a documented residual, in the same
honest-scope spirit as the `ByteArray` FFI wall (`draft_zh.md` M1). -/

/-- `compare` on `UInt256` reflects the underlying `Fin` comparison. -/
private theorem uint256_compare_eq (a b : UInt256) : compare a b = compare a.val b.val := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  show (compare a b).then Ordering.eq = compare a b
  cases compare a b <;> rfl

/-- Distinct `UInt256` keys do not compare `.eq` (the `LawfulEqCmp` direction we
need for storage `findD`; Batteries proves it for `Fin`, we lift it). -/
private theorem uint256_compare_ne_of_ne {x k : UInt256} (h : x ≠ k) : compare x k ≠ .eq := by
  intro hc
  apply h
  obtain ⟨xv⟩ := x; obtain ⟨kv⟩ := k
  rw [uint256_compare_eq] at hc
  exact congrArg UInt256.mk (Std.LawfulEqCmp.eq_of_compare hc)

/-- Storage read-after-write at the `RBMap` level (insert branch): reading the
written key gives the new value, any other key is unchanged. -/
private theorem storage_findD_insert (m : Storage) (k v x : UInt256) :
    (m.insert k v).findD x ⟨0⟩ = if x = k then v else m.findD x ⟨0⟩ := by
  unfold Batteries.RBMap.findD
  by_cases hx : x = k
  · subst hx
    rw [Batteries.RBMap.find?_insert_of_eq m Std.ReflCmp.compare_self]; simp
  · rw [Batteries.RBMap.find?_insert_of_ne m (uint256_compare_ne_of_ne hx)]; simp [hx]

/-- After `SSTORE`, the codeOwner account's `find?` is the storage-updated
account (account exists). -/
private theorem sstore_accountMap_find_codeOwner
    (self : EvmYul.State .EVM) (key val : UInt256) (acc : Account .EVM)
    (hFind : self.accountMap.find? self.executionEnv.codeOwner = some acc) :
    (EvmYul.State.sstore self key val).accountMap.find? self.executionEnv.codeOwner
      = some (acc.updateStorage key val) := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  rw [hFind]
  simp only [Option.option]
  change (self.accountMap.insert self.executionEnv.codeOwner
            (acc.updateStorage key val)).find? self.executionEnv.codeOwner
        = some (acc.updateStorage key val)
  exact Frame.find?_insert_self _ _ _

/-- Base-`State` pointwise storage update after `sstore` (nonzero value): the
post-`sloadVal` reads `val` at `key`, the old value elsewhere. -/
private theorem base_sstore_sloadVal_of_ne_zero
    (self : EvmYul.State .EVM) (key val x : UInt256) (acc : Account .EVM)
    (hFind : self.accountMap.find? self.executionEnv.codeOwner = some acc)
    (hval : (val == default) = false) :
    ((EvmYul.State.sstore self key val).accountMap.find?
        (EvmYul.State.sstore self key val).executionEnv.codeOwner).option (⟨0⟩ : UInt256)
        (Account.lookupStorage (k := x))
      = if x = key then val
        else (self.accountMap.find? self.executionEnv.codeOwner).option (⟨0⟩ : UInt256)
              (Account.lookupStorage (k := x)) := by
  rw [sstore_preserves_executionEnv,
      sstore_accountMap_find_codeOwner self key val acc hFind, hFind]
  simp only [Option.option]
  unfold Account.lookupStorage Account.updateStorage
  simp only [hval]
  exact storage_findD_insert acc.storage key val x

/-- **Strong `SSTORE` shape** (nonzero value). Exposes the storage write as a
pointwise update of `sloadVal`: every slot reads the stored value at `key`, the
old value elsewhere — given the executing account exists. -/
theorem step_SSTORE_shape_strong
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (key val : UInt256) (tl : Stack UInt256) (acc : Account .EVM)
    (hStk : s.stack = key :: val :: tl)
    (hFind : s.accountMap.find? s.executionEnv.codeOwner = some acc)
    (hval : (val == default) = false)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv ∧
    (∀ x, sloadVal s' x = if x = key then val else sloadVal s x) := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show (EvmYul.State.sstore _ _ _).executionEnv = s.executionEnv
    rw [sstore_preserves_executionEnv]
  · intro x
    exact base_sstore_sloadVal_of_ne_zero s.toState key val x acc hFind hval

/-- **Instruction selection — SSTORE (stack).** Lowering `sstore %k, %v` (with
`%k, %v` on top) to the `SSTORE` opcode pops both with no SSA output, so the
layout drops two; the SSA state's `env` is untouched (only `storage` changes). -/
theorem stackSim_sstore (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (k v : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat)) (acc : Account .EVM)
    (hFind : es.accountMap.find? es.executionEnv.codeOwner = some acc)
    (hval : (vs.env v == default) = false)
    (hstep : EVM.step (f + 1) cost (some (.SSTORE, arg)) es = .ok es')
    (h : StackSim vs es (k :: v :: L)) :
    StackSim (vs.sstore (vs.env k) (vs.env v)) es' L := by
  have hStk : es.stack = vs.env k :: vs.env v :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_SSTORE_shape_strong es es' f cost arg (vs.env k) (vs.env v) (L.map vs.env)
      acc hStk hFind hval hstep
  unfold StackSim
  rw [hstk']; rfl

/-- **SSTORE preserves the full simulation** (nonzero value). Lowering
`sstore %k, %v` keeps stack realization (no SSA output) and updates storage
agreement pointwise — the storage *write* companion to `sim_sload`. Requires the
executing account to exist and the value nonzero (insert branch). -/
theorem sim_sstore (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (k v : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat)) (acc : Account .EVM)
    (hFind : es.accountMap.find? es.executionEnv.codeOwner = some acc)
    (hval : (vs.env v == default) = false)
    (hstep : EVM.step (f + 1) cost (some (.SSTORE, arg)) es = .ok es')
    (hsim : Sim vs es (k :: v :: L)) :
    Sim (vs.sstore (vs.env k) (vs.env v)) es' L := by
  obtain ⟨hstack, hsto⟩ := hsim
  refine ⟨stackSim_sstore vs es es' L k v f cost arg acc hFind hval hstep hstack, ?_⟩
  intro x
  obtain ⟨_, _, _, hpt⟩ :=
    step_SSTORE_shape_strong es es' f cost arg (vs.env k) (vs.env v) (L.map vs.env)
      acc (by rw [hstack, List.map_cons, List.map_cons]) hFind hval hstep
  rw [hpt x, hsto x]; rfl

/-! ### The zero-write (slot-clearing) branch, modulo a `find?`-erase interface

`SSTORE`-ing `0` *erases* the slot (`Account.updateStorage` clears keys whose
value is `default`). Reading the erased slot back needs the `find?`-after-`erase`
semantics of `Batteries.RBMap` — which Batteries does **not** provide (it proves
only the structural `Ordered`/`Balanced`/`WF` erase lemmas, and no semantic
`find?`-after-mutation lemma beyond `insert`; deriving them means building the
`RBNode.del` theory from scratch).

We isolate exactly the two missing facts as `RBMapEraseSpec` — the standard
semantics of a map's `erase` — and prove the zero-write branch *from* them. So
the slot-clearing `SSTORE` is verified contingent on a precise, named interface,
and the rigorous nonzero (insert) branch above is untouched. -/

/-- The two `find?`-after-`erase` facts Batteries leaves unproven for
`Batteries.RBMap UInt256 UInt256 compare` (standard `erase` semantics): erasing a
key makes it unfound, and leaves every other key's lookup unchanged. -/
structure RBMapEraseSpec : Prop where
  find?_erase_self : ∀ (m : Storage) (k : UInt256), (m.erase k).find? k = none
  find?_erase_ne : ∀ (m : Storage) (k x : UInt256), x ≠ k → (m.erase k).find? x = m.find? x

/-- Storage read-after-erase (from the interface): the cleared key reads `0`, any
other key is unchanged. -/
theorem storage_findD_erase (spec : RBMapEraseSpec) (m : Storage) (k x : UInt256) :
    (m.erase k).findD x ⟨0⟩ = if x = k then ⟨0⟩ else m.findD x ⟨0⟩ := by
  unfold Batteries.RBMap.findD
  by_cases hx : x = k
  · subst hx; rw [spec.find?_erase_self]; simp
  · rw [spec.find?_erase_ne m k x hx]; simp [hx]

/-- Base-`State` pointwise storage update after a zero `sstore` (slot cleared):
the written key reads `0`, the old value elsewhere — contingent on the erase
interface. -/
private theorem base_sstore_sloadVal_zero (spec : RBMapEraseSpec)
    (self : EvmYul.State .EVM) (key val x : UInt256) (acc : Account .EVM)
    (hFind : self.accountMap.find? self.executionEnv.codeOwner = some acc)
    (hval : (val == default) = true) :
    ((EvmYul.State.sstore self key val).accountMap.find?
        (EvmYul.State.sstore self key val).executionEnv.codeOwner).option (⟨0⟩ : UInt256)
        (Account.lookupStorage (k := x))
      = if x = key then (⟨0⟩ : UInt256)
        else (self.accountMap.find? self.executionEnv.codeOwner).option (⟨0⟩ : UInt256)
              (Account.lookupStorage (k := x)) := by
  rw [sstore_preserves_executionEnv,
      sstore_accountMap_find_codeOwner self key val acc hFind, hFind]
  simp only [Option.option]
  unfold Account.lookupStorage Account.updateStorage
  simp only [hval]
  exact storage_findD_erase spec acc.storage key x

/-- **Strong `SSTORE` shape — zero-write (slot-clearing).** Storing a `default`
value clears the slot, so every slot reads `0` at `key` and the old value
elsewhere — contingent on the `find?`-erase interface. Companion to the nonzero
`step_SSTORE_shape_strong`. -/
theorem step_SSTORE_shape_strong_zero (spec : RBMapEraseSpec)
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (key val : UInt256) (tl : Stack UInt256) (acc : Account .EVM)
    (hStk : s.stack = key :: val :: tl)
    (hFind : s.accountMap.find? s.executionEnv.codeOwner = some acc)
    (hval : (val == default) = true)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv ∧
    (∀ x, sloadVal s' x = if x = key then (⟨0⟩ : UInt256) else sloadVal s x) := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show (EvmYul.State.sstore _ _ _).executionEnv = s.executionEnv
    rw [sstore_preserves_executionEnv]
  · intro x
    exact base_sstore_sloadVal_zero spec s.toState key val x acc hFind hval

/-- **SSTORE preserves the full simulation — zero-write.** Lowering
`sstore %k, %v` with `%v = 0` clears the slot and keeps storage agreement
pointwise; contingent on the erase interface. Closes the zero-write gap the
rigorous `sim_sstore` (insert branch) left open. -/
theorem sim_sstore_zero (spec : RBMapEraseSpec)
    (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (k v : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat)) (acc : Account .EVM)
    (hFind : es.accountMap.find? es.executionEnv.codeOwner = some acc)
    (hv0 : vs.env v = ⟨0⟩)
    (hstep : EVM.step (f + 1) cost (some (.SSTORE, arg)) es = .ok es')
    (hsim : Sim vs es (k :: v :: L)) :
    Sim (vs.sstore (vs.env k) (vs.env v)) es' L := by
  obtain ⟨hstack, hsto⟩ := hsim
  have hval : (vs.env v == default) = true := by rw [hv0]; rfl
  obtain ⟨_, hstk', _, hpt⟩ :=
    step_SSTORE_shape_strong_zero spec es es' f cost arg (vs.env k) (vs.env v) (L.map vs.env)
      acc (by rw [hstack, List.map_cons, List.map_cons]) hFind hval hstep
  refine ⟨?_, ?_⟩
  · show es'.stack = L.map (vs.sstore (vs.env k) (vs.env v)).env
    rw [hstk']; rfl
  · intro x
    rw [hpt x, hsto x, hv0]; rfl

/-! ## Pure ops at the full-`Sim` level

The computing/scheduling ops do not touch persistent storage, so they preserve
the storage half of `Sim` for free: whenever an EVM step leaves the account map
and execution env unchanged (which every pure op's strong shape now exposes),
`sloadVal` is unchanged, and the Venom `storage` is untouched. `sim_of_pure_step`
captures this once; each pure op then lifts its `StackSim` lemma to `Sim` in a
few lines — making `Sim` the uniform currency for composing storage blocks. -/

/-- **Lift a pure (storage-preserving) lowering step to the full `Sim`.** If the
EVM step preserves the account map and execution env (so `sloadVal` is
unchanged) and the SSA `storage` is untouched, a `StackSim` step extends to a
`Sim` step. -/
theorem sim_of_pure_step (vs vs' : VenomState) (es es' : EVM.State) (L L' : Layout)
    (hstorage : vs'.storage = vs.storage)
    (hacc : es'.accountMap = es.accountMap)
    (henv : es'.executionEnv = es.executionEnv)
    (hstack : StackSim vs es L → StackSim vs' es' L')
    (hsim : Sim vs es L) : Sim vs' es' L' := by
  obtain ⟨hs, hsto⟩ := hsim
  refine ⟨hstack hs, fun x => ?_⟩
  rw [show sloadVal es' x = sloadVal es x from by
        simp only [sloadVal, EvmYul.State.lookupAccount, hacc, henv], hsto x, hstorage]

/-- **NOT preserves the full simulation** — the opt-side `~addr` slot
computation of the balance peephole, at the `Sim` level. -/
theorem sim_not (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (hstep : EVM.step (f + 1) cost (some (.NOT, arg)) es = .ok es')
    (hsim : Sim vs es (a :: L)) :
    Sim (vs.set c (UInt256.lnot (vs.env a))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: L.map vs.env := by rw [hsim.1, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_NOT_shape_strong es es' f cost arg (vs.env a) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (stackSim_not vs es es' L c a f cost arg hc hstep) hsim

/-- **ISZERO preserves the full simulation.** -/
theorem sim_iszero (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (hstep : EVM.step (f + 1) cost (some (.ISZERO, arg)) es = .ok es')
    (hsim : Sim vs es (a :: L)) :
    Sim (vs.set c (UInt256.isZero (vs.env a))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: L.map vs.env := by rw [hsim.1, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_ISZERO_shape_strong es es' f cost arg (vs.env a) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (stackSim_iszero vs es es' L c a f cost arg hc hstep) hsim

/-- **ADD preserves the full simulation.** -/
theorem sim_add (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.ADD, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.add (vs.env a) (vs.env b))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_ADD_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: b :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (stackSim_add vs es es' L c a b f cost arg hc hstep) hsim

/-- **SUB preserves the full simulation** — the safe-math debit in a `transfer`,
at the `Sim` level. -/
theorem sim_sub (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.SUB, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.sub (vs.env a) (vs.env b))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_SUB_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: b :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (stackSim_sub vs es es' L c a b f cost arg hc hstep) hsim

/-! ### Comparisons (`LT`/`GT`/`EQ`)

The condition-producing ops needed for guards/`require`s and branch predicates.
Each dispatches through `dispatchBinary` exactly like `ADD`/`SUB`, so the strong
shapes and `Sim` lifts are the same template. -/

/-- Strong `LT` shape (dispatches to `UInt256.lt`). -/
theorem step_LT_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.LT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.stack = UInt256.lt hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  solve_binop_shape hStep hStk

/-- Strong `GT` shape (dispatches to `UInt256.gt`). -/
theorem step_GT_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.GT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.stack = UInt256.gt hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  solve_binop_shape hStep hStk

/-- Strong `EQ` shape (dispatches to `UInt256.eq`). -/
theorem step_EQ_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.EQ, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.stack = UInt256.eq hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  solve_binop_shape hStep hStk

/-- **LT preserves the full simulation.** -/
theorem sim_lt (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.LT, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.lt (vs.env a) (vs.env b))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, hshape, henv, hacc⟩ :=
    step_LT_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: b :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (fun _ => stackSim_binop_of_shape vs es' L c a b UInt256.lt hc hshape) hsim

/-- **GT preserves the full simulation.** -/
theorem sim_gt (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.GT, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.gt (vs.env a) (vs.env b))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, hshape, henv, hacc⟩ :=
    step_GT_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: b :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (fun _ => stackSim_binop_of_shape vs es' L c a b UInt256.gt hc hshape) hsim

/-- **EQ preserves the full simulation.** -/
theorem sim_eq (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hc : c ∉ a :: b :: L)
    (hstep : EVM.step (f + 1) cost (some (.EQ, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set c (UInt256.eq (vs.env a) (vs.env b))) es' (c :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, hshape, henv, hacc⟩ :=
    step_EQ_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs _ es es' (a :: b :: L) (c :: L)
    (VenomState.set_storage vs c _) hacc henv
    (fun _ => stackSim_binop_of_shape vs es' L c a b UInt256.eq hc hshape) hsim

/-! ### Scheduling primitives at the full-`Sim` level

`DUP1`/`SWAP1` make no SSA-state change, so they trivially preserve the storage
half (the Venom `storage` is unchanged and the EVM account map is too). The
`Frame` library shapes expose `executionEnv` but not `accountMap`; the small
`accountMap`-only lemmas below close that gap with the same reduction. -/

/-- `DUP1` preserves the account map (it only rearranges the stack). -/
theorem step_DUP1_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP1, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 1 (hd :: tl) = [hd] from rfl,
             List.length_singleton, ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- `SWAP1` preserves the account map (it only rearranges the stack). -/
theorem step_SWAP1_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP1, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (1 + 1) (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show List.drop (1 + 1) (hd1 :: hd2 :: tl) = tl from rfl,
             show ([hd1, hd2] : List UInt256).length = 1 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- **DUP1 preserves the full simulation** — duplicate a live value, no SSA
change. -/
theorem sim_dup1 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP1, arg)) es = .ok es')
    (hsim : Sim vs es (a :: L)) :
    Sim vs es' (a :: a :: L) := by
  have hstk : es.stack = vs.env a :: L.map vs.env := by rw [hsim.1, List.map_cons]
  obtain ⟨_, _, henv⟩ := step_DUP1_shape es es' f cost arg (vs.env a) (L.map vs.env) hstk hstep
  have hacc := step_DUP1_accountMap es es' f cost arg (vs.env a) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs vs es es' (a :: L) (a :: a :: L) rfl hacc henv
    (stackSim_dup1 vs es es' L a f cost arg hstep) hsim

/-- **SWAP1 preserves the full simulation** — reorder the top two live values,
no SSA change. -/
theorem sim_swap1 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP1, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim vs es' (b :: a :: L) := by
  have hstk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv⟩ :=
    step_SWAP1_shape es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  have hacc :=
    step_SWAP1_accountMap es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs vs es es' (a :: b :: L) (b :: a :: L) rfl hacc henv
    (stackSim_swap1 vs es es' L a b f cost arg hstep) hsim

/-! ### Depth-2 scheduling (`DUP2`/`SWAP2`)

The next reach of the scheduler: `DUP2` duplicates the second live value,
`SWAP2` exchanges the top with the third. Together with `DUP1`/`SWAP1` this
covers stack depth 3 — enough to position both operands of a binary op. The
deeper `DUPn`/`SWAPn` follow the same template (each opcode is distinct, but the
`dup`/`swap` body is uniform). -/

/-- Strong `DUP2` shape: `[hd1, hd2, …] ↦ [hd2, hd1, hd2, …]`. -/
theorem step_DUP2_shape_strong
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP2, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd2 :: hd1 :: hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 2 (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show ([hd1, hd2] : List UInt256).length = 2 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl, rfl⟩
  show (([hd1, hd2] : List UInt256).getLast! :: (hd1 :: hd2 :: tl)) = hd2 :: hd1 :: hd2 :: tl
  rfl

/-- Strong `SWAP2` shape: `[hd1, hd2, hd3, …] ↦ [hd3, hd2, hd1, …]`. -/
theorem step_SWAP2_shape_strong
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP2, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd3 :: hd2 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show List.drop (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 2 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl, rfl⟩
  show (([hd1, hd2, hd3] : List UInt256).getLast!
          :: ([hd1, hd2, hd3] : List UInt256).tail!.dropLast
          ++ [([hd1, hd2, hd3] : List UInt256).head!] ++ tl) = hd3 :: hd2 :: hd1 :: tl
  rfl

/-- **DUP2 (stack).** Duplicate the second live value: `a :: b :: L ↦
b :: a :: b :: L`. -/
theorem stackSim_dup2 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP2, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: L)) :
    StackSim vs es' (b :: a :: b :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_DUP2_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hStk hstep
  unfold StackSim
  rw [hstk']; simp only [List.map_cons]

/-- **SWAP2 (stack).** Exchange the top and third live values: `a :: b :: c :: L
↦ c :: b :: a :: L`. -/
theorem stackSim_swap2 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP2, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: c :: L)) :
    StackSim vs es' (c :: b :: a :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_SWAP2_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (L.map vs.env)
      hStk hstep
  unfold StackSim
  rw [hstk']; simp only [List.map_cons]

/-- **DUP2 preserves the full simulation.** -/
theorem sim_dup2 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP2, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: L)) :
    Sim vs es' (b :: a :: b :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_DUP2_shape_strong es es' f cost arg (vs.env a) (vs.env b) (L.map vs.env) hStk hstep
  exact sim_of_pure_step vs vs es es' (a :: b :: L) (b :: a :: b :: L) rfl hacc henv
    (stackSim_dup2 vs es es' L a b f cost arg hstep) hsim

/-- **SWAP2 preserves the full simulation.** -/
theorem sim_swap2 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP2, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: c :: L)) :
    Sim vs es' (c :: b :: a :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_SWAP2_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (L.map vs.env)
      hStk hstep
  exact sim_of_pure_step vs vs es es' (a :: b :: c :: L) (c :: b :: a :: L) rfl hacc henv
    (stackSim_swap2 vs es es' L a b c f cost arg hstep) hsim

/-- **Worked reorder.** `SWAP2` is its own inverse: applying it twice returns to
the original layout — `Sim` end-to-end. A first sanity check that the
scheduler's moves compose correctly under the simulation. -/
example (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg1 arg2 : Option (UInt256 × Nat))
    (h1 : EVM.step (f + 1) cost (some (.SWAP2, arg1)) es = .ok es1)
    (h2 : EVM.step (f + 1) cost (some (.SWAP2, arg2)) es1 = .ok es2)
    (hsim : Sim vs es (a :: b :: c :: L)) :
    Sim vs es2 (a :: b :: c :: L) :=
  sim_swap2 vs es1 es2 L c b a f cost arg2 h2
    (sim_swap2 vs es es1 L a b c f cost arg1 h1 hsim)

/-! ### Depth-3 scheduling and the general `DUPn`/`SWAPn` stack effect

`dup_stack_general` / `swap_stack_general` capture the *uniform* stack math of
every `DUPk` / `SWAPk` (over the `dup`/`swap` transformers, any depth `n`) — the
basis of the `_stack_reorder` scheduler. Because the 16 `DUPk`/`SWAPk` are
distinct opcodes (no parametric `EVM.step` lemma), the per-opcode shapes are
still written out; `DUP3`/`SWAP3` here extend usable scheduling to stack depth 4,
following the same template. -/

/-- **General `dup n` stack effect.** With the stack at least `n` deep, `dup n`
pushes the `n`-th element (`(take n).getLast!`) and preserves env/account map. -/
theorem dup_stack_general (n : ℕ) (s s' : EVM.State)
    (hlen : n ≤ s.stack.length) (h : EvmYul.dup n s = .ok s') :
    s'.stack = (s.stack.take n).getLast! :: s.stack ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EvmYul.dup at h
  simp only [List.length_take, Nat.min_eq_left hlen, if_true, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, rfl, rfl⟩

/-- **General `swap n` stack effect.** With the stack at least `n+1` deep,
`swap n` exchanges the top and `(n+1)`-th elements, preserving env/account map. -/
theorem swap_stack_general (n : ℕ) (s s' : EVM.State)
    (hlen : n + 1 ≤ s.stack.length) (h : EvmYul.swap n s = .ok s') :
    s'.stack = (s.stack.take (n + 1)).getLast! :: (s.stack.take (n + 1)).tail!.dropLast
                 ++ [(s.stack.take (n + 1)).head!] ++ s.stack.drop (n + 1) ∧
    s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
  unfold EvmYul.swap at h
  simp only [List.length_take, Nat.min_eq_left hlen, if_true, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, rfl, rfl⟩

/-- Strong `DUP3` shape: `[h1,h2,h3,…] ↦ [h3,h1,h2,h3,…]`. -/
theorem step_DUP3_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.DUP3, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd3 :: hd1 :: hd2 :: hd3 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 3 (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 3 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl, rfl⟩
  show (([hd1, hd2, hd3] : List UInt256).getLast! :: (hd1 :: hd2 :: hd3 :: tl))
       = hd3 :: hd1 :: hd2 :: hd3 :: tl
  rfl

/-- Strong `SWAP3` shape: `[h1,h2,h3,h4,…] ↦ [h4,h2,h3,h1,…]`. -/
theorem step_SWAP3_shape_strong
    (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f + 1) cost (some (.SWAP3, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd4 :: hd2 :: hd3 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = [hd1, hd2, hd3, hd4] from rfl,
             show List.drop (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3, hd4] : List UInt256).length = 3 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl, rfl⟩
  show (([hd1, hd2, hd3, hd4] : List UInt256).getLast!
          :: ([hd1, hd2, hd3, hd4] : List UInt256).tail!.dropLast
          ++ [([hd1, hd2, hd3, hd4] : List UInt256).head!] ++ tl)
       = hd4 :: hd2 :: hd3 :: hd1 :: tl
  rfl

/-- **DUP3 (stack).** Duplicate the third live value: `a :: b :: c :: L ↦
c :: a :: b :: c :: L`. -/
theorem stackSim_dup3 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP3, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: c :: L)) :
    StackSim vs es' (c :: a :: b :: c :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_DUP3_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (L.map vs.env)
      hStk hstep
  unfold StackSim
  rw [hstk']; simp only [List.map_cons]

/-- **SWAP3 (stack).** Exchange the top and fourth live values: `a :: b :: c ::
d :: L ↦ d :: b :: c :: a :: L`. -/
theorem stackSim_swap3 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c d : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP3, arg)) es = .ok es')
    (h : StackSim vs es (a :: b :: c :: d :: L)) :
    StackSim vs es' (d :: b :: c :: a :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: vs.env d :: L.map vs.env := by
    rw [h, List.map_cons, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, hstk', _, _⟩ :=
    step_SWAP3_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (vs.env d)
      (L.map vs.env) hStk hstep
  unfold StackSim
  rw [hstk']; simp only [List.map_cons]

/-- **DUP3 preserves the full simulation.** -/
theorem sim_dup3 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.DUP3, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: c :: L)) :
    Sim vs es' (c :: a :: b :: c :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_DUP3_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (L.map vs.env)
      hStk hstep
  exact sim_of_pure_step vs vs es es' (a :: b :: c :: L) (c :: a :: b :: c :: L) rfl hacc henv
    (stackSim_dup3 vs es es' L a b c f cost arg hstep) hsim

/-- **SWAP3 preserves the full simulation.** -/
theorem sim_swap3 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c d : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP3, arg)) es = .ok es')
    (hsim : Sim vs es (a :: b :: c :: d :: L)) :
    Sim vs es' (d :: b :: c :: a :: L) := by
  have hStk : es.stack = vs.env a :: vs.env b :: vs.env c :: vs.env d :: L.map vs.env := by
    rw [hsim.1, List.map_cons, List.map_cons, List.map_cons, List.map_cons]
  obtain ⟨_, _, henv, hacc⟩ :=
    step_SWAP3_shape_strong es es' f cost arg (vs.env a) (vs.env b) (vs.env c) (vs.env d)
      (L.map vs.env) hStk hstep
  exact sim_of_pure_step vs vs es es' (a :: b :: c :: d :: L) (d :: b :: c :: a :: L) rfl hacc henv
    (stackSim_swap3 vs es es' L a b c d f cost arg hstep) hsim

/-- **Worked scheduling for a non-adjacent binary op.** To lower `%r = sub %c, %a`
when the live layout is `[a, b, c]` — the operands `%c` (3rd) and `%a` (1st) are
neither on top nor adjacent — the scheduler reorders with `SWAP1; SWAP2` to bring
them to the top as `c :: a :: …`, then `SUB` consumes them; the intervening `%b`
is preserved. This is the operand-positioning a real `_stack_reorder` performs
before each instruction, verified end-to-end under `Sim`. -/
theorem scheduled_sub (vs : VenomState) (es0 es1 es2 es3 : EVM.State) (L : Layout)
    (a b c r : VarName) (f cost : ℕ) (s1 s2 sub : Option (UInt256 × Nat))
    (hr : r ∉ c :: a :: b :: L)
    (hw1 : EVM.step (f + 1) cost (some (.SWAP1, s1)) es0 = .ok es1)
    (hw2 : EVM.step (f + 1) cost (some (.SWAP2, s2)) es1 = .ok es2)
    (hsub : EVM.step (f + 1) cost (some (.SUB, sub)) es2 = .ok es3)
    (hsim : Sim vs es0 (a :: b :: c :: L)) :
    Sim (vs.set r (UInt256.sub (vs.env c) (vs.env a))) es3 (r :: b :: L) := by
  have h1 : Sim vs es1 (b :: a :: c :: L) :=
    sim_swap1 vs es0 es1 (c :: L) a b f cost s1 hw1 hsim
  have h2 : Sim vs es2 (c :: a :: b :: L) :=
    sim_swap2 vs es1 es2 L b a c f cost s2 hw2 h1
  exact sim_sub vs es2 es3 (b :: L) r c a f cost sub hr hsub h2

/-! ### The reorder composition backbone (`_stack_reorder`)

A `_stack_reorder` is a *sequence* of `SWAP` moves taking the current stack
layout to the one the next instruction needs. Its correctness splits into:

* **soundness / composition** — each move preserves `Sim`, and a chain of moves
  composes; this is captured here (`Reorder`, `reorder_refl`/`trans`, the move
  generators, and worked permutations like the 3-cycle `reorder_rot3`).
* **completeness / synthesis** — *every* target permutation is reachable, and an
  algorithm emits the move sequence. **Proved at the layout level** (`perm_reaches`,
  no axioms): the transpositions `(0,k)` (each `SWAPk` swaps the top with the
  `k`-th element) generate the full symmetric group, and the constructive proof
  *is* the synthesis (`List.Perm` head-swap generation + cons-congruence by
  conjugation `(1,k+1) = (0,1)(0,k+1)(0,1)`). The concrete `SWAP1/2/3` realize the
  `(0,1)/(0,2)/(0,3)` moves (`starSwap_of_swap*`); the only remainder is the
  mechanical EVM realization of the deeper `SWAP4..16` opcodes. -/

/-- A verified **reorder**: a (possibly multi-step) stack rearrangement carrying
the simulation from layout `L` to `L'` with the SSA state `vs` fixed (pure
scheduling — nothing is computed, values are only repositioned). -/
def Reorder (vs : VenomState) (es : EVM.State) (L : Layout)
            (es' : EVM.State) (L' : Layout) : Prop :=
  Sim vs es L → Sim vs es' L'

theorem reorder_refl (vs : VenomState) (es : EVM.State) (L : Layout) :
    Reorder vs es L es L := id

theorem reorder_trans {vs : VenomState} {es0 es1 es2 : EVM.State} {L0 L1 L2 : Layout}
    (h1 : Reorder vs es0 L0 es1 L1) (h2 : Reorder vs es1 L1 es2 L2) :
    Reorder vs es0 L0 es2 L2 := h2 ∘ h1

/-- `SWAP1` as a reorder move (the transposition `(0,1)`). -/
theorem reorder_swap1 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP1, arg)) es = .ok es') :
    Reorder vs es (a :: b :: L) es' (b :: a :: L) :=
  fun h => sim_swap1 vs es es' L a b f cost arg hstep h

/-- `SWAP2` as a reorder move (the transposition `(0,2)`). -/
theorem reorder_swap2 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP2, arg)) es = .ok es') :
    Reorder vs es (a :: b :: c :: L) es' (c :: b :: a :: L) :=
  fun h => sim_swap2 vs es es' L a b c f cost arg hstep h

/-- `SWAP3` as a reorder move (the transposition `(0,3)`). -/
theorem reorder_swap3 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b c d : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP3, arg)) es = .ok es') :
    Reorder vs es (a :: b :: c :: d :: L) es' (d :: b :: c :: a :: L) :=
  fun h => sim_swap3 vs es es' L a b c d f cost arg hstep h

/-- **Worked reorder: a 3-cycle.** `SWAP1; SWAP2` rotates the top three live
values `[a, b, c] ↦ [c, a, b]` — a cyclic permutation realized as a chain of two
transposition moves (so the reorder reaches beyond single transpositions). -/
theorem reorder_rot3 (vs : VenomState) (es0 es1 es2 : EVM.State) (L : Layout)
    (a b c : VarName) (f cost : ℕ) (s1 s2 : Option (UInt256 × Nat))
    (hw1 : EVM.step (f + 1) cost (some (.SWAP1, s1)) es0 = .ok es1)
    (hw2 : EVM.step (f + 1) cost (some (.SWAP2, s2)) es1 = .ok es2) :
    Reorder vs es0 (a :: b :: c :: L) es2 (c :: a :: b :: L) :=
  reorder_trans (reorder_swap1 vs es0 es1 (c :: L) a b f cost s1 hw1)
                (reorder_swap2 vs es1 es2 L b a c f cost s2 hw2)

/-- **Worked reorder: a 4-cycle.** `SWAP1; SWAP2; SWAP3` rotates the top four live
values `[a, b, c, d] ↦ [d, a, b, c]` — a longer permutation than `reorder_rot3`,
reached by chaining three transposition moves. Evidence the `(0,k)` generators
compose toward arbitrary permutations (the completeness crux remains the general
synthesis algorithm). -/
theorem reorder_rot4 (vs : VenomState) (es0 es1 es2 es3 : EVM.State) (L : Layout)
    (a b c d : VarName) (f cost : ℕ) (s1 s2 s3 : Option (UInt256 × Nat))
    (hw1 : EVM.step (f + 1) cost (some (.SWAP1, s1)) es0 = .ok es1)
    (hw2 : EVM.step (f + 1) cost (some (.SWAP2, s2)) es1 = .ok es2)
    (hw3 : EVM.step (f + 1) cost (some (.SWAP3, s3)) es2 = .ok es3) :
    Reorder vs es0 (a :: b :: c :: d :: L) es3 (d :: a :: b :: c :: L) :=
  reorder_trans
    (reorder_trans (reorder_swap1 vs es0 es1 (c :: d :: L) a b f cost s1 hw1)
                   (reorder_swap2 vs es1 es2 (d :: L) b a c f cost s2 hw2))
    (reorder_swap3 vs es2 es3 L c a b d f cost s3 hw3)

/-! #### Reorder completeness (the star transpositions generate every permutation)

The soundness side above realizes each `SWAPk` move; this is the **completeness**
side — at the *layout* level (decoupled from the per-opcode EVM steps): the
`(0,k)` star transpositions reach **any** target permutation, and the proof is
constructive (it *is* the synthesis algorithm). The key step is cons-congruence
(reorder the tail under a fixed head) via conjugation `(1,k+1) = (0,1)(0,k+1)(0,1)`;
`List.Perm`'s head-swap generation then closes it. -/

/-- A `SWAPk` move at the layout level: swap the head `a` with the element `b` at
depth `|pre|+1` — the star transposition `(0, k)`. -/
inductive StarSwap : Layout → Layout → Prop
  | mk (a b : VarName) (pre post : Layout) :
      StarSwap (a :: pre ++ b :: post) (b :: pre ++ a :: post)

/-- Reachability by a finite sequence of `SWAPk` moves (the reorder closure). -/
inductive Reaches : Layout → Layout → Prop
  | refl (L : Layout) : Reaches L L
  | step {L L1 L2 : Layout} (h1 : StarSwap L L1) (h2 : Reaches L1 L2) : Reaches L L2

theorem reaches_single {L L' : Layout} (h : StarSwap L L') : Reaches L L' := .step h (.refl _)

theorem reaches_trans {L L1 L2 : Layout} (h1 : Reaches L L1) (h2 : Reaches L1 L2) :
    Reaches L L2 := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- Head-swap `[y,x,…] ↦ [x,y,…]` is one star move (`pre = []`). -/
theorem reaches_head_swap (x y : VarName) (l : Layout) :
    Reaches (y :: x :: l) (x :: y :: l) :=
  reaches_single (by simpa using StarSwap.mk y x [] l)

/-- **Conjugation:** lifting one star move under a fixed head costs three star
moves — `(1,k+1) = (0,1)(0,k+1)(0,1)`. -/
theorem cons_starswap (x : VarName) {l l1 : Layout} (h : StarSwap l l1) :
    Reaches (x :: l) (x :: l1) := by
  cases h with
  | mk a b pre post =>
    have s1 : StarSwap (x :: a :: pre ++ b :: post) (a :: x :: pre ++ b :: post) := by
      simpa using StarSwap.mk x a [] (pre ++ b :: post)
    have s2 : StarSwap (a :: x :: pre ++ b :: post) (b :: x :: pre ++ a :: post) := by
      simpa using StarSwap.mk a b (x :: pre) post
    have s3 : StarSwap (b :: x :: pre ++ a :: post) (x :: b :: pre ++ a :: post) := by
      simpa using StarSwap.mk b x [] (pre ++ a :: post)
    exact .step s1 (.step s2 (reaches_single s3))

/-- **Cons-congruence:** reorder the tail under a fixed head. -/
theorem cons_reaches (x : VarName) {l l' : Layout} (h : Reaches l l') :
    Reaches (x :: l) (x :: l') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact reaches_trans (cons_starswap x hs) ih

/-- **Reorder completeness.** Any layout permutation is reachable by `SWAPk`
moves — the star transpositions `(0,k)` generate the full symmetric group on the
stack, and this constructive proof *is* the synthesis algorithm (no axioms). -/
theorem perm_reaches {l l' : Layout} (h : l.Perm l') : Reaches l l' := by
  induction h with
  | nil => exact .refl _
  | cons x _ ih => exact cons_reaches x ih
  | swap x y l => exact reaches_head_swap x y l
  | trans _ _ ih1 ih2 => exact reaches_trans ih1 ih2

/-- The concrete `SWAP1` realizes the `(0,1)` star move (`reorder_swap1`'s layout
effect). -/
theorem starSwap_of_swap1 (a b : VarName) (L : Layout) :
    StarSwap (a :: b :: L) (b :: a :: L) := by simpa using StarSwap.mk a b [] L
/-- `SWAP2` realizes the `(0,2)` star move. -/
theorem starSwap_of_swap2 (a b c : VarName) (L : Layout) :
    StarSwap (a :: b :: c :: L) (c :: b :: a :: L) := by simpa using StarSwap.mk a c [b] L
/-- `SWAP3` realizes the `(0,3)` star move. -/
theorem starSwap_of_swap3 (a b c d : VarName) (L : Layout) :
    StarSwap (a :: b :: c :: d :: L) (d :: b :: c :: a :: L) := by simpa using StarSwap.mk a d [b, c] L

/-! ### Deep `SWAP4..16`: the EVM realization of the remaining `StarSwap` moves

`perm_reaches` decomposes any permutation into `StarSwap (0,k)` moves; `SWAP1/2/3`
realize `k = 1,2,3`. These complete the realization up to the EVM's deepest swap,
`SWAP16`. The per-opcode `step_SWAPk_shape` (one `mk_swap_shape` macro line each)
gives the byte-level effect, and the general `sim_swap_via_shape` carries the
simulation across *any* such move — so every `StarSwap` of depth ≤ 16 is realized
on the real EVM under `Sim`. -/

theorem getLast!_concat {α} [Inhabited α] (l : List α) (x : α) : (l ++ [x]).getLast! = x := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.cons_append]
    cases as with
    | nil => rfl
    | cons b bs =>
      rw [show (a :: (b :: bs ++ [x])).getLast! = (b :: bs ++ [x]).getLast! from rfl]; exact ih

local macro "mk_swap_shape" name:ident idx:num opc:term : command => `(
  theorem $name (s s' : EVM.State) (f cost : ℕ) (arg : Option (UInt256 × Nat))
      (heads : List UInt256) (tl : Stack UInt256) (hlen : heads.length = $idx + 1)
      (hStk : s.stack = heads ++ tl)
      (hStep : EVM.step (f + 1) cost (some ($opc, arg)) s = .ok s') :
      s'.stack = heads.getLast! :: heads.tail!.dropLast ++ [heads.head!] ++ tl ∧
      s'.executionEnv = s.executionEnv ∧ s'.accountMap = s.accountMap := by
    unfold EVM.step at hStep
    simp only [bind, Except.bind, pure, Except.pure] at hStep
    unfold EvmYul.step at hStep
    simp only [Id.run] at hStep
    unfold swap at hStep
    rw [hStk] at hStep
    simp only [show List.take ($idx + 1) (heads ++ tl) = heads from List.take_left' hlen,
               show List.drop ($idx + 1) (heads ++ tl) = tl from List.drop_left' hlen,
               hlen, ↓reduceIte, Except.ok.injEq] at hStep
    subst hStep
    refine ⟨rfl, rfl, rfl⟩)

mk_swap_shape step_SWAP4_shape 4 (.SWAP4)
mk_swap_shape step_SWAP5_shape 5 (.SWAP5)
mk_swap_shape step_SWAP6_shape 6 (.SWAP6)
mk_swap_shape step_SWAP7_shape 7 (.SWAP7)
mk_swap_shape step_SWAP8_shape 8 (.SWAP8)
mk_swap_shape step_SWAP9_shape 9 (.SWAP9)
mk_swap_shape step_SWAP10_shape 10 (.SWAP10)
mk_swap_shape step_SWAP11_shape 11 (.SWAP11)
mk_swap_shape step_SWAP12_shape 12 (.SWAP12)
mk_swap_shape step_SWAP13_shape 13 (.SWAP13)
mk_swap_shape step_SWAP14_shape 14 (.SWAP14)
mk_swap_shape step_SWAP15_shape 15 (.SWAP15)
mk_swap_shape step_SWAP16_shape 16 (.SWAP16)

theorem sim_swap_via_shape (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (pre : Layout)
    (hsh : es'.stack = ((a :: pre ++ [b]).map vs.env).getLast!
             :: ((a :: pre ++ [b]).map vs.env).tail!.dropLast
             ++ [((a :: pre ++ [b]).map vs.env).head!] ++ L.map vs.env)
    (henv : es'.executionEnv = es.executionEnv) (hacc : es'.accountMap = es.accountMap)
    (hsim : Sim vs es (a :: pre ++ b :: L)) :
    Sim vs es' (b :: pre ++ a :: L) := by
  have heq : (a :: pre ++ [b]).map vs.env = (vs.env a :: pre.map vs.env) ++ [vs.env b] := by
    simp [List.map_append, List.map_cons]
  have key : es'.stack = (b :: pre ++ a :: L).map vs.env := by
    rw [hsh, heq, getLast!_concat]
    simp only [List.cons_append, List.head!_cons, List.tail!_cons, List.dropLast_concat,
      List.map_append, List.map_cons, List.append_assoc, List.nil_append]
  refine ⟨key, fun x => ?_⟩
  rw [show sloadVal es' x = sloadVal es x from by
        simp only [sloadVal, EvmYul.State.lookupAccount, hacc, henv]]
  exact hsim.2 x

/-- The same as a **reorder move** (`StarSwap (0,k)` for any `k`, from the EVM
`SWAPk` shape). -/
theorem reorder_swap_via_shape (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a b : VarName) (pre : Layout)
    (hsh : es'.stack = ((a :: pre ++ [b]).map vs.env).getLast!
             :: ((a :: pre ++ [b]).map vs.env).tail!.dropLast
             ++ [((a :: pre ++ [b]).map vs.env).head!] ++ L.map vs.env)
    (henv : es'.executionEnv = es.executionEnv) (hacc : es'.accountMap = es.accountMap) :
    Reorder vs es (a :: pre ++ b :: L) es' (b :: pre ++ a :: L) :=
  fun h => sim_swap_via_shape vs es es' L a b pre hsh henv hacc h

/-- **Worked SWAP4 realization.** The deep transposition `(0,4)` —
`a :: m₁ :: m₂ :: m₃ :: b :: L ↦ b :: m₁ :: m₂ :: m₃ :: a :: L` (the `StarSwap.mk a b [m₁,m₂,m₃] L`
move) — carried by the EVM `SWAP4` under `Sim`. SWAP5..16 are identical via their
generated shapes; this completes the EVM realization of `perm_reaches`'s moves up
to the EVM's SWAP16. -/
theorem sim_swap4 (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a m₁ m₂ m₃ b : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.SWAP4, arg)) es = .ok es')
    (hsim : Sim vs es (a :: m₁ :: m₂ :: m₃ :: b :: L)) :
    Sim vs es' (b :: m₁ :: m₂ :: m₃ :: a :: L) := by
  have hstk : es.stack = ([a, m₁, m₂, m₃, b].map vs.env) ++ L.map vs.env := by
    rw [hsim.1]; simp [List.map_cons]
  obtain ⟨hsh, henv, hacc⟩ := step_SWAP4_shape es es' f cost arg _ _ rfl hstk hstep
  exact sim_swap_via_shape vs es es' L a b [m₁, m₂, m₃] hsh henv hacc hsim

/-- **Worked peephole, full state.** The optimized balance load
`%s = not %addr; %b = sload %s` carries `Sim` end-to-end: the `~addr` slot
computation and its `SLOAD`, with stack realization *and* storage agreement
preserved. The loaded value is exactly the balance at the `~addr` slot,
`storage(~addr)`. -/
example (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (s b addr : VarName) (f cost : ℕ) (argN argS : Option (UInt256 × Nat))
    (hs : s ∉ addr :: L) (hb : b ∉ s :: L)
    (hn : EVM.step (f + 1) cost (some (.NOT, argN)) es = .ok es1)
    (hsl : EVM.step (f + 1) cost (some (.SLOAD, argS)) es1 = .ok es2)
    (hsim : Sim vs es (addr :: L)) :
    Sim ((vs.set s (UInt256.lnot (vs.env addr))).set b
          (vs.storage (UInt256.lnot (vs.env addr)))) es2 (b :: L) := by
  have h1 := sim_not vs es es1 L s addr f cost argN hs hn hsim
  have h2 := sim_sload (vs.set s (UInt256.lnot (vs.env addr))) es1 es2 L b s
              f cost argS hb hsl h1
  simpa using h2

/-! ## Control flow and stack-drop (toward M3 / CFG)

The single-block work above is straight-line. These primitives cross basic-block
boundaries and discard dead values — the first M3 (CFG) bricks. `POP` discards;
`JUMP`/`JUMPI` transfer control while leaving the live layout (and storage
agreement) intact, setting `pc` to the resolved target. None touch the account
map, so the storage half of `Sim` carries through (account-map lemmas below;
`POP`'s strong shape already exposes it). -/

/-- `JUMP` preserves the account map (only pops the target and sets `pc`). -/
theorem step_JUMP_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMP, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- `JUMPI` preserves the account map (pops target/condition, sets `pc`). -/
theorem step_JUMPI_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMPI, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- **POP drops the top live value** (a dead value the scheduler discards),
preserving the full simulation. -/
theorem sim_pop (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (a : VarName) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.POP, arg)) es = .ok es')
    (hsim : Sim vs es (a :: L)) :
    Sim vs es' L := by
  have hstk : es.stack = vs.env a :: L.map vs.env := by rw [hsim.1, List.map_cons]
  obtain ⟨_, hstack', henv, hacc⟩ :=
    step_POP_shape_strong es es' f cost arg (vs.env a) (L.map vs.env) hstk hstep
  exact sim_of_pure_step vs vs es es' (a :: L) L rfl hacc henv (fun _ => hstack') hsim

/-- **Unconditional jump (`JUMP`) preserves the simulation and transfers
control.** The lowering of `jmp @label` pushes the target PC above the live
layout, then `JUMP` pops it and sets `pc := target`, leaving the layout `L` (and
storage agreement) intact — the control-flow primitive for crossing a CFG
edge. -/
theorem sim_jump (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (target : UInt256) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstk : es.stack = target :: L.map vs.env)
    (hsto : ∀ x, sloadVal es x = vs.storage x)
    (hjump : EVM.step (f + 1) cost (some (.JUMP, arg)) es = .ok es') :
    Sim vs es' L ∧ es'.pc = target := by
  obtain ⟨hpc, hstack', henv⟩ :=
    step_JUMP_shape es es' f cost arg target (L.map vs.env) hstk hjump
  have hacc := step_JUMP_accountMap es es' f cost arg target (L.map vs.env) hstk hjump
  refine ⟨⟨hstack', fun x => ?_⟩, hpc⟩
  rw [show sloadVal es' x = sloadVal es x from by
        simp only [sloadVal, EvmYul.State.lookupAccount, hacc, henv]]
  exact hsto x

/-- **Conditional jump (`JUMPI`) preserves the simulation and branches.** The
lowering of `jnz %c, @then` pushes the target above the condition value of `%c`,
then `JUMPI` pops both, leaving the layout `L`, and sets `pc` to the target when
`%c ≠ 0` (taken) or the fallthrough otherwise. -/
theorem sim_jumpi (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (c : VarName) (target : UInt256) (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstk : es.stack = target :: vs.env c :: L.map vs.env)
    (hsto : ∀ x, sloadVal es x = vs.storage x)
    (hjumpi : EVM.step (f + 1) cost (some (.JUMPI, arg)) es = .ok es') :
    Sim vs es' L ∧ es'.pc = (if vs.env c != ⟨0⟩ then target else es.pc + ⟨1⟩) := by
  obtain ⟨hpc, hstack', henv⟩ :=
    step_JUMPI_shape es es' f cost arg target (vs.env c) (L.map vs.env) hstk hjumpi
  have hacc := step_JUMPI_accountMap es es' f cost arg target (vs.env c) (L.map vs.env) hstk hjumpi
  refine ⟨⟨hstack', fun x => ?_⟩, hpc⟩
  rw [show sloadVal es' x = sloadVal es x from by
        simp only [sloadVal, EvmYul.State.lookupAccount, hacc, henv]]
  exact hsto x

/-- **JUMPDEST (a block's entry label) preserves the full simulation.** The
landing pad after a control transfer. -/
theorem sim_jumpdest (vs : VenomState) (es es' : EVM.State) (L : Layout)
    (f cost : ℕ) (arg : Option (UInt256 × Nat))
    (hstep : EVM.step (f + 1) cost (some (.JUMPDEST, arg)) es = .ok es')
    (hsim : Sim vs es L) :
    Sim vs es' L := by
  obtain ⟨_, hstack', henv, hacc⟩ := step_JUMPDEST_shape_strong es es' f cost arg hstep
  exact sim_of_pure_step vs vs es es' L L rfl hacc henv (fun h => hstack'.trans h) hsim

/-- **Worked CFG edge (unconditional).** Block 0's terminator `JUMP`s to block 1,
control lands on block 1's `JUMPDEST`, and block 1 computes `%c = not %a` — all
under one `Sim`. The first verified crossing of a CFG edge into a working block:
`sim_jump` carries the simulation across the edge and pins `pc` to the target,
`sim_jumpdest` lands, and instruction selection resumes. -/
example (vs : VenomState) (es es1 es2 es3 : EVM.State) (L : Layout)
    (c a : VarName) (target : UInt256) (f cost : ℕ)
    (argJ argD argN : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (hstk : es.stack = target :: (a :: L).map vs.env)
    (hsto : ∀ x, sloadVal es x = vs.storage x)
    (hjump : EVM.step (f + 1) cost (some (.JUMP, argJ)) es = .ok es1)
    (hjd : EVM.step (f + 1) cost (some (.JUMPDEST, argD)) es1 = .ok es2)
    (hnot : EVM.step (f + 1) cost (some (.NOT, argN)) es2 = .ok es3) :
    Sim (vs.set c (UInt256.lnot (vs.env a))) es3 (c :: L) ∧ es1.pc = target := by
  obtain ⟨hsim1, hpc⟩ := sim_jump vs es es1 (a :: L) target f cost argJ hstk hsto hjump
  have hsim2 := sim_jumpdest vs es1 es2 (a :: L) f cost argD hjd hsim1
  exact ⟨sim_not vs es2 es3 L c a f cost argN hc hnot hsim2, hpc⟩

/-- **Worked CFG edge (conditional, taken arm).** Block 0 ends in `jnz %cond,
@then`; the condition is nonzero, so control reaches block 1, lands on its
`JUMPDEST`, and block 1 computes `%c = not %a` — `Sim` preserved across the
conditional edge. -/
example (vs : VenomState) (es es1 es2 es3 : EVM.State) (L : Layout)
    (c a cond : VarName) (target : UInt256) (f cost : ℕ)
    (argJ argD argN : Option (UInt256 × Nat))
    (hc : c ∉ a :: L)
    (htaken : (vs.env cond != (⟨0⟩ : UInt256)) = true)
    (hstk : es.stack = target :: vs.env cond :: (a :: L).map vs.env)
    (hsto : ∀ x, sloadVal es x = vs.storage x)
    (hjumpi : EVM.step (f + 1) cost (some (.JUMPI, argJ)) es = .ok es1)
    (hjd : EVM.step (f + 1) cost (some (.JUMPDEST, argD)) es1 = .ok es2)
    (hnot : EVM.step (f + 1) cost (some (.NOT, argN)) es2 = .ok es3) :
    Sim (vs.set c (UInt256.lnot (vs.env a))) es3 (c :: L) ∧ es1.pc = target := by
  obtain ⟨hsim1, hpc⟩ := sim_jumpi vs es es1 (a :: L) cond target f cost argJ hstk hsto hjumpi
  refine ⟨?_, by rw [hpc, htaken]; rfl⟩
  exact sim_not vs es2 es3 L c a f cost argN hc hnot
    (sim_jumpdest vs es1 es2 (a :: L) f cost argD hjd hsim1)

/-! ### Reconvergence: `jmp` to a join, and a worked diamond (phi)

The dual of branching is *joining*: an arm leaves its value in the slot the join
block expects and `jmp`s there. `sim_jmp` is that reconvergence edge; the worked
diamond below threads `Sim` through a full branch-and-join, so the join reads the
phi value the taken arm produced. -/

/-- `PUSH1` preserves the account map. -/
theorem step_PUSH1_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (v : UInt256)
    (hStep : EVM.step (f' + 1) cost (some (.Push .PUSH1, some (v, 1))) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  rfl

/-- **`jmp @join` from a realized layout.** Push the join target (a label PC, a
constant — modelled as `PUSH1` here) above the live layout, then `JUMP`: the
layout `L` and storage agreement are preserved and `pc := joinTarget`. The
reconvergence edge of a diamond. -/
theorem sim_jmp (vs : VenomState) (es es1 es2 : EVM.State) (L : Layout)
    (joinTarget : UInt256) (f cost : ℕ) (argJ : Option (UInt256 × Nat))
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (joinTarget, 1))) es = .ok es1)
    (hjump : EVM.step (f + 1) cost (some (.JUMP, argJ)) es1 = .ok es2)
    (hsim : Sim vs es L) :
    Sim vs es2 L ∧ es2.pc = joinTarget := by
  obtain ⟨_, hpushstk, hpushenv⟩ := step_PUSH1_shape es es1 f cost joinTarget hpush
  have hpushacc := step_PUSH1_accountMap es es1 f cost joinTarget hpush
  have hstk1 : es1.stack = joinTarget :: L.map vs.env := by rw [hpushstk, hsim.1]
  have hsto1 : ∀ y, sloadVal es1 y = vs.storage y := fun y => by
    rw [show sloadVal es1 y = sloadVal es y from by
          simp only [sloadVal, EvmYul.State.lookupAccount, hpushacc, hpushenv]]
    exact hsim.2 y
  exact sim_jump vs es1 es2 L joinTarget f cost argJ hstk1 hsto1 hjump

/-- **Worked diamond (phi/join).** A full branch-and-reconverge:
`jnz %cond, @then` (taken) → `@then: %x = not %a; jmp @join` → `@join: %r = not %x`.
The taken arm computes the phi variable `%x` and leaves it in its slot, jumps to
the join, which reads `%x` (the resolved phi) and computes `%r = not %x`. So the
join sees the value the arm produced — `Sim` carried across both the conditional
edge and the reconvergence edge, ending with `%r = not (not %a)`. The other arm
is symmetric: it leaves its own `%x` in the same slot, so the join is correct on
either path. -/
example (vs : VenomState) (es0 es1 es2 es3 es4 es5 es6 es7 : EVM.State) (L : Layout)
    (cond a x r : VarName) (thenT joinT : UInt256) (f cost : ℕ)
    (jiA dA nA jA dJ nR : Option (UInt256 × Nat))
    (hx : x ∉ a :: L) (hr : r ∉ x :: L)
    (htaken : (vs.env cond != (⟨0⟩ : UInt256)) = true)
    (hstk : es0.stack = thenT :: vs.env cond :: (a :: L).map vs.env)
    (hsto : ∀ y, sloadVal es0 y = vs.storage y)
    (hji : EVM.step (f + 1) cost (some (.JUMPI, jiA)) es0 = .ok es1)
    (hd1 : EVM.step (f + 1) cost (some (.JUMPDEST, dA)) es1 = .ok es2)
    (hnx : EVM.step (f + 1) cost (some (.NOT, nA)) es2 = .ok es3)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (joinT, 1))) es3 = .ok es4)
    (hjmp : EVM.step (f + 1) cost (some (.JUMP, jA)) es4 = .ok es5)
    (hd2 : EVM.step (f + 1) cost (some (.JUMPDEST, dJ)) es5 = .ok es6)
    (hnr : EVM.step (f + 1) cost (some (.NOT, nR)) es6 = .ok es7) :
    Sim ((vs.set x (UInt256.lnot (vs.env a))).set r
          (UInt256.lnot ((vs.set x (UInt256.lnot (vs.env a))).env x))) es7 (r :: L)
        ∧ es1.pc = thenT ∧ es5.pc = joinT := by
  obtain ⟨hsimA, hpc1⟩ := sim_jumpi vs es0 es1 (a :: L) cond thenT f cost jiA hstk hsto hji
  have hsimA2 := sim_jumpdest vs es1 es2 (a :: L) f cost dA hd1 hsimA
  have hsimX : Sim (vs.set x (UInt256.lnot (vs.env a))) es3 (x :: L) :=
    sim_not vs es2 es3 L x a f cost nA hx hnx hsimA2
  obtain ⟨hsimJ, hpc2⟩ :=
    sim_jmp (vs.set x (UInt256.lnot (vs.env a))) es3 es4 es5 (x :: L) joinT f cost jA hpush hjmp hsimX
  have hsimJ2 := sim_jumpdest (vs.set x (UInt256.lnot (vs.env a))) es5 es6 (x :: L) f cost dJ hd2 hsimJ
  refine ⟨sim_not (vs.set x (UInt256.lnot (vs.env a))) es6 es7 L r x f cost nR hr hnr hsimJ2,
          ?_, ?_⟩
  · rw [hpc1, htaken]; rfl
  · exact hpc2

/-- **Worked reconciled join (phi reconciliation across a CFG edge).** A
predecessor reaches the join with its live values in layout `[w, p]` — the
live-through `w` *above* the phi-source `p` — but the join expects `p` on top
(`[p, w]`). The scheduler emits a `SWAP1` to reconcile the layout (the
phi-elimination stack shuffle), then `jmp @join`. `Sim` is carried across *both*
the reconciliation move and the reconvergence edge, so the join reads the phi
value `p` in the slot it expects. This is the stack reconciliation the plain
diamond does not exercise (there both arms already align), and the first
M3 brick that reorders *before* crossing a CFG edge. -/
example (vs : VenomState) (es es1 es2 es3 : EVM.State) (L : Layout)
    (w p : VarName) (joinT : UInt256) (f cost : ℕ) (sw argJ : Option (UInt256 × Nat))
    (hsw : EVM.step (f + 1) cost (some (.SWAP1, sw)) es = .ok es1)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (joinT, 1))) es1 = .ok es2)
    (hjump : EVM.step (f + 1) cost (some (.JUMP, argJ)) es2 = .ok es3)
    (hsim : Sim vs es (w :: p :: L)) :
    Sim vs es3 (p :: w :: L) ∧ es3.pc = joinT := by
  have hrec : Sim vs es1 (p :: w :: L) := reorder_swap1 vs es es1 L w p f cost sw hsw hsim
  exact sim_jmp vs es1 es2 es3 (p :: w :: L) joinT f cost argJ hpush hjump hrec

/-- **Worked reconciled diamond (full branch → compute → reconcile → join).** The
taken arm of `jnz %cond, @then` computes the phi value `%x = not %a` *above* a
live-through `%w` (leaving layout `[x, w]`), but the join expects `%w` on top
(`[w, x]`). The scheduler emits a `SWAP1` to reconcile, then `jmp @join` — so
`Sim` threads the whole edge `jnz → jumpdest → not → swap → jmp → jumpdest`, and
the join sees the reconciled layout. Unlike the plain diamond (whose arm already
aligns), this is a complete CFG branch-and-join that *reorders mid-arm* — the M3
reconciliation milestone in context. (The fallthrough arm is symmetric.) -/
example (vs : VenomState) (es0 es1 es2 es3 es4 es5 es6 : EVM.State) (L : Layout)
    (cond a x w : VarName) (thenT joinT : UInt256) (f cost : ℕ)
    (jiA dA nA sw jA : Option (UInt256 × Nat))
    (hx : x ∉ a :: w :: L)
    (htaken : (vs.env cond != (⟨0⟩ : UInt256)) = true)
    (hstk : es0.stack = thenT :: vs.env cond :: (a :: w :: L).map vs.env)
    (hsto : ∀ y, sloadVal es0 y = vs.storage y)
    (hji : EVM.step (f + 1) cost (some (.JUMPI, jiA)) es0 = .ok es1)
    (hd1 : EVM.step (f + 1) cost (some (.JUMPDEST, dA)) es1 = .ok es2)
    (hnx : EVM.step (f + 1) cost (some (.NOT, nA)) es2 = .ok es3)
    (hsw : EVM.step (f + 1) cost (some (.SWAP1, sw)) es3 = .ok es4)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (joinT, 1))) es4 = .ok es5)
    (hjmp : EVM.step (f + 1) cost (some (.JUMP, jA)) es5 = .ok es6) :
    Sim (vs.set x (UInt256.lnot (vs.env a))) es6 (w :: x :: L)
        ∧ es1.pc = thenT ∧ es6.pc = joinT := by
  obtain ⟨hsimA, hpc1⟩ :=
    sim_jumpi vs es0 es1 (a :: w :: L) cond thenT f cost jiA hstk hsto hji
  have hsimA2 := sim_jumpdest vs es1 es2 (a :: w :: L) f cost dA hd1 hsimA
  have hsimX : Sim (vs.set x (UInt256.lnot (vs.env a))) es3 (x :: w :: L) :=
    sim_not vs es2 es3 (w :: L) x a f cost nA hx hnx hsimA2
  have hsimR : Sim (vs.set x (UInt256.lnot (vs.env a))) es4 (w :: x :: L) :=
    reorder_swap1 (vs.set x (UInt256.lnot (vs.env a))) es3 es4 L x w f cost sw hsw hsimX
  obtain ⟨hsimJ, hpc2⟩ :=
    sim_jmp (vs.set x (UInt256.lnot (vs.env a))) es4 es5 es6 (w :: x :: L) joinT f cost jA
      hpush hjmp hsimR
  exact ⟨hsimJ, by rw [hpc1, htaken]; rfl, hpc2⟩

/-! ### A verified `require` / `assert` guard

`assert %a ≤ %b` (Vyper's safe-math / require) lowers to a predicate plus a
branch to a revert block: `GT %a, %b; jnz @fail`. On the *passing* path the
predicate is `0`, so the branch is not taken and control falls through to the
continuation — this is the guard a `transfer` performs before debiting. -/

/-- `gt a b = 0` when `a ≤ b` (the guard predicate is false, so the check
passes). -/
theorem gt_eq_zero_of_le {a b : UInt256} (h : a ≤ b) : UInt256.gt a b = UInt256.ofNat 0 := by
  have hnb : ¬ (b.val < a.val) := not_lt.mpr (show a.val ≤ b.val from h)
  have h' : ¬ (a > b) := fun hba => hnb hba
  simp only [UInt256.gt, Bool.toUInt256, decide_eq_false h', Bool.false_eq_true, if_false]

/-- **Lowered `assert %a ≤ %b` (passing path).** The guard `GT %a, %b;
PUSH @fail; JUMPI` falls through — the simulation is preserved and control does
*not* branch to `@fail` — exactly when `%a ≤ %b`. The revert block is unreachable
on this path. -/
theorem sim_assert_le (vs : VenomState) (es es1 es2 es3 : EVM.State) (L : Layout)
    (cond a b : VarName) (failT : UInt256) (f cost : ℕ)
    (gA jiA : Option (UInt256 × Nat))
    (hcond : cond ∉ a :: b :: L)
    (hle : vs.env a ≤ vs.env b)
    (hgt : EVM.step (f + 1) cost (some (.GT, gA)) es = .ok es1)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (failT, 1))) es1 = .ok es2)
    (hji : EVM.step (f + 1) cost (some (.JUMPI, jiA)) es2 = .ok es3)
    (hsim : Sim vs es (a :: b :: L)) :
    Sim (vs.set cond (UInt256.gt (vs.env a) (vs.env b))) es3 L ∧ es3.pc = es2.pc + ⟨1⟩ := by
  have hsim1 : Sim (vs.set cond (UInt256.gt (vs.env a) (vs.env b))) es1 (cond :: L) :=
    sim_gt vs es es1 L cond a b f cost gA hcond hgt hsim
  set vs' := vs.set cond (UInt256.gt (vs.env a) (vs.env b)) with hvs'
  obtain ⟨_, hpushstk, hpushenv⟩ := step_PUSH1_shape es1 es2 f cost failT hpush
  have hpushacc := step_PUSH1_accountMap es1 es2 f cost failT hpush
  have hstk2 : es2.stack = failT :: vs'.env cond :: L.map vs'.env := by
    rw [hpushstk, hsim1.1, List.map_cons]
  have hsto2 : ∀ x, sloadVal es2 x = vs'.storage x := fun x => by
    rw [show sloadVal es2 x = sloadVal es1 x from by
          simp only [sloadVal, EvmYul.State.lookupAccount, hpushacc, hpushenv]]
    exact hsim1.2 x
  obtain ⟨hsimJ, hpcJ⟩ := sim_jumpi vs' es2 es3 L cond failT f cost jiA hstk2 hsto2 hji
  have hcond0 : vs'.env cond = ⟨0⟩ := by
    rw [hvs', VenomState.set_env_self]; exact gt_eq_zero_of_le hle
  refine ⟨hsimJ, ?_⟩
  rw [hpcJ, hcond0, show ((⟨0⟩ : UInt256) != (⟨0⟩ : UInt256)) = false from by decide]
  rfl

/-! ## Capstone: a lowered storage read-modify-write

Tying instruction selection, the storage-op pair, and scheduling together: the
contract operation `storage[k] := g (storage[k]) amt` — the read-modify-write a
`transfer` performs on the very balance map the `~addr` peephole rewrites the
slots of — lowered SSA→stack with an explicit schedule and verified end-to-end.

The SSA block is `%res = sload %k; %new = <binop> %res, %amt; sstore %k, %new`,
lowered to `DUP2; SLOAD; <binop>; SWAP1; SSTORE` (the `DUP2` keeps a copy of the
key live for the trailing store; the `SWAP1` puts key-over-value for `SSTORE`).
We conclude both that the full `Sim` is preserved *and* that the resulting
storage at the key is exactly `g (old) amt`. The inner op is abstracted, so the
safe-math debit (`SUB`, `old − amt`) and credit (`ADD`, `old + amt`) are
instances. -/

/-- **Lowered read-modify-write** `storage[k] := g (storage[k]) amt`, the general
form. The inner binary op is abstracted as `hbinop` — its `Sim`-level lowering
step — so the only op-specific input is that one step; the schedule
`DUP2; SLOAD; <binop>; SWAP1; SSTORE` and the storage bookkeeping are uniform.
Run on the real `EVM.step` from a stack realizing the initial layout `amt :: k :: L`
(an arbitrary tail `L` carried through, enabling composition), it preserves the
simulation and leaves `storage(k) = g (storage(k)) amt`. We also expose the
**frame conditions** — storage off `k` and the env off the fresh `res`/`new` are
unchanged — which a *next* block needs to recover its operands across this one's
existential. SSA freshness of `res`/`new` are the distinctness hypotheses; the
runtime side conditions are the executing account existing and the written value
nonzero (the SSTORE insert branch). -/
theorem lowered_rmw
    (g : UInt256 → UInt256 → UInt256)
    (vs : VenomState) (es0 es1 es2 es3 es4 es5 : EVM.State) (acc : Account .EVM)
    (k amt res new : VarName) (L : Layout) (f cost : ℕ)
    (a1 a2 a4 a5 : Option (UInt256 × Nat))
    (hbk : res ≠ k) (hba : res ≠ amt) (hnk : new ≠ k) (hresL : res ∉ L)
    (hdup : EVM.step (f + 1) cost (some (.DUP2,  a1)) es0 = .ok es1)
    (hsld : EVM.step (f + 1) cost (some (.SLOAD, a2)) es1 = .ok es2)
    (hbinop : Sim (vs.set res (vs.storage (vs.env k))) es2 (res :: amt :: k :: L)
              → Sim ((vs.set res (vs.storage (vs.env k))).set new
                       (g ((vs.set res (vs.storage (vs.env k))).env res)
                          ((vs.set res (vs.storage (vs.env k))).env amt))) es3 (new :: k :: L))
    (hswp : EVM.step (f + 1) cost (some (.SWAP1, a4)) es3 = .ok es4)
    (hsst : EVM.step (f + 1) cost (some (.SSTORE,a5)) es4 = .ok es5)
    (hFind : es4.accountMap.find? es4.executionEnv.codeOwner = some acc)
    (hvalNe : (g (vs.storage (vs.env k)) (vs.env amt) == default) = false)
    (hsim : Sim vs es0 (amt :: k :: L)) :
    ∃ vsf : VenomState,
      Sim vsf es5 L ∧
      vsf.storage (vs.env k) = g (vs.storage (vs.env k)) (vs.env amt) ∧
      (∀ x, x ≠ vs.env k → vsf.storage x = vs.storage x) ∧
      (∀ y, y ≠ res → y ≠ new → vsf.env y = vs.env y) := by
  have set_env_ne : ∀ (s : VenomState) (x y : VarName) (v : UInt256),
      x ≠ y → (s.set y v).env x = s.env x :=
    fun s x y v h => by simp [VenomState.set, h]
  set vs1 := vs.set res (vs.storage (vs.env k)) with hvs1
  have hres1 : vs1.env res = vs.storage (vs.env k) := by rw [hvs1, VenomState.set_env_self]
  have hamt1 : vs1.env amt = vs.env amt := by rw [hvs1]; exact set_env_ne vs amt res _ (Ne.symm hba)
  have hk1 : vs1.env k = vs.env k := by rw [hvs1]; exact set_env_ne vs k res _ (Ne.symm hbk)
  set vs2 := vs1.set new (g (vs1.env res) (vs1.env amt)) with hvs2
  have hnew2 : vs2.env new = g (vs.storage (vs.env k)) (vs.env amt) := by
    rw [hvs2, VenomState.set_env_self, hres1, hamt1]
  have hk2 : vs2.env k = vs.env k := by
    rw [hvs2, set_env_ne vs1 k new _ (Ne.symm hnk)]; exact hk1
  have hsto2 : vs2.storage = vs.storage := by
    rw [hvs2, VenomState.set_storage, hvs1, VenomState.set_storage]
  have s1 : Sim vs es1 (k :: amt :: k :: L) :=
    sim_dup2 vs es0 es1 L amt k f cost a1 hdup hsim
  have s2 : Sim vs1 es2 (res :: amt :: k :: L) :=
    sim_sload vs es1 es2 (amt :: k :: L) res k f cost a2 (by simp [hbk, hba, hresL]) hsld s1
  have s3 : Sim vs2 es3 (new :: k :: L) := hbinop s2
  have s4 : Sim vs2 es4 (k :: new :: L) :=
    sim_swap1 vs2 es3 es4 L new k f cost a4 hswp s3
  have hval : (vs2.env new == default) = false := by rw [hnew2]; exact hvalNe
  have s5 : Sim (vs2.sstore (vs2.env k) (vs2.env new)) es5 L :=
    sim_sstore vs2 es4 es5 L k new f cost a5 acc hFind hval hsst s4
  refine ⟨vs2.sstore (vs2.env k) (vs2.env new), s5, ?_, ?_, ?_⟩
  · simp only [VenomState.sstore_storage, hk2, ↓reduceIte, hnew2]
  · intro x hx
    simp only [VenomState.sstore_storage]
    rw [if_neg (by rw [hk2]; exact hx), hsto2]
  · intro y hyres hynew
    rw [VenomState.sstore_env, hvs2, set_env_ne vs1 y new _ hynew, hvs1,
        set_env_ne vs y res _ hyres]

/-- **Lowered balance debit** `storage[k] := storage[k] - amt` — the `SUB`
instance of `lowered_rmw` (the debit a `transfer` performs). -/
theorem lowered_debit
    (vs : VenomState) (es0 es1 es2 es3 es4 es5 : EVM.State) (acc : Account .EVM)
    (k amt bal new : VarName) (L : Layout) (f cost : ℕ)
    (a1 a2 a3 a4 a5 : Option (UInt256 × Nat))
    (hbk : bal ≠ k) (hba : bal ≠ amt)
    (hnk : new ≠ k) (hnb : new ≠ bal) (hna : new ≠ amt)
    (hbalL : bal ∉ L) (hnewL : new ∉ L)
    (hdup : EVM.step (f + 1) cost (some (.DUP2,  a1)) es0 = .ok es1)
    (hsld : EVM.step (f + 1) cost (some (.SLOAD, a2)) es1 = .ok es2)
    (hsub : EVM.step (f + 1) cost (some (.SUB,   a3)) es2 = .ok es3)
    (hswp : EVM.step (f + 1) cost (some (.SWAP1, a4)) es3 = .ok es4)
    (hsst : EVM.step (f + 1) cost (some (.SSTORE,a5)) es4 = .ok es5)
    (hFind : es4.accountMap.find? es4.executionEnv.codeOwner = some acc)
    (hbalNe : (UInt256.sub (vs.storage (vs.env k)) (vs.env amt) == default) = false)
    (hsim : Sim vs es0 (amt :: k :: L)) :
    ∃ vsf : VenomState,
      Sim vsf es5 L ∧
      vsf.storage (vs.env k) = UInt256.sub (vs.storage (vs.env k)) (vs.env amt) ∧
      (∀ x, x ≠ vs.env k → vsf.storage x = vs.storage x) ∧
      (∀ y, y ≠ bal → y ≠ new → vsf.env y = vs.env y) :=
  lowered_rmw UInt256.sub vs es0 es1 es2 es3 es4 es5 acc k amt bal new L f cost a1 a2 a4 a5
    hbk hba hnk hbalL hdup hsld
    (fun s2 => sim_sub (vs.set bal (vs.storage (vs.env k))) es2 es3 (k :: L) new bal amt
                f cost a3 (by simp [hnb, hna, hnk, hnewL]) hsub s2)
    hswp hsst hFind hbalNe hsim

/-- **Lowered balance credit** `storage[k] := storage[k] + amt` — the `ADD`
instance of `lowered_rmw` (the mint/credit companion to the debit). -/
theorem lowered_credit
    (vs : VenomState) (es0 es1 es2 es3 es4 es5 : EVM.State) (acc : Account .EVM)
    (k amt bal new : VarName) (L : Layout) (f cost : ℕ)
    (a1 a2 a3 a4 a5 : Option (UInt256 × Nat))
    (hbk : bal ≠ k) (hba : bal ≠ amt)
    (hnk : new ≠ k) (hnb : new ≠ bal) (hna : new ≠ amt)
    (hbalL : bal ∉ L) (hnewL : new ∉ L)
    (hdup : EVM.step (f + 1) cost (some (.DUP2,  a1)) es0 = .ok es1)
    (hsld : EVM.step (f + 1) cost (some (.SLOAD, a2)) es1 = .ok es2)
    (hadd : EVM.step (f + 1) cost (some (.ADD,   a3)) es2 = .ok es3)
    (hswp : EVM.step (f + 1) cost (some (.SWAP1, a4)) es3 = .ok es4)
    (hsst : EVM.step (f + 1) cost (some (.SSTORE,a5)) es4 = .ok es5)
    (hFind : es4.accountMap.find? es4.executionEnv.codeOwner = some acc)
    (hbalNe : (UInt256.add (vs.storage (vs.env k)) (vs.env amt) == default) = false)
    (hsim : Sim vs es0 (amt :: k :: L)) :
    ∃ vsf : VenomState,
      Sim vsf es5 L ∧
      vsf.storage (vs.env k) = UInt256.add (vs.storage (vs.env k)) (vs.env amt) ∧
      (∀ x, x ≠ vs.env k → vsf.storage x = vs.storage x) ∧
      (∀ y, y ≠ bal → y ≠ new → vsf.env y = vs.env y) :=
  lowered_rmw UInt256.add vs es0 es1 es2 es3 es4 es5 acc k amt bal new L f cost a1 a2 a4 a5
    hbk hba hnk hbalL hdup hsld
    (fun s2 => sim_add (vs.set bal (vs.storage (vs.env k))) es2 es3 (k :: L) new bal amt
                f cost a3 (by simp [hnb, hna, hnk, hnewL]) hadd s2)
    hswp hsst hFind hbalNe hsim

/-! ## A full token transfer, lowered

Composing the debit and credit: a `transfer(amt)` from account `kf` to a
*distinct* account `kd` is `storage[kf] -= amt; storage[kd] += amt`, lowered to
the ten-instruction block

    DUP2; SLOAD; SUB; SWAP1; SSTORE;   -- debit kf
    DUP2; SLOAD; ADD; SWAP1; SSTORE    -- credit kd

The two blocks compose through `Sim`: the debit leaves the carry layout
`amt :: kd :: L` (so the initial layout holds a second `amt`/`kd` for the credit),
and the debit's frame conditions let the credit recover that `kd`/`amt` still
read their original values and that the debit left `kd`'s cell untouched — which
needs the accounts to be distinct *addresses* (`vs.env kf ≠ vs.env kd`). We
conclude that the two balances move by exactly `amt` and nothing else, i.e. the
transfer conserves total balance (cf. `Solvency.balSumZ_transfer`). -/

/-- **Lowered token transfer.** The ten-instruction block above, run on the real
`EVM.step` from a stack realizing `amt :: kf :: amt :: kd :: L`, preserves the
simulation and leaves `storage(kf) = old_kf − amt` and `storage(kd) = old_kd +
amt` — the two balances move by `amt`, conserving the total. -/
theorem lowered_transfer
    (vs : VenomState) (es0 es1 es2 es3 es4 es5 es6 es7 es8 es9 es10 : EVM.State)
    (accF accD : Account .EVM)
    (kf kd amt bf nf bd nd : VarName) (L : Layout) (f cost : ℕ)
    (b1 b2 b3 b4 b5 c1 c2 c3 c4 c5 : Option (UInt256 × Nat))
    (hbfkf : bf ≠ kf) (hbfamt : bf ≠ amt) (hnfkf : nf ≠ kf) (hnfbf : nf ≠ bf) (hnfamt : nf ≠ amt)
    (hbfL : bf ∉ amt :: kd :: L) (hnfL : nf ∉ amt :: kd :: L)
    (hbdkd : bd ≠ kd) (hbdamt : bd ≠ amt) (hndkd : nd ≠ kd) (hndbd : nd ≠ bd) (hndamt : nd ≠ amt)
    (hbdL : bd ∉ L) (hndL : nd ∉ L)
    (hkfd : vs.env kf ≠ vs.env kd)
    (hd1 : EVM.step (f+1) cost (some (.DUP2,  b1)) es0 = .ok es1)
    (hl1 : EVM.step (f+1) cost (some (.SLOAD, b2)) es1 = .ok es2)
    (hs1 : EVM.step (f+1) cost (some (.SUB,   b3)) es2 = .ok es3)
    (hw1 : EVM.step (f+1) cost (some (.SWAP1, b4)) es3 = .ok es4)
    (ht1 : EVM.step (f+1) cost (some (.SSTORE,b5)) es4 = .ok es5)
    (hd2 : EVM.step (f+1) cost (some (.DUP2,  c1)) es5 = .ok es6)
    (hl2 : EVM.step (f+1) cost (some (.SLOAD, c2)) es6 = .ok es7)
    (ha2 : EVM.step (f+1) cost (some (.ADD,   c3)) es7 = .ok es8)
    (hw2 : EVM.step (f+1) cost (some (.SWAP1, c4)) es8 = .ok es9)
    (ht2 : EVM.step (f+1) cost (some (.SSTORE,c5)) es9 = .ok es10)
    (hFindF : es4.accountMap.find? es4.executionEnv.codeOwner = some accF)
    (hFindD : es9.accountMap.find? es9.executionEnv.codeOwner = some accD)
    (hbalNe : (UInt256.sub (vs.storage (vs.env kf)) (vs.env amt) == default) = false)
    (hovfNe : (UInt256.add (vs.storage (vs.env kd)) (vs.env amt) == default) = false)
    (hsim : Sim vs es0 (amt :: kf :: amt :: kd :: L)) :
    ∃ vsf : VenomState,
      Sim vsf es10 L ∧
      vsf.storage (vs.env kf) = UInt256.sub (vs.storage (vs.env kf)) (vs.env amt) ∧
      vsf.storage (vs.env kd) = UInt256.add (vs.storage (vs.env kd)) (vs.env amt) ∧
      (∀ x, x ≠ vs.env kf → x ≠ vs.env kd → vsf.storage x = vs.storage x) := by
  -- block 1: debit kf, carrying `amt :: kd :: L`
  obtain ⟨vsf1, hsim1, hkf1, hoff1, henv1⟩ :=
    lowered_debit vs es0 es1 es2 es3 es4 es5 accF kf amt bf nf (amt :: kd :: L) f cost
      b1 b2 b3 b4 b5 hbfkf hbfamt hnfkf hnfbf hnfamt hbfL hnfL
      hd1 hl1 hs1 hw1 ht1 hFindF hbalNe hsim
  -- recover, via the frames, that block 1 left kd/amt and kd's cell untouched
  have hbfkd : bf ≠ kd := by intro h; apply hbfL; rw [h]; simp
  have hnfkd : nf ≠ kd := by intro h; apply hnfL; rw [h]; simp
  have hvsf1_kd : vsf1.env kd = vs.env kd := henv1 kd (Ne.symm hbfkd) (Ne.symm hnfkd)
  have hvsf1_amt : vsf1.env amt = vs.env amt := henv1 amt (Ne.symm hbfamt) (Ne.symm hnfamt)
  have hvsf1_sto_kd : vsf1.storage (vs.env kd) = vs.storage (vs.env kd) :=
    hoff1 (vs.env kd) (Ne.symm hkfd)
  have hovf2 : (UInt256.add (vsf1.storage (vsf1.env kd)) (vsf1.env amt) == default) = false := by
    rw [hvsf1_kd, hvsf1_sto_kd, hvsf1_amt]; exact hovfNe
  -- block 2: credit kd
  obtain ⟨vsf2, hsim2, hkd2, hoff2, henv2⟩ :=
    lowered_credit vsf1 es5 es6 es7 es8 es9 es10 accD kd amt bd nd L f cost
      c1 c2 c3 c4 c5 hbdkd hbdamt hndkd hndbd hndamt hbdL hndL
      hd2 hl2 ha2 hw2 ht2 hFindD hovf2 hsim1
  refine ⟨vsf2, hsim2, ?_, ?_, ?_⟩
  · -- storage(kf) still old_kf − amt: block 2 wrote kd's cell, not kf's
    have hne : vs.env kf ≠ vsf1.env kd := by rw [hvsf1_kd]; exact hkfd
    rw [hoff2 (vs.env kf) hne]; exact hkf1
  · -- storage(kd) = old_kd + amt
    have hcast : vsf2.storage (vs.env kd) = vsf2.storage (vsf1.env kd) := by rw [hvsf1_kd]
    rw [hcast, hkd2, hvsf1_kd, hvsf1_sto_kd, hvsf1_amt]
  · -- off both keys, storage is unchanged (compose both blocks' frames)
    intro x hxf hxd
    have hx_kd : x ≠ vsf1.env kd := by rw [hvsf1_kd]; exact hxd
    rw [hoff2 x hx_kd, hoff1 x hxf]

/-! ## A guarded balance decrement (require + debit)

Putting the front and back halves together: the `require` guard and the storage
read-modify-write compose into a realistic guarded operation — `assert amt ≤
balance; storage[k] -= amt`. The guard secures the safe-math precondition, so the
decrement provably does not underflow. -/

/-- **Guarded balance debit** `assert %amt ≤ %bal; storage[%k] -= %amt`, where
`%bal` holds the sender's balance `storage[%k]`. The require guard
(`GT; PUSH @fail; JUMPI`) falls through (no revert) because `%amt ≤ %bal`, then
the debit block (`DUP2; SLOAD; SUB; SWAP1; SSTORE`) decrements the slot. We
conclude the result is `storage[%k] - %amt` *and* that this is a safe
(non-underflowing) subtraction — `%amt ≤ storage[%k]` — which is exactly what the
guard secured. -/
theorem guarded_debit
    (vs : VenomState) (es0 es1 es2 es3 es4 es5 es6 es7 es8 : EVM.State) (acc : Account .EVM)
    (cond bal k amt dbal dnew : VarName) (failT : UInt256) (L : Layout) (f cost : ℕ)
    (gA jiA d1 d2 d3 d4 d5 : Option (UInt256 × Nat))
    (hcond : cond ∉ amt :: bal :: amt :: k :: L)
    (hca : cond ≠ amt) (hck : cond ≠ k)
    (hbalval : vs.env bal = vs.storage (vs.env k))
    (hle : vs.env amt ≤ vs.env bal)
    (hdbk : dbal ≠ k) (hdba : dbal ≠ amt)
    (hdnk : dnew ≠ k) (hdnb : dnew ≠ dbal) (hdna : dnew ≠ amt)
    (hdbalL : dbal ∉ L) (hdnewL : dnew ∉ L)
    (hbalNe : (UInt256.sub (vs.storage (vs.env k)) (vs.env amt) == default) = false)
    (hgt : EVM.step (f + 1) cost (some (.GT, gA)) es0 = .ok es1)
    (hpush : EVM.step (f + 1) cost (some (.Push .PUSH1, some (failT, 1))) es1 = .ok es2)
    (hji : EVM.step (f + 1) cost (some (.JUMPI, jiA)) es2 = .ok es3)
    (hdup : EVM.step (f + 1) cost (some (.DUP2,  d1)) es3 = .ok es4)
    (hsld : EVM.step (f + 1) cost (some (.SLOAD, d2)) es4 = .ok es5)
    (hsub : EVM.step (f + 1) cost (some (.SUB,   d3)) es5 = .ok es6)
    (hswp : EVM.step (f + 1) cost (some (.SWAP1, d4)) es6 = .ok es7)
    (hsst : EVM.step (f + 1) cost (some (.SSTORE,d5)) es7 = .ok es8)
    (hFind : es7.accountMap.find? es7.executionEnv.codeOwner = some acc)
    (hsim : Sim vs es0 (amt :: bal :: amt :: k :: L)) :
    ∃ vsf : VenomState,
      Sim vsf es8 L ∧
      vsf.storage (vs.env k) = UInt256.sub (vs.storage (vs.env k)) (vs.env amt) ∧
      vs.env amt ≤ vs.storage (vs.env k) := by
  obtain ⟨hsimA, _⟩ :=
    sim_assert_le vs es0 es1 es2 es3 (amt :: k :: L) cond amt bal failT f cost gA jiA
      hcond hle hgt hpush hji hsim
  set vs1 := vs.set cond (UInt256.gt (vs.env amt) (vs.env bal)) with hvs1
  have he_amt : vs1.env amt = vs.env amt := by rw [hvs1]; simp [VenomState.set, Ne.symm hca]
  have he_k : vs1.env k = vs.env k := by rw [hvs1]; simp [VenomState.set, Ne.symm hck]
  have he_sto : vs1.storage = vs.storage := by rw [hvs1, VenomState.set_storage]
  have hbalNe' : (UInt256.sub (vs1.storage (vs1.env k)) (vs1.env amt) == default) = false := by
    rw [he_sto, he_k, he_amt]; exact hbalNe
  obtain ⟨vsf, hsimF, hkf, _, _⟩ :=
    lowered_debit vs1 es3 es4 es5 es6 es7 es8 acc k amt dbal dnew L f cost
      d1 d2 d3 d4 d5 hdbk hdba hdnk hdnb hdna hdbalL hdnewL
      hdup hsld hsub hswp hsst hFind hbalNe' hsimA
  refine ⟨vsf, hsimF, ?_, ?_⟩
  · rw [he_k, he_sto, he_amt] at hkf; exact hkf
  · rw [← hbalval]; exact hle

end EvmYul.Venom.Backend

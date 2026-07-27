import EvmYul.Frame.StepShapes
import EvmYul.Venom.BalanceSlot
import EvmYul.Venom.SlotAbstraction

/-!
# Lifting the balance peephole to EVM bytecode

The Venom-IR equivalence (`EvmYul/Venom/BalanceSlot.lean`) and the evm-smith
demo both reason about the peephole at the *block* level. This file lifts the
load equivalence onto EVMYulLean's **real EVM bytecode stepper** (`EVM.step`),
using the `Frame/StepShapes` step lemmas, so the statement is about executing
the actual `KECCAK256; SLOAD` and `NOT; SLOAD` opcode tails.

## Honest scope

EVMYulLean's `MachineState.memory` is a `ByteArray`, and `readWithPadding` /
`ByteArray.write` rest on the **opaque FFI** `ffi.ByteArray.zeroes`. So the
keccak *value* a real `KECCAK256` produces is not kernel-reducible — exactly
why `step_KECCAK256_shape` exposes only `∃ v` and the demo had to *assume*
`hOrig`. We therefore do not prove `kO = keccak(slot ++ addr)` on the
`ByteArray` machine (that would require axiomatising the FFI).

Instead:

* `evm_sload_equiv` / `evm_balanceLoad_block_equiv` prove the equivalence on
  the real `EVM.step`, reducing the assumption to a **single, minimal
  interface**: the two storage slots the tails land on hold the same value
  (the per-address storage relation). Everything else — the stack flow, the
  `SLOAD` value (`storage[key]`) — is *proved* via the `Frame` step lemmas.
* `balanceKeccak_is_slot_keccak` discharges the *meaning* of that interface in
  the reasoning-friendly `List`-memory Venom model (`keccak_staged`): there,
  the orig slot provably **is** `keccak256(slot ++ addr)`. So the residual
  relation is the standard balance relation between `keccak(slot ++ addr)` and
  `~addr`, justified by a reference model — not an opaque blob.
-/

namespace EvmYul.Venom
open EvmYul EvmYul.EVM EvmYul.Frame

/-- The value `SLOAD key` pushes: `storage[key]` of the executing account
(the form `step_SLOAD_shape_strong` exposes). -/
def sloadVal (s : EVM.State) (key : UInt256) : UInt256 :=
  (s.lookupAccount s.executionEnv.codeOwner).option ⟨0⟩ (Account.lookupStorage (k := key))

/-- An EVM state's persistent storage, viewed as a `slot → value` function —
the bridge to the abstract `SlotAbstraction` layer. -/
def evmStorage (s : EVM.State) : UInt256 → UInt256 := fun k => sloadVal s k

/-- The per-slot EVM storage relation underlying the load equivalence: the orig
slot `kO` and the opt slot `kP` hold the same value. -/
def EvmStorageRel (s_o s_p : EVM.State) (kO kP : UInt256) : Prop :=
  sloadVal s_o kO = sloadVal s_p kP

/-- **EVM-bytecode-level load equivalence (core).** If the original keccak
slot `kO` and the optimized `~addr` slot `kP` hold the same value (the
per-address storage relation), then executing `SLOAD` on each — on
EVMYulLean's real `EVM.step` — pushes equal values. -/
theorem evm_sload_equiv
    (s_o s_o' s_p s_p' : EVM.State) (f cost : ℕ) (argO argP : Option (UInt256 × Nat))
    (kO kP : UInt256) (tlO tlP : Stack UInt256)
    (hOstk : s_o.stack = kO :: tlO)
    (hPstk : s_p.stack = kP :: tlP)
    (hOstep : EVM.step (f + 1) cost (some (.SLOAD, argO)) s_o = .ok s_o')
    (hPstep : EVM.step (f + 1) cost (some (.SLOAD, argP)) s_p = .ok s_p')
    (hRel : EvmStorageRel s_o s_p kO kP) :
    s_o'.stack.head? = s_p'.stack.head? := by
  obtain ⟨_, hO, _, _⟩ := step_SLOAD_shape_strong s_o s_o' f cost argO kO tlO hOstk hOstep
  obtain ⟨_, hP, _, _⟩ := step_SLOAD_shape_strong s_p s_p' f cost argP kP tlP hPstk hPstep
  rw [hO, hP]
  simp only [List.head?_cons, Option.some.injEq]
  exact hRel

/-- **Block-level lift.** On the real `EVM.step`, the original tail
`KECCAK256; SLOAD` and the optimized tail `NOT; SLOAD` push equal values,
provided the two storage slots they land on hold the same value. `KECCAK256`
and `NOT` produce opaque/memory-dependent keys, named via the step shapes; the
only residual assumption is the storage relation on those keys. -/
theorem evm_balanceLoad_block_equiv
    (s_o0 s_o1 s_o2 s_p0 s_p1 s_p2 : EVM.State) (f cost : ℕ)
    (argK argSO argN argSP : Option (UInt256 × Nat))
    (szO offO : UInt256) (tlO : Stack UInt256)
    (aP : UInt256) (tlP : Stack UInt256)
    (hO0 : s_o0.stack = szO :: offO :: tlO)
    (hOkec : EVM.step (f + 1) cost (some (.KECCAK256, argK)) s_o0 = .ok s_o1)
    (hOsl  : EVM.step (f + 1) cost (some (.SLOAD, argSO)) s_o1 = .ok s_o2)
    (hP0 : s_p0.stack = aP :: tlP)
    (hPnot : EVM.step (f + 1) cost (some (.NOT, argN)) s_p0 = .ok s_p1)
    (hPsl  : EVM.step (f + 1) cost (some (.SLOAD, argSP)) s_p1 = .ok s_p2)
    (hRel : ∀ kO kP, s_o1.stack = kO :: tlO → s_p1.stack = kP :: tlP →
              EvmStorageRel s_o1 s_p1 kO kP) :
    s_o2.stack.head? = s_p2.stack.head? := by
  obtain ⟨_, ⟨kO, hkO⟩, _⟩ := step_KECCAK256_shape s_o0 s_o1 f cost argK szO offO tlO hO0 hOkec
  obtain ⟨_, ⟨kP, hkP⟩, _⟩ := step_NOT_shape s_p0 s_p1 f cost argN aP tlP hP0 hPnot
  exact evm_sload_equiv s_o1 s_o2 s_p1 s_p2 f cost argSO argSP kO kP tlO tlP
    hkO hkP hOsl hPsl (hRel kO kP hkO hkP)

/-- **List-model justification of the residual interface.** Under faithful
(`List`-based) memory, the slot the orig tail lands on is exactly
`keccak256(slot ++ addr)` — proved without any `ByteArray` opacity as
`keccak_staged`. So `hRel` above is the standard per-address balance relation
between `keccak(slot ++ addr)` and `~addr`. -/
theorem balanceKeccak_is_slot_keccak (s : VenomState) (slot addr : UInt256) :
    keccak ((s.mstore (UInt256.ofNat 0x00) slot).mstore (UInt256.ofNat 0x20) addr)
        (UInt256.ofNat 0x00) (UInt256.ofNat 0x40)
      = venomKeccakOf (Mem.toBytes32 slot ++ Mem.toBytes32 addr) :=
  keccak_staged s slot addr

/-! ## Bridge from the abstraction layer

The residual storage relation is not an arbitrary assumption: it *follows*
from the original and optimized storages being faithful realizations of one
abstract balance map (`SlotAbstraction.orig_opt_agree`). -/

/-- If the orig and opt EVM storages realize the **same** abstract balance map
(orig under slot function `f`, opt under `~addr`), then at every address the
per-slot EVM relation holds between `f a` and `~a`. So `EvmStorageRel` is
*derived* from abstract realization. -/
theorem evmStorageRel_of_realizes (s_o s_p : EVM.State) (B f : UInt256 → UInt256)
    (hO : Realizes (evmStorage s_o) B f)
    (hP : Realizes (evmStorage s_p) B UInt256.lnot)
    (a : UInt256) :
    EvmStorageRel s_o s_p (f a) (UInt256.lnot a) :=
  orig_opt_agree hO hP a

/-- **Fully packaged load equivalence.** With both states holding their balance
slot key on top (`f a` for orig, `~a` for opt) and realizing the same abstract
balance map, the two `SLOAD`s push equal values — the residual relation is
discharged by realization rather than assumed. -/
theorem evm_sload_equiv_of_realizes
    (s_o s_o' s_p s_p' : EVM.State) (f' cost : ℕ) (argO argP : Option (UInt256 × Nat))
    (B fslot : UInt256 → UInt256) (a : UInt256) (tlO tlP : Stack UInt256)
    (hOstk : s_o.stack = fslot a :: tlO)
    (hPstk : s_p.stack = UInt256.lnot a :: tlP)
    (hOstep : EVM.step (f' + 1) cost (some (.SLOAD, argO)) s_o = .ok s_o')
    (hPstep : EVM.step (f' + 1) cost (some (.SLOAD, argP)) s_p = .ok s_p')
    (hO : Realizes (evmStorage s_o) B fslot)
    (hP : Realizes (evmStorage s_p) B UInt256.lnot) :
    s_o'.stack.head? = s_p'.stack.head? :=
  evm_sload_equiv s_o s_o' s_p s_p' f' cost argO argP (fslot a) (UInt256.lnot a) tlO tlP
    hOstk hPstk hOstep hPstep (evmStorageRel_of_realizes s_o s_p B fslot hO hP a)

end EvmYul.Venom

import EvmYul.Wheels

/-!
# M1: an FFI-axiom decision for the EVM memory wall

EVMYulLean's `MachineState.memory` is a `ByteArray`, and reads past written data
zero-pad through the **opaque FFI** primitive

```
@[extern "memset_zero"] opaque ffi.ByteArray.zeroes (n : USize) : ByteArray
```

Because `zeroes` is opaque, the size and contents of a padded read do not
kernel-reduce — the "M1 wall" that forced the Venom semantics onto a `List`-based
memory and left `mload`/`mstore`/`keccak` *value* reasoning out of reach on the
real machine.

This file makes the **policy decision** the rest of the development deliberately
avoided: it introduces a small, explicit axiom characterising that one FFI
primitive — exactly the standard semantics of C's `memset_zero` (allocate `n`
bytes, all zero). With it, the zero-padding region's size and contents reduce,
the prerequisite for memory read/write and keccak-input reasoning on the
`ByteArray` machine.

These are the **only** new axioms in the development; everything else remains on
`[propext, Classical.choice, Quot.sound]`. They are clearly isolated here so the
trust boundary is explicit: the EVM memory results that depend on M1 rest on
*this* faithful model of `memset_zero`, nothing more.
-/

namespace EvmYul.M1

/-- **FFI axiom.** `ffi.ByteArray.zeroes n` allocates exactly `n` bytes (its `C`
implementation is `memset_zero`). -/
axiom ffi_zeroes_size (n : USize) : (ffi.ByteArray.zeroes n).size = n.toNat

/-- **FFI axiom.** Every byte of `ffi.ByteArray.zeroes n` is `0`. -/
axiom ffi_zeroes_get (n : USize) (i : ℕ) : (ffi.ByteArray.zeroes n).get! i = 0

/-- `USize.ofNat` round-trips below `USize.size` (here for memory lengths). -/
theorem usize_ofNat_toNat (n : ℕ) (h : n < USize.size) : (USize.ofNat n).toNat = n :=
  USize.toNat_ofNat_of_lt' h

/-- **M1 unblocked — length.** The EVM zero-padding region of `k` bytes
(`ffi.ByteArray.zeroes ⟨k⟩`, as `readWithPadding`/`readBytes` build it) has size
exactly `k` — the length the opaque FFI hid. The structural prerequisite for all
memory read/write length reasoning. -/
theorem zeroes_size_nat (k : ℕ) (h : k < USize.size) :
    (ffi.ByteArray.zeroes (USize.ofNat k)).size = k := by
  rw [ffi_zeroes_size]; exact usize_ofNat_toNat k h

/-- **M1 unblocked — content.** Every byte of the zero-padding region is `0` — the
content the FFI hid, now available for memory-*value* reasoning (e.g.
uninitialized memory reads as `0`, the basis of keccak-input reduction). -/
theorem zeroes_get_zero (n : USize) (i : ℕ) : (ffi.ByteArray.zeroes n).get! i = 0 :=
  ffi_zeroes_get n i

end EvmYul.M1

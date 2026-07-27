import EvmYul.Venom.State
import EvmYul.Venom.VenomMemProps

/-!
# Venom IR — ABI arg-decode bridge

The mid-term half of the ABI integration (cf. the executable
`scripts/abi_crossval.sh` cross-validation against evm-abi-lean): a
*provable* link between the ABI encoding of a primitive argument and the
Venom `CALLDATALOAD` semantics.

An ERC-20 argument is always primitive — `address` or `uint256` — and its
ABI encoding is exactly a 32-byte big-endian word, i.e. `Mem.toBytes32`.
`VenomState.calldataload off` reads a 32-byte big-endian word from calldata
at byte `off` (`Mem.fromBytes32 (calldata.readBytes off 32)`). So decoding
is the left inverse of encoding, with no dependence on `keccak256` (which is
opaque, and whose *values* the executable harness covers).

This keeps the two repos separate — EVMYulLean gets its own tiny ABI layer
(`Abi.encodeUint256`/`encodeAddress`) proved against the Venom semantics,
while `abi_crossval.sh` checks that layer agrees with abi-lean out of process.
-/

namespace EvmYul.Venom

namespace Abi

/-- ABI encoding of a `uint256` argument: the 32-byte big-endian word. -/
abbrev encodeUint256 (v : UInt256) : Mem := Mem.toBytes32 v

/-- ABI encoding of an `address` argument. `Mem.toBytes32` is the full
32-byte big-endian encoding, so an address value `< 2^160` lands in the low
20 bytes with the ABI's 12-byte left pad above it. -/
abbrev encodeAddress (a : UInt256) : Mem := Mem.toBytes32 a

end Abi

namespace Mem

/-- Reading 32 bytes back out of `pre ++ toBytes32 w ++ suf` at the offset
where the word was placed recovers exactly its bytes. -/
theorem readBytes_append_toBytes32 (pre suf : Mem) (w : UInt256) (off : Nat)
    (h : off = pre.length) :
    (pre ++ Mem.toBytes32 w ++ suf).readBytes off 32 = Mem.toBytes32 w := by
  subst h
  have hlen : (Mem.toBytes32 w).length = 32 := toBytes32_length w
  rw [List.append_assoc]
  simp only [Mem.readBytes]
  rw [expand_of_length_le _ _
      (by rw [List.length_append, List.length_append, hlen]; omega)]
  rw [drop_append_length_eq pre (Mem.toBytes32 w ++ suf) pre.length rfl]
  exact take_append_length_eq (Mem.toBytes32 w) suf 32 hlen.symm

end Mem

namespace VenomState

/-- **ABI arg-decode bridge.** If the calldata places the 32-byte encoding of
`w` at byte `off`, then `calldataload off` returns `w`. Links the ABI encoder
(`Mem.toBytes32`, i.e. `Abi.encodeUint256`/`encodeAddress`) to the Venom
`CALLDATALOAD` semantics — the arg-decode half of the ABI interface. -/
theorem calldataload_append_toBytes32
    (s : VenomState) (pre suf : Mem) (w : UInt256) (off : UInt256)
    (hcd : s.calldata = pre ++ Mem.toBytes32 w ++ suf)
    (hoff : off.toNat = pre.length) :
    s.calldataload off = w := by
  unfold VenomState.calldataload
  rw [hcd, Mem.readBytes_append_toBytes32 pre suf w off.toNat hoff,
     Mem.fromBytes32_toBytes32]

/-- ERC-20 `transfer(address,uint256)` calldata is
`selector(4) ++ encodeAddress recv ++ encodeUint256 amount ++ …`; the recipient
decodes from offset 4. -/
theorem calldataload_transfer_to
    (s : VenomState) (sel suf : Mem) (recv amount : UInt256)
    (hsel : sel.length = 4)
    (hcd : s.calldata = sel ++ Abi.encodeAddress recv ++ Abi.encodeUint256 amount ++ suf) :
    s.calldataload (UInt256.ofNat 4) = recv := by
  apply calldataload_append_toBytes32 s sel (Abi.encodeUint256 amount ++ suf) recv
    (UInt256.ofNat 4)
  · rw [hcd]; simp only [Abi.encodeAddress, Abi.encodeUint256, List.append_assoc]
  · rw [hsel]; decide

/-- …and the amount decodes from offset 36 (4-byte selector + 32-byte
address). -/
theorem calldataload_transfer_amount
    (s : VenomState) (sel suf : Mem) (recv amount : UInt256)
    (hsel : sel.length = 4)
    (hcd : s.calldata = sel ++ Abi.encodeAddress recv ++ Abi.encodeUint256 amount ++ suf) :
    s.calldataload (UInt256.ofNat 36) = amount := by
  apply calldataload_append_toBytes32 s (sel ++ Abi.encodeAddress recv) suf amount
    (UInt256.ofNat 36)
  · rw [hcd]
  · have hrecv : (Abi.encodeAddress recv).length = 32 := Mem.toBytes32_length recv
    rw [List.length_append, hsel, hrecv]
    decide

end VenomState

end EvmYul.Venom

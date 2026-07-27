import EvmYul.Venom.Hol.Types
import EvmYul.Venom.Hol.Semantics
import EvmYul.Venom.Hol.CoreAxioms
open EvmYul.Venom.Hol
open EvmYul (UInt256 fromBytesBigEndian toBytesBigEndian fromBytes' toBytes')

namespace EvmYul.Venom.Hol

theorem length_wordToBytes (w : bytes32) : (wordToBytes w).size = 32 := by
  unfold wordToBytes
  have h_bound : (toBytesBigEndian w.toNat).length ≤ 32 := by
    have h := toBytes'_UInt256_le (n := w.val.val) w.val.isLt
    unfold toBytesBigEndian
    simpa [UInt256.toNat] using h
  rw [byteArray_size_toByteArray]
  simp [h_bound]

theorem read_memory_write_memory (offset : Nat) (bytes : ByteArray) (s : VenomState)
    (hpos : 0 < bytes.size) (hwrap : offset - s.memory.size < USize.size) (hsz : bytes.size < 2 ^ 64) :
  readMemory offset bytes.size (writeMemoryWithExpansion offset bytes s) = bytes := by
  unfold readMemory writeMemoryWithExpansion
  exact byteArray_write_read bytes s.memory offset hpos hwrap hsz

theorem memory_expansion_mono (offset : Nat) (bytes : ByteArray) (s : VenomState) :
  s.memory.size ≤ (writeMemoryWithExpansion offset bytes s).memory.size := by
  unfold writeMemoryWithExpansion
  apply byteArray_write_size bytes s.memory offset

/--
  List-level BE roundtrip with left-zero-padding to 32 bytes.
  fromBytesBigEndian (replicate k 0 ++ toBytesBigEndian n) = n
-/
private lemma be_padded_roundtrip (n : ℕ) (_h : (toBytesBigEndian n).length ≤ 32) :
    fromBytesBigEndian (List.replicate (32 - (toBytesBigEndian n).length) 0 ++ toBytesBigEndian n) = n := by
  set k := 32 - (toBytesBigEndian n).length
  calc
    fromBytesBigEndian (List.replicate k 0 ++ toBytesBigEndian n)
    = fromBytes' (List.reverse (List.replicate k 0 ++ toBytesBigEndian n)) := rfl
    _ = fromBytes' (List.reverse (toBytesBigEndian n) ++ List.replicate k 0) := by simp
    _ = fromBytes' (List.reverse (toBytesBigEndian n)) := by simp [extend_bytes_zero]
    _ = fromBytes' (List.reverse (List.reverse (toBytes' n))) := rfl
    _ = fromBytes' (toBytes' n) := by simp
    _ = n := fromBytes'_toBytes' (x := n)

theorem wordOfBytes_wordToBytes (w : bytes32) : wordOfBytes (wordToBytes w) = w := by
  unfold wordOfBytes wordToBytes
  have h_bound : (toBytesBigEndian w.toNat).length ≤ 32 := by
    have h := toBytes'_UInt256_le (n := w.val.val) w.val.isLt
    unfold toBytesBigEndian
    simpa [UInt256.toNat] using h
  calc
    UInt256.ofNat (fromBytesBigEndian ((List.toByteArray
      (List.replicate (32 - (toBytesBigEndian w.toNat).length) 0 ++ toBytesBigEndian w.toNat)).toList))
    = UInt256.ofNat (fromBytesBigEndian
        (List.replicate (32 - (toBytesBigEndian w.toNat).length) 0 ++ toBytesBigEndian w.toNat)) := by
      rw [toByteArray_toList]
    _ = UInt256.ofNat w.toNat := by rw [be_padded_roundtrip w.toNat h_bound]
    _ = w := by
      dsimp [UInt256.ofNat, UInt256.toNat]
      apply congrArg UInt256.mk; apply Fin.ext; simp

theorem read_memory_write_memory_32 (offset : Nat) (v : bytes32) (s : VenomState)
    (hwrap : offset - s.memory.size < USize.size) :
  readMemory offset 32 (writeMemoryWithExpansion offset (wordToBytes v) s) = wordToBytes v := by
  have h := read_memory_write_memory offset (wordToBytes v) s
    (by rw [length_wordToBytes]; norm_num) hwrap (by rw [length_wordToBytes]; norm_num)
  rw [length_wordToBytes v] at h
  exact h

theorem mstore_mload_inverse (offset : Nat) (v : bytes32) (s : VenomState)
    (hwrap : offset - s.memory.size < USize.size) :
  mload offset (mstore offset v s) = v := by
  unfold mload mstore
  rw [read_memory_write_memory_32 offset v s hwrap]
  apply wordOfBytes_wordToBytes

end EvmYul.Venom.Hol

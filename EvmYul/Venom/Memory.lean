import EvmYul.UInt256

/-!
# Venom IR — a reasoning-friendly memory model

EVMYulLean's `EvmYul.MachineState.memory` is a `ByteArray`. `ByteArray`
operations (`readWithPadding`, `write`) are opaque to the kernel — they do
not reduce by `rfl`, which is exactly why the `add_venom` ERC-20
equivalence demo had to *assume* its keccak-preimage characterization
(`whnf`/`isDefEq` time out).

For the Venom semantics we instead represent byte memory as a plain
`List UInt8` and define every access by `List.take`/`drop`/`replicate`.
These reduce definitionally and admit clean equational lemmas
(`EvmYul/Venom/VenomMemProps.lean`), so memory facts — including the
two-`MSTORE`-then-`KECCAK256` preimage — can be *proved* rather than
assumed.
-/

namespace EvmYul.Venom

/-- Byte-addressed memory, little-administrative: a flat list of bytes,
index 0 first. Unwritten memory past the end reads as zero, modelled by
zero-extending on demand (`Mem.expand`). -/
abbrev Mem := List UInt8

namespace Mem

/-- Zero-extend `mem` so it is at least `len` bytes long. A no-op when
`mem` is already long enough (the appended `replicate` is empty). -/
def expand (mem : Mem) (len : Nat) : Mem :=
  mem ++ List.replicate (len - mem.length) 0

/-- Write the byte string `bytes` into `mem` starting at byte `offset`,
zero-extending first so the region exists. Splices `bytes` over the
`[offset, offset + bytes.length)` window:
`take offset ++ bytes ++ drop (offset + bytes.length)`. -/
def writeBytes (mem : Mem) (offset : Nat) (bytes : Mem) : Mem :=
  let e := mem.expand (offset + bytes.length)
  e.take offset ++ bytes ++ e.drop (offset + bytes.length)

/-- Read `len` bytes from `mem` starting at `offset`, zero-padding past
the written end. -/
def readBytes (mem : Mem) (offset len : Nat) : Mem :=
  let e := mem.expand (offset + len)
  (e.drop offset).take len

/-! ## 32-byte word codec

`mstore`/`mload` move 256-bit words as 32 big-endian bytes. We define the
encoder by direct indexing so its length is `32` definitionally and it is
total (no dependence on the private byte-length lemmas in `UInt256.lean`).
-/

/-- The big-endian 32-byte encoding of a `UInt256`. Byte `i` is the
`(31 - i)`-th base-256 digit, most-significant first. -/
def toBytes32 (v : UInt256) : Mem :=
  (List.range 32).map (fun i => UInt8.ofNat (v.toNat / 256 ^ (31 - i) % 256))

/-- Decode 32 big-endian bytes back to a `UInt256`
(reusing `EvmYul.fromBytesBigEndian`). -/
def fromBytes32 (bytes : Mem) : UInt256 :=
  UInt256.ofNat (fromBytesBigEndian bytes)

/-- Store a 256-bit word at byte `addr` (32-byte big-endian). -/
def storeWord (mem : Mem) (addr : UInt256) (v : UInt256) : Mem :=
  mem.writeBytes addr.toNat (toBytes32 v)

/-- Load a 256-bit word from byte `addr`. -/
def loadWord (mem : Mem) (addr : UInt256) : UInt256 :=
  fromBytes32 (mem.readBytes addr.toNat 32)

/-- Store a single byte (`mstore8`). -/
def storeByte (mem : Mem) (addr : UInt256) (v : UInt256) : Mem :=
  mem.writeBytes addr.toNat [UInt8.ofNat (v.toNat % 256)]

/-- The number of 32-byte words touched, used for `msize`. -/
def sizeWords (mem : Mem) : Nat :=
  (mem.length + 31) / 32

end Mem

end EvmYul.Venom

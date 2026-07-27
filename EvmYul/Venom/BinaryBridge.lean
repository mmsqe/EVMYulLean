/-
Decoder agreement with lean-endianness (`Binary`), early in the import graph.

These two lemmas prove EVMYulLean's hand-rolled byte decoders equal the
independently verified library's. They used to live in `EndiannessCrossval`,
at the very end of the import graph — fine while they were only a *check*.
`Mem.toBytes32`/`Mem.fromBytes32` are now *defined* via the library codec, so
the memory lemma layer (`VenomMemProps`) needs the agreement to relate the old
decoder `fromBytesBigEndian` to the new definitions; hence this module, which
depends only on `EvmYul.UInt256` and `Binary`.
-/
import EvmYul.UInt256
import Binary

namespace EvmYul.Venom

open EvmYul

/-- EVMYulLean's little-endian byte decoder agrees with lean-endianness'. -/
theorem fromBytes'_eq_decodeLEU : ∀ bs : List UInt8, fromBytes' bs = Binary.decodeLEU bs
  | [] => rfl
  | b :: bs => by
    simp only [fromBytes', Binary.decodeLEU, Binary.uint8ToNats, List.map_cons,
      Binary.decodeLE, fromBytes'_eq_decodeLEU bs]
    rfl

/-- EVMYulLean's big-endian byte decoder agrees with lean-endianness'. -/
theorem fromBytesBigEndian_eq_decodeBEU (bs : List UInt8) :
    fromBytesBigEndian bs = Binary.decodeBEU bs := by
  show fromBytes' bs.reverse = _
  rw [fromBytes'_eq_decodeLEU]
  simp [Binary.decodeLEU, Binary.decodeBEU, Binary.decodeBE,
    Binary.uint8ToNats, List.map_reverse]

end EvmYul.Venom

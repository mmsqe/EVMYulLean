import EvmAbi.Codec
import EvmAbi.Codec.Strict

/-!
# The function-argument level (downstream of evm-abi-lean)

An ABI call's arguments are encoded exactly as the tuple of their types, so this
level is *definitionally* the tuple level and `roundtrip_args` is a one-line
corollary of the library's `decodeStrict_encode`. It lives here rather than in
`evm-abi-lean` for that reason: it adds no verification content to the codec, it
just names the shape a caller works in (the 4-byte selector is prepended by the
caller -- see `AbiLean.Hash.selectorBytes`).
-/

namespace EvmYul.Venom.AbiLean

open EvmAbi EvmAbi.Ty

/-- Encode a function's argument list. -/
def encodeArgs (ts : List Ty) (vs : TupleVal ts) : List UInt8 :=
  EvmAbi.encode (.tuple ts) vs

/-- Decode a function's argument list.  `decodeStrict`, not the prefix
decoder: call data is a whole buffer, so the encoding must be canonical
*and* consume it exactly — a trailing byte is a malformed call, not a
successful decode with a remainder. -/
def decodeArgs (ts : List Ty) (buf : List UInt8) : Option (TupleVal ts) :=
  EvmAbi.decodeStrict (.tuple ts) buf

/-- **Function-call roundtrip**: an argument tuple decodes from its own
encoding, under the same length bound as the library's capstone (the
dynamic payload bounds are carried by the values themselves). -/
theorem roundtrip_args (ts : List Ty) (hv : AllValid ts) (vs : TupleVal ts)
    (hb : (encodeArgs ts vs).length < 2 ^ 256) :
    decodeArgs ts (encodeArgs ts vs) = some vs :=
  EvmAbi.decodeStrict_encode (.tuple ts) hv vs hb

end EvmYul.Venom.AbiLean

import EvmAbi.Codec

/-!
# The function-argument level (downstream of evm-abi-lean)

An ABI call's arguments are encoded exactly as the tuple of their types, so this
level is *definitionally* the tuple level and `roundtrip_args` is a one-line
corollary of the library's unified `roundtrip`. It lives here rather than in
`evm-abi-lean` for that reason: it adds no verification content to the codec, it
just names the shape a caller works in (the 4-byte selector is prepended by the
caller -- see `AbiLean.Hash.selectorBytes`).
-/

namespace EvmYul.Venom.AbiLean

open EvmAbi EvmAbi.Ty

/-- Encode a function's argument list. -/
def encodeArgs (ts : List Ty) (vs : TupleVal ts) : List UInt8 :=
  EvmAbi.encode (.tuple ts) vs

/-- Decode a function's argument list. -/
def decodeArgs (ts : List Ty) (buf : List UInt8) : Option (TupleVal ts) :=
  EvmAbi.decode (.tuple ts) buf

/-- **Function-call roundtrip**: an argument tuple decodes from its own
encoding, under the same length bound as the library's `roundtrip`. -/
theorem roundtrip_args (ts : List Ty) (hv : AllValid ts) (vs : TupleVal ts)
    (hl : LenBound (.tuple ts) vs) (hb : (encodeArgs ts vs).length < 2 ^ 256) :
    decodeArgs ts (encodeArgs ts vs) = some vs :=
  EvmAbi.roundtrip (.tuple ts) hv vs hl hb

end EvmYul.Venom.AbiLean

namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

/-- `n` zero bytes. The C `memset_zero` (`@[extern]`) backs it at runtime; the Lean
    reference body `⟨Array.replicate n.toNat 0⟩` (faithful to `memset_zero`) lets us
    prove its size/contents (`unfold ByteArray.zeroes`), so byte-level memory
    round-trips need **no axiom** about the FFI. Marked `irreducible` so it stays
    inert under `whnf`/`rfl` exactly like the old `opaque` — `EvmYul.step` reductions
    do not try to unfold it (which would blow the heartbeat limit). -/
@[extern "memset_zero"]
def ByteArray.zeroes (n : USize) : ByteArray := ⟨Array.replicate n.toNat 0⟩

attribute [irreducible] ByteArray.zeroes

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi

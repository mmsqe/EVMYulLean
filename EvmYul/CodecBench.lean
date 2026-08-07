/-
A/B harness for the byte codec, isolated from the interpreter.

`conform` is the end-to-end measurement, but it walks the whole corpus with no
subsetting and spends most of its time in EVM execution and Python subprocess
calls for the precompiles, so a codec change of a few percent does not survive
the noise. This drives `fromBytesBigEndian` and `BE` directly instead: an upper
bound on what the codec swap can be worth, and the instrument that catches a
`@[csimp]` landing on the reference implementation rather than the fast one.

Values are full width (above `2 ^ 63`), which is where the bignum cost lives —
a benchmark of small words measures nothing. They vary with the loop index too,
or Lean floats the whole call into a cached constant and reports nanoseconds.
-/
import EvmYul.UInt256
import EvmYul.Wheels

open EvmYul

def wordCount : Nat := 2000

/-- Full-width words, distinct so nothing can be cached. -/
def wideWords : Array Nat :=
  (List.range wordCount).toArray.map fun i => 2 ^ 250 + i * 7919 + 1

/-- The same, pre-encoded, so the decode loop times only decoding. -/
def wideBytes : Array (List UInt8) := wideWords.map toBytesBigEndian

def timeIt (label : String) (reps : Nat) (act : Nat → Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for i in [0:reps] do
    checksum := checksum + act i
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(t1 - t0) / reps} ns/word  (checksum {checksum % 97})"

def main : IO Unit := do
  IO.println s!"byte codec, {wordCount} full-width words"
  timeIt "decode  fromBytesBigEndian" wordCount fun i =>
    fromBytesBigEndian wideBytes[i % wordCount]!
  timeIt "encode  BE                " wordCount fun i =>
    (BE wideWords[i % wordCount]!).size

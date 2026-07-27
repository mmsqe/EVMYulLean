import EvmYul.Venom.Parse
import EvmYul.Venom.Semantics
import Lean.Data.Json

/-!
# `venom_run` — a whole-transaction `.venom` oracle

Executes one message call against a `.venom` program with the Lean Venom
semantics, as a stateless subprocess with a JSON protocol — so a Python
driver (pydefi) can thread storage across a transaction sequence and diff
the results against a production EVM (titanoboa / anvil).

```
lake exe venom_run program.venom   < call.json   > result.json
```

Input  (stdin JSON, all fields optional):
```
{ "calldata": "0x40c10f19…",
  "caller":   "0x…", "callvalue": "0",
  "storage":  [ ["0x2","0x63"], … ] }   ; persistent storage in (key,val) hex pairs
```
Output (stdout JSON):
```
{ "status":  "return|revert|stop|invalid|selfdestruct|stuck|outoffuel",
  "return":  "0x…",                    ; returned/reverted bytes
  "storage": [ ["0x…","0x…"], … ] }    ; resulting storage (input ∪ writes)
```

`keccak256`/`sha3` use the real FFI hash, so storage slots and return
values are concrete and directly comparable to an EVM.
-/

open EvmYul EvmYul.Venom
open Lean (Json)

/-! ## Hex helpers -/

private def nibble (d : Nat) : Char := "0123456789abcdef".data.getD (d % 16) '0'

private partial def natToHexAux : Nat → String
  | 0 => ""
  | n => natToHexAux (n / 16) ++ String.singleton (nibble (n % 16))

/-- Lower-case `0x` hex of a `UInt256`. -/
def u256ToHex (v : UInt256) : String :=
  let n := v.toNat
  "0x" ++ (if n == 0 then "0" else natToHexAux n)

/-- `0x` hex of a byte string. -/
def bytesToHex (b : Mem) : String :=
  "0x" ++ String.join (b.map (fun byte =>
    let n := byte.toNat
    String.singleton (nibble (n / 16)) ++ String.singleton (nibble (n % 16))))

private def hexNibble (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else let lc := c.toLower; if 'a' ≤ lc && lc ≤ 'f' then 10 + (lc.toNat - 'a'.toNat) else 0

private partial def bytesOfChars : List Char → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * hexNibble a + hexNibble b) :: bytesOfChars rest
  | _ => []

/-- Parse a `0x`-prefixed (or bare) hex string to a byte list. -/
def hexToBytes (s0 : String) : Mem :=
  let s := if s0.startsWith "0x" || s0.startsWith "0X" then s0.drop 2 else s0
  let s := if s.length % 2 == 1 then "0" ++ s else s
  bytesOfChars s.data

/-! ## JSON field extraction -/

private def jStr? (j : Json) (k : String) : Option String :=
  (j.getObjVal? k >>= Json.getStr?).toOption

private def jStorage (j : Json) : List (UInt256 × UInt256) :=
  match (j.getObjVal? "storage" >>= Json.getArr?).toOption with
  | none => []
  | some arr => arr.toList.filterMap (fun p =>
      match p.getArr?.toOption with
      | some a =>
          match (a[0]? >>= fun x => x.getStr?.toOption), (a[1]? >>= fun x => x.getStr?.toOption) with
          | some ks, some vs => some (Parse.parseConst ks, Parse.parseConst vs)
          | _, _ => none
      | none => none)

/-! ## Result projection -/

private def resultState : Result → VenomState
  | .halted s _ => s | .stuck s => s | .outOfFuel s => s

private def resultStatusData : Result → String × Mem
  | .halted _ (.ret d)      => ("return", d)
  | .halted _ (.revert d)   => ("revert", d)
  | .halted _ .stop         => ("stop", [])
  | .halted _ .invalid      => ("invalid", [])
  | .halted _ .selfdestruct => ("selfdestruct", [])
  | .stuck _                => ("stuck", [])
  | .outOfFuel _            => ("outoffuel", [])

private def dedup (ks : List UInt256) : List UInt256 :=
  (ks.foldl (fun acc k => if acc.contains k then acc else k :: acc) []).reverse

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let src ← IO.FS.readFile path
      let input ← (do pure (← (← IO.getStdin).readToEnd)) <|> pure ""
      let j := (Json.parse input).toOption.getD (Json.mkObj [])
      let cd  := (jStr? j "calldata").map hexToBytes |>.getD []
      let cl  := (jStr? j "caller").map Parse.parseConst |>.getD (UInt256.ofNat 0)
      let cv  := (jStr? j "callvalue").map Parse.parseConst |>.getD (UInt256.ofNat 0)
      let sto := jStorage j
      let stoFn : UInt256 → UInt256 := fun key =>
        (sto.find? (·.1 == key)).map (·.2) |>.getD (UInt256.ofNat 0)
      match Parse.parseProgram src with
      | [] => IO.eprintln "venom_run: no functions parsed"; pure 1
      | fn :: _ =>
          let s0 : VenomState :=
            { calldata := cd, caller := cl, callvalue := cv, storage := stoFn }
          let res := fn.exec 5000000 s0
          let fs := resultState res
          let (status, ret) := resultStatusData res
          -- On a successful halt the new storage is (input ∪ writes); on a
          -- revert/abort the call rolls back, so the storage is the input.
          let stoPairs : List (UInt256 × UInt256) :=
            if status == "return" || status == "stop" || status == "selfdestruct" then
              (dedup (sto.map (·.1) ++ fs.touchedKeys.reverse)).map (fun k => (k, fs.sload k))
            else sto
          let stoOut : Json := Json.arr <|
            (stoPairs.map (fun kv =>
              Json.arr #[Json.str (u256ToHex kv.1), Json.str (u256ToHex kv.2)])).toArray
          let out := Json.mkObj
            [ ("status",  Json.str status)
            , ("return",  Json.str (bytesToHex ret))
            , ("storage", stoOut) ]
          IO.println out.compress
          pure 0
  | _ => IO.eprintln "usage: venom_run <file.venom>  (call spec on stdin as JSON)"; pure 1

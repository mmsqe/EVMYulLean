/-
Stack Model — Venom Codegen Layer 2

Port of vyper-hol/venom/codegen/defs/stackModelScript.sml

The stack is a list of operands: HD = bottom, LAST = TOS.
Distance from TOS: 0 = TOS, 1 = one below, etc.

Operations:
  stack_push, stack_pop, stack_peek, stack_poke,
  stack_swap, stack_dup, stack_find, stack_get_depth, stack_get_phi_depth
-/

import EvmYul.Venom.Hol.Types
open EvmYul.Venom.Hol

namespace EvmYul.Venom.Hol.Codegen

/- ===== Stack Operations ===== -/

/-- Push: append to end (TOS = last element). -/
def stackPush (op : Operand) (stk : List Operand) : List Operand :=
  stk ++ [op]

/-- Pop n items from TOS. -/
def stackPop (n : Nat) (stk : List Operand) : List Operand :=
  stk.take (stk.length - n)

/-- Peek at distance from TOS (0 = TOS). -/
def stackPeek (dist : Nat) (stk : List Operand) : Operand :=
  stk[stk.length - 1 - dist]!

/-- Poke: update element at distance from TOS. -/
def stackPoke (dist : Nat) (op : Operand) (stk : List Operand) : List Operand :=
  let idx := stk.length - 1 - dist
  stk.set idx op

/-- Swap TOS with element at distance dist (dist > 0). -/
def stackSwap (dist : Nat) (stk : List Operand) : List Operand :=
  let topIdx := stk.length - 1
  let tgtIdx := stk.length - 1 - dist
  let topVal := stk[topIdx]!
  let tgtVal := stk[tgtIdx]!
  (stk.set topIdx tgtVal).set tgtIdx topVal

/-- Dup: copy element at distance to TOS. -/
def stackDup (dist : Nat) (stk : List Operand) : List Operand :=
  stk ++ [stackPeek dist stk]

/- ===== Depth Search ===== -/

/-- Find first matching operand from TOS, return distance.
    Searches reversed list (TOS first). Returns none if not found. -/
def stackFind (p : Operand → Bool) (stk : List Operand) : Option Nat :=
  match stk with
  | [] => none
  | x :: xs =>
    if p x then some 0
    else match stackFind p xs with
      | some d => some (d + 1)
      | none => none

/-- Get depth (distance from TOS) of an operand.
    0 = TOS, 1 = one below. Searches reversed to scan from TOS first. -/
def stackGetDepth (op : Operand) (stk : List Operand) : Option Nat :=
  stackFind (λ x => x == op) stk.reverse

/-- Get depth of first matching phi operand. -/
def stackGetPhiDepth (phis : List Operand) (stk : List Operand) : Option Nat :=
  stackFind (λ x => phis.contains x) stk.reverse

end EvmYul.Venom.Hol.Codegen

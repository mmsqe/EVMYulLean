import EvmYul.EVM.Semantics
import EvmYul.Venom.VenomMemProps
import EvmYul.Venom.Operand

/-!
# M5 — the verified `.venom` → bytecode assembler (foundation)

The backend (`Backend.lean`) certifies *single-block lowering* against the `Sim`
relation, but stops at a symbolic instruction stream — it never commits to a byte
layout. M5 closes that last gap: an **assembler** `List Item → ByteArray` that

* resolves block/function labels to concrete program counters, and
* emits a dense dispatch jump table (the thing the `venom_run` oracle *cannot*
  execute — `djmp`'s offsets are fixed only at assembly time),

together with the proof that the emitted bytes **decode back** to the intended
instructions (`EVM.decode`) and that every label lands on a real `JUMPDEST`
(hence is a valid jump target in `EVM.D_J`).

This file is the foundation: the symbolic `Item` type, its byte encoder, a
reducible *list*-level mirror of `EVM.decode` (`decodeAtL`), and the two atomic
round-trip facts every later result rests on —

* `parseInstr_serializeInstr` — every opcode byte parses back to its opcode;
* `decodeAtL_op` / `decodeAtL_push32` / `decodeAtL_pushLabel` / `decodeAtL_label`
  — each single item decodes back to itself at the head of its own bytes.

Subsequent layers (M5.2+) add the two-pass label layout, concatenation /
fetch-decode at arbitrary offsets, and the bridge from `decodeAtL` to the real
`ByteArray` `EVM.decode` / `EVM.D_J` (through the `MemBridge` `toList_eq_data`
keystone).
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation

/-! ## The two atomic round-trip facts -/

/-- Every EVM opcode byte parses back to itself: the encoder/decoder agree on
opcodes (a finite check over all ~140 constructors). -/
theorem parseInstr_serializeInstr (o : Operation .EVM) :
    parseInstr (serializeInstr o) = some o := by
  cases o <;> rename_i a <;> cases a <;> rfl

/-! ## Symbolic assembly -/

/-- A symbolic assembly item, with labels still abstract. `pushLabel`/`label`
are the dense-dispatch primitives the `djmp` oracle cannot express: their byte
positions are fixed only once the whole layout is known.

For a first, provably-correct cut every immediate uses a fixed-width `PUSH32`
(33 bytes) — non-minimal but unambiguous, which keeps the layout arithmetic and
the decode round-trip clean. Minimal-width `PUSH` is a later optimization. -/
inductive Item where
  /-- A single-byte opcode (one whose `argOnNBytesOfInstr` is `0`). -/
  | op (o : Operation .EVM)
  /-- `PUSH32` of a literal immediate. -/
  | push32 (imm : UInt256)
  /-- A *minimal-width* `PUSHk` (`k = argOnNBytesOfInstr (.Push p)`) of a literal
  immediate; matches what Vyper actually emits. -/
  | pushN (p : POp) (imm : UInt256)
  /-- `PUSH32` of a label's resolved program counter. -/
  | pushLabel (l : Label)
  /-- A label definition site; emits `JUMPDEST`. -/
  | label (l : Label)
deriving Repr, DecidableEq

/-- The minimal-width `n`-byte big-endian payload of a `PUSHk` — the low `n`
bytes of the 32-byte big-endian encoding. Its length is `n` *unconditionally*
(for `n ≤ 32`), which keeps `encode1_length`/`emit_length` hypothesis-free; the
value round-trips only when it fits (`fromBytes32_beBytesN`). -/
def beBytesN (n : Nat) (v : UInt256) : List UInt8 := (Mem.toBytes32 v).drop (32 - n)

theorem beBytesN_length (n : Nat) (v : UInt256) (h : n ≤ 32) :
    (beBytesN n v).length = n := by
  simp only [beBytesN, List.length_drop, Mem.toBytes32_length]; omega

/-- Every `PUSH` immediate is at most 32 bytes. -/
theorem argOnNBytesOfInstr_push_le (p : POp) : argOnNBytesOfInstr (.Push p) ≤ 32 := by
  cases p <;> decide

/-- The byte width of an assembled item (independent of the label map — widths
are fixed, which is what makes the two-pass layout well-defined). -/
def Item.width : Item → Nat
  | .op _        => 1
  | .push32 _    => 33
  | .pushN p _   => 1 + argOnNBytesOfInstr (.Push p)
  | .pushLabel _ => 33
  | .label _     => 1

/-- Encode one item to bytes, given a resolved label → PC map `lm`. -/
def Item.encode1 (lm : Label → UInt256) : Item → List UInt8
  | .op o        => [serializeInstr o]
  | .push32 imm  => 0x7f :: Mem.toBytes32 imm
  | .pushN p imm => serializeInstr (.Push p) :: beBytesN (argOnNBytesOfInstr (.Push p)) imm
  | .pushLabel l => 0x7f :: Mem.toBytes32 (lm l)
  | .label _     => [0x5b]

/-- The encoding realizes the declared `width` (unconditionally). -/
theorem Item.encode1_length (lm : Label → UInt256) (a : Item) :
    (a.encode1 lm).length = a.width := by
  cases a with
  | pushN p imm =>
    simp only [encode1, width, List.length_cons,
      beBytesN_length _ _ (argOnNBytesOfInstr_push_le p), Nat.add_comm]
  | _ => simp [encode1, width, Mem.toBytes32_length]

/-! ## A reducible list-level mirror of `EVM.decode`

`EVM.decode` reads a `ByteArray`; `uInt256OfByteArray (arr.extract' (pc+1) (pc+1+w))`
is `UInt256.ofNat (fromBytesBigEndian (arr.data.toList.drop (pc+1) |>.take w))`,
i.e. `Mem.fromBytes32` of those bytes when `w = 32`. We mirror it over `List UInt8`
so the round-trips reduce, and bridge to the `ByteArray` form later. -/
def decodeAtL (code : List UInt8) (pc : Nat) :
    Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let b ← code[pc]?
  let instr ← parseInstr b
  let w := argOnNBytesOfInstr instr
  some (instr, if w == 0 then none
               else some (Mem.fromBytes32 ((code.drop (pc+1)).take w), w))

/-! ## Single-item round-trips (each item decodes back at the head of its bytes) -/

/-- A non-PUSH op decodes back to itself, with no immediate. -/
theorem decodeAtL_op (lm : Label → UInt256) (o : Operation .EVM)
    (hw : argOnNBytesOfInstr o = 0) :
    decodeAtL (Item.encode1 lm (.op o)) 0 = some (o, none) := by
  simp [decodeAtL, Item.encode1, parseInstr_serializeInstr, hw]

/-- A `push32` decodes back to `PUSH32` with its immediate intact. -/
theorem decodeAtL_push32 (lm : Label → UInt256) (imm : UInt256) :
    decodeAtL (Item.encode1 lm (.push32 imm)) 0 = some (.Push .PUSH32, some (imm, 32)) := by
  have hlen : (Mem.toBytes32 imm).length = 32 := Mem.toBytes32_length imm
  have htake : (Mem.toBytes32 imm).take 32 = Mem.toBytes32 imm := by
    rw [← hlen]; exact List.take_length
  show (decodeAtL (0x7f :: Mem.toBytes32 imm) 0) = _
  unfold decodeAtL
  simp only [List.getElem?_cons_zero, List.drop_succ_cons, List.drop_zero, bind, Option.bind]
  rw [show (parseInstr 127 : Option (Operation .EVM)) = some (Operation.Push POp.PUSH32) from rfl]
  dsimp only
  rw [show argOnNBytesOfInstr (Operation.Push POp.PUSH32) = 32 from rfl, htake,
    Mem.fromBytes32_toBytes32]
  rfl

/-- A `pushLabel` decodes to `PUSH32` of the label's resolved PC (same bytes as
`push32 (lm l)`). -/
theorem decodeAtL_pushLabel (lm : Label → UInt256) (l : Label) :
    decodeAtL (Item.encode1 lm (.pushLabel l)) 0 = some (.Push .PUSH32, some (lm l, 32)) :=
  decodeAtL_push32 lm (lm l)

/-- A `label` site decodes to `JUMPDEST` (the byte `0x5b`). -/
theorem decodeAtL_label (lm : Label → UInt256) (l : Label) :
    decodeAtL (Item.encode1 lm (.label l)) 0 = some (.JUMPDEST, none) := by
  simp [decodeAtL, Item.encode1]
  rfl

/-! ## The minimal-width PUSH codec (the `pushN` payload) -/

/-- `fromBytes'` ignores trailing zero bytes (little-endian high digits). -/
theorem fromBytes'_append_zeros (xs : List UInt8) (k : Nat) :
    fromBytes' (xs ++ List.replicate k 0) = fromBytes' xs := by
  induction xs with
  | nil =>
    simp only [List.nil_append]
    induction k with
    | zero => rfl
    | succ k ih => simp only [List.replicate, fromBytes']; simpa using ih
  | cons b bs ih => simp only [List.cons_append, fromBytes', ih]

/-- A big-endian byte list ignores leading zero bytes. -/
theorem fromBytesBigEndian_zeros_prefix (k : Nat) (bs : List UInt8) :
    fromBytesBigEndian (List.replicate k 0 ++ bs) = fromBytesBigEndian bs := by
  unfold fromBytesBigEndian
  simp only [Function.comp, List.reverse_append, List.reverse_replicate, fromBytes'_append_zeros]

/-- The high `32 - n` bytes of the big-endian encoding are zero when the value
fits in `n` bytes. -/
theorem toBytes32_take_zero (v : UInt256) (n : Nat) (hfit : v.toNat < 256 ^ n) :
    (Mem.toBytes32 v).take (32 - n) = List.replicate (32 - n) 0 := by
  apply List.ext_getElem
  · simp only [List.length_take, Mem.toBytes32_length, List.length_replicate]; omega
  · intro i hi hi2
    have hilt : i < 32 - n := by
      simp only [List.length_take, Mem.toBytes32_length] at hi; omega
    simp only [List.getElem_take, List.getElem_replicate, Mem.toBytes32, List.getElem_map,
      List.getElem_range]
    have : v.toNat / 256 ^ (31 - i) = 0 := by
      apply Nat.div_eq_of_lt
      calc v.toNat < 256 ^ n := hfit
        _ ≤ 256 ^ (31 - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [this]

/-- **The minimal-width payload decodes back to the value when it fits.** -/
theorem fromBytes32_beBytesN (n : Nat) (v : UInt256) (hfit : v.toNat < 256 ^ n) :
    Mem.fromBytes32 (beBytesN n v) = v := by
  have hsplit : Mem.toBytes32 v = List.replicate (32 - n) 0 ++ beBytesN n v := by
    conv_lhs => rw [← List.take_append_drop (32 - n) (Mem.toBytes32 v)]
    rw [toBytes32_take_zero v n hfit, beBytesN]
  calc Mem.fromBytes32 (beBytesN n v)
      = UInt256.ofNat (fromBytesBigEndian (List.replicate (32 - n) 0 ++ beBytesN n v)) := by
          rw [fromBytesBigEndian_zeros_prefix]; rfl
    _ = Mem.fromBytes32 (Mem.toBytes32 v) := by rw [← hsplit]; rfl
    _ = v := Mem.fromBytes32_toBytes32 v

/-- **General minimal-width PUSH decode.** A `PUSHk` (`k = argOnNBytesOfInstr`)
whose immediate fits in its `k` bytes decodes back to that immediate.
`decodeAtL_push32` is the `k = 32`, fixed-width special case. -/
theorem decodeAtL_pushN (p : POp) (imm : UInt256) (tail : List UInt8)
    (hpos : 1 ≤ argOnNBytesOfInstr (.Push p))
    (hfit : imm.toNat < 256 ^ argOnNBytesOfInstr (.Push p)) :
    decodeAtL (serializeInstr (.Push p) :: (beBytesN (argOnNBytesOfInstr (.Push p)) imm ++ tail)) 0
      = some (.Push p, some (imm, argOnNBytesOfInstr (.Push p))) := by
  have hlen : (beBytesN (argOnNBytesOfInstr (.Push p)) imm).length = argOnNBytesOfInstr (.Push p) :=
    beBytesN_length _ imm (argOnNBytesOfInstr_push_le p)
  have htake : (beBytesN (argOnNBytesOfInstr (.Push p)) imm ++ tail).take
                 (argOnNBytesOfInstr (.Push p)) = beBytesN (argOnNBytesOfInstr (.Push p)) imm :=
    List.take_left' hlen
  unfold decodeAtL
  simp only [List.getElem?_cons_zero, List.drop_succ_cons, List.drop_zero, bind, Option.bind]
  rw [parseInstr_serializeInstr (.Push p)]
  dsimp only
  rw [if_neg (by simpa using Nat.one_le_iff_ne_zero.mp hpos), htake, fromBytes32_beBytesN _ _ hfit]

/-! ## The two-pass layout

Pass 2 (`emit`) concatenates each item's encoding. Crucially, the emitted
*length* depends only on the fixed item widths, **not** on the resolved label
map — so pass 1 (computing offsets) and pass 2 (filling in values) cannot
disagree. That `emit_length` independence is what makes the two-pass scheme
sound. -/

/-- Emit a whole program: concatenate each item's byte encoding. -/
def emit (lm : Label → UInt256) (prog : List Item) : List UInt8 :=
  (prog.map (·.encode1 lm)).flatten

@[simp] theorem emit_nil (lm : Label → UInt256) : emit lm [] = [] := rfl

@[simp] theorem emit_cons (lm : Label → UInt256) (a : Item) (rest : List Item) :
    emit lm (a :: rest) = a.encode1 lm ++ emit lm rest := by
  simp [emit]

theorem emit_append (lm : Label → UInt256) (xs ys : List Item) :
    emit lm (xs ++ ys) = emit lm xs ++ emit lm ys := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [emit_cons, ih, List.append_assoc]

/-- **Layout is label-map independent.** The emitted length is the sum of the
fixed item widths; resolved values cannot shift any offset. This is precisely
why pass 1 (offsets from widths) and pass 2 (filling values) agree. -/
theorem emit_length (lm : Label → UInt256) (prog : List Item) :
    (emit lm prog).length = (prog.map Item.width).sum := by
  induction prog with
  | nil => simp
  | cons a rest ih =>
    rw [emit_cons, List.length_append, Item.encode1_length, ih, List.map_cons, List.sum_cons]

/-- **Prefix decode.** Decoding at the end of a prefix sees exactly the suffix
from its start: both the read position and the immediate window shift by
`pre.length`, leaving the whole decode unchanged. -/
theorem decodeAtL_prefix (pre rest : List UInt8) :
    decodeAtL (pre ++ rest) pre.length = decodeAtL rest 0 := by
  unfold decodeAtL
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  have hdrop : (pre ++ rest).drop (pre.length + 1) = rest.drop (0 + 1) := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1; omega
  rw [hdrop]

/-! ## Fetch-decode correctness at item offsets, and jump resolution

The payoff: decoding the emitted program at item `i`'s program counter sees
exactly item `i`'s own bytes (`decodeAtL_offset`), so each instruction means at
its PC what the backend intended; and every `.label` site lands on a real
`JUMPDEST` byte (`emit_getElem?_label`), the prerequisite for `EVM.D_J` admitting
it as a valid jump target. The `.pushLabel` corollary is the dense-dispatch
primitive: a table entry decodes to the label's *resolved* PC — what `djmp`'s
oracle cannot evaluate. -/

/-- Well-formedness: an `.op` item must carry a zero-immediate opcode (PUSHes go
through `push32`/`pushLabel`); a `pushN` must carry a real PUSH whose immediate
fits its declared width. The other constructors are always well-formed. -/
def Item.WF : Item → Prop
  | .op o        => argOnNBytesOfInstr o = 0
  | .pushN p imm => 1 ≤ argOnNBytesOfInstr (.Push p) ∧ imm.toNat < 256 ^ argOnNBytesOfInstr (.Push p)
  | _            => True

instance : DecidablePred Item.WF := fun a => by
  unfold Item.WF; cases a <;> dsimp only <;> infer_instance

/-- A zero-immediate op decodes back to itself even with trailing bytes. -/
theorem decodeAtL_op_tail (o : Operation .EVM) (tail : List UInt8)
    (hw : argOnNBytesOfInstr o = 0) :
    decodeAtL (serializeInstr o :: tail) 0 = some (o, none) := by
  simp [decodeAtL, parseInstr_serializeInstr, hw]

/-- A `push32`'s 32 immediate bytes are self-delimiting: trailing bytes don't
change its decode. -/
theorem decodeAtL_push32_tail (imm : UInt256) (tail : List UInt8) :
    decodeAtL (0x7f :: (Mem.toBytes32 imm ++ tail)) 0 = some (.Push .PUSH32, some (imm, 32)) := by
  have hlen : (Mem.toBytes32 imm).length = 32 := Mem.toBytes32_length imm
  have htake : (Mem.toBytes32 imm ++ tail).take 32 = Mem.toBytes32 imm := by
    rw [← hlen]; exact List.take_left
  unfold decodeAtL
  simp only [List.getElem?_cons_zero, List.drop_succ_cons, List.drop_zero, bind, Option.bind]
  rw [show (parseInstr 127 : Option (Operation .EVM)) = some (Operation.Push POp.PUSH32) from rfl]
  dsimp only
  rw [show argOnNBytesOfInstr (Operation.Push POp.PUSH32) = 32 from rfl, htake,
    Mem.fromBytes32_toBytes32]
  rfl

/-- **Self-delimiting items.** Appending bytes after a well-formed item's
encoding does not change how that item decodes. -/
theorem decodeAtL_encode1_append (lm : Label → UInt256) (a : Item) (tail : List UInt8)
    (hwf : a.WF) :
    decodeAtL (a.encode1 lm ++ tail) 0 = decodeAtL (a.encode1 lm) 0 := by
  cases a with
  | op o =>
    simp only [Item.encode1, List.singleton_append]
    rw [decodeAtL_op_tail o tail hwf, decodeAtL_op_tail o [] hwf]
  | push32 imm =>
    simp only [Item.encode1, List.cons_append]
    rw [decodeAtL_push32_tail imm tail,
      show (Mem.toBytes32 imm : List UInt8) = Mem.toBytes32 imm ++ [] from (List.append_nil _).symm,
      decodeAtL_push32_tail imm []]
  | pushN p imm =>
    obtain ⟨hpos, hfit⟩ := hwf
    simp only [Item.encode1, List.cons_append]
    rw [decodeAtL_pushN p imm tail hpos hfit,
      show (beBytesN (argOnNBytesOfInstr (.Push p)) imm : List UInt8)
         = beBytesN (argOnNBytesOfInstr (.Push p)) imm ++ [] from (List.append_nil _).symm,
      decodeAtL_pushN p imm [] hpos hfit]
  | pushLabel l =>
    simp only [Item.encode1, List.cons_append]
    rw [decodeAtL_push32_tail (lm l) tail,
      show (Mem.toBytes32 (lm l) : List UInt8) = Mem.toBytes32 (lm l) ++ [] from (List.append_nil _).symm,
      decodeAtL_push32_tail (lm l) []]
  | label l =>
    simp only [Item.encode1]
    rfl

/-- The program counter of item `i`: the length of everything emitted before it.
By `emit_length` this is the sum of the prior items' fixed widths, so it does not
depend on the label map. -/
def offsetOf (lm : Label → UInt256) (prog : List Item) (i : Nat) : Nat :=
  (emit lm (prog.take i)).length

/-- **Fetch-decode correctness.** Decoding the emitted program at item `i`'s
program counter sees exactly item `i`'s own bytes — so by the single-item
round-trips, the byte at `offsetOf … i` decodes back to item `i`. -/
theorem decodeAtL_offset (lm : Label → UInt256) (prog : List Item) (i : Nat)
    (hi : i < prog.length) (hwf : (prog[i]'hi).WF) :
    decodeAtL (emit lm prog) (offsetOf lm prog i) = decodeAtL ((prog[i]'hi).encode1 lm) 0 := by
  have hsplit : emit lm prog = emit lm (prog.take i) ++ emit lm (prog.drop i) := by
    rw [← emit_append, List.take_append_drop]
  rw [hsplit, offsetOf, decodeAtL_prefix, List.drop_eq_getElem_cons hi, emit_cons,
    decodeAtL_encode1_append _ _ _ hwf]

/-- **Jump targets resolve.** A `.label` item lands on a real `JUMPDEST` byte
(`0x5b`) at its program counter — what `EVM.D_J` needs to admit it as a valid
jump destination (discharged against the real `ByteArray` in M5.4). -/
theorem emit_getElem?_label (lm : Label → UInt256) (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hlab : (prog[i]'hi) = .label l) :
    (emit lm prog)[offsetOf lm prog i]? = some 0x5b := by
  have hsplit : emit lm prog = emit lm (prog.take i) ++ emit lm (prog.drop i) := by
    rw [← emit_append, List.take_append_drop]
  rw [hsplit, offsetOf, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.drop_eq_getElem_cons hi, hlab, emit_cons]
  simp [Item.encode1]

/-- A label site, decoded at its program counter, is a `JUMPDEST`. -/
theorem decodeAtL_offset_label (lm : Label → UInt256) (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hlab : (prog[i]'hi) = .label l) :
    decodeAtL (emit lm prog) (offsetOf lm prog i) = some (.JUMPDEST, none) := by
  rw [decodeAtL_offset lm prog i hi (by rw [hlab]; trivial), hlab, decodeAtL_label]

/-- A dispatch-table label push, decoded at its program counter, yields the
label's *resolved* program counter — the dense-dispatch primitive the `djmp`
oracle cannot evaluate. -/
theorem decodeAtL_offset_pushLabel (lm : Label → UInt256) (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hpl : (prog[i]'hi) = .pushLabel l) :
    decodeAtL (emit lm prog) (offsetOf lm prog i) = some (.Push .PUSH32, some (lm l, 32)) := by
  rw [decodeAtL_offset lm prog i hi (by rw [hpl]; trivial), hpl, decodeAtL_pushLabel]

end EvmYul.Venom.Asm

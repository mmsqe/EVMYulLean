import EvmYul.Venom.Asm

/-!
# M5.5 — jump-destination alignment: every label is a valid `JUMP` target

`Asm.lean` proves a `.label` site holds a `JUMPDEST` byte (`emit_getElem?_label`),
but the EVM does **not** treat every `0x5b` byte as a valid jump destination — one
buried inside a PUSH immediate is rejected. `EVM.X` only admits targets in
`EVM.D_J`, the set the linear byte-scan `EVM.D_J_aux` collects by walking
instruction by instruction from PC 0.

This file proves the **alignment** property `D_J` relies on: `djScan` — a total,
fuel-bounded structural mirror of `EVM.D_J_aux` — collects, over the assembled
program, *exactly* the offsets of its jump-destination items (`djScan_emit`). The
crux is that each item is self-delimiting, so the scan advances by exactly the
item's width and therefore visits every item boundary and no interior byte. The
headline corollary `offsetOf_mem_djScan` concludes that a label's resolved program
counter is a recognized jump destination — a `JUMP`/`JUMPI` to it is valid, never
a `BadJumpDestination`.

(`EVM.D_J_aux` itself is a `partial def`, hence opaque to the kernel; `djScan`
faithfully mirrors its recurrence with explicit fuel so the alignment content is
provable. Relating the two is the residual partial-definition step.)
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation

theorem decodeAtL_drop (code : List UInt8) (pc : Nat) :
    decodeAtL code pc = decodeAtL (code.drop pc) 0 := by
  unfold decodeAtL
  have h0 : code[pc]? = (code.drop pc)[0]? := by rw [List.getElem?_drop, Nat.add_zero]
  have h1 : code.drop (pc + 1) = (code.drop pc).drop (0 + 1) := by rw [List.drop_drop]
  rw [h0, h1]

/-- The opcode an item decodes to. -/
def Item.decodedOp : Item → Operation .EVM
  | .op o        => o
  | .push32 _    => .Push .PUSH32
  | .pushN p _   => .Push p
  | .pushLabel _ => .Push .PUSH32
  | .label _     => .JUMPDEST

/-- The immediate an item decodes to. -/
def Item.decodedArg (lm : Label → UInt256) : Item → Option (UInt256 × Nat)
  | .op _        => none
  | .push32 i    => some (i, 32)
  | .pushN p i   => some (i, argOnNBytesOfInstr (.Push p))
  | .pushLabel l => some (lm l, 32)
  | .label _     => none

/-- Whether an item emits a `JUMPDEST` (a valid jump target). -/
def Item.isJD : Item → Bool
  | .op o        => decide (o = Operation.JUMPDEST)
  | .label _     => true
  | _            => false

/-- A well-formed item decodes (even with trailing code) to its `decodedOp`/`decodedArg`. -/
theorem item_decode (lm : Label → UInt256) (a : Item) (tail : List UInt8) (hwf : a.WF) :
    decodeAtL (a.encode1 lm ++ tail) 0 = some (a.decodedOp, a.decodedArg lm) := by
  cases a with
  | op o =>
    simp only [Item.encode1, List.singleton_append, Item.decodedOp, Item.decodedArg]
    exact decodeAtL_op_tail o tail hwf
  | push32 imm =>
    simp only [Item.encode1, List.cons_append, Item.decodedOp, Item.decodedArg]
    exact decodeAtL_push32_tail imm tail
  | pushN p imm =>
    obtain ⟨hpos, hfit⟩ := hwf
    simp only [Item.encode1, List.cons_append, Item.decodedOp, Item.decodedArg]
    exact decodeAtL_pushN p imm tail hpos hfit
  | pushLabel l =>
    simp only [Item.encode1, List.cons_append, Item.decodedOp, Item.decodedArg]
    exact decodeAtL_push32_tail (lm l) tail
  | label l =>
    simp only [Item.encode1, Item.decodedOp, Item.decodedArg, List.cons_append, List.nil_append]
    exact decodeAtL_op_tail Operation.JUMPDEST tail rfl

/-- The scan advances by exactly the item's width. -/
theorem decodedOp_advance (a : Item) (hwf : a.WF) :
    1 + argOnNBytesOfInstr (a.decodedOp) = a.width := by
  cases a with
  | op o => simp only [Item.decodedOp, Item.width]; rw [Item.WF] at hwf; omega
  | push32 _ => rfl
  | pushN p _ => simp only [Item.decodedOp, Item.width]
  | pushLabel _ => rfl
  | label _ => rfl

/-- Decoded `JUMPDEST` exactly when the item emits one. -/
theorem decodedOp_isJD (a : Item) :
    decide (a.decodedOp = Operation.JUMPDEST) = a.isJD := by
  cases a with
  | op o => rfl
  | push32 _ => rfl
  | pushN _ _ => rfl
  | pushLabel _ => rfl
  | label _ => rfl

/-- Total, fuel-bounded byte-level jump-destination scan — the structural mirror
of `EVM.D_J_aux`: decode at `pc`, advance past the instruction, record `pc` when
it is a `JUMPDEST`. -/
def djScan (code : List UInt8) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, pc, acc =>
    match decodeAtL code pc with
    | none => acc
    | some (instr, _) =>
      djScan code fuel (pc + 1 + argOnNBytesOfInstr instr)
        (if decide (instr = Operation.JUMPDEST) then acc ++ [pc] else acc)

/-- The absolute offsets of the jump-destination items (the intended valid jump
targets), starting the layout at `pc`. -/
def jumpdestOffsets : List Item → Nat → List Nat
  | [], _ => []
  | a :: rest, pc => (if a.isJD then [pc] else []) ++ jumpdestOffsets rest (pc + a.width)

/-- **Jump-destination alignment.** Scanning the assembled program byte by byte
(as `EVM.D_J` does) collects exactly the offsets of its jump-destination items —
so every `JUMPDEST` is recognized at a true instruction boundary, and no `0x5b`
byte buried inside a PUSH immediate is ever mistaken for one. With the scan run
over a window whose suffix from `pc` is the emitted program. -/
theorem djScan_emit (lm : Label → UInt256) (prog : List Item) (hwf : ∀ a ∈ prog, a.WF) :
    ∀ (whole : List UInt8) (pc : Nat) (acc : List Nat) (fuel : Nat),
      whole.drop pc = emit lm prog → prog.length ≤ fuel →
      djScan whole fuel pc acc = acc ++ jumpdestOffsets prog pc := by
  induction prog with
  | nil =>
    intro whole pc acc fuel hdrop _
    have hnone : decodeAtL whole pc = none := by rw [decodeAtL_drop, hdrop, emit_nil]; rfl
    cases fuel with
    | zero => simp [djScan, jumpdestOffsets]
    | succ f => simp [djScan, hnone, jumpdestOffsets]
  | cons a rest ih =>
    intro whole pc acc fuel hdrop hlen
    cases fuel with
    | zero => simp [List.length_cons] at hlen
    | succ f =>
      have hwfa : a.WF := hwf a (List.mem_cons_self ..)
      have hwfr : ∀ x ∈ rest, x.WF := fun x hx => hwf x (List.mem_cons_of_mem a hx)
      have hdec : decodeAtL whole pc = some (a.decodedOp, a.decodedArg lm) := by
        rw [decodeAtL_drop, hdrop, emit_cons]; exact item_decode lm a (emit lm rest) hwfa
      have hadv : pc + 1 + argOnNBytesOfInstr a.decodedOp = pc + a.width := by
        have := decodedOp_advance a hwfa; omega
      have hdrop' : whole.drop (pc + a.width) = emit lm rest := by
        rw [← List.drop_drop, hdrop, emit_cons, ← Item.encode1_length lm a, List.drop_left]
      have hflen : rest.length ≤ f := by simp only [List.length_cons] at hlen; omega
      rw [djScan, hdec]
      dsimp only
      rw [hadv, ih hwfr whole (pc + a.width) _ f hdrop' hflen, jumpdestOffsets, decodedOp_isJD a]
      cases a.isJD <;> simp [List.append_assoc]

/-- A jump-destination item's offset is among the collected offsets. -/
theorem mem_jumpdestOffsets (prog : List Item) (i pc : Nat) (hi : i < prog.length)
    (hjd : (prog[i]'hi).isJD) :
    pc + ((prog.take i).map Item.width).sum ∈ jumpdestOffsets prog pc := by
  induction prog generalizing i pc with
  | nil => exact absurd hi (by simp)
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hjd
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, jumpdestOffsets, hjd,
        if_true, List.singleton_append, List.mem_cons, true_or]
    | succ j =>
      have hj : j < rest.length := by simp only [List.length_cons] at hi; omega
      have hjd' : (rest[j]'hj).isJD := by simpa using hjd
      have := ih j (pc + a.width) hj hjd'
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, jumpdestOffsets]
      rw [show pc + (a.width + ((rest.take j).map Item.width).sum)
            = (pc + a.width) + ((rest.take j).map Item.width).sum from by omega]
      exact List.mem_append.mpr (Or.inr this)

/-- **Every label is a recognized jump destination.** Its program counter is
collected by the byte-level scan that `EVM.D_J` runs — i.e. a `JUMP`/`JUMPI` to a
label's resolved PC is a *valid* destination, not a `BadJumpDestination`. -/
theorem offsetOf_mem_djScan (lm : Label → UInt256) (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hwf : ∀ a ∈ prog, a.WF) (hlab : (prog[i]'hi) = .label l)
    (fuel : Nat) (hfuel : prog.length ≤ fuel) :
    offsetOf lm prog i ∈ djScan (emit lm prog) fuel 0 [] := by
  have hjd : (prog[i]'hi).isJD := by rw [hlab]; rfl
  rw [djScan_emit lm prog hwf (emit lm prog) 0 [] fuel (by simp) hfuel, List.nil_append,
    offsetOf, emit_length]
  simpa using mem_jumpdestOffsets prog i 0 hi hjd

end EvmYul.Venom.Asm

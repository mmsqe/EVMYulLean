import EvmYul.Venom.AsmJumps

/-!
# M5.6 — pass 1: the label resolver (closing the two-pass loop)

Everything in `Asm.lean` / `AsmJumps.lean` is parameterized over a *resolved*
label map `lm : Label → UInt256` — an oracle. A real assembler must **compute**
that map (pass 1) and prove the computed program counters are self-consistent:
the PC a label resolves to must actually be a valid jump destination in the
bytecode emitted *from that same map*.

`findLabelOffset` is pass 1 — walk the items accumulating widths, a label resolves
to the offset of its defining `.label` item. `labelMap prog` packages it as the
map pass 2 consumes. The results close the loop on the program assembled from
itself (`emit (labelMap prog) prog`, no external oracle):

* `findLabelOffset_mem` — a resolved offset is one of the jump-destination offsets;
* `labelMap_resolves_to_jumpdest` — hence it is collected by the `D_J`-style scan,
  i.e. a valid jump target;
* `dispatch_target_valid_jumpdest` — the value a `pushLabel` dispatch entry pushes
  (`labelMap prog l`) is a valid jump destination. With `decodeAtL_offset_pushLabel`
  (the entry decodes to exactly that value), the dense dispatch table is end-to-end
  sound with no oracle map.
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation

/-- **Pass 1.** Walk the items accumulating byte offsets; a label resolves to the
offset of its defining `.label` item (first occurrence). -/
def findLabelOffset : List Item → Label → Nat → Nat
  | [], _, _ => 0
  | a :: rest, l, off =>
    match a with
    | .label l' => if l' = l then off else findLabelOffset rest l (off + a.width)
    | _         => findLabelOffset rest l (off + a.width)

/-- The resolved label → PC map computed from the program itself (closing the
two-pass loop: no external oracle map). -/
def labelMap (prog : List Item) : Label → UInt256 :=
  fun l => UInt256.ofNat (findLabelOffset prog l 0)

/-- A resolved label offset is one of the program's jump-destination offsets. -/
theorem findLabelOffset_mem (prog : List Item) (l : Label) (off : Nat)
    (hl : (Item.label l) ∈ prog) :
    findLabelOffset prog l off ∈ jumpdestOffsets prog off := by
  induction prog generalizing off with
  | nil => simp at hl
  | cons a rest ih =>
    cases a with
    | label l' =>
      simp only [findLabelOffset, jumpdestOffsets, Item.isJD, if_true, List.singleton_append]
      by_cases hll : l' = l
      · simp [hll, List.mem_cons]
      · simp only [hll, if_false]
        have hl' : (Item.label l) ∈ rest := by
          rcases List.mem_cons.mp hl with h | h
          · simp only [Item.label.injEq] at h; exact absurd h.symm hll
          · exact h
        exact List.mem_cons.mpr (Or.inr (ih (off + (Item.label l').width) hl'))
    | op o =>
      simp only [findLabelOffset, jumpdestOffsets]
      have hl' : (Item.label l) ∈ rest := by
        rcases List.mem_cons.mp hl with h | h
        · exact absurd h (by simp)
        · exact h
      exact List.mem_append.mpr (Or.inr (ih (off + (Item.op o).width) hl'))
    | push32 imm =>
      simp only [findLabelOffset, jumpdestOffsets, Item.isJD]
      have hl' : (Item.label l) ∈ rest := by
        rcases List.mem_cons.mp hl with h | h
        · exact absurd h (by simp)
        · exact h
      simpa using ih (off + (Item.push32 imm).width) hl'
    | pushN p imm =>
      simp only [findLabelOffset, jumpdestOffsets, Item.isJD]
      have hl' : (Item.label l) ∈ rest := by
        rcases List.mem_cons.mp hl with h | h
        · exact absurd h (by simp)
        · exact h
      simpa using ih (off + (Item.pushN p imm).width) hl'
    | pushLabel l'' =>
      simp only [findLabelOffset, jumpdestOffsets, Item.isJD]
      have hl' : (Item.label l) ∈ rest := by
        rcases List.mem_cons.mp hl with h | h
        · exact absurd h (by simp)
        · exact h
      simpa using ih (off + (Item.pushLabel l'').width) hl'

/-- **Two-pass loop closed.** The PC that pass 1 resolves a label to is a valid
jump destination in the program pass 2 emits *from that same map* — fully
self-contained (no external oracle map: `emit (labelMap prog) prog`). -/
theorem labelMap_resolves_to_jumpdest (prog : List Item) (l : Label)
    (hwf : ∀ a ∈ prog, a.WF) (hl : (Item.label l) ∈ prog)
    (fuel : Nat) (hfuel : prog.length ≤ fuel) :
    findLabelOffset prog l 0 ∈ djScan (emit (labelMap prog) prog) fuel 0 [] := by
  rw [djScan_emit (labelMap prog) prog hwf (emit (labelMap prog) prog) 0 [] fuel (by simp) hfuel,
    List.nil_append]
  exact findLabelOffset_mem prog l 0 hl

/-- **Dense-dispatch capstone.** The value a dispatch-table entry (`pushLabel l`)
pushes — `labelMap prog l` — is a valid jump destination in the self-assembled
bytecode. With `decodeAtL_offset_pushLabel` (the entry decodes to exactly this
value), the dispatch table is end-to-end sound: each entry pushes a real,
in-`D_J` program counter, no oracle map involved. -/
theorem dispatch_target_valid_jumpdest (prog : List Item) (l : Label)
    (hwf : ∀ a ∈ prog, a.WF) (hl : (Item.label l) ∈ prog)
    (fuel : Nat) (hfuel : prog.length ≤ fuel)
    (hsmall : findLabelOffset prog l 0 < 2 ^ 256) :
    (labelMap prog l).toNat ∈ djScan (emit (labelMap prog) prog) fuel 0 [] := by
  have heq : (labelMap prog l).toNat = findLabelOffset prog l 0 := by
    simp only [labelMap, UInt256.ofNat, UInt256.toNat, Id.run]; exact Nat.mod_eq_of_lt hsmall
  rw [heq]; exact labelMap_resolves_to_jumpdest prog l hwf hl fuel hfuel


end EvmYul.Venom.Asm

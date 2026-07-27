import EvmYul.Venom.AsmJumps
import EvmYul.Venom.AsmBridge
import EvmYul.Venom.AsmResolve
import EvmYul.Venom.AsmTop

/-!
# M5.8 — the `EVM.D_J` correspondence (jumps are valid in the real EVM)

`AsmJumps.lean` proves the *list* mirror `djScan` collects exactly the label
offsets, but `EVM.X` admits a `JUMP` only if the target is in `EVM.D_J`, computed
by `EVM.D_J_aux` — a `partial def`, hence opaque to the kernel (no equation
lemma, cannot be unfolded or inducted on).

We bridge that gap honestly. `DJAuxSpec` names `D_J_aux`'s defining recurrence as
an interface (it is the literal body of the `partial def`; discharging it would
need `D_J_aux` reformulated as a fuel/structural definition in the core EVM — the
same kind of residual as the development's other irreducibles). *Under that one
interface, everything else is proved*: `DJ_aux_eq_djScan` shows the partial
`D_J_aux` equals the total `djScan` (`UInt256` PCs read back as `Nat`) by fuel
induction, using only the recurrence to unfold each step; the headline
`labelMap_mem_DJ` then lifts `offsetOf_mem_djScan` to conclude a label's program
counter is in the real `EVM.D_J (assemble prog) 0` — so a `JUMP`/`JUMPI` to it is
admitted, never `BadJumpDestination`.
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM

theorem N_toNat (i : UInt256) (instr : Operation .EVM)
    (h : i.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 256) :
    (N i instr).toNat = i.toNat + 1 + argOnNBytesOfInstr instr := by
  unfold N
  rw [uint256_add_toNat, uint256_add_toNat, uint256_ofNat_toNat]
  rw [show (⟨1⟩ : UInt256).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : argOnNBytesOfInstr instr < 2^256),
    Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2^256), Nat.mod_eq_of_lt h]

theorem get?_self_toList (code : ByteArray) (n : Nat) : code.get? n = code.toList[n]? := by
  rw [ba_get?_eq, ← Array.getElem?_toList, ← MemBridge.toList_eq_data]

/-- `djScan` over a `ByteArray`'s bytes, one step, written as `EVM.D_J_aux`'s
recurrence (opcode-only; `djScan` ignores the immediate). -/
theorem djScan_succ_eq (code : ByteArray) (fuel i : Nat) (acc : List Nat) :
    djScan code.toList (fuel + 1) i acc
      = match code.get? i >>= parseInstr with
        | none => acc
        | some cᵢ => djScan code.toList fuel (i + 1 + argOnNBytesOfInstr cᵢ)
            (if decide (cᵢ = Operation.JUMPDEST) then acc ++ [i] else acc) := by
  rw [djScan]
  have hb := get?_self_toList code i
  rcases hbyte : code.toList[i]? with _ | b
  · rw [show (code.get? i >>= parseInstr) = none from by rw [hb, hbyte]; rfl]
    simp [decodeAtL, hbyte]
  · rcases hpi : parseInstr b with _ | cᵢ
    · rw [show (code.get? i >>= parseInstr) = none from by rw [hb, hbyte]; simp [hpi]]
      simp [decodeAtL, hbyte, hpi]
    · rw [show (code.get? i >>= parseInstr) = some cᵢ from by rw [hb, hbyte]; simp [hpi]]
      simp [decodeAtL, hbyte, hpi]

/-- The defining recurrence of `EVM.D_J_aux`. It is the literal body of the
`partial def`, hence true, but Lean exposes no equation lemma for a `partial def`,
so we name it as an interface (like the development's other irreducibles).
Discharging it would need `D_J_aux` reformulated as a fuel/structural def in core. -/
def DJAuxSpec : Prop :=
  ∀ (c : ByteArray) (i : UInt256) (r : Array UInt256),
    D_J_aux c i r = match c.get? i.toNat >>= parseInstr with
      | none => r
      | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = Operation.JUMPDEST then r.push i else r)

/-- **Partial→total bridge.** Under the `DJAuxSpec` interface, the partial
`EVM.D_J_aux` equals the total list mirror `djScan` (its `UInt256` PCs read back
as `Nat`), given enough fuel and a realistic no-wraparound code-size bound. -/
theorem DJ_aux_eq_djScan (hspec : DJAuxSpec) (code : ByteArray) (hsz : code.size + 33 ≤ 2 ^ 256) :
    ∀ (fuel : Nat) (i : UInt256) (acc : Array UInt256), code.size ≤ i.toNat + fuel →
      (D_J_aux code i acc).toList.map UInt256.toNat
        = djScan code.toList fuel i.toNat (acc.toList.map UInt256.toNat) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hf
    rw [hspec code i acc,
      show (code.get? i.toNat >>= parseInstr) = none from by
        rw [show code.get? i.toNat = none from by unfold ByteArray.get?; rw [dif_neg (by omega)]]; rfl]
    simp [djScan]
  | succ fuel ih =>
    intro i acc hf
    rw [hspec code i acc, djScan_succ_eq code fuel i.toNat (acc.toList.map UInt256.toNat)]
    cases hopt : code.get? i.toNat >>= parseInstr with
    | none => rfl
    | some cᵢ =>
      have hlt : i.toNat < code.size := by
        by_contra hc
        rw [show code.get? i.toNat = none from by unfold ByteArray.get?; rw [dif_neg (by omega)]] at hopt
        simp at hopt
      have hadv : (N i cᵢ).toNat = i.toNat + 1 + argOnNBytesOfInstr cᵢ :=
        N_toNat i cᵢ (by have h32 := argOnNBytesOfInstr_le cᵢ; omega)
      have hpush : (if cᵢ = Operation.JUMPDEST then acc.push i else acc).toList.map UInt256.toNat
                 = (if decide (cᵢ = Operation.JUMPDEST)
                    then acc.toList.map UInt256.toNat ++ [i.toNat] else acc.toList.map UInt256.toNat) := by
        by_cases hj : cᵢ = Operation.JUMPDEST <;> simp [hj, Array.toList_push]
      rw [ih (N i cᵢ) (if cᵢ = Operation.JUMPDEST then acc.push i else acc) (by omega), hadv, hpush]

theorem Item.width_pos (a : Item) : 1 ≤ a.width := by cases a <;> simp [Item.width]

theorem length_le_emit_length (lm : Label → UInt256) (prog : List Item) :
    prog.length ≤ (emit lm prog).length := by
  rw [emit_length]
  induction prog with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have := a.width_pos; omega

/-- **A label is a valid jump destination in the real EVM** (under the `DJAuxSpec`
interface). Its program counter is in `EVM.D_J (assemble prog) 0` — the set
`EVM.X` checks before a `JUMP`/`JUMPI`, so the jump is admitted, never a
`BadJumpDestination`. This lifts the list-level `offsetOf_mem_djScan` to the
partial `EVM.D_J` the driver actually runs. -/
theorem labelMap_mem_DJ (hspec : DJAuxSpec) (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hwf : ∀ a ∈ prog, a.WF) (hlab : (prog[i]'hi) = .label l)
    (hsz : (assemble prog).size + 33 ≤ 2 ^ 256) :
    offsetOf (labelMap prog) prog i ∈ (D_J (assemble prog) ⟨0⟩).toList.map UInt256.toNat := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  rw [D_J, DJ_aux_eq_djScan hspec (assemble prog) hsz (assemble prog).size ⟨0⟩ #[]
        (by rw [h0]; omega), h0]
  have htl : (assemble prog).toList = emit (labelMap prog) prog := by
    rw [assemble, MemBridge.ltba_toList]
  rw [htl, show (#[] : Array UInt256).toList.map UInt256.toNat = [] from rfl]
  have hfuel : prog.length ≤ (assemble prog).size := by
    rw [assemble, MemBridge.ltba_size]; exact length_le_emit_length _ _
  exact offsetOf_mem_djScan (labelMap prog) prog i l hi hwf hlab (assemble prog).size hfuel

end EvmYul.Venom.Asm

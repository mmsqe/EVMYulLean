import EvmYul.Venom.AsmBridge
import EvmYul.Venom.AsmResolve

/-!
# M5 capstone — the top-level `assemble` API

The public face of the verified assembler: `assemble : List Item → ByteArray`
runs pass 1 (`labelMap`, resolve labels to PCs) and pass 2 (`emit`, lay down
bytes), and the bundled theorems state its correctness against the real EVM
decoder, with no oracle map.

* `assemble_decodes` — decoding `assemble prog` at item `i`'s program counter
  yields exactly item `i`'s instruction (real `EVM.decode`).
* `assemble_dispatch_sound` — the end-to-end dense-dispatch guarantee: at a
  `pushLabel` entry's PC the assembled bytecode decodes to `PUSH32` of a value
  that is a *valid jump destination* in the same program. This is the case the
  `venom_run` oracle could not execute (≥4 selectors → dense jump table whose
  offsets are fixed only at assembly time), now proven sound end to end.
-/

namespace EvmYul.Venom.Asm
open EvmYul EvmYul.EVM Operation

/-- **The assembler.** Pass 1 (`labelMap`) resolves labels to PCs, pass 2
(`emit`) lays down the bytes, packaged as a `ByteArray`. -/
def assemble (prog : List Item) : ByteArray := (emit (labelMap prog) prog).toByteArray

/-- The program counter of item `i` in the assembled output. -/
def itemPC (prog : List Item) (i : Nat) : Nat := offsetOf (labelMap prog) prog i

/-- **Assembler decode correctness.** Decoding `assemble prog` at item `i`'s
program counter yields exactly item `i`'s decoded instruction. -/
theorem assemble_decodes (prog : List Item) (i : Nat) (hi : i < prog.length)
    (hwf : (prog[i]'hi).WF) (hpc : itemPC prog i + 33 < 2 ^ 64) :
    decode (assemble prog) (UInt256.ofNat (itemPC prog i))
      = some ((prog[i]'hi).decodedOp, (prog[i]'hi).decodedArg (labelMap prog)) := by
  rw [assemble, itemPC, decode_emit_offset (labelMap prog) prog i hi hwf hpc,
    show (prog[i]'hi).encode1 (labelMap prog)
       = (prog[i]'hi).encode1 (labelMap prog) ++ [] from (List.append_nil _).symm]
  exact item_decode (labelMap prog) (prog[i]'hi) [] hwf

/-- **Dense-dispatch soundness (end to end).** At a `pushLabel` dispatch entry's
program counter, the assembled bytecode decodes to `PUSH32` of a value that is a
*valid jump destination* in the same program — the complete dense-dispatch
guarantee, with no oracle map. -/
theorem assemble_dispatch_sound (prog : List Item) (i : Nat) (l : Label)
    (hi : i < prog.length) (hwfall : ∀ a ∈ prog, a.WF) (hpl : (prog[i]'hi) = .pushLabel l)
    (hl : (Item.label l) ∈ prog) (hpc : itemPC prog i + 33 < 2 ^ 64)
    (hsmall : findLabelOffset prog l 0 < 2 ^ 256) (fuel : Nat) (hfuel : prog.length ≤ fuel) :
    ∃ v, decode (assemble prog) (UInt256.ofNat (itemPC prog i)) = some (.Push .PUSH32, some (v, 32)) ∧
         v.toNat ∈ djScan (emit (labelMap prog) prog) fuel 0 [] := by
  refine ⟨labelMap prog l, ?_, ?_⟩
  · have hwfi : (prog[i]'hi).WF := hwfall _ (List.getElem_mem hi)
    rw [assemble_decodes prog i hi hwfi hpc, hpl]; rfl
  · exact dispatch_target_valid_jumpdest prog l hwfall hl fuel hfuel hsmall

end EvmYul.Venom.Asm

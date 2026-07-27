import EvmYul.Venom.Hol.Types

/-!
# Liveness — the pure (fixpoint-free) helpers

Port of the phi/edge helpers from `vyper-hol main:venom/analysis/liveness/defs/
livenessDefsScript.sml` that the stack-plan generator uses directly (at a `JMP`
join point). `inputVarsFrom` rewrites a block's live-in set across a control edge,
substituting phi-related entries with the operand coming from the source block.

These are pure (they take the live-var list as input). The *fixpoint* that computes
those live-var lists — `live_vars_at = df_at (df_analyze_fuel …)` — needs the full
dataflow framework (+ cfg + worklist) and is a separate, larger port.
-/

namespace EvmYul.Venom.Hol.Codegen
open EvmYul.Venom.Hol

/-- `phi_pairs`: `(label, value)` pairs from PHI operands `[Label l, Var v, …]`. -/
def phiPairs : List Operand → List (String × String)
  | []                                      => []
  | [_]                                     => []
  | Operand.Label l :: Operand.Var v :: rest => (l, v) :: phiPairs rest
  | _ :: _ :: rest                          => phiPairs rest

/-- `collect_phis`: the leading PHI instructions of a block. -/
def collectPhis : List Instruction → List Instruction
  | []          => []
  | inst :: rest => if inst.opcode = Opcode.PHI then inst :: collectPhis rest else []

/-- `build_phi_maps`: `(output-var → phi-index)` and `(phi-index → src-var for src_label)`. -/
def buildPhiMaps (srcLabel : String) (phis : List Instruction)
    : AssocList String Nat × AssocList Nat String :=
  phis.zipIdx.foldl
    (fun (maps : AssocList String Nat × AssocList Nat String) (phiI : Instruction × Nat) =>
      let (opMap, matching) := maps
      let (phi, i) := phiI
      let pairs := phiPairs phi.operands
      let opMap' := phi.outputs.foldl (fun m v => AssocList.insert String Nat m v i) opMap
      let matching' :=
        match pairs.find? (fun p => p.1 == srcLabel) with
        | some (_, v) => AssocList.insert Nat String matching i v
        | none        => matching
      (opMap', matching'))
    ([], [])

/-- `input_vars_from`: rewrite `baseLiveness` at a join, replacing phi-related entries
    with the source-matching operand (deduped by phi index). -/
def inputVarsFrom (srcLabel : String) (targetInstrs : List Instruction)
    (baseLiveness : List String) : List String :=
  let phis := collectPhis targetInstrs
  if phis.isEmpty then baseLiveness
  else
    let (opMap, matching) := buildPhiMaps srcLabel phis
    (baseLiveness.foldl
      (fun (acc : List String × List Nat) v =>
        let (res, placed) := acc
        match AssocList.lookup String Nat opMap v with
        | some phiIdx =>
          if placed.contains phiIdx then (res, placed)
          else
            match AssocList.lookup Nat String matching phiIdx with
            | some srcV => (res ++ [srcV], phiIdx :: placed)
            | none      => (res, placed)
        | none => (res ++ [v], placed))
      ([], [])).1

/-- **`inputVarsFrom` for a phi-free target** is just the base liveness: with no `PHI` instructions in
    the target, there is nothing to remap, so the expected entry layout is exactly the target's live
    vars at entry. The common case (phis live only at join points) — it reduces the well-scheduling
    obligation `S = inputVarsFrom …` to the cleaner `S = liveVarsAt …`. -/
theorem inputVarsFrom_no_phi (srcLabel : String) (targetInstrs : List Instruction)
    (baseLiveness : List String) (hphi : collectPhis targetInstrs = []) :
    inputVarsFrom srcLabel targetInstrs baseLiveness = baseLiveness := by
  unfold inputVarsFrom
  rw [hphi]
  simp

end EvmYul.Venom.Hol.Codegen

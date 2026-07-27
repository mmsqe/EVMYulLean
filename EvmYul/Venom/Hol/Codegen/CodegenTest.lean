import EvmYul.Venom.Hol.Codegen.CodegenPipeline

/-!
# Codegen smoke test

A compile-time check that the transcribed stack-plan generator actually *runs*
end-to-end (all analyses — cfg / dataflow / liveness / dfg — + the full generator)
and produces a plan for a small well-formed function. This is concrete non-vacuity:
`generateContextPlanFuel` returns `some _` (not the old `none` stub).
-/

namespace EvmYul.Venom.Hol.Codegen.Test
open EvmYul.Venom.Hol EvmYul.Venom.Hol.Codegen

/-- `main(): a := PARAM; b := PARAM; c := ADD a b; STOP`. -/
def exampleCtx : VenomContext :=
  { functions :=
      [{ name := "main",
         blocks :=
           [{ label := "entry",
              instructions :=
                [{ id := 0, opcode := Opcode.PARAM, operands := [], outputs := ["a"] },
                 { id := 1, opcode := Opcode.PARAM, operands := [], outputs := ["b"] },
                 { id := 2, opcode := Opcode.ADD,
                   operands := [Operand.Var "a", Operand.Var "b"], outputs := ["c"] },
                 { id := 3, opcode := Opcode.STOP, operands := [], outputs := [] }] }] }],
    entry := some "main" }

-- The generator runs and produces a (non-`none`) stack plan.
#guard (generateContextPlanFuel 100000 exampleCtx []).isSome

-- …and the plan is non-empty (the block plan + the revert postamble).
#guard ((generateContextPlanFuel 100000 exampleCtx []).map (·.length)).getD 0 > 0

end EvmYul.Venom.Hol.Codegen.Test

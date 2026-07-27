/-
Machine-checked trust-boundary guard for the **Venom → EVM codegen-correctness stack**.

`EvmYul/Venom/Audit.lean` audits the M1–M7 Venom/optimizer results; it has no `Hol` import, so the
~124 `codegen_correct` results this branch is actually about were invisible to the drift guard.
This file closes that hole. Driven by `scripts/codegen_axiom_audit.sh`, which asserts:
  * no result depends on `sorry` (sorryAx) or `Lean.ofReduceBool` (`native_decide`), and
  * every axiom is one of [propext, Classical.choice, Quot.sound] or the isolated M1 FFI pair
    (`ffi_zeroes_size` / `ffi_zeroes_get`).

NOTE the boundary here differs from `Audit.lean`'s by design: the codegen capstones legitimately
inherit the M1 FFI pair through `memoryRel` / `readWithPadding`, so the pair is allowed on ALL of
them — whereas in `Audit.lean` it is pinned to the M1 / machine-memory results only. Keeping the two
guards separate preserves that stricter invariant where it applies.
-/

import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.Demos
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.Dispatch
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeBinops
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeEntry
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeFinal
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeMemory
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeReads
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeSlices
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeTernops
import EvmYul.Venom.Hol.Codegen.GenBlockSimExample.RecipeWalk

namespace EvmYul.Venom.Hol.Codegen.CodegenAudit

#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_jmp_stop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_singleBlockHalt
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_stop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_selfdestruct
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_stop_sched
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_canonical_stop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_canonical_jmpStop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_canonical_addStop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_canonical_selfdestruct
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_jmp_stop_sched
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramSstore
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_singleBlock_halt
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramAdd
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_caller
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramCommBinop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramMul
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramAddNot
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramAddNotNot
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramNotChain
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_chain3
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_paramJmpSstore
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_ncb
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_dvvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mdvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sdvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_smvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_ltvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_gtvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_slvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sgvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_shvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_srvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_savFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_exvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_iszFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cb
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mlvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_anvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_orvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_xrvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_eqvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sxvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_byvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sloFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bkhFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bhhFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_singleBlockHalt_viaRecipe
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_stop_viaRecipe
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_stop_viaDispatch
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_selfdestruct_viaDispatch
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_invalid
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_invalid_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_jmpStop_viaRecipe
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_jmpStop_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_jnzStop_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mxMulVarLit_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mxMulLitVar_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_csFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bretFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_brevFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bsdFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_scFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_acFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_unFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_clFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_llFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_ssFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_tsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_msvFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_m8vFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sh3Fn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mldFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_shsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_ildFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mtpFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_singleBlockStop
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_deadBuriedFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mcpFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_lgFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.ExIS.codegen_correct_isFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_tldFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_r0
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_r0_caller
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_pvrFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bbfFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_racc
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_balFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_ecsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_echFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_adrFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_orgFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_tspFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_numFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_chdFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cbsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_gprFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_glmFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cdsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_gsrFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_bfeFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cszFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_rdsFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_sblFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_tFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_rFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cvStop_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_addStop_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_loopVFn_fuel
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cvInv_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cvJmp_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_cvJnz_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_djFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_retFn_vacuous
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_rFn_symbolic
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_tFn_symbolic
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_admFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.Example.codegen_correct_mmdFn_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_of_HbsimMatch
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_singleBlock_of_HbsimMatch
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_ofBlocks_HbsimMatch
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_ofBlocks_recipeW
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_ofBlocks_recipeW_invCur
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_ofBlocks_recipeW_inv
#print axioms EvmYul.Venom.Hol.Codegen.codegen_correct_ofBlocks_recipeW_invJ

end EvmYul.Venom.Hol.Codegen.CodegenAudit

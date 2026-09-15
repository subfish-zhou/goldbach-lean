import R2FouvryPaid
import Lean

#check @WuPaper.R2Fouvry.shortScale
#check @WuPaper.R2Fouvry.longScale
#check @WuPaper.R2Fouvry.physicalScale
#check @WuPaper.R2Fouvry.physicalScale_eq_four
#check @WuPaper.R2Fouvry.occupied_product_lower
#check @WuPaper.R2Fouvry.high_product_residue
#check @WuPaper.R2Fouvry.strict_nu
#check @WuPaper.R2Fouvry.original_parameters
#check @WuPaper.R2Fouvry.original_error_uniform
#check @WuPaper.R2Fouvry.original_rosser_error_uniform
#check @WuPaper.R2Fouvry.original_sieve_cell
#check @WuPaper.R2Fouvry.original_physical_prefix
#check @WuPaper.R2Fouvry.original_sieve_cell_paid
#check @WuPaper.R2Fouvry.original_physical_prefix_paid

#print axioms WuPaper.R2Fouvry.shortScale
#print axioms WuPaper.R2Fouvry.longScale
#print axioms WuPaper.R2Fouvry.physicalScale
#print axioms WuPaper.R2Fouvry.physicalScale_eq_four
#print axioms WuPaper.R2Fouvry.occupied_product_lower
#print axioms WuPaper.R2Fouvry.high_product_residue
#print axioms WuPaper.R2Fouvry.strict_nu
#print axioms WuPaper.R2Fouvry.original_parameters
#print axioms WuPaper.R2Fouvry.original_error_uniform
#print axioms WuPaper.R2Fouvry.original_rosser_error_uniform
#print axioms WuPaper.R2Fouvry.original_sieve_cell
#print axioms WuPaper.R2Fouvry.original_physical_prefix
#print axioms WuPaper.R2Fouvry.original_sieve_cell_paid
#print axioms WuPaper.R2Fouvry.original_physical_prefix_paid

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo := [`WuPaper.R2Fouvry.original_physical_prefix_paid]
  let mut seen : Std.HashSet Name := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      todo := ci.type.getUsedConstants.toList ++ todo
      if let some v := ci.value? (allowOpaque := true) then
        todo := v.getUsedConstants.toList ++ todo
  for n in [
    `WuPaper.R2Fouvry.high_product_residue,
    `WuPaper.R2Fouvry.strict_nu,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_clean_unconditional,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.direct_wellFactorable_signedError_c2,
    `MathlibNt.SieveTheory.LiLiuPrereqWF.externalTerm_signedWellFactorable,
    `OriginalU8.primorial_error_eq,
    `OriginalU8.exceptional_log_payment,
    `U8Literal.Join.occupied_to_original,
    `U8Literal.Join.sifted_eq] do
    unless seen.contains n do throwError "MISSING_ORIGINAL_PRODUCER {n}"
    logInfo m!"ORIGINAL_PRODUCER_REACHED {n}"
  for n in [
    `sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler,
    `OriginalU8.error_uniform,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.direct_wellFactorable_signedError_kscale,
    `OriginalU8.Weighted.physicalSmall_original_integral] do
    if seen.contains n then throwError "UNADMITTED_SHORTCUT_REACHED {n}"
  logInfo "STRICT_ORIGINAL_CELL_CONE_PASS"

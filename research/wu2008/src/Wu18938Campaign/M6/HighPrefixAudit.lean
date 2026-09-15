import Wu18938Campaign.M6.HighPrefixIntegral
import Lean

set_option pp.all true

#check @Wu18938Campaign.M6.physicalSmall_output_inj
#print axioms Wu18938Campaign.M6.physicalSmall_output_inj
#check @Wu18938Campaign.M6.outputBad_card_le
#print axioms Wu18938Campaign.M6.outputBad_card_le
#check @Wu18938Campaign.M6.outputBad_log_paid
#print axioms Wu18938Campaign.M6.outputBad_log_paid
#check @Wu18938Campaign.M6.physicalPrefix_le_rectangles_paid_output
#print axioms Wu18938Campaign.M6.physicalPrefix_le_rectangles_paid_output
#check @Wu18938Campaign.M6.high_prefix_paid
#print axioms Wu18938Campaign.M6.high_prefix_paid
#check @Wu18938Campaign.M6.high_prefix_normalized
#print axioms Wu18938Campaign.M6.high_prefix_normalized
#check @Wu18938Campaign.M6.paperSmallEighth_normalized_add_low
#print axioms Wu18938Campaign.M6.paperSmallEighth_normalized_add_low
#check @Wu18938Campaign.M6.high_prefix_original_integral
#print axioms Wu18938Campaign.M6.high_prefix_original_integral
#check @Wu18938Campaign.M6.paperSmallEighth_original_integral_add_low
#print axioms Wu18938Campaign.M6.paperSmallEighth_original_integral_add_low

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo := [`Wu18938Campaign.M6.paperSmallEighth_original_integral_add_low]
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
    `Wu18938Campaign.M6.outputBad_card_le,
    `Wu18938Campaign.M6.sqrt_error_log_payment,
    `WuPaper.R2Fouvry.original_physical_prefix_paid,
    `WuPaper.R2Fouvry.high_product_residue,
    `WuPaper.R2Fouvry.strict_nu,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_clean_unconditional,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.direct_wellFactorable_signedError_c2,
    `U8Literal.Mesh.mesh_log_payment,
    `OriginalU8.actualCenter_normalized,
    `Wu18938Campaign.M6.paperSmallEighth_eq,
    `OriginalU8.Weighted.original_mass_integral,
    `Wu18938Campaign.M6.high_prefix_original_integral] do
    unless seen.contains n do throwError "MISSING_M6_PRODUCER {n}"
    logInfo m!"M6_PRODUCER_REACHED {n}"
  for n in [
    `OriginalU8.error_uniform,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.direct_wellFactorable_signedError_kscale,
    `OriginalU8.Weighted.physicalSmall_original_integral] do
    if seen.contains n then throwError "UNADMITTED_M6_SHORTCUT_REACHED {n}"
  logInfo "M6_STRICT_ORIGINAL_HIGH_PREFIX_INTEGRAL_CONE_PASS"

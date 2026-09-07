import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConsumed
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_G12Rough_allRetained_small_epsilon
  let mut todo := [root]
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS5Closed_normalized_upper_paperSplit,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9S5Low_integral_upper,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS5HighFirstClosed_normalized_upper_integral,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_remainingFive_allRetained_small_epsilon,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_uniformScalar_numeric_fixed,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_sharpBuchstabIntegral,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g11UniformScalar_lt_upper,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS3_oneThird_coefficient_le_retained236056871187,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS3_threeElevenths_coefficient_le_retained195190815363,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightFiveCoefficient_zero_ge_allRetained,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.B10Retained.goldbachB10I10_eight_mul_le_540995781,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.S4Retained.goldbachB8MainIntegral_eight_mul_le_60961168,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_paperSplit_allRetainedG11_consumed_small_epsilon,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG12_le_roughSum_add_normalized,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachQuadruple_exceptions_normalized,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG12_roughQuotient_sandwich] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G9_ACTUAL_TOTAL_CONE_PASS {seen.size}"


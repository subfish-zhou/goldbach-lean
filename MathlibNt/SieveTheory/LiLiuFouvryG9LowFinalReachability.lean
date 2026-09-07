import MathlibNt.SieveTheory.LiLiuFouvryG9LowFinal
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9S5Low_integral_upper
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9S5Low_kernel_upper,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9RectangleMass_le_kernel,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9WeightedPrefix_le_primePi,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9WeightedPairPrefix_PNT,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9RelaxedPairKernel_final,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.exists_fouvryG9RelaxedIntegralUpperSum_le_low_add,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9RelaxedIntegralUpperSum_eq_integral,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9RelaxedIntegralLow_eq_setIntegral,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9RelaxedIntegralUpperSum_le_low_add_error,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9MainScalar_payment,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9S5Low_mass_upper,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g9_actual_weighted_euler_eventually,
    `LiLiuPrereqBuchstab.primePi_error_le,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.direct_wellFactorable_signedError_kscale] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G9_ACTUAL_TOTAL_CONE_PASS {seen.size}"


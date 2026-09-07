import MathlibNt.SieveTheory.LiLiuGoldbachG67MovingLower
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67_movingKernel_paid
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachPairMovingMain_paid,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachComposite_moving_count_lower,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachComposite_moving_lowerDensity,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.exists_goldbachComposite_dimensionOne_constant,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.pairLayer_coordinate_eventually,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.pairLayer_floor_div,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.pairLayer_log_rounding,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachPair_product_bounds,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_lowerErrSum_le_prefixSum,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_mul_injective,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG6Pairs_sum_eq,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG7Pairs_sum_eq,
    `MathlibNt.SieveTheory.exists_actual_lowerRosser_jr_powerBudget,
    `MathlibNt.SieveTheory.continuousLowerFactor_eq_jr1965f,
    `MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.jr_errorEnvelope_le_exp,
    `MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965f_initial,
    `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G67_MOVING_CONE_PASS {seen.size}"


import MathlibNt.SieveTheory.LiLiuGoldbachG67PaidLower
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67_lowerRosser_paid
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_lowerRosser_paid,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_lowerErrSum_le_prefixSum,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_lowerRosser_finite,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachComposite_lowerRosser_finite,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_level_eventually,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachCompositeSieve_pair_abs_rem_le_prefix,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachCompositeSieve_rem_eq_standardPrimeAPError,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_prefix_doubleSum_le,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachOrderedPair_mul_injective,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG6Pairs_sum_eq,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG7Pairs_sum_eq,
    `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G67_PAID_CONE_PASS {seen.size}"


import MathlibNt.SieveTheory.LiLiuGoldbachWeightFourPaperConsumed
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_remainingFour_paperSplit_consumed_small_epsilon
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS5Closed_actual_split_first,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.fouvryG9S5Low_integral_upper,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS5HighFirstClosed_normalized_upper_integral,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_remainingFive_small_epsilon,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightRemainingFive_eq_remainingFour_sub_s5] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G9_ACTUAL_TOTAL_CONE_PASS {seen.size}"


import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughPaid
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG12_le_roughSum_add_normalized
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
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG12_roughQuotient_sandwich,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG12_eq_label_sum,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11_cell_sandwich,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12_exceptions_normalized,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachQuadruple_exceptions_normalized,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachQuadrupleDivisorFiber_card_le,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS5SquareCount_normalized,
    `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS4_finiteLoss_normalized] do
    unless seen.contains n do throwError "MISSING_PRODUCER {n}"
    logInfo m!"REACHABLE_PRODUCER {n}"
  for n in seen.toList do
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "FORBIDDEN_TRUST {n}"
  logInfo m!"G12_ROUGH_PAID_CONE_PASS {seen.size}"


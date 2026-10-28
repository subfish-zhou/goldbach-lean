import Goldbach.OnePlusOneNine
import Lean

/-! The retained final dependency check follows the quantitative proof and both
existence consequences. Literal statements and axiom whitelists are checked in
`Goldbach.OnePlusOneNineChecks`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`Goldbach.one_plus_one_nine_count, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_authorG11_numericLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_paperSplit_authorG11_consumed_small_epsilon, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_pair_lower, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_cross_upper, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_authorIntegral_direct, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67IntegralConstant_lower_certified, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67_piecewise_lower_certified, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target, `G12AnalyticCertificate.actual_le_target, `G12SharpOutput.original_total_integral, `G12SharpQuadrature.sharp_kernel_le_integral_eventually, `G12AuthorOutput.admitted_boundary_mesh]),
    (`Goldbach.one_plus_one_nine, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_gt_paper_0004, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19_pos_iff]),
    (`Goldbach.one_plus_one_nine_real, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_onePlusOneNine_nat_unconditional, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.oneNine_power_iff_source_exponent]),
    (`Goldbach.one_plus_one_nine_lower_bound, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_authorG11_numericLedger])]
  for (root, targets) in checks do
    let mut todo := [root]
    let mut seen : Std.HashSet Name := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        todo := ci.type.getUsedConstants.toList ++ todo
        if let some value := ci.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
    for target in targets do
      unless seen.contains target do
        throwError "MISSING_PRODUCER {root} -> {target}"
    for n in seen.toList do
      if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
        throwError "FORBIDDEN_TRUST {root} -> {n}"
    logInfo m!"FINAL_CONE_PASS {root} {seen.size}"

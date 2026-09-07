import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredPolynomial
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationFTC
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredError
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBranches
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBridge
import MathlibNt.SieveTheory.LiLiuGoldbachG67Constants
import MathlibNt.SieveTheory.LiLiuGoldbachG67Forms
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral1
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral2
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral3
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral4
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral5
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredEndpoint
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineUnconditional
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_onePlusOneNine_unconditional, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_pairIntegralLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ProductPrimeTotal_eq_active, `G12SharpOutput.original_total_integral, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorLowHigh_integral_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorLowHigh_kernel_terminal, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorSource_kernel_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorRough_kernel_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorRough_le_kernel, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_buchstab_le_factor, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_canonical_low_logQuotient, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_low_log_budget, `LiLiuGoldbachG12BuchstabMajorant.buchstab_le_561990, `LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383, `G12SharpQuadrature.sharp_kernel_le_integral_eventually, `G12SharpQuadrature.upper_integral_tendsto, `G12SharpQuadrature.upper_eventually_eq, `G12SharpQuadrature.kernel_mono, `G12SharpQuadrature.sharp_le_upper, `G12AuthorOutput.admitted_boundary_mesh, `G12SafeGridBudget.safe_union_normalized, `G12FineGrid.original_total_high_normalized, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpCrossIntegralLedger, `G67SumCoordinate.actual_constant_lower_piecewise, `G67SumCoordinate.elementaryIntegral_eq_piecewise, `G67SumCoordinate.elementaryIntegral_eq_oneDimensional, `G67SumCoordinate.rectangle_sum_formula, `G67SumCoordinate.rectangle_integral_piecewise, `G67SumCoordinate.square_integral_piecewise, `G67ElementaryIntegral.actual_constant_lower, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19_pos_iff, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.oneNine_power_iff_source_exponent, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachSharpElementaryMargin_lower_certified, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67_piecewise_lower_certified, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target, `G12AnalyticCertificate.actual_le_target, `G67CenteredEvaluation.centered_endpoint_bound, `G67CenteredEnvelope.polynomialIntegral_sub_errorBudget_le_piecewiseIntegral]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_lower_of_coefficient_lt, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachSharpElementaryMargin_lower_certified, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpPiecewiseLedger]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67_piecewise_lower_certified, [`G67CenteredEnvelope.L_error, `G67CenteredEnvelope.reciprocal_error, `G67CenteredEnvelope.product_error, `G67CenteredEnvelope.density_bridge, `G67CenteredEnvelope.integrate_loss, `G67CenteredEvaluation.density1_eq, `G67CenteredEvaluation.primitive1_deriv, `G67CenteredEvaluation.integral1_eq, `G67CenteredEvaluation.endpoint1_eq, `G67CenteredEvaluation.density2_eq, `G67CenteredEvaluation.primitive2_deriv, `G67CenteredEvaluation.integral2_eq, `G67CenteredEvaluation.endpoint2_eq, `G67CenteredEvaluation.density3_eq, `G67CenteredEvaluation.primitive3_deriv, `G67CenteredEvaluation.integral3_eq, `G67CenteredEvaluation.endpoint3_eq, `G67CenteredEvaluation.density4_eq, `G67CenteredEvaluation.primitive4_deriv, `G67CenteredEvaluation.integral4_eq, `G67CenteredEvaluation.endpoint4_eq, `G67CenteredEvaluation.density5_eq, `G67CenteredEvaluation.primitive5_deriv, `G67CenteredEvaluation.integral5_eq, `G67CenteredEvaluation.endpoint5_eq]),
    (`G12AnalyticCertificate.actual_le_target, [`G12AnalyticCertificate.sharp_le_rationalIntegral, `G12AnalyticCertificate.upperMass_eq_endpoints, `G12AnalyticCertificate.low_upper_integral_exact, `G12AnalyticCertificate.high_upper_integral_exact, `G12AnalyticCertificate.low_composed_deriv, `G12AnalyticCertificate.high_composed_deriv, `G12AnalyticCertificate.lowF_deriv, `G12AnalyticCertificate.highF_deriv, `G12AnalyticCertificate.low_division, `G12AnalyticCertificate.rationalIntegral_le_target, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.log_bounds])]
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
        if let some v := ci.value? (allowOpaque := true) then
          todo := v.getUsedConstants.toList ++ todo
    for n in targets do
      unless seen.contains n do throwError "MISSING_PRODUCER {root} -> {n}"
      logInfo m!"REACHABLE_PRODUCER {n}"
      logInfo m!"ROOT_PRODUCER {root} -> {n}"
    for n in seen.toList do
      if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
        throwError "FORBIDDEN_TRUST {root} -> {n}"
    logInfo m!"QUADRATURE_CONE_PASS {root} {seen.size}"

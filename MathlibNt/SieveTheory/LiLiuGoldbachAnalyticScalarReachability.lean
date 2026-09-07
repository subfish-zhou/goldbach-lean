import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticLogBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG67Analytic
import MathlibNt.SieveTheory.LiLiuGoldbachG67RationalLower
import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent
import MathlibNt.SieveTheory.LiLiuGoldbachSharpG9CertifiedLedger
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpG9CertifiedLedger, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpCrossIntegralLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_endpoints, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.endpoints_le_target, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_envelope, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.partial_fraction1, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.partial_fraction2, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.primitive1_deriv, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.primitive2_deriv, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.scaled_log_bounds, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.log_bounds]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.eventually_onePlusOneNine_source_of_two_integral_bounds, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.sharp_margin_lower_of_two_integral_bounds, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.eventually_onePlusOneNine_of_sharp_margin_pos, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.oneNine_power_iff_source_exponent]),
    (`G67Analytic.rationalIntegral_le_piecewise, [`G67Analytic.densityLower_le, `G67Analytic.integral_densityLower_le, `G67Analytic.logLower_le_log, `G67Analytic.profileLower_le]),
    (`G12AnalyticCertificate.sharp_le_rationalIntegral, [`G12AnalyticCertificate.density_le_upperDensity, `G12AnalyticCertificate.sharp_le_log_mul_upperMass, `G12AnalyticCertificate.external_log_le, `G12AnalyticCertificate.upperMass_nonneg, `G12SharpQuadrature.sharp_integral_split]),
    (`G12AnalyticCertificate.high_integral_exact, [`G12AnalyticCertificate.densityPrimitive_deriv])]
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

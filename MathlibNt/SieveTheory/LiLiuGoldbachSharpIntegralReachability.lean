import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpWeight
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpRough
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpIntegralSplit
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpQuadrature
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumDensity
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumFubini
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumWeightProperties
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Specialization
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Truncation
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpMassIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpOutputIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachSharpCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachSharpPiecewiseLedger
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpCrossIntegralLedger, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_pairIntegralLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ProductPrimeTotal_eq_active, `G12SharpOutput.original_total_integral, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorLowHigh_integral_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorLowHigh_kernel_terminal, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorSource_kernel_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorRough_kernel_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_authorRough_le_kernel, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_buchstab_le_factor, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_canonical_low_logQuotient, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.g12Sharp_low_log_budget, `LiLiuGoldbachG12BuchstabMajorant.buchstab_le_561990, `LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383, `G12SharpQuadrature.sharp_kernel_le_integral_eventually, `G12SharpQuadrature.upper_integral_tendsto, `G12SharpQuadrature.upper_eventually_eq, `G12SharpQuadrature.kernel_mono, `G12SharpQuadrature.sharp_le_upper, `G12AuthorOutput.admitted_boundary_mesh, `G12SafeGridBudget.safe_union_normalized, `G12FineGrid.original_total_high_normalized]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpPiecewiseLedger, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpCrossIntegralLedger, `G67SumCoordinate.actual_constant_lower_piecewise, `G67SumCoordinate.elementaryIntegral_eq_piecewise, `G67SumCoordinate.elementaryIntegral_eq_oneDimensional, `G67SumCoordinate.rectangle_sum_formula, `G67SumCoordinate.rectangle_integral_piecewise, `G67SumCoordinate.square_integral_piecewise, `G67ElementaryIntegral.actual_constant_lower]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.eventually_onePlusOneNine_of_sharp_margin_pos, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_sharpPiecewiseLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19_pos_iff]),
    (`G12SharpQuadrature.sharp_kernel_le_split_eventually, [`G12SharpQuadrature.sharp_kernel_le_integral_eventually, `G12SharpQuadrature.sharp_integral_split]),
    (`G12SharpQuadrature.sharp_outer_intervalIntegrable, [`G12SharpQuadrature.sharp_integrable, `G12SharpQuadrature.sharp_mul_integrable])]
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

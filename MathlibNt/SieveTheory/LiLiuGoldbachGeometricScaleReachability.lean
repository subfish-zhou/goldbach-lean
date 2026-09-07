import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScale
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleUniform
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleCoefficient
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScalePackage
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGrid
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridMother
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutputWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledC2Sieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalGridPartition
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`G12FlexibleWF.exists_scaled_rectangle_C2_sieve, [`G12LocalScale.uniform_source_package, `G12LocalScale.uniform_admission, `G12LocalScale.uniform_coefficient, `G12LocalScale.coefficient_of_logs, `G12LocalScale.logarithmic_geometry, `G12LocalScale.recover_T, `G12FlexibleWF.exists_rectangle_paid_C2_sieve, `G12FlexibleWF.signed_corrections_paid, `G12FlexibleWF.family_C2_bound, `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale]),
    (`G12FineGrid.original_total_grid_partition, [`G12LowHighOutput.original_total_partition, `G12LowHighOutput.original_filtered_count, `G12LowHighOutput.low_eq_mother, `G12FineGrid.refined_weighted_partition, `G12FineGrid.weighted_partition, `G12FineGrid.mother_partition, `G12FineGrid.mother_cover, `G12FineGrid.cell_disjoint, `G12FineGrid.local_weighted_partition, `G12FineGrid.safe_subset, `G12FlexibleRectangle.rectangle_subset_mother]),
    (`G12LowHighOutput.highAPWindow_eq_output_dvd, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12LinkedPrimeWindow_product_le]),
    (`G12LowHighOutput.highAPWindow_card_eq_inverse, [`G12LowHighOutput.highAPWindow_eq_sdiff, `G12LowHighOutput.mem_highWindow, `G12LowHighOutput.highCut_lt_iff]),
    (`G12FineGrid.short_dyadic, [`G12FineGrid.clipped_dyadic, `G12FineGrid.clipped_width]),
    (`G12FineGrid.boundaryCell_iff, [`G12FlexibleRectangle.local_boundary_iff])]
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

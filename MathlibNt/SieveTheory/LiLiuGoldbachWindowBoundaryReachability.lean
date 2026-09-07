import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundary
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundaryBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission
import MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12CutoffSlicePayment
import MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedC2Sieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundarySource
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalPaidGrid
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`G12FineGrid.exists_occupied_C2_sieve, [`G12FineGrid.uniform_occupied_source, `G12FineGrid.uniform_occupied_geometry, `G12FineGrid.occupied_long_lower, `G12FineGrid.occupied_atom_coordinates, `G12LocalScale.uniform_source_package, `G12FlexibleWF.exists_rectangle_paid_C2_sieve, `G12FlexibleWF.signed_corrections_paid, `G12FlexibleWF.family_C2_bound]),
    (`G12FineGrid.original_total_paid_grid, [`G12FineGrid.original_total_grid_partition, `G12FineGrid.cutoffOutput_normalized, `G12FineGrid.cutoffOutput_le, `G12FineGrid.cutoffSlice_card, `G12FineGrid.boundary_union_decomposition, `G12FineGrid.boundary_sum_le_branches]),
    (`G12FineGrid.boundarySource_common_log_saving, [`G12ClippedWindow.longMask_common_log_saving, `G12ClippedWindow.commonResidual_log_saving, `G12ClippedWindow.residual_squarefree, `Wu2004MeanValue.balanced_common_profile_primeCentered_natural, `G12FineGrid.boundaryCoefficient_eq_longMask]),
    (`G12FineGrid.boundary_source_mass_le, [`G12FineGrid.boundary_source_mass_split, `G12FineGrid.boundaryWindow_eq_source_filter, `G12FineGrid.boundaryCell_weighted_window, `G12ClippedWindow.clamp_window_eq_filter, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12MainMassBad_le]),
    (`G12FineGrid.boundarySourceBadMass_log_saving, [`G12FineGrid.boundarySourceBadMass_le, `G12RectangleGate.numerical_log_saving]),
    (`G12ClippedWindow.highCommonResidual_log_saving, [`G12ClippedWindow.highAPResidual_eq, `G12LowHighOutput.highAPWindow_card_eq_inverse, `G12ClippedWindow.commonResidual_log_saving, `G12ClippedWindow.highCommonResidual_eq_AP]),
    (`G12FineGrid.fixed_grid_productBoundary_integral_budget, [`G12FineGrid.bandMass_le_thinSum, `G12FineGrid.pairMass_le_bandMass, `G12FineGrid.product_bands_integral_budget, `G12FineGrid.short_ratio_of_rounding, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ThinSum_integral_budget]),
    (`G12FineGrid.boundary_output_le_source, [`G12FineGrid.boundary_sum_le_source, `G12FineGrid.boundaryWindow_eq_source_filter, `G12FineGrid.boundaryCell_eq_masked_window])]
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

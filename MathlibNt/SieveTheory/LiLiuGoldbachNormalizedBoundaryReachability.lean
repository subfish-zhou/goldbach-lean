import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedRosser
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedUniform
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutputSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughElementary
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12MovingEuler
import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalHighNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG12RawBoundarySmallMesh
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`G12FineGrid.original_total_high_normalized, [`G12FineGrid.original_total_grid_partition, `G12FineGrid.cutoffOutput_normalized, `G12ClippedWindow.physical_high_uniformEight, `G12ClippedWindow.physical_high_le_source, `G12ClippedWindow.highPrimeOutput_uniformEight, `G12RoughBoundary.fullBoundary_sum_cells]),
    (`G12ClippedWindow.actual_output_uniformEight, [`G12ClippedWindow.primeOutput_le_paidRosser, `G12ClippedWindow.output_upperErrSum_le, `G12ClippedWindow.siftedMass_le_rosserFactor, `G12ClippedWindow.outputSieve_rem, `G12ClippedWindow.output_sum, `G12ClippedWindow.primeOutput_le_sifted, `G12ClippedWindow.commonResidual_log_saving, `MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth]),
    (`G12MovingEuler.exists_scaled_rectangle_normalized, [`G12FlexibleWF.exists_scaled_rectangle_C2_sieve, `G12MovingEuler.normalized, `G12MovingEuler.error_eventually, `G12MovingEuler.euler_eq, `G12MovingEuler.euler_nonneg, `G12MovingEuler.mass_nonneg, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachB10PrimeProduct_log_le_liuSingularSeries]),
    (`G12FineGrid.exists_small_raw_boundary_mesh, [`G12RoughBoundary.exists_fixed_fullBoundary_constant, `G12RoughBoundary.fixed_grid_fullBoundary_budget, `G12RoughBoundary.fullBoundary_mass_le, `G12RoughBoundary.roughBoundary_mass_le_nearMass, `G12RoughBoundary.nearWindowMass_le_nearMass, `G12RoughBoundary.nearMass_uniform, `G12RoughBoundary.integer_band_reciprocal, `G12RoughBoundary.harmonic_eventually, `G12RoughBoundary.cofactor_eventually, `G12FineGrid.fixed_grid_productBoundary_integral_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12_rough_upper_buchstab])]
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

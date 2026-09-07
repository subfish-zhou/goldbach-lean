import MathlibNt.SieveTheory.LiLiuGoldbachG12BandOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12BandWindows
import MathlibNt.SieveTheory.LiLiuGoldbachG12BandMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundaryOutputBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LogBudgetTools
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidSafeCell
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidFixedGrid
import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorSourceBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorLowHigh
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorAssemblyTools
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorOutputIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachAuthorCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorBranchForm
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_authorCrossIntegralLedger, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_pairIntegralLedger, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ProductPrimeTotal_eq_active, `G12AuthorOutput.original_total_integral, `G12AuthorOutput.admitted_boundary_mesh, `G12AuthorOutput.safe_authorMass_le, `G12AuthorOutput.choose_loss, `G12BandOutput.fixed_grid_boundaryOutput_budget, `G12BandOutput.boundary_subset_cover, `G12BandOutput.sourceOutput_uniformEight, `G12BandOutput.sourceMass_budget, `G12BandOutput.bad_transport_eventually, `G12BandOutput.badMass_le, `G12SafeGridBudget.safe_union_normalized, `G12SafeGridBudget.safe_cell_paid, `G12SafeGridBudget.all_fees, `G12SafeGridBudget.correction_numerical, `G12SafeGridBudget.outside_numerical, `G12SafeGridBudget.indices_card_log, `G12SafeGridBudget.fixed_grid_normalized, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorLowHigh_integral_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorSource_split, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorSource_integral_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorBad_normalized_paid, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12WeightedGood_le_fullRough, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12GoodCross_sum_product_real, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12WeightedRough_le_kernel, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12_rough_upper_buchstab, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12PrimeKernel_author_le_integral_eventually, `G12ClippedWindow.physical_high_uniformEight, `G12FineGrid.original_total_high_normalized]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorIntegralConstant_eq_split, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12PrimeIntegral_author_split, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12PrimeIntegral_eq_single]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorLowMotherMass_eq_rational, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12AuthorPrimeWeight_eq_low_mother, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11AuthorWeight_eq_low, `G12LowRectangle.mother_linked_iff])]
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

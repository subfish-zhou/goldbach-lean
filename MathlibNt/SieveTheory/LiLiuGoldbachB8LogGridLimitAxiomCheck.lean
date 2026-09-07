import MathlibNt.SieveTheory.LiLiuGoldbachB8LogGridLimit

open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight

#check goldbachB8LogGridCell
#check goldbachB8LogGridRegion
#check goldbachB8LogSourceRegion
#check goldbachB8LogAmbientBox
#check goldbachB8LeftStrip
#check goldbachB8ObliqueStrip
#check measurableSet_goldbachB8LogGridCell
#check measurableSet_goldbachB8LogGridRegion
#check measurableSet_goldbachB8LogSourceRegion
#check measurableSet_goldbachB8LogAmbientBox
#check isCompact_goldbachB8LogAmbientBox
#check measurableSet_goldbachB8LeftStrip
#check measurableSet_goldbachB8ObliqueStrip
#check goldbachB8LogSourceRegion_section
#check goldbachB8LeftStrip_section
#check goldbachB8DiagonalStrip_section
#check goldbachB8ObliqueStrip_section
#check volume_goldbachB8LeftStrip
#check volume_goldbachB8ObliqueStrip
#check goldbachB8LogGridCell_pairwiseDisjoint
#check goldbachB8LogGridCell_subset_ambientBox
#check goldbachB8LogGridRegion_subset_ambientBox
#check goldbachB8LogSourceRegion_subset_ambientBox
#check goldbachB8LogAmbientBox_gap
#check goldbachB8LogGridRegion_excess_subset
#check goldbachB8MainIntegral
#check goldbachB8LogGridUpperIntegrand
#check goldbachB8LogIntegrand_eq
#check goldbachB8LogDensity_bounds
#check goldbachB8LogKernel_bounds
#check goldbachB8LogIntegrand_bounds
#check integrableOn_goldbachB8LogIntegrand
#check integrable_goldbachB8SourceIndicator
#check goldbachB8MainIntegral_eq_setIntegral
#check goldbachB8MainIntegral_nonneg
#check integrable_goldbachB8LogGridUpperIntegrand
#check goldbachB8LogGridUpperSum_eq_integral
#check goldbachB8LogGrid_kernel_variation
#check goldbachB8LogGridErrorConstant_pos
#check goldbachB8LogGridUpperSum_sub_mainIntegral_le
#check exists_goldbachB8LogGridUpperSum_le_mainIntegral_add

#print axioms goldbachB8LogGridCell
#print axioms goldbachB8LogGridRegion
#print axioms goldbachB8LogSourceRegion
#print axioms goldbachB8LogAmbientBox
#print axioms goldbachB8LeftStrip
#print axioms goldbachB8ObliqueStrip
#print axioms measurableSet_goldbachB8LogGridCell
#print axioms measurableSet_goldbachB8LogGridRegion
#print axioms measurableSet_goldbachB8LogSourceRegion
#print axioms measurableSet_goldbachB8LogAmbientBox
#print axioms isCompact_goldbachB8LogAmbientBox
#print axioms measurableSet_goldbachB8LeftStrip
#print axioms measurableSet_goldbachB8ObliqueStrip
#print axioms goldbachB8LogSourceRegion_section
#print axioms goldbachB8LeftStrip_section
#print axioms goldbachB8DiagonalStrip_section
#print axioms goldbachB8ObliqueStrip_section
#print axioms volume_goldbachB8LeftStrip
#print axioms volume_goldbachB8ObliqueStrip
#print axioms goldbachB8LogGridCell_pairwiseDisjoint
#print axioms goldbachB8LogGridCell_subset_ambientBox
#print axioms goldbachB8LogGridRegion_subset_ambientBox
#print axioms goldbachB8LogSourceRegion_subset_ambientBox
#print axioms goldbachB8LogAmbientBox_gap
#print axioms goldbachB8LogGridRegion_excess_subset
#print axioms goldbachB8MainIntegral
#print axioms goldbachB8LogGridUpperIntegrand
#print axioms goldbachB8LogIntegrand_eq
#print axioms goldbachB8LogDensity_bounds
#print axioms goldbachB8LogKernel_bounds
#print axioms goldbachB8LogIntegrand_bounds
#print axioms integrableOn_goldbachB8LogIntegrand
#print axioms integrable_goldbachB8SourceIndicator
#print axioms goldbachB8MainIntegral_eq_setIntegral
#print axioms goldbachB8MainIntegral_nonneg
#print axioms integrable_goldbachB8LogGridUpperIntegrand
#print axioms goldbachB8LogGridUpperSum_eq_integral
#print axioms goldbachB8LogGrid_kernel_variation
#print axioms goldbachB8LogGridErrorConstant_pos
#print axioms goldbachB8LogGridUpperSum_sub_mainIntegral_le
#print axioms exists_goldbachB8LogGridUpperSum_le_mainIntegral_add

#print goldbachB8LogGridCells
#print goldbachB8LogGridUpperSum
#print goldbachB8MainIntegral
#check goldbachB8Pairs_covered_by_logGrid
#check goldbachB8PairLogKernel_le_gridUpperSum_eventually
#check goldbachB8LogGridCell_cornerGap_ge
#check goldbachAffineDiagonalStrip_section
#check volume_goldbachB8DiagonalStrip
#check logarithmicRectangleMass_eq_setIntegral
#print axioms goldbachB8Pairs_covered_by_logGrid
#print axioms goldbachB8PairLogKernel_le_gridUpperSum_eventually
#print axioms goldbachB8LogGridCell_cornerGap_ge
#print axioms goldbachAffineDiagonalStrip_section
#print axioms volume_goldbachB8DiagonalStrip
#print axioms logarithmicRectangleMass_eq_setIntegral

example : goldbachB8MainIntegral =
    ∫ u in (3 / 11 : ℝ)..(1 / 3),
      ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v)) := rfl

example (u v : ℝ) : liuLogIntegrand (u, v) = 1 / (u * v * (1 - u - v)) :=
  goldbachB8LogIntegrand_eq u v

example : Integrable (goldbachB8LogSourceRegion.indicator liuLogIntegrand) :=
  integrable_goldbachB8SourceIndicator

example : 0 ≤ goldbachB8MainIntegral := goldbachB8MainIntegral_nonneg

example : (0 : ℝ) < 1000 := goldbachB8LogGridErrorConstant_pos

example (n : ℕ) (hn : 0 < n) :
    goldbachB8LogGridUpperSum n -
      (∫ u in (3 / 11 : ℝ)..(1 / 3),
        ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) ≤ 1000 / (n : ℝ) :=
  goldbachB8LogGridUpperSum_sub_mainIntegral_le n hn

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ goldbachB8LogGridUpperSum n ≤ goldbachB8MainIntegral + δ :=
  exists_goldbachB8LogGridUpperSum_le_mainIntegral_add δ hδ
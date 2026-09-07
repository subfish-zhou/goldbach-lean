import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit

open Filter Finset MeasureTheory Set
open scoped BigOperators Interval Topology
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open PrimeReciprocalLogRectangle

theorem goldbachB9LogGrid_publicAudit :
    0 ≤ goldbachB9MainIntegral ∧
    (∀ n : ℕ, 0 < n →
      goldbachB9LogGridUpperSum n - goldbachB9MainIntegral ≤ 10000 / (n : ℝ)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 0 < n ∧
      goldbachB9LogGridUpperSum n ≤ goldbachB9MainIntegral + δ) ∧
    (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB9PairLogKernel N ≤ goldbachB9MainIntegral + δ) :=
  ⟨goldbachB9MainIntegral_nonneg, goldbachB9LogGridUpperSum_sub_mainIntegral_le,
    exists_goldbachB9LogGridUpperSum_le_mainIntegral_add,
    goldbachB9PairLogKernel_le_mainIntegral_eventually⟩

#check instDecidablePropB9LogKernel
#check goldbachB9Pair_logGeometry
#check goldbachB9PrimeLogExponent_second_le_upper
#check goldbachB9OneSubPrimeLogExponent_pos
#check goldbachB9LogProd_eq
#check goldbachB9PairLogKernelTerm_eq
#check goldbachB9PairLogKernel_eq_logCoordinateSum
#check goldbachB9PairLogKernelTerm_nonneg
#check goldbachB9PairLogKernel_nonneg
#check goldbachB9PairsInLogRectangle
#check goldbachB9PairLogKernelRectangleContribution
#check goldbachB9PairsInLogRectangle_subset_primeLogRectanglePairs
#check goldbachB9PairLogKernelRectangleContribution_le
#print axioms instDecidablePropB9LogKernel
#print axioms goldbachB9Pair_logGeometry
#print axioms goldbachB9PrimeLogExponent_second_le_upper
#print axioms goldbachB9OneSubPrimeLogExponent_pos
#print axioms goldbachB9LogProd_eq
#print axioms goldbachB9PairLogKernelTerm_eq
#print axioms goldbachB9PairLogKernel_eq_logCoordinateSum
#print axioms goldbachB9PairLogKernelTerm_nonneg
#print axioms goldbachB9PairLogKernel_nonneg
#print axioms goldbachB9PairsInLogRectangle
#print axioms goldbachB9PairLogKernelRectangleContribution
#print axioms goldbachB9PairsInLogRectangle_subset_primeLogRectanglePairs
#print axioms goldbachB9PairLogKernelRectangleContribution_le

#check instDecidablePropB9LogGrid
#check goldbachB9AlphaGridWidth
#check goldbachB9BetaGridWidth
#check goldbachB9AlphaGridPoint
#check goldbachB9BetaGridPoint
#check goldbachB9AlphaGridStep
#check goldbachB9BetaGridStep
#check goldbachB9LogGridCells
#check goldbachB9LogGridMajorant
#check goldbachB9LogGridUpperSum
#check goldbachB9LogGridMajorant_eq_primeReciprocalProducts
#check mem_goldbachB9LogGridCells_iff
#check goldbachB9AlphaGridStep_pos
#check goldbachB9BetaGridStep_pos
#check goldbachB9AlphaGridPoint_eq_step
#check goldbachB9BetaGridPoint_eq_step
#check goldbachB9AlphaGridPoint_succ
#check goldbachB9BetaGridPoint_succ
#check goldbachB9AlphaGridPoint_pos
#check goldbachB9BetaGridPoint_pos
#check goldbachB9AlphaGridPoint_lt_succ
#check goldbachB9BetaGridPoint_lt_succ
#check goldbachB9AlphaGridPoint_mono
#check goldbachB9BetaGridPoint_mono
#check goldbachB9AlphaGridPoint_end
#check goldbachB9BetaGridPoint_end
#check goldbachB9AlphaGridPoint_succ_le_end
#check goldbachB9BetaGridPoint_succ_le_end
#check goldbachB9LogGridCell_cornerGap_ge
#check goldbachB9LogGridCell_cornerGap_pos
#check goldbachB9LogGridCell_upperCorner_lt_one
#check goldbachB9Pairs_covered_by_logGrid
#check goldbachB9PairLogKernel_le_logGridMajorant
#check tendsto_goldbachB9LogGridMajorant
#check goldbachB9PairLogKernel_le_gridUpperSum_eventually
#print axioms instDecidablePropB9LogGrid
#print axioms goldbachB9AlphaGridWidth
#print axioms goldbachB9BetaGridWidth
#print axioms goldbachB9AlphaGridPoint
#print axioms goldbachB9BetaGridPoint
#print axioms goldbachB9AlphaGridStep
#print axioms goldbachB9BetaGridStep
#print axioms goldbachB9LogGridCells
#print axioms goldbachB9LogGridMajorant
#print axioms goldbachB9LogGridUpperSum
#print axioms goldbachB9LogGridMajorant_eq_primeReciprocalProducts
#print axioms mem_goldbachB9LogGridCells_iff
#print axioms goldbachB9AlphaGridStep_pos
#print axioms goldbachB9BetaGridStep_pos
#print axioms goldbachB9AlphaGridPoint_eq_step
#print axioms goldbachB9BetaGridPoint_eq_step
#print axioms goldbachB9AlphaGridPoint_succ
#print axioms goldbachB9BetaGridPoint_succ
#print axioms goldbachB9AlphaGridPoint_pos
#print axioms goldbachB9BetaGridPoint_pos
#print axioms goldbachB9AlphaGridPoint_lt_succ
#print axioms goldbachB9BetaGridPoint_lt_succ
#print axioms goldbachB9AlphaGridPoint_mono
#print axioms goldbachB9BetaGridPoint_mono
#print axioms goldbachB9AlphaGridPoint_end
#print axioms goldbachB9BetaGridPoint_end
#print axioms goldbachB9AlphaGridPoint_succ_le_end
#print axioms goldbachB9BetaGridPoint_succ_le_end
#print axioms goldbachB9LogGridCell_cornerGap_ge
#print axioms goldbachB9LogGridCell_cornerGap_pos
#print axioms goldbachB9LogGridCell_upperCorner_lt_one
#print axioms goldbachB9Pairs_covered_by_logGrid
#print axioms goldbachB9PairLogKernel_le_logGridMajorant
#print axioms tendsto_goldbachB9LogGridMajorant
#print axioms goldbachB9PairLogKernel_le_gridUpperSum_eventually

#check goldbachB9LogGridCell
#check goldbachB9LogGridRegion
#check goldbachB9LogSourceRegion
#check goldbachB9LogAmbientBox
#check goldbachB9LeftStrip
#check goldbachB9BottomStrip
#check goldbachB9ObliqueStrip
#check measurableSet_goldbachB9LogGridCell
#check measurableSet_goldbachB9LogGridRegion
#check measurableSet_goldbachB9LogSourceRegion
#check measurableSet_goldbachB9LogAmbientBox
#check isCompact_goldbachB9LogAmbientBox
#check measurableSet_goldbachB9LeftStrip
#check measurableSet_goldbachB9BottomStrip
#check measurableSet_goldbachB9ObliqueStrip
#check goldbachB9LogSourceRegion_section
#check goldbachB9LeftStrip_section
#check goldbachB9BottomStrip_section
#check goldbachB9ObliqueStrip_section
#check volume_goldbachB9LeftStrip
#check volume_goldbachB9BottomStrip
#check volume_goldbachB9ObliqueStrip
#check goldbachB9LogGridCell_pairwiseDisjoint
#check goldbachB9LogGridCell_subset_ambientBox
#check goldbachB9LogGridRegion_subset_ambientBox
#check goldbachB9LogSourceRegion_subset_ambientBox
#check goldbachB9LogAmbientBox_gap
#check goldbachB9LogGridRegion_excess_subset
#print axioms goldbachB9LogGridCell
#print axioms goldbachB9LogGridRegion
#print axioms goldbachB9LogSourceRegion
#print axioms goldbachB9LogAmbientBox
#print axioms goldbachB9LeftStrip
#print axioms goldbachB9BottomStrip
#print axioms goldbachB9ObliqueStrip
#print axioms measurableSet_goldbachB9LogGridCell
#print axioms measurableSet_goldbachB9LogGridRegion
#print axioms measurableSet_goldbachB9LogSourceRegion
#print axioms measurableSet_goldbachB9LogAmbientBox
#print axioms isCompact_goldbachB9LogAmbientBox
#print axioms measurableSet_goldbachB9LeftStrip
#print axioms measurableSet_goldbachB9BottomStrip
#print axioms measurableSet_goldbachB9ObliqueStrip
#print axioms goldbachB9LogSourceRegion_section
#print axioms goldbachB9LeftStrip_section
#print axioms goldbachB9BottomStrip_section
#print axioms goldbachB9ObliqueStrip_section
#print axioms volume_goldbachB9LeftStrip
#print axioms volume_goldbachB9BottomStrip
#print axioms volume_goldbachB9ObliqueStrip
#print axioms goldbachB9LogGridCell_pairwiseDisjoint
#print axioms goldbachB9LogGridCell_subset_ambientBox
#print axioms goldbachB9LogGridRegion_subset_ambientBox
#print axioms goldbachB9LogSourceRegion_subset_ambientBox
#print axioms goldbachB9LogAmbientBox_gap
#print axioms goldbachB9LogGridRegion_excess_subset

#check goldbachB9MainIntegral
#check goldbachB9LogGridUpperIntegrand
#check goldbachB9LogIntegrand_eq
#check goldbachB9LogDensity_bounds
#check goldbachB9LogKernel_bounds
#check goldbachB9LogIntegrand_bounds
#check continuousOn_goldbachB9LogDensity
#check continuousOn_goldbachB9LogKernel
#check continuousOn_goldbachB9LogIntegrand
#check continuousOn_goldbachB9MainInner
#check intervalIntegrable_goldbachB9MainInner
#check integrableOn_goldbachB9LogDensity
#check integrableOn_goldbachB9LogIntegrand
#check integrable_goldbachB9SourceIndicator
#check goldbachB9MainIntegral_eq_iteratedSetIntegral
#check goldbachB9SourceIndicator_integral_section
#check intervalIntegrable_goldbachB9MainOuter
#check goldbachB9MainIntegral_eq_setIntegral
#check goldbachB9MainIntegral_nonneg
#check integrable_goldbachB9LogGridUpperIntegrand
#check goldbachB9LogGridUpperSum_eq_integral
#check goldbachB9LogGridUpperIntegrand_eq_of_mem
#check goldbachB9LogGridUpperIntegrand_eq_zero
#check goldbachB9LogGridUpperIntegrand_le
#check goldbachB9LogGrid_kernel_variation_step
#check goldbachB9LogGrid_kernel_error
#check goldbachB9LogGrid_kernel_variation
#check goldbachB9LogGridUpperIntegrand_le_integrand_add
#check goldbachB9LogGridErrorConstant_pos
#check goldbachB9LogGridUpperSum_sub_mainIntegral_le
#check exists_goldbachB9LogGridUpperSum_le_mainIntegral_add
#check goldbachB9PairLogKernel_le_mainIntegral_eventually
#check goldbachB9PairLogKernel_le_doubleIntegral_eventually
#check goldbachB9LogGrid_publicAudit
#print axioms goldbachB9MainIntegral
#print axioms goldbachB9LogGridUpperIntegrand
#print axioms goldbachB9LogIntegrand_eq
#print axioms goldbachB9LogDensity_bounds
#print axioms goldbachB9LogKernel_bounds
#print axioms goldbachB9LogIntegrand_bounds
#print axioms continuousOn_goldbachB9LogDensity
#print axioms continuousOn_goldbachB9LogKernel
#print axioms continuousOn_goldbachB9LogIntegrand
#print axioms continuousOn_goldbachB9MainInner
#print axioms intervalIntegrable_goldbachB9MainInner
#print axioms integrableOn_goldbachB9LogDensity
#print axioms integrableOn_goldbachB9LogIntegrand
#print axioms integrable_goldbachB9SourceIndicator
#print axioms goldbachB9MainIntegral_eq_iteratedSetIntegral
#print axioms goldbachB9SourceIndicator_integral_section
#print axioms intervalIntegrable_goldbachB9MainOuter
#print axioms goldbachB9MainIntegral_eq_setIntegral
#print axioms goldbachB9MainIntegral_nonneg
#print axioms integrable_goldbachB9LogGridUpperIntegrand
#print axioms goldbachB9LogGridUpperSum_eq_integral
#print axioms goldbachB9LogGridUpperIntegrand_eq_of_mem
#print axioms goldbachB9LogGridUpperIntegrand_eq_zero
#print axioms goldbachB9LogGridUpperIntegrand_le
#print axioms goldbachB9LogGrid_kernel_variation_step
#print axioms goldbachB9LogGrid_kernel_error
#print axioms goldbachB9LogGrid_kernel_variation
#print axioms goldbachB9LogGridUpperIntegrand_le_integrand_add
#print axioms goldbachB9LogGridErrorConstant_pos
#print axioms goldbachB9LogGridUpperSum_sub_mainIntegral_le
#print axioms exists_goldbachB9LogGridUpperSum_le_mainIntegral_add
#print axioms goldbachB9PairLogKernel_le_mainIntegral_eventually
#print axioms goldbachB9PairLogKernel_le_doubleIntegral_eventually
#print axioms goldbachB9LogGrid_publicAudit

#check goldbachB9PairLogKernel
#check mem_goldbachC10Pairs_iff
#check goldbachB8PairLogKernelTerm_le_rectangleCorner
#check exists_nat_cell
#check sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle
#check tendsto_weighted_sum_primeReciprocalLogRectangle
#check logarithmicRectangleMass_eq_setIntegral
#check primeReciprocalLogRectangle_eq_mul
#print axioms goldbachB9PairLogKernel
#print axioms mem_goldbachC10Pairs_iff
#print axioms goldbachB8PairLogKernelTerm_le_rectangleCorner
#print axioms exists_nat_cell
#print axioms sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle
#print axioms tendsto_weighted_sum_primeReciprocalLogRectangle
#print axioms logarithmicRectangleMass_eq_setIntegral
#print axioms primeReciprocalLogRectangle_eq_mul

#print goldbachB9PairLogKernel
#print goldbachB9MainIntegral
#print goldbachB9LogGridCells
#print goldbachB9LogGridMajorant
#print goldbachB9LogGridUpperSum
#print goldbachB9LogSourceRegion
#print primeReciprocalLogRectangle
#print logarithmicRectangleMass

example (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) :
    goldbachB9PairLogKernel N ≤ goldbachB9LogGridMajorant n N :=
  goldbachB9PairLogKernel_le_logGridMajorant n N hn hN

example (n N r : ℕ) (hn : 0 < n) (hN : 2 ≤ N)
    (hr : (r, r) ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ q ∈ goldbachB9LogGridCells n,
      LiuPairInLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) (r, r) :=
  goldbachB9Pairs_covered_by_logGrid n N hn hN hr

example (n : ℕ) (hn : 0 < n) :
    Tendsto (goldbachB9LogGridMajorant n) atTop (nhds (goldbachB9LogGridUpperSum n)) :=
  tendsto_goldbachB9LogGridMajorant n hn

example (n : ℕ) (hn : 0 < n) :
    goldbachB9LogGridUpperSum n -
      (∫ u in (4 / 53 : ℝ)..(1 / 3),
        ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) ≤
          10000 / (n : ℝ) :=
  goldbachB9LogGridUpperSum_sub_mainIntegral_le n hn

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
        1 / ((goldbachC10Prod rs : ℝ) *
          (1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ)))) ≤
        (∫ u in (4 / 53 : ℝ)..(1 / 3),
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) + δ :=
  goldbachB9PairLogKernel_le_mainIntegral_eventually δ hδ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
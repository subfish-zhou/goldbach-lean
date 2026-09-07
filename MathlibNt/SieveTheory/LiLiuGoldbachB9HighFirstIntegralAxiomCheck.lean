import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstIntegral

open MeasureTheory Set
open scoped BigOperators Interval
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

attribute [local instance] instDecidablePropB9HighFirstLogGrid

theorem goldbachB9HighFirstIntegral_publicAudit :
    0 ≤ goldbachB9HighMainIntegral ∧
    (∀ n : ℕ, 0 < n →
      goldbachB9HighLogGridUpperSum n - goldbachB9HighMainIntegral ≤ 10000 / (n : ℝ)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachK9High N ≤ goldbachB9HighMainIntegral + δ) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ε < (2 : ℝ) / 15 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
          (8 * goldbachB9HighMainIntegral + δ) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2)) :=
  ⟨goldbachB9HighMainIntegral_nonneg,
    goldbachB9HighLogGridUpperSum_sub_mainIntegral_le,
    goldbachK9High_le_mainIntegral_eventually,
    goldbachS5HighFirstClosed_normalized_upper_integral⟩

theorem goldbachK9High_expanded_integralAudit (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
        1 / (((rs.1 : ℝ) * rs.2) *
          (1 - Real.log ((rs.1 : ℝ) * rs.2) / Real.log (N : ℝ)))) ≤
        (∫ u in (1 / 10 : ℝ)..(1 / 3),
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) + δ := by
  simpa only [goldbachK9High, goldbachC10Prod, Nat.cast_mul, goldbachB9HighMainIntegral]
    using goldbachK9High_le_mainIntegral_eventually δ hδ

theorem goldbachS5HighFirstNormalized_inputAudit
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((8 + δ) *
          (∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
            1 / ((goldbachC10Prod rs : ℝ) *
              (1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ)))) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  simpa only [goldbachK9High] using
    goldbachS5HighFirstClosed_normalized_upper δ ε hδ hε hεu

theorem goldbachS5HighFirst_expanded_integralAudit
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (((∑ rs ∈ (goldbachS4Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))).filter
          (fun rs => (rs.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
            (N : ℝ) ^ (1 / 3 : ℝ) ≤ (rs.2 : ℝ)),
        literalH ((goldbachPrimeCarrier N ε).image (fun p => N - p))
          (N * rs.1) (rs.1 * rs.2) rs.2) : ℤ) : ℝ) ≤
        (8 * (∫ u in (1 / 10 : ℝ)..(1 / 3),
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  simpa only [goldbachS5Closed, goldbachDifferenceCarrier, goldbachB9HighMainIntegral]
    using goldbachS5HighFirstClosed_normalized_upper_integral δ ε hδ hε hεu

theorem goldbachB9HighFirstBoundary_gridAudit
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) (rs : ℕ × ℕ)
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)))
    (hboundary : (N : ℝ) ^ (1 / 10 : ℝ) = (rs.1 : ℝ)) :
    primeLogExponent N rs.1 = (1 / 10 : ℝ) ∧
      ∃ q ∈ goldbachB9HighLogGridCells n,
        LiuPairInLogRectangle N
          (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
          (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) rs := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  refine ⟨?_, goldbachB9HighPairs_covered_by_logGrid n N hn hN hrs⟩
  unfold primeLogExponent
  rw [← hboundary, Real.log_rpow hNp]
  exact mul_div_cancel_right₀ _ hlogN.ne'

#check instDecidablePropB9HighFirstLogGrid
#check goldbachB9HighLogGridCells
#check goldbachB9HighLogGridMajorant
#check goldbachB9HighLogGridUpperSum
#check goldbachB9HighLogGridCells_subset
#check mem_goldbachB9HighLogGridCells_iff
#check goldbachB9HighPairs_subset
#check goldbachB9HighPair_logGeometry
#check goldbachK9High_eq_logCoordinateSum
#check goldbachB9HighPairs_covered_by_logGrid
#check goldbachK9High_le_logGridMajorant
#check goldbachB9HighLogGridMajorant_eq_primeReciprocalProducts
#check tendsto_goldbachB9HighLogGridMajorant
#check goldbachK9High_le_gridUpperSum_eventually
#print axioms instDecidablePropB9HighFirstLogGrid
#print axioms goldbachB9HighLogGridCells
#print axioms goldbachB9HighLogGridMajorant
#print axioms goldbachB9HighLogGridUpperSum
#print axioms goldbachB9HighLogGridCells_subset
#print axioms mem_goldbachB9HighLogGridCells_iff
#print axioms goldbachB9HighPairs_subset
#print axioms goldbachB9HighPair_logGeometry
#print axioms goldbachK9High_eq_logCoordinateSum
#print axioms goldbachB9HighPairs_covered_by_logGrid
#print axioms goldbachK9High_le_logGridMajorant
#print axioms goldbachB9HighLogGridMajorant_eq_primeReciprocalProducts
#print axioms tendsto_goldbachB9HighLogGridMajorant
#print axioms goldbachK9High_le_gridUpperSum_eventually

#check goldbachB9HighLogGridRegion
#check goldbachB9HighLogSourceRegion
#check goldbachB9HighLeftStrip
#check goldbachB9HighBottomStrip
#check goldbachB9HighObliqueStrip
#check goldbachB9HighLogGridUpperIntegrand
#check measurableSet_goldbachB9HighLogGridRegion
#check measurableSet_goldbachB9HighLogSourceRegion
#check measurableSet_goldbachB9HighLeftStrip
#check measurableSet_goldbachB9HighBottomStrip
#check measurableSet_goldbachB9HighObliqueStrip
#check goldbachB9HighLogGridRegion_subset_full
#check goldbachB9HighLogGridRegion_subset_ambientBox
#check goldbachB9HighLogSourceRegion_subset_ambientBox
#check goldbachB9HighLogSourceRegion_subset_gridRegion
#check goldbachB9HighLogGridRegion_excess_subset
#check volume_goldbachB9HighLeftStrip
#check volume_goldbachB9HighBottomStrip
#check goldbachB9HighObliqueStrip_section
#check volume_goldbachB9HighObliqueStrip
#check integrable_goldbachB9HighSourceIndicator
#check integrable_goldbachB9HighLogGridUpperIntegrand
#check goldbachB9HighLogGridUpperSum_eq_integral
#check goldbachB9HighLogGridUpperIntegrand_eq_of_mem
#check goldbachB9HighLogGridUpperIntegrand_eq_zero
#check goldbachB9HighLogGridUpperIntegrand_eq_full_of_mem
#check goldbachB9HighLogGridUpperIntegrand_le
#check goldbachB9HighLogGridUpperIntegrand_le_integrand_add
#print axioms goldbachB9HighLogGridRegion
#print axioms goldbachB9HighLogSourceRegion
#print axioms goldbachB9HighLeftStrip
#print axioms goldbachB9HighBottomStrip
#print axioms goldbachB9HighObliqueStrip
#print axioms goldbachB9HighLogGridUpperIntegrand
#print axioms measurableSet_goldbachB9HighLogGridRegion
#print axioms measurableSet_goldbachB9HighLogSourceRegion
#print axioms measurableSet_goldbachB9HighLeftStrip
#print axioms measurableSet_goldbachB9HighBottomStrip
#print axioms measurableSet_goldbachB9HighObliqueStrip
#print axioms goldbachB9HighLogGridRegion_subset_full
#print axioms goldbachB9HighLogGridRegion_subset_ambientBox
#print axioms goldbachB9HighLogSourceRegion_subset_ambientBox
#print axioms goldbachB9HighLogSourceRegion_subset_gridRegion
#print axioms goldbachB9HighLogGridRegion_excess_subset
#print axioms volume_goldbachB9HighLeftStrip
#print axioms volume_goldbachB9HighBottomStrip
#print axioms goldbachB9HighObliqueStrip_section
#print axioms volume_goldbachB9HighObliqueStrip
#print axioms integrable_goldbachB9HighSourceIndicator
#print axioms integrable_goldbachB9HighLogGridUpperIntegrand
#print axioms goldbachB9HighLogGridUpperSum_eq_integral
#print axioms goldbachB9HighLogGridUpperIntegrand_eq_of_mem
#print axioms goldbachB9HighLogGridUpperIntegrand_eq_zero
#print axioms goldbachB9HighLogGridUpperIntegrand_eq_full_of_mem
#print axioms goldbachB9HighLogGridUpperIntegrand_le
#print axioms goldbachB9HighLogGridUpperIntegrand_le_integrand_add

#check goldbachB9HighMainIntegral
#check intervalIntegrable_goldbachB9HighMainInner
#check goldbachB9HighMainIntegral_eq_iteratedSetIntegral
#check goldbachB9HighSourceIndicator_integral_section
#check intervalIntegrable_goldbachB9HighMainOuter
#check goldbachB9HighMainIntegral_eq_setIntegral
#check goldbachB9HighMainIntegral_nonneg
#check goldbachB9HighLogGridErrorConstant_pos
#check goldbachB9HighLogGridUpperSum_sub_mainIntegral_le
#check exists_goldbachB9HighLogGridUpperSum_le_mainIntegral_add
#check goldbachK9High_le_mainIntegral_eventually
#check goldbachK9High_le_doubleIntegral_eventually
#check goldbachS5HighFirstClosed_normalized_upper_integral
#print axioms goldbachB9HighMainIntegral
#print axioms intervalIntegrable_goldbachB9HighMainInner
#print axioms goldbachB9HighMainIntegral_eq_iteratedSetIntegral
#print axioms goldbachB9HighSourceIndicator_integral_section
#print axioms intervalIntegrable_goldbachB9HighMainOuter
#print axioms goldbachB9HighMainIntegral_eq_setIntegral
#print axioms goldbachB9HighMainIntegral_nonneg
#print axioms goldbachB9HighLogGridErrorConstant_pos
#print axioms goldbachB9HighLogGridUpperSum_sub_mainIntegral_le
#print axioms exists_goldbachB9HighLogGridUpperSum_le_mainIntegral_add
#print axioms goldbachK9High_le_mainIntegral_eventually
#print axioms goldbachK9High_le_doubleIntegral_eventually
#print axioms goldbachS5HighFirstClosed_normalized_upper_integral

#check goldbachB9HighFirstIntegral_publicAudit
#check goldbachK9High_expanded_integralAudit
#check goldbachS5HighFirstNormalized_inputAudit
#check goldbachS5HighFirst_expanded_integralAudit
#check goldbachB9HighFirstBoundary_gridAudit
#print axioms goldbachB9HighFirstIntegral_publicAudit
#print axioms goldbachK9High_expanded_integralAudit
#print axioms goldbachS5HighFirstNormalized_inputAudit
#print axioms goldbachS5HighFirst_expanded_integralAudit
#print axioms goldbachB9HighFirstBoundary_gridAudit

#check goldbachK9High
#check goldbachK9High_nonneg
#check goldbachC10HighFirstPairs_eq_filter
#check goldbachS5HighFirstClosed_eq_card
#check goldbachS5HighFirstClosed_normalized_upper
#check goldbachB9Pairs_covered_by_logGrid
#check goldbachB9PairLogKernelTerm_eq
#check goldbachB9PairLogKernelTerm_nonneg
#check goldbachB9PairLogKernelRectangleContribution_le
#check PrimeReciprocalLogRectangle.tendsto_weighted_sum_primeReciprocalLogRectangle
#check logarithmicRectangleMass_eq_setIntegral
#check goldbachB9LogGridCell_pairwiseDisjoint
#check goldbachB9LogGridCell_subset_ambientBox
#check integrableOn_goldbachB9LogDensity
#check integrableOn_goldbachB9LogIntegrand
#check goldbachB9LogDensity_bounds
#check goldbachB9LogIntegrand_bounds
#check goldbachB9LogGrid_kernel_variation
#check goldbachB9LogGridUpperIntegrand_le
#check goldbachB9LogGridUpperIntegrand_le_integrand_add
#print axioms goldbachK9High
#print axioms goldbachK9High_nonneg
#print axioms goldbachC10HighFirstPairs_eq_filter
#print axioms goldbachS5HighFirstClosed_eq_card
#print axioms goldbachS5HighFirstClosed_normalized_upper
#print axioms goldbachB9Pairs_covered_by_logGrid
#print axioms goldbachB9PairLogKernelTerm_eq
#print axioms goldbachB9PairLogKernelTerm_nonneg
#print axioms goldbachB9PairLogKernelRectangleContribution_le
#print axioms PrimeReciprocalLogRectangle.tendsto_weighted_sum_primeReciprocalLogRectangle
#print axioms logarithmicRectangleMass_eq_setIntegral
#print axioms goldbachB9LogGridCell_pairwiseDisjoint
#print axioms goldbachB9LogGridCell_subset_ambientBox
#print axioms integrableOn_goldbachB9LogDensity
#print axioms integrableOn_goldbachB9LogIntegrand
#print axioms goldbachB9LogDensity_bounds
#print axioms goldbachB9LogIntegrand_bounds
#print axioms goldbachB9LogGrid_kernel_variation
#print axioms goldbachB9LogGridUpperIntegrand_le
#print axioms goldbachB9LogGridUpperIntegrand_le_integrand_add

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
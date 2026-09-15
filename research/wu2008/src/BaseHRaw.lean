import MathlibNt.Wu2008DoubleSieve.BaseLowerCounts

namespace Wu2008DoubleSieve.BaseLowerCounts
open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The actual limiting lower improvement is retained in the zero-depth source. -/
theorem fixed_delta_li_with_h {δ κ η : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hs : 1 ≤ (1/2-δ)/κ) (hs10 : (1/2-δ)/κ ≤ 10)
    (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (wuLowerCoefficient ((1/2-δ)/κ) + wuImprovementLimit false δ ((1/2-δ)/κ) - η) *
        (4 * logarithmicIntegral N * wuSingularSeries N / ((1/2-δ)*log N)) ≤
      (sieveCount N 1 N ((N : ℝ)^κ) : ℝ) := by
  obtain ⟨T, hT⟩ := wuImprovementLimit_sub_mem false 0 hδ hδhi hs hs10 hη
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_right _ _).trans hN
  have h := hT N hNT hN4 he 0 (1 + log (N : ℝ)^(-4 : ℝ)) Fin.elim0
    (wuSourceBox_zero_depth 1 N δ hN4)
  change (wuLowerCoefficient ((1/2-δ)/κ) + (wuImprovementLimit false δ ((1/2-δ)/κ) - η)) * _ ≤ _ at h
  rw [boxTheta_zero_depth, phi_zero, cutoff_exact (by omega) hδhi,
    log_rpow (by positivity : (0 : ℝ) < N)] at h
  simpa only [sub_eq_add_neg, add_assoc] using h


end Wu2008DoubleSieve.BaseLowerCounts

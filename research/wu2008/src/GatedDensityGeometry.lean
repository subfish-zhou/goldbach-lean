import FiniteEndpointJ

namespace GatedDensityPayment
open Wu2008DoubleSieve MotherPair Real Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

theorem q_bounds {p : SecondFunctionalParameters} (hp : AnalyticParameters p) (j : Term) :
    0 ≤ 1-upperQ p j ∧ 0 ≤ 1-lowerQ p j := by
  have h1 : 1 ≤ p.kappa3 := hp.mother.one_le_s.trans hp.mother.s_le_kappa3
  have h2 : 1 ≤ p.kappa2 := h1.trans hp.mother.kappa3_lt_kappa2.le
  have h3 : 1 ≤ p.kappa1 := h2.trans hp.mother.kappa2_lt_kappa1.le
  have hS : 1 ≤ p.S := h3.trans hp.mother.kappa1_le_S
  have hreciprocal : ∀ {x : ℝ}, 1 ≤ x → 0 ≤ 1-1/x := by
    intro x hx
    have := (div_le_one (by linarith : 0<x)).mpr hx
    linarith
  cases j <;> simp only [upperQ,lowerQ] <;> exact ⟨hreciprocal (by assumption),hreciprocal (by assumption)⟩

theorem lower_antitone {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) :
    feedbackLower p j v ≤ feedbackLower p j a := by
  have hS : 0 ≤ p.S := by linarith [hp.three_le_S]
  have hd := div_le_div_of_nonneg_right hav hS
  have hq := (q_bounds hp j).1
  have hhreciprocal := div_le_div_of_nonneg_left hq (by linarith : 0<a+1)
    (by linarith : a+1 ≤ v+1)
  have hhalf := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by linarith : 0<2*(a+1)) (by linarith : 2*(a+1) ≤ 2*(v+1))
  cases j <;> simp only [feedbackLower] at *
  all_goals apply max_le_max_left
  all_goals apply max_le_max
  all_goals first | exact hhreciprocal | exact hhalf | linarith

/-- Endpoint minimum enclosure for the original upper boundary; no extra partition. -/
theorem upper_endpoint_min {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a b v : ℝ} (ha : 1 ≤ a) (hv : v ∈ Icc a b) :
    min (feedbackUpper p j a) (feedbackUpper p j b) ≤ feedbackUpper p j v := by
  have hS : 0 ≤ p.S := by linarith [hp.three_le_S]
  have had := div_le_div_of_nonneg_right hv.1 hS
  have hbd := div_le_div_of_nonneg_right hv.2 hS
  have hq := (q_bounds hp j).2
  have hr := div_le_div_of_nonneg_left hq (by linarith [hv.1] : 0<v+1)
    (by linarith [hv.2] : v+1 ≤ b+1)
  have hr2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by linarith [hv.1] : 0<v+2) (by linarith [hv.2] : v+2 ≤ b+2)
  cases j <;> simp only [feedbackUpper] at *
  all_goals apply le_min
  all_goals first
    | exact (min_le_left _ _).trans (min_le_left _ _)
    | skip
  all_goals apply le_min
  all_goals first
    | exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_left _ _).trans (by first | exact hr | linarith)))
    | skip
  all_goals first
    | exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans hr2))
    | skip
  all_goals apply le_min
  all_goals first
    | exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_left _ _).trans (by linarith))))
    | exact (min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans had)))

end
end GatedDensityPayment

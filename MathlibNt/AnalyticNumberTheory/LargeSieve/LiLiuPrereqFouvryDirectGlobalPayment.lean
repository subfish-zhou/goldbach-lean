import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalParameters

/-! Uniform scalar payment for the three actual normalized monomials.
This module selects no analytic hypotheses and does not assert C.2. -/
noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


/-- One internal exponent is fixed before all varying data. It simultaneously
pays the four arithmetic exponents and the remaining analytic losses. -/
theorem c2_direct_common_exponent {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η < ε ∧ 416*η ≤ ε/4 := by
  obtain ⟨η, hη, hηε, hpay⟩ := c2_direct_loss_allowance hε (by norm_num : (0 : ℝ) ≤ 416)
  refine ⟨min η 1, lt_min hη (by norm_num), min_le_right _ _,
    lt_of_le_of_lt (min_le_left _ _) hηε, ?_⟩
  exact (mul_le_mul_of_nonneg_left (min_le_left η 1) (by norm_num : (0 : ℝ) ≤ 416)).trans hpay

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

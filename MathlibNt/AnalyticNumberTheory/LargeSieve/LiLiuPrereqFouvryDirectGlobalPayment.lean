import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalParameters

/-! Uniform scalar payment for the three actual normalized monomials.
This module selects no analytic hypotheses and does not assert C.2. -/
noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem c2_direct_zero_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10)
    (hL : L ≤ ε / 4) :
    x ^ L * (x ^ c2RExponent ν ε * Real.sqrt (x ^ c2SExponent ν ε) /
      Real.sqrt x) ≤ x ^ (-(ε / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le,
    ← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have h := (c2_direct_normalized_margins hε hεν hν hL).1
  linarith

theorem c2_direct_main_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10)
    (hL : L ≤ ε / 4) :
    x ^ L * ((x ^ ν) ^ (5 / 4 : ℝ) *
      (x ^ c2RExponent ν ε) ^ (7 / 4 : ℝ) *
      (x ^ c2SExponent ν ε) ^ 2 / x) ≤ x ^ (-(ε / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le,
    ← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
  conv_lhs => arg 2; arg 2; rw [← Real.rpow_one x]
  rw [← Real.rpow_sub hx0, ← Real.rpow_add hx0]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have h := (c2_direct_normalized_margins hε hεν hν hL).2.1
  norm_num
  linarith

theorem c2_direct_secondary_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10)
    (hL : L ≤ ε / 4) :
    x ^ L * (x ^ ν * (x ^ c2RExponent ν ε) ^ (3 / 4 : ℝ) *
      (x ^ c2SExponent ν ε) ^ (3 / 2 : ℝ) / Real.sqrt x) ≤
        x ^ (-(ε / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le,
    ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0,
    ← Real.rpow_add hx0]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have h := (c2_direct_normalized_margins hε hεν hν hL).2.2
  linarith

/-- One internal exponent is fixed before all varying data. It simultaneously
pays the four arithmetic exponents and the remaining analytic losses. -/
theorem c2_direct_common_exponent {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η < ε ∧ 416*η ≤ ε/4 := by
  obtain ⟨η, hη, hηε, hpay⟩ := c2_direct_loss_allowance hε (by norm_num : (0 : ℝ) ≤ 416)
  refine ⟨min η 1, lt_min hη (by norm_num), min_le_right _ _,
    lt_of_le_of_lt (min_le_left _ _) hηε, ?_⟩
  exact (mul_le_mul_of_nonneg_left (min_le_left η 1) (by norm_num : (0 : ℝ) ≤ 416)).trans hpay

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

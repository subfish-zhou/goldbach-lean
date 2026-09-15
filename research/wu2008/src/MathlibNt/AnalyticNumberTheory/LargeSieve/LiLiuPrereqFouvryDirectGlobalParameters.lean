import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryParameters

/-!
# Uniform exponent margins for the existing C.2 split

Reuse the existing factor exponents, including the S = 1 branch. These
are scalar payment lemmas, not an assertion of the distribution estimate.
Actual coefficient, carrier and local-frequency estimates are separate.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The secondary normalized exponent fits the existing split uniformly. -/
theorem c2_direct_secondary_exponent_margin {ν ε : ℝ}
    (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10) :
    ν + 3 * c2RExponent ν ε / 4 + 3 * c2SExponent ν ε / 2 - 1 / 2 ≤
      -(3 * ε / 4) := by
  unfold c2RExponent c2SExponent
  by_cases hs : 0 ≤ (1 - 10 * ν) / 9 - ε / 2
  · rw [max_eq_right hs]
    linarith
  · rw [max_eq_left (by linarith : (1 - 10 * ν) / 9 - ε / 2 ≤ 0)]
    linarith

/-- A common loss allowance, without changing the already used R/S split. -/
theorem c2_direct_normalized_margins {ν ε L : ℝ}
    (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10) (hL : L ≤ ε / 4) :
    c2RExponent ν ε + c2SExponent ν ε / 2 - 1 / 2 + L ≤ -(ε / 2) ∧
    5 * ν / 4 + 7 * c2RExponent ν ε / 4 + 2 * c2SExponent ν ε - 1 + L ≤
      -(ε / 2) ∧
    ν + 3 * c2RExponent ν ε / 4 + 3 * c2SExponent ν ε / 2 - 1 / 2 + L ≤
      -(ε / 2) := by
  obtain ⟨_, _, _, hfirst, hsecond⟩ := c2_exponent_bounds hε hεν hν
  have hthird := c2_direct_secondary_exponent_margin hε hεν hν
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Choose an internal exponent after a fixed loss multiplier, before data. -/
theorem c2_direct_loss_allowance {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ C * η ≤ ε / 4 := by
  have hd : 0 < 4 * (C + 1) := by positivity
  refine ⟨ε / (4 * (C + 1)), div_pos hε hd, ?_, ?_⟩
  · have hsmall : ε / (4 * (C + 1)) ≤ ε / 4 := by
      apply (div_le_iff₀ hd).2
      nlinarith [mul_nonneg hε.le hC]
    linarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

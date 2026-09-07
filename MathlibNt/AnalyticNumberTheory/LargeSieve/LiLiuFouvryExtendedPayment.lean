import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryExtendedParameters

/-! Uniform scalar payment for the three actual normalized monomials.
This module selects no analytic hypotheses and does not assert C.2. -/
noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem c2_extended_zero_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10)
    (hL : L ≤ ε / 4) :
    x ^ L * (x ^ c2RExponent ν ε * Real.sqrt (x ^ c2SExponent ν ε) /
      Real.sqrt x) ≤ x ^ (-(ε / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le,
    ← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have h := (c2_extended_normalized_margins hε hεν hν hL).1
  linarith

theorem c2_extended_main_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10)
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
  have h := (c2_extended_normalized_margins hε hεν hν hL).2.1
  norm_num
  linarith

theorem c2_extended_secondary_monomial {x ν ε L : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10)
    (hL : L ≤ ε / 4) :
    x ^ L * (x ^ ν * (x ^ c2RExponent ν ε) ^ (3 / 4 : ℝ) *
      (x ^ c2SExponent ν ε) ^ (3 / 2 : ℝ) / Real.sqrt x) ≤
        x ^ (-(ε / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le,
    ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0,
    ← Real.rpow_add hx0]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have h := (c2_extended_normalized_margins hε hεν hν hL).2.2
  linarith


theorem c2_extended_factor_levels {x ν ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10) :
    let R := x ^ c2RExponent ν ε
    let S := x ^ c2SExponent ν ε
    1 ≤ R ∧ 1 ≤ S ∧ R * S = x ^ ((5 - 5 * ν) / 9 - ε) ∧
      max (R ^ 2 * S) ((x ^ ν) ^ (5 / 4 : ℝ) * R ^ (7 / 4 : ℝ) * S ^ 2) ≤
        x ^ (1 - 3 * ε / 2) := by
  dsimp only
  obtain ⟨hr, hs, hsum, hfirst, hsecond⟩ := c2_extended_exponent_bounds hε hεν hν
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  refine ⟨Real.one_le_rpow hx hr, Real.one_le_rpow hx hs, ?_, max_le ?_ ?_⟩
  · rw [← Real.rpow_add hxpos, hsum]
  · rw [← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith
  · rw [← Real.rpow_mul hxpos.le, ← Real.rpow_mul hxpos.le,
      ← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

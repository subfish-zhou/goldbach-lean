import MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensityBounds

/-! # Uniform scalar budgets for the unbounded dimension constant -/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity

theorem dimension_quotient_le_target {ε x K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 1 ≤ x) (hK : 0 ≤ K) :
    K / x ≤ (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * x ^ (-(1 / 3 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hi : x⁻¹ ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have he : K ≤ Real.exp (6 * K + 2) := by
    linarith [Real.add_one_le_exp (6 * K + 2)]
  have heps : 1 ≤ (ε ^ 8)⁻¹ :=
    (one_le_inv₀ (pow_pos hε 8)).mpr (pow_le_one₀ hε.le hε1)
  have hE : Real.exp (6 * K + 2) ≤ (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heps (Real.exp_pos _).le
  rw [div_eq_mul_inv]
  exact (mul_le_mul he hi (inv_nonneg.mpr hx0.le) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hx0.le _))

/-- Large `K` is paid directly from the bounded aggregate, without multiplying
the internal analytic error by an unbounded Euler ratio. -/
theorem large_dimension_square_le_target {a ε x y K : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : 1 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) (hxK : x ≤ K) :
    (y / a * (1 + K / a)) ^ 2 ≤
      ((1 / a) * (1 + 1 / a)) ^ 2 *
        ((ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * x ^ (-(1 / 3 : ℝ))) := by
  let b := (1 / a) * (1 + 1 / a)
  let r := x ^ (-(1 / 3 : ℝ))
  have hx0 : 0 < x := by linarith
  have hK : 0 ≤ K := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr : 0 ≤ r := Real.rpow_nonneg hx0.le _
  have hi : x⁻¹ ≤ r := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hunit : 1 ≤ (1 + K) * r := by
    have h := mul_le_mul_of_nonneg_left hi hx0.le
    rw [mul_inv_cancel₀ hx0.ne'] at h
    have h' := mul_le_mul_of_nonneg_right (show x ≤ 1 + K by linarith) hr
    exact h.trans h'
  have hya : y / a ≤ (1 + K) / a :=
    div_le_div_of_nonneg_right (by linarith) ha.le
  have hka : 1 + K / a ≤ (1 + 1 / a) * (1 + K) := by
    have hia : 0 ≤ 1 / a := by positivity
    simp only [div_eq_mul_inv, one_mul] at hia ⊢
    nlinarith
  have hm : y / a * (1 + K / a) ≤ b * (1 + K) ^ 2 := by
    have h := mul_le_mul hya hka (by positivity) (by positivity)
    exact h.trans_eq (by dsimp [b]; ring)
  have hm2 : (y / a * (1 + K / a)) ^ 2 ≤ b ^ 2 * (1 + K) ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ y / a * (1 + K / a)) hm 2
    exact h.trans_eq (by ring)
  have he : 1 + K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have he5 : (1 + K) ^ 5 ≤ Real.exp (5 * K) := by
    calc
      _ ≤ Real.exp K ^ 5 := pow_le_pow_left₀ (by positivity) he 5
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hexp : Real.exp (5 * K) ≤ Real.exp (6 * K + 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have heps : 1 ≤ (ε ^ 8)⁻¹ :=
    (one_le_inv₀ (pow_pos hε 8)).mpr (pow_le_one₀ hε.le hε1)
  have hH : (1 + K) ^ 5 ≤ (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) := by
    apply (he5.trans hexp).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heps (Real.exp_pos _).le
  calc
    _ ≤ b ^ 2 * (1 + K) ^ 4 := hm2
    _ ≤ b ^ 2 * (1 + K) ^ 5 * r := by
      have h := mul_le_mul_of_nonneg_left hunit
        (show 0 ≤ b ^ 2 * (1 + K) ^ 4 by positivity)
      nlinarith
    _ ≤ b ^ 2 * ((ε ^ 8)⁻¹ * Real.exp (6 * K + 2)) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (sq_nonneg b)) hr
    _ = _ := by dsimp [b, r]; ring

#print axioms dimension_quotient_le_target
#print axioms large_dimension_square_le_target

end MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity

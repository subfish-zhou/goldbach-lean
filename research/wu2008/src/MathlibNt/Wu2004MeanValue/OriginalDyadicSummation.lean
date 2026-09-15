import MathlibNt.Wu2004MeanValue.OriginalDyadicGeometry

/-! Uniform logarithmic comparison and geometric summation for all retained
dyadic scales. Constants are independent of `η`, the terminal index, and `x`. -/

namespace Wu2004MeanValue

open Filter

noncomputable section

theorem log_scale_lower_of_sqrt {x H : ℝ} (hx : 16 ≤ x)
    (hH : Real.sqrt x / 2 ≤ H) :
    Real.log x / 4 ≤ Real.log H := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlog := Real.log_le_log (by positivity : 0 < Real.sqrt x / 2) hH
  rw [Real.log_div hs.ne' (by norm_num), Real.log_sqrt hx0.le] at hlog
  have hl16 : 4 * Real.log 2 ≤ Real.log x := by
    calc
      4 * Real.log 2 = Real.log ((2 : ℝ) ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log x := Real.log_le_log (by norm_num) (by norm_num; exact hx)
  linarith

theorem dyadicScale_log_lower {η x : ℝ} (hη : 0 < η) (hx : 16 ≤ x)
    (hfirst : Real.sqrt x ≤ dyadicScale η x 0) {j : ℕ}
    (hj : j ≤ dyadicLast η x) :
    Real.log x / 4 ≤ Real.log (dyadicScale η x j) :=
  log_scale_lower_of_sqrt hx (dyadicScale_retained_lower hη (by linarith) hfirst hj)

theorem scale_div_log_sq_le {x H : ℝ} (hx : 16 ≤ x)
    (hH : Real.sqrt x / 2 ≤ H) :
    H / Real.log H ^ 2 ≤ 16 * H / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity : 0 < Real.sqrt x / 2) hH
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl := log_scale_lower_of_sqrt hx hH
  have hlH : 0 < Real.log H := by linarith
  have hsq : Real.log x ^ 2 ≤ 16 * Real.log H ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ Real.log x / 4) hl
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hlH) (sq_pos_of_pos hlx)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hH0.le]

theorem sum_dyadicScale_div_log_sq_le {η x : ℝ} (hη : 0 < η) (hx : 16 ≤ x)
    (hfirst : Real.sqrt x ≤ dyadicScale η x 0) :
    (∑ j ∈ Finset.range (dyadicLast η x + 1),
      dyadicScale η x j / Real.log (dyadicScale η x j) ^ 2) ≤
        16 * η * x / Real.log x ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (dyadicLast η x + 1),
        16 * dyadicScale η x j / Real.log x ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact scale_div_log_sq_le hx (dyadicScale_retained_lower hη
        (by linarith) hfirst (by simpa using Finset.mem_range.mp hj))
    _ = 16 * (∑ j ∈ Finset.range (dyadicLast η x + 1),
        dyadicScale η x j) / Real.log x ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ 16 * η * x / Real.log x ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have h := sum_dyadicScale_le hη (by linarith : 0 < x) (dyadicLast η x)
      nlinarith

/-- An absolute logarithmic bound on the number of retained blocks. -/
theorem dyadicLast_add_one_le_log {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : 16 ≤ x) (hfirst : Real.sqrt x ≤ dyadicScale η x 0) :
    ((dyadicLast η x + 1 : ℕ) : ℝ) ≤ (1 / Real.log 2) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlη : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl := dyadicScale_log_lower hη hx hfirst (j := dyadicLast η x) le_rfl
  have hid : Real.log (dyadicScale η x (dyadicLast η x)) =
      Real.log η + Real.log x - ((dyadicLast η x + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [dyadicScale, Real.log_div (mul_pos hη hx0).ne' (by positivity),
      Real.log_mul hη.ne' hx0.ne', Real.log_pow]
  have hb : ((dyadicLast η x + 1 : ℕ) : ℝ) ≤ Real.log x / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (by linarith)
  simpa [div_eq_mul_inv, mul_comm] using hb

end
end Wu2004MeanValue

import MathlibNt.Wu2008DoubleSieve.TruncatedSixthAssembly

/-!
# A source-backed truncated-sixth finite eleven upper bound

The coefficient uses the accepted two outer-weight errors, the joint
repeated-first budget, and the pair-endpoint budget. No original
untruncated eleven-term inequality is asserted.
-/

namespace Wu2008DoubleSieve

open Real

theorem truncatedSixth_le_count_power {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (truncatedSixthExpression N z w u v V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzw := rpow_le_rpow_of_exponent_le hN1 hκ
  have hwu := rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 2 - 3 * κ₁ by linarith)
  have hwv := rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 3 by linarith)
  have huv := rpow_le_rpow_of_exponent_le hN1
    (show 1 / 2 - 3 * κ₁ ≤ 1 / 3 by linarith)
  have hu : 0 ≤ (N : ℝ) ^ (1 / 2 - 3 * κ₁) := rpow_nonneg hN0.le _
  have hV : (N : ℝ) ^ (1 / 2 - 2 * κ₁) =
      (N : ℝ) ^ κ₁ * (N : ℝ) ^ (1 / 2 - 3 * κ₁) := by
    rw [← rpow_add hN0]
    congr 1
    ring
  have hv : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := rpow_nonneg hN0.le _
  have hNv : (N : ℝ) ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [← rpow_natCast, ← rpow_mul hN0.le]
    norm_num
  have hE := truncatedSixth_le_count_explicit (by omega : 0 < N) hz
    hzw hwu hwv huv hu hV.le hv hNv
    (s3ThirdRange_subset_source_triples (by omega) hκ hparam)
  have hR := s3_repeated_first_two_ranges_le hN he (by linarith : 0 < κ₁) hz hwu
  have hP := pair_endpoint_sum_le hN he (by linarith : 0 < κ₂) (hz.trans hzw) hwu
  have hdiv : (N : ℝ) / (N : ℝ) ^ κ₂ = (N : ℝ) ^ (1 - κ₂) := by
    rw [rpow_sub hN0, rpow_one]
  rw [hdiv] at hP
  have hP' : (s3PairRepeatedBudget N ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) : ℝ) ≤
        2 * (1 / κ₂) ^ 2 * (N : ℝ) ^ (1 - κ₂) := by
    simpa only [s3PairRepeatedBudget, Int.cast_sum, Int.cast_natCast] using hP
  have hpw := rpow_le_rpow_of_exponent_le hN1 (show 1 - κ₂ ≤ 1 - κ₁ by linarith)
  have hP'' := hP'.trans (mul_le_mul_of_nonneg_left hpw
    (show 0 ≤ 2 * (1 / κ₂) ^ 2 by positivity))
  have hEw := lowerWeight_error_le_rpow (by omega : 0 < N)
    (show κ₂ ≤ 1 / 2 by linarith)
  have hEz := lowerWeight_error_le_rpow (by omega : 0 < N)
    (show κ₁ ≤ 1 / 2 by linarith)
  nlinarith

noncomputable def truncatedSixthFixedExpression (N : ℕ) : ℤ :=
  let κ₁ : ℝ := 100 / 1327
  let κ₂ : ℝ := 25 / 206
  truncatedSixthExpression N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
    ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ))
    ((N : ℝ) ^ (1 / 2 - 2 * κ₁))

noncomputable def truncatedSixthErrorConstant : ℝ :=
  16 + 2 * (1327 / 100 : ℝ) ^ 3 + 2 * (206 / 25 : ℝ) ^ 2

theorem truncatedSixthErrorConstant_pos : 0 < truncatedSixthErrorConstant := by
  norm_num [truncatedSixthErrorConstant]

theorem truncatedSixth_fixed_le_count {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) (hz : 2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    (truncatedSixthFixedExpression N : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        truncatedSixthErrorConstant * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  have h := truncatedSixth_le_count_power (κ₁ := 100 / 1327) (κ₂ := 25 / 206)
    hN he (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz
  norm_num only [truncatedSixthFixedExpression, truncatedSixthErrorConstant,
    one_div_div, div_one] at h ⊢
  exact h

end Wu2008DoubleSieve

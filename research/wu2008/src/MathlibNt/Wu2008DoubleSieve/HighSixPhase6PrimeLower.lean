import MathlibNt.Wu2008DoubleSieve.HighSixPrimeDeltaLimit

namespace Wu2008DoubleSieve.HighSixPhase6
open Set Real MeasureTheory

/-- Exact constant lower bound on the original closed prime window. -/
theorem prime_kernel_zero_lower {t : ℝ} (ht : t ∈ Icc HighSix.left HighSix.right) :
    (16 : ℝ) ≤ 1/(t*(1/2-0-t)) := by
  have ht0 : 0 < t := by norm_num [HighSix.left] at ht; linarith [ht.1]
  have ht1 : 0 < 1/2-0-t := by norm_num [HighSix.right] at ht; linarith [ht.2]
  apply (le_div_iff₀ (mul_pos ht0 ht1)).mpr
  nlinarith only [sq_nonneg (t-1/4)]

/-- No numerical integration: compare with the constant kernel 16. -/
theorem primeIntegral_zero_lower : (160/1327 : ℝ) ≤ HighSix.primeIntegral 0 := by
  have h := intervalIntegral.integral_mono_on
    (show HighSix.left ≤ HighSix.right by norm_num [HighSix.left,HighSix.right])
    (show IntervalIntegrable (fun _ : ℝ => (16 : ℝ)) volume HighSix.left HighSix.right
      from intervalIntegrable_const)
    (HighSixDeltaLimit.prime_kernel_integrable (δ := 0) (by norm_num))
    (fun t ht => prime_kernel_zero_lower ht)
  norm_num [HighSix.primeIntegral,HighSix.left,HighSix.right] at h ⊢
  exact h

theorem primeIntegral_zero_positive : 0 < HighSix.primeIntegral 0 :=
  lt_of_lt_of_le (by norm_num) primeIntegral_zero_lower

end Wu2008DoubleSieve.HighSixPhase6

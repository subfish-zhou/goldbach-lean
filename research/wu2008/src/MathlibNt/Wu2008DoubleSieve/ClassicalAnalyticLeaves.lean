import MathlibNt.Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
import MathlibNt.Wu2008DoubleSieve.CoefficientRecurrence

namespace Wu2008DoubleSieve.ClassicalAnalyticLeaves
open Real Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Positivity comes from the frozen delay solution, not a consumer premise. -/
theorem lower_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ wuLowerCoefficient s := by
  exact div_nonneg (mul_nonneg hs.le (jr1965f_nonneg hs)) (by positivity)

theorem upper_pos {s : ℝ} (hs : 0 < s) : 0 < wuUpperCoefficient s := by
  exact div_pos (mul_pos hs (jr1965F_pos hs)) (by positivity)

theorem lower_mono {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    wuLowerCoefficient s ≤ wuLowerCoefficient t := by
  have h := wuLowerCoefficient_sub_eq_integral hs hst
  have hi : 0 ≤ ∫ u in (s-1)..(t-1), wuUpperCoefficient u / u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact div_nonneg (upper_pos hu0).le hu0.le
  linarith

theorem upper_mono {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    wuUpperCoefficient s ≤ wuUpperCoefficient t := by
  have h := wuUpperCoefficient_sub_eq_integral hs hst
  have hi : 0 ≤ ∫ u in (s-1)..(t-1), wuLowerCoefficient u / u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact div_nonneg (lower_nonneg hu0) hu0.le
  linarith

theorem upper_ge_one {s : ℝ} (hs : 1 ≤ s) : 1 ≤ wuUpperCoefficient s := by
  by_cases h3 : s ≤ 3
  · exact le_of_eq (jr1965F_normalized_initial (by linarith) h3).symm
  · have h := upper_mono (by norm_num : (2 : ℝ) ≤ 3) (le_of_not_ge h3)
    have hinit : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
    linarith

/-- An FTC on a positive interval; no estimated integral is assumed. -/
theorem integral_reciprocal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, 1/u) = log b - log a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hab] at hu
    simpa only [one_div] using hasDerivAt_log (ha.trans_le hu.1).ne'
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div continuousOn_id (fun u hu => by
      rw [uIcc_of_le hab] at hu
      exact (ha.trans_le hu.1).ne')

/-- This is a global lower bound, not an invalid continuation of the initial equality. -/
theorem lower_ge_log {s : ℝ} (hs : 2 ≤ s) : log (s-1) ≤ wuLowerCoefficient s := by
  have hrec := wuLowerCoefficient_sub_eq_integral (le_rfl : (2 : ℝ) ≤ 2) hs
  have hz : wuLowerCoefficient 2 = 0 := by
    simp [wuLowerCoefficient, jr1965f_initial le_rfl]
  have hi : (∫ u in (1 : ℝ)..(s-1), 1/u) ≤
      ∫ u in (1 : ℝ)..(s-1), wuUpperCoefficient u/u := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuousOn_const.div continuousOn_id (fun u hu => by
        rw [uIcc_of_le (by linarith : (1 : ℝ) ≤ s-1)] at hu
        change u ≠ 0
        linarith [hu.1])).intervalIntegrable
    · exact wuUpperCoefficient_div_intervalIntegrable (by norm_num) (by linarith)
    · intro u hu
      exact div_le_div_of_nonneg_right (upper_ge_one hu.1) (by linarith [hu.1])
  rw [integral_reciprocal (by norm_num) (by linarith), log_one, sub_zero] at hi
  norm_num only [show (2 : ℝ)-1=1 by norm_num, hz, sub_zero] at hrec
  linarith

theorem fifth_nonneg : 0 ≤ fifthPairFlin := by
  unfold fifthPairFlin fifthPairFdelta
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg truncatedSixthLower_parameters.2.1.le
  intro y hy
  apply intervalIntegral.integral_nonneg hy.1
  intro x hx
  have hb := fifthPair_triangle_bounds (δ := 0) (by norm_num) (by norm_num)
    hx.1 hx.2 hy.2
  apply div_nonneg (lower_nonneg (by linarith [hb.2.2.1]))
  have hd : 0 < truncatedSixthLowerC 0 - x - y := by
    have hxy := hb.2.2.2.2.1
    have hc := hb.2.2.2.2.2
    linarith [hb.2.1]
  exact (mul_pos (mul_pos hb.1 hb.2.1) hd).le

theorem sixth_nonneg : 0 ≤ truncatedSixthLowerF6lin := by
  unfold truncatedSixthLowerF6lin truncatedSixthLowerFdelta
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg truncatedSixthLower_parameters.2.1.le
  intro x _hx
  apply intervalIntegral.integral_nonneg truncatedSixthLower_parameters.2.2.1.le
  intro y _hy
  split_ifs with h
  · have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) h
    apply div_nonneg (lower_nonneg (by linarith [hb.2.2.2.1]))
    exact mul_nonneg (mul_nonneg hb.1.le hb.2.1.le)
      ((mul_nonneg (by norm_num) truncatedSixthLower_parameters.1.le).trans hb.2.2.1)
  · exact le_rfl

/-- An unconditional analytic lower estimate for the two literal base terms. -/
theorem base_log_lower :
    24 * log (1127/200 : ℝ) + 8 * log (78/25 : ℝ) ≤
      24 * wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
      8 * wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have h1 := lower_ge_log (s := 1/(2*truncatedSixthLowerAlpha)) (by
    norm_num [truncatedSixthLowerAlpha])
  have h2 := lower_ge_log (s := 1/(2*truncatedSixthLowerBeta)) (by
    norm_num [truncatedSixthLowerBeta])
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerBeta] at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve.ClassicalAnalyticLeaves

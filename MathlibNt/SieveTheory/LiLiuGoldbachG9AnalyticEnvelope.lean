import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation

open Set MeasureTheory
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The production logarithmic polynomial, with the literal split weights. -/
def envelope : ℝ :=
  (36 / 5 : ℝ) * (∫ u in (4 / 53 : ℝ)..(1 / 10),
    S3Correction.L (1 - 3 * u) / (u * (1 - u)^2)) +
  8 * (∫ u in (1 / 10 : ℝ)..(1 / 3),
    S3Correction.L (1 - 3 * u) / (u * (1 - u)))

/-- A whole-half-line analytic remainder; no samples or scalar assumptions. -/
theorem log_remainder {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ S3Correction.L x - Real.log (1+x) ∧
    S3Correction.L x - Real.log (1+x) ≤ x^34 / 34 := by
  refine ⟨sub_nonneg.mpr (S3Correction.log_le_L hx), ?_⟩
  let F : ℝ → ℝ := fun y => y^34 / 34 - S3Correction.L y + Real.log (1+y)
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt F (y^33 - S3Correction.dL y + 1/(1+y)) y := by
    intro y hy
    have hl : HasDerivAt (fun z : ℝ => Real.log (1+z)) (1/(1+y)) y := by
      convert! (Real.hasDerivAt_log (by linarith [hy.1] : 1+y ≠ 0)).comp y
        ((hasDerivAt_id y).const_add 1) using 1; simp [one_div]
    have hp : HasDerivAt (fun z : ℝ => z^34 / 34) (y^33) y := by
      convert! (hasDerivAt_pow 34 y).div_const 34 using 1; norm_num
    exact (hp.sub (S3Correction.L_deriv y)).add hl
  have hp : ∀ y ∈ Icc (0 : ℝ) x,
      0 ≤ y^33 - S3Correction.dL y + 1/(1+y) := by
    intro y hy
    have he := S3Correction.L_residual y
    have hpos : 0 < 1+y := by linarith [hy.1]
    have hid : y^33 - S3Correction.dL y + 1/(1+y) = y^34/(1+y) := by
      apply (eq_div_iff hpos.ne').2
      field_simp
      nlinarith only [he, show y^34 = y^33*y by ring]
    rw [hid]
    positivity
  have hm : MonotoneOn F (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hp y (interior_subset hy))
  have h := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have hz : F 0 = 0 := by simp [F, S3Correction.L_zero]
  rw [hz] at h
  dsimp [F] at h
  linarith

theorem continuousOn_envelope_kernel (k : ℕ) :
    ContinuousOn (fun u : ℝ => S3Correction.L (1-3*u)/(u*(1-u)^k))
      (Icc (4/53 : ℝ) (1/3)) := by
  have hc : Continuous (fun u : ℝ => S3Correction.L (1-3*u)) := by
    unfold S3Correction.L
    fun_prop
  apply hc.continuousOn.div (continuousOn_id.mul ((continuousOn_const.sub continuousOn_id).pow k))
  intro u hu
  exact mul_ne_zero (by dsimp; linarith [hu.1])
    (pow_ne_zero k (by change 1-u ≠ 0; linarith [hu.2]))

theorem actual_le_envelope : goldbachB9PaperSplitIntegral ≤ envelope := by
  rw [goldbachB9PaperSplitIntegral_eq_singleIntegrals]
  unfold envelope
  have hl : (∫ u in (4/53 : ℝ)..(1/10), Real.log (2-3*u)/(u*(1-u)^2)) ≤
      ∫ u in (4/53 : ℝ)..(1/10), S3Correction.L (1-3*u)/(u*(1-u)^2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)]
      exact continuousOn_goldbachB9WeightedSingleIntegrand.mono (Icc_subset_Icc_right (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)]
      exact (continuousOn_envelope_kernel 2).mono (Icc_subset_Icc_right (by norm_num))
    · intro u hu
      have h := S3Correction.log_le_L (by linarith [hu.2] : 0 ≤ 1-3*u)
      rw [show (1:ℝ)+(1-3*u) = 2-3*u by ring] at h
      exact div_le_div_of_nonneg_right h (by have := hu.1; positivity)
  have hh : (∫ u in (1/10 : ℝ)..(1/3), Real.log (2-3*u)/(u*(1-u))) ≤
      ∫ u in (1/10 : ℝ)..(1/3), S3Correction.L (1-3*u)/(u*(1-u)) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 1/3)]
      exact continuousOn_goldbachB9SingleIntegrand.mono (Icc_subset_Icc_left (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 1/3)]
      simpa only [pow_one] using
        (continuousOn_envelope_kernel 1).mono (Icc_subset_Icc_left (by norm_num))
    · intro u hu
      have h := S3Correction.log_le_L (by linarith [hu.2] : 0 ≤ 1-3*u)
      rw [show (1:ℝ)+(1-3*u) = 2-3*u by ring] at h
      exact div_le_div_of_nonneg_right h (mul_nonneg (by linarith [hu.1]) (by linarith [hu.2]))
  exact add_le_add (mul_le_mul_of_nonneg_left hl (by norm_num))
    (mul_le_mul_of_nonneg_left hh (by norm_num))

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic

import WRMapMFirstConstants

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve

namespace WuPaper.RMapMFirst

theorem original_affine_integral (r : ℝ) :
    (∫ x in alpha..r, originalKernel ((1 / 2 - x) / alpha)) =
      alpha * ∫ t in ((1 / 2 - r) / alpha)..((1 / 2 - alpha) / alpha),
        originalKernel t := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun y => originalKernel (y / alpha)) (1 / 2)]
  simpa only [div_eq_mul_inv, inv_inv, smul_eq_mul, mul_comm (alpha⁻¹)] using
    (intervalIntegral.integral_comp_mul_left
      (a := (1 / 2 : ℝ) - r) (b := (1 / 2 : ℝ) - alpha)
      (c := alpha⁻¹) originalKernel
      (by norm_num [alpha, truncatedSixthLowerAlpha]))

theorem original_affine_kernel {x : ℝ} (hx : x ∈ Icc alpha (1 / 3 : ℝ)) :
    wuUpperCoefficient ((1 / 2 - x) / alpha) / (x * (1 / 2 - x)) =
      (2 / alpha) * originalKernel ((1 / 2 - x) / alpha) := by
  have ha : alpha ≠ 0 := by norm_num [alpha, truncatedSixthLowerAlpha]
  have hx0 : x ≠ 0 :=
    (lt_of_lt_of_le (by norm_num [alpha, truncatedSixthLowerAlpha] : 0 < alpha) hx.1).ne'
  have hc : (1 / 2 : ℝ) - x ≠ 0 := by linarith [hx.2]
  unfold originalKernel denominator
  field_simp
  ring

theorem Glin_eq_original {r : ℝ} (hr : alpha ≤ r) (hr3 : r ≤ 1 / 3) :
    SingleUpperClassicalLimit.Glin r =
      8 * ∫ t in ((1 / 2 - r) / alpha)..top, originalKernel t := by
  have he : (∫ x in alpha..r,
      wuUpperCoefficient ((1 / 2 - x) / alpha) / (x * (1 / 2 - x))) =
      (2 / alpha) * ∫ x in alpha..r, originalKernel ((1 / 2 - x) / alpha) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr] at hx
    exact original_affine_kernel ⟨hx.1, hx.2.trans hr3⟩
  simp only [SingleUpperClassicalLimit.Glin, SingleUpperClassicalLimit.Gdelta, sub_zero]
  rw [he, original_affine_integral]
  norm_num [alpha, top, truncatedSixthLowerAlpha]
  ring

theorem C3_exact : C3 = Wu08TerminalAlignment.thirdMain := by
  symm
  unfold Wu08TerminalAlignment.thirdMain
  rw [Glin_eq_original (by norm_num [alpha, truncatedSixthLowerAlpha]) le_rfl]
  norm_num [C3, alpha, bottom, truncatedSixthLowerAlpha]

theorem C4_exact : C4 = Wu08TerminalAlignment.fourthMain := by
  symm
  unfold Wu08TerminalAlignment.fourthMain
  rw [Glin_eq_original
    (by norm_num [alpha, truncatedSixthLowerSigma, truncatedSixthLowerAlpha])
    (by norm_num [truncatedSixthLowerSigma, truncatedSixthLowerAlpha])]
  norm_num [C4, alpha, truncatedSixthLowerSigma, truncatedSixthLowerAlpha]

#check @original_affine_integral
#print axioms original_affine_integral
#check @original_affine_kernel
#print axioms original_affine_kernel
#check @Glin_eq_original
#print axioms Glin_eq_original
#check @C3_exact
#print axioms C3_exact
#check @C4_exact
#print axioms C4_exact

end WuPaper.RMapMFirst

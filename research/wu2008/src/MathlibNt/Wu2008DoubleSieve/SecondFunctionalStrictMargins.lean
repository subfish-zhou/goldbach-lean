import MathlibNt.Wu2008DoubleSieve.SecondFunctionalRationalCost
import MathlibNt.Wu2008DoubleSieve.PositiveKernelBound

namespace Wu2008DoubleSieve.SecondFunctionalStrictMargins
open Set MeasureTheory SecondFunctionalParameters SecondFunctionalSignedCore
open SecondFunctionalRationalCost
open scoped Interval

/-- Strict original signed-core margin at an explicitly fixed delta. -/
theorem row3_D_zero : (1/500 : ℝ) < D row3 (0) := by
  have hS := positiveKernel_original_strict_lower (a := row3.s) (b := row3.S)
    (by norm_num [row3]) (by norm_num [row3])
    (by norm_num [row3]) (by norm_num [row3])
  have hk := positiveKernel_original_strict_lower (a := row3.kappa3) (b := row3.kappa1)
    (by norm_num [row3]) (by norm_num [row3])
    (by norm_num [row3]) (by norm_num [row3])
  have hl := directedL_upper (c := row3.kappa2)
    (by norm_num [row3]) (by norm_num [row3])
  have hc := row3_cost_upper
  norm_num only [row3] at hS hk hl hc
  dsimp only [D, row3]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hc]

/-- Strict original signed-core margin at an explicitly fixed delta. -/
theorem row4_D_zero : (1/50 : ℝ) < D row4 (0) := by
  have hS := positiveKernel_original_strict_lower (a := row4.s) (b := row4.S)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hk := positiveKernel_original_strict_lower (a := row4.kappa3) (b := row4.kappa1)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hl := directedL_upper (c := row4.kappa2)
    (by norm_num [row4]) (by norm_num [row4])
  have hc := row4_cost_upper
  norm_num only [row4] at hS hk hl hc
  dsimp only [D, row4]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hc]

/-- Strict original signed-core margin at an explicitly fixed delta. -/
theorem row3_D_fixed : (1/600 : ℝ) < D row3 (1/1000) := by
  have hS := positiveKernel_original_strict_lower (a := row3.s) (b := row3.S)
    (by norm_num [row3]) (by norm_num [row3])
    (by norm_num [row3]) (by norm_num [row3])
  have hk := positiveKernel_original_strict_lower (a := row3.kappa3) (b := row3.kappa1)
    (by norm_num [row3]) (by norm_num [row3])
    (by norm_num [row3]) (by norm_num [row3])
  have hl := directedL_upper (c := row3.kappa2)
    (by norm_num [row3]) (by norm_num [row3])
  have hc := row3_cost_upper
  norm_num only [row3] at hS hk hl hc
  dsimp only [D, row3]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hc]

/-- Strict original signed-core margin at an explicitly fixed delta. -/
theorem row4_D_fixed : (1/60 : ℝ) < D row4 (1/1000) := by
  have hS := positiveKernel_original_strict_lower (a := row4.s) (b := row4.S)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hk := positiveKernel_original_strict_lower (a := row4.kappa3) (b := row4.kappa1)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hl := directedL_upper (c := row4.kappa2)
    (by norm_num [row4]) (by norm_num [row4])
  have hc := row4_cost_upper
  norm_num only [row4] at hS hk hl hc
  dsimp only [D, row4]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hc]

/-- Strict original signed-core margin at an explicitly fixed delta. -/
theorem row4_D_larger_delta : (1/60 : ℝ) < D row4 (1/100) := by
  have hS := positiveKernel_original_strict_lower (a := row4.s) (b := row4.S)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hk := positiveKernel_original_strict_lower (a := row4.kappa3) (b := row4.kappa1)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hl := directedL_upper (c := row4.kappa2)
    (by norm_num [row4]) (by norm_num [row4])
  have hc := row4_cost_upper
  norm_num only [row4] at hS hk hl hc
  dsimp only [D, row4]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hc]

/-- Removing feedback uses the actual nonnegative improvement and density, not a sign premise. -/
theorem actual_core_lower (i : Fin 4) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    D (SecondFunctionalPositive.parameters i) δ/5 ≤
      wuImprovementLimit true δ (SecondFunctionalPositive.parameters i).s := by
  have h := original_H_with_feedback i hδ hδhi
  have hr := original_remainder_nonneg i hδ hδhi
  have hi : 0 ≤ ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v *
      SecondFunctionalCoupledFeedback.density (SecondFunctionalPositive.parameters i) v := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact mul_nonneg ((wuImprovementLimit_bounds hδ (by linarith) hv.1 (by linarith [hv.2])).1)
      (SecondFunctionalCoupledFeedback.density_nonnegative _
        (SecondFunctionalPositive.parameters_analytic i) v)
  linarith only [h, hr, hi]

/-- The original nonnegative gains increase the signed source. -/
theorem actual_source_core_lower (i : Fin 4) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    D (SecondFunctionalPositive.parameters i) δ/5 ≤
      Omega3ElementaryFeedback.source (SecondFunctionalPositive.parameters i) δ := by
  rw [original_source_eq i hδ hδhi]
  exact le_add_of_nonneg_right (original_remainder_nonneg i hδ hδhi)

/-- Actual original H with a strict margin at the common fixed delta. -/
theorem row3_H_positive : (1/3000 : ℝ) < wuImprovementLimit true (1/1000) row3.s := by
  have h := actual_core_lower (2 : Fin 4) (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)
  change D row3 (1/1000)/5 ≤ wuImprovementLimit true (1/1000) row3.s at h
  linarith only [h, row3_D_fixed]

/-- Actual original source with a strict margin at the common fixed delta. -/
theorem row3_source_positive : (1/3000 : ℝ) < Omega3ElementaryFeedback.source row3 (1/1000) := by
  have h := actual_source_core_lower (2 : Fin 4) (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)
  change D row3 (1/1000)/5 ≤ Omega3ElementaryFeedback.source row3 (1/1000) at h
  linarith only [h, row3_D_fixed]

/-- Actual original H with a strict margin at the common fixed delta. -/
theorem row4_H_positive : (1/300 : ℝ) < wuImprovementLimit true (1/1000) row4.s := by
  have h := actual_core_lower (3 : Fin 4) (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)
  change D row4 (1/1000)/5 ≤ wuImprovementLimit true (1/1000) row4.s at h
  linarith only [h, row4_D_fixed]

/-- Actual original source with a strict margin at the common fixed delta. -/
theorem row4_source_positive : (1/300 : ℝ) < Omega3ElementaryFeedback.source row4 (1/1000) := by
  have h := actual_source_core_lower (3 : Fin 4) (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)
  change D row4 (1/1000)/5 ≤ Omega3ElementaryFeedback.source row4 (1/1000) at h
  linarith only [h, row4_D_fixed]

end Wu2008DoubleSieve.SecondFunctionalStrictMargins

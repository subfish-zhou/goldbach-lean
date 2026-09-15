import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivativeBound

/-!
# Weak-strip difference bounds for Dirichlet L-functions

This module integrates the continued derivative along a horizontal segment and
then applies the pointwise weak-strip derivative estimate at every point of the
integration path.
-/

open Complex Set

namespace DirichletLWeakStripDifferenceBound

open DirichletLWeakStripDerivativeBound

variable {q : ℕ} [NeZero q]

/-- The horizontal integral of the derivative of a nonprincipal Dirichlet
L-function is the difference of its endpoint values. -/
theorem integral_deriv_LFunction_eq_sub
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ₁ σ₂ t : ℝ) :
    (∫ σ in σ₁..σ₂, deriv χ.LFunction (σ + t * I)) =
      χ.LFunction (σ₂ + t * I) - χ.LFunction (σ₁ + t * I) := by
  have diff : ∀ σ : ℝ, DifferentiableAt ℂ χ.LFunction (σ + t * I) := by
    intro σ
    exact χ.differentiable_LFunction hχ (σ + t * I)
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro σ _
    exact (diff σ).restrictScalars ℝ |>.comp σ
      (DifferentiableAt.add_const (c := t * I) (differentiableAt_ofReal σ))
  · have hderiv : Continuous (deriv χ.LFunction) :=
      ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).deriv.continuous
    exact hderiv.continuousOn.comp
      (continuous_ofReal.continuousOn.add continuousOn_const) (mapsTo_image _ _)

/-- Integrating the pointwise derivative estimate gives a Lipschitz bound along
any horizontal segment contained in the requested weak strip. -/
theorem norm_LFunction_sub_le_fixed_log_sq_mul
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A C σ₁ σ₂ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hlower : 1 - A / Real.log |t| ≤ σ₁) (hσ₁σ₂ : σ₁ < σ₂)
    (hupper : σ₂ ≤ 2) (ht : 3 < |t|) (hC : 2 ≤ C) :
    ‖χ.LFunction (σ₂ + t * I) - χ.LFunction (σ₁ + t * I)‖ ≤
      Real.exp A * (C + 100 * q) * (Real.log |t|) ^ 2 * (σ₂ - σ₁) := by
  rw [← integral_deriv_LFunction_eq_sub χ hχ σ₁ σ₂ t]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr
    rw [_root_.abs_of_nonneg (sub_nonneg.mpr hσ₁σ₂.le)]
  · intro σ hσ
    rw [uIoc_of_le hσ₁σ₂.le, mem_Ioc] at hσ
    exact norm_deriv_LFunction_le_fixed_log_sq χ hχ hA
      (hlower.trans hσ.1.le) (hσ.2.trans hupper) ht hC

end DirichletLWeakStripDifferenceBound

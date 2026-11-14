module

public import Mathlib.Analysis.Complex.RealDeriv
public import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Weak-strip difference bounds for Dirichlet L-functions

This module integrates the continued derivative along a horizontal segment and
then applies the pointwise weak-strip derivative estimate at every point of the
integration path.
-/

@[expose] public section

open Complex Set

namespace DirichletLWeakStripDifferenceBound


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
  have hline (σ : ℝ) :
      HasDerivAt (fun x : ℝ => χ.LFunction (x + t * I))
        (deriv χ.LFunction (σ + t * I)) σ := by
    have htranslate : HasDerivAt (fun z : ℂ => z + t * I) 1 (σ : ℂ) :=
      (hasDerivAt_id (σ : ℂ)).add_const _
    have hcomp := (diff σ).hasDerivAt.comp (σ : ℂ) htranslate
    simpa only [Function.comp_apply, mul_one] using hcomp.comp_ofReal
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact funext fun σ => (hline σ).deriv
  · exact fun σ _ => (hline σ).differentiableAt
  · have hderiv : Continuous (deriv χ.LFunction) :=
      ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).deriv.continuous
    exact hderiv.continuousOn.comp
      (continuous_ofReal.continuousOn.add continuousOn_const) (mapsTo_image _ _)


end DirichletLWeakStripDifferenceBound

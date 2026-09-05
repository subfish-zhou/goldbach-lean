import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex
open ArithmeticFunction hiding log
open scoped LSeries.notation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- A nonprincipal Dirichlet L-function is entire in the differentiability API. -/
lemma lFunction_entire_of_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  differentiable_LFunction hχ

/-- The completed L-function is entire for a nonprincipal character. -/
lemma completedLFunction_entire_of_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) :=
  differentiable_completedLFunction hχ

/-- In the half-plane of absolute convergence, the negative logarithmic derivative
is the L-series of the von Mangoldt twist. -/
lemma LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗vonMangoldt) s = -deriv (LFunction χ) s / LFunction χ s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs

/-- The negative logarithmic derivative is continuous wherever a nonprincipal
Dirichlet L-function is nonzero. -/
lemma continuousOn_neg_logDeriv_LFunction
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ContinuousOn (fun s ↦ -deriv (LFunction χ) s / LFunction χ s)
      {s | LFunction χ s ≠ 0} :=
  continuousOn_neg_logDeriv_LFunction_of_nontriv hχ

end DirichletCharacter
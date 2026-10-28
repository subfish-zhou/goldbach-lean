import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex
open ArithmeticFunction hiding log
open scoped LSeries.notation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]


/-- In the half-plane of absolute convergence, the negative logarithmic derivative
is the L-series of the von Mangoldt twist. -/
lemma LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗vonMangoldt) s = -deriv (LFunction χ) s / LFunction χ s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs


end DirichletCharacter
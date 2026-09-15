import TailEndpointPayment

noncomputable section
open Real F1JointFTC
namespace TailRationalBasis

/-- A fifth pole is forced by division of the original first floor by u. -/
def fifthPrimitive (a c u : ℝ) : ℝ := -c/(4*(u-a)^4)

theorem fifthPrimitive_deriv (a c u : ℝ) (h : u-a ≠ 0) :
    HasDerivAt (fifthPrimitive a c) (c/(u-a)^5) u := by
  have hd := ((((hasDerivAt_id u).sub_const a).pow 4).inv (pow_ne_zero 4 h)).const_mul (-c/4)
  convert hd using 1 <;> first
    | rfl
    | (funext x; dsimp [fifthPrimitive]; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
    | (dsimp; field_simp)

/-- The original low has the same denominator and no new approximation. -/
def lowNumerator (x : ℝ) : ℝ := -1/30+(22/105)*x-(21/5)*x^2-(58/3)*x^3-
  (88/3)*x^4-(2/15)*x^5+(439/15)*x^6+(298/15)*x^7+(155/42)*x^8

theorem low_rational {x : ℝ} (hx : 0 < x) :
    low x=lowNumerator x/(x^2*(x+1)^4*(x^2+8*x+1)) := by
  unfold low lowNumerator F1FullRecoveryPayment.lowerGapPayment
    F1LowerResidual.payment F1LowerResidual.denom
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog
    Wu2008DoubleSieve.SharpLogRecurrence.upperLog
  field_simp (disch := positivity)
  ring
end TailRationalBasis

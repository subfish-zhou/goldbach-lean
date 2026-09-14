import MathlibNt.Tactic.ElementaryDeriv
import Mathlib.Tactic.Ring

-- Nonzero logarithm arguments, including negative ones, are valid over the reals.
example (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log (1/x) x := by
  elementary_deriv []

example (a x : ℝ) : HasDerivAt (fun t : ℝ => t^3/a) (3*x^2/a) x := by
  elementary_deriv []
  ring

example (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => Real.log (1+t)) (1/(1+x)) x := by
  elementary_deriv []
  all_goals simp

example (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp (t^2)/t) ((2*x^2-1)*Real.exp (x^2)/x^2) x := by
  elementary_deriv []
  field_simp
  ring

example (f : ℝ → ℝ) (d x : ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun t : ℝ => f t + Real.exp t) (d + Real.exp x) x := by
  elementary_deriv [hf]
  all_goals simp

-- Missing conditions and wrong requested derivative must not become complete proofs.
example (_x : ℝ) : True := by
  fail_if_success
    have : HasDerivAt Real.log (1/_x) _x := by
      elementary_deriv []
      all_goals simp
  fail_if_success
    have : HasDerivAt (fun t : ℝ => t^2) (2*_x+1) _x := by
      elementary_deriv []
      all_goals (try simp; try ring)
  trivial

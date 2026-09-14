import MathlibNt.Tactic.PolynomialDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

example (a b x : ℝ) : HasDerivAt (fun t : ℝ => a*t^3 + b*t - 7)
    (3*a*x^2+b) x := by
  polynomial_deriv
  ring

example (a x : ℝ) : HasDerivAt (fun t : ℝ => (t+1)^4/a)
    (4*(x+1)^3/a) x := by
  polynomial_deriv
  ring

example (x : ℝ) : HasDerivAt (fun _ : ℝ => Real.log (x^2+1)) 0 x := by
  polynomial_deriv

example (_x : ℝ) : True := by
  fail_if_success
    have : HasDerivAt (fun t : ℝ => t^2) (2*_x+1) _x := by
      polynomial_deriv
      ring
  trivial

example (_x : ℝ) : True := by
  fail_if_success
    have : HasDerivAt (fun t : ℝ => 1/t) (-(_x^2)⁻¹) _x := by
      polynomial_deriv
  fail_if_success
    have : HasDerivAt Real.log (1/_x) _x := by
      polynomial_deriv
  trivial

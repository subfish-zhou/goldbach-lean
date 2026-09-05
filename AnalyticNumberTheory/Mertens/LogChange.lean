import AnalyticNumberTheory.Mertens.PrimeAbel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic change of variables for the prime Abel integral

This file records the substitution `x = exp u` in the integral occurring in
`primeDirichletSum_eq_mul_integral_of_pos`.  The Jacobian cancels the extra
factor `x⁻¹`, leaving the exponential Abel kernel `exp (-εu)`.
-/

namespace AnalyticNumberTheory.Mertens

open Real Set

private theorem exp_smul_prime_cpow (ε u : ℝ) :
    Real.exp u •
        ((primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) *
          (Real.exp u : ℂ) ^ (-((ε : ℂ) + 1))) =
      (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) *
        (Real.exp (-(ε * u)) : ℂ) := by
  rw [Complex.real_smul]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u))]
  rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  simp_rw [Complex.ofReal_exp]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/--
The logarithmic change of variables `x = exp u` for the prime Abel integral.
No separate integrability assumption is needed: this is the unconditional
change-of-variables identity for the Bochner integral used by Mathlib.
-/
theorem primeAbel_integral_log_change (ε : ℝ) (_hε : 0 < ε) :
    (∫ x : ℝ in Ioi 1,
        (primeReciprocalSum ⌊x⌋₊ : ℂ) *
          (x : ℂ) ^ (-((ε : ℂ) + 1))) =
      ∫ u : ℝ in Ioi 0,
        (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) *
          (Real.exp (-(ε * u)) : ℂ) := by
  rw [← Real.exp_zero]
  rw [← MeasureTheory.integral_comp_exp_Ioi
    (fun x : ℝ =>
      (primeReciprocalSum ⌊x⌋₊ : ℂ) *
        (x : ℂ) ^ (-((ε : ℂ) + 1))) 0]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  exact exp_smul_prime_cpow ε u

end AnalyticNumberTheory.Mertens

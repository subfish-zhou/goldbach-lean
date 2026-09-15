import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory
open scoped Topology

/-- Euler's logarithmic moment, from the existing Gamma derivative at one.
This identifies the normalization only, not the Buchstab limit. -/
theorem euler_log_moment :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)) =
      -Real.eulerMascheroniConstant := by
  have hEq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with s hs
    exact Complex.Gamma_eq_integral hs
  have h := (Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)).congr_of_eventuallyEq hEq
  have he := h.unique Complex.hasDerivAt_Gamma_one
  simp only [sub_self, Complex.cpow_zero, one_mul, ← Complex.ofReal_mul] at he
  have ho := integral_complex_ofReal (f := fun t : ℝ => Real.log t * Real.exp (-t))
    (μ := volume.restrict (Ioi (0 : ℝ)))
  rw [ho] at he
  exact_mod_cast he

end Wu2008DoubleSieve.SecondFunctionalJointTail

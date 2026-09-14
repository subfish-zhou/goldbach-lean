import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace MathlibNt.Analysis

/-- A fixed scalar multiple of any real log power is eventually below any
positive power, with the threshold selected before the varying real input. -/
theorem eventually_const_mul_log_rpow_le_rpow (C b : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ b ≤ x ^ a := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop b ha).const_mul_left C).eventuallyLE,
    eventually_ge_atTop (0 : ℝ)] with x h hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx a)] using h)

end MathlibNt.Analysis

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The truncated Perron sine kernel

This file records only the real-analytic foundation for a truncated Perron kernel.  In
particular, it makes no step-function or approximation claim.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace AnalyticNumberTheory.LargeSieve

/-- The removable-at-zero form of `sin (t * x) / t`. -/
def truncatedPerronIntegrand (x t : ℝ) : ℝ :=
  if t = 0 then x else Real.sin (t * x) / t

/-- The removable definition is exactly `x` times Mathlib's unnormalised sinc. -/
theorem truncatedPerronIntegrand_eq_mul_sinc (x t : ℝ) :
    truncatedPerronIntegrand x t = x * Real.sinc (t * x) := by
  by_cases ht : t = 0
  · simp [truncatedPerronIntegrand, ht]
  by_cases hx : x = 0
  · simp [truncatedPerronIntegrand, ht, hx]
  · rw [truncatedPerronIntegrand, if_neg ht, Real.sinc_of_ne_zero (mul_ne_zero ht hx)]
    field_simp


@[simp]
theorem truncatedPerronIntegrand_zero_left (t : ℝ) :
    truncatedPerronIntegrand 0 t = 0 := by
  rw [truncatedPerronIntegrand_eq_mul_sinc]
  simp

@[simp]
theorem truncatedPerronIntegrand_neg_left (x t : ℝ) :
    truncatedPerronIntegrand (-x) t = -truncatedPerronIntegrand x t := by
  simp only [truncatedPerronIntegrand_eq_mul_sinc]
  rw [mul_neg, Real.sinc_neg]
  ring

/-- Continuity in the integration variable, including at the removable point `t = 0`. -/
theorem continuous_truncatedPerronIntegrand_right (x : ℝ) :
    Continuous (truncatedPerronIntegrand x) := by
  change Continuous (fun t ↦ truncatedPerronIntegrand x t)
  simp_rw [truncatedPerronIntegrand_eq_mul_sinc]
  fun_prop


/-- The sinc bound gives a uniform pointwise majorant for the integrand. -/
theorem abs_truncatedPerronIntegrand_le (x t : ℝ) :
    |truncatedPerronIntegrand x t| ≤ |x| := by
  rw [truncatedPerronIntegrand_eq_mul_sinc, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t * x)) (abs_nonneg x)


end AnalyticNumberTheory.LargeSieve

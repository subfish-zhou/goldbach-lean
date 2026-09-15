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
theorem truncatedPerronIntegrand_zero_right (x : ℝ) :
    truncatedPerronIntegrand x 0 = x := by
  simp [truncatedPerronIntegrand]

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

/-- Continuity in the Perron spatial variable. -/
theorem continuous_truncatedPerronIntegrand_left (t : ℝ) :
    Continuous (fun x ↦ truncatedPerronIntegrand x t) := by
  simp_rw [truncatedPerronIntegrand_eq_mul_sinc]
  fun_prop

/-- Joint continuity of the removable sine kernel. -/
theorem continuous_truncatedPerronIntegrand_uncurry :
    Continuous (Function.uncurry truncatedPerronIntegrand) := by
  change Continuous (fun p : ℝ × ℝ ↦ truncatedPerronIntegrand p.1 p.2)
  simp_rw [truncatedPerronIntegrand_eq_mul_sinc]
  fun_prop

/-- The sine kernel is integrable on every finite interval. -/
theorem intervalIntegrable_truncatedPerronIntegrand (x a b : ℝ) :
    IntervalIntegrable (truncatedPerronIntegrand x) volume a b :=
  (continuous_truncatedPerronIntegrand_right x).intervalIntegrable a b

/-- The real truncated Perron kernel. -/
def truncatedPerronKernel (T x : ℝ) : ℝ :=
  1 / 2 + (1 / Real.pi) * ∫ t in 0..T, truncatedPerronIntegrand x t

@[simp]
theorem truncatedPerronKernel_zero (T : ℝ) :
    truncatedPerronKernel T 0 = 1 / 2 := by
  simp [truncatedPerronKernel]

/-- Reflection in the spatial variable exchanges the two sides of the kernel. -/
theorem truncatedPerronKernel_neg (T x : ℝ) :
    truncatedPerronKernel T (-x) = 1 - truncatedPerronKernel T x := by
  simp_rw [truncatedPerronKernel, truncatedPerronIntegrand_neg_left,
    intervalIntegral.integral_neg]
  ring

/-- For fixed truncation height, the kernel is continuous in `x`. -/
theorem continuous_truncatedPerronKernel_left (T : ℝ) :
    Continuous (fun x ↦ truncatedPerronKernel T x) := by
  unfold truncatedPerronKernel
  apply Continuous.add continuous_const
  apply Continuous.const_mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    continuous_truncatedPerronIntegrand_uncurry 0 T

/-- For fixed `x`, the kernel is continuous in its truncation height. -/
theorem continuous_truncatedPerronKernel_right (x : ℝ) :
    Continuous (fun T ↦ truncatedPerronKernel T x) := by
  unfold truncatedPerronKernel
  apply Continuous.add continuous_const
  apply Continuous.const_mul
  exact intervalIntegral.continuous_primitive
    (intervalIntegrable_truncatedPerronIntegrand x) 0

/-- Triangle inequality for the defining integral. -/
theorem abs_truncatedPerronKernel_sub_half_le_integral_abs {T x : ℝ} (hT : 0 ≤ T) :
    |truncatedPerronKernel T x - 1 / 2| ≤
      (1 / Real.pi) * ∫ t in 0..T, |truncatedPerronIntegrand x t| := by
  rw [truncatedPerronKernel]
  have hpi : 0 ≤ (1 / Real.pi : ℝ) := by positivity
  calc
    |1 / 2 + (1 / Real.pi) * (∫ t in 0..T, truncatedPerronIntegrand x t) - 1 / 2| =
        (1 / Real.pi) * |∫ t in 0..T, truncatedPerronIntegrand x t| := by
          rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hpi]
    _ ≤ (1 / Real.pi) * ∫ t in 0..T, |truncatedPerronIntegrand x t| :=
      mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs hT) hpi

/-- The sinc bound gives a uniform pointwise majorant for the integrand. -/
theorem abs_truncatedPerronIntegrand_le (x t : ℝ) :
    |truncatedPerronIntegrand x t| ≤ |x| := by
  rw [truncatedPerronIntegrand_eq_mul_sinc, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t * x)) (abs_nonneg x)

/-- Coarse but robust integral norm bound, sufficient for later `L¹` estimates. -/
theorem integral_abs_truncatedPerronIntegrand_le {T x : ℝ} (hT : 0 ≤ T) :
    (∫ t in 0..T, |truncatedPerronIntegrand x t|) ≤ T * |x| := by
  calc
    (∫ t in 0..T, |truncatedPerronIntegrand x t|) ≤ ∫ _t in 0..T, |x| := by
      apply intervalIntegral.integral_mono_on hT
      · exact (continuous_truncatedPerronIntegrand_right x).abs.intervalIntegrable 0 T
      · exact continuous_const.intervalIntegrable 0 T
      · intro t _
        exact abs_truncatedPerronIntegrand_le x t
    _ = T * |x| := by simp

/-- Combined triangle and uniform sinc bound. -/
theorem abs_truncatedPerronKernel_sub_half_le {T x : ℝ} (hT : 0 ≤ T) :
    |truncatedPerronKernel T x - 1 / 2| ≤ (T * |x|) / Real.pi := by
  calc
    |truncatedPerronKernel T x - 1 / 2| ≤
        (1 / Real.pi) * ∫ t in 0..T, |truncatedPerronIntegrand x t| :=
      abs_truncatedPerronKernel_sub_half_le_integral_abs hT
    _ ≤ (1 / Real.pi) * (T * |x|) := by
      gcongr
      exact integral_abs_truncatedPerronIntegrand_le hT
    _ = (T * |x|) / Real.pi := by ring

end AnalyticNumberTheory.LargeSieve

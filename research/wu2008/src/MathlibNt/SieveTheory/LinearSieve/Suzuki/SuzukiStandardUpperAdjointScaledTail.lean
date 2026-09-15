/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjoint

/-!
# The scaled Laplace tail of Suzuki's standard upper adjoint

The change of variables `u = s * x` rewrites `s * p(s)` as the integral of
`exp (-u - Ein (u / s))` over the positive half-line.  Dominated convergence,
using `0 ≤ Ein` there, then gives the limit `1`.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory Set

noncomputable section

/-- The elementary large-parameter Laplace asymptotic needed at infinity. -/
def SuzukiStandardUpperAdjointScaledTail : Prop :=
  Tendsto (fun s : ℝ => s * suzukiStandardUpperAdjoint s) atTop (nhds 1)

/-- Suzuki's genuine Laplace-integral standard upper adjoint has the elementary
scaled tail `s * p(s) → 1`. -/
theorem suzukiStandardUpperAdjoint_scaledTail :
    SuzukiStandardUpperAdjointScaledTail := by
  change Tendsto (fun s : ℝ => s * suzukiStandardUpperAdjoint s) atTop (nhds 1)
  let F : ℝ → ℝ → ℝ := fun s u => Real.exp (-u - suzukiEin (u / s))
  let bound : ℝ → ℝ := fun u => Real.exp (-u)
  have hbound : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0)
    exact integrableOn_exp_neg_Ioi 0
  have hmeas : ∀ᶠ s : ℝ in atTop,
      AEStronglyMeasurable (F s) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with s
    apply AEStronglyMeasurable.restrict
    dsimp only [F]
    exact (Real.continuous_exp.comp
      (continuous_neg.sub (continuous_suzukiEin.comp
        (continuous_id.div_const s)))).aestronglyMeasurable
  have hdom : ∀ᶠ s : ℝ in atTop, ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖F s u‖ ≤ bound u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp only [F, bound]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hEin : 0 ≤ suzukiEin (u / s) :=
      suzukiEin_nonneg (div_nonneg (le_of_lt hu) hs.le)
    linarith
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun s : ℝ => F s u) atTop (nhds (bound u)) := by
    filter_upwards with u
    have hdiv : Tendsto (fun s : ℝ => u / s) atTop (nhds 0) :=
      tendsto_id.const_div_atTop u
    have hEin : Tendsto (fun s : ℝ => suzukiEin (u / s)) atTop
        (nhds (suzukiEin 0)) :=
      continuous_suzukiEin.continuousAt.tendsto.comp hdiv
    have hneg_u : Tendsto (fun _ : ℝ => -u) atTop (nhds (-u)) :=
      tendsto_const_nhds
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hneg_u.sub hEin)
    change Tendsto (fun s : ℝ => Real.exp (-u - suzukiEin (u / s))) atTop
      (nhds (Real.exp (-u - suzukiEin 0))) at hexp
    simpa only [F, bound, suzukiEin, intervalIntegral.integral_same, sub_zero] using hexp
  have hint : Tendsto (fun s : ℝ => ∫ u : ℝ in Ioi 0, F s u)
      atTop (nhds (∫ u : ℝ in Ioi 0, bound u)) :=
    tendsto_integral_filter_of_dominated_convergence bound hmeas hdom hbound hpoint
  have hchange : ∀ᶠ s : ℝ in atTop,
      s * suzukiStandardUpperAdjoint s = ∫ u : ℝ in Ioi 0, F s u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hcomp := integral_comp_mul_left_Ioi (F s) 0 hs
    have hfun : (fun x : ℝ => F s (s * x)) =
        (fun x : ℝ => Real.exp (-s * x - suzukiEin x)) := by
      funext x
      dsimp only [F]
      congr 2
      · ring
      · rw [mul_div_cancel_left₀ x hs.ne']
    rw [hfun] at hcomp
    rw [suzukiStandardUpperAdjoint, hcomp]
    simp only [mul_zero, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have htail := hint.congr' (Filter.EventuallyEq.symm hchange)
  simpa only [bound, integral_exp_neg_Ioi_zero] using htail


end

end MathlibNt.SieveTheory

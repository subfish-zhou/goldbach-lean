import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabTailLimit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Abel convergence for the literal Buchstab Laplace integral.
Only the positive-ray bounds and the proved tail limit are used. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real LiLiuPrereqBuchstab
open scoped Topology

/-- The scaled integral, with its exact moving lower endpoint. -/
theorem buchstabLaplace_scaled {z : ℝ} (hz : 0 < z) :
    z * buchstabLaplace z =
      ∫ v : ℝ in Ioi z, buchstab (v / z) * exp (-v) := by
  have h := integral_comp_mul_left_Ioi'
    (fun v : ℝ => buchstab (v / z) * exp (-v)) 1 hz
  simpa only [smul_eq_mul, mul_one, mul_div_cancel_left₀ _ hz.ne',
    neg_mul, buchstabLaplace] using h

/-- The fixed-domain integrand retains the cutoff before evaluating any bound. -/
noncomputable def buchstabAbelKernel (z v : ℝ) : ℝ :=
  (Ioi z).indicator (fun v : ℝ => buchstab (v / z) * exp (-v)) v

theorem buchstabAbelKernel_measurable (z : ℝ) :
    AEStronglyMeasurable (buchstabAbelKernel z) (volume.restrict (Ioi 0)) := by
  exact ((continuous_buchstab.comp (continuous_id.div_const z)).mul
    (continuous_exp.comp continuous_neg)).aestronglyMeasurable.indicator measurableSet_Ioi

theorem buchstabAbelKernel_bound {z : ℝ} (hz : 0 < z) (v : ℝ) :
    ‖buchstabAbelKernel z v‖ ≤ exp (-v) := by
  by_cases hv : v ∈ Ioi z
  · have hu : 1 ≤ v / z := (le_div_iff₀ hz).2 (by simpa using hv.le)
    rw [buchstabAbelKernel, indicator_of_mem hv, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (buchstab_nonneg hu) (exp_pos _).le)]
    exact mul_le_of_le_one_left (exp_pos _).le (buchstab_le_one hu)
  · rw [buchstabAbelKernel, indicator_of_notMem hv, norm_zero]
    exact (exp_pos _).le

theorem buchstabAbelKernel_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (buchstabAbelKernel z) (Ioi 0) := by
  have hi : IntegrableOn (fun v : ℝ => exp (-v)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  exact hi.mono' (buchstabAbelKernel_measurable z)
    (Eventually.of_forall (buchstabAbelKernel_bound hz))

/-- The moving domain is realized on one fixed positive ray. -/
theorem buchstabLaplace_scaled_fixed {z : ℝ} (hz : 0 < z) :
    z * buchstabLaplace z = ∫ v : ℝ in Ioi 0, buchstabAbelKernel z v := by
  simp only [buchstabAbelKernel]
  rw [buchstabLaplace_scaled hz,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (Ioi_subset_Ioi hz.le)]

/-- Each positive fixed coordinate escapes to infinity as the parameter decreases to zero. -/
theorem buchstabAbelKernel_tendsto {v : ℝ} (hv : 0 < v) :
    Tendsto (fun z : ℝ => buchstabAbelKernel z v) (𝓝[>] 0)
      (𝓝 (buchstabTailLimit * exp (-v))) := by
  have hdiv : Tendsto (fun z : ℝ => v / z) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hv
  have h := (tendsto_buchstab_tail_limit.comp hdiv).mul_const (exp (-v))
  apply h.congr'
  filter_upwards [(eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds] with z hz
  exact (indicator_of_mem (show v ∈ Ioi z from hz)
    (fun w : ℝ => buchstab (w / z) * exp (-w))).symm

/-- Abel's endpoint for the actual integral, with no additional analytic hypotheses. -/
theorem tendsto_mul_buchstabLaplace_zero :
    Tendsto (fun z : ℝ => z * buchstabLaplace z) (𝓝[>] 0) (𝓝 buchstabTailLimit) := by
  have hi : IntegrableOn (fun v : ℝ => exp (-v)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := buchstabAbelKernel) (f := fun v => buchstabTailLimit * exp (-v))
    (fun v : ℝ => exp (-v))
    (Eventually.of_forall buchstabAbelKernel_measurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact Eventually.of_forall (buchstabAbelKernel_bound hz)) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact buchstabAbelKernel_tendsto hv)
  have he : (∫ v : ℝ in Ioi 0, buchstabTailLimit * exp (-v)) = buchstabTailLimit := by
    rw [integral_const_mul]
    have hexp := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (0 : ℝ)
    simpa using congrArg (buchstabTailLimit * ·) hexp
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (buchstabLaplace_scaled_fixed hz).symm

end Wu2008DoubleSieve.SecondFunctionalJointTail

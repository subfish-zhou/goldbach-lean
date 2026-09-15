import WE04ContinuousCell

noncomputable section
namespace WuTarget.E04Continuous
open Set MeasureTheory QuarterTrim NodeExtension ActualNineFeedback W01Continuous
open scoped Classical

def surplusDensity (x : Fin 9 → ℝ) (v : ℝ × ℝ) : ℝ :=
  continuousUniform x 0 v - DirectFiniteF6.uniform (matrixApply transferMatrix x) 0 v

theorem surplusDensity_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Integrable (surplusDensity x) :=
  (continuousUniform_integrable hx le_rfl).sub (DirectFiniteF6.uniform_integrable _ le_rfl)

theorem surplusDensity_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (v : ℝ × ℝ) : 0 ≤ surplusDensity x v := by
  unfold surplusDensity continuousUniform DirectFiniteF6.uniform
  split_ifs with hv
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right
      (old_profile_le_continuous hx (u_bounds hv))
      (DirectFiniteF6.denominator_bounds hv).1.le)
  · norm_num

theorem net_integral {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (continuousGain x-W01.lowGain x)/4 = ∫ v, surplusDensity x v := by
  unfold surplusDensity
  rw [integral_sub (continuousUniform_integrable hx le_rfl)
    (DirectFiniteF6.uniform_integrable _ le_rfl)]
  unfold continuousGain continuousGamma W01.lowGain DirectFiniteF6.Gamma
  ring

theorem rectangle_measurable : MeasurableSet rectangle :=
  measurableSet_Icc.prod measurableSet_Icc

theorem rectangle_volume : volume.real rectangle = (1/500000 : ℝ) := by
  change (volume.prod volume).real
    (Icc (1/10 : ℝ) (51/500) ×ˢ Icc (123/500 : ℝ) (247/1000)) = _
  rw [measureReal_prod_prod,Real.volume_real_Icc,Real.volume_real_Icc]
  norm_num

theorem surplus_linear {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x 0/44000 ≤ (continuousGain x-W01.lowGain x)/4 := by
  have hi : Integrable (rectangle.indicator (fun _ : ℝ × ℝ => 125*x 0/11)) :=
    (integrable_indicator_iff rectangle_measurable).mpr
      (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)
  have hm := integral_mono hi (surplusDensity_integrable hx) (fun v => by
    by_cases hv : v ∈ rectangle
    · rw [indicator_of_mem hv]
      exact rectangle_kernel_surplus hx hv
    · rw [indicator_of_notMem hv]
      exact surplusDensity_nonneg hx v)
  rw [integral_indicator_const _ rectangle_measurable,rectangle_volume,smul_eq_mul] at hm
  rw [net_integral hx]
  linarith only [hm]

end WuTarget.E04Continuous

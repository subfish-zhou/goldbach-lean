import HighConsumerProfile

namespace WuTarget.W15
open Real Set MeasureTheory QuarterTrim Wu08G6High Wu2008DoubleSieve
open scoped Classical
noncomputable section

def highDensityFloor : ℝ :=
  (546 / (1327 * 20000)) / (alpha * (1/4 - 2*alpha) / 2)

def highFloor : ℝ := 2 * highDensityFloor * (1/4 - 3*alpha)^2

theorem high_parameter_upper {x y : ℝ} (h : (x,y) ∈ highDomain) :
    u x y ≤ 927/400 := by
  have hx := ((high_iff x y).mp h).1.1
  have hy := ((high_iff x y).mp h).2.1
  norm_num [u, alpha] at hx ⊢
  linarith

theorem high_denominator_upper {x y : ℝ} (h : (x,y) ∈ highDomain) :
    x*y*(1/2-x-y) ≤ alpha * (1/4-2*alpha) / 2 := by
  obtain ⟨hx,hy⟩ := (high_iff x y).mp h
  have hx0 : 0 ≤ x := alpha_pos.le.trans hx.1
  have hfirst : y*(1/2-x-y) ≤ (1/4)*(1/4-x) := by
    nlinarith only [mul_nonneg (by linarith [hy.1] : 0 ≤ y-1/4)
      (by linarith [hy.1] : 0 ≤ x+y-1/4)]
  have hsecond : x*(1/4-x) ≤ (1/4-2*alpha)*(2*alpha) := by
    have hb : 0 ≤ 1/4-(1/4-2*alpha)-x := by
      norm_num [alpha] at hx ⊢
      linarith [hx.2]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2) hb]
  nlinarith only [mul_le_mul_of_nonneg_left hfirst hx0, hsecond]

theorem high_correction_lower {x y : ℝ} (h : (x,y) ∈ highDomain) :
    546 / (1327 * 20000) ≤ PositiveH.lowerCorrection (u x y) := by
  have hu := (HighConsumer.original_high_parameters h).1
  have hm := HighConsumer.correction_antitone (by linarith : 1 < u x y)
    (high_parameter_upper h)
  have hl := HighSixPhase5.log_lower (by norm_num : (1 : ℝ) ≤ 800/527)
  norm_num [PositiveH.lowerCorrection] at hm hl ⊢
  linarith only [hm,hl]

theorem high_kernel_lower (v : ℝ × ℝ) :
    highDomain.indicator (fun _ => highDensityFloor) v ≤ HighConsumer.highGainKernel v := by
  by_cases hv : v ∈ highDomain
  · rw [indicator_of_mem hv, HighConsumer.highGainKernel, indicator_of_mem hv]
    have hd := (published_denominator hv.1).1
    apply le_trans _ (div_le_div_of_nonneg_right (high_correction_lower hv) hd.le)
    exact div_le_div_of_nonneg_left (by norm_num) hd (high_denominator_upper hv)
  · simp only [indicator_of_notMem hv, HighConsumer.highGainKernel]
    rw [indicator_of_notMem hv]

theorem high_constant_integrable (c : ℝ) :
    Integrable (highDomain.indicator (fun _ => c)) := by
  have hsub : highDomain ⊆
      Icc alpha (1/4-2*alpha) ×ˢ Icc (1/4) (1/2-3*alpha) := by
    intro v hv
    obtain ⟨hx,hy⟩ := (high_iff v.1 v.2).mp hv
    exact ⟨hx,hy.1.le,by linarith [hy.2,hx.1]⟩
  apply (integrable_indicator_iff high_measurable).mpr
  exact (continuousOn_const.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set hsub

theorem high_constant_integral (c : ℝ) :
    (∫ v : ℝ × ℝ, highDomain.indicator (fun _ => c) v) =
      c * (1/4-3*alpha)^2 / 2 := by
  rw [show (∫ v : ℝ × ℝ, highDomain.indicator (fun _ => c) v) =
      ∫ x, ∫ y, highDomain.indicator (fun _ => c) (x,y) from
    integral_prod _ (high_constant_integrable c)]
  have hs : Function.support (fun x => ∫ y, highDomain.indicator (fun _ => c) (x,y)) ⊆
      Icc alpha (1/4-2*alpha) := by
    intro x hx
    by_contra hn
    apply hx
    have he : (fun y => highDomain.indicator (fun _ => c) (x,y)) = 0 := by
      funext y
      exact indicator_of_notMem (fun hv => hn ((high_iff x y).mp hv).1) _
    rw [he]
    simp
  rw [truncatedSixthMass_integral_eq_interval high_x_bounds hs]
  have he : (∫ x in alpha..(1/4-2*alpha),
      ∫ y, highDomain.indicator (fun _ => c) (x,y)) =
      ∫ x in alpha..(1/4-2*alpha), ((1/4-2*alpha)-x)*c := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le high_x_bounds] at hx
    have hf : (fun y => highDomain.indicator (fun _ => c) (x,y)) =
        (Ioc (1/4) (1/2-2*alpha-x)).indicator (fun _ => c) := by
      funext y
      simp only [indicator, high_iff, hx, true_and]
    rw [hf, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx.2]),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he]
  have hd (x : ℝ) : HasDerivAt
      (fun t : ℝ => ((1/4-2*alpha)*t-t^2/2)*c) (((1/4-2*alpha)-x)*c) x := by
    convert (((hasDerivAt_id x).const_mul (1/4-2*alpha)).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).mul_const c using 1 <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => ((1/4-2*alpha)-x)*c)).intervalIntegrable _ _)]
  ring

theorem highGain_lower : highFloor ≤ HighConsumer.highGain := by
  have h := integral_mono (high_constant_integrable highDensityFloor)
    HighConsumer.highGain_integrable high_kernel_lower
  rw [high_constant_integral] at h
  unfold highFloor HighConsumer.highGain
  linarith only [h]

theorem highFloor_positive : 0 < highFloor := by
  norm_num [highFloor, highDensityFloor, alpha]

end
end WuTarget.W15

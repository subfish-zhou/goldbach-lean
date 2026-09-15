import Hf4ActualOuter

noncomputable section
namespace Hf4Actual
open Real Set MeasureTheory NodeExtension SigmaVariableFull SigmaVariableOuterPayment
open OriginalProfileSigmaPayment FirstFeedbackIntegrals
open scoped Interval BigOperators

theorem sigma_upper {t : ℝ} (ht : t ∈ Icc 1 3) :
    sigma 3 (t+2) (t+1) ≤ innerMass t+(1/24000:ℝ) := by
  have hi := SigmaVariableFull.density_integrable ht.1
  have hm := intervalIntegral.integral_mono_on (by linarith [ht.1] : (3:ℝ) ≤ t+2)
    (sigma_integrable (by norm_num) (by linarith [ht.1]) (by linarith [ht.1] : 0 < t+1))
    (hi.add intervalIntegrable_const) (show ∀ v ∈ Icc (3:ℝ) (t+2),
      log ((t+1)/(v-1))/v ≤ density t v+(1/48000:ℝ) from by
      intro v hv
      have hx := SigmaVariableFull.argument_bounds ht.1 hv
      have hl := log_error_big ⟨hx.1,hx.2.trans (by linarith [ht.2])⟩
      have hd : (log (argument t v)-RemainingHf.basicLower (argument t v))/v ≤ (1/48000:ℝ) := by
        apply (div_le_iff₀ (by linarith [hv.1] : 0 < v)).mpr
        linarith only [hl,hv.1]
      rw [sub_div] at hd
      unfold density argument at *
      linarith only [hd])
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    SigmaVariableFull.density_integral ht,intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  change sigma 3 (t+2) (t+1) ≤ innerMass t+(t+2-3)*(1/48000) at hm
  linarith only [hm,ht.2]

theorem sigma_weight_upper {t : ℝ} (ht : t ∈ Icc 1 3) :
    sigma 3 (t+2) (t+1)/t ≤ paidWeight t+(1/1250+1/24000:ℝ) := by
  have h := sigma_upper ht
  have hd : (sigma 3 (t+2) (t+1)-innerMass t)/t ≤ (1/24000:ℝ) := by
    apply (div_le_iff₀ (by linarith [ht.1] : 0 < t)).mpr
    linarith only [h,ht.1]
  have ho := outer_weight_upper ht
  unfold SigmaVariableFull.weight at ho
  rw [endpointMass_eq ht] at ho
  rw [sub_div] at hd
  linarith only [ho,hd]

theorem profile_mass_cap : (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t) ≤ (1/25:ℝ) := by
  have he := profile_integral_cells NineFeedbackStrength.originalH le_rfl
    (by norm_num [upperNode] : (1:ℝ) ≤ upperNode 0)
    (show ContinuousOn (fun _ : ℝ => (1:ℝ)) (uIcc 1 3) from continuous_const.continuousOn)
  simp only [mul_one] at he
  rw [he]
  norm_num [Fin.sum_univ_succ,NineFeedbackStrength.originalH,cellLeft,upperLeft,upperNode]

theorem weighted_transfer {f g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : IntervalIntegrable (fun t => nineProfile NineFeedbackStrength.originalH t*f t) volume 1 3)
    (hg : IntervalIntegrable (fun t => nineProfile NineFeedbackStrength.originalH t*g t) volume 1 3)
    (hfg : ∀ t ∈ Icc (1:ℝ) 3, f t ≤ g t+c) :
    (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t*f t) ≤
      (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t*g t)+c/25 := by
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  have hm := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 3) hf (hg.add (hp.const_mul c))
    (show ∀ t ∈ Icc (1:ℝ) 3,
      nineProfile NineFeedbackStrength.originalH t*f t ≤
      nineProfile NineFeedbackStrength.originalH t*g t+c*nineProfile NineFeedbackStrength.originalH t from by
      intro t ht
      have hh := mul_le_mul_of_nonneg_left (hfg t ht)
        (nineProfile_nonneg CoupledIntegralRecovery.originalH_nonneg t)
      nlinarith only [hh])
  rw [intervalIntegral.integral_add hg (hp.const_mul c),intervalIntegral.integral_const_mul] at hm
  have hcap := mul_le_mul_of_nonneg_left profile_mass_cap hc
  linarith only [hm,hcap]

theorem actual_numerator_upper :
    (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1)) ≤
    SigmaActualBlockSeparable.endpointNumerator NineFeedbackStrength.originalH+(1/31250+1/600000:ℝ) := by
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  have hs : IntervalIntegrable (fun t => nineProfile NineFeedbackStrength.originalH t*(sigma 3 (t+2) (t+1)/t)) volume 1 3 := by
    convert (profile_div_integrable hp).mul_continuousOn original_sigma_continuous using 1
    ext t
    ring
  have h := weighted_transfer (by norm_num : (0:ℝ) ≤ 1/1250+1/24000) hs
    (hp.mul_continuousOn paidWeight_continuous) (fun _ ht => sigma_weight_upper ht)
  rw [← SigmaActualBlockSeparable.endpointNumerator_eq_integral] at h
  have hc : ((1/1250+1/24000:ℝ)/25) = 1/31250+1/600000 := by norm_num
  rw [hc] at h
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using h

end Hf4Actual

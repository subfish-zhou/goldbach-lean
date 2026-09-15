import Hf4ActualNumerator

noncomputable section
namespace Hf4Actual
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open scoped Interval BigOperators

theorem true_D0_upper : D0 ≤ D0FullDensity.dPaid+(1/750000:ℝ) := by
  have hi : IntervalIntegrable D0FullDensity.density volume 3 5 :=
    D0FullDensity.density_continuous.intervalIntegrable
  have hm := intervalIntegral.integral_mono_on (by norm_num : (3:ℝ) ≤ 5)
    (sigma_integrable (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 4))
    (hi.add intervalIntegrable_const) (show ∀ v ∈ Icc (3:ℝ) 5,
      log (4/(v-1))/v ≤ D0FullDensity.density v+(1/1500000:ℝ) from by
      intro v hv
      have hpos : 0 < v-1 := by linarith [hv.1]
      have hx : 4/(v-1) ∈ Icc (1:ℝ) 2 := by
        constructor
        · apply (le_div_iff₀ hpos).mpr
          linarith [hv.2]
        · apply (div_le_iff₀ hpos).mpr
          linarith [hv.1]
      have hl := (split_errors hx).1
      have hd : (log (4/(v-1))-RemainingHf.splitLower (4/(v-1)))/v ≤ (1/1500000:ℝ) := by
        apply (div_le_iff₀ (by linarith [hv.1] : 0 < v)).mpr
        linarith only [hl,hv.1]
      rw [sub_div] at hd
      unfold D0FullDensity.density
      linarith only [hd])
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    D0FullDensity.density_integral,intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  change D0 ≤ D0FullDensity.fullMass+(5-3)*(1/1500000) at hm
  rw [← Hf4DE.dPaid_eq_fullMass] at hm
  linarith only [hm]

theorem true_D0_cap : D0 ≤ (171695/1000000:ℝ) := by
  linarith only [true_D0_upper,Hf4DE.dPaid_bounds.2]

theorem e_paid_integral :
    (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t*TerminalE.density t) =
      TerminalECells.mass NineFeedbackStrength.originalH := by
  rw [profile_integral_cells NineFeedbackStrength.originalH le_rfl
    (by norm_num [upperNode]) (TerminalE.density_continuous le_rfl (by norm_num))]
  unfold TerminalECells.mass
  apply Finset.sum_congr rfl
  intro k _
  have he : cellLeft 1 k = upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he,TerminalE.density_integral (SigmaEndpointPayment.original_cell_bounds k).1
    (SigmaEndpointPayment.original_cell_bounds k).2.1]

theorem actual_e_upper :
    (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*log ((t+1)/2)) ≤
      TerminalECells.mass NineFeedbackStrength.originalH+(1/12500000:ℝ) := by
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  have hw : ContinuousOn (fun t : ℝ => log ((t+1)/2)/t) (uIcc 1 3) := by
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hm := weighted_transfer (by norm_num : (0:ℝ) ≤ 1/500000)
    (hp.mul_continuousOn hw)
    (hp.mul_continuousOn (TerminalE.density_continuous le_rfl (by norm_num)))
    (show ∀ t ∈ Icc (1:ℝ) 3, log ((t+1)/2)/t ≤ TerminalE.density t+(1/500000:ℝ) from by
      intro t ht
      have hx : (t+1)/2 ∈ Icc (1:ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
      have hh := (split_errors hx).1
      have hd : (log ((t+1)/2)-RemainingHf.splitLower ((t+1)/2))/t ≤ (1/500000:ℝ) := by
        apply (div_le_iff₀ (by linarith [ht.1] : 0 < t)).mpr
        linarith only [hh,ht.1]
      rw [sub_div] at hd
      unfold TerminalE.density
      linarith only [hd])
  rw [e_paid_integral] at hm
  have hc : (1/500000:ℝ)/25 = 1/12500000 := by norm_num
  rw [hc] at hm
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using hm

end Hf4Actual

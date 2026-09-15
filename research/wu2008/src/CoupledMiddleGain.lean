import CoupledMiddleAssembly

namespace CoupledMiddleGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment CoupledHGateRecovery
open scoped Interval BigOperators
noncomputable section

/-- Strict finite gain certified without evaluating a logarithm. -/
def middleGainFloor (p : SecondFunctionalParameters) : ℝ :=
  log (middleRatio p)*(log (lowerSwitch p)-log (upperSwitch p)-
    (lowerSwitch p-upperSwitch p)/lowerSwitch p)

theorem logarithmic_gap_pos {a b : ℝ} (ha : 0<a) (hab : a<b) :
    0<log b-log a-(b-a)/b := by
  have hb : 0<b := ha.trans hab
  have hratio : a/b<1 := (div_lt_one hb).mpr hab
  have h := log_lt_sub_one_of_pos (div_pos ha hb) (ne_of_lt hratio)
  rw [log_div ha.ne' hb.ne'] at h
  have he : (b-a)/b=1-a/b := by field_simp
  rw [he]
  linarith only [h]

theorem middleGainFloor_pos (i : Fin 4) : 0< middleGainFloor (coupledRow i) := by
  obtain ⟨ha,hab,_,_⟩ := original_middle_geometry i
  exact mul_pos (middle_log_pos (coupledRow_geometry i).1)
    (logarithmic_gap_pos (by linarith) hab)

theorem middleGainFloor_le (i : Fin 4) : middleGainFloor (coupledRow i)≤ middleGain (coupledRow i) := by
  have hp := (coupledRow_geometry i).1
  obtain ⟨ha,hab,hbn,_⟩ := original_middle_geometry i
  have hb : lowerSwitch (coupledRow i)≤3 :=
    hbn.trans (by norm_num [upperNode])
  have he := kernelEndpoint_le hp .gammaEight ha hb ⟨hab.le,le_rfl⟩
  rw [middle_kernel_eq hp ha hb ⟨hab.le,le_rfl⟩] at he
  have hm := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hab.le)
  unfold middleGainFloor middleGain middlePayment oldMiddleBox
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem middleGain_pos (i : Fin 4) : 0< middleGain (coupledRow i) :=
  (middleGainFloor_pos i).trans_le (middleGainFloor_le i)

theorem original_four_quantitative (i : Fin 4) :
    restoredLower (coupledRow i) NineFeedbackStrength.originalH+
      NineFeedbackStrength.originalH 0*middleGainFloor (coupledRow i)/5≤
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (middleGainFloor_le i) (CoupledIntegralRecovery.originalH_nonneg 0))
    (by norm_num : (0:ℝ)≤5)
  have hc := original_four_middle_restored i
  unfold middleRestoredLower at hc
  linarith only [h,hc]

theorem original_four_strict_middle_gain (i : Fin 4) :
    restoredLower (coupledRow i) NineFeedbackStrength.originalH<
      middleRestoredLower (coupledRow i) NineFeedbackStrength.originalH := by
  have hz : 0<NineFeedbackStrength.originalH 0 := by norm_num [NineFeedbackStrength.originalH]
  have hg : 0<NineFeedbackStrength.originalH 0*middleGain (coupledRow i)/5 :=
    div_pos (mul_pos hz (middleGain_pos i)) (by norm_num)
  exact lt_add_of_pos_right _ hg

/-- The real shared aProfile is retained for independent sigma strengthening. -/
def actualProfileLower (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*aProfile (nineProfile z)+CoupledFiniteAssembly.remainder p z+
    (densityFinite p z+z 0*gatePayment p+z 0*middleGain p)/5

theorem actualProfileLower_le (i : Fin 4) {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    actualProfileLower (coupledRow i) z≤coupledFeedback (coupledRow i) z := by
  have hd := div_le_div_of_nonneg_right (density_replace_middle i hz) (by norm_num : (0:ℝ)≤5)
  have hc := CoupledFiniteAssembly.analytic_lower (coupledRow_geometry i) hz
  unfold actualProfileLower
  linarith only [hd,hc]

theorem actualProfileLower_decomposition (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) :
    actualProfileLower p z=middleRestoredLower p z+
      CoupledFiniteAssembly.aCoefficient p*(aProfile (nineProfile z)-OriginalProfileSigmaPayment.aFiniteLower z) := by
  unfold actualProfileLower middleRestoredLower restoredLower CoupledFullyFinite.lower
  ring

/-- Quantitative improvement of the actual original hc margin, not a replacement target. -/
theorem original_hc_margin (i : Fin 4) :
    NineFeedbackStrength.publication (i.castAdd 5)+
      restoredLower (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5)+
      NineFeedbackStrength.originalH 0*middleGainFloor (coupledRow i)/5≤
    NineFeedbackStrength.publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5) := by
  linarith only [original_four_quantitative i]

/-- The actual profile correction and both recovered domains enter hc only once. -/
theorem original_hc_actual_profile_margin (i : Fin 4) :
    NineFeedbackStrength.publication (i.castAdd 5)+
      actualProfileLower (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5)≤
    NineFeedbackStrength.publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5) := by
  linarith only [actualProfileLower_le i CoupledIntegralRecovery.originalH_nonneg]

end
end CoupledMiddleGateRecovery

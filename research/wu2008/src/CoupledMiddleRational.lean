import CoupledMiddleGain

namespace CoupledMiddleGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment CoupledHGateRecovery
open scoped Interval BigOperators
noncomputable section

/-- Exactly one permitted split of the original FTC argument b/a, never its factors. -/
theorem logarithmic_gap_rational {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (b-a)^2/(2*b*(a+b))≤log b-log a-(b-a)/b := by
  have hab : 0<a+b := add_pos ha hb
  have hf : 0<(a+b)/(2*a) := div_pos hab (mul_pos (by norm_num) ha)
  have hg : 0<2*b/(a+b) := div_pos (mul_pos (by norm_num) hb) hab
  have he : ((a+b)/(2*a))*(2*b/(a+b))=b/a := by field_simp
  have hl : log b-log a=log ((a+b)/(2*a))+log (2*b/(a+b)) := by
    rw [← log_mul hf.ne' hg.ne',he,log_div hb.ne' ha.ne']
  have h1 := reciprocal_log_lower hf
  have h2 := reciprocal_log_lower hg
  have hid : (1-1/((a+b)/(2*a)))+(1-1/(2*b/(a+b)))-(b-a)/b=
      (b-a)^2/(2*b*(a+b)) := by
    field_simp
    ring
  rw [hl,← hid]
  linarith only [h1,h2]

/-- A positive rational expression, obtained without evaluating any logarithm. -/
def middleRationalGain (p : SecondFunctionalParameters) : ℝ :=
  (1-1/middleRatio p)*(lowerSwitch p-upperSwitch p)^2/
    (2*lowerSwitch p*(upperSwitch p+lowerSwitch p))

theorem middleRationalGain_le (i : Fin 4) : middleRationalGain (coupledRow i)≤ middleGain (coupledRow i) := by
  let p := coupledRow i
  have hp := (coupledRow_geometry i).1
  obtain ⟨ha,hab,_,_⟩ := original_middle_geometry i
  have ha0 : 0<upperSwitch p := by dsimp only [p]; linarith
  have hb0 : 0<lowerSwitch p := ha0.trans hab
  have hc1 : 1< middleRatio p := by
    unfold middleRatio
    apply (one_lt_div (by linarith [hp.two_lt_s,hp.mother.s_le_kappa3,
      hp.mother.kappa3_lt_kappa2] : 0<p.kappa2-1)).mpr
    linarith [hp.mother.kappa2_lt_kappa1]
  have hc0 : 0< middleRatio p := by linarith
  have hn : 0≤1-1/middleRatio p := by
    have h := (div_le_one hc0).mpr hc1.le
    linarith
  have hrat := logarithmic_gap_rational ha0 hb0
  have hlog := reciprocal_log_lower hc0
  have hr0 : 0≤(lowerSwitch p-upperSwitch p)^2/
      (2*lowerSwitch p*(upperSwitch p+lowerSwitch p)) := by positivity
  have hm := mul_le_mul hlog hrat hr0 (middle_log_pos hp).le
  have he : middleRationalGain p≤ middleGainFloor p := by
    unfold middleRationalGain middleGainFloor
    simpa only [mul_div_assoc] using hm
  exact he.trans (middleGainFloor_le i)

theorem middleRationalGain_pos (i : Fin 4) : 0< middleRationalGain (coupledRow i) := by
  let p := coupledRow i
  have hp := (coupledRow_geometry i).1
  obtain ⟨ha,hab,_,_⟩ := original_middle_geometry i
  have ha0 : 0<upperSwitch p := by dsimp only [p]; linarith
  have hb0 : 0<lowerSwitch p := ha0.trans hab
  have hc1 : 1< middleRatio p := by
    unfold middleRatio
    apply (one_lt_div (by linarith [hp.two_lt_s,hp.mother.s_le_kappa3,
      hp.mother.kappa3_lt_kappa2] : 0<p.kappa2-1)).mpr
    linarith [hp.mother.kappa2_lt_kappa1]
  have hn : 0<1-1/middleRatio p := by
    have h := (div_lt_one (by linarith : 0< middleRatio p)).mpr hc1
    linarith
  have hs : 0<(lowerSwitch p-upperSwitch p)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  exact div_pos (mul_pos hn hs) (by positivity)

/-- The original four hc margins now have an explicit rational improvement. -/
theorem original_four_rational_margin (i : Fin 4) :
    NineFeedbackStrength.publication (i.castAdd 5)+restoredLower (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5)+
      NineFeedbackStrength.originalH 0*middleRationalGain (coupledRow i)/5≤
    NineFeedbackStrength.publication (i.castAdd 5)+coupledFeedback (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5) := by
  have hg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (middleRationalGain_le i) (CoupledIntegralRecovery.originalH_nonneg 0))
    (by norm_num : (0:ℝ)≤5)
  have hc := original_four_middle_restored i
  unfold middleRestoredLower at hc
  linarith only [hg,hc]

/-- Positivity concerns the actual original H weight, not an arbitrary replacement vector. -/
theorem original_rational_increment_pos (i : Fin 4) :
    0<NineFeedbackStrength.originalH 0*middleRationalGain (coupledRow i)/5 := by
  have hz : 0<NineFeedbackStrength.originalH 0 := by norm_num [NineFeedbackStrength.originalH]
  exact div_pos (mul_pos hz (middleRationalGain_pos i)) (by norm_num)

end
end CoupledMiddleGateRecovery

import CompleteReciprocalKernel
import RetainedEndpointFeedback

namespace Wu2008DoubleSieve.Phase16
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11 Phase12
open Phase13 (κh κH κh_pos κH_pos H_retained_quadratic amplitude_endpoint_closed rhoEndpoint rhoEndpoint_bounds)
open Phase14 (q1 q2 poly poly_nonneg)
noncomputable section

/-- The whole actual numerator is compared once; the denominator is not truncated. -/
theorem actual_reciprocal_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc L0 (movingRight δ)) : amplitude δ*f0 t ≤ kernel δ t := by
  have hg := moving_geometry hδ hδhi
  have hts : t ∈ Icc (shapeLeft δ) ((1/2-δ)/2) := ⟨hg.2.1.trans ht.1,ht.2⟩
  have ht0 := lt_of_lt_of_le fixed_geometry.1 ht.1
  have hct : 0 < (1/2-δ)-t := by dsimp [movingRight] at ht; linarith [ht.2]
  have hc0 : 0 < 1/2-t := by linarith
  have hH := H_retained_quadratic hδ hδhi (shape_argument hδ hδhi hts)
  have he : amplitude δ*(κH+(25/468)*(23/5-argument δ t)^2+
      κh*(5/18)*(23/5-argument δ t)) = amplitude δ*poly (t-shapeLeft δ) := by
    unfold poly q1 q2 argument shapeLeft truncatedSixthLowerAlpha
    ring
  rw [he] at hH
  have hpoly := poly_mono (sub_nonneg.mpr ht.1)
    (show t-L0 ≤ t-shapeLeft δ by linarith only [hg.2.1])
  have hnum := mul_le_mul_of_nonneg_left hpoly (amplitude_nonneg hδ hδhi)
  have hp := mul_nonneg (amplitude_nonneg hδ hδhi) (poly_nonneg (sub_nonneg.mpr ht.1))
  have hd : t*((1/2-δ)-t) ≤ t*(1/2-t) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0.le
  unfold f0 kernel
  rw [← mul_div_assoc]
  exact (div_le_div₀ hp le_rfl (mul_pos ht0 hct) hd).trans
    ((div_le_div_iff_of_pos_right (mul_pos ht0 hct)).2 (hnum.trans hH))

/-- Drop the nonnegative left strip and retain the actual moving right endpoint. -/
theorem actual_quad_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*(∫ t in L0..movingRight δ, f0 t) ≤
      ∫ t in shapeLeft δ..movingRight δ, kernel δ t := by
  have hg := moving_geometry hδ hδhi
  have hs := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ shapeLeft δ :=
    (by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha).trans hs.1
  have hi1 := kernel_integrable hδ hδhi ha hg.2.1 hg.2.2.1.le
  have hi2 := kernel_integrable hδ hδhi (ha.trans hg.2.1) hg.2.2.1.le le_rfl
  have hn := intervalIntegral.integral_nonneg (μ := volume) hg.2.1
    (fun t ht => kernel_nonneg hδ hδhi (ha.trans ht.1) (ht.2.trans hg.2.2.1.le))
  have hm := intervalIntegral.integral_mono_on hg.2.2.1.le
    ((f0_integrable le_rfl hg.2.2.1.le hg.2.2.2.1).const_mul (amplitude δ)) hi2
    (fun t ht => actual_reciprocal_lower hδ hδhi ht)
  rw [intervalIntegral.integral_const_mul] at hm
  have he := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith only [hn,hm,he]

/-- Original tail and middle plus the single full reciprocal integral. -/
theorem three_piece_reciprocal_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)+
      amplitude δ*(∫ t in L0..movingRight δ, f0 t)+
      (16*amplitude δ*middleMass)*((2/5)*truncatedSixthLowerAlpha) ≤
      ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have hs := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi1 := kernel_integrable hδ hδhi ha hg.2.1.le (hg.2.2.1.le.trans hg.2.2.2)
  have hi2 := kernel_integrable hδ hδhi (ha.trans hg.2.1.le) hg.2.2.1.le hg.2.2.2
  have hi3 := kernel_integrable hδ hδhi (ha.trans hs.1) hg.2.2.2 le_rfl
  have htail : tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5) ≤
      ∫ t in truncatedSixthLowerAlpha..b0, kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => tailCoefficient δ*(t-a0)^4)
        volume truncatedSixthLowerAlpha b0 :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 4)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.1.le hi hi1
      (fun t ht => kernel_tail_lower hδ hδhi ht)
    rwa [quartic_integral] at hm
  have hmiddle := middle_integral_lower hδ hδhi
  have hlast := actual_quad_lower hδ hδhi
  change amplitude δ*(∫ t in L0..movingRight δ, f0 t) ≤ ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t at hlast
  have hadd12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith only [htail,hmiddle,hlast,hadd12,hadd123]

theorem actual_low_H_reciprocal_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    movingC δ*amplitude δ ≤ gainH34 δ/4 := by
  have hi := three_piece_reciprocal_lower hδ hδhi
  have he : movingC δ*amplitude δ = Ctail*amplitude δ+Cmid*amplitude δ+
      2*(amplitude δ*(∫ t in L0..movingRight δ, f0 t)) := by unfold movingC; ring
  rw [he,Ctail_identity,Cmid_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

def g16 : ℝ := C16*sourceP/(1-rhoEndpoint)
def B16 : ℝ := M*sourceP/(1-rhoEndpoint)+(100/49)*C16*envelopeE/(1-rhoEndpoint)

theorem g16_pos : 0 < g16 :=
  div_pos (mul_pos C16_pos (by norm_num [sourceP])) (sub_pos.mpr rhoEndpoint_bounds.2)

theorem B16_pos : 0 < B16 := by
  unfold B16
  exact add_pos (div_pos (mul_pos M_pos (by norm_num [sourceP])) (sub_pos.mpr rhoEndpoint_bounds.2))
    (div_pos (mul_pos (mul_pos (by norm_num) C16_pos) (by norm_num [envelopeE]))
      (sub_pos.mpr rhoEndpoint_bounds.2))

/-- Positive moving coefficients pay the amplitude from below; no upper amplitude bound. -/
theorem gain16_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g16-B16*δ ≤ gainH34 δ/4 := by
  have hc := movingC_bounds hδ hδhi
  have hd := sub_pos.mpr rhoEndpoint_bounds.2
  have hp : 0 < sourceP := by norm_num [sourceP]
  have he : 0 < envelopeE := by norm_num [envelopeE]
  have hpen : 0 ≤ penalty δ := by
    unfold penalty
    exact div_nonneg (by positivity) (by linarith)
  have hA := (mul_le_mul_of_nonneg_left (amplitude_endpoint_closed hδ hδhi) hc.1).trans
    (actual_low_H_reciprocal_lower hδ hδhi)
  have hP := mul_le_mul_of_nonneg_right hc.2.2 (div_pos hp hd).le
  have hE := mul_le_mul_of_nonneg_right hc.2.1 (mul_nonneg hpen (div_pos he hd).le)
  have hpenhi := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    (div_pos (mul_pos C16_pos he) hd).le
  have hrewrite : movingC δ*((sourceP-penalty δ*envelopeE)/(1-rhoEndpoint)) =
      movingC δ*(sourceP/(1-rhoEndpoint))-movingC δ*(penalty δ*(envelopeE/(1-rhoEndpoint))) := by ring
  rw [hrewrite] at hA
  unfold g16 B16
  simp only [div_eq_mul_inv] at hP hE hpenhi hA ⊢
  nlinarith only [hP,hE,hpenhi,hA]

end
end Wu2008DoubleSieve.Phase16

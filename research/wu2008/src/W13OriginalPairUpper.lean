import W13WeightedMoments

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass Wu08OriginalFourWeights

namespace WuTarget.W13

def c0Upper : ℝ := 1/alpha-FourLogAffine.l/beta
def a2 : ℝ := (4/7)*FourLogAffine.w*c0Upper/2
def a3 : ℝ := (4/7)*(c0Upper/6+FourLogAffine.w/(3*beta))
def a4 : ℝ := (4/7)/(8*beta)
def profile (x : ℝ) : ℝ := a2*tail 2 x+a3*tail 3 x+a4*tail 4 x

def pairUpper : ℝ := a2*momentUpper 2+a3*momentUpper 3+a4*momentUpper 4

theorem coefficients_positive : 0 < c0Upper ∧ 0 < a2 ∧ 0 < a3 ∧ 0 < a4 := by
  norm_num [c0Upper, a2, a3, a4, FourLogAffine.l, FourLogAffine.w,
    SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog,
    alpha, beta, lam, truncatedSixthLowerAlpha, truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem C0_le_upper : FourLogAffine.C0 ≤ c0Upper := by
  have hb := geometry.1.trans_le (geometry.2.1.trans geometry.2.2.1)
  exact sub_le_sub_left
    (div_le_div_of_nonneg_right FourLogAffine.fixed_log_bounds.2.1 hb.le) _

theorem outer_pair_upper {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x+regularOuter11 x ≤ profile x := by
  have hx0 := geometry.1.trans_le hx.1
  have hb := geometry.1.trans_le (geometry.2.1.trans geometry.2.2.1)
  have hE := FourLogAffine.ell_nonneg hx.1 hx.2
  have hC := FourLogAffine.C0_pos
  have hW := ClassicalLogFourBounds.log_caps.2.2.1
  have hw := hW.trans FourLogAffine.fixed_log_bounds.2.2.2.2
  have h3 := mul_le_mul_of_nonneg_right C0_le_upper (pow_nonneg hE 3)
  have h2 := mul_le_mul_of_nonneg_right C0_le_upper (pow_nonneg hE 2)
  have hten :
      (4/7)*(FourLogAffine.C0*FourLogAffine.ell x^3/6+
        FourLogAffine.ell x^4/(8*beta))/x ≤
      (4/7)*(c0Upper*FourLogAffine.ell x^3/6+
        FourLogAffine.ell x^4/(8*beta))/x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith only [h3]
  have hbracket :
      FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) ≤
      c0Upper*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) := by linarith only [h2]
  have hbracket0 :
      0 ≤ FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta) := by positivity
  have heleven := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul FourLogAffine.fixed_log_bounds.2.2.2.2 hbracket hbracket0 hw)
      (show (0 : ℝ) ≤ 4/7 by norm_num)) hx0.le
  have h10 := (FourLogAffine.outer10_upper hx.1 hx.2).trans hten
  have h11 := FourLogAffine.outer11_upper hx.1 hx.2
  simp only [profile, a2, a3, a4, tail, FourLogAffine.ell] at h10 h11 heleven ⊢
  ring_nf at h10 h11 heleven ⊢
  linarith only [h10, h11, heleven]

theorem profile_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable profile volume a b :=
  (((tail_continuousOn 2 ha hab).intervalIntegrable.const_mul a2).add
    ((tail_continuousOn 3 ha hab).intervalIntegrable.const_mul a3)).add
    ((tail_continuousOn 4 ha hab).intervalIntegrable.const_mul a4)

theorem weighted_profile_integrable :
    IntervalIntegrable (fun x => profile x/(1-x)) volume alpha cut := by
  convert (((weighted_tail_integrable 2).const_mul a2).add
    ((weighted_tail_integrable 3).const_mul a3)).add
    ((weighted_tail_integrable 4).const_mul a4) using 1
  funext x
  unfold profile
  ring

theorem profile_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, profile x) =
      a2*(∫ x in a..b, tail 2 x)+a3*(∫ x in a..b, tail 3 x)+
        a4*(∫ x in a..b, tail 4 x) := by
  have h2 := (tail_continuousOn 2 ha hab).intervalIntegrable (μ := volume)
  have h3 := (tail_continuousOn 3 ha hab).intervalIntegrable (μ := volume)
  have h4 := (tail_continuousOn 4 ha hab).intervalIntegrable (μ := volume)
  unfold profile
  rw [intervalIntegral.integral_add ((h2.const_mul a2).add (h3.const_mul a3))
    (h4.const_mul a4),
    intervalIntegral.integral_add (h2.const_mul a2) (h3.const_mul a3)]
  simp only [intervalIntegral.integral_const_mul]

theorem weighted_profile_integral :
    (∫ x in alpha..cut, profile x/(1-x)) =
      a2*(∫ x in alpha..cut, tail 2 x/(1-x))+
        a3*(∫ x in alpha..cut, tail 3 x/(1-x))+
        a4*(∫ x in alpha..cut, tail 4 x/(1-x)) := by
  have he : (fun x => profile x/(1-x)) =
      (fun x => a2*(tail 2 x/(1-x))+a3*(tail 3 x/(1-x))+
        a4*(tail 4 x/(1-x))) := by funext x; unfold profile; ring
  rw [he, intervalIntegral.integral_add
    (((weighted_tail_integrable 2).const_mul a2).add
      ((weighted_tail_integrable 3).const_mul a3))
    ((weighted_tail_integrable 4).const_mul a4),
    intervalIntegral.integral_add ((weighted_tail_integrable 2).const_mul a2)
      ((weighted_tail_integrable 3).const_mul a3)]
  simp only [intervalIntegral.integral_const_mul]

theorem original_pair_le_moments :
    original10+original11 ≤ a2*moment 2+a3*moment 3+a4*moment 4 := by
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  change IntervalIntegrable (fun x => regularOuter10 x/(1-x)) volume alpha cut at hs10
  change IntervalIntegrable (fun x => regularOuter11 x/(1-x)) volume alpha cut at hs11
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume) cut beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume) cut beta
  have hs := intervalIntegral.integral_mono_on geometry.2.1
    (hs10.add hs11) weighted_profile_integrable (fun x hx => by
      have hden : 0 ≤ 1-x := by linarith [hx.2, geometry.2.2.2]
      simpa only [add_div] using div_le_div_of_nonneg_right
        (outer_pair_upper ⟨hx.1, hx.2.trans geometry.2.2.1⟩) hden)
  have hl := intervalIntegral.integral_mono_on geometry.2.2.1
    (hl10.add hl11)
    (profile_integrable (geometry.1.trans_le geometry.2.1) geometry.2.2.1)
    (fun x hx => outer_pair_upper ⟨geometry.2.1.trans hx.1, hx.2⟩)
  rw [intervalIntegral.integral_add hs10 hs11, weighted_profile_integral] at hs
  rw [intervalIntegral.integral_add hl10 hl11,
    profile_integral (geometry.1.trans_le geometry.2.1) geometry.2.2.1] at hl
  unfold original10 original11 original moment
  dsimp only [cut] at hs hl ⊢
  ring_nf at hs hl ⊢
  linarith only [hs, hl]

theorem original_pair_upper : original10+original11 ≤ pairUpper := by
  have h2 := mul_le_mul_of_nonneg_left (moment_upper 2) coefficients_positive.2.1.le
  have h3 := mul_le_mul_of_nonneg_left (moment_upper 3) coefficients_positive.2.2.1.le
  have h4 := mul_le_mul_of_nonneg_left (moment_upper 4) coefficients_positive.2.2.2.le
  exact original_pair_le_moments.trans (add_le_add (add_le_add h2 h3) h4)

theorem pairUpper_lt : pairUpper < 21/20 := by
  norm_num [pairUpper, momentUpper, c0Upper, a2, a3, a4, h, d, k, cut,
    FourLogAffine.l, FourLogAffine.u, FourLogAffine.w,
    SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog,
    alpha, beta, lam, truncatedSixthLowerAlpha, truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem original_pair_lt : original10+original11 < 21/20 :=
  original_pair_upper.trans_lt pairUpper_lt

end WuTarget.W13

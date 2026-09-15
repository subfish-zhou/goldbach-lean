import MathlibNt.Wu2008DoubleSieve.GVariableQuadratic

namespace Wu2008DoubleSieve.GVariableCoefficient
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure FixedCoefficientHLowerEnclosure
open GVariableRecurrence GVariableIntegral GVariableQuadratic
open scoped Interval

noncomputable def exactGain : ℝ :=
  8*((2776/10125)*(affinePrimitive 5 (c 5)-affinePrimitive 5 a)+
    (56/243)*(affinePrimitive 4 (c 4)-affinePrimitive 4 (c 5))+
    (quadraticPrimitive s-quadraticPrimitive (c 4)))

/-- The original two G integrals: all three low pieces and the exact high piece. -/
theorem G_pair_variable_lower : Hbound+exactGain ≤
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s := by
  have h5 : a ≤ c 5 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 : s ≤ 1/3 := truncatedSixthLower_parameters.2.2.2.1.le
  have hseg5 := affine_segment (fun _ hu => upper_five_affine hu) le_rfl le_rfl
    (h54.trans (h4s.trans hs3)) h5
  have hseg4 := affine_segment (fun _ hu => upper_four_affine hu) h5 le_rfl
    (h4s.trans hs3) h54
  have hseg3 := quadratic_segment
  have hi5 := ClassicalSingleBounds.g_integrable le_rfl (h54.trans (h4s.trans hs3)) h5
  have hi4 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs3) h54
  have hi3 := ClassicalSingleBounds.g_integrable (h5.trans h54) hs3 h4s
  have hiH := ClassicalSingleBounds.g_integrable (h5.trans (h54.trans h4s)) le_rfl hs3
  have he1 := intervalIntegral.integral_add_adjacent_intervals hi5 hi4
  have he2 := intervalIntegral.integral_add_adjacent_intervals (hi5.trans hi4) hi3
  have he3 := intervalIntegral.integral_add_adjacent_intervals ((hi5.trans hi4).trans hi3) hiH
  have heH := ClassicalSingleBounds.high_integral_eq
  have hlogH : reciprocalPrimitive (1/3)-reciprocalPrimitive s = 2*log (6*a/s) := by
    have he := primitive_crossRatio (r := 1/3) (by norm_num) (by norm_num)
    have hes := primitive_crossRatio (r := s)
      (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
      (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    have hdiv := log_div (x := crossRatio (1/3)) (y := crossRatio s)
      (by norm_num [crossRatio,a,truncatedSixthLowerAlpha])
      (by norm_num [crossRatio,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    have hid : crossRatio (1/3)/crossRatio s = 6*a/s := by
      norm_num [crossRatio,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
    rw [hid] at hdiv
    linarith
  rw [← hlogH] at heH
  have hg1 : SingleUpperClassicalLimit.Glin (1/3) = 4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have hg2 : SingleUpperClassicalLimit.Glin s = 4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  rw [hg1,hg2]
  unfold Hbound exactGain
  linarith

noncomputable def rationalGain : ℝ :=
  8*((2776/10125)*affinePayment 5 a (c 5)+
    (56/243)*affinePayment 4 (c 5) (c 4)+quadraticPayment)

theorem rational_gain_lower : rationalGain ≤ exactGain := by
  have h5 := affine_payment_lower (j := 5) (l := a) (r := c 5) (by norm_num)
    (by norm_num [a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h4 := affine_payment_lower (j := 4) (l := c 5) (r := c 4) (by norm_num)
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h3 := quadratic_payment_lower
  unfold rationalGain exactGain
  linarith

theorem G_pair_rational_lower : FixedCoefficientHLowerEnclosure.rationalH+rationalGain ≤
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s :=
  (add_le_add rationalH_lower rational_gain_lower).trans G_pair_variable_lower

noncomputable def variableUpper : ℝ := FixedCoefficientHLowerEnclosure.rationalUpper-rationalGain

/-- Reassembled from actual original signed terms, not an assumed upper-bound wrapper. -/
theorem complete_variable_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ variableUpper := by
  have hb := base_upper
  have hf := FixedCoefficientLogMassEnclosure.fifth_log_upper
  have hs := FixedCoefficientLogMassEnclosure.sixth_log_upper
  have hp := FixedCoefficientLogMassEnclosure.positive_rational_upper
  have hg := G_pair_rational_lower
  have hj := FixedCoefficientJLowerEnclosure.weighted_J_lower
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient variableUpper
    FixedCoefficientHLowerEnclosure.rationalUpper
  linarith

theorem rational_gain_pos : 0 < rationalGain := by
  norm_num [rationalGain,affinePayment,quadraticPayment,c,lowerLog,upperLog,
    a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem strict_improvement : variableUpper < FixedCoefficientHLowerEnclosure.rationalUpper := by
  have h := rational_gain_pos
  unfold variableUpper
  linarith

#print axioms G_pair_variable_lower
#print axioms complete_variable_upper
#print axioms strict_improvement
end Wu2008DoubleSieve.GVariableCoefficient

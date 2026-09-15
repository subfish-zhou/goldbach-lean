import MathlibNt.Wu2008DoubleSieve.RefinedRetainedFTC

namespace Wu2008DoubleSieve.RetainedSixthCoefficient
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure
open scoped Interval

noncomputable def rationalFifth : ℝ := 2*densityConstant*(upperLog (b/a))^2

 theorem actual_fifth_upper : fifthPairFlin ≤ rationalFifth := by
  have hp := truncatedSixthLower_parameters
  have hb := hp.1.trans hp.2.1
  have hl := log_upper (t := b/a) ((le_div_iff₀ hp.1).2 (by linarith [hp.2.1]))
  rw [log_div hb.ne' hp.1.ne'] at hl
  have hn : 0 ≤ log b-log a := sub_nonneg.mpr (log_le_log hp.1 hp.2.1.le)
  have hs := mul_le_mul hl hl hn (hn.trans hl)
  have hc : 0 ≤ densityConstant := by norm_num [densityConstant,a,truncatedSixthLowerAlpha]
  have hh := mul_le_mul_of_nonneg_left hs hc
  have hf := FixedCoefficientLogMassEnclosure.fifth_log_upper
  unfold FixedCoefficientLogMassEnclosure.fifthLog rationalFifth at *
  nlinarith only [hf,hh]

noncomputable def rationalUpper : ℝ := baseBound+rationalFifth+RefinedRetainedFTC.rationalSixth+
  47/481250-FixedCoefficientHLowerEnclosure.rationalH-FixedCoefficientJLowerEnclosure.weightedRational

 theorem complete_rational_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := actual_fifth_upper
  have hs := RefinedRetainedFTC.actual_sixth_upper
  have hg := FixedCoefficientHLowerEnclosure.rationalH_lower.trans
    FixedCoefficientHLowerEnclosure.G_pair_H_lower
  have hj := FixedCoefficientJLowerEnclosure.weighted_J_lower
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
  linarith

 theorem literal_complete_upper :
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
    truncatedSixthLowerF6lin+47/481250-
    SingleUpperClassicalLimit.Glin (1/3)-SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ rationalUpper := complete_rational_upper

 theorem upper_improvement : rationalUpper+1 < FixedCoefficientHLowerEnclosure.rationalUpper := by
  norm_num [rationalUpper,rationalFifth,RefinedRetainedFTC.rationalSixth,
    FixedCoefficientHLowerEnclosure.rationalUpper,FixedCoefficientLogMassEnclosure.rationalPositive,
    densityConstant,upperLog,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  linarith

 theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,complete_rational_upper⟩

end Wu2008DoubleSieve.RetainedSixthCoefficient

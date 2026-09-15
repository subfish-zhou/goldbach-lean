import MathlibNt.Wu2008DoubleSieve.FourPositiveRationalLower

namespace Wu2008DoubleSieve.FourPositiveCompleteCoefficient
open Real ClassicalAnalyticLeaves SharpLogRecurrence FixedCoefficientUpperEnclosure

noncomputable def rationalUpper : ℝ :=
  baseBound+RetainedSixthCoefficient.rationalFifth+RefinedRetainedFTC.rationalSixth+
  47/481250-FixedCoefficientHLowerEnclosure.rationalH-GVariableCoefficient.rationalGain-
  JCubicRationalLower.weightedRational-FourPositiveRationalLower.weightedRational

/-- Reassemble the same full coefficient from its original termwise producers. -/
theorem complete_rational_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := RefinedRetainedFTC.actual_sixth_upper
  have hg := GVariableCoefficient.G_pair_rational_lower
  have hj := JCubicRationalLower.weighted_J_lower
  have h10 := FourPositiveRationalLower.actual_ten_lower
  have h11 := FourPositiveRationalLower.actual_eleven_lower
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
  unfold FourPositiveRationalLower.weightedRational
  linarith

theorem literal_complete_upper :
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
    truncatedSixthLowerF6lin+47/481250-
    SingleUpperClassicalLimit.Glin (1/3)-SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ rationalUpper := complete_rational_upper

/-- An envelope identity proved only after the actual termwise reassembly. -/
theorem envelope_identity : rationalUpper+FourPositiveRationalLower.weightedRational =
    JCubicCompleteCoefficient.rationalUpper := by
  unfold rationalUpper JCubicCompleteCoefficient.rationalUpper
  ring

theorem strict_improvement : rationalUpper < JCubicCompleteCoefficient.rationalUpper := by
  have h := envelope_identity
  have hp := FourPositiveRationalLower.weighted_positive
  linarith

theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,complete_rational_upper⟩

end Wu2008DoubleSieve.FourPositiveCompleteCoefficient

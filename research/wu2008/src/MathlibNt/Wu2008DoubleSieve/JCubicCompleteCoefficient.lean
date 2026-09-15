import MathlibNt.Wu2008DoubleSieve.JCubicRationalLower

namespace Wu2008DoubleSieve.JCubicCompleteCoefficient
open Real ClassicalAnalyticLeaves SharpLogRecurrence FixedCoefficientUpperEnclosure

noncomputable def rationalUpper : ℝ :=
  baseBound+RetainedSixthCoefficient.rationalFifth+RefinedRetainedFTC.rationalSixth+
  47/481250-FixedCoefficientHLowerEnclosure.rationalH-GVariableCoefficient.rationalGain-
  JCubicRationalLower.weightedRational

/-- Every original signed term is supplied by its actual producer. -/
theorem complete_rational_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := RefinedRetainedFTC.actual_sixth_upper
  have hg := GVariableCoefficient.G_pair_rational_lower
  have hj := JCubicRationalLower.weighted_J_lower
  have hi := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
  linarith

theorem literal_complete_upper :
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
    truncatedSixthLowerF6lin+47/481250-
    SingleUpperClassicalLimit.Glin (1/3)-SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ rationalUpper := complete_rational_upper

/-- An exact relation between the scalar envelopes, not the proof of the actual bound. -/
theorem envelope_identity : rationalUpper = CombinedCoefficientEnclosure.rationalUpper+
    FixedCoefficientJLowerEnclosure.weightedRational-JCubicRationalLower.weightedRational := by
  unfold rationalUpper CombinedCoefficientEnclosure.rationalUpper RetainedSixthCoefficient.rationalUpper
  ring

theorem strict_improvement : rationalUpper < CombinedCoefficientEnclosure.rationalUpper := by
  rw [envelope_identity]
  have h := JCubicRationalLower.weighted_improves
  linarith

theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,complete_rational_upper⟩

end Wu2008DoubleSieve.JCubicCompleteCoefficient

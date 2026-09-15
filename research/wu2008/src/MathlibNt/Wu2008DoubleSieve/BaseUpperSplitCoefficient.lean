import MathlibNt.Wu2008DoubleSieve.BaseUpperSplitRecurrence
import MathlibNt.Wu2008DoubleSieve.NaturalSplitCoefficient

namespace Wu2008DoubleSieve.BaseUpperSplitCoefficient
open Real ClassicalAnalyticLeaves FixedCoefficientUpperEnclosure

noncomputable def newUpper : ℝ :=
  BaseUpperSplitRecurrence.newBase+RetainedSixthCoefficient.rationalFifth+
  NaturalSplitActual.newSixth+47/481250-
  FixedCoefficientHLowerEnclosure.rationalH-GVariableCoefficient.rationalGain-
  JCubicRationalLower.weightedRational-FourPositiveRationalLower.weightedRational

/-- Assemble the same complete coefficient from each actual signed term. -/
theorem complete_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ newUpper := by
  have hb := BaseUpperSplitRecurrence.base_upper
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := NaturalSplitActual.actual_sixth_upper
  have hg := GVariableCoefficient.G_pair_rational_lower
  have hj := JCubicRationalLower.weighted_J_lower
  have h10 := FourPositiveRationalLower.actual_ten_lower
  have h11 := FourPositiveRationalLower.actual_eleven_lower
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient newUpper
  unfold FourPositiveRationalLower.weightedRational
  linarith

/-- Literal regression: no changed weights, missing negative terms, or consumer hypotheses. -/
theorem literal_complete_upper :
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
    truncatedSixthLowerF6lin+47/481250-
    SingleUpperClassicalLimit.Glin (1/3)-SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ newUpper :=
  complete_upper

/-- Envelope comparison is downstream of the actual term assembly. -/
theorem envelope_identity : newUpper = NaturalSplitCoefficient.exactUpper-
    (baseBound-BaseUpperSplitRecurrence.newBase) := by
  rw [← NaturalSplitCoefficient.rational_upper_eq]
  unfold newUpper NaturalSplitCoefficient.rationalUpper
  ring

theorem exact_upper_lt_five : newUpper < (5 : ℝ) := by
  rw [envelope_identity,BaseUpperSplitRecurrence.base_difference]
  norm_num [NaturalSplitCoefficient.exactUpper,FourPositiveExactEnvelope.exactUpper,
    NaturalSplitActual.exactGain]

theorem complete_lt_five :
    TruncatedElevenClassicalCountLower.classicalCoefficient < (5 : ℝ) :=
  complete_upper.trans_lt exact_upper_lt_five

end Wu2008DoubleSieve.BaseUpperSplitCoefficient

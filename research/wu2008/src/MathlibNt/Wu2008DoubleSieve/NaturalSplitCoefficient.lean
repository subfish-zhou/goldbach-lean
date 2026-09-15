import MathlibNt.Wu2008DoubleSieve.NaturalSplitActual
import MathlibNt.Wu2008DoubleSieve.FourPositiveExactEnvelope

namespace Wu2008DoubleSieve.NaturalSplitCoefficient
open Real ClassicalAnalyticLeaves SharpLogRecurrence FixedCoefficientUpperEnclosure

noncomputable def rationalUpper : ℝ :=
  baseBound+RetainedSixthCoefficient.rationalFifth+NaturalSplitActual.newSixth+
  47/481250-FixedCoefficientHLowerEnclosure.rationalH-GVariableCoefficient.rationalGain-
  JCubicRationalLower.weightedRational-FourPositiveRationalLower.weightedRational

/-- Consume the actual terms, not a difference of independent upper bounds. -/
theorem complete_rational_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := NaturalSplitActual.actual_sixth_upper
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
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ rationalUpper :=
  complete_rational_upper

/-- Scalar comparison is downstream of the complete actual coefficient proof. -/
theorem envelope_identity : rationalUpper+NaturalSplitActual.exactGain =
    FourPositiveCompleteCoefficient.rationalUpper := by
  have h := NaturalSplitActual.exact_improvement
  unfold rationalUpper FourPositiveCompleteCoefficient.rationalUpper
  linarith

theorem strict_improvement : rationalUpper < FourPositiveCompleteCoefficient.rationalUpper := by
  have h := envelope_identity
  have hp := NaturalSplitActual.gain_positive
  linarith

noncomputable def exactUpper : ℝ := FourPositiveExactEnvelope.exactUpper-NaturalSplitActual.exactGain

theorem rational_upper_eq : rationalUpper = exactUpper := by
  have h := envelope_identity
  rw [FourPositiveExactEnvelope.rational_upper_eq] at h
  unfold exactUpper
  linarith

theorem actual_exact_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ exactUpper := by
  rw [← rational_upper_eq]
  exact complete_rational_upper

end Wu2008DoubleSieve.NaturalSplitCoefficient

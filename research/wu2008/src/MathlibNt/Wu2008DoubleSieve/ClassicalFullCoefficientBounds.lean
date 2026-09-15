import MathlibNt.Wu2008DoubleSieve.ClassicalPositiveBounds

namespace Wu2008DoubleSieve.ClassicalFullCoefficientBounds
open ClassicalRemainingBounds ClassicalLogBounds ClassicalPositiveBounds

/-- An unconditional bound on the original complete coefficient, not on a renamed truncation.
All three J weights, both G windows, both fourfold integrals and both positive masses are used.
The negative numerical lower bound is not a claim that the coefficient is positive. -/
theorem complete_coefficient_gt_negative_seventeen :
    (-17 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := base_gt_fifty_two
  have hg := ClassicalSingleBounds.G_pair_lt_fifty_two
  have h4 := ClassicalLogFourBounds.four_weighted_lt_two
  have h7 := J7_lt_tenth
  have h8 := J8_lt_seven_eighths
  have h9 := J9_lt_one
  have hp := fifth_gt_four_fifths
  have hq := sixth_gt_four_fifths
  change SingleUpperClassicalLimit.Glin (1/3) +
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma < 52 at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient
  linarith

/-- Literal expansion of the original coefficient; no term or multiplicity is omitted. -/
theorem full_literal_coefficient_gt_negative_seventeen :
    (-17 : ℝ) <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
      truncatedSixthLowerF6lin + 47/481250 -
      SingleUpperClassicalLimit.Glin (1/3) -
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma - 8*J9 -
      16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
      8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_negative_seventeen

end Wu2008DoubleSieve.ClassicalFullCoefficientBounds

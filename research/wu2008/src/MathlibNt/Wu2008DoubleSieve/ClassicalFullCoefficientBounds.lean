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


end Wu2008DoubleSieve.ClassicalFullCoefficientBounds

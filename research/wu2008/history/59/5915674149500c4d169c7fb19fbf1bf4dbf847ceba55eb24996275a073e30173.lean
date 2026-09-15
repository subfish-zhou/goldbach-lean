import Wu08FourMotherTerminal
import BaseSharedSlack

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.W11
open Wu08TerminalAlignment
open VariableGIntegral (a s c)

/-- The common low interval is counted twice; the original high tail only once. -/
theorem pair_integral_identity :
    thirdMain + fourthMain =
      8 * (∫ t in a..s, ClassicalSingleBounds.g t) + 8 * log (6 * a / s) := by
  have hg := GConvexChord.geometry
  have has : a ≤ s := hg.2.1.trans (hg.2.2.1.trans hg.2.2.2.1)
  have hlo := ClassicalSingleBounds.g_integrable le_rfl hg.2.2.2.2 has
  have hhi := ClassicalSingleBounds.g_integrable has le_rfl hg.2.2.2.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hlo hhi
  have htail := ClassicalSingleBounds.high_integral_eq
  have hthird : thirdMain = 4 * ∫ t in a..(1 / 3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [thirdMain, SingleUpperClassicalLimit.Glin,
      SingleUpperClassicalLimit.Gdelta, sub_zero, ClassicalSingleBounds.g,
      ClassicalSingleBounds.a, a]
  have hfourth : fourthMain = 4 * ∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [fourthMain, SingleUpperClassicalLimit.Glin,
      SingleUpperClassicalLimit.Gdelta, sub_zero, ClassicalSingleBounds.g,
      ClassicalSingleBounds.a, a, s]
  change (∫ t in s..(1 / 3 : ℝ), ClassicalSingleBounds.g t) =
    2 * log (6 * a / s) at htail
  rw [hthird, hfourth]
  linarith only [hadd, htail]

def pairAnalyticUpper : ℝ := Phase23.gModel - GCurvatureChord.deltaG

theorem actual_pair_analytic_upper : thirdMain + fourthMain ≤ pairAnalyticUpper := by
  simpa only [thirdMain, fourthMain, pairAnalyticUpper, Phase23.gModel,
    FixedCoefficientUpperEnclosure.a, FixedCoefficientUpperEnclosure.s,
    FixedCoefficientHLowerEnclosure.c, a, s, c, SharpSingleBalance.c,
    SharpSingleBalance.a] using GCurvatureChord.full_G_upper

def pairUpper : ℝ := GConvexChord.rationalG - GCurvatureChord.deltaG

theorem actual_pair_upper : thirdMain + fourthMain ≤ pairUpper :=
  GCurvatureChord.full_G_rational

theorem pairUpper_exact :
    pairUpper = 77998668864853643785980411539 / 1792635052362773743884375000 := by
  norm_num [pairUpper, GConvexChord.rationalG, GCurvatureChord.deltaG,
    GConvexChord.m, GConvexChord.C, GConvexChord.r4, GConvexChord.r5,
    VariableGIntegral.logCoefficient, VariableGIntegral.linearCoefficient,
    SharpLogRecurrence.upperLog, a, s, c, SharpSingleBalance.c,
    SharpSingleBalance.a, truncatedSixthLowerAlpha, truncatedSixthLowerSigma]

theorem pairUpper_bounds :
    (43510623 / 1000000 : ℝ) < pairUpper ∧ pairUpper < 43510624 / 1000000 := by
  rw [pairUpper_exact]
  norm_num

theorem actual_pair_upper_decimal :
    thirdMain + fourthMain < (43510624 / 1000000 : ℝ) :=
  actual_pair_upper.trans_lt pairUpper_bounds.2

theorem normalized_signed_pair_lower :
    -pairUpper / 4 ≤ (-thirdMain - fourthMain) / 4 := by
  linarith only [actual_pair_upper]

/-- These are disjoint pieces of the same signed weight (8 - 24*t), not
    additional independent F1 or G payments. -/
def sharedRecovery : ℝ :=
  ExactWeightTripleEnclosure.highLower + ExactWeightTripleEnclosure.middleLower +
    BaseSharedSlack.lowGain

theorem sharedRecovery_le : sharedRecovery ≤ AnalyticTotalThreshold.sharedLoss := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hl := BaseSharedSlack.low_gain_paid
  rw [BaseGSharedActualRecovery.shared_exact]
  unfold sharedRecovery
  linarith only [hw.1, hw.2.2.1, hl]

def correlatedCredit : ℝ :=
  24 * Phase23.alphaModel - Phase23.gModel +
    SharedRationalEnvelope.deltaShared + sharedRecovery

/-- F1 remains the actual firstMain until its cancellation in the consumer. -/
theorem actual_correlated_lower :
    correlatedCredit ≤ 3 * firstMain - thirdMain - fourthMain := by
  have h := sharedRecovery_le
  unfold AnalyticTotalThreshold.sharedLoss at h
  rw [← first_exact]
  unfold correlatedCredit thirdMain fourthMain
  change sharedRecovery ≤
    24 * wuLowerCoefficient (1 / (2 * truncatedSixthLowerAlpha)) -
      (SingleUpperClassicalLimit.Glin (1 / 3) +
        SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma) -
      (24 * Phase23.alphaModel - Phase23.gModel +
        SharedRationalEnvelope.deltaShared) at h
  linarith only [h]

theorem actual_correlated_pair_upper :
    thirdMain + fourthMain ≤ 3 * firstMain - correlatedCredit := by
  linarith only [actual_correlated_lower]

end WuTarget.W11

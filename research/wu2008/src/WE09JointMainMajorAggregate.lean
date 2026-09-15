import WE09JointMainMajorHighPayment

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.E09JointMainMajor

def aggregatePayment : ℝ :=
  logPayment + E09JointMain.jointGain + middlePayment + highPayment

theorem aggregate_shared_paid :
    W11.sharedRecovery + E09JointMain.jointGain + middlePayment + highPayment ≤
      AnalyticTotalThreshold.sharedLoss := by
  have hh := high_gain_paid
  have hm := middle_gain_paid
  have hl := E09JointMain.low_gain_paid
  rw [BaseGSharedActualRecovery.shared_exact]
  unfold W11.sharedRecovery
  linarith only [hh, hm, hl, middlePayment_le_gain, highPayment_le_gain]

theorem aggregatePayment_le_actual :
    aggregatePayment ≤ 3 * Wu08TerminalAlignment.firstMain -
      Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain := by
  have he := E09JointMain.correlated_remaining_exact
  have hs := aggregate_shared_paid
  have hp := logPayment_le_credit
  unfold aggregatePayment
  linarith only [he, hs, hp]

theorem aggregate_strict : E09JointMain.payment < aggregatePayment := by
  have h := logPayment_gain
  unfold aggregatePayment E09JointMain.payment
  linarith only [h, middlePayment_pos, highPayment_pos]

theorem aggregate_target : (7 / 5 : ℝ) ≤ aggregatePayment := by
  have he : aggregatePayment = aggregatePayment := rfl
  conv at he =>
    lhs
    norm_num [aggregatePayment, logPayment, W11Credit.collected, E09JointMain.jointGain,
      highPayment, highRational, highLogA, highLogB, highCoefficients, signedLog,
      middlePayment, middleRational, middleLogA, middleLogB, middleCoefficients,
      Fin.sum_univ_succ, polePolynomial, middlePole, curvaturePrimitive,
      FixedCoefficientUpperEnclosure.a, FixedCoefficientHLowerEnclosure.c,
      truncatedSixthLowerAlpha, upperFour, upperFive, highA0, highA1, highA2, highA3,
      logThreeCap, upperLog, lowerLog]
  rw [← he]
  norm_num

end WuTarget.E09JointMainMajor

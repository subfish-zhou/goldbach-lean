import W13TightPair

noncomputable section
open Wu2008DoubleSieve FourRoughClosedMass WuTarget.W13
open Wu08OriginalFourWeights

namespace WuTarget.W13Tight

theorem pairUpper_exact : pairUpper =
    (26875435940533312228039000328979770798335983204226556846125448310403759489773059933399307753781372028836762611769214239837171110424285006609 /
      31056238955554783684880132090014895082157336063748158774085392966780320600050047236645407782538827346182611039854112280896035211618041856000 : ℝ) := by
  unfold pairUpper momentUpper
  rw [discount_two, discount_three, discount_four]
  norm_num [c0Upper, a2, a3, a4, h, d, k, cut,
    FourLogAffine.l, FourLogAffine.u, FourLogAffine.w,
    SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog,
    alpha, beta, lam, truncatedSixthLowerAlpha, truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem pairUpper_lt_display : pairUpper < 865380/1000000 := by
  rw [pairUpper_exact]
  norm_num

theorem original_pair_lt_display : original10+original11 < 865380/1000000 :=
  original_pair_upper.trans_lt pairUpper_lt_display

theorem recovery_lower : (9828/1000000 : ℝ) < W13.pairUpper-pairUpper := by
  rw [W13.pairUpper_exact, pairUpper_exact]
  norm_num

end WuTarget.W13Tight

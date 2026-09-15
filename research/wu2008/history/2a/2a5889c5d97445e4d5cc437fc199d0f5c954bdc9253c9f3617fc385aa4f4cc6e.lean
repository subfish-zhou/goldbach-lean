import W13OriginalPairUpper

noncomputable section
open Wu2008DoubleSieve FourRoughClosedMass Wu08OriginalFourWeights

namespace WuTarget.W13

theorem pairUpper_exact : pairUpper =
    (407606662625739962914479556341121140700455456240052084290583163185246970648901541869903193238581459123 /
      465725496850905243266226990091493224552975524834629888128264962598350887110434218458128272126102077440 : ℝ) := by
  norm_num [pairUpper, momentUpper, c0Upper, a2, a3, a4, h, d, k, cut,
    FourLogAffine.l, FourLogAffine.u, FourLogAffine.w,
    SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog,
    alpha, beta, lam, truncatedSixthLowerAlpha, truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem pairUpper_lt_display : pairUpper < 875208/1000000 := by
  rw [pairUpper_exact]
  norm_num

theorem original_pair_lt_display : original10+original11 < 875208/1000000 :=
  original_pair_upper.trans_lt pairUpper_lt_display

end WuTarget.W13

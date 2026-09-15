import WE10FourPayment

noncomputable section
open Wu2008DoubleSieve FourRoughClosedMass Wu08OriginalFourWeights

namespace WuTarget.E10Four

theorem kappa_exact : kappa = (200/727 : ℝ) := by
  norm_num [kappa,alpha,lam,truncatedSixthLowerAlpha,truncatedSixthLowerLambda]

theorem recovery_exact : recovery =
    (134699878059802486838900730948097082678706176 /
      6739864167343234194298133074909794062490699015 : ℝ) := by
  norm_num [recovery,rebateCoeff,kappa,FourLogAffine.l,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem netCredit_exact : netCredit =
    (33674969514950621709725182737024270669676544 /
      6739864167343234194298133074909794062490699015 : ℝ) := by
  rw [netCredit,recovery_exact]
  norm_num

theorem pairUpper_exact : pairUpper =
    (32552230430458819268289158270894402654410226271007019884390475629642237676592004617874043735224181764042923177847589487077698213913170752237424478098075669859 /
      38505392819428692512922483799422960816618117515019303921651960295130914202588378001961674290472294401853213957276913114180362448664319597957947312050323456000 : ℝ) := by
  rw [pairUpper,W13Tight.pairUpper_exact,recovery_exact]
  norm_num

theorem recovery_bounds : (999/50000 : ℝ) < recovery ∧ recovery < 1/50 := by
  rw [recovery_exact]
  norm_num

theorem netCredit_bounds : (999/200000 : ℝ) < netCredit ∧ netCredit < 1/200 := by
  rw [netCredit_exact]
  norm_num

theorem pairUpper_lt_display : pairUpper < (4227/5000 : ℝ) := by
  have hold := W13Tight.pairUpper_lt_display
  have hgain := recovery_bounds.1
  unfold pairUpper
  linarith only [hold,hgain]

theorem original_pair_lt_display :
    original10+original11 < (4227/5000 : ℝ) :=
  original_pair_upper.trans_lt pairUpper_lt_display

end WuTarget.E10Four

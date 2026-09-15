import RemainingHfFinite
namespace RemainingHfParent
open Real RemainingHf Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open FirstFeedbackIntegrals F1FullRecoveryPayment Wu04FactorEnvelopes
noncomputable section

theorem splitLower_one : splitLower 1=0 := by
  norm_num [splitLower,basicLower,leftFactor,rightFactor,lowerLog,upperLog,lowerGapPayment,
    F1LowerResidual.payment,F1LowerResidual.denom]

theorem splitUpper_one : splitUpper 1=0 := by
  norm_num [splitUpper,basicUpper,leftFactor,rightFactor,lowerLog,upperLog,V,upperGapPayment]

theorem signed_one (c : ℝ) : signed c 1=0 := by
  simp [signed,splitLower_one,splitUpper_one]

theorem jPaid_diagonal (S A a : ℝ) (ha : a ≠ 0) (h1 : a+A+1 ≠ 0)
    (h2 : a+(-(2*S-A-1)) ≠ 0) (h3 : a+1 ≠ 0) (h4 : S-1-a ≠ 0) :
    RemainingHf.jPaid S A a a=0 := by
  unfold RemainingHf.jPaid
  dsimp only
  rw [div_self ha,div_self h1,div_self h2,div_self h3,div_self h4]
  simp only [signed_one,sub_self,mul_zero,add_zero]
end
end RemainingHfParent

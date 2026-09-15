import Wu04RecoverComplete

namespace Wu04RecoverPaid
open Wu2008DoubleSieve SecondFunctionalParameters
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

theorem cost_rational : Wu04RecoverComplete.costCap ≤ (80228 : ℝ)/1000000 := by
  norm_num [Wu04RecoverComplete.costCap,Wu04RecoverCost.costCap,Wu04ThreeCost.costCap,
    Wu04RecoverRectangle.gain,Wu04RecoverRectangle.massLower,
    Wu04RecoverRectangle.a,Wu04RecoverRectangle.b,Wu04RecoverRectangle.c,
    Wu04RecoverRectangle.f,Wu04RecoverRectangle.r,
    Wu04RecoverGammaMass.gain,Wu04RecoverGammaMass.massLower,
    Wu04RecoverGamma.d,Wu04RecoverGamma.lo,Wu04RecoverGamma.hi,Wu04RecoverGamma.r,
    Wu04WholeCostPaid.costCap,Wu04WholeCostPaid.tripleCap,Wu04WholeCostPaid.fourCap,
    Wu04WholeCostPaid.lx,Wu04WholeCostPaid.ux,Wu04WholeCostPaid.ly,Wu04WholeCostPaid.uy,
    Wu04WholeCostPaid.lz,Wu04WholeCostPaid.uz,Wu04WholeCostPaid.lw,Wu04WholeCostPaid.uw,
    Wu04ThreeMass.gain,Wu04ThreeMass.massLower,Wu04MainTail.cap,Wu04ThreeTail.cap,row1,
    Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]

theorem first_cost : coupledCostMass row1 ≤ (80228 : ℝ)/1000000 :=
  Wu04RecoverComplete.complete_cost_paid.trans cost_rational

theorem first_joint : (79099 : ℝ)/1000000 ≤ classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := Wu04WholeReversePaid.first_classical
  have hc := first_cost
  linarith only [hb,hc]

theorem first_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    (239555 : ℝ)/5000000-2*(80228/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := Wu04RecoverComplete.actual hd hh
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left cost_rational (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ 5*(1-2*δ) by linarith)
  linarith only [h,hc]

theorem residual_identity :
    classicalNumerator row1-2*coupledCostMass row1-5*(15826357 : ℝ)/1000000000 =
      (classicalNumerator row1-239555/1000000)+
      2*(80228/1000000-coupledCostMass row1)-6557/200000000 := by ring

end
end Wu04RecoverPaid

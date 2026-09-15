import Wu04WholeReverseL

namespace Wu04WholeReversePaid
open Wu2008DoubleSieve Real SecondFunctionalParameters SharpLogRecurrence JointLogTotalComparison
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open Wu04WholeCollection Wu04WholePayment Wu04FactorLPrimitive
noncomputable section

def smallPaid : ℝ := rationalPart (row1.kappa2-1)-rationalPart 2+
  up ((row1.kappa2-1)/2)/5-low (row1.kappa2-2)/20+
  (976/405)*up ((row1.kappa2+1)/4)-(536/405)*low ((3*row1.kappa2-5)/(row1.kappa2+1))

theorem small_payment : fourthRowClassicalL row1.kappa2≤smallPaid := by
  apply (Wu04WholeReverseL.actual_upper_small (by norm_num [row1] : 2<row1.kappa2)
    (by norm_num [row1])).trans
  rw [Wu04WholeReverseL.collected_small (by norm_num [row1] : 2<row1.kappa2)]
  have h1 := (bounds (show 0<(row1.kappa2-1)/2 by norm_num [row1])).2
  have h2 := (bounds (show 0<row1.kappa2-2 by norm_num [row1])).1
  have h3 := (bounds (show 0<(row1.kappa2+1)/4 by norm_num [row1])).2
  have h4 := (bounds (show 0<(3*row1.kappa2-5)/(row1.kappa2+1) by norm_num [row1])).1
  unfold smallPaid
  linarith only [h1,h2,h3,h4]

def classicalPaid : ℝ := jSPaid+jKPaid-2*lSPaid-2*lKPaid-smallPaid

theorem classical_payment : classicalPaid≤classicalNumerator row1 := by
  have hj := jS_payment.trans (Wu04FactorJPrimitive.actual_lower
    (by norm_num [row1] : 2<row1.s) (by norm_num [row1])
    (by norm_num [Wu04MainClassical.a,row1]) (by norm_num [Wu04MainClassical.a,row1]))
  have hk := jK_payment.trans (Wu04FactorJPrimitive.actual_lower
    (by norm_num [row1] : 2<row1.kappa3) (by norm_num [row1])
    (by norm_num [Wu04MainClassical.a,row1]) (by norm_num [Wu04MainClassical.a,row1]))
  have hl := (Wu04FactorLPrimitive.actual_upper (by norm_num [row1] : 3≤row1.S)).trans lS_payment
  have hm := (Wu04FactorLPrimitive.actual_upper (by norm_num [row1] : 3≤row1.kappa1)).trans lK_payment
  have hn := small_payment
  unfold classicalPaid classicalNumerator
  linarith only [hj,hk,hl,hm,hn]

theorem reverse_gain_paid : (96:ℝ)/1000000≤-2*lowerLog (20/19)+V (10/9)-smallPaid := by
  norm_num [smallPaid,Wu04FactorLPrimitive.rationalPart,low,up,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,lowerLog,upperLog,V,row1]

theorem classical_rational : (239555:ℝ)/1000000≤classicalPaid := by
  have h := Wu04WholePayment.classical_rational
  have hg := reverse_gain_paid
  unfold classicalPaid Wu04WholePayment.classicalPaid at *
  linarith only [h,hg]

theorem first_classical : (239555:ℝ)/1000000≤classicalNumerator row1 :=
  classical_rational.trans classical_payment

theorem first_joint_paid : (78815:ℝ)/1000000≤classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical
  have hc := Wu04MainConsumer.first_cost
  linarith only [hb,hc]

theorem first_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (239555:ℝ)/5000000-2*(80370/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left Wu04MainConsumer.first_cost (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := first_classical
  linarith only [h,hc,hb]

end
end Wu04WholeReversePaid

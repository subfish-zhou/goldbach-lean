import Wu04WholePayment

namespace Wu04WholePaidActual
open Wu2008DoubleSieve ActualNineFeedback NodeExtension SecondFunctionalParameters
open Wu08OriginalPsiRecovery Wu04WholePayment
noncomputable section

theorem first_classical : (239459:ℝ)/1000000≤classicalNumerator row1 :=
  classical_rational.trans (certificate_payment.trans Wu04FactorConsumer.classical_lower)

theorem first_joint_paid : (78719:ℝ)/1000000≤classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical
  have hc := Wu04MainConsumer.first_cost
  linarith only [hb,hc]

theorem first_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (239459:ℝ)/5000000-2*(80370/1000000)/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left Wu04MainConsumer.first_cost (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := first_classical
  linarith only [h,hc,hb]

theorem exact_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    classicalPaid/5-2*Wu04MainProducer.rationalCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := Wu04FactorConsumer.first_actual_rational_cost hd hh
  have hb := certificate_payment
  linarith only [h,hb]

end
end Wu04WholePaidActual

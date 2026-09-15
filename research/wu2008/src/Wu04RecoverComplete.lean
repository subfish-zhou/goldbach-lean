import Wu04RecoverGammaMass

namespace Wu04RecoverComplete
open Wu2008DoubleSieve SecondFunctionalParameters SecondFunctionalJointTail
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
noncomputable section

def costCap : ℝ := Wu04RecoverCost.costCap-Wu04RecoverGammaMass.gain

/-- Independent Gamma9 is improved inside its own supremum, never coupled to the other phi. -/
theorem complete_cost_paid : coupledCostMass row1≤costCap := by
  have hc : coupledCostMass row1≤(Wu04MainProducer.omegaCap-Wu04RecoverGammaMass.gain)+Wu04RecoverCost.jointCap := by
    apply original_cost_of_pointwise
    · intro phi hphi
      exact Wu04RecoverGammaMass.first_omega hphi
    · intro phi hphi
      exact Wu04RecoverCost.kernel_paid hphi
  have he := Wu04MainProducer.complete_cap_identity
  have hb := Wu04WholeCostPaid.complete_cap_paid
  unfold costCap Wu04RecoverCost.costCap Wu04RecoverCost.jointCap
    Wu04ThreeCost.costCap Wu04ThreeCost.jointCap at *
  linarith only [hc,he,hb]

theorem strict_improvement : costCap<Wu04RecoverCost.costCap := by
  unfold costCap
  linarith only [Wu04RecoverGammaMass.gain_pos]

theorem actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    (239555:ℝ)/5000000-2*costCap/(5*(1-2*δ))+
      coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5-2*coupledCostMass row1/(5*(1-2*δ))+
    coupledFeedback row1 (actualNine δ)≤wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left complete_cost_paid (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  have hb := Wu04WholeReversePaid.first_classical
  linarith only [h,hc,hb]
end
end Wu04RecoverComplete

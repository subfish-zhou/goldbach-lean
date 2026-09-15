import Wu04RecoverRectangle

namespace Wu04RecoverCost
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalJointTail
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open scoped BigOperators
noncomputable section

def jointCap : ℝ := Wu04ThreeCost.jointCap-Wu04RecoverRectangle.gain
def costCap : ℝ := Wu04ThreeCost.costCap-Wu04RecoverRectangle.gain

theorem lower_sum {phi : ℝ} (hphi : 2≤phi) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) j phi) ≤
      Wu04MainTail.cap*(∑ j : Fin 6, lowerMass row1 j)-Wu04ThreeMass.gain-Wu04RecoverRectangle.gain := by
  classical
  have hp (j : Fin 6) : LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) j phi ≤ Wu04MainTail.cap*lowerMass row1 j -
      (if j=2 then Wu04ThreeMass.gain else 0) - (if j=3 then Wu04RecoverRectangle.gain else 0) := by
    by_cases h2 : j=2
    · subst j
      simp only [ite_true, show (2:Fin 6)≠3 by decide, ite_false, sub_zero]
      have hk := Wu04ThreeMass.third_kernel hphi
      have hm := mul_le_mul_of_nonneg_left Wu04ThreeMass.third_mass_paid
        (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
      unfold Wu04ThreeMass.gain
      nlinarith only [hk,hm]
    · by_cases h3 : j=3
      · subst j
        simpa using Wu04RecoverRectangle.fourth_kernel hphi
      · simpa [h2,h3] using Wu04MainCost.first_lower_mass j hphi
  have h := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => hp j)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

theorem kernel_paid {phi : ℝ} (hphi : 2≤phi) : SecondFunctionalCoupled.kernel row1 phi≤jointCap := by
  have hl := lower_sum hphi
  have hf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) =>
    four_mass_bound row1 (original_mother 0) (original_s_ge_two 0) phi j)
  have hh := Wu04CoupledCostProducer.original_high_le_U20 0 phi
  change Wu04HighCoupledSupport.highKernel row1 phi≤Wu04HighCoupledSupport.U20 row1 at hh
  unfold SecondFunctionalCoupled.kernel jointCap Wu04ThreeCost.jointCap Wu04MainProducer.jointCap
    Wu04HighCoupledSupport.highKernel at *
  linarith only [hl,hf,hh]

/-- Gamma9 retains its own supremum; six+four+unit/legal terms all retained. -/
theorem complete_cost_paid : coupledCostMass row1≤costCap := by
  have hc : coupledCostMass row1≤Wu04MainProducer.omegaCap+jointCap := by
    apply original_cost_of_pointwise
    · intro phi hphi
      exact Wu04MainCost.first_omega hphi
    · intro phi hphi
      exact kernel_paid hphi
  have he := Wu04MainProducer.complete_cap_identity
  have hb := Wu04WholeCostPaid.complete_cap_paid
  unfold jointCap costCap Wu04ThreeCost.jointCap Wu04ThreeCost.costCap at *
  linarith only [hc,he,hb]

theorem strict_improvement : costCap<Wu04ThreeCost.costCap := by
  unfold costCap
  linarith only [Wu04RecoverRectangle.gain_pos]

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
end Wu04RecoverCost

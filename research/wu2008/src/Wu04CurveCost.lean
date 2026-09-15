import Wu04CurveMass

namespace Wu04CurveCost
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalJointTail
open ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open scoped BigOperators
noncomputable section

/-- The old complete cap retains the independent Gamma9 improvement. -/
def costCap : ℝ := Wu04RecoverComplete.costCap-Wu04CurveMass.gain

def jointCap : ℝ := Wu04RecoverCost.jointCap-Wu04CurveMass.gain

theorem lower_sum {phi : ℝ} (hphi : 2≤phi) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) j phi) ≤
      Wu04MainTail.cap*(∑ j : Fin 6, lowerMass row1 j)-Wu04ThreeMass.gain-
        Wu04RecoverRectangle.gain-Wu04CurveMass.gain := by
  classical
  have hp (j : Fin 6) : LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) j phi ≤
      Wu04MainTail.cap*lowerMass row1 j - (if j=2 then Wu04ThreeMass.gain else 0) -
        (if j=3 then Wu04RecoverRectangle.gain+Wu04CurveMass.gain else 0) := by
    by_cases hj : j=3
    · subst j
      simp only [show (3:Fin 6)≠2 by decide,ite_false,ite_true,sub_zero]
      linarith only [Wu04CurveMass.fourth_kernel hphi]
    · by_cases ht : j=2
      · subst j
        simp only [ite_true,show (2:Fin 6)≠3 by decide,ite_false,sub_zero]
        have hk := Wu04ThreeMass.third_kernel hphi
        have hm := mul_le_mul_of_nonneg_left Wu04ThreeMass.third_mass_paid
          (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
        unfold Wu04ThreeMass.gain
        nlinarith only [hk,hm]
      · simpa only [hj,ht,ite_false,sub_zero] using Wu04MainCost.first_lower_mass j hphi
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => hp j)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at hs
  linarith only [hs]

/-- All six lower triples, all four four-prime terms and unit/legal high terms remain. -/
theorem joint_paid {phi : ℝ} (hphi : 2≤phi) : SecondFunctionalCoupled.kernel row1 phi≤jointCap := by
  have hl := lower_sum hphi
  have hf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) =>
    four_mass_bound row1 (original_mother 0) (original_s_ge_two 0) phi j)
  have hh := Wu04CoupledCostProducer.original_high_le_U20 0 phi
  change Wu04HighCoupledSupport.highKernel row1 phi≤Wu04HighCoupledSupport.U20 row1 at hh
  unfold SecondFunctionalCoupled.kernel jointCap Wu04RecoverCost.jointCap
    Wu04ThreeCost.jointCap Wu04MainProducer.jointCap Wu04HighCoupledSupport.highKernel at *
  linarith only [hl,hf,hh]

/-- The two supremum variables remain independent in original_cost_of_pointwise. -/
theorem complete_cost_paid : coupledCostMass row1≤costCap := by
  have hp : coupledCostMass row1 ≤
      (Wu04MainProducer.omegaCap-Wu04RecoverGammaMass.gain)+jointCap := by
    apply original_cost_of_pointwise
    · intro phi hphi
      exact Wu04RecoverGammaMass.first_omega hphi
    · intro phi hphi
      exact joint_paid hphi
  have he := Wu04MainProducer.complete_cap_identity
  have hb := Wu04WholeCostPaid.complete_cap_paid
  unfold costCap jointCap Wu04RecoverComplete.costCap Wu04RecoverCost.costCap
    Wu04RecoverCost.jointCap Wu04ThreeCost.costCap Wu04ThreeCost.jointCap at *
  linarith only [hp,he,hb]

theorem strict_improvement : costCap<Wu04RecoverComplete.costCap := by
  unfold costCap
  linarith only [Wu04CurveMass.gain_pos]

end
end Wu04CurveCost

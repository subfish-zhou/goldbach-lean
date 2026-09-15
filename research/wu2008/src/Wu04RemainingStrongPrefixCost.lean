import Wu04RemainingStrongThird

namespace Wu04RemainingStrongPrefixCost
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open Wu04RemainingCore SecondFunctionalFourSevenths SecondFunctionalJointTail
open SecondFunctionalGeometricMass
open scoped BigOperators
noncomputable section

/-- The genuine third-domain payment is subtracted from the complete cap. -/
def costCap (p : SecondFunctionalParameters) : ℝ :=
  Wu04RemainingEnvelope.costCap p-Wu04RemainingStrongThird.gain p

theorem six_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j φ) ≤
    Wu04MainTail.cap*(∑ j : Fin 6, lowerMass (row i) j)-Wu04RemainingStrongThird.gain (row i) := by
  have hp (j : Fin 6) : LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j φ ≤
      Wu04MainTail.cap*lowerMass (row i) j-
        (if j=2 then Wu04RemainingStrongThird.gain (row i) else 0) := by
    by_cases hj : j=2
    · subst j
      simpa only [ite_true] using Wu04RemainingStrongThird.kernel_paid i hφ
    · simpa only [hj,ite_false,sub_zero] using Wu04RemainingLower.lower_paid i j hφ
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => hp j)
  simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] using hs

theorem joint_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    SecondFunctionalCoupled.kernel (row i) φ ≤
      Wu04RemainingCost.jointCore (row i)-Wu04RemainingStrongThird.gain (row i) := by
  have hl := six_paid i hφ
  have hf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) =>
    four_mass_bound (row i) (original_mother i.succ) (original_s_ge_two i.succ) φ j)
  have hh := Wu04CoupledCostProducer.original_high_le_U20 i.succ φ
  change Wu04HighCoupledSupport.highKernel (row i) φ≤Wu04HighCoupledSupport.U20 (row i) at hh
  unfold SecondFunctionalCoupled.kernel Wu04RemainingCost.jointCore
    Wu04HighCoupledSupport.highKernel at *
  linarith only [hl,hf,hh]

theorem complete_paid (i : Fin 3) : coupledCostMass (row i)≤costCap (row i) := by
  have hc := original_cost_of_pointwise (fun _ hφ => Wu04RemainingGamma.remaining_omega i hφ)
    (fun _ hφ => joint_paid i hφ)
  have he := Wu04RemainingCost.complete_identity (row i) (original_mother i.succ)
    (original_s_ge_two i.succ)
  have ht := mul_le_mul_of_nonneg_left (Wu04RemainingEnvelope.polynomials_paid i).1
    (show 0≤Wu04MainTail.cap by norm_num [Wu04MainTail.cap])
  have hf := (Wu04RemainingEnvelope.polynomials_paid i).2
  have hh := Wu04RemainingEnvelope.high_paid i
  have hb : Wu04RemainingCost.costCore (row i)≤Wu04RemainingEnvelope.costCap (row i) := by
    unfold Wu04RemainingCost.costCore Wu04RemainingEnvelope.costCap
    linarith only [ht,hf,hh]
  unfold costCap
  linarith only [hc,he,hb]

/-- Complete original positive-delta consumer; no publication comparison is retried. -/
theorem actual_remaining (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    Wu04RemainingStrongClassical.certificate (row i)/5-2*costCap (row i)/(5*(1-2*δ))+
      coupledFeedback (row i) (actualNine δ)≤wuImprovementLimit true δ (row i).s :=
  actual_of_paid (coupledRow_geometry i.succ) (Wu04RemainingStrongClassical.complete_paid i)
    (complete_paid i) hd hh

end
end Wu04RemainingStrongPrefixCost

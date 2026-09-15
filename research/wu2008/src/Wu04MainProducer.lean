import Wu04MainCost

namespace Wu04MainProducer
open Wu2008DoubleSieve Wu04MainTail Wu04MainCost Wu04FullPsiMass
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalGeometricMass.Elementary SecondFunctionalJointTail
open ActualNineFeedback NodeExtension Wu04CoupledCostProducer Wu08OriginalPsiRecovery
open Wu04FullPsiCostCertificate SharpLogRecurrence JointLogTotalComparison
open scoped BigOperators
noncomputable section

/-- Exact grouping of Γ9 and all six labeled lower triple masses. -/
theorem triple_mass_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    elementaryMomentOne 1 (1/p.kappa1) (1/p.kappa3) +
      (∑ j : Fin 6, lowerMass p j) = triplePolynomial p := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have he0 := hc0.trans_le hce
  have hf0 := he0.trans_le hef
  have hyz := adjacent_log_join hb0 hc0 he0
  have hzw := adjacent_log_join hc0 he0 hf0
  rw [lowerMass_sum_eq_elementary p hp hs]
  unfold elementaryLowerMass
  dsimp only
  unfold elementaryMomentOne elementaryMomentZero
  rw [hyz,hzw]
  simp only [momentPolynomial,Nat.factorial,Nat.cast_one,one_div_one_div]
  unfold lowerThreeLog lowerFiveLog triplePolynomial x y z w
  rw [hzw]
  simp only [one_div,div_inv_eq_mul]
  ring

def omegaCap : ℝ := cap * elementaryMomentOne 1 (1/row1.kappa1) (1/row1.kappa3)
def jointCap : ℝ := cap * (∑ j : Fin 6, lowerMass row1 j) +
  (∑ j : Fin 4, fourMass row1 j) + Wu04HighCoupledSupport.U20 row1

def completeCap : ℝ := cap*triplePolynomial row1 + fourPolynomial row1 + Wu04HighCoupledSupport.U20 row1

theorem first_kernel {phi : ℝ} (hphi : 2 ≤ phi) : SecondFunctionalCoupled.kernel row1 phi ≤ jointCap := by
  have hl := first_lower_sum hphi
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    four_mass_bound row1 (original_mother 0) (original_s_ge_two 0) phi j)
  have hh := original_high_le_U20 0 phi
  change Wu04HighCoupledSupport.highKernel row1 phi ≤ Wu04HighCoupledSupport.U20 row1 at hh
  unfold SecondFunctionalCoupled.kernel jointCap Wu04HighCoupledSupport.highKernel at *
  linarith only [hl,hf,hh]

theorem complete_cap_identity : omegaCap+jointCap = completeCap := by
  have ht := triple_mass_eq row1 (original_mother 0) (original_s_ge_two 0)
  have he := full_cost_polynomial row1 (original_mother 0) (original_s_ge_two 0)
  unfold Omega3ElementaryFeedback.omegaCost kernelCap fullCostPolynomial at he
  unfold omegaCap jointCap completeCap cap
  nlinarith only [ht,he]

/-- The two independent true suprema are bounded independently. No shared maximizer is assumed. -/
theorem first_complete_cost : coupledCostMass row1 ≤ completeCap := by
  rw [← complete_cap_identity]
  apply original_cost_of_pointwise
  · intro phi hphi
    exact first_omega hphi
  · intro phi hphi
    exact first_kernel hphi

/-- Original actual positive-delta consumer, with all unit/legal/fourprime costs and feedback retained. -/
theorem first_actual_unrounded {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    classicalNumerator row1/5 - 2*completeCap/(5*(1-2*δ)) +
      coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  rw [← complete_cap_identity]
  apply quantitative_source_producer (coupledRow_geometry 0)
  · intro phi hphi
    exact first_omega hphi
  · intro phi hphi
    exact first_kernel hphi
  · exact hd
  · exact hh

/-- Main-sector improvement only: no fourprime/high refinement has been used. -/
theorem exact_main_gain : fullCostPolynomial row1-completeCap = (4397/1118040)*triplePolynomial row1 := by
  unfold fullCostPolynomial completeCap cap
  ring

def rationalCap : ℝ := cap*tripleCap+fourCap+207/8318750

theorem first_rational_cap : completeCap ≤ rationalCap := by
  have ht := first_polynomials_bounded.1
  have hf := first_polynomials_bounded.2
  have hh := first_U20_rational
  have hc : 0 ≤ cap := by norm_num [cap]
  have hm := mul_le_mul_of_nonneg_left ht hc
  unfold completeCap rationalCap
  linarith only [hm,hf,hh]

#print axioms triple_mass_eq
#print axioms first_complete_cost
#print axioms first_actual_unrounded
#print axioms exact_main_gain
end
end Wu04MainProducer

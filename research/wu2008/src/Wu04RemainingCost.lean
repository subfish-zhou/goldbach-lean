import Wu04RemainingGamma

namespace Wu04RemainingCost
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open Wu04RemainingCore Wu04MainTail Wu04FullPsiMass
open SecondFunctionalGeometricMass SecondFunctionalJointTail SecondFunctionalFourSevenths
open scoped BigOperators
noncomputable section

/-- Same complete polynomial, sharper already-proved global Buchstab cap. -/
def costCore (p : SecondFunctionalParameters) : ℝ :=
  cap*triplePolynomial p+fourPolynomial p+Wu04HighCoupledSupport.U20 p

def jointCore (p : SecondFunctionalParameters) : ℝ :=
  cap*(∑ j : Fin 6,lowerMass p j)+(∑ j : Fin 4,fourMass p j)+Wu04HighCoupledSupport.U20 p

theorem complete_identity (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2≤p.s) :
    cap*Elementary.elementaryMomentOne 1 (1/p.kappa1) (1/p.kappa3)+jointCore p=costCore p := by
  have ht := Wu04MainProducer.triple_mass_eq p hp hs
  have hf := full_cost_polynomial p hp hs
  unfold Omega3ElementaryFeedback.omegaCost Wu04CoupledCostProducer.kernelCap
    fullCostPolynomial at hf
  unfold jointCore costCore
  linarith only [hf,congrArg (fun x : ℝ => cap*x) ht,ht]

/-- Six lower terms, four four-prime terms, and both unit/legal high families share phi. -/
theorem joint_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    SecondFunctionalCoupled.kernel (row i) φ≤jointCore (row i) := by
  have hl := Wu04RemainingLower.six_paid i hφ
  have hf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) =>
    four_mass_bound (row i) (original_mother i.succ) (original_s_ge_two i.succ) φ j)
  have hh := Wu04CoupledCostProducer.original_high_le_U20 i.succ φ
  change Wu04HighCoupledSupport.highKernel (row i) φ≤Wu04HighCoupledSupport.U20 (row i) at hh
  unfold SecondFunctionalCoupled.kernel jointCore Wu04HighCoupledSupport.highKernel at *
  linarith only [hl,hf,hh]

/-- No unproved cap premise; Gamma9 keeps its independent supremum. -/
theorem complete_paid (i : Fin 3) : coupledCostMass (row i)≤costCore (row i) := by
  rw [← complete_identity (row i) (original_mother i.succ) (original_s_ge_two i.succ)]
  exact original_cost_of_pointwise (fun _ hφ => Wu04RemainingGamma.remaining_omega i hφ)
    (fun _ hφ => joint_paid i hφ)

theorem actual_remaining (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    classicalCore (row i)/5-2*costCore (row i)/(5*(1-2*δ))+
      coupledFeedback (row i) (actualNine δ)≤wuImprovementLimit true δ (row i).s :=
  actual_of_paid (coupledRow_geometry i.succ) (remaining_classical i) (complete_paid i) hd hh

theorem budget_remaining (i : Fin 3) :
    classicalCore (row i)-2*costCore (row i)≤classicalNumerator (row i)-2*coupledCostMass (row i) := by
  linarith only [remaining_classical i,complete_paid i]

end
end Wu04RemainingCost

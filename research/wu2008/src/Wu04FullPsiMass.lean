import Wu04CoupledCostProducer

namespace Wu04FullPsiMass
open Wu2008DoubleSieve Wu04CoupledCostProducer
open SecondFunctionalGeometricMass SecondFunctionalGeometricMass.Elementary
open SecondFunctionalJointTail SecondFunctionalFourSevenths
noncomputable section

/-- Four adjacent original endpoint logarithms. These are not new cutpoints. -/
def x (p : SecondFunctionalParameters) : ℝ := Real.log ((1/p.kappa1)/(1/p.S))
def y (p : SecondFunctionalParameters) : ℝ := Real.log ((1/p.kappa2)/(1/p.kappa1))
def z (p : SecondFunctionalParameters) : ℝ := Real.log ((1/p.kappa3)/(1/p.kappa2))
def w (p : SecondFunctionalParameters) : ℝ := Real.log ((1/p.s)/(1/p.kappa3))

/-- Gamma9 and all six lower-triple masses combined before endpoint comparison. -/
def triplePolynomial (p : SecondFunctionalParameters) : ℝ :=
  (p.kappa1-p.kappa2+2*p.kappa3)*y p +
  (2*p.kappa1-p.kappa2+p.kappa3)*z p + (p.S-p.kappa2)*w p -
  p.kappa3*y p*w p + p.kappa1*x p*z p + (p.s-p.kappa2)*x p -
  2*(p.kappa1-p.kappa3)

/-- All four-prime masses; cross-term cancellation retains their multiplicities. -/
def fourPolynomial (p : SecondFunctionalParameters) : ℝ :=
  (p.kappa2+2*p.kappa3)*z p + (p.kappa2-p.kappa3)*w p -
  p.kappa3*z p*w p + (p.s/2)*(z p)^2 - 3*(p.kappa2-p.kappa3) +
  (p.kappa3+p.s)*y p*w p - 2*(p.kappa3-p.s)*y p

def fullCostPolynomial (p : SecondFunctionalParameters) : ℝ :=
  (4/7)*triplePolynomial p + fourPolynomial p + Wu04HighCoupledSupport.U20 p

theorem adjacent_log_join {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (c/a) = Real.log (b/a) + Real.log (c/b) := by
  rw [Real.log_div hc.ne' ha.ne', Real.log_div hb.ne' ha.ne', Real.log_div hc.ne' hb.ne']
  ring

theorem full_cost_polynomial (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    Omega3ElementaryFeedback.omegaCost p + kernelCap p = fullCostPolynomial p := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have he0 := hc0.trans_le hce
  have hf0 := he0.trans_le hef
  have hyz := adjacent_log_join hb0 hc0 he0
  have hzw := adjacent_log_join hc0 he0 hf0
  rw [kernelCap_eq_elementary p hp hs]
  unfold Omega3ElementaryFeedback.omegaCost elementaryKernelCap fullCostPolynomial
  unfold elementaryMass elementaryLowerMass
  dsimp only
  unfold elementaryMomentOne elementaryMomentZero
  rw [hyz, hzw]
  simp only [momentPolynomial, Nat.factorial, Nat.cast_ofNat, Nat.cast_one,
    one_div_one_div]
  unfold lowerThreeLog lowerFiveLog triplePolynomial fourPolynomial x y z w
  rw [hzw]
  simp only [one_div, div_inv_eq_mul]
  ring

theorem original_cost_polynomial (i : Fin 4) :
    ActualNineFeedback.coupledCostMass (SecondFunctionalPositive.parameters i) ≤
      fullCostPolynomial (SecondFunctionalPositive.parameters i) := by
  rw [← full_cost_polynomial _ (original_mother i) (original_s_ge_two i)]
  exact original_cost_majorant i

#print axioms full_cost_polynomial
#print axioms original_cost_polynomial
end
end Wu04FullPsiMass

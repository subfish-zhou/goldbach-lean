import CoupledJErrorCells

namespace CoupledJLogRecovery
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery CoupledMiddleGateRecovery CoupledHGateRecovery GatedDensityPayment
open scoped Interval BigOperators
noncomputable section

def remainder (p : SecondFunctionalParameters) : ℝ :=
  (4*CoupledCorrectedE.correctedRest NineFeedbackStrength.originalH p.S+
    CoupledCorrectedE.correctedRest NineFeedbackStrength.originalH p.kappa1+
    jRest NineFeedbackStrength.originalH p.s p.S+
    jRest NineFeedbackStrength.originalH p.kappa2 p.S+
    jRest NineFeedbackStrength.originalH p.kappa3 p.S+
    densityFinite p NineFeedbackStrength.originalH+
    NineFeedbackStrength.originalH 0*gatePayment p+
    NineFeedbackStrength.originalH 0*middleGain p)/5

def actualLower (p : SecondFunctionalParameters) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*aProfile (nineProfile NineFeedbackStrength.originalH)+remainder p

def cubicLower (p : SecondFunctionalParameters) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+remainder p

theorem actualLower_le (i : Fin 4) : actualLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  let p := coupledRow i
  let z := NineFeedbackStrength.originalH
  have hp := coupledRow_geometry i
  have hz := originalH_nonneg
  have hg := coupled_geometry_bounds hp
  have he0 := CoupledCorrectedE.eTerm_le hz hp.1.three_le_S hp.1.S_le_five
  have he1 := CoupledCorrectedE.eTerm_le hz hp.2.1 hg.2.2.2.2.2.2
  have hj0 := jTerm_le z hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := jTerm_le z hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := jTerm_le z hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := density_replace_middle i hz
  unfold CoupledCorrectedE.eTerm at he0 he1
  unfold jTerm at hj0 hj2 hj3
  unfold actualLower remainder coupledFeedback CoupledFiniteAssembly.aCoefficient
  dsimp only [p,z] at *
  linarith only [he0,he1,hj0,hj2,hj3,hd]

theorem cubicLower_le_actualLower (i : Fin 4) : cubicLower (coupledRow i) ≤ actualLower (coupledRow i) := by
  have ha := mul_le_mul_of_nonneg_left CubicCommonProfile.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg (coupledRow_geometry i))
  unfold cubicLower actualLower
  linarith only [ha]

theorem cubicLower_le_original (i : Fin 4) : cubicLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  (cubicLower_le_actualLower i).trans (actualLower_le i)

def jRecovery (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*((FirstErrorFullPayment.errorPrimitive (jStart s S+1)
      (FiniteEndpointPayment.right (jStart s S-1) (S-2) k)-
    FirstErrorFullPayment.errorPrimitive (jStart s S+1)
      (FiniteEndpointPayment.left (jStart s S-1) (S-2) k))+
    (secondPrimitive S (jStart s S) (FiniteEndpointPayment.right (jStart s S-1) (S-2) k)-
      secondPrimitive S (jStart s S) (FiniteEndpointPayment.left (jStart s S-1) (S-2) k)))

theorem jRest_exact (z : Fin 9 → ℝ) (s S : ℝ) :
    jRest z s S = CoupledFiniteAssembly.jRest z s S+jRecovery z s S := by
  unfold jRest CoupledFiniteAssembly.jRest jRecovery fullPrimitive
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem exact_replacement (p : SecondFunctionalParameters) :
    cubicLower p = CoupledCorrectedE.lower p+
      (jRecovery NineFeedbackStrength.originalH p.s p.S+
       jRecovery NineFeedbackStrength.originalH p.kappa2 p.S+
       jRecovery NineFeedbackStrength.originalH p.kappa3 p.S)/5 := by
  unfold cubicLower remainder CoupledCorrectedE.lower
  rw [jRest_exact,jRest_exact,jRest_exact]
  ring

end
end CoupledJLogRecovery

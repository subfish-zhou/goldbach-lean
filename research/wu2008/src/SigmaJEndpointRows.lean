import SigmaJEndpointIntegral

namespace SigmaJEndpoint
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback CoupledIntegralRecovery
open CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
noncomputable section

def replacementGain (p : SecondFunctionalParameters) : ℝ :=
  ((endpointRest NineFeedbackStrength.originalH p.s p.S-CoupledJLogRecovery.jRest NineFeedbackStrength.originalH p.s p.S)+
   (endpointRest NineFeedbackStrength.originalH p.kappa2 p.S-CoupledJLogRecovery.jRest NineFeedbackStrength.originalH p.kappa2 p.S)+
   (endpointRest NineFeedbackStrength.originalH p.kappa3 p.S-CoupledJLogRecovery.jRest NineFeedbackStrength.originalH p.kappa3 p.S))/5

def endpointLower (p : SecondFunctionalParameters) : ℝ :=
  SigmaJJoint.coupledLower p+replacementGain p

theorem endpointLower_le_original (i : Fin 4) : endpointLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have he0 := CoupledCorrectedE.eTerm_le originalH_nonneg hp.1.three_le_S hp.1.S_le_five
  have he1 := CoupledCorrectedE.eTerm_le originalH_nonneg hp.2.1 hg.2.2.2.2.2.2
  have hj0 := endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := density_replace_middle i originalH_nonneg
  have ha := mul_le_mul_of_nonneg_left SigmaExistingLogError.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg hp)
  unfold CoupledCorrectedE.eTerm at he0 he1
  unfold endpointLower replacementGain SigmaJJoint.coupledLower CoupledJLogRecovery.remainder
    coupledFeedback CoupledFiniteAssembly.aCoefficient at *
  linarith only [he0,he1,hj0,hj2,hj3,hd,ha]

theorem endpoint_hc_of_scalar (i : Fin 4)
    (h : NineFeedbackStrength.originalH (i.castAdd 5) ≤
      NineFeedbackStrength.publication (i.castAdd 5)+endpointLower (coupledRow i)) :
    NineFeedbackStrength.originalH (i.castAdd 5) ≤
      NineFeedbackStrength.publication (i.castAdd 5)+coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  h.trans (add_le_add le_rfl (endpointLower_le_original i))

end
end SigmaJEndpoint

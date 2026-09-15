import SigmaRemainingOriginal
namespace SigmaRemaining
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FirstFeedbackIntegrals FiniteEndpointPayment CoupledIntegralRecovery
open CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
noncomputable section

/-- Replace the parent's sole common sigma, preserving its full clipped E and endpoint J. -/
def coupledLower (p : SecondFunctionalParameters) : ℝ :=
  ResidualEndpointJoint.coupledLower p+CoupledFiniteAssembly.aCoefficient p*
    (finiteLower NineFeedbackStrength.originalH-SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH)

theorem coupledLower_le_original (i : Fin 4) : coupledLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have he0 := ResidualEndpointJoint.eTerm_le originalH_nonneg hp.1.three_le_S hp.1.S_le_five
  have he1 := ResidualEndpointJoint.eTerm_le originalH_nonneg hp.2.1 hg.2.2.2.2.2.2
  have hj0 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := density_replace_middle i originalH_nonneg
  have ha := mul_le_mul_of_nonneg_left original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg hp)
  unfold ResidualEndpointJoint.eTerm at he0 he1
  unfold coupledLower ResidualEndpointJoint.coupledLower SigmaJEndpoint.endpointLower
    SigmaJEndpoint.replacementGain SigmaJJoint.coupledLower CoupledJLogRecovery.remainder
    coupledFeedback CoupledFiniteAssembly.aCoefficient at *
  linarith only [he0,he1,hj0,hj2,hj3,hd,ha]

end
end SigmaRemaining

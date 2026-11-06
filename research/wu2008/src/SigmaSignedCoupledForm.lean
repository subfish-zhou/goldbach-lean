import SigmaSignedInnerProfile
namespace SigmaSignedCells
open Real Wu2008DoubleSieve ActualNineFeedback NodeExtension
open CoupledIntegralRecovery CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
noncomputable section

/-- Full original finite expression, not a shortened E/J or a newly introduced scalar hypothesis. -/
theorem coupledLower_collected (p : SecondFunctionalParameters) : coupledLower p =
    CoupledFiniteAssembly.aCoefficient p*profileLower+
      (4*ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.S+
        ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.kappa1+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.s p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa2 p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa3 p.S+
        densityFinite p NineFeedbackStrength.originalH+
        NineFeedbackStrength.originalH 0*gatePayment p+
        NineFeedbackStrength.originalH 0*middleGain p)/5 := by
  unfold coupledLower SigmaRemaining.coupledLower ResidualEndpointJoint.coupledLower
    SigmaJEndpoint.endpointLower SigmaJEndpoint.replacementGain SigmaJJoint.coupledLower
    CoupledJLogRecovery.remainder
  ring




end
end SigmaSignedCells

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

theorem correctedCoupledLower_collected (p : SecondFunctionalParameters) : correctedCoupledLower p =
    CoupledFiniteAssembly.aCoefficient p*correctedProfile+
      (4*ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.S+
        ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.kappa1+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.s p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa2 p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa3 p.S+
        densityFinite p NineFeedbackStrength.originalH+
        NineFeedbackStrength.originalH 0*gatePayment p+
        NineFeedbackStrength.originalH 0*middleGain p)/5 := by
  unfold correctedCoupledLower
  rw [coupledLower_collected]
  ring

theorem quadratic_firstCoefficient_negative : (-438353120/201331053 : ℝ)/2<0 := by norm_num

theorem quadratic_secondCoefficient_positive :
    0 < ((-21945288920/1811979477 : ℝ)-9*(-438353120/201331053))/(2*F1JointFTC.root) := by
  apply div_pos _ (mul_pos (by norm_num) F1JointFTC.root_pos)
  norm_num

end
end SigmaSignedCells

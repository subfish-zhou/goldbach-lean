import SigmaInnerProfileIntegral
import Hf03OriginalTargets

namespace SigmaInnerProfile
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FirstFeedbackIntegrals FiniteEndpointPayment CoupledIntegralRecovery
open CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
noncomputable section

/-- Exact new common sigma, with the existing clipped E and endpoint J unchanged. -/
def coupledLower (p : SecondFunctionalParameters) : ℝ :=
  SigmaRemaining.coupledLower p + CoupledFiniteAssembly.aCoefficient p *
    (d0Lower NineFeedbackStrength.originalH - SigmaRemaining.finiteLower NineFeedbackStrength.originalH)

theorem old_coupledLower_le (i : Fin 4) : SigmaRemaining.coupledLower (coupledRow i) ≤
    coupledLower (coupledRow i) := by
  have ha := CoupledFiniteAssembly.aCoefficient_nonneg (coupledRow_geometry i)
  have h := mul_nonneg ha (sub_nonneg.mpr old_finiteLower_le)
  unfold coupledLower
  linarith only [h]

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
  have ha := mul_le_mul_of_nonneg_left original_d0Lower_le_profile
    (CoupledFiniteAssembly.aCoefficient_nonneg hp)
  unfold ResidualEndpointJoint.eTerm at he0 he1
  unfold coupledLower SigmaRemaining.coupledLower ResidualEndpointJoint.coupledLower
    SigmaJEndpoint.endpointLower SigmaJEndpoint.replacementGain SigmaJJoint.coupledLower
    CoupledJLogRecovery.remainder coupledFeedback CoupledFiniteAssembly.aCoefficient at *
  linarith only [he0,he1,hj0,hj2,hj3,hd,ha]

/-- Reuse the four completed original first-feedback rows without new certificates. -/
theorem original_hf_first_four (i : Fin 5) (hi : i.val < 4) :
    NineFeedbackStrength.originalH (Fin.natAdd 4 i) ≤
      Wu04FirstCore.publication i+
        firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) :=
  Hf03OriginalTargets.original_hf_first_four i hi

end
end SigmaInnerProfile

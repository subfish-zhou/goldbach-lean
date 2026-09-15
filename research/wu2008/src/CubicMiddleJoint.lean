import CubicOriginalProfilePayment
import CoupledMiddleRational

namespace CubicMiddleJoint
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledMiddleGateRecovery CoupledHGateRecovery GatedDensityPayment
noncomputable section

/-- Both independent restorations enter the same original feedback row. -/
def lower (p : SecondFunctionalParameters) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+
    CoupledFiniteAssembly.remainder p NineFeedbackStrength.originalH+
    (densityFinite p NineFeedbackStrength.originalH+
      NineFeedbackStrength.originalH 0*gatePayment p+
      NineFeedbackStrength.originalH 0*middleGain p)/5

theorem lower_le_original (i : Fin 4) : lower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have ha := mul_le_mul_of_nonneg_left CubicCommonProfile.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg (coupledRow_geometry i))
  have hc := actualProfileLower_le i CoupledIntegralRecovery.originalH_nonneg
  unfold lower
  unfold actualProfileLower at hc
  linarith only [ha,hc]

/-- Remove the old common-profile payment before installing the cubic-restored one. -/
theorem exact_replacement (p : SecondFunctionalParameters) : lower p =
    middleRestoredLower p NineFeedbackStrength.originalH+
      CoupledFiniteAssembly.aCoefficient p*
        (CubicCommonProfile.finiteLower NineFeedbackStrength.originalH-
          OriginalProfileSigmaPayment.aFiniteLower NineFeedbackStrength.originalH) := by
  unfold lower middleRestoredLower restoredLower CoupledFullyFinite.lower
  ring

theorem original_hc_margin (i : Fin 4) :
    NineFeedbackStrength.publication (i.castAdd 5)+lower (coupledRow i)-
      NineFeedbackStrength.originalH (i.castAdd 5) ≤
    NineFeedbackStrength.publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5) := by
  linarith only [lower_le_original i]

end
end CubicMiddleJoint

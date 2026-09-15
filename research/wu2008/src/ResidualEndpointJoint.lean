import RemainingHfRows
import SigmaJEndpointOrder
namespace ResidualEndpointJoint
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FirstFeedbackIntegrals FiniteEndpointPayment CoupledIntegralRecovery
open CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
open scoped Interval BigOperators
noncomputable section

def eRest (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*RemainingHf.paidCell S (left (S-2) 3 k) (right (S-2) 3 k)

def eTerm (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  aProfile (nineProfile z)*log (4/(S-1))+eRest z S

theorem eTerm_le {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) {S : ℝ}
    (hS : 3 ≤ S) (hS5 : S ≤ 5) : eTerm z S ≤ eProfile (nineProfile z) S := by
  have hab : S-2 ≤ 3 := by linarith
  have ha : 1 ≤ S-2 := by linarith
  have hw : ContinuousOn (fun t => log ((t+1)/(S-1))/t) (uIcc (S-2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp
    linarith [ht.1]
  have hi := (profile_subinterval (nineProfile_integrable z) ha hab).mul_continuousOn hw
  have he := integral_cells z ha hab le_rfl hi
  unfold eTerm eProfile
  apply add_le_add le_rfl
  calc
    _ ≤ ∫ t in (S-2)..3,nineProfile z t*(log ((t+1)/(S-1))/t) := by
      rw [he]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (RemainingHf.paidCell_paid hS (clip_bounds hab).1 (cell_order _ _ k)) (hz k)
    _ = _ := by congr 1; funext t; ring

def coupledLower (p : SecondFunctionalParameters) : ℝ :=
  SigmaJEndpoint.endpointLower p+
    (4*(eRest NineFeedbackStrength.originalH p.S-CoupledCorrectedE.correctedRest NineFeedbackStrength.originalH p.S)+
      (eRest NineFeedbackStrength.originalH p.kappa1-CoupledCorrectedE.correctedRest NineFeedbackStrength.originalH p.kappa1))/5

theorem coupledLower_le_original (i : Fin 4) : coupledLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have he0 := eTerm_le originalH_nonneg hp.1.three_le_S hp.1.S_le_five
  have he1 := eTerm_le originalH_nonneg hp.2.1 hg.2.2.2.2.2.2
  have hj0 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := SigmaJEndpoint.endpointRest_le NineFeedbackStrength.originalH originalH_nonneg
    hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := density_replace_middle i originalH_nonneg
  have ha := mul_le_mul_of_nonneg_left SigmaExistingLogError.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg hp)
  unfold eTerm at he0 he1
  unfold coupledLower SigmaJEndpoint.endpointLower SigmaJEndpoint.replacementGain
    SigmaJJoint.coupledLower CoupledJLogRecovery.remainder
    coupledFeedback CoupledFiniteAssembly.aCoefficient at *
  linarith only [he0,he1,hj0,hj2,hj3,hd,ha]

end
end ResidualEndpointJoint

import FirstErrorFullRows
import CoupledCMRowThreeNormal

namespace CoupledCorrectedE
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FirstFeedbackIntegrals FirstErrorFullPayment FiniteEndpointPayment
open CoupledIntegralRecovery CoupledMiddleGateRecovery CoupledHGateRecovery GatedDensityPayment
open scoped Interval BigOperators
noncomputable section

/-- All clipped cells, including when S-2 is beyond the first original node. -/
def correctedRest (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*correctedCell S (left (S-2) 3 k) (right (S-2) 3 k)
def eTerm (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  aProfile (nineProfile z)*log (4/(S-1))+correctedRest z S

theorem eTerm_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {S : ℝ}
    (hS : 3≤S) (hS5 : S≤5) : eTerm z S≤eProfile (nineProfile z) S := by
  have hab : S-2≤3 := by linarith
  have ha : 1≤S-2 := by linarith
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
        (correctedCell_paid hS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2) (hz k)
    _ = _ := by congr 1; funext t; ring

/-- The same complete row, replacing both E payments rather than adding two whole bounds. -/
def lower (p : SecondFunctionalParameters) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+
    (4*correctedRest NineFeedbackStrength.originalH p.S+
      correctedRest NineFeedbackStrength.originalH p.kappa1+
      CoupledFiniteAssembly.jRest NineFeedbackStrength.originalH p.s p.S+
      CoupledFiniteAssembly.jRest NineFeedbackStrength.originalH p.kappa2 p.S+
      CoupledFiniteAssembly.jRest NineFeedbackStrength.originalH p.kappa3 p.S+
      densityFinite p NineFeedbackStrength.originalH+
      NineFeedbackStrength.originalH 0*gatePayment p+
      NineFeedbackStrength.originalH 0*middleGain p)/5

theorem lower_le_original (i : Fin 4) : lower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  let p := coupledRow i
  let z := NineFeedbackStrength.originalH
  have hp := coupledRow_geometry i
  have hz := originalH_nonneg
  have hg := coupled_geometry_bounds hp
  have he0 := eTerm_le hz hp.1.three_le_S hp.1.S_le_five
  have he1 := eTerm_le hz hp.2.1 hg.2.2.2.2.2.2
  have hj0 := j_le z hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := j_le z hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := j_le z hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := density_replace_middle i hz
  have ha := mul_le_mul_of_nonneg_left CubicCommonProfile.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg hp)
  unfold eTerm at he0 he1
  unfold FiniteEndpointPayment.j at hj0 hj2 hj3
  unfold lower coupledFeedback CoupledFiniteAssembly.aCoefficient at *
  dsimp only [p,z] at *
  unfold CoupledFiniteAssembly.jRest
  linarith only [he0,he1,hj0,hj2,hj3,hd,ha]

theorem exact_replacement (p : SecondFunctionalParameters) : lower p =
    CubicMiddleJoint.lower p+
      (4*(correctedRest NineFeedbackStrength.originalH p.S-
          CoupledFiniteAssembly.eRest NineFeedbackStrength.originalH p.S)+
        (correctedRest NineFeedbackStrength.originalH p.kappa1-
          CoupledFiniteAssembly.eRest NineFeedbackStrength.originalH p.kappa1))/5 := by
  unfold lower CubicMiddleJoint.lower CoupledFiniteAssembly.remainder
  ring

end
end CoupledCorrectedE

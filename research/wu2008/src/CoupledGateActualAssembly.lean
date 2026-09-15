import CoupledHDensityRestoration

namespace CoupledHGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment
open scoped Interval BigOperators
noncomputable section

/-- Original-row geometry of the recovered branch, including the previously zero endpoint. -/
theorem original_gate_geometry (i : Fin 4) :
    1 ≤ gateStart (coupledRow i) ∧
    gateStart (coupledRow i) < upperSwitch (coupledRow i) ∧
    upperSwitch (coupledRow i) ≤ 3 ∧
    upperSwitch (coupledRow i) ≤ lowerSwitch (coupledRow i) ∧
    kernelEndpoint (coupledRow i) .gammaEight 1 (upperSwitch (coupledRow i)) = 0 ∧
    firstSplit (coupledRow i) 1 (upperNode 0) = upperSwitch (coupledRow i) := by
  revert i
  simp only [Fin.forall_fin_succ]
  dsimp [coupledRow,SecondFunctionalPositive.parameters,SecondFunctionalParameters.row1,SecondFunctionalParameters.row2,
    SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]
  norm_num [gateStart,upperSwitch,lowerSwitch,kernelEndpoint,feedbackLower,feedbackUpper,
    upperP,upperQ,lowerQ,firstSplit,clip,upperNode]

/-- Replace only the old zero gamma-eight contribution in the first cell. -/
theorem density_add_gate (i : Fin 4) {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    densityFinite (coupledRow i) z+z 0*gatePayment (coupledRow i) ≤
      densityMoment (coupledRow i) z := by
  let p := coupledRow i
  have hp := (coupledRow_geometry i).1
  obtain ⟨ha,hab,hb,hs,hzero,hfirst⟩ := original_gate_geometry i
  have h0 := mul_le_mul_of_nonneg_left
    (first_cell_add_gate hp ha hab.le hb hs hzero hfirst) (hz 0)
  have hk (k : Fin 8) := mul_le_mul_of_nonneg_left
    (intervalPayment_le hp (clip_bounds (by norm_num : (1:ℝ) ≤ 3)).1
      (cell_order 1 3 k.succ) (clip_bounds (by norm_num : (1:ℝ) ≤ 3)).2) (hz k.succ)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hk k)
  rw [densityMoment,integral_cells z (by norm_num) (by norm_num) le_rfl
    (density_profile_integrable (coupledRow i) hp z)]
  unfold densityFinite
  simp only [Fin.sum_univ_succ] at hsum ⊢
  have hl : left 1 3 (0:Fin 9)=1 := by norm_num [left,clip,upperLeft]
  have hr : right 1 3 (0:Fin 9)=upperNode 0 := by norm_num [right,clip,upperNode]
  rw [hl,hr]
  dsimp only [left] at hsum ⊢
  linarith only [h0,hsum]

/-- A genuine improvement of the same complete finite expression. -/
def restoredLower (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  CoupledFullyFinite.lower p z+z 0*gatePayment p/5

theorem restoredLower_le (i : Fin 4) {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    restoredLower (coupledRow i) z ≤ coupledFeedback (coupledRow i) z := by
  have hd := div_le_div_of_nonneg_right (density_add_gate i hz) (by norm_num : (0:ℝ) ≤ 5)
  have hc := CoupledFiniteAssembly.finite_profile_lower (coupledRow_geometry i) hz
  unfold restoredLower CoupledFullyFinite.lower
  linarith only [hd,hc]

theorem original_four_restored (i : Fin 4) :
    restoredLower (coupledRow i) NineFeedbackStrength.originalH ≤
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  restoredLower_le i CoupledIntegralRecovery.originalH_nonneg

theorem original_four_strict_gain (i : Fin 4) :
    CoupledFullyFinite.lower (coupledRow i) NineFeedbackStrength.originalH <
      restoredLower (coupledRow i) NineFeedbackStrength.originalH := by
  obtain ⟨ha,hab,_,_,_,_⟩ := original_gate_geometry i
  have hk : 0 < (coupledRow i).kappa2 := by
    have hg := (coupledRow_geometry i).1
    linarith [hg.two_lt_s,hg.mother.s_le_kappa3,hg.mother.kappa3_lt_kappa2]
  have hg := gatePayment_pos hk (by linarith : 0 < gateStart (coupledRow i)) hab
  have hz : 0 < NineFeedbackStrength.originalH 0 := by norm_num [NineFeedbackStrength.originalH]
  have hgain : 0 < NineFeedbackStrength.originalH 0*gatePayment (coupledRow i)/5 := by positivity
  unfold restoredLower
  linarith only [hgain]

end
end CoupledHGateRecovery

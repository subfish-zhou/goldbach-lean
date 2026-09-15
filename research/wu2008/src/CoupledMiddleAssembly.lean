import CoupledMiddleKernel

namespace CoupledMiddleGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment CoupledHGateRecovery
open scoped Interval BigOperators
noncomputable section

/-- The exact old gamma-eight middle box to be removed, not added a second time. -/
def oldMiddleBox (p : SecondFunctionalParameters) : ℝ :=
  (lowerSwitch p-upperSwitch p)*kernelEndpoint p .gammaEight (upperSwitch p) (lowerSwitch p)

/-- Replacement difference only: exact middle mass minus its already paid box. -/
def middleGain (p : SecondFunctionalParameters) : ℝ := middlePayment p-oldMiddleBox p

theorem original_middle_geometry (i : Fin 4) :
    1≤upperSwitch (coupledRow i) ∧ upperSwitch (coupledRow i)<lowerSwitch (coupledRow i) ∧
    lowerSwitch (coupledRow i)≤upperNode 0 ∧
    secondSplit (coupledRow i) 1 (upperNode 0)=lowerSwitch (coupledRow i) := by
  revert i
  simp only [Fin.forall_fin_succ]
  dsimp [coupledRow,SecondFunctionalPositive.parameters,SecondFunctionalParameters.row1,
    SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]
  norm_num [upperSwitch,lowerSwitch,secondSplit,clip,upperNode]

theorem middle_segment_replace {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤upperSwitch p) (hab : upperSwitch p≤lowerSwitch p) (hb : lowerSwitch p≤3) :
    (lowerSwitch p-upperSwitch p)*densityEndpoint p (upperSwitch p) (lowerSwitch p)+
      middleGain p≤∫ v in (upperSwitch p)..(lowerSwitch p),SecondFunctionalCoupledFeedback.density p v := by
  have h5 := kernelEndpoint_integral_le hp .gammaFive ha hab hb
  have h6 := kernelEndpoint_integral_le hp .gammaSix ha hab hb
  have h7 := kernelEndpoint_integral_le hp .gammaSeven ha hab hb
  rw [density_integral_four hp,middle_integral hp ha hab hb]
  unfold middleGain oldMiddleBox densityEndpoint
  linarith only [h5,h6,h7]

/-- Preserve the paid first branch and all other three kernels, replacing only its middle box. -/
theorem first_cell_replace (i : Fin 4) :
    intervalPayment (coupledRow i) 1 (upperNode 0)+gatePayment (coupledRow i)+middleGain (coupledRow i)≤
      ∫ v in (1:ℝ)..(upperNode 0),SecondFunctionalCoupledFeedback.density (coupledRow i) v := by
  let p := coupledRow i
  have hp := (coupledRow_geometry i).1
  obtain ⟨hg,hgu,hb,hs,hzero,hfirst⟩ := original_gate_geometry i
  obtain ⟨ha,hab,hbn,hsecond⟩ := original_middle_geometry i
  have hn3 : upperNode 0≤(3:ℝ) := by norm_num [upperNode]
  have h0 := first_segment_add_gate hp hg hgu.le hb hs hzero
  have h1 := middle_segment_replace hp ha hab.le (hbn.trans hn3)
  have h2 := densityEndpoint_integral_le hp (ha.trans hab.le) hbn hn3
  have hi := density_integrable p hp
  have he0 := intervalIntegral.integral_add_adjacent_intervals
    (a := (1:ℝ)) (b := upperSwitch p) (c := lowerSwitch p)
    hi.intervalIntegrable hi.intervalIntegrable
  have he1 := intervalIntegral.integral_add_adjacent_intervals
    (a := (1:ℝ)) (b := lowerSwitch p) (c := upperNode 0)
    hi.intervalIntegrable hi.intervalIntegrable
  unfold intervalPayment
  rw [hfirst,hsecond]
  linarith only [h0,h1,h2,he0,he1]

theorem density_replace_middle (i : Fin 4) {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    densityFinite (coupledRow i) z+z 0*gatePayment (coupledRow i)+z 0*middleGain (coupledRow i)≤
      densityMoment (coupledRow i) z := by
  have hp := (coupledRow_geometry i).1
  have h0 := mul_le_mul_of_nonneg_left (first_cell_replace i) (hz 0)
  have hk (k : Fin 8) := mul_le_mul_of_nonneg_left
    (intervalPayment_le hp (clip_bounds (by norm_num : (1:ℝ)≤3)).1
      (cell_order 1 3 k.succ) (clip_bounds (by norm_num : (1:ℝ)≤3)).2) (hz k.succ)
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

/-- The entire original finite lower bound with first payment retained exactly once. -/
def middleRestoredLower (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  restoredLower p z+z 0*middleGain p/5

theorem middleRestoredLower_le (i : Fin 4) {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    middleRestoredLower (coupledRow i) z≤coupledFeedback (coupledRow i) z := by
  have hd := div_le_div_of_nonneg_right (density_replace_middle i hz) (by norm_num : (0:ℝ)≤5)
  have hc := CoupledFiniteAssembly.finite_profile_lower (coupledRow_geometry i) hz
  unfold middleRestoredLower restoredLower CoupledFullyFinite.lower
  linarith only [hd,hc]

/-- All four original rows and the actual original H, with every prior payment retained. -/
theorem original_four_middle_restored (i : Fin 4) :
    middleRestoredLower (coupledRow i) NineFeedbackStrength.originalH≤
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  middleRestoredLower_le i CoupledIntegralRecovery.originalH_nonneg

end
end CoupledMiddleGateRecovery

import CrossA1D
import CrossA2D
import CrossA1B1
import CrossA1B2
import CrossA2B1
import CrossA2B2
import CrossAB1
import CrossAB2

noncomputable section
open Real Set MeasureTheory F1CrossFTC F1FactorCross F1BFullFTC FreshRemainingFactors
open scoped Interval
namespace F1CrossMass

def kernels (u : ℝ) : ℝ := A1D.kernel u+A2D.kernel u+A1B1.kernel u+A1B2.kernel u+A2B1.kernel u+A2B2.kernel u+AB1.kernel u+AB2.kernel u

def mass : ℝ := A1D.mass+A2D.mass+A1B1.mass+A1B2.mass+A2B1.mass+A2B2.mass+AB1.mass+AB2.mass

theorem cross_eq {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : cross u=kernels u := by
  rw [cross_rational hu]
  simp only [add_div]
  rw [A1D.source_exact hu.1,A2D.source_exact hu.1,A1B1.source_exact hu.1,A1B2.source_exact hu.1,A2B1.source_exact hu.1,A2B2.source_exact hu.1,AB1.source_exact hu.1,AB2.source_exact hu.1]
  rfl

theorem kernels_continuousOn : ContinuousOn kernels (Icc 2 (927/200)) :=
  (((((((A1D.kernel_continuousOn).add A2D.kernel_continuousOn).add A1B1.kernel_continuousOn).add A1B2.kernel_continuousOn).add A2B1.kernel_continuousOn).add A2B2.kernel_continuousOn).add AB1.kernel_continuousOn).add AB2.kernel_continuousOn

theorem cross_continuousOn : ContinuousOn cross (Icc 2 (927/200)) := by
  apply kernels_continuousOn.congr
  intro u hu
  exact cross_eq hu

theorem integral_exact : (∫ u in (2:ℝ)..(927/200),cross u)=mass := by
  rw [intervalIntegral.integral_congr (fun u hu => cross_eq (by
    simpa only [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] using hu))]
  have h0 := A1D.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h1 := A2D.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h2 := A1B1.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h3 := A1B2.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h4 := A2B1.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h5 := A2B2.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h6 := AB1.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have h7 := AB2.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  unfold kernels mass
  rw [intervalIntegral.integral_add ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6) h7]
  rw [intervalIntegral.integral_add (((((h0.add h1).add h2).add h3).add h4).add h5) h6]
  rw [intervalIntegral.integral_add ((((h0.add h1).add h2).add h3).add h4) h5]
  rw [intervalIntegral.integral_add (((h0.add h1).add h2).add h3) h4]
  rw [intervalIntegral.integral_add ((h0.add h1).add h2) h3]
  rw [intervalIntegral.integral_add (h0.add h1) h2]
  rw [intervalIntegral.integral_add h0 h1]
  rw [A1D.integral_exact,A2D.integral_exact,A1B1.integral_exact,A1B2.integral_exact,A2B1.integral_exact,A2B2.integral_exact,AB1.integral_exact,AB2.integral_exact]

theorem mass_nonneg : 0 ≤ mass := by
  rw [← integral_exact]
  exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => cross_nonneg hu)

def remDensity (u : ℝ) : ℝ := (unpaidA u-freshA u)+(unpaidB u-freshB u)

theorem rem_eq {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : remDensity u=cross u+tails u := by
  unfold remDensity
  rw [remainingA_exact hu.1,remainingB_exact hu,F1FactorCross.charged_once]

theorem rem_continuousOn : ContinuousOn remDensity (Icc 2 (927/200)) :=
  (unpaid_continuousOn.1.sub F1FreshMass.fresh_continuousOn.1).add
    (unpaid_continuousOn.2.sub F1FreshMass.fresh_continuousOn.2)

theorem tails_continuousOn : ContinuousOn tails (Icc 2 (927/200)) := by
  apply (rem_continuousOn.sub cross_continuousOn).congr
  intro u hu
  dsimp
  rw [rem_eq hu]
  ring

def tailMass : ℝ := ∫ u in (2:ℝ)..(927/200),tails u

theorem tailMass_nonneg : 0 ≤ tailMass :=
  intervalIntegral.integral_nonneg (by norm_num) (fun u hu => F1FactorCross.tails_nonneg hu)

theorem remaining_exact : FreshFTCJoint.remaining=mass+tailMass := by
  have hA := unpaid_continuousOn.1.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have hB := unpaid_continuousOn.2.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have hFA := F1FreshMass.fresh_continuousOn.1.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have hFB := F1FreshMass.fresh_continuousOn.2.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ)≤927/200)
  have he : (∫ u in (2:ℝ)..(927/200),remDensity u)=FreshFTCJoint.remaining := by
    unfold remDensity FreshFTCJoint.remaining unpaidMassA unpaidMassB F1FreshMass.massA F1FreshMass.massB
    rw [intervalIntegral.integral_add (hA.sub hFA) (hB.sub hFB),
      intervalIntegral.integral_sub hA hFA,intervalIntegral.integral_sub hB hFB]
  rw [← he,intervalIntegral.integral_congr (fun u hu => rem_eq (by
    simpa only [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] using hu))]
  rw [intervalIntegral.integral_add
    (cross_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    (tails_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num)),integral_exact]
  rfl

def joint : ℝ := FreshCommonLog.collected+mass

theorem firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(joint+tailMass+FreshCommonLog.eLoss) := by
  have h := FreshCommonLog.firstMain_exact
  unfold FreshCommonLog.unpaid FreshCommonLog.logLoss at h
  rw [FreshRemainingFactors.mass_exact,remaining_exact] at h
  unfold joint
  linarith only [h]

theorem joint_le_actual : 8*joint ≤ Wu08TerminalAlignment.firstMain := by
  rw [firstMain_exact]
  linarith only [tailMass_nonneg,FreshCommonLog.eLoss_nonneg]
end F1CrossMass

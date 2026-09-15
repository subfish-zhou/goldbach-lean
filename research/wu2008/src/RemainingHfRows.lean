import RemainingHfCells
namespace RemainingHf
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open SharpLogRecurrence FirstErrorFullPayment CoupledIntegralRecovery
open scoped Interval BigOperators
noncomputable section

def paidCells (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*paidCell S (cellLeft (S-2) k) (upperNode k)

theorem paidCells_le {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) {S : ℝ}
    (hS : 3 ≤ S) (hS2 : S-2 ≤ upperNode 0) :
    aProfile (nineProfile z)*log (4/(S-1))+paidCells z S ≤ eProfile (nineProfile z) S := by
  have hS5 : S ≤ 5 := by have h := (upperNode_bounds 0).2; linarith
  have hw : ContinuousOn (fun t => log ((t+1)/(S-1))/t) (uIcc (S-2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le (by linarith : S-2 ≤ 3)] at ht
    dsimp
    linarith [ht.1]
  have he := profile_integral_cells z (by linarith : 1 ≤ S-2) hS2 hw
  have hm : paidCells z S ≤ ∫ t in (S-2)..3,nineProfile z t*(log ((t+1)/(S-1))/t) := by
    rw [he]
    apply Finset.sum_le_sum
    intro k _
    have hb := cell_bounds (by linarith : 1 ≤ S-2) hS2 k
    exact mul_le_mul_of_nonneg_left (paidCell_paid hS hb.1 hb.2.1) (hz k)
  unfold eProfile
  apply add_le_add le_rfl
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using hm

def lower (s S : ℝ) : ℝ :=
  SigmaJJoint.firstCoefficient s S*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
    paidCells NineFeedbackStrength.originalH S+
    CoupledJLogRecovery.jRest NineFeedbackStrength.originalH s S/2

theorem lower_le {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) (hS2 : S-2 ≤ upperNode 0) :
    lower s S ≤ firstFeedback NineFeedbackStrength.originalH s S := by
  have h0 := log_nonneg ((one_le_div (by linarith : 0<S-1)).mpr (by linarith : S-1 ≤ 4))
  have h1 := log_nonneg ((one_le_div (by linarith : 0<s-1)).mpr (by linarith : s-1 ≤ S-1))
  have hc : 0 ≤ SigmaJJoint.firstCoefficient s S := by unfold SigmaJJoint.firstCoefficient; linarith only [h0,h1]
  have ha := mul_le_mul_of_nonneg_left SigmaExistingLogError.original_finiteLower hc
  have he := paidCells_le originalH_nonneg hS hS2
  have hj := CoupledJLogRecovery.jTerm_le NineFeedbackStrength.originalH originalH_nonneg hs hS hS5 hsS hr
  unfold lower SigmaJJoint.firstCoefficient firstFeedback CoupledJLogRecovery.jTerm at *
  linarith only [ha,he,hj]

theorem lower_original_rows (i : Fin 5) : lower (firstNode i) (firstS i) ≤
    firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  rcases i with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals apply lower_le <;> norm_num [firstNode,firstS,upperNode]

theorem terminal_exact : lower 3 3=
    log 2*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
      paidCells NineFeedbackStrength.originalH 3 := by
  unfold lower SigmaJJoint.firstCoefficient
  rw [SigmaJJoint.terminal_J_zero]
  norm_num
end
end RemainingHf

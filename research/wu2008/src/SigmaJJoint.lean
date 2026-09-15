import SigmaJFirstCertificate1
import SigmaJFirstCertificate2

namespace SigmaJJoint
open Real Wu2008DoubleSieve ActualNineFeedback NodeExtension FirstFeedbackIntegrals
open CoupledIntegralRecovery SigmaExistingLogError FirstErrorFullPayment
noncomputable section

def coupledLower (p : SecondFunctionalParameters) : ℝ :=
  CoupledFiniteAssembly.aCoefficient p*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
    CoupledJLogRecovery.remainder p

theorem coupledLower_le_original (i : Fin 4) : coupledLower (coupledRow i) ≤
    coupledFeedback (coupledRow i) NineFeedbackStrength.originalH := by
  have ha := mul_le_mul_of_nonneg_left SigmaExistingLogError.original_finiteLower
    (CoupledFiniteAssembly.aCoefficient_nonneg (coupledRow_geometry i))
  have hj := CoupledJLogRecovery.actualLower_le i
  unfold coupledLower CoupledJLogRecovery.actualLower at *
  linarith only [ha,hj]

theorem coupled_exact_replacement (p : SecondFunctionalParameters) : coupledLower p=
    CoupledJLogRecovery.cubicLower p+CoupledFiniteAssembly.aCoefficient p*
      (SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH-
        CubicCommonProfile.finiteLower NineFeedbackStrength.originalH) := by
  unfold coupledLower CoupledJLogRecovery.cubicLower
  ring

def firstCoefficient (s S : ℝ) : ℝ := log (4/(S-1))+log ((S-1)/(s-1))/2

def firstLower (s S : ℝ) : ℝ :=
  firstCoefficient s S*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
    correctedCells NineFeedbackStrength.originalH S+
    CoupledJLogRecovery.jRest NineFeedbackStrength.originalH s S/2

theorem firstLower_le {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) (hS2 : S-2 ≤ upperNode 0) :
    firstLower s S ≤ firstFeedback NineFeedbackStrength.originalH s S := by
  have h0 := log_nonneg ((one_le_div (by linarith : 0<S-1)).mpr (by linarith : S-1 ≤ 4))
  have h1 := log_nonneg ((one_le_div (by linarith : 0<s-1)).mpr (by linarith : s-1 ≤ S-1))
  have hc : 0 ≤ firstCoefficient s S := by unfold firstCoefficient; linarith only [h0,h1]
  have ha := mul_le_mul_of_nonneg_left SigmaExistingLogError.original_finiteLower hc
  have he := correctedCells_paid originalH_nonneg hS hS2
  have hj := CoupledJLogRecovery.jTerm_le NineFeedbackStrength.originalH originalH_nonneg hs hS hS5 hsS hr
  unfold firstLower firstCoefficient firstFeedback CoupledJLogRecovery.jTerm at *
  linarith only [ha,he,hj]

theorem first_original_rows (i : Fin 5) : firstLower (firstNode i) (firstS i) ≤
    firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  rcases i with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals apply firstLower_le <;> norm_num [firstNode,firstS,upperNode]

theorem terminal_J_zero : CoupledJLogRecovery.jRest NineFeedbackStrength.originalH 3 3=0 := by
  norm_num [CoupledJLogRecovery.jRest,jStart,FiniteEndpointPayment.left,
    FiniteEndpointPayment.right,FiniteEndpointPayment.clip]

theorem first_terminal_exact : firstLower 3 3=
    log 2*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
      correctedCells NineFeedbackStrength.originalH 3 := by
  unfold firstLower firstCoefficient
  rw [terminal_J_zero]
  norm_num

end
end SigmaJJoint

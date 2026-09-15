import SigmaExistingOriginalProfile

namespace SigmaExistingLogError
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback Wu2008DoubleSieve
open Wu04WholeCollection SharpLogRecurrence FirstErrorFullPayment
noncomputable section

/-- Replace only the common profile in the original first payment; corrected E stays once. -/
def firstLower (s S : ℝ) : ℝ :=
  firstACoefficient s S*finiteLower NineFeedbackStrength.originalH+
    firstResidual NineFeedbackStrength.originalH s S+eRecovery NineFeedbackStrength.originalH S

theorem firstLower_exact_replacement (s S : ℝ) : firstLower s S=
    FirstErrorFullPayment.lower s S+firstACoefficient s S*
      (finiteLower NineFeedbackStrength.originalH-CubicCommonProfile.finiteLower NineFeedbackStrength.originalH) := by
  unfold firstLower FirstErrorFullPayment.lower
  ring

theorem firstLower_le {s S : ℝ} (hs : 2 ≤ s) (hS : 3<S) (hS5 : S≤5) (hsS : s≤S)
    (hr : 2≤S-S/s) (hS2 : S-2≤upperNode 0) :
    firstLower s S ≤ firstFeedback NineFeedbackStrength.originalH s S := by
  have ha := mul_le_mul_of_nonneg_left original_finiteLower
    (firstACoefficient_nonneg hs hS.le hS5 hsS)
  have hf := affine_recovered CoupledIntegralRecovery.originalH_nonneg hs hS hS5 hsS hr hS2
  unfold firstLower
  linarith only [ha,hf]

/-- The original terminal row has exactly zero J forcing, also after this replacement. -/
theorem firstLower_terminal_exact : firstLower 3 3 =
    low 2*finiteLower NineFeedbackStrength.originalH+correctedCells NineFeedbackStrength.originalH 3 := by
  have hj : jCurvePaid 3 3=0 := by
    norm_num [jCurvePaid,signedLow_one]
  have hw : jWeight 3 3=0 := by
    norm_num [jWeight,low,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor,lowerLog]
  unfold firstLower firstACoefficient firstResidual eRecovery
  rw [hj,hw]
  norm_num

theorem firstLower_terminal_le : firstLower 3 3 ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have he := correctedCells_paid CoupledIntegralRecovery.originalH_nonneg
    (by norm_num : (3:ℝ)≤3) (by norm_num [upperNode] : (3:ℝ)-2≤upperNode 0)
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg CoupledIntegralRecovery.originalH_nonneg t)).1
  have hw := mul_le_mul_of_nonneg_right (bounds (by norm_num : (0:ℝ)<2)).1 hA
  have hc := mul_le_mul_of_nonneg_left original_finiteLower (low_nonneg (by norm_num : (1:ℝ)≤2))
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (4:ℝ)/2=2 by norm_num] at he
  rw [firstLower_terminal_exact]
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [he,hw,hc]

theorem original_firstLower_le (i : Fin 5) : firstLower (firstNode i) (firstS i) ≤
    firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  rcases i with ⟨i,hi⟩
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · apply firstLower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply firstLower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply firstLower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply firstLower_le <;> norm_num [firstNode,firstS,upperNode]
  · convert firstLower_terminal_le using 1 <;> norm_num [firstNode,firstS]

end
end SigmaExistingLogError

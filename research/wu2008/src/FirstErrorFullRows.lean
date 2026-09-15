import FirstErrorFullCells

namespace FirstErrorFullPayment
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback Wu2008DoubleSieve
open Wu04WholeCollection SharpLogRecurrence
noncomputable section

/-- The genuine old affine first payment with its E replaced once and its common profile paid fully. -/
def lower (s S : ℝ) : ℝ :=
  firstACoefficient s S*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+
  firstResidual NineFeedbackStrength.originalH s S+eRecovery NineFeedbackStrength.originalH S

theorem affine_recovered {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {s S : ℝ}
    (hs : 2≤ s) (hS : 3<S) (hS5 : S≤5) (hsS : s≤S)
    (hr : 2≤S-S/s) (hS2 : S-2≤upperNode 0) :
    firstACoefficient s S*aProfile (nineProfile z)+firstResidual z s S+eRecovery z S ≤
      firstFeedback z s S := by
  have hj := jPaid_le hz hs hS hS5 hsS hr hS2
  have he := original_eCells_recovered hz hS.le hS2
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have hw := mul_le_mul_of_nonneg_right (bounds (div_pos (by norm_num : (0:ℝ)<4)
    (by linarith : 0<S-1))).1 hA
  unfold firstFeedback firstACoefficient firstResidual jPaid at *
  nlinarith only [hj,he,hw]

theorem firstACoefficient_nonneg {s S : ℝ} (hs : 2≤ s) (hS : 3≤S)
    (hS5 : S≤5) (hsS : s≤S) : 0≤firstACoefficient s S := by
  have h1 := low_nonneg ((one_le_div (by linarith : 0<S-1)).mpr (by linarith : S-1≤4))
  have h2 := low_nonneg ((one_le_div (by linarith : 0<s-1)).mpr (by linarith : s-1≤S-1))
  unfold firstACoefficient jWeight
  positivity

theorem lower_le {s S : ℝ} (hs : 2≤ s) (hS : 3<S) (hS5 : S≤5) (hsS : s≤S)
    (hr : 2≤S-S/s) (hS2 : S-2≤upperNode 0) :
    lower s S ≤ firstFeedback NineFeedbackStrength.originalH s S := by
  have ha := mul_le_mul_of_nonneg_left CubicCommonProfile.original_finiteLower
    (firstACoefficient_nonneg hs hS.le hS5 hsS)
  have hf := affine_recovered CoupledIntegralRecovery.originalH_nonneg hs hS hS5 hsS hr hS2
  unfold lower
  linarith only [ha,hf]

theorem signedLow_one (c : ℝ) : signedLow c 1=0 := by
  norm_num [signedLow,low,up,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,JointLogTotalComparison.V,lowerLog,upperLog]

theorem terminal_lower_exact : lower 3 3 =
    low 2*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+
      correctedCells NineFeedbackStrength.originalH 3 := by
  have hj : jCurvePaid 3 3=0 := by
    norm_num [jCurvePaid,signedLow_one]
  have hw : jWeight 3 3=0 := by
    norm_num [jWeight,low,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor,lowerLog]
  unfold lower firstACoefficient firstResidual eRecovery
  rw [hj,hw]
  norm_num

theorem terminal_lower_le : lower 3 3≤firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have he := correctedCells_paid CoupledIntegralRecovery.originalH_nonneg
    (by norm_num : (3:ℝ)≤3) (by norm_num [upperNode] : (3:ℝ)-2≤upperNode 0)
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg CoupledIntegralRecovery.originalH_nonneg t)).1
  have hw := mul_le_mul_of_nonneg_right (bounds (by norm_num : (0:ℝ)<2)).1 hA
  have hc := mul_le_mul_of_nonneg_left CubicCommonProfile.original_finiteLower
    (low_nonneg (by norm_num : (1:ℝ)≤2))
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (4:ℝ)/2=2 by norm_num] at he
  rw [terminal_lower_exact]
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [he,hw,hc]

/-- All five original rows, with the last row's forcing exactly zero. -/
theorem original_rows_lower_le (i : Fin 5) :
    lower (firstNode i) (firstS i) ≤
      firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  rcases i with ⟨i,hi⟩
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · apply lower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply lower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply lower_le <;> norm_num [firstNode,firstS,upperNode]
  · apply lower_le <;> norm_num [firstNode,firstS,upperNode]
  · convert terminal_lower_le using 1 <;> norm_num [firstNode,firstS]

end
end FirstErrorFullPayment

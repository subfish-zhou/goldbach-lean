import Wu08OriginalFourWeights

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve FourRoughClosedMass
namespace Wu08RecoveredInputs
open Wu08OriginalFourWeights

/-- This is exactly Wu08's F10 integral, not the unit-weight current producer. -/
theorem original10_literal : original10 =
    (36/5)*(∫ x in alpha..(1/10:ℝ),
      (∫ y in x..beta, ∫ z in y..beta, ∫ t in z..beta, kernel x y z t)/(1-x))+
    8*(∫ x in (1/10:ℝ)..beta,
      ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..beta, kernel x y z t) := by
  unfold original10 original
  congr 2
  · apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le parameters.1] at hx
    rw [outer10_eq ⟨hx.1,hx.2.trans parameters.2.1⟩]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le parameters.2.1] at hx
    exact outer10_eq ⟨parameters.1.trans hx.1,hx.2⟩

/-- The original fourth variable in F11 ends at lambda-z, not at beta. -/
theorem original11_literal : original11 =
    (36/5)*(∫ x in alpha..(1/10:ℝ),
      (∫ y in x..beta, ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t)/(1-x))+
    8*(∫ x in (1/10:ℝ)..beta,
      ∫ y in x..beta, ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t) := by
  unfold original11 original
  congr 2
  · apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le parameters.1] at hx
    rw [outer11_eq ⟨hx.1,hx.2.trans parameters.2.1⟩]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le parameters.2.1] at hx
    exact outer11_eq ⟨parameters.1.trans hx.1,hx.2⟩

/-- Direction matters: these smaller original upper amounts cannot be substituted
using only the present larger count upper estimates. -/
theorem original_pair_le_current : original10+original11 ≤
    Wu08TerminalAlignment.tenthCurrent+Wu08TerminalAlignment.eleventhCurrent := by
  rw [actual_tenth_debit,actual_eleventh_debit]
  linarith only [debits_nonnegative.1,debits_nonnegative.2]

/-- Restoring the original 0.899 coefficient would imply the requested later
logarithmic threshold. This comparison uses only the already proved universal V. -/
theorem original_target_suffices : QtwoWholeCertificate.threshold < (899/1000:ℝ) := by
  have h := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hV : 8*JointLogTotalComparison.V (5000/4469) < (899/1000:ℝ) := by
    norm_num [JointLogTotalComparison.V,SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog]
  unfold QtwoWholeCertificate.threshold
  linarith only [h,hV]

#print axioms original10_literal
#print axioms original11_literal
#print axioms original_target_suffices
end Wu08RecoveredInputs

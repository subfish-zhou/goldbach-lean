import Hf4ActualDE

noncomputable section
namespace Hf4Actual
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped Interval

theorem true_numerator_cap :
    (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1)) ≤
    (957/1000000:ℝ) := by
  linarith only [actual_numerator_upper,Hf4Quad.original_Q_bounds.2]

theorem true_profile_cap : aProfile (nineProfile NineFeedbackStrength.originalH) ≤
    (957/1000000:ℝ)/(1-171695/1000000) := by
  rw [aProfile_eq]
  calc
    _ ≤ (957/1000000:ℝ)/(1-D0) :=
      div_le_div_of_nonneg_right true_numerator_cap (sub_pos.mpr D0_lt_one).le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith only [true_D0_cap])

/-- Upper bound for the original flat nine-cell feedback itself, not for a lower model. -/
theorem true_feedback_cap :
    firstFeedback NineFeedbackStrength.originalH 3 3 ≤ (728/100000:ℝ) := by
  have hm := mul_le_mul true_profile_cap Hf4Target.log_two_bounds.2.le
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    (by norm_num : (0:ℝ) ≤ (957/1000000)/(1-171695/1000000))
  have he := actual_e_upper
  have hb := Hf4DE.original_e_mass_bounds.2
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  unfold eProfile
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (3:ℝ)-2=1 by norm_num,
    show (4:ℝ)/2=2 by norm_num]
  norm_num at hm
  linarith only [hm,he,hb]

theorem true_feedback_interval : (72504/10000000:ℝ) ≤
    firstFeedback NineFeedbackStrength.originalH 3 3 ∧
    firstFeedback NineFeedbackStrength.originalH 3 3 ≤ (728/100000:ℝ) :=
  ⟨Hf4Amount.original_feedback_lower,true_feedback_cap⟩

theorem true_feedback_lt_originalH8 :
    firstFeedback NineFeedbackStrength.originalH 3 3 < NineFeedbackStrength.originalH 8 := by
  rw [Hf4Target.original_threshold]
  linarith only [true_feedback_cap]

/-- Refutes the old sufficient row test, not the Goldbach bound or the actual H function. -/
theorem original_flat_profile_hf4_false :
    ¬ (NineFeedbackStrength.originalH 8 ≤ firstFeedback NineFeedbackStrength.originalH 3 3) :=
  not_le.mpr true_feedback_lt_originalH8

theorem true_feedback_deficit : (143/10000000:ℝ) ≤
    NineFeedbackStrength.originalH 8-firstFeedback NineFeedbackStrength.originalH 3 3 := by
  rw [Hf4Target.original_threshold]
  linarith only [true_feedback_cap]

end Hf4Actual

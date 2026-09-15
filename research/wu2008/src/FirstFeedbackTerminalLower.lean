import FirstFeedbackJPayment

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real
open Wu04WholeCollection
noncomputable section

/-- The zero-forcing original terminal still keeps its complete genuine e feedback. -/
theorem terminal_feedback_paid {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    low 2*aProfile (nineProfile z)+eCells z 3≤firstFeedback z 3 3 := by
  have he := eCells_paid hz (by norm_num : (3:ℝ)≤3)
    (by norm_num [upperNode] : (3:ℝ)-2≤upperNode 0)
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have hw := mul_le_mul_of_nonneg_right (bounds (by norm_num : (0:ℝ)<2)).1 hA
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (4:ℝ)/2=2 by norm_num] at he
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [he,hw]

end
end FirstFeedbackIntegrals

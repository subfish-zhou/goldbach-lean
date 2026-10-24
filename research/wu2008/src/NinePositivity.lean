import NineLiteral
import NineBaselinePositivity

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Real Set MeasureTheory
open scoped BigOperators Interval
noncomputable section

theorem Ainf_pos (i : Fin 9) : 0 < FeedbackLimit.Ainf i := by
  by_cases hi : i=8
  · subst i
    have h0 : 0 < FeedbackLimit.Ainf 0 :=
      (publication_pos (by decide : (0 : Fin 9)≠8)).trans_le (publication_le_Ainf 0)
    have hs : feedbackMatrix 8 0 * FeedbackLimit.Ainf 0 ≤
        matrixApply feedbackMatrix FeedbackLimit.Ainf 8 :=
      Finset.single_le_sum (fun k _ => mul_nonneg (feedbackMatrix_nonneg 8 k) (FeedbackLimit.Ainf_nonneg k))
        (Finset.mem_univ 0)
    rw [Ainf_affine]
    exact (mul_pos terminal_first_entry_pos h0).trans_le
      (hs.trans (le_add_of_nonneg_left (base_nonneg 8)))
  · exact (publication_pos hi).trans_le (publication_le_Ainf i)

/-- Strict diagonal control follows from the genuine positive forcing, not a numerical entry bound. -/
theorem terminal_diagonal_lt_one : feedbackMatrix 8 8 < 1 := by
  have hs : feedbackMatrix 8 8 * FeedbackLimit.Ainf 8 <
      matrixApply feedbackMatrix FeedbackLimit.Ainf 8 := by
    exact Finset.single_lt_sum (by decide : (0 : Fin 9)≠8)
      (Finset.mem_univ 8) (Finset.mem_univ 0)
      (mul_pos terminal_first_entry_pos (Ainf_pos 0))
      (fun k _ _ => mul_nonneg (feedbackMatrix_nonneg 8 k) (FeedbackLimit.Ainf_nonneg k))
  have he := Ainf_affine 8
  have hb : base (8 : Fin 9)=0 := rfl
  rw [hb,zero_add] at he
  rw [← he] at hs
  nlinarith only [hs,Ainf_pos 8]

end
end NineFeedbackStrength

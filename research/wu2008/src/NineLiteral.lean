import NineBaseline
import FeedbackFixedPoint

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

/-- Clipping is genuinely removable only after the paid original base is proved nonnegative. -/
theorem Ainf_affine (i : Fin 9) : FeedbackLimit.Ainf i =
    base i + matrixApply feedbackMatrix FeedbackLimit.Ainf i := by
  rw [FeedbackLimit.Ainf_fixed]
  exact max_eq_right (add_nonneg (base_nonneg i)
    (matrixApply_nonneg feedbackMatrix_nonneg FeedbackLimit.Ainf_nonneg i))

theorem publication_le_Ainf (i : Fin 9) : publication i ≤ FeedbackLimit.Ainf i := by
  rw [Ainf_affine]
  exact (publication_le_base i).trans (le_add_of_nonneg_right
    (matrixApply_nonneg feedbackMatrix_nonneg FeedbackLimit.Ainf_nonneg i))

end
end NineFeedbackStrength

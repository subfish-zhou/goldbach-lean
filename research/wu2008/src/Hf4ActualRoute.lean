import Hf4ActualTerminal

noncomputable section
namespace Hf4Actual
open ActualNineFeedback

/-- The unchanged first-row premises of the old sufficient converter cannot all hold. -/
theorem old_first_row_certificate_impossible :
    ¬ (∀ i : Fin 5, NineFeedbackStrength.originalH (Fin.natAdd 4 i) ≤
      Wu04FirstCore.publication i+
        firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i)) := by
  intro h
  have hh := h 4
  norm_num [Wu04FirstCore.publication,firstNode,firstS] at hh
  change NineFeedbackStrength.originalH 8 ≤ 0+firstFeedback NineFeedbackStrength.originalH 3 3 at hh
  exact original_flat_profile_hf4_false (by simpa only [zero_add] using hh)

end Hf4Actual

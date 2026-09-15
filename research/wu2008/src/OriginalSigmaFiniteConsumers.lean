import OriginalProfileSigmaPayment

namespace OriginalProfileSigmaPayment
open Real NodeExtension ActualNineFeedback FirstFeedbackIntegrals Wu04WholeCollection
noncomputable section

/-- Positivity of the already-paid first feedback's coefficient; no J is re-evaluated. -/
theorem first_coefficient_nonneg {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) :
    0 ≤ firstACoefficient s S := by
  have h0 := low_nonneg ((one_le_div (by linarith : 0<S-1)).mpr
    (by linarith : S-1 ≤ 4))
  have h1 := low_nonneg ((one_le_div (by linarith : 0<s-1)).mpr
    (by linarith : s-1 ≤ S-1))
  unfold firstACoefficient jWeight
  positivity

/-- The parent's complete first-J payment consumes the new fully finite common profile bound. -/
theorem firstFeedback_finite_profile_lower {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3<S) (hS5 : S ≤ 5) (hsS : s ≤ S)
    (hr : 2 ≤ S-S/s) (hS2 : S-2 ≤ upperNode 0) :
    firstACoefficient s S*aFiniteLower z+firstResidual z s S  ≤  firstFeedback z s S := by
  exact (add_le_add
    (mul_le_mul_of_nonneg_left (aFiniteLower_le_aProfile hz)
      (first_coefficient_nonneg hs hS.le hS5 hsS)) le_rfl).trans
    (firstFeedback_affine_lower hz hs hS hS5 hsS hr hS2)

/-- The zero-forcing terminal retains both the now-finite common profile and every e cell. -/
theorem terminal_finite_profile_lower {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    low 2*aFiniteLower z+eCells z 3  ≤  firstFeedback z 3 3 := by
  exact (add_le_add
    (mul_le_mul_of_nonneg_left (aFiniteLower_le_aProfile hz) (low_nonneg (x := 2) (by norm_num)))
      le_rfl).trans (terminal_feedback_paid hz)

theorem original_terminal_finite_profile_lower :
    low 2*aFiniteLower NineFeedbackStrength.originalH+eCells NineFeedbackStrength.originalH 3  ≤ 
      firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminal_finite_profile_lower CoupledIntegralRecovery.originalH_nonneg

end
end OriginalProfileSigmaPayment

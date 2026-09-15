import W09RadiusV2

namespace WuTarget.W09
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
noncomputable section

theorem seed_feedback_actual {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ commonRadius)
    (i : Fin 9) :
    seed i + matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i := by
  have ha := actual_with_loss hd (hr.trans commonRadius_cap) i
  have hl := common_debit_le_half_slack hd hr i
  have hi := increment_le_half_slack i
  rw [seed_eq_publication_add_increment]
  linarith only [ha, hl, hi]

theorem seed_actual_same_delta : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
      seed i + matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i :=
  ⟨commonRadius, commonRadius_pos, commonRadius_cap,
    fun _ hd hr i => seed_feedback_actual hd hr i⟩

theorem seed_le_actual {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ commonRadius) (i : Fin 9) :
    seed i ≤ actualNine δ i :=
  (le_add_of_nonneg_right (matrixApply_nonneg feedbackMatrix_nonneg
    (actualNine_nonneg hd (hr.trans commonRadius_cap)) i)).trans
      (seed_feedback_actual hd hr i)

theorem seed_paid_update {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ commonRadius)
    {x y : Fin 9 → ℝ} (hx : ∀ i, x i ≤ actualNine δ i)
    (hy : ∀ i, y i ≤ seed i + matrixApply feedbackMatrix x i) :
    ∀ i, y i ≤ actualNine δ i := by
  intro i
  exact (hy i).trans ((add_le_add le_rfl
    (matrixApply_mono feedbackMatrix_nonneg hx i)).trans
      (seed_feedback_actual hd hr i))

theorem seed_twentyone_actual {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ commonRadius)
    (j : Fin 21) :
    matrixApply transferMatrix seed j ≤
      wuImprovementLimit false δ (rNode (j.val + 1)) :=
  (matrixApply_mono transferMatrix_nonneg (seed_le_actual hd hr) j).trans
    (actual_twentyone_matrix hd (hr.trans commonRadius_cap) j)

end
end WuTarget.W09

import W17JointSplit

noncomputable section
namespace WuTarget.W17Joint
open NodeExtension ActualNineFeedback
open scoped BigOperators

theorem symbolic_matrix_bounds (i k : Fin 9) :
    0 ≤ jointMatrix i k ∧ Wu04Bypass.M i k ≤ jointMatrix i k ∧
      jointMatrix i k ≤ feedbackMatrix i k :=
  ⟨jointMatrix_nonneg i k, baseline_le_jointMatrix i k,
    jointMatrix_le_feedbackMatrix i k⟩

theorem symbolic_apply_le_feedback {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    (i : Fin 9) :
    matrixApply jointMatrix z i ≤ matrixApply feedbackMatrix z i :=
  Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (jointMatrix_le_feedbackMatrix i k) (hz k))

theorem symbolic_seed_nonneg (i : Fin 9) : 0 ≤ W09.seed i :=
  W09.seed_nonneg i

theorem symbolic_seed_stronger (i : Fin 8) :
    NineFeedbackStrength.publication i.castSucc < W09.seed i.castSucc :=
  W09.seed_strictly_stronger i

theorem symbolic_actual_with_seed {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ W09.commonRadius) (i : Fin 9) :
    W09.seed i + matrixApply jointMatrix (actualNine δ) i ≤ actualNine δ i :=
  (add_le_add le_rfl
    (symbolic_apply_le_feedback
      (actualNine_nonneg hd (hr.trans W09.commonRadius_cap)) i)).trans
    (W09.seed_feedback_actual hd hr i)

theorem symbolic_seed_le_actual {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ W09.commonRadius) (i : Fin 9) :
    W09.seed i ≤ actualNine δ i :=
  W09.seed_le_actual hd hr i

theorem symbolic_same_delta_system :
    (∀ i k : Fin 9, 0 ≤ jointMatrix i k) ∧
    (∀ i k : Fin 9, Wu04Bypass.M i k ≤ jointMatrix i k) ∧
    (∀ i : Fin 9, 0 ≤ W09.seed i) ∧
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d →
        (∀ i : Fin 9, W09.seed i ≤ actualNine δ i) ∧
        (∀ i : Fin 9, W09.seed i + matrixApply jointMatrix (actualNine δ) i ≤
          actualNine δ i) :=
  ⟨jointMatrix_nonneg, baseline_le_jointMatrix, symbolic_seed_nonneg,
    W09.commonRadius, W09.commonRadius_pos, W09.commonRadius_cap,
    fun _ hd hr => ⟨symbolic_seed_le_actual hd hr, symbolic_actual_with_seed hd hr⟩⟩

theorem symbolic_paid_update {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ W09.commonRadius)
    {x y : Fin 9 → ℝ} (hx : ∀ k, x k ≤ actualNine δ k)
    (hy : ∀ i, y i ≤ W09.seed i + matrixApply jointMatrix x i) :
    ∀ i, y i ≤ actualNine δ i := by
  intro i
  exact (hy i).trans
    ((add_le_add le_rfl (matrixApply_mono jointMatrix_nonneg hx i)).trans
      (symbolic_actual_with_seed hd hr i))

end WuTarget.W17Joint

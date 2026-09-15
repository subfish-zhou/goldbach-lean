import W17JointTable

noncomputable section
namespace WuTarget.W17Joint
open Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped BigOperators

def seedQ : Fin 9 → ℚ :=
  ![15826959223/1000000000000, 15255699828/1000000000000,
    13904075181/1000000000000, 11781229047/1000000000000,
    9411030887/1000000000000, 6562045207/1000000000000,
    3537860555/1000000000000, 1056766244/1000000000000, 0]

def seed (i : Fin 9) : ℝ := seedQ i

theorem seed_eq (i : Fin 9) : seed i = W09.seed i := rfl

theorem seed_nonneg (i : Fin 9) : 0 ≤ seed i := W09.seed_nonneg i

theorem seed_stronger (i : Fin 8) :
    NineFeedbackStrength.publication i.castSucc < seed i.castSucc :=
  W09.seed_strictly_stronger i

theorem terminal_seed : seed 8 = 0 := W09.terminal_seed

theorem matrix_nonneg (i k : Fin 9) : 0 ≤ matrix i k := by
  rw [matrix_eq_jointMatrix]
  exact jointMatrix_nonneg i k

theorem matrixQ_nonneg (i k : Fin 9) : 0 ≤ matrixQ i k := by
  exact_mod_cast matrix_nonneg i k

theorem matrix_le_feedbackMatrix (i k : Fin 9) : matrix i k ≤ feedbackMatrix i k := by
  rw [matrix_eq_jointMatrix]
  exact jointMatrix_le_feedbackMatrix i k

theorem baseline_le_matrix (i k : Fin 9) : Wu04Bypass.M i k ≤ matrix i k := by
  rw [matrix_eq_jointMatrix]
  exact baseline_le_jointMatrix i k

theorem matrix_coupled (i : Fin 4) (k : Fin 9) :
    matrix ⟨i.val, by omega⟩ k =
      rationalSigmaMatrix ⟨i.val, by omega⟩ k +
        (RemainingHf.paidCell (coupledRow i).kappa1
            (FirstFeedbackIntegrals.cellLeft ((coupledRow i).kappa1 - 2) k)
            (upperNode k) / 5 +
          4 * W04.clippedCell (coupledRow i).S k / 5 +
          (W05.rationalJCoefficient (coupledRow i).s (coupledRow i).S k +
            W05.rationalJCoefficient (coupledRow i).kappa2 (coupledRow i).S k +
            W05.rationalJCoefficient (coupledRow i).kappa3 (coupledRow i).S k) / 5 +
          W07.paidTable i k) := by
  rw [matrix_eq_jointMatrix]
  simp only [jointMatrix, remainderMatrix, W08.paidMatrix, W04.extraMatrix,
    W04.coupledExtra, W05.jTable_eq, W05.rationalJMatrix, W05.assembleJ,
    W07.paidMatrix, dif_pos i.isLt]

theorem matrix_first (i : Fin 5) (k : Fin 9) :
    matrix ⟨i.val + 4, by omega⟩ k =
      rationalSigmaMatrix ⟨i.val + 4, by omega⟩ k +
        (RemainingHf.paidCell (firstS i)
            (FirstFeedbackIntegrals.cellLeft (firstS i - 2) k) (upperNode k) +
          W05.rationalJCoefficient (firstNode i) (firstS i) k / 2) := by
  rw [matrix_eq_jointMatrix]
  simp only [jointMatrix, remainderMatrix, W08.paidMatrix, W04.extraMatrix,
    W05.jTable_eq, W05.rationalJMatrix, W05.assembleJ, W07.paidMatrix,
    show ¬i.val + 4 < 4 by omega, dif_neg, Nat.add_sub_cancel, add_zero]

theorem matrix_apply_le_feedback {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    matrixApply matrix z i ≤ matrixApply feedbackMatrix z i :=
  Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (matrix_le_feedbackMatrix i k) (hz k))

theorem actual_with_seed {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ W09.commonRadius)
    (i : Fin 9) :
    seed i + matrixApply matrix (actualNine δ) i ≤ actualNine δ i :=
  (add_le_add le_rfl
    (matrix_apply_le_feedback (actualNine_nonneg hd (hr.trans W09.commonRadius_cap)) i)).trans
      (W09.seed_feedback_actual hd hr i)

theorem actual_seed_lower {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ W09.commonRadius)
    (i : Fin 9) : seed i ≤ actualNine δ i :=
  W09.seed_le_actual hd hr i

theorem same_delta_system :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d →
        (∀ i : Fin 9, seed i ≤ actualNine δ i) ∧
        (∀ i : Fin 9, seed i + matrixApply matrix (actualNine δ) i ≤ actualNine δ i) :=
  ⟨W09.commonRadius, W09.commonRadius_pos, W09.commonRadius_cap,
    fun _ hd hr => ⟨actual_seed_lower hd hr, actual_with_seed hd hr⟩⟩

theorem rational_actual_system :
    (∀ i k : Fin 9, 0 ≤ matrixQ i k) ∧
    (∀ i : Fin 9, (0 : ℝ) ≤ (seedQ i : ℝ)) ∧
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
        (seedQ i : ℝ) + ∑ k : Fin 9, (matrixQ i k : ℝ) * actualNine δ k ≤
          actualNine δ i := by
  refine ⟨matrixQ_nonneg, seed_nonneg, W09.commonRadius,
    W09.commonRadius_pos, W09.commonRadius_cap, ?_⟩
  intro δ hd hr i
  exact actual_with_seed hd hr i

theorem paid_update {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ W09.commonRadius)
    {x y : Fin 9 → ℝ} (hx : ∀ k, x k ≤ actualNine δ k)
    (hy : ∀ i, y i ≤ seed i + matrixApply matrix x i) :
    ∀ i, y i ≤ actualNine δ i := by
  intro i
  exact (hy i).trans ((add_le_add le_rfl (matrixApply_mono matrix_nonneg hx i)).trans
    (actual_with_seed hd hr i))

end WuTarget.W17Joint

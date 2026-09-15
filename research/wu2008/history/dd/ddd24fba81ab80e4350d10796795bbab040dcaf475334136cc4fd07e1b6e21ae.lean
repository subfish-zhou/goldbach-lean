import W05JTables

noncomputable section
namespace WuTarget.W05
open Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped BigOperators

def jTable : Fin 9 → Fin 9 → ℝ :=
  ![fun k => (coupledTable0_s k + coupledTable0_kappa2 k + coupledTable0_kappa3 k) / 5,
    fun k => (coupledTable1_s k + coupledTable1_kappa2 k + coupledTable1_kappa3 k) / 5,
    fun k => (coupledTable2_s k + coupledTable2_kappa2 k + coupledTable2_kappa3 k) / 5,
    fun k => (coupledTable3_s k + coupledTable3_kappa2 k + coupledTable3_kappa3 k) / 5,
    fun k => firstTable0 k / 2, fun k => firstTable1 k / 2,
    fun k => firstTable2 k / 2, fun k => firstTable3 k / 2, fun k => firstTable4 k / 2]

theorem jTable_eq (i k : Fin 9) : jTable i k = rationalJMatrix i k := by
  fin_cases i
  · change (coupledTable0_s k + coupledTable0_kappa2 k + coupledTable0_kappa3 k) / 5 = _
    rw [← coupledTable0_s_exact, ← coupledTable0_kappa2_exact, ← coupledTable0_kappa3_exact]
    rfl
  · change (coupledTable1_s k + coupledTable1_kappa2 k + coupledTable1_kappa3 k) / 5 = _
    rw [← coupledTable1_s_exact, ← coupledTable1_kappa2_exact, ← coupledTable1_kappa3_exact]
    rfl
  · change (coupledTable2_s k + coupledTable2_kappa2 k + coupledTable2_kappa3 k) / 5 = _
    rw [← coupledTable2_s_exact, ← coupledTable2_kappa2_exact, ← coupledTable2_kappa3_exact]
    rfl
  · change (coupledTable3_s k + coupledTable3_kappa2 k + coupledTable3_kappa3 k) / 5 = _
    rw [← coupledTable3_s_exact, ← coupledTable3_kappa2_exact, ← coupledTable3_kappa3_exact]
    rfl
  · change firstTable0 k / 2 = _
    rw [← firstTable0_exact]
    rfl
  · change firstTable1 k / 2 = _
    rw [← firstTable1_exact]
    rfl
  · change firstTable2 k / 2 = _
    rw [← firstTable2_exact]
    rfl
  · change firstTable3 k / 2 = _
    rw [← firstTable3_exact]
    rfl
  · change firstTable4 k / 2 = _
    rw [← firstTable4_exact]
    rfl

theorem jTable_nonneg (i k : Fin 9) : 0 ≤ jTable i k := by
  rw [jTable_eq]
  exact rationalJMatrix_nonneg i k

theorem table_separated_payment {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    otherFeedback z i + aProfile (nineProfile z) * jSigmaWeight i +
      ∑ k : Fin 9, jTable i k * z k ≤ feedback z i := by
  apply le_trans _ (feedback_separated_payment hz i)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  rw [jTable_eq]
  exact mul_le_mul_of_nonneg_right (rationalJMatrix_le i k) (hz k)

theorem table_matrix_paid (i k : Fin 9) :
    Wu04Bypass.M i k + jTable i k ≤ feedbackMatrix i k := by
  rw [jTable_eq]
  exact paidMatrix_le i k

theorem table_feedback_paid {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    (∑ k : Fin 9, (Wu04Bypass.M i k + jTable i k) * z k) ≤ feedback z i := by
  simpa only [jTable_eq, paidMatrix, matrixApply] using paid_feedback hz i

theorem v8_table_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
      base i - deltaLoss δ * loss i +
        (∑ k : Fin 9, (Wu04Bypass.M i k + jTable i k) * Wu04Bypass.v8 k) ≤
          actualNine δ i := by
  simpa only [jTable_eq, paidMatrix, matrixApply] using v8_paid_actual

theorem first_row_last_coefficient : jTable 4 8 = 49 / 7740 := by
  change ((49 : ℝ) / 3870) / 2 = _
  norm_num

theorem first_row_strict_increment :
    Wu04Bypass.M 4 8 < Wu04Bypass.M 4 8 + jTable 4 8 := by
  rw [first_row_last_coefficient]
  linarith

theorem terminal_table_zero (k : Fin 9) : jTable 8 k = 0 := by
  rw [jTable_eq]
  exact terminal_rationalJMatrix_zero k

end WuTarget.W05

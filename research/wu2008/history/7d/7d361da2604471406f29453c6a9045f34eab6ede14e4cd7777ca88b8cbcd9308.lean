import MathlibNt.Wu2008DoubleSieve.TableFeedbackGeometry

/-!
# The five actual first-functional rows of the source system

The column vector is the actual upper improvement at the nine source
endpoints, not a proposed numerical table.
-/

namespace Wu2008DoubleSieve

open Real
open scoped BigOperators Interval Matrix

theorem tableFeedback_actual_row {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (i : Fin 5) :
    tableFeedbackScalar δ i +
      ∑ j : Fin 9, tableFeedbackMatrix i j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ (tableFeedbackS i) := by
  obtain ⟨hs, hs3, ht, ht5, hratio⟩ := tableFeedback_parameters i
  have hp := tableFeedback_first_partition hδ hδhi hs hs3 ht ht5 hratio
    tableFeedbackR_monotone tableFeedbackR_first tableFeedbackR_last
  have heq :
      (∑ j : Fin 9, tableFeedbackMatrix i j * tableFeedbackActualVector δ j) =
        ∑ k ∈ Finset.range 9, wuImprovementLimit true δ (tableFeedbackR (k + 1)) *
          ∫ x in tableFeedbackR k..tableFeedbackR (k + 1),
            firstFeedbackXi x (tableFeedbackS i) (tableFeedbackT i) := by
    simp only [tableFeedbackMatrix, tableFeedbackActualVector]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (∫ x in tableFeedbackR k..tableFeedbackR (k + 1),
        firstFeedbackXi x (tableFeedbackS i) (tableFeedbackT i)) *
          wuImprovementLimit true δ (tableFeedbackR (k + 1))) 9]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [heq]
  exact hp

theorem tableFeedback_actual_matrix_rows {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∀ i : Fin 5, tableFeedbackScalar δ i +
      (tableFeedbackMatrix *ᵥ tableFeedbackActualVector δ) i ≤
      tableFeedbackActualVector δ (tableFeedbackRowIndex i) := by
  intro i
  rw [tableFeedbackActualVector, tableFeedback_row_endpoint]
  exact tableFeedback_actual_row hδ hδhi i

theorem tableFeedback_actual_source_rows {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (i : Fin 5) :
    firstFunctionalGainPsiOne (tableFeedbackS i) (tableFeedbackT i) -
        (2 * δ / (1 - 2 * δ)) *
          omega3XIntegralEnvelope (tableFeedbackS i) (tableFeedbackT i) +
      ∑ j : Fin 9, tableFeedbackMatrix i j * tableFeedbackActualVector δ j ≤
      tableFeedbackActualVector δ (tableFeedbackRowIndex i) := by
  rw [← tableFeedbackScalar_eq_source_sub_penalty hδhi i]
  exact tableFeedback_actual_matrix_rows hδ hδhi i

theorem tableFeedback_row_26 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    firstFunctionalGainPsi δ (26 / 10) (358 / 100) +
      ∑ j : Fin 9, tableFeedbackMatrix 0 j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ (26 / 10) := by
  have hs : tableFeedbackS 0 = 26 / 10 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 0 = 358 / 100 := rfl
  simpa only [tableFeedbackScalar, hs, ht] using tableFeedback_actual_row hδ hδhi 0

theorem tableFeedback_row_27 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    firstFunctionalGainPsi δ (27 / 10) (347 / 100) +
      ∑ j : Fin 9, tableFeedbackMatrix 1 j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ (27 / 10) := by
  have hs : tableFeedbackS 1 = 27 / 10 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 1 = 347 / 100 := rfl
  simpa only [tableFeedbackScalar, hs, ht] using tableFeedback_actual_row hδ hδhi 1

theorem tableFeedback_row_28 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    firstFunctionalGainPsi δ (28 / 10) (334 / 100) +
      ∑ j : Fin 9, tableFeedbackMatrix 2 j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ (28 / 10) := by
  have hs : tableFeedbackS 2 = 28 / 10 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 2 = 334 / 100 := rfl
  simpa only [tableFeedbackScalar, hs, ht] using tableFeedback_actual_row hδ hδhi 2

theorem tableFeedback_row_29 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    firstFunctionalGainPsi δ (29 / 10) (319 / 100) +
      ∑ j : Fin 9, tableFeedbackMatrix 3 j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ (29 / 10) := by
  have hs : tableFeedbackS 3 = 29 / 10 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 3 = 319 / 100 := rfl
  simpa only [tableFeedbackScalar, hs, ht] using tableFeedback_actual_row hδ hδhi 3

theorem tableFeedback_row_30 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∑ j : Fin 9, tableFeedbackMatrix 4 j * tableFeedbackActualVector δ j ≤
      wuImprovementLimit true δ 3 := by
  have hs : tableFeedbackS 4 = 3 := by norm_num [tableFeedbackS]
  simpa only [tableFeedbackScalar_last, zero_add, hs] using
    tableFeedback_actual_row hδ hδhi 4

end Wu2008DoubleSieve

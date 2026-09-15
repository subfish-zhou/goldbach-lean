import MathlibNt.Wu2008DoubleSieve.TableFeedbackPartition
import Mathlib.Data.Matrix.Mul

/-!
# The original nine cells and five first-functional parameter pairs

Zero-based column j is source column j+1. Zero-based row i is source
row i+5, so no second-functional row is supplied by these definitions.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped BigOperators Interval

noncomputable def tableFeedbackR (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 + ((n : ℝ) + 1) / 10

theorem tableFeedbackR_first : tableFeedbackR 0 = 1 := by
  norm_num [tableFeedbackR]

theorem tableFeedbackR_last : tableFeedbackR 9 = 3 := by
  norm_num [tableFeedbackR]

theorem tableFeedbackR_monotone : Monotone tableFeedbackR := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => norm_num [tableFeedbackR]
  | succ n =>
    simp only [tableFeedbackR, Nat.succ_ne_zero, if_false, Nat.cast_succ]
    linarith

noncomputable def tableFeedbackS (i : Fin 5) : ℝ := (26 + (i.val : ℝ)) / 10

noncomputable def tableFeedbackT : Fin 5 → ℝ :=
  ![358 / 100, 347 / 100, 334 / 100, 319 / 100, 3]

def tableFeedbackRowIndex (i : Fin 5) : Fin 9 :=
  ⟨i.val + 4, by omega⟩

theorem tableFeedback_parameters (i : Fin 5) :
    2 ≤ tableFeedbackS i ∧ tableFeedbackS i ≤ 3 ∧
      3 ≤ tableFeedbackT i ∧ tableFeedbackT i ≤ 5 ∧
      2 ≤ tableFeedbackT i - tableFeedbackT i / tableFeedbackS i := by
  fin_cases i <;> norm_num [tableFeedbackS, tableFeedbackT]

theorem tableFeedback_row_endpoint (i : Fin 5) :
    tableFeedbackR ((tableFeedbackRowIndex i).val + 1) = tableFeedbackS i := by
  fin_cases i <;> norm_num [tableFeedbackR, tableFeedbackRowIndex, tableFeedbackS]

theorem tableFeedback_endpoint_bounds (j : Fin 9) :
    tableFeedbackR (j.val + 1) ∈ Icc (1 : ℝ) 3 := by
  constructor
  · rw [← tableFeedbackR_first]
    exact tableFeedbackR_monotone (Nat.zero_le _)
  · rw [← tableFeedbackR_last]
    exact tableFeedbackR_monotone (by omega)

noncomputable def tableFeedbackMatrix : Matrix (Fin 5) (Fin 9) ℝ :=
  fun i j => ∫ x in tableFeedbackR j.val..tableFeedbackR (j.val + 1),
    firstFeedbackXi x (tableFeedbackS i) (tableFeedbackT i)

noncomputable def tableFeedbackActualVector (δ : ℝ) : Fin 9 → ℝ :=
  fun j => wuImprovementLimit true δ (tableFeedbackR (j.val + 1))

noncomputable def tableFeedbackScalar (δ : ℝ) : Fin 5 → ℝ :=
  fun i => firstFunctionalGainPsi δ (tableFeedbackS i) (tableFeedbackT i)

theorem tableFeedbackMatrix_nonneg (i : Fin 5) (j : Fin 9) :
    0 ≤ tableFeedbackMatrix i j := by
  obtain ⟨hs, hs3, ht, ht5, _⟩ := tableFeedback_parameters i
  apply intervalIntegral.integral_nonneg (tableFeedbackR_monotone (Nat.le_succ j.val))
  intro x hx
  have hsub := tableFeedback_cell_subset tableFeedbackR_monotone
    tableFeedbackR_first tableFeedbackR_last j.isLt
  rw [uIcc_of_le (tableFeedbackR_monotone (Nat.le_succ j.val)),
    uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hsub
  exact firstFeedbackXi_nonneg hs hs3 ht ht5 (hsub hx)

theorem tableFeedbackActualVector_nonneg {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (j : Fin 9) :
    0 ≤ tableFeedbackActualVector δ j :=
  wuImprovementLimit_nonneg true hδ (by linarith)
    (tableFeedback_endpoint_bounds j).1 (by linarith [(tableFeedback_endpoint_bounds j).2])

theorem tableFeedbackScalar_eq_source_sub_penalty {δ : ℝ}
    (hδhi : δ ≤ 1 / 10) (i : Fin 5) :
    tableFeedbackScalar δ i =
      firstFunctionalGainPsiOne (tableFeedbackS i) (tableFeedbackT i) -
        (2 * δ / (1 - 2 * δ)) *
          omega3XIntegralEnvelope (tableFeedbackS i) (tableFeedbackT i) := by
  obtain ⟨hs, hs3, ht, ht5, _⟩ := tableFeedback_parameters i
  exact firstFunctionalGainPsi_eq_source_sub_penalty (by linarith) hs hs3 ht ht5

theorem tableFeedbackScalar_last (δ : ℝ) : tableFeedbackScalar δ 4 = 0 := by
  have hs : tableFeedbackS 4 = 3 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 4 = 3 := rfl
  rw [tableFeedbackScalar, hs, ht, firstFunctionalGainPsi_self]

end Wu2008DoubleSieve

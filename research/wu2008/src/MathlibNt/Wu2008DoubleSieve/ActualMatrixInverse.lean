import MathlibNt.Wu2008DoubleSieve.ActualMatrixContraction
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed

/-! A genuine nonnegative Neumann inverse of the unchanged integral matrix. -/
namespace Wu2008DoubleSieve.ActualMatrixInverse
open SecondFunctionalPositive ActualMatrixContraction
open scoped Classical BigOperators Matrix.Norms.Operator NNReal

theorem actual_operator_norm_le : ‖matrix‖ ≤ (4/5:ℝ) := by
  have h : ‖matrix‖₊ ≤ (⟨4/5, by norm_num⟩ : ℝ≥0) := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    change ((∑ j, ‖matrix i j‖₊ : ℝ≥0) : ℝ) ≤ (4/5:ℝ)
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (matrix_nonnegative _ _)] using actual_matrix_row_sum i
  exact h

theorem actual_operator_norm_lt_one : ‖matrix‖ < 1 :=
  actual_operator_norm_le.trans_lt (by norm_num)

theorem actual_powers_summable : Summable (fun n : ℕ => matrix ^ n) :=
  summable_geometric_of_norm_lt_one actual_operator_norm_lt_one

noncomputable def Q : Matrix (Fin 4) (Fin 4) ℝ := ∑' n : ℕ, matrix ^ n

theorem Q_mul_one_sub : Q * (1-matrix) = 1 :=
  geom_series_mul_neg matrix actual_operator_norm_lt_one

theorem one_sub_mul_Q : (1-matrix) * Q = 1 :=
  mul_neg_geom_series matrix actual_operator_norm_lt_one

theorem Q_nonnegative (i j : Fin 4) : 0 ≤ Q i j := by
  have hs : HasSum (fun n : ℕ => (matrix ^ n : Fin 4 → Fin 4 → ℝ)) Q :=
    actual_powers_summable.hasSum
  exact HasSum.nonneg (fun n => Matrix.pow_apply_nonneg matrix_nonnegative n i j)
    (Pi.hasSum.mp (Pi.hasSum.mp hs i) j)

end Wu2008DoubleSieve.ActualMatrixInverse

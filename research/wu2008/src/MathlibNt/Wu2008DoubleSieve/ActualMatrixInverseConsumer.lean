import MathlibNt.Wu2008DoubleSieve.ActualMatrixInverse
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCompactTailMother

/-! The actual nonnegative inverse acts on the original and effective compact sources. -/
namespace Wu2008DoubleSieve.ActualMatrixInverse
open SecondFunctionalPositive
open scoped BigOperators

theorem Q_mulVec_mono {x y : Fin 4 → ℝ} (h : x ≤ y) : Q.mulVec x ≤ Q.mulVec y := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (Q_nonnegative i j))

/-- A linear-order step for the proved actual matrix and its constructed actual inverse. -/
theorem solve_actual_rows {x b : Fin 4 → ℝ} (h : matrix.mulVec x + b ≤ x) :
    Q.mulVec b ≤ x := by
  have hb : b ≤ (1-matrix).mulVec x := by
    intro i
    have hi := h i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    change matrix.mulVec x i + b i ≤ x i at hi
    linarith only [hi]
  have hq := Q_mulVec_mono hb
  simpa only [Matrix.mulVec_mulVec, Q_mul_one_sub, Matrix.one_mulVec] using hq

/-- The source and the nonnegative tail both come from the original proved rows. -/
theorem actual_lower_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (literalSource δ + literalTail δ) ≤ actualVector δ := by
  apply solve_actual_rows
  simpa only [add_assoc] using SecondFunctionalPositive.matrix_rows_with_tail hδ hδhi

theorem actual_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (literalSource δ) ≤ actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (actual_lower_with_tail hδ hδhi)

noncomputable def compactSource (δ : ℝ) (m : Fin 4 → ℕ) (P : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => SecondFunctionalCompactTail.source (parameters i) δ (m i) (P i)

/-- The actual inverse consumes the proved effective compact-tail rows, without hRows or hInverse. -/
theorem compact_lower_with_tail (m : Fin 4 → ℕ) (hm : ∀ i, 3 ≤ m i)
    (P : Fin 4 → ℝ) (hP : ∀ i, max 2 (((m i : ℝ) + 6) / 2) ≤ P i)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (compactSource δ m P + literalTail δ) ≤ actualVector δ := by
  apply solve_actual_rows
  change matrix.mulVec (actualVector δ) +
    ((fun i => SecondFunctionalCompactTail.source (parameters i) δ (m i) (P i)) +
      literalTail δ) ≤ actualVector δ
  simpa only [add_assoc] using
    SecondFunctionalCompactTail.matrix_rows_with_tail m hm P hP hδ hδhi

theorem compact_lower (m : Fin 4 → ℕ) (hm : ∀ i, 3 ≤ m i)
    (P : Fin 4 → ℝ) (hP : ∀ i, max 2 (((m i : ℝ) + 6) / 2) ≤ P i)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (compactSource δ m P) ≤ actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (compact_lower_with_tail m hm P hP hδ hδhi)

end Wu2008DoubleSieve.ActualMatrixInverse

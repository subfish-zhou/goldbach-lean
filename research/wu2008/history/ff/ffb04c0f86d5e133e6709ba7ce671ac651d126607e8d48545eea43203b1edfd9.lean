import MathlibNt.Wu2008DoubleSieve.TableFeedbackRows

/-!
# Finite inverse-positive certificates

These are algebraic certificate consumers, not numerical certificates
and not additional analytical rows. Nonnegativity of the inverse, not
merely the subsolution inequality, supplies the comparison direction.
-/

namespace Wu2008DoubleSieve

open scoped BigOperators Matrix

theorem tableFeedback_mulVec_mono {m n : Type*} [Fintype n]
    {Q : Matrix m n ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    {u v : n → ℝ} (huv : u ≤ v) :
    Q *ᵥ u ≤ Q *ᵥ v := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hQ i j))

theorem tableFeedback_mulVec_lower_coefficients {m n : Type*} [Fintype n]
    {Aminus A : Matrix m n ℝ} {X : n → ℝ}
    (hA : ∀ i j, Aminus i j ≤ A i j) (hX : ∀ j, 0 ≤ X j) :
    Aminus *ᵥ X ≤ A *ᵥ X := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hA i j) (hX j))

theorem tableFeedback_inverse_positive_compare {n : Type*} [Fintype n] [DecidableEq n]
    {A Q : Matrix n n ℝ} {X b w : n → ℝ}
    (hactual : b + A *ᵥ X ≤ X)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQI : Q * (1 - A) = 1)
    (hw : (1 - A) *ᵥ w ≤ b) :
    w ≤ X := by
  have hb : b ≤ (1 - A) *ᵥ X := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    intro i
    have hi := hactual i
    change b i + (A *ᵥ X) i ≤ X i at hi
    change b i ≤ X i - (A *ᵥ X) i
    linarith
  have hm := tableFeedback_mulVec_mono hQ (hw.trans hb)
  simpa only [Matrix.mulVec_mulVec, hQI, Matrix.one_mulVec] using hm

theorem tableFeedback_inverse_positive_lower_matrix_compare
    {n : Type*} [Fintype n] [DecidableEq n]
    {Aminus A Q : Matrix n n ℝ} {X b w : n → ℝ}
    (hactual : b + A *ᵥ X ≤ X) (hX : ∀ j, 0 ≤ X j)
    (hA : ∀ i j, Aminus i j ≤ A i j)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQI : Q * (1 - Aminus) = 1)
    (hw : (1 - Aminus) *ᵥ w ≤ b) :
    w ≤ X := by
  apply tableFeedback_inverse_positive_compare (A := Aminus) (b := b) ?_ hQ hQI hw
  have hm := tableFeedback_mulVec_lower_coefficients hA hX
  intro i
  have hi := hactual i
  have hmi := hm i
  change b i + (A *ᵥ X) i ≤ X i at hi
  change b i + (Aminus *ᵥ X) i ≤ X i
  linarith

theorem tableFeedback_inverse_positive_rational_compare
    {n : Type*} [Fintype n] [DecidableEq n]
    (Aminus : Matrix n n ℚ) {A Q : Matrix n n ℝ} {X b w : n → ℝ}
    (hactual : b + A *ᵥ X ≤ X) (hX : ∀ j, 0 ≤ X j)
    (hA : ∀ i j, (Aminus i j : ℝ) ≤ A i j)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hQI : Q * (1 - Aminus.map (fun q => (q : ℝ))) = 1)
    (hw : (1 - Aminus.map (fun q => (q : ℝ))) *ᵥ w ≤ b) :
    w ≤ X :=
  tableFeedback_inverse_positive_lower_matrix_compare hactual hX hA hQ hQI hw

theorem tableFeedback_actual_rational_rows {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (Aminus : Matrix (Fin 5) (Fin 9) ℚ)
    (hA : ∀ i j, (Aminus i j : ℝ) ≤ tableFeedbackMatrix i j) :
    ∀ i : Fin 5, tableFeedbackScalar δ i +
      ∑ j : Fin 9, (Aminus i j : ℝ) * tableFeedbackActualVector δ j ≤
      tableFeedbackActualVector δ (tableFeedbackRowIndex i) := by
  have hm := tableFeedback_mulVec_lower_coefficients hA
    (tableFeedbackActualVector_nonneg hδ hδhi)
  intro i
  have hi := tableFeedback_actual_matrix_rows hδ hδhi i
  have hmi := hm i
  change (∑ j : Fin 9, (Aminus i j : ℝ) * tableFeedbackActualVector δ j) ≤
    ∑ j : Fin 9, tableFeedbackMatrix i j * tableFeedbackActualVector δ j at hmi
  change tableFeedbackScalar δ i +
    (∑ j : Fin 9, tableFeedbackMatrix i j * tableFeedbackActualVector δ j) ≤
    tableFeedbackActualVector δ (tableFeedbackRowIndex i) at hi
  linarith

end Wu2008DoubleSieve

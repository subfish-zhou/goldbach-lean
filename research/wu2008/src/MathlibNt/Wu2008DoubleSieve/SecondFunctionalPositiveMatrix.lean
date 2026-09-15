import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveCoefficients

/-! The four actual nonnegative rows and their future entrywise certificate interface. -/
namespace Wu2008DoubleSieve.SecondFunctionalPositive
open Set MeasureTheory MotherPair SecondFunctionalParameters FourthRowPhiOmega2
open SecondFunctionalCoupledFeedback
open scoped BigOperators Interval

noncomputable def parameters : Fin 4 → SecondFunctionalParameters := ![row1, row2, row3, row4]

 theorem parameters_analytic (i : Fin 4) : AnalyticParameters (parameters i) := by
  revert i
  simp only [Fin.forall_fin_succ]
  exact ⟨SecondFunctionalCoupled.row1_analytic, SecondFunctionalCoupled.row2_analytic,
    SecondFunctionalCoupled.row3_analytic, SecondFunctionalCoupled.row4_analytic, fun i => Fin.elim0 i⟩

 theorem parameters_sample (i : Fin 4) : (parameters i).s = sample i := by
  revert i
  simp only [Fin.forall_fin_succ]
  norm_num [parameters, sample, grid, row1, row2, row3, row4]
  constructor <;> rfl

 theorem samples_literal : sample = ![(22/10:ℝ), 23/10, 24/10, 25/10] := by
  funext i
  revert i
  simp only [Fin.forall_fin_succ]
  norm_num [sample, grid]
  constructor <;> rfl

 theorem entries_literal (p : SecondFunctionalParameters) :
    rowEntry p = ![(∫ v in (1:ℝ)..(22/10:ℝ), density p v)/5,
      (∫ v in (22/10:ℝ)..(23/10:ℝ), density p v)/5,
      (∫ v in (23/10:ℝ)..(24/10:ℝ), density p v)/5,
      (∫ v in (24/10:ℝ)..(25/10:ℝ), density p v)/5] := by
  funext i
  revert i
  simp only [Fin.forall_fin_succ]
  norm_num [rowEntry, grid]
  constructor <;> rfl

noncomputable def matrix : Matrix (Fin 4) (Fin 4) ℝ := fun i j => rowEntry (parameters i) j
noncomputable def literalSource (δ : ℝ) : Fin 4 → ℝ := fun i => source (parameters i) δ
noncomputable def literalTail (δ : ℝ) : Fin 4 → ℝ := fun i => tail (parameters i) δ/5

 theorem matrix_nonnegative : ∀ i j, 0 ≤ matrix i j :=
  fun i j => rowEntry_nonnegative (parameters i) (parameters_analytic i) j

 theorem literalTail_nonnegative {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    0 ≤ literalTail δ := by
  intro i
  exact div_nonneg (actual_tail_nonnegative (parameters i) (parameters_analytic i)
    hδ (by linarith)) (by norm_num)

/-- No point gain, J term, classical term, or same-phi joint supremum has been removed. -/
theorem source_literal (p : SecondFunctionalParameters) (δ : ℝ) :
    source p δ = wuUpperCoefficient p.s +
      (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
        J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S -
        (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 + classical p +
          (2/(1-2*δ)) *
            (omega3XIntegralEnvelope p.kappa3 p.kappa1 + SecondFunctionalCoupled.jointSup p)))/5 := rfl

/-- The stronger actual vector inequality retains the full nonnegative tail. -/
theorem matrix_rows_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    matrix.mulVec (actualVector δ) + literalSource δ + literalTail δ ≤ actualVector δ := by
  intro i
  have h := row_with_tail (parameters i) (parameters_analytic i) hδ hδhi
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, matrix, literalSource, literalTail,
    actualVector, parameters_sample, sample] using h

/-- The advertised matrix inequality is proved from actual_limit, not assumed as hRows. -/
theorem matrix_rows {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    matrix.mulVec (actualVector δ) + literalSource δ ≤ actualVector δ := by
  intro i
  have h := row (parameters i) (parameters_analytic i) hδ hδhi
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, matrix, literalSource,
    actualVector, parameters_sample, sample] using h

 theorem row1_regression {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, matrix 0 j * actualVector δ j) + literalSource δ 0 + literalTail δ 0 ≤
      wuImprovementLimit true δ (22/10) := by
  simpa only [Pi.add_apply, Matrix.mulVec, dotProduct, actualVector, samples_literal,
    Matrix.cons_val_zero] using matrix_rows_with_tail hδ hδhi 0

 theorem row2_regression {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, matrix 1 j * actualVector δ j) + literalSource δ 1 + literalTail δ 1 ≤
      wuImprovementLimit true δ (23/10) := by
  have h := matrix_rows_with_tail hδ hδhi 1
  norm_num [Pi.add_apply, Matrix.mulVec, dotProduct, actualVector, sample, grid] at h ⊢
  exact h

 theorem row3_regression {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, matrix 2 j * actualVector δ j) + literalSource δ 2 + literalTail δ 2 ≤
      wuImprovementLimit true δ (24/10) := by
  have h := matrix_rows_with_tail hδ hδhi 2
  norm_num [Pi.add_apply, Matrix.mulVec, dotProduct, actualVector, sample, grid] at h ⊢
  exact h

 theorem row4_regression {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, matrix 3 j * actualVector δ j) + literalSource δ 3 + literalTail δ 3 ≤
      wuImprovementLimit true δ (25/10) := by
  have h := matrix_rows_with_tail hδ hδhi 3
  norm_num [Pi.add_apply, Matrix.mulVec, dotProduct, actualVector, sample, grid] at h ⊢
  exact h

/-- Future entrywise lower certificates suffice; this asserts neither inverse nor numeric positivity. -/
theorem comparison_rows_with_tail (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, A i j ≤ matrix i j) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    A.mulVec (actualVector δ) + literalSource δ + literalTail δ ≤ actualVector δ := by
  intro i
  have hs : A.mulVec (actualVector δ) i ≤ matrix.mulVec (actualVector δ) i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hA i j)
      (actualVector_nonnegative hδ (by linarith) j)
  have hr := matrix_rows_with_tail hδ hδhi i
  change A.mulVec (actualVector δ) i + literalSource δ i + literalTail δ i ≤ actualVector δ i
  change matrix.mulVec (actualVector δ) i + literalSource δ i + literalTail δ i ≤ actualVector δ i at hr
  linarith only [hs, hr]

 theorem comparison_rows (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, A i j ≤ matrix i j) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    A.mulVec (actualVector δ) + literalSource δ ≤ actualVector δ := by
  intro i
  have ht := literalTail_nonnegative hδ hδhi i
  have hr := comparison_rows_with_tail A hA hδ hδhi i
  change A.mulVec (actualVector δ) i + literalSource δ i ≤ actualVector δ i
  change A.mulVec (actualVector δ) i + literalSource δ i + literalTail δ i ≤ actualVector δ i at hr
  change 0 ≤ literalTail δ i at ht
  linarith only [ht, hr]

end Wu2008DoubleSieve.SecondFunctionalPositive

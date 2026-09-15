import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedSource

namespace Wu2008DoubleSieve.SecondFunctionalSignedCore
open MeasureTheory SecondFunctionalPositive ActualMatrixInverse
open scoped Interval

/-- The displayed residual has exactly the original point gains and weighted integrals. -/
theorem remainder_literal (p : SecondFunctionalParameters) (δ : ℝ) :
    actualGainRemainder p δ =
      (4*wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
        (∫ u in (1-1/p.s)..(1-1/p.S),
          wuImprovementLimit false δ (p.S*u)/(u*(1-u))) +
        (∫ u in (1-1/p.kappa2)..(1-1/p.S),
          wuImprovementLimit false δ (p.S*u)/(u*(1-u))) +
        (∫ u in (1-1/p.kappa3)..(1-1/p.S),
          wuImprovementLimit false δ (p.S*u)/(u*(1-u))))/5 := rfl

/-- The actual H consumer retains the entire integrated feedback. -/
theorem original_H_with_feedback (i : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    D (parameters i) δ/5 + actualGainRemainder (parameters i) δ +
      (∫ v in (1:ℝ)..3, wuImprovementLimit true δ v *
        SecondFunctionalCoupledFeedback.density (parameters i) v)/5 ≤
      wuImprovementLimit true δ (parameters i).s := by
  rw [← original_source_eq i hδ hδhi]
  have h := Omega3ElementaryFeedback.original_actual_limit i hδ hδhi
  unfold Omega3ElementaryFeedback.source SecondFunctionalCoupledFeedback.gain at *
  linarith only [h]

/-- Original matrix rows, retaining both the literal remainder and tail. -/
theorem rows_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    matrix.mulVec (actualVector δ) +
      (fun i => D (parameters i) δ/5 + actualGainRemainder (parameters i) δ) +
      literalTail δ ≤ actualVector δ := by
  simpa only [original_source_eq _ hδ hδhi] using
    Omega3ElementaryFeedback.rows_with_tail hδ hδhi

/-- Actual nonnegative Q consumes the exact signed source and retains the tail. -/
theorem actual_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec ((fun i => D (parameters i) δ/5 + actualGainRemainder (parameters i) δ) +
      literalTail δ) ≤ actualVector δ := by
  simpa only [original_source_eq _ hδ hδhi] using
    Omega3ElementaryFeedback.actual_with_tail hδ hδhi

/-- Removing the tail uses its proved sign through actual Q monotonicity. -/
theorem actual_without_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (fun i => D (parameters i) δ/5 + actualGainRemainder (parameters i) δ) ≤
      actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (actual_with_tail hδ hδhi)

/-- Dropping actual gains does not assert that the remaining signed core is positive. -/
theorem core_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec ((fun i => D (parameters i) δ/5) + literalTail δ) ≤ actualVector δ := by
  apply (Q_mulVec_mono ?_).trans (actual_with_tail hδ hδhi)
  intro i
  change D (parameters i) δ/5 + literalTail δ i ≤
    D (parameters i) δ/5 + actualGainRemainder (parameters i) δ + literalTail δ i
  linarith only [original_remainder_nonneg i hδ hδhi]

/-- Both removals are justified by the actual nonnegative producers. -/
theorem core_without_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (fun i => D (parameters i) δ/5) ≤ actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (core_with_tail hδ hδhi)

end Wu2008DoubleSieve.SecondFunctionalSignedCore

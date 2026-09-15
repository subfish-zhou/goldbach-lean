import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryEnvelope

namespace Wu2008DoubleSieve.Omega3ElementaryFeedback
open MotherPair FourthRowPhiOmega2 SecondFunctionalPositive ActualMatrixInverse
open SecondFunctionalGeometricMass SecondFunctionalFourSevenths
open SecondFunctionalParameters

/-- Each of the four original pairs passes the same fixed symbolic sufficient gate. -/
theorem original_gates (i : Fin 4) :
    19/8 ≤ (parameters i).kappa3 ∧
    (parameters i).kappa3 ≤ (parameters i).kappa1 ∧ (parameters i).kappa1 ≤ 10 := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [row1, row2, row3, row4]

noncomputable def omegaCost (p : SecondFunctionalParameters) : ℝ :=
  (4/7) * Elementary.elementaryMomentOne 1 (1/p.kappa1) (1/p.kappa3)

theorem original_envelope_le (i : Fin 4) :
    omega3XIntegralEnvelope (parameters i).kappa3 (parameters i).kappa1 ≤
      omegaCost (parameters i) :=
  Omega3ElementaryEnvelope.envelope_le (original_gates i).1
    (original_gates i).2.1 (original_gates i).2.2

/-- The only replacement here is the old Omega3 envelope; all other terms stay literal. -/
noncomputable def cost (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
    SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
      (omegaCost p + elementaryCap p)

noncomputable def source (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S - cost p δ)/5

theorem elementary_cost_le (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    elementaryAnalyticCost (parameters i) δ ≤ cost (parameters i) δ := by
  have h := mul_le_mul_of_nonneg_left (original_envelope_le i)
    (show 0 ≤ 2/(1-2*δ) by apply div_nonneg (by norm_num); linarith)
  unfold elementaryAnalyticCost cost
  linarith only [h]

theorem original_cost_le (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    SecondFunctionalCoupledFeedback.cost (parameters i) δ ≤ cost (parameters i) δ := by
  have h := SecondFunctionalFourSevenths.original_cost_le i hδhi
  have he : analyticCost (parameters i) δ = elementaryAnalyticCost (parameters i) δ := by
    unfold analyticCost elementaryAnalyticCost
    rw [analyticCap_eq_elementary _ (original_mother i) (original_s_ge_two i)]
  exact (h.trans_eq he).trans (elementary_cost_le i hδhi)

theorem source_le_elementary (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    source (parameters i) δ ≤ elementaryAnalyticSource (parameters i) δ := by
  have hc := elementary_cost_le i hδhi
  unfold source elementaryAnalyticSource
  linarith only [hc]

theorem source_le_original (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    source (parameters i) δ ≤ SecondFunctionalPositive.source (parameters i) δ := by
  have hc := original_cost_le i hδhi
  unfold source SecondFunctionalPositive.source
  linarith only [hc]

/-- Fixed-delta original H consumer; no positive margin is asserted. -/
theorem original_actual_limit (i : Fin 4) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient (parameters i).s +
      (SecondFunctionalCoupledFeedback.gain (parameters i) δ - cost (parameters i) δ)/5 ≤
      wuImprovementLimit true δ (parameters i).s := by
  have h := SecondFunctionalCoupledFeedback.actual_limit (parameters i) (parameters_analytic i) hδ hδhi
  have hc := original_cost_le i hδhi
  linarith only [h,hc]

/-- Original four rows with their full retained tail. -/
theorem rows_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    matrix.mulVec (actualVector δ) + (fun i => source (parameters i) δ) +
      literalTail δ ≤ actualVector δ := by
  intro i
  have hr := matrix_rows_with_tail hδ hδhi i
  have hs := source_le_original i hδhi
  change matrix.mulVec (actualVector δ) i + source (parameters i) δ +
    literalTail δ i ≤ actualVector δ i
  change matrix.mulVec (actualVector δ) i + SecondFunctionalPositive.source (parameters i) δ +
    literalTail δ i ≤ actualVector δ i at hr
  linarith only [hr,hs]

/-- Actual nonnegative Q and original H vector, retaining the original tail. -/
theorem actual_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec ((fun i => source (parameters i) δ) + literalTail δ) ≤ actualVector δ := by
  apply solve_actual_rows
  simpa only [add_assoc] using rows_with_tail hδ hδhi

/-- Tail removal uses its proved nonnegativity and the actual Q monotonicity producer. -/
theorem actual_without_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (fun i => source (parameters i) δ) ≤ actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (actual_with_tail hδ hδhi)

end Wu2008DoubleSieve.Omega3ElementaryFeedback

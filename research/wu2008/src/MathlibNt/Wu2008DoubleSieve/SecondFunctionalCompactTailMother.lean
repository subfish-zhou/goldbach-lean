import MathlibNt.Wu2008DoubleSieve.SecondFunctionalEulerTail
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveMatrix

/-! The effective compact-tail upper bound enters the original mother and actual feedback. -/
namespace Wu2008DoubleSieve.SecondFunctionalCompactTail
open Real MotherPair FourthRowPhiOmega2 SecondFunctionalJointTail
open scoped Classical

noncomputable def kernelUpper (p : SecondFunctionalParameters) (m : ℕ) (P : ℝ) : ℝ :=
  max (compactSup p P) (exp (-eulerMascheroniConstant) * M p + 4 * M p / (m.factorial : ℝ))

noncomputable def cost (p : SecondFunctionalParameters) (δ : ℝ) (m : ℕ) (P : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
    SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + kernelUpper p m P)

theorem original_cost_le (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) (hm : 3 ≤ m) {P : ℝ} (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P)
    {δ : ℝ} (hδhi : δ ≤ 1/10) :
    SecondFunctionalCoupledFeedback.cost p δ ≤ cost p δ m P := by
  have h := (compact_euler_tail_sandwich p hp.mother hp.two_lt_s.le m hm hP).2
  have hc : 0 ≤ 2/(1-2*δ) := div_nonneg (by norm_num) (by linarith)
  have hpay := mul_le_mul_of_nonneg_left h hc
  unfold SecondFunctionalCoupledFeedback.cost cost kernelUpper
  nlinarith only [hpay]

/-- All parameters and the compact cutoff precede the common original-count threshold. -/
theorem mother (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) (hm : 3 ≤ m) {P : ℝ} (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (cost p δ m P - SecondFunctionalCoupledFeedback.gain p δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, ht⟩ := SecondFunctionalCoupledFeedback.mother p hp k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  apply (ht N hN he i Δ V hb).trans
  apply mul_le_mul_of_nonneg_right
  · linarith only [original_cost_le p hp m hm hP hδhi]
  · exact gamma5Mass_theta_nonneg (by omega) hδ (by linarith) hb

/-- Actual H feedback now uses a compact supremum and an explicit factorial tail budget. -/
theorem actual_limit (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) (hm : 3 ≤ m) {P : ℝ} (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient p.s + (SecondFunctionalCoupledFeedback.gain p δ - cost p δ m P)/5 ≤
      wuImprovementLimit true δ p.s := by
  have h := SecondFunctionalCoupledFeedback.actual_limit p hp hδ hδhi
  have hc := original_cost_le p hp m hm hP hδhi
  linarith only [h, hc]

/-- The exact point gains and three J terms remain in the matrix source. -/
noncomputable def source (p : SecondFunctionalParameters) (δ : ℝ) (m : ℕ) (P : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S - cost p δ m P)/5

theorem source_le_original (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) (hm : 3 ≤ m) {P : ℝ} (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P)
    {δ : ℝ} (hδhi : δ ≤ 1/10) : source p δ m P ≤ SecondFunctionalPositive.source p δ := by
  have hc := original_cost_le p hp m hm hP hδhi
  unfold source SecondFunctionalPositive.source
  linarith only [hc]

/-- No entrywise numerical values, inverse, or positive remainder are postulated. -/
theorem matrix_rows_with_tail (m : Fin 4 → ℕ) (hm : ∀ i, 3 ≤ m i)
    (P : Fin 4 → ℝ) (hP : ∀ i, max 2 (((m i : ℝ) + 6) / 2) ≤ P i)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    SecondFunctionalPositive.matrix.mulVec (SecondFunctionalPositive.actualVector δ) +
      (fun i => source (SecondFunctionalPositive.parameters i) δ (m i) (P i)) +
      SecondFunctionalPositive.literalTail δ ≤ SecondFunctionalPositive.actualVector δ := by
  intro i
  have hr := SecondFunctionalPositive.matrix_rows_with_tail hδ hδhi i
  have hs := source_le_original (SecondFunctionalPositive.parameters i)
    (SecondFunctionalPositive.parameters_analytic i) (m i) (hm i) (hP i) hδhi
  change SecondFunctionalPositive.matrix.mulVec (SecondFunctionalPositive.actualVector δ) i +
    source (SecondFunctionalPositive.parameters i) δ (m i) (P i) +
      SecondFunctionalPositive.literalTail δ i ≤ SecondFunctionalPositive.actualVector δ i
  change SecondFunctionalPositive.matrix.mulVec (SecondFunctionalPositive.actualVector δ) i +
    SecondFunctionalPositive.source (SecondFunctionalPositive.parameters i) δ +
      SecondFunctionalPositive.literalTail δ i ≤ SecondFunctionalPositive.actualVector δ i at hr
  linarith only [hr, hs]

end Wu2008DoubleSieve.SecondFunctionalCompactTail

import MathlibNt.Wu2008DoubleSieve.FourthRowGamma5LinkFinite
import MathlibNt.Wu2008DoubleSieve.Gamma5SeedRational

/-! # The actual fivefold mother with the accepted Gamma5 gain

This isolated join does not modify either production branch. All other
mother addends remain literal; the integral and seed are alternative exits.
-/
namespace Wu2008DoubleSieve
open scoped Interval

/-- The original mother RHS with precisely Gamma5 omitted, not subtracted. -/
noncomputable def fourthRowGamma5LinkRHSwithoutGamma5 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherGamma6 N δ W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1] +
    wuOmega3Sum N δ (5 / 2) (89 / 25) W +
    fourthRowMotherPrefixSum N δ W [1, 1, 2] +
    fourthRowMotherPrefixSum N δ W [1, 2, 2] +
    fourthRowMotherPrefixSum N δ W [0, 1, 2] +
    fourthRowMotherPrefixSum N δ W [0, 2, 2] +
    gamma16PrefixSum N δ W

/-- Literal splitting of the old mother, before any analytic estimate. -/
theorem fourthRowGamma5Link_RHS_split {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    fourthRowMotherRHS N δ W = fourthRowGamma5LinkRHSwithoutGamma5 N δ W +
      fourthRowMotherGamma5 N δ W := by
  unfold fourthRowMotherRHS fourthRowGamma5LinkRHSwithoutGamma5
  ring

/-- The stronger actual-H legal-kernel exit, with a common old-box threshold. -/
theorem fourthRowGamma5Link_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 -
              (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) +
              ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) := by
  have hh : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 2 := by linarith
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowMother_source k hδ hh heps
  obtain ⟨Tg, _, hg⟩ := gamma5Feedback_full_count_upper k hk hδ hδhi heps
  refine ⟨max Tm Tg, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := (le_max_left Tm Tg).trans hN
  have hgN := (le_max_right Tm Tg).trans hN
  have hmother := hm N hmN he i Δ V hb
  have hgamma := hg N hgN he i Δ V hb
  rw [fourthRowGamma5Link_RHS_split,
    fourthRowGamma5Link_count_eq (hTm4.trans hmN) he] at hmother
  calc
    _ ≤ (fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
        gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
          (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V))) +
        (ε / 2) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ V) := hmother
    _ ≤ (fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
        (gamma5MassC5 -
          (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) +
          ε / 2) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
            (convolutionWuWindows N Δ V)) +
        (ε / 2) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ V) := add_le_add (add_le_add le_rfl hgamma) le_rfl
    _ = _ := by ring

/-- The rational seed is an alternative gain, never an additional subtraction. -/
theorem fourthRowGamma5Link_seed_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - 147 / 6630625 + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hh : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 2 := by linarith
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowMother_source k hδ hh heps
  obtain ⟨Tg, _, hg⟩ := gamma5Gain_full_count_upper_seed_rational k hk hδ hδhi heps
  refine ⟨max Tm Tg, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := (le_max_left Tm Tg).trans hN
  have hgN := (le_max_right Tm Tg).trans hN
  have hmother := hm N hmN he i Δ V hb
  have hgamma := hg N hgN he i Δ V hb
  rw [fourthRowGamma5Link_RHS_split,
    fourthRowGamma5Link_count_eq (hTm4.trans hmN) he] at hmother
  calc
    _ ≤ (fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
        gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
          (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V))) +
        (ε / 2) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ V) := hmother
    _ ≤ (fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
        (gamma5MassC5 - 147 / 6630625 + ε / 2) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) +
        (ε / 2) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ V) := add_le_add (add_le_add le_rfl hgamma) le_rfl
    _ = _ := by ring

end Wu2008DoubleSieve

import MathlibNt.Wu2008DoubleSieve.FourthRowJoinedGamma6
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedUpper

/-! Actual closed-gate Gamma10/Gamma13 consumption in the same mother. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoinedGatedRHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1]

theorem fourthRowJoinedGated_split {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowJoinedGamma6RHS N δ W = fourthRowJoinedGatedRHS N δ W +
      (fourthRowMotherPrefixSum N δ W [1, 1, 2] + fourthRowMotherPrefixSum N δ W [0, 1, 2]) := by
  unfold fourthRowJoinedGamma6RHS fourthRowJoinedGatedRHS
  ring

/-- A common threshold retains both full gains and all six literal envelopes. -/
theorem fourthRowJoinedGated_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedGatedRHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 + gamma6BaseC6 - (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) - gamma6GainIntegral δ +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false +
                fourthRowTripleGatedEnvelope true + fourthRowTripleGatedEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedGamma6_full_integral_upper k hk hδ hδhi hε2
  obtain ⟨Tg, _, hg⟩ := fourthRowTripleGated_joint_upper k hδ hδhalf hε2
  refine ⟨max Tm Tg, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm Tg).trans hN) he i Δ V hb
  have hgN := hg N ((le_max_right Tm Tg).trans hN) he i Δ V hb
  rw [fourthRowJoinedGated_split] at hmN
  nlinarith only [hmN, hgN]

/-- A common threshold retains both full gains and all six literal envelopes. -/
theorem fourthRowJoinedGated_seed_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedGatedRHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 + gamma6BaseC6 - 147 / 6630625 - gamma6GainIntegral δ +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false +
                fourthRowTripleGatedEnvelope true + fourthRowTripleGatedEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedGamma6_seed_upper k hk hδ hδhi hε2
  obtain ⟨Tg, _, hg⟩ := fourthRowTripleGated_joint_upper k hδ hδhalf hε2
  refine ⟨max Tm Tg, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm Tg).trans hN) he i Δ V hb
  have hgN := hg N ((le_max_right Tm Tg).trans hN) he i Δ V hb
  rw [fourthRowJoinedGated_split] at hmN
  nlinarith only [hmN, hgN]

end Wu2008DoubleSieve

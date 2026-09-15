import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackCountLink
import MathlibNt.Wu2008DoubleSieve.FourthRowGamma78LinkFinite

/-! All positive Gamma counts have been consumed in the original prefix mother.
The original Phi/Omega2 block remains literal. Delta losses are retained. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoinedAllGammaRHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W

theorem fourthRowJoinedAllGamma_split {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    fourthRowJoinedGatedRHS N δ W = fourthRowJoinedAllGammaRHS N δ W +
      fourthRowMotherPrefixSum N δ W [0, 0] +
      fourthRowMotherPrefixSum N δ W [0, 1] := rfl

/-- Full legal Gamma5 gain and complete K6+K7+K8, with one total epsilon. -/
theorem fourthRowJoinedAllGamma_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedAllGammaRHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 + gamma6BaseC6 + gamma78GainC true + gamma78GainC false -
              (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) -
              (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v *
                (Gamma678Feedback.K6 v + Gamma678Feedback.K7 v + Gamma678Feedback.K8 v)) +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false +
                fourthRowTripleGatedEnvelope true + fourthRowTripleGatedEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedGated_full_integral_upper k hk hδ hδhi hε2
  obtain ⟨Tg, _, hg⟩ := gamma78Gain_joint_full_count_upper k hk hδ hδhi hε2
  refine ⟨max Tm Tg, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hN4 := hTm4.trans ((le_max_left Tm Tg).trans hN)
  have hmN := hm N ((le_max_left Tm Tg).trans hN) he i Δ V hb
  have hgN := hg N ((le_max_right Tm Tg).trans hN) he i Δ V hb
  rw [fourthRowJoinedAllGamma_split, fourthRowGamma78Link_gamma7_eq hN4 he,
    fourthRowGamma78Link_gamma8_eq hN4 he] at hmN
  rw [← gamma678FeedbackCount_gain_sum hδ hδhalf]
  nlinarith only [hmN, hgN]

end Wu2008DoubleSieve

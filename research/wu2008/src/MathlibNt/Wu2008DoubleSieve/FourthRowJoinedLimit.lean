import MathlibNt.Wu2008DoubleSieve.FourthRowJoinedAllGamma
import MathlibNt.Wu2008DoubleSieve.FourthRowPhiOmega2Block

/-! The original fourth-row mother now has no residual count terms.
The coefficient retains the actual H/h, complete gains and fixed-delta losses.
Its final statement is a feedback inequality, not a numerical lower bound. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoinedLimitCoefficient (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient (103 / 25) + wuUpperCoefficient (89 / 25) -
    4 * wuImprovementLimit true δ (103 / 25) -
    wuImprovementLimit true δ (89 / 25) -
    2 * FourthRowPhiOmega2.J δ (5 / 2) (103 / 25) -
    FourthRowPhiOmega2.J δ (291 / 100) (103 / 25) +
    gamma5MassC5 + gamma6BaseC6 + gamma78GainC true + gamma78GainC false -
    (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) -
    (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v *
      (Gamma678Feedback.K6 v + Gamma678Feedback.K7 v + Gamma678Feedback.K8 v)) +
    2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
      fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false +
      fourthRowTripleGatedEnvelope true + fourthRowTripleGatedEnvelope false)

/-- The actual Phi estimate, uniform over every old box at each fixed depth. -/
theorem fourthRowJoinedLimit_actual_phi_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          (fourthRowJoinedLimitCoefficient δ + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedAllGamma_full_integral_upper k hk hδ hδhi hε2
  obtain ⟨Tq, _, hq⟩ := FourthRowPhiOmega2.actual_limit_block k hk hδ hδhi hε2
  refine ⟨max Tm Tq, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm Tq).trans hN) he i Δ V hb
  have hqN := hq N ((le_max_right Tm Tq).trans hN) he i Δ V hb
  unfold fourthRowJoinedAllGammaRHS at hmN
  unfold fourthRowJoinedLimitCoefficient
  nlinarith only [hmN, hqN]

/-- The original actual H limit satisfies the fixed-delta fourth-row feedback.
The same coefficient works for all positive depths; no limiting regularity
in delta, numerical inversion, or caller-supplied count bound is assumed. -/
theorem fourthRowJoinedLimit_actual_H_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    wuUpperCoefficient (5 / 2) - fourthRowJoinedLimitCoefficient δ / 5 ≤
      wuImprovementLimit true δ (5 / 2) := by
  have hδhalf : δ < 1 / 2 := by linarith
  change _ ≤ ⨅ k : ℕ, wuImprovementAtInfinity true (k + 1) δ (5 / 2)
  apply le_ciInf
  intro k
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T, _, hT⟩ := fourthRowJoinedLimit_actual_phi_upper (k + 1) (by omega)
    hδ hδhi (show 0 < 5 * ε by positivity)
  have hmem : wuUpperCoefficient (5 / 2) - fourthRowJoinedLimitCoefficient δ / 5 - ε ∈
      wuEventualImprovements true (k + 1) δ (5 / 2) := by
    refine ⟨T, ?_⟩
    intro N hN _ he i Δ V hb
    have hc := hT N hN he i Δ V hb
    change wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
      (wuUpperCoefficient (5 / 2) -
        (wuUpperCoefficient (5 / 2) - fourthRowJoinedLimitCoefficient δ / 5 - ε)) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    nlinarith only [hc]
  have hs := le_csSup (wuEventualImprovements_bddAbove true (k + 1) hδ hδhalf
    (show (1 : ℝ) ≤ 5 / 2 by norm_num) (by norm_num)) hmem
  change wuUpperCoefficient (5 / 2) - fourthRowJoinedLimitCoefficient δ / 5 - ε ≤
    wuImprovementAtInfinity true (k + 1) δ (5 / 2) at hs
  linarith

end Wu2008DoubleSieve

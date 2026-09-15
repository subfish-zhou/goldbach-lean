import MathlibNt.Wu2008DoubleSieve.FourthRowGamma5LinkMain
import MathlibNt.Wu2008DoubleSieve.FourthRowGamma9Upper
import MathlibNt.Wu2008DoubleSieve.Gamma16FourthRow

/-! Actual fourth-row consumption of the accepted Gamma5, Gamma9 and Gamma16 bounds.
All unestimated counts remain literal. The integral and rational-seed exits are alternatives. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoined5916RHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherGamma6 N δ W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1] +
    fourthRowMotherPrefixSum N δ W [1, 1, 2] +
    fourthRowMotherPrefixSum N δ W [1, 2, 2] +
    fourthRowMotherPrefixSum N δ W [0, 1, 2] +
    fourthRowMotherPrefixSum N δ W [0, 2, 2]

theorem fourthRowJoined5916_split {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    fourthRowGamma5LinkRHSwithoutGamma5 N δ W =
      fourthRowJoined5916RHS N δ W + wuOmega3Sum N δ (5 / 2) (89 / 25) W +
        gamma16PrefixSum N δ W := by
  unfold fourthRowGamma5LinkRHSwithoutGamma5 fourthRowJoined5916RHS
  ring

/-- Three actual producers, each with one third of the final error budget. -/
theorem fourthRowJoined5916_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoined5916RHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowGamma5Link_full_integral_upper k hk hδ hδhi hε3
  obtain ⟨T9, _, h9⟩ := fourthRowGamma9_actual_upper k hδ hδhalf hε3
  obtain ⟨T16, _, h16⟩ := gamma16_fourth_row_prefix_upper k hδ hδhalf hε3
  refine ⟨max Tm (max T9 T16), hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm (max T9 T16)).trans hN) he i Δ V hb
  have h9N := h9 N ((le_max_left T9 T16).trans
    ((le_max_right Tm (max T9 T16)).trans hN)) he i Δ V hb
  have h16N := h16 N ((le_max_right T9 T16).trans
    ((le_max_right Tm (max T9 T16)).trans hN)) he i Δ V hb
  rw [fourthRowJoined5916_split] at hmN
  nlinarith only [hmN, h9N, h16N]

/-- Three actual producers, each with one third of the final error budget. -/
theorem fourthRowJoined5916_seed_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoined5916RHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - 147 / 6630625 +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowGamma5Link_seed_upper k hk hδ hδhi hε3
  obtain ⟨T9, _, h9⟩ := fourthRowGamma9_actual_upper k hδ hδhalf hε3
  obtain ⟨T16, _, h16⟩ := gamma16_fourth_row_prefix_upper k hδ hδhalf hε3
  refine ⟨max Tm (max T9 T16), hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm (max T9 T16)).trans hN) he i Δ V hb
  have h9N := h9 N ((le_max_left T9 T16).trans
    ((le_max_right Tm (max T9 T16)).trans hN)) he i Δ V hb
  have h16N := h16 N ((le_max_right T9 T16).trans
    ((le_max_right Tm (max T9 T16)).trans hN)) he i Δ V hb
  rw [fourthRowJoined5916_split] at hmN
  nlinarith only [hmN, h9N, h16N]

end Wu2008DoubleSieve

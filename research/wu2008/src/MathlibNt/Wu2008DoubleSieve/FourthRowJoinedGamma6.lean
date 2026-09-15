import MathlibNt.Wu2008DoubleSieve.FourthRowGamma6LinkFinite
import MathlibNt.Wu2008DoubleSieve.FourthRowJoinedNoGate
import MathlibNt.Wu2008DoubleSieve.Gamma6GainMain

/-! The actual mother now consumes the complete Gamma6 H gain as well.
No source/count is redefined and no gain is replaced by a rational seed. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoinedGamma6RHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1] +
    fourthRowMotherPrefixSum N δ W [1, 1, 2] +
    fourthRowMotherPrefixSum N δ W [0, 1, 2]

theorem fourthRowJoinedGamma6_split {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    fourthRowJoinedNoGateRHS N δ W = fourthRowJoinedGamma6RHS N δ W +
      fourthRowMotherGamma6 N δ W := by
  unfold fourthRowJoinedNoGateRHS fourthRowJoinedGamma6RHS
  ring

/-- The full accepted gain bounds the original mother count, not merely a parallel label count. -/
theorem fourthRowJoinedGamma6_actual_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherGamma6 N δ (convolutionWuWindows N Δ V) ≤
          (gamma6BaseC6 - gamma6GainIntegral δ + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, h⟩ := gamma6Gain_full_count_upper k hk hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb
  rw [fourthRowGamma6Link_count_eq (hT4.trans hN) he]
  exact h N hN he i Δ V hb

/-- The old joined mother and the full actual Gamma6 estimate share the total error. -/
theorem fourthRowJoinedGamma6_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedGamma6RHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 + gamma6BaseC6 - (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) - gamma6GainIntegral δ +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedNoGate_full_integral_upper k hk hδ hδhi hε2
  obtain ⟨T6, _, h6⟩ := fourthRowJoinedGamma6_actual_upper k hk hδ hδhi hε2
  refine ⟨max Tm T6, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm T6).trans hN) he i Δ V hb
  have h6N := h6 N ((le_max_right Tm T6).trans hN) he i Δ V hb
  rw [fourthRowJoinedGamma6_split] at hmN
  nlinarith only [hmN, h6N]

/-- The old joined mother and the full actual Gamma6 estimate share the total error. -/
theorem fourthRowJoinedGamma6_seed_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedGamma6RHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 + gamma6BaseC6 - 147 / 6630625 - gamma6GainIntegral δ +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoinedNoGate_seed_upper k hk hδ hδhi hε2
  obtain ⟨T6, _, h6⟩ := fourthRowJoinedGamma6_actual_upper k hk hδ hδhi hε2
  refine ⟨max Tm T6, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm T6).trans hN) he i Δ V hb
  have h6N := h6 N ((le_max_right Tm T6).trans hN) he i Δ V hb
  rw [fourthRowJoinedGamma6_split] at hmN
  nlinarith only [hmN, h6N]

end Wu2008DoubleSieve

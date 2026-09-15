import MathlibNt.Wu2008DoubleSieve.FourthRowJoined5916
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateUpper

/-! Actual mother consumption of Gamma5, Gamma9, Gamma11, Gamma14 and Gamma16.
The five remaining positive counts stay literal; seed and full-integral exits are alternatives. -/
namespace Wu2008DoubleSieve
open scoped Interval

noncomputable def fourthRowJoinedNoGateRHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherGamma6 N δ W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1] +
    fourthRowMotherPrefixSum N δ W [1, 1, 2] +
    fourthRowMotherPrefixSum N δ W [0, 1, 2]

theorem fourthRowJoinedNoGate_split {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    fourthRowJoined5916RHS N δ W = fourthRowJoinedNoGateRHS N δ W +
      fourthRowMotherPrefixSum N δ W [1, 2, 2] +
      fourthRowMotherPrefixSum N δ W [0, 2, 2] := by
  unfold fourthRowJoined5916RHS fourthRowJoinedNoGateRHS
  ring

/-- The accepted joined mother and the actual no-gate joint producer share one error budget. -/
theorem fourthRowJoinedNoGate_full_integral_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedNoGateRHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoined5916_full_integral_upper k hk hδ hδhi hε2
  obtain ⟨Tn, _, hn⟩ := fourthRowTripleNoGate_joint_upper k hδ hδhalf hε2
  refine ⟨max Tm Tn, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm Tn).trans hN) he i Δ V hb
  have hnN := hn N ((le_max_right Tm Tn).trans hN) he i Δ V hb
  rw [fourthRowJoinedNoGate_split] at hmN
  nlinarith only [hmN, hnN]

/-- The accepted joined mother and the actual no-gate joint producer share one error budget. -/
theorem fourthRowJoinedNoGate_seed_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowJoinedNoGateRHS N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - 147 / 6630625 +
              2 / (1 - 2 * δ) * (fourthRowGamma9I + gamma16FourthIntegralEnvelope +
                fourthRowTripleNoGateEnvelope true + fourthRowTripleNoGateEnvelope false) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Tm, hTm4, hm⟩ := fourthRowJoined5916_seed_upper k hk hδ hδhi hε2
  obtain ⟨Tn, _, hn⟩ := fourthRowTripleNoGate_joint_upper k hδ hδhalf hε2
  refine ⟨max Tm Tn, hTm4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hmN := hm N ((le_max_left Tm Tn).trans hN) he i Δ V hb
  have hnN := hn N ((le_max_right Tm Tn).trans hN) he i Δ V hb
  rw [fourthRowJoinedNoGate_split] at hmN
  nlinarith only [hmN, hnN]

end Wu2008DoubleSieve

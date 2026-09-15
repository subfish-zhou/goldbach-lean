import MathlibNt.Wu2008DoubleSieve.Omega1Upper
import MathlibNt.Wu2008DoubleSieve.OmegaRepeated
import MathlibNt.Wu2008DoubleSieve.Omega2Lower

/-!
# The first actual weighted upper comparison

The finite error and the same-N0 Omega1 estimate are produced internally.
Both remaining signed terms are literal source count aggregates.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem wu_omega_first_stage_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        2 * wuBoxPhi N δ W s ≤
          2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W -
            wuOmega2Sum N δ s t W + wuOmega3Sum N δ s t W +
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨T1, hT14, hT1⟩ := wu04_51 k hk hδ (show δ < 1 / 2 by linarith)
  obtain ⟨T2, hT2⟩ := wu_omega_weighted_source k hδ hδhi hε
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he i Δ V hb
    t (by linarith) ht
  have h2 := hT2 N0 ((le_max_right _ _).trans hN0) N hN he i Δ V hb s t hs hst ht
  dsimp only at h2 ⊢
  linarith

/-- Both analytic consumers are proved internally. The only unevaluated
source term is the literal positive Omega3 aggregate. -/
theorem wu_omega12_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
        let W := convolutionWuWindows N Δ V
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (wuLowerCoefficient (t * u) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W +
          wuOmega3Sum N δ s t W := by
  obtain ⟨T1, hT14, hT1⟩ := wu_omega_first_stage_upper k hk hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := wu04_52 k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht ht5
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he i Δ V hb
    s t hs hst (by linarith)
  have h2 := hT2 N0 ((le_max_right _ _).trans hN0) N hN he i Δ V hb
    s t hs hst ht ht5
  dsimp only at h1 ⊢
  nlinarith

/-- Wu04 Lemma 5.1 after (5.1) and (5.2), before the switching bound.
The source ratio restriction justifies the displayed logarithmic branch. -/
theorem wu04_first_weighted_omega12 (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ 3 → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
        let W := convolutionWuWindows N Δ V
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W +
          wuOmega3Sum N δ s t W := by
  obtain ⟨T, hT4, hT⟩ := wu_omega12_upper k hk hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h := hT N0 hN0 N hN he i Δ V hb s t hs (by linarith) ht ht5
  have heq := omega2_effective_lower_integral_eq_log k N0 δ hs
    (show s ≤ t by linarith) ht5 hratio
  simp only [wuEffectiveCoefficient, Bool.false_eq_true, if_false] at heq
  dsimp only at h ⊢
  rw [heq] at h
  exact h

end Wu2008DoubleSieve

import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedSieveCombined
import MathlibNt.Wu2008DoubleSieve.Omega3R1Source

/-!
# Actual switched upper bounds with both remainders paid

The accepted balanced distribution is applied to the literal R1. The
actual prime mass X and the fixed-delta density factor remain unchanged.
This is not the rough-number mass estimate (5.9) or a positive sieve gain.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem omega3_switched_upper_remainders_paid (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SwitchedSiftedCount N δ s t (sqrt Q) W ≤
          omega3SieveX N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
            ε * boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ :=
    omega3_switched_upper_R2_paid k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3_sieve_R1_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) he i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  linarith

/-- Same N0 in both improvements, with the actual R1 now removed.
Only the actual raw X remains to be estimated analytically. -/
theorem wu04_first_weighted_switched_distribution (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ 3 → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) + ε) * boxTheta N Q W +
          omega3SieveX N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) := by
  obtain ⟨T1, hT14, hT1⟩ :=
    wu04_first_weighted_switched_sieve k hk hδ hδhi hρ (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3_sieve_R1_relative k hδ
    (show δ < 1 / 2 by linarith) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N (((le_max_right _ _).trans hN0).trans hN)
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 h2 ⊢
  nlinarith

end Wu2008DoubleSieve

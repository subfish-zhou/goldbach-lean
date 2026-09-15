import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedCombined
import MathlibNt.Wu2008DoubleSieve.Omega3SieveSource
import MathlibNt.Wu2008DoubleSieve.Omega3R2Source

/-!
# The physical finite switched sieve in the first weighted comparison

Only R2 is paid by the original Theta. The canonical density errors still
multiply the actual X, and the actual whole-cofactor R1 remains on the
right-hand side. Neither missing analytic producer is a hypothesis.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem omega3_switched_upper_R2_paid (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        let Z := sqrt Q
        omega3SwitchedSiftedCount N δ s t Z W ≤
          omega3SieveX N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
            omega3SieveR1 N (⌊Q⌋₊ + 1) δ s t Z W + ε * boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ := omega3_switched_upper_source_density hδ hδhi hρ
  obtain ⟨T2, _, hT2⟩ := omega3_sieve_R2_relative k hδ hδhi hε
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hd : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 < d := by
    intro d hd
    exact (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  have henlarge := omega3_switched_sifted_le_closed N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
    (convolutionWuWindows N Δ V) hd
  have hfinite := hT1 N hN1 he i s t (convolutionWuWindows N Δ V)
  have hR2 := hT2 N hN2 i Δ V hb s t hs hst ht
  dsimp only at hfinite hR2 ⊢
  linarith

/-- One common N0 is retained in both improvement envelopes. This is a
finite upper-sieve substitution, not the completed switched asymptotic. -/
theorem wu04_first_weighted_switched_sieve (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ 3 → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        let Z := sqrt Q
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) + ε) * boxTheta N Q W +
          omega3SieveX N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
          omega3SieveR1 N (⌊Q⌋₊ + 1) δ s t Z W := by
  obtain ⟨T1, hT14, hT1⟩ := wu04_first_weighted_switched k hk hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3_switched_upper_R2_paid k hδ
    (show δ < 1 / 2 by linarith) hρ (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N (((le_max_right _ _).trans hN0).trans hN) he
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 h2 ⊢
  nlinarith

end Wu2008DoubleSieve

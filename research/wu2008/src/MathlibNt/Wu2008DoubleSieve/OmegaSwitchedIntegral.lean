import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralNormalization
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedBuchstab

/-!
# Physical switched consumers of actual triple-prime quadrature

Wu04, TeX2240--2259, with additive errors and the full fixed-delta
density factor. The same N0 is used in both improvement functions.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem omega3XBuchstabMain_scaled_integral (k : ℕ) {δ K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3XBuchstabMain N δ s t W * (K * wuSingularSeries N / log N) ≤
          omega3XIntegralMain N δ s t W * (K * wuSingularSeries N / log N) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have he : 0 < 2 * ε / K := by positivity
  obtain ⟨T, hT4, hT⟩ := omega3XBuchstabMain_le_integral_paid k hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN4 := hT4.trans hN
  have hC := wuSingularSeries_pos N (by omega : 0 < N)
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hf : 0 ≤ K * wuSingularSeries N / log N := by positivity
  have hraw := mul_le_mul_of_nonneg_right (hT N hN i Δ V hb s t hs hst ht) hf
  have hpaid := omega3X_scaled_error_le hN4 hδ hδhi hb he.le hK.le
  have hcancel : (2 * ε / K) * K / 2 = ε := by field_simp
  rw [hcancel] at hpaid
  dsimp only at hraw ⊢
  rw [add_mul] at hraw
  exact hraw.trans (add_le_add le_rfl hpaid)

theorem omega3_switched_upper_integral (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SwitchedSiftedCount N δ s t (sqrt Q) W ≤
          omega3XIntegralMain N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
            ε * boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ :=
    omega3_switched_upper_buchstab k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3XBuchstabMain_scaled_integral k hδ hδhi
    (omega3X_fixed_density_factor_pos hδhi hρ) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) he i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  linarith

theorem wu04_first_weighted_switched_integral (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
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
          omega3XIntegralMain N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) := by
  obtain ⟨T1, hT14, hT1⟩ :=
    wu04_first_weighted_switched_buchstab k hk hδ hδhi hρ (half_pos hε)
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨T2, _, hT2⟩ := omega3XBuchstabMain_scaled_integral k hδ hδhalf
    (omega3X_fixed_density_factor_pos hδhalf hρ) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N (((le_max_right _ _).trans hN0).trans hN)
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 h2 ⊢
  nlinarith

/-- Fixed delta and arbitrarily small fixed Li slack: not a coefficient 2I. -/
theorem omega3_switched_upper_envelope (k : ℕ) {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SwitchedSiftedCount N δ s t (sqrt Q) W ≤
          ((1 + τ) * ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
            (8 / (1 - 2 * δ))) / 4 * omega3XIntegralEnvelope s t + ε) *
              boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ := omega3_switched_upper_integral k hδ hδhi hρ hε
  obtain ⟨T2, _, hT2⟩ := omega3XIntegralMain_scaled_uniform k hδ hδhi
    (omega3X_fixed_density_factor_pos hδhi hρ).le hτ
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) he i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  nlinarith

theorem wu04_first_weighted_switched_envelope (k : ℕ) (hk : 1 ≤ k) {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ 3 → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) +
            (1 + τ) * ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) / 4 * omega3XIntegralEnvelope s t + ε) *
                boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ :=
    wu04_first_weighted_switched_integral k hk hδ hδhi hρ hε
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨T2, _, hT2⟩ := omega3XIntegralMain_scaled_uniform k hδ hδhalf
    (omega3X_fixed_density_factor_pos hδhalf hρ).le hτ
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N (((le_max_right _ _).trans hN0).trans hN)
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 h2 ⊢
  nlinarith

end Wu2008DoubleSieve

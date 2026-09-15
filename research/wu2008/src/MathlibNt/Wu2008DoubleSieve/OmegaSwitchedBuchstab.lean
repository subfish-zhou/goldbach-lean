import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabSource
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabPayment
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedDistributionCombined

/-!
# Physical switched consumers with the finite Buchstab main sum

Raw X and roughCount have been removed from these bounds. The literal
finite Buchstab sum remains, with the fixed-delta density factor and
the identical N0 in the two first-weight improvements.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem omega3X_buchstab_scaled (k : ℕ) {δ K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3SieveX N δ s t W * (K * wuSingularSeries N / log N) ≤
          omega3XBuchstabMain N δ s t W * (K * wuSingularSeries N / log N) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have he : 0 < 2 * ε / K := by positivity
  obtain ⟨T, hT4, hT⟩ := omega3SieveX_le_buchstab_paid k hδ hδhi he
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

theorem omega3_switched_upper_buchstab (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SwitchedSiftedCount N δ s t (sqrt Q) W ≤
          omega3XBuchstabMain N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
            ε * boxTheta N Q W := by
  obtain ⟨T1, hT14, hT1⟩ :=
    omega3_switched_upper_remainders_paid k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3X_buchstab_scaled k hδ hδhi
    (omega3X_fixed_density_factor_pos hδhi hρ) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) he i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  linarith

/-- Same-threshold first-weight comparison with X replaced by its actual
finite Buchstab main sum. No triple-integral bound is assumed. -/
theorem wu04_first_weighted_switched_buchstab (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
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
          omega3XBuchstabMain N δ s t W *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
              (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) := by
  obtain ⟨T1, hT14, hT1⟩ :=
    wu04_first_weighted_switched_distribution k hk hδ hδhi hρ (half_pos hε)
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨T2, _, hT2⟩ := omega3X_buchstab_scaled k hδ hδhalf
    (omega3X_fixed_density_factor_pos hδhalf hρ) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N (((le_max_right _ _).trans hN0).trans hN)
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 h2 ⊢
  nlinarith

end Wu2008DoubleSieve

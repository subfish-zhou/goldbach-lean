import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedDistribution
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedSwitching
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

/-! # Actual source-scale error payment and gated upper density -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem fourthRowTripleGated_R1_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      fourthRowTripleGatedR1 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleGatedProfiles N δ W ten) ≤
        ε * boxTheta N Q W := by
  obtain ⟨C, hC, T1, hT1, hR⟩ := fourthRowTripleGated_R1_log k hδ hδhi
    (show (0 : ℝ) < (5 * k + 3 : ℕ) by positivity)
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨T3, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb ten W Q
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog := log_pos (by exact_mod_cast (show 1 < N by have := hT1.trans hN1; omega) : (1 : ℝ) < N)
  have hr := hR N hN1 i Δ V hb ten
  dsimp only at hr
  rw [rpow_natCast] at hr
  have htheta := hTheta N hN2 i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.2.1 hb.2.2.2.2.2
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hlogT N hN3)
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (5 * k + 3) := hr
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) := by
      rw [show 5 * k + 3 = (5 * k + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

theorem fourthRowTripleGated_upper_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowMotherPrefixSum N δ W (fourthRowTripleGatedWord ten) ≤
        fourthRowTripleGatedX N δ W (fourthRowTripleGatedProfiles N δ W ten) *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
            (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT0, hs⟩ := fourthRowTripleGated_switching_paid k hδ hδhi hε3
  obtain ⟨T1, _, hR1⟩ := fourthRowTripleGated_R1_relative k hδ hδhi hε3
  obtain ⟨T2, _, hR2⟩ := fourthRowTripleGated_R2_relative k hδ hδhi hε3
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 (max T2 T3)), hT0.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb ten W
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 _).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN4 := hT0.trans hN0
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  have hD : 1 < ⌊Q⌋₊ + 1 := hg.2.2.2.2.1
  have hZ : sqrt Q ≤ (⌊Q⌋₊ + 1 : ℕ) := hg.2.2.2.2.2.1
  have hf := fourthRowTripleGated_upper_finite he δ (sqrt Q) W
    (fourthRowTripleGatedProfiles N δ W ten) hD hZ
  have hx : 0 ≤ fourthRowTripleGatedX N δ W (fourthRowTripleGatedProfiles N δ W ten) :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left (hden N hN3 he) hx
  have hsw := hs N hN0 he i Δ V hb ten
  have hr1 := hR1 N hN1 i Δ V hb ten
  have hr2 := hR2 N hN2 i Δ V hb ten
  dsimp only at hr1 hr2 hsw
  dsimp only [Q, W] at hf hmain ⊢
  linarith

end Wu2008DoubleSieve

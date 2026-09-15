import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateSwitching
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateDistribution
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

/-! # The physical no-gate upper sieve, with all additive errors paid -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem fourthRowTripleNoGate_upper_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowMotherPrefixSum N δ W (fourthRowTripleNoGateWord eleven) ≤
        fourthRowTripleNoGateX N δ W eleven *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
            (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT0, hs⟩ := fourthRowTripleNoGate_switching_paid k hδ hδhi hε3
  obtain ⟨T1, _, hR1⟩ := fourthRowTripleNoGate_R1_relative k hδ hδhi hε3
  obtain ⟨T2, _, hR2⟩ := fourthRowTripleNoGate_R2_relative k hδ hδhi hε3
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 (max T2 T3)), hT0.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb eleven W
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 _).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN4 := hT0.trans hN0
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  have hD : 1 < ⌊Q⌋₊ + 1 := hg.2.2.2.2.1
  have hZ : sqrt Q ≤ (⌊Q⌋₊ + 1 : ℕ) := hg.2.2.2.2.2.1
  have hf := gamma16_family_upper_finite he δ (sqrt Q) W
    (fourthRowTripleNoGateProfiles N δ W eleven) hD hZ
  change fourthRowTripleNoGateS N δ (sqrt Q) W eleven ≤
    fourthRowTripleNoGateX N δ W eleven * _ + _ + _ at hf
  have hx : 0 ≤ fourthRowTripleNoGateX N δ W eleven :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left (hden N hN3 he) hx
  have hsw := hs N hN0 he i Δ V hb eleven
  have hr1 := hR1 N hN1 i Δ V hb eleven
  have hr2 := hR2 N hN2 i Δ V hb eleven
  dsimp only at hr1 hr2
  dsimp only [Q, W] at hf hmain hsw ⊢
  linarith

end Wu2008DoubleSieve

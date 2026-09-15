import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

/-!
# The actual switched finite sieve at Wu's true source level

The source density producer is consumed with fixed delta, retaining
8/(1-2 delta). Its error multiplies the actual X; neither X nor R1 is
analytically estimated here.
-/

namespace Wu2008DoubleSieve

open Finset Real

theorem omega3_switched_upper_source_finite {i N : ℕ} {δ : ℝ}
    (he : Even N) (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (s t : ℝ) (W : Fin i → Finset ℕ) :
    let Q := (N : ℝ) ^ (1 / 2 - δ)
    let Z := sqrt Q
    let D := ⌊Q⌋₊ + 1
    omega3SwitchedSiftedCountLE N δ s t Z W ≤
      omega3SieveX N δ s t W * ordinaryRosserMainSum true N 1 D Z +
        omega3SieveR1 N D δ s t Z W + omega3SieveR2 N D δ s t Z W := by
  have hg := omega3_source_sieve_geometry hN hδ hδhi
  exact omega3_switched_upper_finite he δ s t _ W hg.2.2.2.2.1 hg.2.2.2.2.2.1

/-- Uniform threshold before every box and both source parameters. The
fixed-delta normalization is literal; no universal coefficient eight. -/
theorem omega3_switched_upper_source_density {δ ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (s t : ℝ) (W : Fin i → Finset ℕ),
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      let Z := sqrt Q
      let D := ⌊Q⌋₊ + 1
      omega3SwitchedSiftedCountLE N δ s t Z W ≤
        omega3SieveX N δ s t W *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
            (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
          omega3SieveR1 N D δ s t Z W + omega3SieveR2 N D δ s t Z W := by
  obtain ⟨T, hT, hdensity⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨T, hT, ?_⟩
  intro N hN he i s t W
  have hfinite := omega3_switched_upper_source_finite he (by omega) hδ hδhi s t W
  have hmain := mul_le_mul_of_nonneg_left (hdensity N hN he)
    (omega3SieveX_nonneg N δ s t W)
  dsimp only at hfinite ⊢
  linarith

end Wu2008DoubleSieve

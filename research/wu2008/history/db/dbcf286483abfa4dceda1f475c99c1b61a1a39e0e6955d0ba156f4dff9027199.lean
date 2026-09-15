import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveFinite
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

/-!
# Fixed-delta density and the existing ninth R1 estimate

The true source-level coefficient multiplies the actual X9. The existing
balanced AP estimate pays only R1. R2 and the labelled small-output budget
remain explicitly present; no estimate of X9 or main integral is asserted.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open MathlibNt.SieveTheory.SingularSeries

/-- The existing profile distribution bounds this physical sieve's actual
R1, uniformly in the cutoff Z as well as N. -/
theorem ninthSieveR1_source_bound (A : ℝ) {δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        C * N / log (N : ℝ) ^ A := by
  simpa only [ninthSieveR1, ninthSieveAPResidual] using
    ninth_product_profile_balanced_distribution A hA hδ

/-- Literal fixed-delta density: the relative density error still
multiplies X9, and is not absorbed into an unrelated normalized error. -/
theorem T9_upper_source_density {δ ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
          (8 / (1 - 2 * δ))) * wuSingularSeries N / log (N : ℝ)) * X9 N +
        ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by
  obtain ⟨T, _, hT⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN he
  have hN512 : 512 ≤ N := (le_max_right _ _).trans hN
  have hgeom := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hfinite := T9_upper_finite hN512 he (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
    hgeom.2.2.2.2.1 hgeom.2.2.2.2.2.1
  have hdensity := mul_le_mul_of_nonneg_left
    (hT N ((le_max_left _ _).trans hN) he) (X9_nonneg N)
  calc
    _ ≤ X9 N * ((((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
          (8 / (1 - 2 * δ))) * wuSingularSeries N / log (N : ℝ))) +
        ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by linarith
    _ = _ := by ring

/-- The completed bounded successor: the physical T9 sieve, literal
fixed-delta density, and existing R1 estimate. R2 and small outputs remain
exactly exposed, and X9 is the actual prime-profile mass. -/
theorem T9_upper_source_with_R1 (A : ℝ) {δ ρ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
          (8 / (1 - 2 * δ))) * wuSingularSeries N / log (N : ℝ)) * X9 N +
        C * N / log (N : ℝ) ^ A +
        ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by
  obtain ⟨Td, hTd, hd⟩ := T9_upper_source_density hδ hδhi hρ
  obtain ⟨C, hC, Tr, _, hr⟩ := ninthSieveR1_source_bound A hA hδ
  refine ⟨C, hC, max Td Tr, hTd.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hfinite := hd N ((le_max_left _ _).trans hN) he
  have hR1 := hr N ((le_max_right _ _).trans hN) (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  linarith

end Wu2008DoubleSieve

import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKLargeGCDExclusion
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWTailBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative first large-gcd exclusion for the actual nonzero W sum

The original progression sum, its zero mode and its Fourier tail are estimated
on the identical arbitrary mask supported on `gcd(n₁,n₂) > x^η`. This excludes
the first gcd coordinate, not the union of all five large-gcd coordinates.
The beta parameter `T` is an upper endpoint, not a dyadic lower endpoint.
The condition `β n ≠ 0 → n ∤ a` is retained; its preprocessing is separate.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All three already proved estimates on precisely the same mask. The
constants precede all scales, supports, coefficients, residue and mask. -/
theorem wMaskedTruncated_abs_le_largeGCD
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) (l : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ M T L Y Z x : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 0 < Y → 0 < Z → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M Z) N Q β c a P| ≤
        C * M * x ^ ε *
          (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
            Real.sqrt ((1 + Real.log T) / Y)) +
        |M * dyadicCutoffMass| *
          (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
            Real.sqrt ((1 + Real.log T) / Y)) *
          (1 + Real.log L) ^ (2 * j ^ 2 + 1) +
        D * ((L * (1 + Real.log L) ^ (j - 1)) ^ 2 *
          (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / Z ^ l := by
  simpa only [one_mul] using
    wMaskedTruncated_abs_le_largeGCD_kscale hk hj l hε (le_refl (1 : ℝ))

/-- A power saving for the actual finite nonzero-frequency sum. The cutoff is
constructed, the mask is arbitrary within the first large-beta-gcd exclusion,
and the eventual threshold depends only on the fixed orders and `η`. -/
theorem eventually_wMaskedTruncated_largeGCD_power_saving
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
        3 * M * T ^ 2 * x ^ (-η / 8) := by
  simpa only [one_mul] using
    eventually_wMaskedTruncated_largeGCD_power_saving_kscale hk hj hη (le_refl (1 : ℝ))

/-- Explicit uniform threshold version of the power saving. -/
theorem wMaskedTruncated_largeGCD_power_saving
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
        3 * M * T ^ 2 * x ^ (-η / 8) := by
  simpa only [one_mul] using
    wMaskedTruncated_largeGCD_power_saving_kscale hk hj hη (le_refl (1 : ℝ))

/-- The actual alpha square sum pays every fixed natural logarithmic loss.
The threshold is uniform in both scales, all three signed coefficients,
supports, the varying residue and every submask of the first gcd exclusion. -/
theorem wMaskedTruncated_largeGCD_alpha_log_payment
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / Real.log x ^ A := by
  simpa only [one_mul] using
    wMaskedTruncated_largeGCD_alpha_log_payment_kscale hi hk hj A hη (le_refl (1 : ℝ))

/-- Real logarithmic exponents are paid as well, by rounding the requested
loss upward. No restriction on the fixed real exponent is needed. -/
theorem wMaskedTruncated_largeGCD_alpha_real_log_payment
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (A : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / (Real.log x) ^ A := by
  simpa only [one_mul] using
    wMaskedTruncated_largeGCD_alpha_real_log_payment_kscale hi hk hj A hη (le_refl (1 : ℝ))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

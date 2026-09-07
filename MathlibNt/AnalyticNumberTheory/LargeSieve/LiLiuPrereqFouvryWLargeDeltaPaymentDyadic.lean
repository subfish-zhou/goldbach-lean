import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDeltaDyadic

/-!
# Large common-modulus payment at the C.2 dyadic scale

The actual beta endpoint is `2 * T` when `4 * M * T = x`. Both lengths have
a positive power lower bound with exponent `min ε (min η (1 / 2))`.
The original sum, zero mode and tail use one identical arbitrary mask, and
the frequency cutoff is exactly `wUniformCutoff M (x ^ η)` throughout.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform logarithmic payment of every submask of the large common-modulus
part of the actual clean truncated W sum. No SW or nondivisibility assumption
on the original beta is required, and every divisor order may be zero. -/
theorem betaClean_wMaskedTruncated_largeDelta_dyadic
    (i k j A : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x →
      x ^ ε ≤ T → T ≤ x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t →
        x ^ η < (t.1.1.gcd t.1.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q
          (betaClean β a) c a P| ≤ x ^ 2 / Real.log x ^ A := by
  filter_upwards [betaClean_wMaskedTruncated_largeDelta_dyadic_kscale
    (Cscale := 1) i k j A hε hη le_rfl,
    eventually_ge_atTop (1 : ℝ)] with x hbound hx
  intro M T L hM hT hL hscale hlow hhigh hlevel
  have hhigh' : T ≤ x ^ (1 / 9 : ℝ) :=
    hhigh.trans (Real.rpow_le_rpow_of_exponent_le hx
      (by norm_num : (1 / 10 : ℝ) ≤ 1 / 9))
  simpa only [one_mul] using
    hbound M T L hM hT hL hscale hlow hhigh' hlevel

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

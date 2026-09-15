import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeSupportPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKSupportPaymentDyadic

/-!
# Large supported-factor payment at the C.2 dyadic scale

The actual beta endpoint is `2 * T` when `4 * M * T = x`. No power
separation of the lengths is needed, and the modulus endpoint may reach `x`.
The original sum, zero mode and tail retain the same arbitrary mask, with
frequency cutoff exactly `wUniformCutoff M (x ^ η)`.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform logarithmic payment of every submask of the large canonical
`d₁` part of the actual clean truncated W sum. Every divisor order may be
zero; no SW or nondivisibility assumption on the original beta is required. -/
theorem betaClean_wMaskedTruncated_largeSupport_dyadic
    (i k j A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x → L ≤ x →
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
        x ^ η < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q
          (betaClean β a) c a P| ≤ x ^ 2 / Real.log x ^ A := by
  simpa only [one_mul] using
    (betaClean_wMaskedTruncated_largeSupport_dyadic_kscale
      (Cscale := 1) i k j A hη le_rfl)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

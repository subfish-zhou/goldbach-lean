import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeSupportBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKSupportPayment

/-!
# Power payment for a large canonical supported beta factor

Here `T` is the upper beta endpoint. The sparse square-divisor envelope
saves `x ^ (-η / 4)` before paying the divisor loss and logarithms.
The original sum and zero mode retain the same arbitrary mask, and neither
length requires a positive power lower bound.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform power saving for the original and zero-mode terms on every
submask of the large canonical `d₁` condition. The threshold precedes all
changing data; nondivisibility is later supplied by `betaClean`. -/
theorem eventually_wMaskedOriginal_zero_largeSupport_power_saving
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t →
        x ^ η < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| ≤
        2 * M * T ^ 2 * x ^ (-η / 8) := by
  simpa only [one_mul] using
    (eventually_wMaskedOriginal_zero_largeSupport_power_saving_kscale
      (Cscale := 1) hk j hη le_rfl)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

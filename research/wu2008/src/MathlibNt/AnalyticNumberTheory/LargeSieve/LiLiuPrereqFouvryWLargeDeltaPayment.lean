import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaOriginalBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDeltaPayment

/-!
# Power payment for the same large-common-modulus mask

Here `T` is the upper beta endpoint. The saving depends on a positive lower
power bound for both lengths, not just on the common-modulus threshold.
The original progression sum and its zero mode keep exactly the same mask.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original and zero-mode terms are paid together on an arbitrary
submask of the large common-modulus condition. The threshold is uniform in
all changing data. The positive beta order is removed in the dyadic API. -/
theorem eventually_wMaskedOriginal_zero_largeDelta_power_saving
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ρ η : ℝ}
    (hρ : 0 < ρ) (hρη : ρ ≤ η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x → x ^ ρ ≤ M → x ^ ρ ≤ T →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| ≤
        2 * M * T ^ 2 * x ^ (-ρ / 2) := by
  simpa only [one_mul] using
    (eventually_wMaskedOriginal_zero_largeDelta_power_saving_kscale
      (Cscale := 1) hk j hρ hρη le_rfl)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

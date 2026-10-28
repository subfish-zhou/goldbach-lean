import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeSupportReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportZero
/-!
# The original C.2 error restricted to five small canonical factors

The two remaining supported modulus factors are removed by an exact finite
partition and the same-mask analytic payment. The original signed coefficients,
low-omega conditions, beta-family SW constants, and frequency cutoff are retained.
No estimate of the remaining IV.3 oscillatory sum is asserted.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- An exact subdivision inside any previous mask, with overlap of the two
large supported-modulus conditions counted only once. -/
theorem wMaskedTruncated_eq_modulus_support_small_add_large
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ ((wGCDTuple t).δ₁ : ℝ) ≤ Y ∧ ((wGCDTuple t).δ₂ : ℝ) ≤ Y) +
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧
          (Y < ((wGCDTuple t).δ₁ : ℝ) ∨ Y < ((wGCDTuple t).δ₂ : ℝ))) := by
  simp only [wMaskedTruncated, wMaskedTuples, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hp : P t <;>
    by_cases h₁ : ((wGCDTuple t).δ₁ : ℝ) ≤ Y <;>
    by_cases h₂ : ((wGCDTuple t).δ₂ : ℝ) ≤ Y <;>
    simp [hp, h₁, h₂, not_lt_of_ge, lt_of_not_ge]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

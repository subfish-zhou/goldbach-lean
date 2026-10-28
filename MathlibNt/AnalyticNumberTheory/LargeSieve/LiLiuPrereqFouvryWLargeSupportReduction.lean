import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKSupportPaymentDyadic


/-!
# Removing the large supported beta factor from the original C.2 error

The original signed error is now restricted to low-omega beta pairs with
`d`, `δ`, and `d₁` small. This is an exact subdivision of the previous tuple
domain followed by the same-mask payment, not monotonicity of a signed sum.
The two supported modulus factors and the IV.3 estimate remain separate.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Partition the actual truncated sum inside any preceding mask by `d₁`. -/
theorem wMaskedTruncated_eq_support_small_add_large
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ) ≤ Y) +
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ Y < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) := by
  simp only [wMaskedTruncated, wMaskedTuples, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hp : P t <;>
    by_cases hd : ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ) ≤ Y <;>
    simp [hp, hd, not_lt_of_ge, lt_of_not_ge]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDeltaDyadic


/-!
# The original C.2 error with both gcd restrictions

The low-omega, first-small-beta-gcd tuple domain is partitioned by the common
modulus. Its large part is paid using its own original sum, zero mode and tail.
The retained signed sum has the same coefficients, phases and frequency cutoff.
The three remaining support-factor exclusions and IV.3 are not asserted here.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- An exact partition inside any existing arithmetic mask. -/
theorem wMaskedTruncated_eq_delta_small_add_large
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ (t.1.1.gcd t.1.2 : ℝ) ≤ Y) +
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ Y < (t.1.1.gcd t.1.2 : ℝ)) := by
  simp only [wMaskedTruncated, wMaskedTuples, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hp : P t <;> by_cases hd : (t.1.1.gcd t.1.2 : ℝ) ≤ Y <;>
    simp [hp, hd, not_lt_of_ge, lt_of_not_ge]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

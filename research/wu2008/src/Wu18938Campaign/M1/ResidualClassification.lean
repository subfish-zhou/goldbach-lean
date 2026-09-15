import Wu18938Campaign.M1.FourFactorPoint
import Wu18938Campaign.M1.PointTransport

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

noncomputable def fourFactorIndices (N : ℕ) (z w u v V : ℝ) : Finset ℕ :=
  (range (N + 1)).filter
    (fun p => ∃ a b c d : ℕ, FourFactorShape N p a b c d z w u v V)

theorem fourFactor_residual_sum (N : ℕ) (z w u v V : ℝ) :
    (∑ p ∈ fourFactorIndices N z w u v V,
      (pointExcess N p z w u V - pointGains N p z w u v)) =
      ((fourFactorIndices N z w u v V).card : ℤ) := by
  calc
    _ = ∑ _p ∈ fourFactorIndices N z w u v V, (1 : ℤ) := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨a, b, c, d, h⟩ := (mem_filter.mp hp).2
      exact h.full_signed_residual_one
    _ = _ := by simp

theorem full_residual_classified (N : ℕ) (z w u v V : ℝ) :
    (quotientExcess N z w u V : ℝ) - quotientAssemblyGains N z w u v =
      ((fourFactorIndices N z w u v V).card : ℝ) +
      ((∑ p ∈ range (N + 1) \ fourFactorIndices N z w u v V,
        (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) -
      (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
      (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  have hs := sum_sdiff (f := fun p =>
    pointExcess N p z w u V - pointGains N p z w u v)
    (filter_subset (fun p => ∃ a b c d : ℕ,
      FourFactorShape N p a b c d z w u v V) (range (N + 1)))
  change (∑ p ∈ range (N + 1) \ fourFactorIndices N z w u v V,
    (pointExcess N p z w u V - pointGains N p z w u v)) +
    (∑ p ∈ fourFactorIndices N z w u v V,
      (pointExcess N p z w u V - pointGains N p z w u v)) = _ at hs
  rw [fourFactor_residual_sum] at hs
  rw [full_signed_residual_sum, ← hs]
  push_cast
  ring

end Wu18938Campaign.M1

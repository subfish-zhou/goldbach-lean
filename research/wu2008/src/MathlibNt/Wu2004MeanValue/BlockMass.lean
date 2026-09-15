import MathlibNt.Wu2004MeanValue.BlockMassEndpoints
import MathlibNt.Wu2004MeanValue.BlockMassPrimes

/-!
# The actual manuscript block mass is O(H / log H)

The constant is independent of `N` and `eta`; in fact the proof gives one
constant for all `a > 3/2` and all real `eta`.  The finite source retains its
primality, coprimality, real-power cutoff, square-root cutoff, and nonempty
interval filter.  No estimate for arbitrary empty/reversed endpoint choices
is substituted for that source.
-/

namespace Wu2004MeanValue

open Finset

theorem blockMass_le_reciprocal_sum {H : ℝ} (N : ℕ) (a η : ℝ)
    (hH : 1 < H) :
    blockMass H N a η ≤
      (4 * H / Real.log H) * ∑ m ∈ blockSource H N a η, 1 / (m : ℝ) := by
  unfold blockMass intervalMass
  rw [mul_sum]
  exact sum_le_sum (fun _ hm => blockMass_term_le hH hm)

/-- Uniformity stronger than required by the fixed-`a` manuscript estimate:
one positive constant, the explicit real threshold `4`, and no `eta` bound. -/
theorem blockMass_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 4 ≤ H →
      ∀ (N : ℕ) (a η : ℝ), 3 / 2 < a →
        0 ≤ blockMass H N a η ∧ blockMass H N a η ≤ C * H / Real.log H := by
  obtain ⟨C, hC, hbound⟩ := blockSource_reciprocal_sum_bounded
  refine ⟨4 * C, by positivity, ?_⟩
  intro H hH N a η ha
  refine ⟨blockMass_nonneg H N a η, ?_⟩
  have hlog : 0 < Real.log H := Real.log_pos (by linarith)
  calc
    blockMass H N a η ≤
        (4 * H / Real.log H) * ∑ m ∈ blockSource H N a η, 1 / (m : ℝ) :=
      blockMass_le_reciprocal_sum N a η (by linarith)
    _ ≤ (4 * H / Real.log H) * C :=
      mul_le_mul_of_nonneg_left (hbound H hH N a η ha)
        (div_nonneg (by linarith) hlog.le)
    _ = (4 * C) * H / Real.log H := by ring

/-- The requested fixed-parameter quantifiers for the literal block mass.
The upper restriction on `a` and the restriction on `eta` are not needed for
the stronger uniform theorem, but are retained here as the manuscript API. -/
theorem exists_blockMass_le (a : ℝ) (ha : 3 / 2 < a) (_ha2 : a < 2) :
    ∃ C H₀ : ℝ, 0 < C ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ (N : ℕ) (η : ℝ), η ≤ 1 →
        0 ≤ blockMass H N a η ∧ blockMass H N a η ≤ C * H / Real.log H := by
  obtain ⟨C, hC, hbound⟩ := blockMass_uniform_bound
  exact ⟨C, 4, hC, fun H hH N η _hη => hbound H hH N a η ha⟩

end Wu2004MeanValue

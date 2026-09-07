import MathlibNt.SieveTheory.LiLiuGoldbachG12CutoffSlicePayment
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundaryBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalGridPartition

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12FineGrid

/-- The two boundary branches may overlap. This is an upper bound for a
nonnegative physical test, never a subtraction of signed distribution terms. -/
theorem boundary_sum_le_branches {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ)
    (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k, f p) ≤
      (∑ p ∈ productBoundary ρ N ε, f p) + ∑ p ∈ roughBoundary ρ N ε, f p := by
  have heq : (∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), f p) =
      ∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k, f p := by
    apply sum_biUnion
    intro k _ l _ hkl
    exact (cell_disjoint hρ N ε hkl).mono sdiff_subset sdiff_subset
  rw [← heq,boundary_union_decomposition]
  have h := sum_union_inter (s₁ := productBoundary ρ N ε) (s₂ := roughBoundary ρ N ε) (f := f)
  have hn : 0 ≤ ∑ p ∈ productBoundary ρ N ε ∩ roughBoundary ρ N ε, f p :=
    sum_nonneg (fun p _ => hf p)
  linarith only [h,hn]

/-- The retained prime cutoff slice is actually paid in the complete original
count. Safe, product-boundary and roughness outputs all remain explicit. -/
theorem original_total_paid_grid (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ρ ε : ℝ, 1 < ρ →
      (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
        G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) +
        (400*∑ k ∈ indices ρ N, ∑ p ∈ safe ρ N ε k,
          goldbachG12NormalizedCoefficient N p.1*(if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
        G12LowHighOutput.outputCount N (productBoundary ρ N ε) +
        G12LowHighOutput.outputCount N (roughBoundary ρ N ε) +
        δ*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨J,hJ,hcut⟩ := cutoffOutput_normalized δ hδ
  refine ⟨J,hJ,?_⟩
  intro N hN ρ ε hρ
  let f : ℕ × ℕ → ℝ := fun p => goldbachG12NormalizedCoefficient N p.1*
    (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)
  have hf : ∀ p, 0 ≤ f p := by
    intro p
    exact mul_nonneg (goldbachG12NormalizedCoefficient_bounds N p.1).1
      (by split_ifs <;> norm_num)
  have hb := mul_le_mul_of_nonneg_left (boundary_sum_le_branches hρ N ε f hf)
    (by norm_num : (0 : ℝ) ≤ 400)
  rw [mul_add] at hb
  have hc := hcut N hN ε
  have ht := original_total_grid_partition hρ (by omega : 2 ≤ N) ε
  rw [sum_add_distrib,mul_add] at ht
  change _ = G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) +
    cutoffOutput N ε + ((400*∑ k ∈ indices ρ N, ∑ p ∈ safe ρ N ε k, f p) +
    (400*∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k, f p)) at ht
  change _ ≤ G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) +
    (400*∑ k ∈ indices ρ N, ∑ p ∈ safe ρ N ε k, f p) +
    (400*∑ p ∈ productBoundary ρ N ε, f p) +
    (400*∑ p ∈ roughBoundary ρ N ε, f p) + _
  linarith only [ht,hb,hc]

end G12FineGrid

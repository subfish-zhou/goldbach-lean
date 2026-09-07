import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidFixedGrid

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SafeGridBudget

/-- The literal union of all actual safe cells in the original finite grid. -/
def safeUnion (ρ : ℝ) (N : ℕ) (e : ℝ) : Finset (ℕ × ℕ) :=
  (G12FineGrid.indices ρ N).biUnion (G12FineGrid.safe ρ N e)

theorem safe_pairwise {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N) (e : ℝ) :
    (↑(G12FineGrid.indices ρ N) : Set (ℕ × ℕ)).PairwiseDisjoint (G12FineGrid.safe ρ N e) := by
  intro k _ l _ hkl
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (G12FineGrid.cell_disjoint hρ N e hkl)
    (G12FineGrid.safe_subset ρ hN e k hp) (G12FineGrid.safe_subset ρ hN e l hq)

theorem safe_union_sum {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N)
    (e : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ safeUnion ρ N e, f p) =
      ∑ k ∈ G12FineGrid.indices ρ N, ∑ p ∈ G12FineGrid.safe ρ N e k, f p := by
  exact sum_biUnion (safe_pairwise hρ hN e)

/-- Literal safe-set terminal: no duplicated grid atoms, no artificial weights,
no unbound additive fees, and independent fixed main/additive slacks. -/
theorem safe_union_normalized (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (ρ : ℝ) (hρ : 1 < ρ) (hρu : ρ ≤ 3/2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N →
      (400*∑ p ∈ safeUnion ρ N e, goldbachG12NormalizedCoefficient N p.1*
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
      400*(∑ p ∈ safeUnion ρ N e, goldbachG12NormalizedCoefficient N p.1*
        (goldbachG11AuthorWeight (Real.log p.2 / Real.log N)+δ))*
        SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
      τ*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨J,hJ,hj⟩ := fixed_grid_normalized δ τ hδ hτ e he he1 ρ hρ hρu
  refine ⟨J,hJ,?_⟩
  intro N hN hEven
  have hN1 : 1 ≤ N := by omega
  have h := hj N hN hEven
  unfold originalOutput authorMass at h
  rw [safe_union_sum hρ hN1, safe_union_sum hρ hN1, mul_sum]
  exact h

end G12SafeGridBudget

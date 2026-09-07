import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutputSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalGridPartition
import MathlibNt.SieveTheory.LiLiuGoldbachG12CutoffSlicePayment

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12FineGrid

/-- Original total count with the actual high source normalized and the cutoff
slice paid. The entire boundary remains a literal output count, not a raw mass. -/
theorem original_total_high_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∀ ρ : ℝ, 1 < ρ → ∀ ε : ℝ,
      (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
      (8+δ/2)*400*G12ClippedWindow.highMass N ε*
        SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
      (400*∑ k ∈ indices ρ N, ∑ p ∈ safe ρ N ε k,
        goldbachG12NormalizedCoefficient N p.1*(if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
      G12LowHighOutput.outputCount N ((indices ρ N).biUnion (boundaryCell ρ N ε)) +
      δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨H,hH,hhigh⟩ := G12ClippedWindow.physical_high_uniformEight (δ/2) (half_pos hδ)
  obtain ⟨C,hC,hcut⟩ := cutoffOutput_normalized (δ/2) (half_pos hδ)
  refine ⟨max H C,hH.trans (le_max_left _ _),?_⟩
  intro N hN hEven ρ hρ ε
  have hh := hhigh N ((le_max_left _ _).trans hN) hEven ε
  have hc := hcut N ((le_max_right _ _).trans hN) ε
  have hp := original_total_grid_partition hρ (by omega : 2 ≤ N) ε
  rw [sum_add_distrib,mul_add] at hp
  have hb := G12RoughBoundary.fullBoundary_sum_cells hρ N ε
    (fun p => goldbachG12NormalizedCoefficient N p.1*
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0))
  unfold G12LowHighOutput.outputCount
  rw [hb]
  dsimp only [cutoffOutput] at hc
  linarith only [hp,hh,hc]

end G12FineGrid

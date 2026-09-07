import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutputWindow

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12FineGrid

/-- The original complete product-prime count, not merely the low mother,
retains the high output, the cutoff slice and every unsafe boundary atom. -/
theorem original_total_grid_partition {ρ : ℝ} (hρ : 1 < ρ)
    {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) =
      G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) +
      (400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
      400 * ∑ k ∈ indices ρ N,
        ((∑ p ∈ safe ρ N ε k, goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
        ∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) := by
  have hl : G12LowHighOutput.outputCount N (G12LowHighOutput.low N ε) =
      (400 * ∑ p ∈ G12FlexibleRectangle.mother N ε,
        goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) := by
    rw [G12LowHighOutput.outputCount,G12LowHighOutput.low_eq_mother]
  rw [G12LowHighOutput.original_total_partition N ε hN,hl,
    refined_weighted_partition hρ (by omega : 1 ≤ N) ε]
  ring

end G12FineGrid

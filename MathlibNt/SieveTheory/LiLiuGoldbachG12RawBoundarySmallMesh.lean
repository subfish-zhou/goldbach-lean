import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12FineGrid

/-- Fix a genuinely small geometric mesh before the truncation and ambient
threshold. This is only the raw-mother normalization, not a prime-output bound. -/
theorem exists_small_raw_boundary_mesh (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 3/2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 2/15 →
      ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K,
        Real.log (N : ℝ)/(N : ℝ)*
          (400*∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k,
            goldbachG12NormalizedCoefficient N p.1) ≤ τ := by
  obtain ⟨C,hC,hb⟩ := G12RoughBoundary.exists_fixed_fullBoundary_constant
  let t : ℝ := min (1/2) (τ/(2*C))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht2 : t ≤ 1/2 := min_le_left _ _
  have hct : C*t ≤ τ/2 := by
    calc
      C*t ≤ C*(τ/(2*C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = τ/2 := by field_simp
  refine ⟨1+t/2,by linarith,by linarith,?_⟩
  intro ε he he2
  obtain ⟨K,hK,hbound⟩ := hb (1+t/2) (1+t) ε (by linarith)
    (by linarith) (by linarith) he he2 (τ/2) (half_pos hτ)
  refine ⟨K,hK,?_⟩
  intro N hN
  have h := hbound N hN
  rw [G12RoughBoundary.fullBoundary_sum_cells (by linarith : 1 < 1+t/2)] at h
  linarith only [h,hct]

end G12FineGrid

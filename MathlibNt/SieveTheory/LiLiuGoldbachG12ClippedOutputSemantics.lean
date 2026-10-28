import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedUniform

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12ClippedWindow

/-- The literal indicator sum, including all repeated output representations. -/
theorem primeOutput_eq_indicator (N : ℕ) (g L U : ℕ → ℝ) :
    primeOutput N g L U = 400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
      g m * ∑ r ∈ window N L U m, (if (N-r*m).Prime then (1 : ℝ) else 0) := by
  simp only [primeOutput,Finset.sum_boole]


/-- The original physical high count embeds in the actual ungated high source.
The common mass on the right is highMass, not a coprime physical mass. -/
theorem physical_high_le_source (N : ℕ) (ε : ℝ) :
    G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) ≤ highPrimeOutput N ε := by
  rw [G12LowHighOutput.original_high_count]
  have hsub (m : ℕ) (hm : m ∈ goldbachG12ActiveProductSupport N) :
      ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ))) ⊆
      (G12LowHighOutput.highWindow N ε m).filter (fun r => (N-r*m).Prime) := by
    intro r hr
    obtain ⟨hr,hh⟩ := mem_filter.mp hr
    rw [goldbachG12ProductFirstPrimeFiber_eq_linkedWindow hm] at hr
    obtain ⟨hw,_,hp⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hw,hh⟩,hp⟩
  calc
    _ ≤ ∑ m ∈ goldbachG12ActiveProductSupport N,
        (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
        (((G12LowHighOutput.highWindow N ε m).filter (fun r => (N-r*m).Prime)).card : ℝ) := by
      apply sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hsub m hm))) (Nat.cast_nonneg _)
    _ = _ := by
      unfold highPrimeOutput
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      unfold goldbachG12NormalizedCoefficient
      ring

/-- Original high output theorem, with no subtraction of upper bounds. -/
theorem physical_high_uniformEight (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ),
      G12LowHighOutput.outputCount N (G12LowHighOutput.high N ε) ≤
        (8+δ)*400*highMass N ε*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,hK,h⟩ := highPrimeOutput_uniformEight δ hδ
  exact ⟨K,hK,fun N hN hEven ε => (physical_high_le_source N ε).trans (h N hN hEven ε)⟩


end G12ClippedWindow

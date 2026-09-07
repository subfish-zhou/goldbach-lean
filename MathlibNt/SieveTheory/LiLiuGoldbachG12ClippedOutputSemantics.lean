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

/-- Coprime-r physical subcount. The common source mass is deliberately not renamed. -/
def coprimePrimeOutput (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  400 * ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => r.Coprime N ∧ (N-r*m).Prime)).card : ℝ)

/-- Retained r|N contribution; it is included in the ungated sieve, not silently deleted. -/
def noncoprimePrimeOutput (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  400 * ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => ¬r.Coprime N ∧ (N-r*m).Prime)).card : ℝ)

theorem primeOutput_split_coprime (N : ℕ) (g L U : ℕ → ℝ) :
    primeOutput N g L U = coprimePrimeOutput N g L U + noncoprimePrimeOutput N g L U := by
  unfold primeOutput coprimePrimeOutput noncoprimePrimeOutput
  simp only [← Finset.sum_boole,← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro m _
  congr 1
  apply sum_congr rfl
  intro r _
  by_cases hc : r.Coprime N <;> by_cases hp : (N-r*m).Prime <;> simp [hc,hp]

theorem coprimePrimeOutput_le {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}
    (h : Admissible N ε g L U) : coprimePrimeOutput N g L U ≤ primeOutput N g L U := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 400)
  apply sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left _ (h m hm).1.1
  exact_mod_cast card_le_card (show
    (window N L U m).filter (fun r => r.Coprime N ∧ (N-r*m).Prime) ⊆
      (window N L U m).filter (fun r => (N-r*m).Prime) from
    fun r hr => mem_filter.mpr ⟨(mem_filter.mp hr).1,(mem_filter.mp hr).2.2⟩)

theorem equal_endpoints_empty (N : ℕ) (L : ℕ → ℝ) (m : ℕ) : window N L L m = ∅ := by
  apply eq_empty_of_forall_notMem
  intro r hr
  obtain ⟨_,_,hl,hu⟩ := mem_filter.mp hr
  exact (not_lt_of_ge hu) hl

theorem equal_endpoints_zero (N : ℕ) (g L : ℕ → ℝ) :
    primeOutput N g L L = 0 ∧ mass N g L L = 0 := by
  simp [primeOutput,mass,equal_endpoints_empty]

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

/-- Expanded publication-facing endpoint: the exact indicator sum, not a proxy. -/
theorem actual_output_uniformEight (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N)
      (g L U : ℕ → ℝ) (ε : ℝ), Admissible N ε g L U →
      (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        g m * ∑ r ∈ window N L U m, (if (N-r*m).Prime then (1 : ℝ) else 0)) ≤
        (8+δ)*400*(∑ m ∈ goldbachG12ActiveProductSupport N, g m * (window N L U m).card)*
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,hK,h⟩ := primeOutput_uniformEight δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN hEven g L U ε ha
  have hp := h N hN hEven g L U ε ha
  simpa only [primeOutput_eq_indicator,mass] using hp

end G12ClippedWindow

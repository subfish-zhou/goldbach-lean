import MathlibNt.Wu2004MeanValue.SieveSupport
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The literal real sieve level: `d < D`, `d | P_N(sqrt D)`.
Only the finite modulus summation uses `floor D`; the prime cutoff is
`sqrt D`, never `sqrt (floor D)`. -/

namespace Wu2004MeanValue

open Classical Finset
noncomputable section

def sieveDivisors (N : ℕ) (D : ℝ) : Finset ℕ :=
  (sieveModuli N (Real.sqrt D) ⌊D⌋₊).filter (fun d => (d : ℝ) < D)

theorem mem_sieveDivisors {N d : ℕ} {D : ℝ} :
    d ∈ sieveDivisors N D ↔
      1 ≤ d ∧ (d : ℝ) < D ∧ d ∣ siftingProduct N (Real.sqrt D) := by
  simp only [sieveDivisors, mem_filter, mem_sieveModuli]
  constructor
  · rintro ⟨⟨hd, _, hp⟩, hD⟩
    exact ⟨hd, hD, hp⟩
  · rintro ⟨hd, hD, hp⟩
    have hD0 : 0 ≤ D := (Nat.cast_nonneg d).trans hD.le
    exact ⟨⟨hd, (Nat.le_floor_iff hD0).mpr hD.le, hp⟩, hD⟩

theorem sieveDivisors_subset_sieveModuli (N : ℕ) (D : ℝ) :
    sieveDivisors N D ⊆ sieveModuli N (Real.sqrt D) ⌊D⌋₊ :=
  filter_subset _ _

theorem sieveDivisors_subset_coprime (N : ℕ) (D : ℝ) :
    sieveDivisors N D ⊆ (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d) := by
  intro d hd
  have hd' := sieveDivisors_subset_sieveModuli N D hd
  exact mem_filter.mpr ⟨sieveModuli_subset_Icc N _ _ hd',
    coprime_of_mem_sieveModuli hd'⟩

theorem sieveDivisors_squarefree {N d : ℕ} {D : ℝ}
    (hd : d ∈ sieveDivisors N D) : Squarefree d :=
  squarefree_of_mem_sieveModuli (sieveDivisors_subset_sieveModuli N D hd)

end
end Wu2004MeanValue

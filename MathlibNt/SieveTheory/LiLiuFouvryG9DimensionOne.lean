import MathlibNt.SieveTheory.LiLiuPrereqWFExternalSieve
import MathlibNt.SieveTheory.MertensTheorem

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open SmallRosser

/-- One existing Mertens constant works uniformly for every finite odd-prime
carrier and every local density dominated by the Goldbach local density.
Removing factors for primes dividing the changing product does not change K. -/
theorem g9Density_exists_uniform_dimension_one :
    ∃ K : ℝ, 1 < K ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2 < p) → ∀ g : ℕ → ℝ,
      (∀ p ∈ P, g p ≤ 1/((p : ℝ)-1)) → DimensionOneProductBound P g K := by
  obtain ⟨K,hK,hbound⟩ := MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K,hK,?_⟩
  intro P hP g hg w z hw hwz
  let S := P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hS : ∀ p ∈ S, p.Prime ∧ 2 < p := fun p hp => hP p (mem_filter.mp hp).1
  have hbase : ∀ p ∈ S, 1/((p : ℝ)-1) < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (hS p hp).2
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hsmall : ∀ p ∈ S, g p < 1 := fun p hp =>
    (hg p (mem_filter.mp hp).1).trans_lt (hbase p hp)
  calc
    _ ≤ ∏ p ∈ S, (1-1/((p : ℝ)-1))⁻¹ := by
      apply prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (hsmall p hp).le)
      · intro p hp
        simpa only [one_div] using one_div_le_one_div_of_le
          (sub_pos.mpr (hbase p hp)) (sub_le_sub_left (hg p (mem_filter.mp hp).1) 1)
    _ ≤ _ := hbound S hS w z hw hwz.le (fun p hp => (mem_filter.mp hp).2.2)

end MathlibNt.SieveTheory.LiLiuPrereqWF

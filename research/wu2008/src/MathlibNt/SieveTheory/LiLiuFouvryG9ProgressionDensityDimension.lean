import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensity
import MathlibNt.SieveTheory.MertensTheorem

/-! A uniform dimension-one constant for the actual progression density.
This is only an exact finite-product adapter to the proved Goldbach interval
bound. No Mertens estimate is reproved here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open scoped Classical

/-- One constant works simultaneously for every progression parameter and every
finite carrier of odd primes. The interval retains its closed left and strict
right endpoints. -/
theorem exists_progressionDensity_dimensionOneProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (v : ℕ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2 < p) →
        DimensionOneProductBound P (progressionDensity v) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro v P hP w z hw hwz
  let T := P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  let S := T.filter (fun p => p.Coprime v)
  have hS : ∀ p ∈ S, p.Prime ∧ 2 < p := by
    intro p hp
    exact hP p (mem_filter.mp (mem_filter.mp hp).1).1
  have hSinterval : ∀ p ∈ S, w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
    intro p hp
    exact (mem_filter.mp (mem_filter.mp hp).1).2.2
  have heq : (∏ p ∈ T, (1 - progressionDensity v p)⁻¹) =
      ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    change _ = ∏ p ∈ T.filter (fun p => p.Coprime v), _
    conv_rhs => rw [prod_filter]
    apply prod_congr rfl
    intro p hp
    rw [progressionDensity_prime v (hP p (mem_filter.mp hp).1).1]
    split_ifs <;> simp
  change (∏ p ∈ T, (1 - progressionDensity v p)⁻¹) ≤ _
  rw [heq]
  exact hinterval S hS w z hw hwz.le hSinterval

/-- The precise form consumed by `exists_externalFamilyDensity_ff`. -/
theorem exists_progressionOmega_dimensionOneProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (v : ℕ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2 < p) →
        DimensionOneProductBound P (primeDensity (progressionOmega v)) K := by
  simpa only [primeDensity_progressionOmega] using
    exists_progressionDensity_dimensionOneProductBound

end MathlibNt.SieveTheory.LiLiuPrereqWF

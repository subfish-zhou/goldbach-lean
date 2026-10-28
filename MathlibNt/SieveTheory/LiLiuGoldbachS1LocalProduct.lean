import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums

/-! A single uniform local-product witness for the actual Goldbach S1 sieve. -/
open scoped BigOperators
open Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS1_exists_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ),
      HasDimensionOneLocalProductBound (goldbachS1BoundingSieve N hEven ε z) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven ε z z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (goldbachS1ProdPrimes N z).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    rw [goldbachS1ProdPrimes_primeFactors] at hpS
    have hpData := mem_goldbachS1SiftingPrimes_iff.mp hpS
    refine ⟨hpData.2.1, lt_of_le_of_ne hpData.2.1.two_le ?_⟩
    rintro rfl
    exact hpData.2.2 (even_iff_two_dvd.mp hEven)
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂
    (fun p hp => (Finset.mem_filter.mp hp).2)
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

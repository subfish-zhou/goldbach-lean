import MathlibNt.SieveTheory.LiLiuGoldbachS1LocalProduct
import MathlibNt.SieveTheory.LiLiuGoldbachUpperDensitySix
import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.MertensTheorem

open scoped BigOperators
open Finset Filter
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- The actual finite S3 Rosser main sum, with the genuine local-product
witness supplied internally; the threshold is uniform in every sieve parameter. -/
theorem goldbachS3RosserMain_upper_six (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (N : ℕ) (hEven : Even N) (ε z Δ s : ℝ),
      z₀ ≤ z → 0 < Δ → s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 6 →
      (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
        LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z) (Nat.floor Δ + 1) d /
          (Nat.totient d : ℝ)) ≤
        (suzukiContinuousUpperFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (goldbachS1BoundingSieve N hEven ε z) := by
  obtain ⟨K, hK, hlocal⟩ := goldbachS1_exists_dimensionOneLocalProductBound
  obtain ⟨z₀, hz₀⟩ := goldbach_upperRosserDensity_six K ρ hK hρ
  refine ⟨max 2 z₀, le_max_left _ _, ?_⟩
  intro N hEven ε z Δ s hz hΔ hs hslo hshi
  have hcut : ∀ p ∈ (goldbachS1BoundingSieve N hEven ε z).prodPrimes.primeFactors,
      (p : ℝ) ≤ z := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ goldbachS1ProdPrimes N z :=
      (Nat.mem_primeFactors_of_ne_zero (goldbachS1ProdPrimes_ne_zero N z)).mp hp |>.2
    exact ((prime_dvd_goldbachS1ProdPrimes_iff hpp).mp hpd).1.le
  have h := hz₀ (goldbachS1BoundingSieve N hEven ε z) z Δ s
    ((le_max_right _ _).trans hz) ((le_max_left _ _).trans hz) hΔ
    (hlocal N hEven ε z) hcut hs hslo hshi
  rw [goldbachS1BoundingSieve_mainSum_eq_totientSum] at h
  exact h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
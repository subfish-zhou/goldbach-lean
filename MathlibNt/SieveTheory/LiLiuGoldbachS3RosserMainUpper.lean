import MathlibNt.SieveTheory.LiLiuGoldbachUpperDensitySix
import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.MertensTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators
open Finset Filter
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem S3RosserMain_exists_localProductBound :
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
    have hp' :
        p ∈ (goldbachS1ProdPrimes N z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ goldbachS1ProdPrimes N z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N z)).mp hp'.1 |>.2
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachS1ProdPrimes_iff hprime).mp hpdiv |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hprime.two_le (by simpa using hpne.symm)
    exact ⟨hprime, hp2⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (goldbachS1ProdPrimes N z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound

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
  obtain ⟨K, hK, hlocal⟩ := S3RosserMain_exists_localProductBound
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
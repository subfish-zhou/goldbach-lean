import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.SuzukiLemma147JurkatRichertInterval

open scoped BigOperators
open Finset MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem PairDensity_local_base :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ) (m : ℕ),
      HasDimensionOneLocalProductBound (goldbachS3BoundingSieve N hEven ε z m) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven ε z m z₁ z₂ hz₁ hz₁₂
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

/-- One dimension-one constant works for every actual composite-conditioned
Goldbach sieve, before N, epsilon, the sieve cutoff, and the outer modulus. -/
theorem exists_goldbachComposite_dimensionOne_constant :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ) (m : ℕ),
      HasDimensionOneLocalProductBound (goldbachS3BoundingSieve N hEven ε z m) K := by
  obtain ⟨K₀, _, hlocal₀⟩ := PairDensity_local_base
  refine ⟨max 2 K₀, le_max_left _ _, ?_⟩
  intro N hEven ε z m
  exact MathlibNt.SieveTheory.hasDimensionOneLocalProductBound_mono_K
    (hlocal₀ N hEven ε z m) (le_max_right 2 K₀)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

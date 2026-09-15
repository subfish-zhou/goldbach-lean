import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveGlobalScaling

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144Equation1410

/-- Restricting a support to primes below `z` does not change the middle
carrier when its upper cutoff is at most `z`. -/
theorem sigmaOneCarrier_filter_lt_eq
    (support : Finset ℕ) {D z : ℕ} {σ τ : ℝ}
    (hvz : (D : ℝ) ^ (1 / τ) ≤ (z : ℝ)) :
    sigmaOneCarrier (support.filter fun p => p < z) D σ τ =
      sigmaOneCarrier support D σ τ := by
  ext p
  simp only [sigmaOneCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, _⟩, hlow, hupp⟩
    exact ⟨hp, hlow, hupp⟩
  · rintro ⟨hp, hlow, hupp⟩
    refine ⟨⟨hp, ?_⟩, hlow, hupp⟩
    exact_mod_cast hupp.trans_le hvz

/-- `sigmaTwelve` is exactly unchanged when its full support is replaced by
that support cut off below `z`, provided the middle upper cutoff lies below
`z`.  This is equality, not merely monotonicity. -/
theorem sigmaTwelve_filter_lt_eq
    (support : Finset ℕ) (omega V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (Vz C K Δ : ℝ) (N D z : ℕ) (σ τ : ℝ)
    (hvz : (D : ℝ) ^ (1 / τ) ≤ (z : ℝ)) :
    sigmaTwelve (support.filter fun p => p < z) omega V E
        Vz C K Δ N D σ τ =
      sigmaTwelve support omega V E Vz C K Δ N D σ τ := by
  unfold sigmaTwelve
  rw [sigmaOneCarrier_filter_lt_eq support hvz]

/-- Bounding-sieve specialization: this is the exact carrier represented by
`suzukiSupportedBelow S z` after unfolding that definition. -/
theorem sigmaOneCarrier_supportedBelow_eq_full
    (S : BoundingSieve) {D z : ℕ} {σ τ : ℝ}
    (hvz : (D : ℝ) ^ (1 / τ) ≤ (z : ℝ)) :
    sigmaOneCarrier
        (S.prodPrimes.primeFactors.filter fun p => p < z) D σ τ =
      sigmaOneCarrier S.prodPrimes.primeFactors D σ τ :=
  sigmaOneCarrier_filter_lt_eq S.prodPrimes.primeFactors hvz

/-- Exact supported/full `sigmaTwelve` equality for a bounding sieve.  The
left support is definitionally the finite set used by `suzukiSupportedBelow`. -/
theorem sigmaTwelve_supportedBelow_eq_full
    (S : BoundingSieve) (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (Vz C K Δ : ℝ) (N D z : ℕ) (σ τ : ℝ)
    (hvz : (D : ℝ) ^ (1 / τ) ≤ (z : ℝ)) :
    sigmaTwelve (S.prodPrimes.primeFactors.filter fun p => p < z)
        S.nu V E Vz C K Δ N D σ τ =
      sigmaTwelve S.prodPrimes.primeFactors S.nu V E
        Vz C K Δ N D σ τ :=
  sigmaTwelve_filter_lt_eq S.prodPrimes.primeFactors S.nu V E
    Vz C K Δ N D z σ τ hvz


end SuzukiLemma144Equation1410
end MathlibNt.SieveTheory.SwitchingPrinciple

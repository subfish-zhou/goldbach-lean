/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import AnalyticNumberTheory
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147ContinuousLowerFactor

/-!
# Exact finite bridge from Suzuki densities to `BoundingSieve`

This module identifies the finite carriers and products used on the Suzuki side
with the corresponding Jurkat--Richert `BoundingSieve` objects.  No analytic
estimate or limiting argument enters these identities.
-/

namespace MathlibNt.SieveTheory

open LinearSieve

namespace SwitchingPrinciple

/-- If every supported prime is below the natural cutoff, Suzuki's filtered
carrier is exactly the complete prime-factor carrier of the sieve. -/
theorem suzukiSupportedBelow_eq_primeFactors_of_all_lt
    (S : BoundingSieve) {z : ℕ}
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    suzukiSupportedBelow S z = S.prodPrimes.primeFactors := by
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact hz p hp

/-- Under the corresponding real cutoff hypothesis, Suzuki's `V(z)` is exactly
the Euler product used by `BoundingSieve`. -/
theorem suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt
    (S : BoundingSieve) {z : ℝ}
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) < z) :
    suzukiVProduct S z =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  unfold suzukiVProduct AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
  rw [Finset.filter_eq_self.mpr hz]

/-- The existing divisor/powerset identity for lower Rosser weights, transported
to Suzuki's supported-below carrier. -/
theorem mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt
    (S : BoundingSieve) (D : ℕ) {z : ℕ}
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (lowerRosserWeight S.prodPrimes D) =
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  rw [suzukiSupportedBelow_eq_primeFactors_of_all_lt S hz]
  exact mainSum_lowerRosserWeight_eq_setDensitySum S D

/-- Production bundle: when all prime factors lie both below Suzuki's cutoff and
below the Rosser level, the Suzuki density and Euler product are literally the
`BoundingSieve` main sum and sieve product, and the same finite coefficient has
the required lower-Möbius certificate. -/
theorem suzukiDensityProduct_lowerRosserWeight_exact_bridge
    (S : BoundingSieve) (D z : ℕ)
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z)
    (hD : ∀ p ∈ S.prodPrimes.primeFactors, p < D) :
    S.mainSum (lowerRosserWeight S.prodPrimes D) =
        lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) ∧
      suzukiVProduct S (z : ℝ) =
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ∧
      IsLowerRosserCertificate S.prodPrimes D := by
  refine ⟨mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt S D hz, ?_, ?_⟩
  · apply suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt
    intro p hp
    exact_mod_cast hz p hp
  · exact lowerRosserWeight_certificate S.prodPrimes_squarefree
      S.prodPrimes_ne_zero hD

end SwitchingPrinciple
end MathlibNt.SieveTheory

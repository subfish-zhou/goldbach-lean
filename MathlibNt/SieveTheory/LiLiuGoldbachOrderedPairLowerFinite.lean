import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open BombieriVinogradov

/-- The original divisibility-conditioned carrier satisfies the lower Rosser
inequality for every outer modulus, including a square of a prime. -/
theorem goldbachComposite_lowerRosser_finite
    {N : ℕ} (hEven : Even N) (ε z : ℝ) (p D : ℕ)
    (hprimeD : ∀ q ∈ (goldbachS1ProdPrimes N z).primeFactors, q < D) :
    trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
      ((1 / (Nat.totient p : ℝ)) *
        (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
          LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z) D d /
            (Nat.totient d : ℝ))) -
      LinearSieve.lowerErrSum (goldbachS3BoundingSieve N hEven ε z p) D
        (LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z) D) ≤
      (literalH (goldbachDifferenceCarrier N ε) N p z : ℝ) := by
  let S := goldbachS3BoundingSieve N hEven ε z p
  let P := goldbachS1ProdPrimes N z
  let μ := LinearSieve.lowerRosserWeight P D
  have hcert : LinearSieve.IsLowerRosserCertificate P D :=
    LinearSieve.lowerRosserWeight_certificate
      (goldbachS1ProdPrimes_squarefree N z) (goldbachS1ProdPrimes_ne_zero N z) hprimeD
  have hfinite : S.totalMass * S.mainSum μ - LinearSieve.lowerErrSum S D μ ≤
      S.siftedSum :=
    LinearSieve.mainSum_sub_lowerErrSum_le_siftedSum D μ hcert
      (LinearSieve.lowerRosserWeight_hasLowerLevelSupport P D)
  change (goldbachS3BoundingSieve N hEven ε z p).totalMass *
      (goldbachS3BoundingSieve N hEven ε z p).mainSum μ -
      LinearSieve.lowerErrSum S D μ ≤
      (goldbachS3BoundingSieve N hEven ε z p).siftedSum at hfinite
  rw [goldbachS3BoundingSieve_mainSum_eq_totientSum,
    goldbachS3BoundingSieve_siftedSum_eq] at hfinite
  change (trueLogarithmicIntegral (goldbachS1Endpoint N ε) / Nat.totient p) *
      (∑ d ∈ P.divisors, μ d / (Nat.totient d : ℝ)) -
      LinearSieve.lowerErrSum S D μ ≤ _ at hfinite
  convert hfinite using 1
  ring

/-- Exact signed summation on the given pair family. No main-density term
is discarded, and no product image is substituted for the pair labels. -/
theorem goldbachOrderedPair_lowerRosser_finite
    {N : ℕ} (hEven : Even N) (ε z : ℝ) (Q : ℕ) (T : Finset (ℕ × ℕ))
    (hprimeD : ∀ a ∈ T, ∀ q ∈ (goldbachS1ProdPrimes N z).primeFactors,
      q < Q / (a.1 * a.2) + 1) :
    trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
      (∑ a ∈ T, (1 / (Nat.totient (a.1 * a.2) : ℝ)) *
        (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
          LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z)
            (Q / (a.1 * a.2) + 1) d / (Nat.totient d : ℝ))) -
      (∑ a ∈ T, LinearSieve.lowerErrSum
        (goldbachS3BoundingSieve N hEven ε z (a.1 * a.2))
        (Q / (a.1 * a.2) + 1)
        (LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z)
          (Q / (a.1 * a.2) + 1))) ≤
      ∑ a ∈ T, (literalH (goldbachDifferenceCarrier N ε) N (a.1 * a.2) z : ℝ) := by
  have hs := Finset.sum_le_sum (s := T) (fun a ha =>
    goldbachComposite_lowerRosser_finite hEven ε z (a.1 * a.2)
      (Q / (a.1 * a.2) + 1) (hprimeD a ha))
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using hs

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS3LevelGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS3PaidUpper

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open BombieriVinogradov

#check goldbachS3BoundingSieve
#print axioms goldbachS3BoundingSieve
#check goldbachS3_coprime_of_dvd_prodPrimes
#print axioms goldbachS3_coprime_of_dvd_prodPrimes
#check goldbachS3BoundingSieve_siftedSum_eq
#print axioms goldbachS3BoundingSieve_siftedSum_eq
#check goldbachS3BoundingSieve_multSum_eq_primesInAP
#print axioms goldbachS3BoundingSieve_multSum_eq_primesInAP
#check goldbachS3BoundingSieve_mainSum_eq_totientSum
#print axioms goldbachS3BoundingSieve_mainSum_eq_totientSum
#check goldbachS3BoundingSieve_rem_eq_standardPrimeAPError
#print axioms goldbachS3BoundingSieve_rem_eq_standardPrimeAPError
#check goldbachS3_mod_mem_unitResidues
#print axioms goldbachS3_mod_mem_unitResidues
#check goldbachS3BoundingSieve_abs_rem_le_prefix
#print axioms goldbachS3BoundingSieve_abs_rem_le_prefix
#check goldbachS3_level_eventually
#print axioms goldbachS3_level_eventually
#check goldbachS3_upperErrSum_le_prefixSum
#print axioms goldbachS3_upperErrSum_le_prefixSum
#check goldbachS3Closed_upperRosser_paid
#print axioms goldbachS3Closed_upperRosser_paid

/-- G4: the closed upper endpoint is exactly `N^(1/3)`. -/
example (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 2 / 15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
            trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
              (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
                ((N : ℝ) ^ (1 / 3 : ℝ)),
                (1 / (Nat.totient p : ℝ)) *
                  (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).divisors,
                    LinearSieve.upperRosserWeight
                      (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)))
                      (LiuWeight.panModulusCutoff N B / p + 1) d /
                        (Nat.totient d : ℝ))) +
              C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨B, hB, C, hC, h⟩ := goldbachS3Closed_upperRosser_paid U hU
  refine ⟨B, hB, C, hC, ?_⟩
  intro ε hε hεu
  obtain ⟨N₀, hN₀, hn⟩ := h ε hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  exact hn N hN hEven _
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) le_rfl

/-- G5: specialize the same uniform theorem, without merging repeated primes
from the two different outer sums. -/
example (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 2 / 15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
            trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
              (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
                ((N : ℝ) ^ (3 / 11 : ℝ)),
                (1 / (Nat.totient p : ℝ)) *
                  (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).divisors,
                    LinearSieve.upperRosserWeight
                      (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)))
                      (LiuWeight.panModulusCutoff N B / p + 1) d /
                        (Nat.totient d : ℝ))) +
              C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨B, hB, C, hC, h⟩ := goldbachS3Closed_upperRosser_paid U hU
  refine ⟨B, hB, C, hC, ?_⟩
  intro ε hε hεu
  obtain ⟨N₀, hN₀, hn⟩ := h ε hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  exact hn N hN hEven _
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
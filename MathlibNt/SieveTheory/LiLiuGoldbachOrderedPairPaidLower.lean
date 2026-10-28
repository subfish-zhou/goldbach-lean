import MathlibNt.SieveTheory.LiLiuGoldbachCompositeSieveAP
import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairPrefix
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairLevel
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional


open scoped BigOperators
open Finset Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open BombieriVinogradov

/-- The complete lower Rosser error on the given ordered family is paid once
by the full modulus prefix. Square pairs and the divisor one are retained. -/
theorem goldbachOrderedPair_lowerErrSum_le_prefixSum
    {N : ℕ} (hEven : Even N) {ε z y₁ y₂ : ℝ} (Q : ℕ)
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (T : Finset (ℕ × ℕ))
    (hT : ∀ a ∈ T, a.1 ∈ goldbachClosedPrimes N z y₁ ∧
      a.2 ∈ goldbachClosedPrimes N z y₂ ∧ a.1 ≤ a.2) :
    (∑ a ∈ T, LinearSieve.lowerErrSum
      (goldbachS3BoundingSieve N hEven ε z (a.1 * a.2)) (Q / (a.1 * a.2) + 1)
      (LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z)
        (Q / (a.1 * a.2) + 1))) ≤
      ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
  classical
  have hshape : ∀ a ∈ T, a.1.Prime ∧ a.2.Prime ∧ a.1 ≤ a.2 ∧ z ≤ (a.1 : ℝ) := by
    intro a ha
    obtain ⟨hr, hs, hrs⟩ := hT a ha
    exact ⟨(mem_goldbachClosedPrimes_iff.mp hr).1,
      (mem_goldbachClosedPrimes_iff.mp hs).1, hrs,
      (mem_goldbachClosedPrimes_iff.mp hr).2.2.1⟩
  refine le_trans (Finset.sum_le_sum fun a ha => ?_)
    (goldbachOrderedPair_prefix_doubleSum_le N Q z T hshape)
  change (∑ d ∈ (goldbachS1ProdPrimes N z).divisors.filter
      (fun d => d < Q / (a.1 * a.2) + 1),
    |LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z)
      (Q / (a.1 * a.2) + 1) d| *
    |(goldbachS3BoundingSieve N hEven ε z (a.1 * a.2)).rem d|) ≤ _
  apply Finset.sum_le_sum
  intro d hd
  have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hw := mul_le_mul_of_nonneg_right
    (LinearSieve.abs_lowerRosserWeight_le_one (goldbachS1ProdPrimes N z)
      (Q / (a.1 * a.2) + 1) d)
    (abs_nonneg ((goldbachS3BoundingSieve N hEven ε z (a.1 * a.2)).rem d))
  simp only [one_mul] at hw
  exact hw.trans
    (goldbachCompositeSieve_pair_abs_rem_le_prefix hEven hε hm
      (hT a ha).1 (hT a ha).2.1 hdvd)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

import MathlibNt.SieveTheory.LiLiuGoldbachCompositeSieveAP
import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairPrefix
import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairLowerFinite
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

private theorem PairPaid_endpoint_two_le {N : ℕ} {ε : ℝ}
    (hN : 4 ≤ N) (hε : ε < 2 / 15) : 2 ≤ goldbachS1Endpoint N ε := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 3 ≤ (1 - ε) * (N : ℝ) := by nlinarith
  have hc : 3 ≤ Nat.ceil ((1 - ε) * (N : ℝ)) := by
    exact_mod_cast hx.trans (Nat.le_ceil ((1 - ε) * (N : ℝ)))
  unfold goldbachS1Endpoint
  omega

/-- Actual ordered-pair sifted counts with the unconditional BV error paid.
Constants and the common threshold precede every changing pair family. -/
theorem goldbachOrderedPair_lowerRosser_paid (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 2 / 15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ T : Finset (ℕ × ℕ),
            (∀ a ∈ T,
              a.1 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
              a.2 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
              a.1 ≤ a.2) →
            trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
              (∑ a ∈ T, (1 / (Nat.totient (a.1 * a.2) : ℝ)) *
                (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ)^(4/53 : ℝ))).divisors,
                  LinearSieve.lowerRosserWeight
                    (goldbachS1ProdPrimes N ((N : ℝ)^(4/53 : ℝ)))
                    (LiuWeight.panModulusCutoff N B / (a.1 * a.2) + 1) d /
                    (Nat.totient d : ℝ))) - C * (N : ℝ) / Real.log (N : ℝ)^U ≤
              ∑ a ∈ T, (literalH (goldbachDifferenceCarrier N ε) N (a.1 * a.2)
                ((N : ℝ)^(4/53 : ℝ)) : ℝ) := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov U hU
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hBV.and (goldbachOrderedPair_level_eventually B))
  refine ⟨B, hB, C, hC, ?_⟩
  intro ε hε hεu
  refine ⟨max 4 K, le_max_left _ _, ?_⟩
  intro N hN hEven T hT
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd := hK N ((le_max_right _ _).trans hN)
  have hlevel : ∀ a ∈ T,
      ∀ q ∈ (goldbachS1ProdPrimes N ((N : ℝ)^(4/53 : ℝ))).primeFactors,
        q < LiuWeight.panModulusCutoff N B / (a.1 * a.2) + 1 := by
    intro a ha
    obtain ⟨hr, hs, _⟩ := hT a ha
    have hrp := mem_goldbachClosedPrimes_iff.mp hr
    have hsp := mem_goldbachClosedPrimes_iff.mp hs
    have hprod : ((a.1 * a.2 : ℕ) : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) := by
      calc
        ((a.1 * a.2 : ℕ) : ℝ) = (a.1 : ℝ) * (a.2 : ℝ) := by simp
        _ ≤ (N : ℝ)^(4/33 : ℝ) * (N : ℝ)^(3/11 : ℝ) := by gcongr; exact hrp.2.2.2; exact hsp.2.2.2
        _ = (N : ℝ)^(13/33 : ℝ) := by
          rw [← Real.rpow_add hN0]
          congr 1
          norm_num
    exact (hd.2.2 (a.1 * a.2) (Nat.mul_pos hrp.1.pos hsp.1.pos) hprod).2
  have hf := goldbachOrderedPair_lowerRosser_finite hEven ε ((N : ℝ)^(4/53 : ℝ))
    (LiuWeight.panModulusCutoff N B) T hlevel
  have he := goldbachOrderedPair_lowerErrSum_le_prefixSum hEven
    (LiuWeight.panModulusCutoff N B) hε.le (PairPaid_endpoint_two_le hN4 hεu) T hT
  have hb := hd.1 (by omega)
  exact (sub_le_sub_left (he.trans hb) _).trans hf

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

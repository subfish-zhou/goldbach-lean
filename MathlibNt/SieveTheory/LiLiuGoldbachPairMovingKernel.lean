import MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingCount
import MathlibNt.SieveTheory.LiLiuGoldbachG67PaidLower

open scoped BigOperators
open Finset Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open JurkatRichert1965ChenGammaOneQOne

/-- Actual prime-pair membership supplies both product power bounds. -/
theorem goldbachPair_product_bounds {N r s : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)))
    (hs : s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) :
    0 < r*s ∧ (N : ℝ)^(8/53 : ℝ) ≤ ((r*s : ℕ) : ℝ) ∧
      ((r*s : ℕ) : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrp := mem_goldbachClosedPrimes_iff.mp hr
  have hsp := mem_goldbachClosedPrimes_iff.mp hs
  refine ⟨Nat.mul_pos hrp.1.pos hsp.1.pos, ?_, ?_⟩
  · calc
      (N : ℝ)^(8/53 : ℝ) = (N : ℝ)^(4/53 : ℝ) * (N : ℝ)^(4/53 : ℝ) := by
        rw [← Real.rpow_add hNp]
        congr 1
        norm_num
      _ ≤ (r : ℝ)*(s : ℝ) := by gcongr; exact hrp.2.2.1; exact hsp.2.2.1
      _ = ((r*s : ℕ) : ℝ) := by simp
  · calc
      ((r*s : ℕ) : ℝ) = (r : ℝ)*(s : ℝ) := by simp
      _ ≤ (N : ℝ)^(4/33 : ℝ) * (N : ℝ)^(3/11 : ℝ) := by
        gcongr
        exact hrp.2.2.2
        exact hsp.2.2.2
      _ = (N : ℝ)^(13/33 : ℝ) := by
        rw [← Real.rpow_add hNp]
        congr 1
        norm_num

/-- A nonnegative kernel on the original pair labels at the genuine natural layer. -/
noncomputable def goldbachPairMovingMain (N : ℕ) (hEven : Even N)
    (ε B ρ : ℝ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ a ∈ T,
    let S := goldbachS3BoundingSieve N hEven ε ((N : ℝ)^(4/53 : ℝ)) (a.1*a.2)
    let D := LiuWeight.panModulusCutoff N B / (a.1*a.2) + 1
    S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
      max 0 (jr1965f (Real.log (D : ℝ) / Real.log ((N : ℝ)^(4/53 : ℝ))) - ρ)

/-- Actual moving lower kernels with the complete BV error paid, including
the low-coordinate branch. The threshold precedes epsilon and every pair family. -/
theorem goldbachPairMovingMain_paid (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        ∀ ε : ℝ, 0 ≤ ε → ε < 2/15 → ∀ T : Finset (ℕ × ℕ),
          (∀ a ∈ T,
            a.1 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
            a.2 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
            a.1 ≤ a.2) →
          goldbachPairMovingMain N hEven ε B ρ T -
              C*(N : ℝ)/Real.log (N : ℝ)^U ≤
            ∑ a ∈ T, (literalH (goldbachDifferenceCarrier N ε) N (a.1*a.2)
              ((N : ℝ)^(4/53 : ℝ)) : ℝ) := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov U hU
  refine ⟨B, hB, C, hC, ?_⟩
  intro ρ hρ
  obtain ⟨Nc, hNc, hc⟩ := goldbachComposite_moving_count_lower B ρ hB hρ
  obtain ⟨Nb, hb⟩ := eventually_atTop.mp hBV
  refine ⟨max Nc Nb, by omega, ?_⟩
  intro N hN hEven ε hε hεu T hT
  have hN4 : 4 ≤ N := by omega
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hx : 3 ≤ (1-ε)*(N : ℝ) := by nlinarith
  have hceil : 3 ≤ Nat.ceil ((1-ε)*(N : ℝ)) := by
    exact_mod_cast hx.trans (Nat.le_ceil ((1-ε)*(N : ℝ)))
  have hm : 2 ≤ goldbachS1Endpoint N ε := by unfold goldbachS1Endpoint; omega
  have hf := Finset.sum_le_sum (s := T) (fun a ha =>
    hc N (by omega) hEven ε hεu (a.1*a.2)
      (goldbachPair_product_bounds hN4 (hT a ha).1 (hT a ha).2.1).1
      (goldbachPair_product_bounds hN4 (hT a ha).1 (hT a ha).2.1).2.1
      (goldbachPair_product_bounds hN4 (hT a ha).1 (hT a ha).2.1).2.2)
  rw [Finset.sum_sub_distrib] at hf
  have he := goldbachOrderedPair_lowerErrSum_le_prefixSum hEven
    (LiuWeight.panModulusCutoff N B) hε hm T hT
  have hbound := hb N (by omega) (by omega)
  exact (sub_le_sub_left (he.trans hbound) _).trans hf

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

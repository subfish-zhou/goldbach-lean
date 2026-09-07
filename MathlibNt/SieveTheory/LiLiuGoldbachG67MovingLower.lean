import MathlibNt.SieveTheory.LiLiuGoldbachPairMovingKernel

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The same BV constants pay each original G6 and G7 family. They remain
separate families: their common closed endpoint is counted in each original term. -/
theorem goldbachG67_movingKernel_paid (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 2/15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
          (goldbachPairMovingMain N hEven ε B ρ
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) -
              C * (N : ℝ) / Real.log (N : ℝ)^U ≤
            (goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ)) ∧
          (goldbachPairMovingMain N hEven ε B ρ
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ))) - C * (N : ℝ) / Real.log (N : ℝ)^U ≤
            (goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ)) := by
  obtain ⟨B, hB, C, hC, hp⟩ := goldbachPairMovingMain_paid U hU
  refine ⟨B, hB, C, hC, ?_⟩
  intro ρ hρ ε hε hεu
  obtain ⟨N₀, hN₀, hn⟩ := hp ρ hρ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzc : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hbc : (N : ℝ)^(4/33 : ℝ) ≤ (N : ℝ)^(3/11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h6 := hn N hN hEven ε hε.le hεu
    (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) (by
      intro a ha
      obtain ⟨hs, hr⟩ := mem_goldbachG6Pairs_iff.mp ha
      have hrp := mem_goldbachClosedPrimes_iff.mp hr
      have hsp := mem_goldbachClosedPrimes_iff.mp hs
      exact ⟨mem_goldbachClosedPrimes_iff.mpr
        ⟨hrp.1, hrp.2.1, hrp.2.2.1, hrp.2.2.2.trans hsp.2.2.2⟩,
        mem_goldbachClosedPrimes_iff.mpr
          ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.trans hbc⟩,
        by exact_mod_cast hrp.2.2.2⟩)
  have h7 := hn N hN hEven ε hε.le hεu
    (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
      ((N : ℝ)^(3/11 : ℝ))) (by
      intro a ha
      obtain ⟨hr, hs⟩ := Finset.mem_product.mp ha
      have hrp := mem_goldbachClosedPrimes_iff.mp hr
      have hsp := mem_goldbachClosedPrimes_iff.mp hs
      exact ⟨hr, mem_goldbachClosedPrimes_iff.mpr
        ⟨hsp.1, hsp.2.1, hzc.trans hsp.2.2.1, hsp.2.2.2⟩,
        by exact_mod_cast hrp.2.2.2.trans hsp.2.2.1⟩)
  constructor
  · simpa only [← Int.cast_sum, goldbachG6Pairs_sum_eq] using h6
  · simpa only [← Int.cast_sum, goldbachG7Pairs_sum_eq] using h7

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

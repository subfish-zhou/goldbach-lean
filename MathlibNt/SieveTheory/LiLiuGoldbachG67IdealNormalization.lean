import MathlibNt.SieveTheory.LiLiuGoldbachPairIdealNormalization
import MathlibNt.SieveTheory.LiLiuGoldbachG67MovingLower

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both original closed pair families consume the same scalar and coordinate threshold. -/
theorem goldbachG67_ideal_normalized (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hρK : ρ < 53/(2*Real.exp Real.eulerMascheroniConstant)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        ((53/(2*Real.exp Real.eulerMascheroniConstant)-ρ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) *
          goldbachPairIdealSum N (2*ρ)
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) ≤
          goldbachPairMovingMain N hEven ε B ρ
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)))) ∧
        ((53/(2*Real.exp Real.eulerMascheroniConstant)-ρ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) *
          goldbachPairIdealSum N (2*ρ)
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ))) ≤
          goldbachPairMovingMain N hEven ε B ρ
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ)))) := by
  obtain ⟨ε₀, hε₀, hε₀u, he⟩ := goldbachPair_ideal_sum_normalized B ρ hB hρ hρK
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hn⟩ := he ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzc : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hbc : (N : ℝ)^(4/33 : ℝ) ≤ (N : ℝ)^(3/11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  constructor
  · apply hn N hN hEven
    intro a ha
    obtain ⟨hs, hr⟩ := mem_goldbachG6Pairs_iff.mp ha
    have hrp := mem_goldbachClosedPrimes_iff.mp hr
    have hsp := mem_goldbachClosedPrimes_iff.mp hs
    have hrr : a.1 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) := mem_goldbachClosedPrimes_iff.mpr
      ⟨hrp.1, hrp.2.1, hrp.2.2.1, hrp.2.2.2.trans hsp.2.2.2⟩
    have hss : a.2 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(3/11 : ℝ)) := mem_goldbachClosedPrimes_iff.mpr
      ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.trans hbc⟩
    exact ⟨(goldbachPair_product_bounds hN4 hrr hss).1,
      (goldbachPair_product_bounds hN4 hrr hss).2.2⟩
  · apply hn N hN hEven
    intro a ha
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp ha
    have hsp := mem_goldbachClosedPrimes_iff.mp hs
    have hss : a.2 ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(3/11 : ℝ)) := mem_goldbachClosedPrimes_iff.mpr
      ⟨hsp.1, hsp.2.1, hzc.trans hsp.2.2.1, hsp.2.2.2⟩
    exact ⟨(goldbachPair_product_bounds hN4 hr hss).1,
      (goldbachPair_product_bounds hN4 hr hss).2.2⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

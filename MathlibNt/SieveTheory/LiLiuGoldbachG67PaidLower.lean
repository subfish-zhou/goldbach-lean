import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairPaidLower
import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitial

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open BombieriVinogradov

/-- The original G6 labels, with the smaller selected prime first. -/
noncomputable def goldbachG6Pairs (N : ℕ) (z b : ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachClosedPrimes N z b).sigma (fun s => goldbachClosedPrimes N z (s : ℝ))).image
    (fun a => (a.2, a.1))

/-- The original closed G7 labels; the shared endpoint is not removed. -/
noncomputable def goldbachG7Pairs (N : ℕ) (z b c : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachClosedPrimes N z b) ×ˢ (goldbachClosedPrimes N b c)

theorem mem_goldbachG6Pairs_iff {N : ℕ} {z b : ℝ} {a : ℕ × ℕ} :
    a ∈ goldbachG6Pairs N z b ↔
      a.2 ∈ goldbachClosedPrimes N z b ∧ a.1 ∈ goldbachClosedPrimes N z (a.2 : ℝ) := by
  constructor
  · rintro ha
    obtain ⟨⟨s, r⟩, hsr, heq⟩ := Finset.mem_image.mp ha
    subst a
    exact Finset.mem_sigma.mp hsr
  · rintro ⟨hs, hr⟩
    exact Finset.mem_image.mpr ⟨⟨a.2, a.1⟩, Finset.mem_sigma.mpr ⟨hs, hr⟩, rfl⟩

theorem goldbachG6Pairs_sum_eq (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    (∑ a ∈ goldbachG6Pairs N z b, literalH A N (a.1 * a.2) z) =
      goldbachWeightG6 A N z b := by
  classical
  have hinj : Function.Injective (fun a : (s : ℕ) × ℕ => (a.2, a.1)) := by
    rintro ⟨s, r⟩ ⟨t, q⟩ h
    have hq := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    dsimp at hq ht
    subst q
    subst t
    rfl
  rw [goldbachG6Pairs, Finset.sum_image hinj.injOn,
    goldbachWeightG6, Finset.sum_sigma']

theorem goldbachG7Pairs_sum_eq (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    (∑ a ∈ goldbachG7Pairs N z b c, literalH A N (a.1 * a.2) z) =
      goldbachWeightG7 A N z b c := by
  rw [goldbachG7Pairs, Finset.sum_product, Finset.sum_comm]
  rfl

/-- The actual signed ordinary Rosser main term, not an integral approximation. -/
noncomputable def goldbachPairLowerMain (N : ℕ) (ε B : ℝ) (T : Finset (ℕ × ℕ)) : ℝ :=
  trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
    (∑ a ∈ T, (1 / (Nat.totient (a.1 * a.2) : ℝ)) *
      (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ)^(4/53 : ℝ))).divisors,
        LinearSieve.lowerRosserWeight
          (goldbachS1ProdPrimes N ((N : ℝ)^(4/53 : ℝ)))
          (LiuWeight.panModulusCutoff N B / (a.1 * a.2) + 1) d / (Nat.totient d : ℝ)))

/-- The same BV constants pay each original G6 and G7 family. They remain
separate families: their common closed endpoint is counted in each original term. -/
theorem goldbachG67_lowerRosser_paid (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 2/15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachPairLowerMain N ε B
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) -
              C * (N : ℝ) / Real.log (N : ℝ)^U ≤
            (goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ)) ∧
          (goldbachPairLowerMain N ε B
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ))) - C * (N : ℝ) / Real.log (N : ℝ)^U ≤
            (goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ)) := by
  obtain ⟨B, hB, C, hC, hp⟩ := goldbachOrderedPair_lowerRosser_paid U hU
  refine ⟨B, hB, C, hC, ?_⟩
  intro ε hε hεu
  obtain ⟨N₀, hN₀, hn⟩ := hp ε hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzc : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hbc : (N : ℝ)^(4/33 : ℝ) ≤ (N : ℝ)^(3/11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h6 := hn N hN hEven
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
  have h7 := hn N hN hEven
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
  · simpa only [goldbachPairLowerMain, ← Int.cast_sum, goldbachG6Pairs_sum_eq] using h6
  · simpa only [goldbachPairLowerMain, ← Int.cast_sum, goldbachG7Pairs_sum_eq] using h7

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

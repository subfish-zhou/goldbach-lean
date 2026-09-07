import MathlibNt.SieveTheory.LiLiuGoldbachG11ExceptionBudget
import MathlibNt.SieveTheory.LiLiuGoldbachWeightLowPositivePrefixConsumed

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11RoughTotal (N : ℕ) (ε : ℝ) : ℤ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
    goldbachG11RoughCount N ε v

/-- Replace only the actual G11 term. No other signed term is changed or estimated. -/
noncomputable def goldbachWeightG11RoughRemainder (N : ℕ) (ε : ℝ) : ℤ :=
  goldbachWeightRemainingFour (goldbachDifferenceCarrier N ε) N
    ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) ((N : ℝ)^(3 / 11 : ℝ)) +
  goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
    ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) - goldbachG11RoughTotal N ε

theorem goldbachWeightG11_le_roughTotal_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) ≤
        (goldbachG11RoughTotal N ε : ℝ) + δ *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, he⟩ := goldbachG11_exceptions_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε hε
  have heN := he N hN ε hε
  have hs := (goldbachWeightG11_roughQuotient_sandwich N ε
    ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) hε).2
  have hsR : (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
      ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) ≤
      ((goldbachG11RoughTotal N ε +
        (∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
        (∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) : ℤ) : ℝ) := by
    exact_mod_cast hs
  push_cast at hsR heN
  linarith

/-- The rough G11 count and the low-S5 sifted count both remain literal, unestimated counts. -/
theorem goldbachWeight_g11Rough_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
        (goldbachWeightG11RoughRemainder N ε : ℝ) -
          (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
          (goldbachWeightHighFirstCoefficient ε - δ) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
          4 * (D19 N : ℝ) := by
  obtain ⟨Nb, hNb, hb⟩ := goldbachWeight_lowPositivePrefix_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Ng, _hNg, hg⟩ := goldbachWeightG11_le_roughTotal_normalized (δ / 2) (by positivity)
  refine ⟨max Nb Ng, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hb N ((le_max_left _ _).trans hN) hEven Z hZ hZu
  have hG := hg N ((le_max_right _ _).trans hN) ε hε.le
  unfold goldbachWeightG11RoughRemainder
  push_cast
  nlinarith [hbase, hG]

theorem goldbachWeight_g11Rough_consumed_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightG11RoughRemainder N ε : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              (goldbachWeightHighFirstCoefficient 0 - δ) *
                (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
              4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hb⟩ := goldbachWeight_lowPositivePrefix_consumed_small_epsilon
    (δ / 2) (by positivity)
  obtain ⟨Ng, _hNg, hg⟩ := goldbachWeightG11_le_roughTotal_normalized (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nb, hNb, hbN⟩ := hb ε hε hεlt
  refine ⟨max Nb Ng, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hbN N ((le_max_left _ _).trans hN) hEven Z hZ hZu
  have hG := hg N ((le_max_right _ _).trans hN) ε hε.le
  unfold goldbachWeightG11RoughRemainder
  push_cast
  nlinarith [hbase, hG]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
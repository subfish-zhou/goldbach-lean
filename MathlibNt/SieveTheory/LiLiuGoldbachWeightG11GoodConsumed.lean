import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedTransport

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachWeightG11GoodRemainder (N : ℕ) (ε : ℝ) : ℤ :=
  goldbachWeightG11RoughRemainder N ε + goldbachG11RoughTotal N ε -
    goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ))

theorem goldbachG11RoughTotal_le_goodSwitched_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε →
      (goldbachG11RoughTotal N ε : ℝ) ≤
        (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ))
          ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) + δ *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, he⟩ := goldbachG11_exceptions_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε hε
  have heN := he N hN ε hε
  have hc := (goldbachG11RoughTotal_good_comparison N ε hε).2
  have hcR : (goldbachG11RoughTotal N ε : ℝ) ≤
      (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) +
      ((∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) : ℝ) := by
    exact_mod_cast hc
  have hr0 : (0 : ℤ) ≤ ∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ))
      ((N : ℝ)^(4 / 33 : ℝ)), goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hrR : (0 : ℝ) ≤ ((∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ))
      ((N : ℝ)^(4 / 33 : ℝ)), goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) : ℝ) := by
    exact_mod_cast hr0
  push_cast at heN
  linarith

theorem goldbachWeightG11_le_goodSwitched_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) ≤
      (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) + δ *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨Na, hNa, ha⟩ := goldbachWeightG11_le_roughTotal_normalized (δ / 2) (by positivity)
  obtain ⟨Nb, _hNb, hb⟩ := goldbachG11RoughTotal_le_goodSwitched_normalized (δ / 2) (by positivity)
  refine ⟨max Na Nb, hNa.trans (le_max_left _ _), ?_⟩
  intro N hN ε hε
  have h1 := ha N ((le_max_left _ _).trans hN) ε hε
  have h2 := hb N ((le_max_right _ _).trans hN) ε hε
  linarith

/-- The coprime switched G11 count remains literal; only finite exceptional losses are paid. -/
theorem goldbachWeight_g11GoodSwitched_consumed_eventually
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
        (goldbachWeightG11GoodRemainder N ε : ℝ) -
          (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
          (goldbachWeightHighFirstCoefficient ε - δ) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
          4 * (D19 N : ℝ) := by
  obtain ⟨Nb, hNb, hb⟩ := goldbachWeight_g11Rough_consumed_eventually
    (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Ng, _hNg, hg⟩ := goldbachG11RoughTotal_le_goodSwitched_normalized (δ / 2) (by positivity)
  refine ⟨max Nb Ng, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hb N ((le_max_left _ _).trans hN) hEven Z hZ hZu
  have hG := hg N ((le_max_right _ _).trans hN) ε hε.le
  unfold goldbachWeightG11GoodRemainder
  push_cast
  nlinarith [hbase, hG]

theorem goldbachWeight_g11GoodSwitched_consumed_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ Z : ℝ, 1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
            (goldbachWeightG11GoodRemainder N ε : ℝ) -
              (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ) +
              (goldbachWeightHighFirstCoefficient 0 - δ) *
                (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
              4 * (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, hb⟩ := goldbachWeight_g11Rough_consumed_small_epsilon
    (δ / 2) (by positivity)
  obtain ⟨Ng, _hNg, hg⟩ := goldbachG11RoughTotal_le_goodSwitched_normalized (δ / 2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nb, hNb, hbN⟩ := hb ε hε hεlt
  refine ⟨max Nb Ng, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ hZu
  have hbase := hbN N ((le_max_left _ _).trans hN) hEven Z hZ hZu
  have hG := hg N ((le_max_right _ _).trans hN) ε hε.le
  unfold goldbachWeightG11GoodRemainder
  push_cast
  nlinarith [hbase, hG]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
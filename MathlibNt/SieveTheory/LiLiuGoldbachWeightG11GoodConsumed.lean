import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedTransport

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
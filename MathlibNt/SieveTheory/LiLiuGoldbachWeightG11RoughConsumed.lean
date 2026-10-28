import MathlibNt.SieveTheory.LiLiuGoldbachG11ExceptionBudget
import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixTransport
import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFourCoarse


open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11RoughTotal (N : ℕ) (ε : ℝ) : ℤ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
    goldbachG11RoughCount N ε v


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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
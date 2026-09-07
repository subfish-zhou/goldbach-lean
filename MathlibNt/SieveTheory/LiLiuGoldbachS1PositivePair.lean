import MathlibNt.SieveTheory.LiLiuGoldbachS1AlphaNormalizedLower
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaNormalizedLower

open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The two actual S1 positive terms in the signed weight, with their genuine
multiplicities and a single arbitrary error budget. This is not a Base bound. -/
theorem goldbachS1_positivePair_normalized_lower
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ((1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
          ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
            (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) - δ) *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
      ((3 * goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) +
        goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 33 : ℝ)) : ℤ) : ℝ) := by
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨Na, hNa, ha⟩ := goldbachS1_alphaFourFiftyThree_normalized_lower
    (δ / 4) ε hδ4 hε hεu
  obtain ⟨Nb, _hNb, hb⟩ := goldbachS1_beta_normalized_lower (δ / 4) hδ4 ε hε hεu
  refine ⟨max Na Nb, hNa.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNa' : Na ≤ N := (le_max_left _ _).trans hN
  have hNb' : Nb ≤ N := (le_max_right _ _).trans hN
  have hα := ha N hNa' hEven
  have hβ := hb N hNb' hEven
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hα (by norm_num : (0 : ℝ) ≤ 3)) hβ
  have hshape :
      ((1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
          ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
            (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) - δ) *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) =
      3 * ((((53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
          dimensionOneLowerLinearSieveFactor 6) - δ / 4) *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2)) +
      (((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
          dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - δ / 4) *
        SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by ring
  rw [hshape]
  norm_cast at hsum ⊢

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
import MathlibNt.SieveTheory.LiLiuGoldbachG12IntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegralBridge
import MathlibNt.SieveTheory.LiLiuGoldbachUniformCrossIntegralLedger

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG12UniformClosedConstant : ℝ :=
  8*(564383/1000000 : ℝ)*
    (Real.log (9/4 : ℝ)*((43/2 : ℝ)*Real.log (53/33 : ℝ)-10))

/-- Exact closed cross expression, retaining the strongest already proved C67. -/
theorem goldbachWeight_closedCrossIntegralLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
          goldbachB9PaperSplitIntegral - 10385101/100000000 -
          goldbachG12UniformClosedConstant - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  simpa only [goldbachG12UniformClosedConstant, goldbachG12PrimeIntegral_one_closed] using
    goldbachWeight_uniformCrossIntegralLedger δ hδ

/-- An auxiliary elementary lower ledger, not a numerical positivity assertion.
The preceding theorem continues to retain the larger actual JR constant. -/
theorem goldbachWeight_elementaryIntegralLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (4*G67ElementaryIntegral.elementaryIntegral + (124341093/200000000 : ℝ) -
          goldbachB9PaperSplitIntegral - 10385101/100000000 -
          goldbachG12UniformClosedConstant - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hh⟩ := goldbachWeight_closedCrossIntegralLedger δ hδ
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨N₀,hN₀,hbound⟩ := hh ε hε hεlt
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  have h := hbound N hN hEven
  have hm : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hp := mul_le_mul_of_nonneg_right G67ElementaryIntegral.actual_constant_lower hm
  linarith only [h,hp]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

import MathlibNt.SieveTheory.LiLiuGoldbachSharpCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The remaining fixed scalar margin, with a proved elementary lower bound for C67. -/
def goldbachSharpElementaryMargin : ℝ :=
  4*G67SumCoordinate.piecewiseIntegral + (124341093/200000000 : ℝ) -
    goldbachB9PaperSplitIntegral - 10385101/100000000 - goldbachG12SharpIntegralConstant

/-- Actual D19 ledger with every integral on fixed, explicitly known intervals. -/
theorem goldbachWeight_sharpPiecewiseLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachSharpElementaryMargin-δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ε₀,he,heu,h⟩ := goldbachWeight_sharpCrossIntegralLedger δ hδ
  refine ⟨ε₀,he,heu,?_⟩
  intro ε hε hεu
  obtain ⟨K,hK,hk⟩ := h ε hε hεu
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hi := G67SumCoordinate.actual_constant_lower_piecewise
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _)) (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hi hs
  have hn := hk N hN hEven
  unfold goldbachSharpElementaryMargin
  nlinarith only [hb,hn]

/-- Conditional proof exit only: the numerical scalar positivity is NOT supplied here. -/
theorem eventually_onePlusOneNine_of_sharp_margin_pos
    (hpos : 0 < goldbachSharpElementaryMargin) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^10 ≤ q^9 := by
  obtain ⟨ε₀,he,_,hl⟩ := goldbachWeight_sharpPiecewiseLedger
    (goldbachSharpElementaryMargin/2) (half_pos hpos)
  obtain ⟨K,hK,hk⟩ := hl (ε₀/2) (half_pos he) (half_lt_self he)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 < SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N) hn) (sq_pos_of_pos hlN)
  have hp := (mul_pos (by linarith : 0 < goldbachSharpElementaryMargin-goldbachSharpElementaryMargin/2)
    hscale).trans_le (hk N hN hEven)
  apply (D19_pos_iff N).mp
  exact_mod_cast (show (0 : ℝ) < (D19 N : ℝ) by linarith only [hp])

/-- Three explicit scalar bounds suffice; none of the three bounds is asserted here. -/
theorem sharp_margin_lower_of_integral_bounds
    (h67 : (54233/10000 : ℝ) ≤ 4*G67SumCoordinate.piecewiseIntegral)
    (h9 : goldbachB9PaperSplitIntegral ≤ (527231/100000 : ℝ))
    (h12 : goldbachG12SharpIntegralConstant ≤ (66821/100000 : ℝ)) :
    (1/2000 : ℝ) ≤ goldbachSharpElementaryMargin := by
  unfold goldbachSharpElementaryMargin
  linarith only [h67,h9,h12]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

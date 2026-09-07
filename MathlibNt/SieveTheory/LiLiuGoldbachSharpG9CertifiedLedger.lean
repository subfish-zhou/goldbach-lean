import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticScalar
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual D19 ledger now consumes the certified G9 constant. -/
theorem goldbachWeight_sharpG9CertifiedLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
          527231/100000 - 10385101/100000000 - goldbachG12SharpIntegralConstant-δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ε₀,he,heu,h⟩ := goldbachWeight_sharpCrossIntegralLedger δ hδ
  refine ⟨ε₀,he,heu,?_⟩
  intro ε hε hεu
  obtain ⟨K,hK,hk⟩ := h ε hε hεu
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right G9Analytic.actual_le_target hs
  have hn := hk N hN hEven
  nlinarith only [hb,hn]

/-- Only the G67 and G12 scalar bounds remain as premises here. -/
theorem sharp_margin_lower_of_two_integral_bounds
    (h67 : (54233/10000 : ℝ) ≤ 4*G67SumCoordinate.piecewiseIntegral)
    (h12 : goldbachG12SharpIntegralConstant ≤ (66821/100000 : ℝ)) :
    (1/2000 : ℝ) ≤ goldbachSharpElementaryMargin :=
  sharp_margin_lower_of_integral_bounds h67 G9Analytic.actual_le_target h12

/-- A conditional exit in the paper's literal real-exponent syntax.
The two scalar premises are deliberately explicit and are not proved here. -/
theorem eventually_onePlusOneNine_source_of_two_integral_bounds
    (h67 : (54233/10000 : ℝ) ≤ 4*G67SumCoordinate.piecewiseIntegral)
    (h12 : goldbachG12SharpIntegralConstant ≤ (66821/100000 : ℝ)) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  have hm := sharp_margin_lower_of_two_integral_bounds h67 h12
  obtain ⟨K,hK,h⟩ := eventually_onePlusOneNine_of_sharp_margin_pos (by linarith)
  refine ⟨K,hK,?_⟩
  intro N hN he
  obtain ⟨p,r,q,hp,hpp,hr,hq,hn,hh⟩ := h N hN he
  exact ⟨p,r,q,hp,hpp,hr,hq,hn,(oneNine_power_iff_source_exponent r q).mp hh⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

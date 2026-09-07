import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBridge
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredEndpoint
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationScalar
import MathlibNt.SieveTheory.LiLiuGoldbachSharpG9CertifiedLedger

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both independently proved halves use the same frozen polynomial and loss. -/
theorem goldbachG67_piecewise_lower_certified :
    (54233/10000 : ℝ) ≤ 4*G67SumCoordinate.piecewiseIntegral := by
  have h := G67CenteredEvaluation.centered_endpoint_bound.trans
    G67CenteredEnvelope.polynomialIntegral_sub_errorBudget_le_piecewiseIntegral
  linarith only [h]

theorem goldbachG67IntegralConstant_lower_certified :
    (54233/10000 : ℝ) ≤ goldbachG67IntegralConstant :=
  goldbachG67_piecewise_lower_certified.trans G67SumCoordinate.actual_constant_lower_piecewise

/-- Exact retained lower bound for the margin; all three integral estimates are supplied. -/
theorem goldbachSharpElementaryMargin_lower_certified :
    (126891/200000000 : ℝ) ≤ goldbachSharpElementaryMargin := by
  have h67 := goldbachG67_piecewise_lower_certified
  have h9 := G9Analytic.actual_le_target
  have h12 := G12AnalyticCertificate.actual_le_target
  unfold goldbachSharpElementaryMargin
  linarith only [h67,h9,h12]

theorem goldbachSharpElementaryMargin_pos : 0 < goldbachSharpElementaryMargin :=
  lt_of_lt_of_le (by norm_num) goldbachSharpElementaryMargin_lower_certified

/-- Quantitative lower bounds below the retained limit, with the coefficient fixed
before the common natural cutoff. The normalization is the Liu singular series. -/
theorem goldbach_D19_lower_of_coefficient_lt (κ : ℝ)
    (hκ : κ < (126891/800000000 : ℝ)) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      κ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        (D19 N : ℝ) := by
  let δ : ℝ := (126891/200000000 : ℝ)-4*κ
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hκ]
  obtain ⟨ε₀,he,_,hl⟩ := goldbachWeight_sharpPiecewiseLedger δ hδ
  obtain ⟨K,hK,hk⟩ := hl (ε₀/2) (half_pos he) (half_lt_self he)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachSharpElementaryMargin_lower_certified δ) hs
  have hn := hk N hN hEven
  dsimp [δ] at hb hn
  nlinarith only [hb,hn]

/-- Unconditional 1+1.9 in exact natural-power syntax. -/
theorem goldbach_onePlusOneNine_nat_unconditional :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^10 ≤ q^9 :=
  eventually_onePlusOneNine_of_sharp_margin_pos goldbachSharpElementaryMargin_pos

/-- Unconditional 1+1.9 in the source's real-exponent syntax.
No integral-bound or positivity premises remain. -/
theorem goldbach_onePlusOneNine_unconditional :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  obtain ⟨K,hK,h⟩ := goldbach_onePlusOneNine_nat_unconditional
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  obtain ⟨p,r,q,hp,hpp,hr,hq,hn,hh⟩ := h N hN hEven
  exact ⟨p,r,q,hp,hpp,hr,hq,hn,(oneNine_power_iff_source_exponent r q).mp hh⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

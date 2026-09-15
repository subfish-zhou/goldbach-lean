import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedRectangles

namespace Wu2008DoubleSieve.SecondFunctionalSignedCore
open Set MeasureTheory MotherPair SecondFunctionalPositive SecondFunctionalParameters
open FourthRowPhiOmega2
open scoped Interval

/-- The actual lower improvement, with its original positive weight. -/
noncomputable def lowerGain (δ a b : ℝ) : ℝ :=
  ∫ u in (1-1/a)..(1-1/b), wuImprovementLimit false δ (b*u)/(u*(1-u))

/-- The logarithmic classical summand and actual gain are separately integrable. -/
theorem J_split {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : 3 ≤ b) (hb5 : b ≤ 5)
    (hr : 2 ≤ b-b/a) :
    J δ a b = fourthRowClassicalJ a b + lowerGain δ a b := by
  rw [J_eq_log ha hab hb5 hr]
  simp only [add_div]
  exact intervalIntegral.integral_add
    (firstFunctionalGain_log_intervalIntegrable ha hab hb hb5 hr)
    (firstFunctionalGain_limit_intervalIntegrable hδ hδhi ha hab hb hb5)

/-- Literal residual: two upper point gains and three lower gain integrals. -/
noncomputable def actualGainRemainder (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
    lowerGain δ p.s p.S + lowerGain δ p.kappa2 p.S + lowerGain δ p.kappa3 p.S)/5

/-- Signed core with the original directed L(kappa2) and fixed delta loss. -/
noncomputable def D (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  fourthRowClassicalJ p.s p.S + fourthRowClassicalJ p.kappa3 p.kappa1 -
    2*fourthRowClassicalL p.S - 2*fourthRowClassicalL p.kappa1 -
    fourthRowClassicalL p.kappa2 - (2/(1-2*δ))*
      (Omega3ElementaryFeedback.omegaCost p + SecondFunctionalFourSevenths.elementaryCap p)

theorem original_log_domains (i : Fin 4) :
    3 ≤ (parameters i).kappa1 ∧
    2 ≤ (parameters i).S - (parameters i).S/(parameters i).s ∧
    2 ≤ (parameters i).S - (parameters i).S/(parameters i).kappa2 ∧
    2 ≤ (parameters i).S - (parameters i).S/(parameters i).kappa3 := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [row1, row2, row3, row4]

/-- All geometry and both summand integrabilities are discharged internally. -/
theorem original_source_eq (i : Fin 4) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Omega3ElementaryFeedback.source (parameters i) δ =
      D (parameters i) δ/5 + actualGainRemainder (parameters i) δ := by
  have hp := parameters_analytic i
  have hg := original_log_domains i
  have he := hp.mother.s_le_kappa3
  have hc := hp.mother.kappa3_lt_kappa2.le
  have hb := hp.mother.kappa2_lt_kappa1.le
  have hS := hp.mother.kappa1_le_S
  have hδhalf : δ < 1/2 := by linarith
  have hsS := he.trans (hc.trans (hb.trans hS))
  have h2S := hb.trans hS
  have h3S := hc.trans h2S
  have hjs := J_split hδ hδhalf hp.two_lt_s.le hsS hp.three_le_S hp.S_le_five hg.2.1
  have hj2 := J_split hδ hδhalf (hp.two_lt_s.le.trans (he.trans hc)) h2S
    hp.three_le_S hp.S_le_five hg.2.2.1
  have hj3 := J_split hδ hδhalf (hp.two_lt_s.le.trans he) h3S
    hp.three_le_S hp.S_le_five hg.2.2.2
  have hclassic := SecondFunctionalClassicalAlgebra.coefficient_eq hp.two_lt_s.le
    hp.s_le_three hg.1 hS hp.S_le_five (hp.two_lt_s.trans_le (he.trans hc)) h2S
    (hp.two_lt_s.trans_le he) (hc.trans hb)
  unfold Omega3ElementaryFeedback.source Omega3ElementaryFeedback.cost
  rw [hjs, hj2, hj3, original_classical_eq_triangles]
  unfold D actualGainRemainder
  linarith only [hclassic]

/-- Nonnegativity comes from the actual H/h producers, not a sign hypothesis. -/
theorem original_remainder_nonneg (i : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    0 ≤ actualGainRemainder (parameters i) δ := by
  have hp := parameters_analytic i
  have he := hp.mother.s_le_kappa3
  have hc := hp.mother.kappa3_lt_kappa2.le
  have hb := hp.mother.kappa2_lt_kappa1.le
  have hS := hp.mother.kappa1_le_S
  have hδhalf : δ < 1/2 := by linarith
  have huS := wuImprovementLimit_nonneg true hδ hδhalf
    (show 1 ≤ (parameters i).S by linarith [hp.three_le_S]) hp.mother.S_le_ten
  have huB := wuImprovementLimit_nonneg true hδ hδhalf
    (show 1 ≤ (parameters i).kappa1 by linarith [(original_log_domains i).1])
    (hS.trans hp.mother.S_le_ten)
  have hs := firstFunctionalGain_integral_nonneg hδ hδhalf hp.two_lt_s.le
    (he.trans (hc.trans (hb.trans hS))) hp.three_le_S hp.S_le_five
  have h2 := firstFunctionalGain_integral_nonneg hδ hδhalf
    (hp.two_lt_s.le.trans (he.trans hc)) (hb.trans hS) hp.three_le_S hp.S_le_five
  have h3 := firstFunctionalGain_integral_nonneg hδ hδhalf
    (hp.two_lt_s.le.trans he) (hc.trans (hb.trans hS)) hp.three_le_S hp.S_le_five
  unfold actualGainRemainder lowerGain
  positivity

end Wu2008DoubleSieve.SecondFunctionalSignedCore

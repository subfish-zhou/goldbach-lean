import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackLog

/-! Public literal consumers and all four parameter-row regressions. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real MeasureTheory SecondFunctionalParameters
open scoped Classical Topology Interval

theorem feedback_log_domain {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {v : ℝ} (hv : v ∈ Icc 1 3)
    (hLU : feedbackLower p j v < feedbackUpper p j v) :
    0 < feedbackLower p j v ∧ 0 < feedbackUpper p j v ∧
    0 < feedbackPole p j v-feedbackLower p j v ∧
    0 < feedbackPole p j v-feedbackUpper p j v ∧
    0 < feedbackUpper p j v * (feedbackPole p j v-feedbackLower p j v) /
      (feedbackLower p j v * (feedbackPole p j v-feedbackUpper p j v)) := by
  have hL := feedback_pole_geometry h j hv ⟨le_rfl,hLU.le⟩
  have hU := feedback_pole_geometry h j hv ⟨hLU.le,le_rfl⟩
  exact ⟨hL.1,hU.1,sub_pos.mpr hL.2,sub_pos.mpr hU.2,
    div_pos (mul_pos hU.1 (sub_pos.mpr hL.2)) (mul_pos hL.1 (sub_pos.mpr hU.2))⟩

theorem feedback_log_actual_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * feedbackLogKernel p j v)
      volume 1 3 := by
  have hi := feedback_actual_integrable h j hδ hδhi
  simpa only [feedback_kernel_log h j] using hi

/-- Literal original nested integral, including both legal insertion gates. -/
theorem feedback_literal_identity {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        if 2*u ≤ 1 ∧ u+2*t ≤ 1 then
          wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u)) else 0) =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel p j v :=
  by
    convert! gainIntegral_feedbackLog h j hδ hδhi using 1
    unfold gainIntegral
    apply intervalIntegral.integral_congr
    intro t _
    apply intervalIntegral.integral_congr
    intro u _
    by_cases hl : 2*u ≤ 1 ∧ u+2*t ≤ 1 <;> simp [gainLiteral,gamma5GainLegal,hl]

theorem feedback_fullH_identity {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u))) =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel p j v := by
  rw [← fullH_gainIntegral_uncut h j hj]
  exact gainIntegral_feedbackLog h.toAnalyticParameters j hδ hδhi

theorem row1_feedback (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral row1 j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel row1 j v :=
  gainIntegral_feedbackLog row1_fullH.toAnalyticParameters j hδ hδhi

theorem row2_feedback (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral row2 j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel row2 j v :=
  gainIntegral_feedbackLog row2_fullH.toAnalyticParameters j hδ hδhi

theorem row3_feedback (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral row3 j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel row3 j v :=
  gainIntegral_feedbackLog row3_fullH.toAnalyticParameters j hδ hδhi

theorem row4_feedback (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral row4 j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel row4 j v :=
  gainIntegral_feedbackLog row4_fullH.toAnalyticParameters j hδ hδhi

end Wu2008DoubleSieve.MotherPair

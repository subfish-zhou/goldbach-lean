import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackLog

/-! Public literal consumers and all four parameter-row regressions. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real MeasureTheory SecondFunctionalParameters
open scoped Classical Topology Interval


theorem feedback_log_actual_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * feedbackLogKernel p j v)
      volume 1 3 := by
  have hi := feedback_actual_integrable h j hδ hδhi
  simpa only [feedback_kernel_log h j] using hi


theorem feedback_fullH_identity {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u))) =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel p j v := by
  rw [← fullH_gainIntegral_uncut h j hj]
  exact gainIntegral_feedbackLog h.toAnalyticParameters j hδ hδhi





end Wu2008DoubleSieve.MotherPair

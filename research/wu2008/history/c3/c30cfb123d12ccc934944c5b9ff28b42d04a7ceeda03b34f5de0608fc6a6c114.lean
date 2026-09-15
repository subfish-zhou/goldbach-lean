import MathlibNt.Wu2008DoubleSieve.FirstFeedbackCross
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel

/-!
# The actual cross bound with the weight in Lemma 6.1 (6.3)

Source: author TeX lines 2594--2608. Only the integral primitive, not the
actual lower or upper gain, is asserted to be continuous.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

theorem firstFeedbackWeighted_parameters {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hac : 2 ≤ a * c) :
    0 < c ∧ a * c ≤ b * c ∧ b * c < c := by
  have hc : 0 < c := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)
    linarith
  exact ⟨hc, mul_le_mul_of_nonneg_right hab hc.le, by nlinarith⟩

theorem wuImprovementLimit_firstFeedback_weighted_intervalIntegrable
    {δ a b c : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun v =>
      wuImprovementLimit false δ (c * v) / (v * (1 - v))) volume a b := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  exact firstFeedbackWeighted_intervalIntegrable ha hab hb hp.1.ne'
    (wuImprovementLimit_intervalIntegrable false hδ (by linarith : δ < 1 / 2)
      (by linarith) hp.2.1 (by linarith))

theorem wuImprovementLimit_firstFeedback_weighted_nested_integrable
    {δ a b c : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun u =>
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) *
        firstFeedbackWeightedKernel c u) volume (a * c) (b * c) := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  have hsub : uIcc (a * c) (b * c) ⊆ Icc 2 4 := by
    rw [uIcc_of_le hp.2.1]
    intro u hu
    exact ⟨hac.trans hu.1, hu.2.trans hbc⟩
  exact ((continuousOn_const.add
    ((firstFeedback_tail_continuous hδ hδhi).mono hsub)).mul
    (firstFeedbackWeightedKernel_continuousOn (by linarith) hp.2.1 hp.2.2)).intervalIntegrable

/-- The author's exact substitution followed by the actual Wu08 (3.8)
comparison; the constant remains `h_delta(4)`. -/
theorem wuImprovementLimit_firstFeedback_weighted_nested
    {δ a b c : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    (∫ u in (a * c)..(b * c),
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) *
        firstFeedbackWeightedKernel c u) ≤
      ∫ v in a..b, wuImprovementLimit false δ (c * v) / (v * (1 - v)) := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  have hi := (wuImprovementLimit_intervalIntegrable false hδ
    (by linarith : δ < 1 / 2) (by linarith : 1 ≤ a * c) hp.2.1
    (by linarith : b * c ≤ 10)).mul_continuousOn
    (firstFeedbackWeightedKernel_continuousOn (by linarith) hp.2.1 hp.2.2)
  rw [firstFeedbackWeighted_substitution _ hp.1.ne']
  apply intervalIntegral.integral_mono_on hp.2.1
    (wuImprovementLimit_firstFeedback_weighted_nested_integrable
      hδ hδhi ha hab hb hac hbc) hi
  intro u hu
  exact mul_le_mul_of_nonneg_right
    (wuImprovementLimit_firstFeedback_lower_tail hδ hδhi
      (hac.trans hu.1) (hu.2.trans hbc))
    (firstFeedbackWeightedKernel_nonneg (by linarith [hu.1]) (hu.2.trans_lt hp.2.2))

end Wu2008DoubleSieve

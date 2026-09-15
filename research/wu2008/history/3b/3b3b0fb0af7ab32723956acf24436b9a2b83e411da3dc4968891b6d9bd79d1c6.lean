import MathlibNt.Wu2008DoubleSieve.TableFeedbackRows
import MathlibNt.Wu2008DoubleSieve.PositiveGainActual

/-!
# Actual positive seed to the feedback bound at three

The accepted positive seed is used only on its proved interval.
The remaining part of the actual feedback integral is nonnegative.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem tableFeedback_seed_to_three {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (1 / 5000 : ℝ) * (∫ x in (1 : ℝ)..(29 / 10), firstFeedbackXi x 3 3) ≤
      wuImprovementLimit true δ 3 := by
  have hK := firstFeedbackXi_intervalIntegrable (s := 3) (t := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hHK := firstFeedbackXi_gain_intervalIntegrable true hδ (by linarith)
    (s := 3) (t := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hleft : uIcc (1 : ℝ) (29 / 10) ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 29 / 10),
      uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hright : uIcc (29 / 10 : ℝ) 3 ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le (by norm_num : (29 / 10 : ℝ) ≤ 3),
      uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hseed :
      (1 / 5000 : ℝ) * (∫ x in (1 : ℝ)..(29 / 10), firstFeedbackXi x 3 3) ≤
        ∫ x in (1 : ℝ)..(29 / 10), wuImprovementLimit true δ x * firstFeedbackXi x 3 3 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 29 / 10)
      ((hK.mono_set hleft).const_mul _) (hHK.mono_set hleft)
    intro x hx
    exact mul_le_mul_of_nonneg_right (positiveGain_actual_upper_range hδ hδhi hx.1 hx.2)
      (firstFeedbackXi_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨hx.1, by linarith [hx.2]⟩)
  have htail : 0 ≤ ∫ x in (29 / 10 : ℝ)..3,
      wuImprovementLimit true δ x * firstFeedbackXi x 3 3 := by
    apply intervalIntegral.integral_nonneg (by norm_num : (29 / 10 : ℝ) ≤ 3)
    intro x hx
    exact mul_nonneg (wuImprovementLimit_nonneg true hδ (by linarith)
      (by linarith [hx.1]) (by linarith [hx.2]))
      (firstFeedbackXi_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨by linarith [hx.1], hx.2⟩)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hHK.mono_set hleft) (hHK.mono_set hright)
  have hfeedback := wuImprovementLimit_firstFeedback_three hδ hδhi
  linarith

end Wu2008DoubleSieve

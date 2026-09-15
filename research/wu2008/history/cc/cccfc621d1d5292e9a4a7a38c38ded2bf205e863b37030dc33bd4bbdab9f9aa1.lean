import MathlibNt.Wu2008DoubleSieve.FirstFeedbackCross
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrated actual feedback before exchanging order

Wu04, TeX lines 2572--2591. Both uses of Proposition 2 have already
been proved for the actual gains. This module integrates their comparison
on `[3,5]`; the only continuous functions used are integral primitives.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem firstFeedback_nested_continuous {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ContinuousOn (fun v => ∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) (Icc 3 5) := by
  have hi := firstFeedback_nested_intervalIntegrable hδ hδhi
    (v := 3) (by norm_num) (by norm_num)
  norm_num at hi
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (4 : ℝ) ∈ uIcc 2 4 by norm_num)
  rw [uIcc_of_le (show (2 : ℝ) ≤ 4 by norm_num)] at hc
  have hn := hc.neg.congr (fun y _ => intervalIntegral.integral_symm 4 y)
  exact hn.comp (continuous_id.sub continuous_const).continuousOn
    (fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩)

theorem firstFeedback_iterated_intervalIntegrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    IntervalIntegrable (fun v => (∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) / v)
      volume 3 5 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (3 : ℝ) ≤ 5)
  apply (firstFeedback_nested_continuous hδ hδhi).div continuousOn_id
  intro v hv
  change v ≠ 0
  linarith [hv.1]

theorem wuImprovementLimit_firstFeedback_iterated {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (∫ v in (3 : ℝ)..5, (∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) / v) ≤
      wuImprovementLimit false δ 4 := by
  apply le_trans _ (wuImprovementLimit_firstFeedback_hfour hδ hδhi)
  exact intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 5)
    (firstFeedback_iterated_intervalIntegrable hδ hδhi)
    (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith : δ < 1 / 2)
      (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) ≤ 5) (by norm_num))
    (fun v hv => div_le_div_of_nonneg_right
      (wuImprovementLimit_firstFeedback_nested hδ hδhi hv.1 hv.2)
      (by linarith [hv.1] : 0 ≤ v))

theorem firstFeedback_nested_split {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    (∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) =
    wuImprovementLimit false δ 4 * log (4 / (v - 1)) +
      ∫ u in (v - 1)..4,
        (∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u := by
  have hsub : uIcc (v - 1) 4 ⊆ Icc 2 4 := by
    rw [uIcc_of_le (by linarith : v - 1 ≤ 4)]
    exact fun u hu => ⟨by linarith [hu.1], hu.2⟩
  have hc : ContinuousOn (fun u : ℝ => 1 / u) (uIcc (v - 1) 4) := by
    apply continuousOn_const.div continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [(hsub hu).1]
  have hi0 : IntervalIntegrable (fun u => wuImprovementLimit false δ 4 / u)
      volume (v - 1) 4 := by
    simpa only [mul_one_div] using hc.intervalIntegrable.const_mul
      (wuImprovementLimit false δ 4)
  have hi1 : IntervalIntegrable (fun u =>
      (∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u)
      volume (v - 1) 4 := by
    apply (((firstFeedback_tail_continuous hδ hδhi).mono hsub).div
      continuousOn_id ?_).intervalIntegrable
    intro u hu
    change u ≠ 0
    linarith [(hsub hu).1]
  simp_rw [add_div]
  rw [intervalIntegral.integral_add hi0 hi1]
  congr 1
  rw [show (fun u : ℝ => wuImprovementLimit false δ 4 / u) =
    (fun u => wuImprovementLimit false δ 4 * (1 / u)) by
      ext u; ring]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_of_pos (by linarith : 0 < v - 1) (by norm_num : (0 : ℝ) < 4)]

end Wu2008DoubleSieve

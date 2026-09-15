import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower

/-!
# The actual cross inputs to Wu04 Lemma 6.1

Author TeX lines 2572--2591: the first line of (6.4) and the subsequent
`h(4)` comparison. All gains here are the accepted fixed-delta limits.
Continuity is used only for an integral primitive, not for either gain.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem firstFeedback_tail_continuous {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ContinuousOn (fun u => ∫ x in (u - 1)..3,
      wuImprovementLimit true δ x / x) (Icc 2 4) := by
  have hi := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (3 : ℝ) ∈ uIcc 1 3 by norm_num)
  have hn : ContinuousOn (fun y => ∫ x in y..3,
      wuImprovementLimit true δ x / x) (Icc 1 3) := by
    rw [uIcc_of_le (show (1 : ℝ) ≤ 3 by norm_num)] at hc
    exact hc.neg.congr fun y _ => intervalIntegral.integral_symm 3 y
  exact hn.comp (continuous_id.sub continuous_const).continuousOn
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)

theorem firstFeedback_nested_intervalIntegrable {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    IntervalIntegrable (fun u =>
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u)
      volume (v - 1) 4 := by
  have hsub : uIcc (v - 1) 4 ⊆ Icc 2 4 := by
    rw [uIcc_of_le (by linarith : v - 1 ≤ 4)]
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  apply ((continuousOn_const.add
    ((firstFeedback_tail_continuous hδ hδhi).mono hsub)).div continuousOn_id ?_).intervalIntegrable
  intro u hu
  have := (hsub hu).1
  change u ≠ 0
  linarith

theorem wuImprovementLimit_firstFeedback_lower_tail {δ u : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    wuImprovementLimit false δ 4 +
      (∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) ≤
    wuImprovementLimit false δ u := by
  convert (wu08_38 hδ hδhi hu hu4 (by norm_num : (4 : ℝ) ≤ 10)).1 using 1
  norm_num

/-- The first two comparisons of the author's (6.4), including `v = 5`. -/
theorem wuImprovementLimit_firstFeedback_nested {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    (∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) ≤
    wuImprovementLimit true δ v := by
  have hi := wuImprovementLimit_div_intervalIntegrable false hδ
    (by linarith : δ < 1 / 2) (a := v - 1) (b := 4)
    (by linarith) (by linarith) (by norm_num)
  have hle := intervalIntegral.integral_mono_on (by linarith : v - 1 ≤ 4)
    (firstFeedback_nested_intervalIntegrable hδ hδhi hv hv5) hi
    (fun u hu => div_le_div_of_nonneg_right
      (wuImprovementLimit_firstFeedback_lower_tail hδ hδhi
        (by linarith [hu.1]) hu.2) (by linarith [hu.1] : 0 ≤ u))
  have hcross := (wu08_38 hδ hδhi (by linarith : 2 ≤ v)
    hv5 (by norm_num : (5 : ℝ) ≤ 10)).2
  have hnon := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1 / 2)
    (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ) ≤ 10)
  norm_num at hcross
  linarith

/-- The scalar feedback is closed at `h_delta(4)`, not a free constant. -/
theorem wuImprovementLimit_firstFeedback_hfour {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (∫ v in (3 : ℝ)..5, wuImprovementLimit true δ v / v) ≤
      wuImprovementLimit false δ 4 := by
  have hcross := (wu08_38 hδ hδhi (s := 4) (t := 6)
    (by norm_num) (by norm_num) (by norm_num)).1
  have hnon := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1 / 2)
    (by norm_num : (1 : ℝ) ≤ 6) (by norm_num : (6 : ℝ) ≤ 10)
  norm_num at hcross
  linarith

end Wu2008DoubleSieve

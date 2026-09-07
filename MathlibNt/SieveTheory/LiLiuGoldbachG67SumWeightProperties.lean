import MathlibNt.SieveTheory.LiLiuGoldbachG67SumFubini

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace G67SumCoordinate

/-- Continuity of the closed-form density, including both vanishing endpoints. -/
theorem weight_continuousOn {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousOn (weight a b c d) (Icc (a+c) (b+d)) := by
  have hL : Continuous (lower a d) := continuous_const.max (continuous_id.sub continuous_const)
  have hU : Continuous (upper b c) := continuous_const.min (continuous_id.sub continuous_const)
  have hN := hU.mul (continuous_id.sub hL)
  have hD := hL.mul (continuous_id.sub hU)
  have hpos : ∀ s ∈ Icc (a+c) (b+d),
      0 < upper b c s * (s-lower a d s) ∧
        0 < lower a d s * (s-upper b c s) := by
    intro s hs
    have h := fiber_bounds ha hc hab hcd hs
    constructor
    · exact mul_pos (h.1.trans_le h.2.1) (by linarith [h.2.1, h.2.2])
    · exact mul_pos h.1 h.2.2
  exact ((hN.continuousOn.div hD.continuousOn (fun s hs => (hpos s hs).2.ne')).log
    (fun s hs => (div_pos (hpos s hs).1 (hpos s hs).2).ne')).div
      continuousOn_id (fun s hs => (show 0 < s by linarith [hs.1]).ne')

/-- Closed-form early branch: both moving boundaries are below their switches. -/
theorem weight_first {a b c d s : ℝ} (hL : s ≤ a+d) (hU : s ≤ b+c) :
    weight a b c d s = Real.log ((s-c)*(s-a)/(a*c))/s := by
  have hl : lower a d s = a := max_eq_left (by linarith)
  have hu : upper b c s = s-c := min_eq_right (by linarith)
  simp only [weight, hl, hu, sub_sub_cancel]

/-- Closed-form middle branch for a short horizontal side. -/
theorem weight_middle {a b c d s : ℝ} (hL : s ≤ a+d) (hU : b+c ≤ s) :
    weight a b c d s = Real.log (b*(s-a)/(a*(s-b)))/s := by
  have hl : lower a d s = a := max_eq_left (by linarith)
  have hu : upper b c s = b := min_eq_left (by linarith)
  simp only [weight, hl, hu]

/-- Closed-form late branch: both moving boundaries have crossed their switches. -/
theorem weight_last {a b c d s : ℝ} (hL : a+d ≤ s) (hU : b+c ≤ s) :
    weight a b c d s = Real.log (b*d/((s-d)*(s-b)))/s := by
  have hl : lower a d s = s-d := max_eq_right (by linarith)
  have hu : upper b c s = b := min_eq_left (by linarith)
  simp only [weight, hl, hu, sub_sub_cancel]

/-- Degenerate first sum fiber has exactly zero weight. -/
theorem weight_left_endpoint {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) : weight a b c d (a+c) = 0 := by
  rw [weight_first (by linarith : a+c ≤ a+d) (by linarith : a+c ≤ b+c)]
  simp only [add_sub_cancel_right, add_sub_cancel_left,
    div_self (mul_pos ha hc).ne', Real.log_one, zero_div]

/-- Degenerate last sum fiber has exactly zero weight. -/
theorem weight_right_endpoint {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) : weight a b c d (b+d) = 0 := by
  rw [weight_last (by linarith : a+d ≤ b+d) (by linarith : b+c ≤ b+d)]
  simp only [add_sub_cancel_right, add_sub_cancel_left,
    div_self (mul_pos (ha.trans_le hab) (hc.trans_le hcd)).ne', Real.log_one, zero_div]

end G67SumCoordinate

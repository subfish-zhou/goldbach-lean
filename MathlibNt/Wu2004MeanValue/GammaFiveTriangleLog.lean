import MathlibNt.Wu2004MeanValue.GammaFiveTriangleLiteral
import MathlibNt.Wu2004MeanValue.GammaFiveLossKernelIdentity

/-! Evaluation of the transported Gamma₅ sections as logarithmic kernels. -/
namespace Wu2004MeanValue.GammaFiveLossBudget
open Real Set MeasureTheory
open scoped Classical Interval

/-- Partial fractions evaluate a nonsingular section of the transported density. -/
theorem section_density_integral {L U W : ℝ} (hL : 0 < L)
    (hLU : L ≤ U) (hUW : U < W) (v : ℝ) :
    (∫ t in L..U, 1/(v*t*(W-t))) =
      (1/(v*W))*log (U*(W-L)/(L*(W-U))) := by
  have hU := hL.trans_le hLU
  have hWL : 0 < W-L := by linarith
  have hWU : 0 < W-U := sub_pos.mpr hUW
  have hW : W ≠ 0 := (hU.trans hUW).ne'
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume L U := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    rw [uIcc_of_le hLU]
    exact fun t ht => (hL.trans_le ht.1).ne'
  have hj : IntervalIntegrable (fun t : ℝ => (W-t)⁻¹) volume L U := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.sub continuousOn_id).inv₀
    rw [uIcc_of_le hLU]
    exact fun t ht => (sub_pos.mpr (ht.2.trans_lt hUW)).ne'
  calc
    _ = ∫ t in L..U, (1/(v*W))*(t⁻¹+(W-t)⁻¹) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hLU]
      intro t ht
      have ht0 := (hL.trans_le ht.1).ne'
      have hWt := (sub_pos.mpr (ht.2.trans_lt hUW)).ne'
      dsimp only
      by_cases hv : v = 0
      · simp only [hv, zero_mul, div_zero]
      · field_simp
        ring
    _ = (1/(v*W))*(log (U/L)+log ((W-L)/(W-U))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hj,
        intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) W,
        integral_inv_of_pos hL hU, integral_inv_of_pos hWU hWL]
    _ = _ := by
      rw [← log_mul (div_pos hU hL).ne' (div_pos hWL hWU).ne']
      congr 2
      field_simp

/-- The closed section formula also covers a collapsed interval. -/
theorem sectionLog_of_le {W L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hUW : U < W) :
    sectionLog W L U = log (U*(W-L)/(L*(W-U))) := by
  by_cases h : L < U
  · exact if_pos h
  · have he : U = L := le_antisymm (le_of_not_gt h) hLU
    subst U
    have hd : L*(W-L) ≠ 0 := mul_ne_zero hL.ne' (sub_pos.mpr hUW).ne'
    simp only [sectionLog, lt_self_iff_false, if_false, div_self hd, log_one]

/-- Integrating the closed section mask gives the clipped logarithmic section. -/
theorem masked_section_integral {W L U : ℝ} (hL : 0 < L) (hUW : U < W) (v : ℝ) :
    (∫ t : ℝ, if L ≤ t ∧ t ≤ U then 1/(v*t*(W-t)) else 0) =
      (1/(v*W))*sectionLog W L U := by
  have he : (fun t : ℝ => if L ≤ t ∧ t ≤ U then 1/(v*t*(W-t)) else 0) =
      (Icc L U).indicator (fun t => 1/(v*t*(W-t))) := by
    funext t
    simp only [Set.indicator, mem_Icc]
  rw [he]
  rw [integral_indicator measurableSet_Icc]
  by_cases hLU : L ≤ U
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLU,
      section_density_integral hL hLU hUW, sectionLog_of_le hL hLU hUW]
  · simp only [Icc_eq_empty hLU, Measure.restrict_empty, integral_zero_measure,
      sectionLog, if_neg (not_lt.mpr (le_of_not_ge hLU)), mul_zero]

end Wu2004MeanValue.GammaFiveLossBudget

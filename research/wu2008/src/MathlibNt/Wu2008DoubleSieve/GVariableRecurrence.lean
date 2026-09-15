import MathlibNt.Wu2008DoubleSieve.FixedCoefficientHLowerEnclosure

namespace Wu2008DoubleSieve.GVariableRecurrence
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure FixedCoefficientHLowerEnclosure
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

/-- The lower-function ratio is increasing; no upper-ratio reversal is used. -/
theorem upper_affine_from_ratio {j u C d : ℝ} (hj : 2 ≤ j) (hu : j ≤ u)
    (hC : C ≤ wuUpperCoefficient j) (hd : d ≤ wuLowerCoefficient (j-1)/(j-1)) :
    C+d*(u-j) ≤ wuUpperCoefficient u := by
  have hj0 : 0 < j-1 := by linarith
  have hab : j-1 ≤ u-1 := by linarith
  have hr := wuUpperCoefficient_sub_eq_integral hj hu
  have hm := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := d) (μ := volume))
    (wuLowerCoefficient_div_intervalIntegrable hj0 hab)
    (fun v hv => hd.trans (lower_ratio_mono hj0 hv.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
  linarith

theorem upper_four_affine {u : ℝ} (hu : 4 ≤ u) :
    34832/30375+(56/243)*(u-4) ≤ wuUpperCoefficient u := by
  apply upper_affine_from_ratio (by norm_num) hu upper_four_lower
  have he : wuLowerCoefficient 3 = log 2 := by
    convert jr1965f_normalized_firstInterval (s := 3) (by norm_num) (by norm_num) using 1 <;>
      norm_num [wuLowerCoefficient]
  norm_num only [show (4 : ℝ)-1=3 by norm_num, he]
  linarith [log_two_bounds.1]

theorem upper_five_affine {u : ℝ} (hu : 5 ≤ u) :
    340/243+(2776/10125)*(u-5) ≤ wuUpperCoefficient u := by
  apply upper_affine_from_ratio (by norm_num) hu upper_five_lower
  have he : wuLowerCoefficient 4 = log 3 := by
    convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1 <;>
      norm_num [wuLowerCoefficient]
  norm_num only [show (5 : ℝ)-1=4 by norm_num, he]
  linarith [log_three_bounds.1]

#print axioms upper_four_affine
#print axioms upper_five_affine
end Wu2008DoubleSieve.GVariableRecurrence

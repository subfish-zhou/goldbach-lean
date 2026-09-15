import MathlibNt.Wu2008DoubleSieve.FixedCoefficientUpperEnclosure

namespace Wu2008DoubleSieve.BaseUpperSplitRecurrence
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure
open scoped Interval

/-- The actual recurrence kernel is split at five, including the zero-width tail. -/
theorem lower_after_six {t : ℝ} (ht : 6 ≤ t) :
    wuLowerCoefficient t ≤ 203/144+311/1080+(42823/151875)*(t-6) := by
  have h5 := lower_after_five (t := 5) le_rfl
  norm_num only [sub_self, mul_zero, add_zero] at h5
  have ht5 : 5 ≤ t-1 := by linarith
  have h45 : (4 : ℝ) ≤ 5 := by norm_num
  have hi45 := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0 : ℝ) < 4) h45
  have hi5t := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0 : ℝ) < 5) ht5
  have hfirst := intervalIntegral.integral_mono_on h45 hi45
    (intervalIntegrable_const (c := (311/1080 : ℝ)) (μ := volume))
    (fun v hv => (SharpSingleBalance.upper_ratio_antitone
      (by norm_num : (0 : ℝ) < 4) hv.1).trans upper_four_div)
  have htail := intervalIntegral.integral_mono_on ht5 hi5t
    (intervalIntegrable_const (c := (42823/151875 : ℝ)) (μ := volume))
    (fun v hv => (SharpSingleBalance.upper_ratio_antitone
      (by norm_num : (0 : ℝ) < 5) hv.1).trans upper_five_div)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi45 hi5t
  have hrec := wuLowerCoefficient_sub_eq_integral
    (by norm_num : (2 : ℝ) ≤ 5) (show 5 ≤ t by linarith)
  norm_num only [show (5 : ℝ)-1=4 by norm_num] at hrec
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hfirst htail
  linarith

noncomputable def newBase : ℝ :=
  24*(203/144+311/1080+(42823/151875)*(1/(2*a)-6))+
  8*(11/10+(1/(2*b)-4)/3)

/-- Original positive base with its unchanged coefficients twenty-four and eight. -/
theorem base_upper :
    24*wuLowerCoefficient (1/(2*a))+8*wuLowerCoefficient (1/(2*b)) ≤ newBase := by
  have ha := lower_after_six (t := 1/(2*a)) (by norm_num [a,truncatedSixthLowerAlpha])
  have hb := FixedCoefficientScalarEnclosure.lower_affine_upper (s := 1/(2*b))
    (by norm_num [b,truncatedSixthLowerBeta])
  have hlog := log_three_bounds.2
  unfold newBase
  linarith

theorem base_difference : baseBound-newBase = (925957/10125000 : ℝ) := by
  norm_num [baseBound,newBase,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem strict_base_improvement : newBase < baseBound := by
  have h := base_difference
  linarith

end Wu2008DoubleSieve.BaseUpperSplitRecurrence

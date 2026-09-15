import MathlibNt.Wu2008DoubleSieve.GVariableRecurrence
import MathlibNt.Wu2008DoubleSieve.RationalMovingSixth

namespace Wu2008DoubleSieve.BaseRecurrenceLower
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

noncomputable def Q (v : ℝ) : ℝ := v^2/18-(2/3)*v+2*log v
noncomputable def P (j C d v : ℝ) : ℝ := d*v+(C-j*d)*log v

theorem Q_derivative {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt Q ((1+(v-3)^2/9)/v) v := by
  have h := ((((hasDerivAt_id v).pow 2).div_const 18).sub
    ((hasDerivAt_id v).const_mul (2/3))).add ((hasDerivAt_log hv).const_mul 2)
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem P_derivative (j C d : ℝ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (P j C d) ((C+d*(v-j))/v) v := by
  have h := ((hasDerivAt_id v).const_mul d).add
    ((hasDerivAt_log hv).const_mul (C-j*d))
  convert h using 1 <;> first | rfl | (field_simp; ring)

theorem polynomial_div_integrable (f : ℝ → ℝ) (hf : Continuous f)
    {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun v => f v/v) volume l r := by
  apply ContinuousOn.intervalIntegrable
  exact hf.continuousOn.div continuousOn_id (fun v hv => by
    rw [uIcc_of_le hlr] at hv
    exact (hl.trans_le hv.1).ne')

theorem quadratic_segment {r : ℝ} (hr : 3 ≤ r) (hr4 : r ≤ 4) :
    Q r-Q 3 ≤ ∫ v in (3 : ℝ)..r, wuUpperCoefficient v/v := by
  have hi := polynomial_div_integrable (fun v : ℝ => 1+(v-3)^2/9)
    (by fun_prop) (by norm_num : (0 : ℝ) < 3) hr
  have h := intervalIntegral.integral_mono_on hr hi
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) hr)
    (fun v hv => div_le_div_of_nonneg_right
      (SharpSingleBalance.upper_quadratic hv.1 (hv.2.trans hr4))
      (by linarith [hv.1]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi] at h
  · exact h
  · intro v hv
    rw [uIcc_of_le hr] at hv
    exact Q_derivative (by linarith [hv.1])

theorem affine_segment (j C d : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hbound : ∀ v ∈ Icc l r, C+d*(v-j) ≤ wuUpperCoefficient v) :
    P j C d r-P j C d l ≤ ∫ v in l..r, wuUpperCoefficient v/v := by
  have hi := polynomial_div_integrable (fun v : ℝ => C+d*(v-j))
    (by fun_prop) hl hlr
  have h := intervalIntegral.integral_mono_on hlr hi
    (wuUpperCoefficient_div_intervalIntegrable hl hlr)
    (fun v hv => div_le_div_of_nonneg_right (hbound v hv) (hl.trans_le hv.1).le)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi] at h
  · exact h
  · intro v hv
    rw [uIcc_of_le hlr] at hv
    exact P_derivative j C d (hl.trans_le hv.1).ne'

theorem Q_difference {l r : ℝ} (hl : l ≠ 0) (hr : r ≠ 0) :
    Q r-Q l = (r^2-l^2)/18-(2/3)*(r-l)+2*log (r/l) := by
  rw [log_div hr hl]
  unfold Q
  ring

theorem P_difference (j C d : ℝ) {l r : ℝ} (hl : l ≠ 0) (hr : r ≠ 0) :
    P j C d r-P j C d l = d*(r-l)+(C-j*d)*log (r/l) := by
  rw [log_div hr hl]
  unfold P
  ring

theorem lower_four_value : wuLowerCoefficient 4 = log 3 := by
  convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1 <;>
    norm_num [wuLowerCoefficient]

/-- The original lower recurrence uses A(v)/v, from 3 to s-1. -/
theorem alpha_real_lower :
    log 3+(Q 4-Q 3)+
      (P 4 (34832/30375) (56/243) 5-P 4 (34832/30375) (56/243) 4)+
      (P 5 (340/243) (2776/10125) (1127/200)-P 5 (340/243) (2776/10125) 5)
      ≤ wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) := by
  have hq := quadratic_segment (by norm_num : (3 : ℝ) ≤ 4) le_rfl
  have h4 := affine_segment 4 (34832/30375) (56/243)
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 5)
    (fun v hv => GVariableRecurrence.upper_four_affine hv.1)
  have h5 := affine_segment 5 (340/243) (2776/10125)
    (by norm_num : (0 : ℝ) < 5) (by norm_num : (5 : ℝ) ≤ 1127/200)
    (fun v hv => GVariableRecurrence.upper_five_affine hv.1)
  have hi34 := wuUpperCoefficient_div_intervalIntegrable
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
  have hi45 := wuUpperCoefficient_div_intervalIntegrable
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 5)
  have hi5r := wuUpperCoefficient_div_intervalIntegrable
    (by norm_num : (0 : ℝ) < 5) (by norm_num : (5 : ℝ) ≤ 1127/200)
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals hi34 hi45
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (hi34.trans hi45) hi5r
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4)
    (by norm_num [truncatedSixthLowerAlpha] : 4 ≤ 1/(2*truncatedSixthLowerAlpha))
  norm_num only [show (4 : ℝ)-1=3 by norm_num,
    show 1/(2*truncatedSixthLowerAlpha)-1=(1127/200 : ℝ) by norm_num [truncatedSixthLowerAlpha],
    lower_four_value] at hr
  linarith

theorem beta_real_lower :
    log 3+(Q (78/25)-Q 3) ≤ wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have hq := quadratic_segment (by norm_num : (3 : ℝ) ≤ 78/25) (by norm_num)
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4)
    (by norm_num [truncatedSixthLowerBeta] : 4 ≤ 1/(2*truncatedSixthLowerBeta))
  norm_num only [show (4 : ℝ)-1=3 by norm_num,
    show 1/(2*truncatedSixthLowerBeta)-1=(78/25 : ℝ) by norm_num [truncatedSixthLowerBeta],
    lower_four_value] at hr
  linarith

#print axioms Q_derivative
#print axioms P_derivative
#print axioms alpha_real_lower
#print axioms beta_real_lower
end Wu2008DoubleSieve.BaseRecurrenceLower

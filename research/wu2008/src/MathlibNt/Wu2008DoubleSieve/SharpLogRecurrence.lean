import MathlibNt.Wu2008DoubleSieve.ClassicalFullCoefficientBounds

namespace Wu2008DoubleSieve.SharpLogRecurrence
open Real Set MeasureTheory ClassicalAnalyticLeaves
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def lowerLog (t : ℝ) : ℝ :=
  2*((t-1)/(t+1)) + 2*((t-1)/(t+1))^3/3
noncomputable def upperLog (t : ℝ) : ℝ :=
  (t-1)*(t^2+10*t+1)/(6*t*(t+1))

theorem lower_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => log t-lowerLog t) ((t-1)^4/(t*(t+1)^4)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hq := ((hasDerivAt_id t).sub_const 1).div ((hasDerivAt_id t).add_const 1) ht1
  have h := (hasDerivAt_log ht0).sub ((hq.const_mul 2).add ((hq.pow 3).const_mul 2 |>.div_const 3))
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem upper_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => upperLog t-log t) ((t-1)^4/(6*t^2*(t+1)^2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hd : 6*t*(t+1) ≠ 0 := by positivity
  have hn := ((hasDerivAt_id t).sub_const 1).mul
    ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 10)).add_const 1)
  have hh := ((hasDerivAt_id t).const_mul 6).mul ((hasDerivAt_id t).add_const 1)
  have h := (hn.div hh hd).sub (hasDerivAt_log ht0)
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem anchored_nonnegative {f d : ℝ → ℝ} (hd : ∀ t, 1 ≤ t → HasDerivAt f (d t) t)
    (hn : ∀ t, 1 ≤ t → 0 ≤ d t) {t : ℝ} (ht : 1 ≤ t) : f 1 ≤ f t := by
  have hm : MonotoneOn f (Ici 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  exact hm (by simp) ht ht

/-- Fixed universal envelope, proved by its derivative on the entire half-line. -/
theorem log_lower {t : ℝ} (ht : 1 ≤ t) : lowerLog t ≤ log t := by
  have h := anchored_nonnegative (fun x hx => lower_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [lowerLog] at h
  exact h

/-- Fixed universal envelope; no order selection or function sampling occurs. -/
theorem log_upper {t : ℝ} (ht : 1 ≤ t) : log t ≤ upperLog t := by
  have h := anchored_nonnegative (fun x hx => upper_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [upperLog] at h
  exact h

theorem log_two_bounds : (56/81 : ℝ) ≤ log 2 ∧ log 2 ≤ 25/36 := by
  have hl := log_lower (by norm_num : (1 : ℝ) ≤ 2)
  have hu := log_upper (by norm_num : (1 : ℝ) ≤ 2)
  norm_num [lowerLog,upperLog] at hl hu
  exact ⟨hl,hu⟩

theorem log_three_bounds : (11104/10125 : ℝ) ≤ log 3 ∧ log 3 ≤ 11/10 := by
  have hl := log_lower (by norm_num : (1 : ℝ) ≤ 3/2)
  have hu := log_upper (by norm_num : (1 : ℝ) ≤ 3/2)
  have he : log (3 : ℝ) = log 2+log (3/2 : ℝ) := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3/2 : ℝ) ≠ 0)]
    norm_num
  obtain ⟨h2l,h2u⟩ := log_two_bounds
  norm_num [lowerLog,upperLog] at hl hu
  constructor <;> linarith

noncomputable def upperPrimitive (v : ℝ) : ℝ :=
  (v-1)/6-log (v-1)/6+4*log v/3+8/(3*v)

theorem upperPrimitive_derivative {v : ℝ} (hv : 2 ≤ v) :
    HasDerivAt upperPrimitive (upperLog (v-1)/v) v := by
  have hv0 : v ≠ 0 := by linarith
  have hv1 : v-1 ≠ 0 := by linarith
  have hh := ((((hasDerivAt_id v).sub_const 1).div_const 6).sub
    ((((hasDerivAt_id v).sub_const 1).log hv1).div_const 6)).add
    ((hasDerivAt_log hv0).const_mul 4 |>.div_const 3)
  have h := hh.add ((hasDerivAt_const v (8 : ℝ)).div ((hasDerivAt_id v).const_mul 3)
    (mul_ne_zero (by norm_num) hv0))
  convert h using 1 <;> first | rfl | (dsimp [upperLog]; field_simp [hv0,hv1]; ring)

theorem upper_recurrence_bound {j : ℝ} (hj : 3 ≤ j) (hj5 : j ≤ 5) :
    wuUpperCoefficient j ≤ 1+upperPrimitive (j-1)-upperPrimitive 2 := by
  have hrec := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 3) hj
  have hinit : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have horder : 2 ≤ j-1 := by linarith
  have hi : IntervalIntegrable (fun v => upperLog (v-1)/v) volume 2 (j-1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · unfold upperLog
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro v hv
        rw [uIcc_of_le horder] at hv
        have hv1 : 0 < v-1 := by linarith [hv.1]
        positivity
    · exact continuousOn_id
    · intro v hv
      rw [uIcc_of_le horder] at hv
      linarith [hv.1]
  have hle := intervalIntegral.integral_mono_on horder
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) horder) hi (fun v hv => by
      have he : wuLowerCoefficient v = log (v-1) :=
        jr1965f_normalized_firstInterval hv.1 (by linarith [hv.2])
      rw [he]
      exact div_le_div_of_nonneg_right (log_upper (by linarith [hv.1])) (by linarith [hv.1]))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => upperPrimitive_derivative (by rw [uIcc_of_le horder] at hv; exact hv.1)) hi
  rw [he] at hle
  norm_num only [show (3 : ℝ)-1=2 by norm_num, hinit] at hrec
  linarith

theorem upper_four : wuUpperCoefficient 4 ≤ 13/18+4*log 3/3-3*log 2/2 := by
  have h := upper_recurrence_bound (by norm_num : (3 : ℝ) ≤ 4) (by norm_num)
  norm_num [upperPrimitive] at h
  linarith

theorem upper_five : wuUpperCoefficient 5 ≤ 2/3+4*log 2/3-log 3/6 := by
  have h := upper_recurrence_bound (by norm_num : (3 : ℝ) ≤ 5) le_rfl
  have he : log (4 : ℝ) = 2*log 2 := by
    have hh := log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  norm_num [upperPrimitive,he] at h
  linarith

theorem upper_four_div : wuUpperCoefficient 4/4 ≤ 311/1080 := by
  have h := upper_four
  obtain ⟨h2l,_⟩ := log_two_bounds
  obtain ⟨_,h3u⟩ := log_three_bounds
  linarith

theorem upper_five_div : wuUpperCoefficient 5/5 ≤ 42823/151875 := by
  have h := upper_five
  obtain ⟨_,h2u⟩ := log_two_bounds
  obtain ⟨h3l,_⟩ := log_three_bounds
  linarith

end Wu2008DoubleSieve.SharpLogRecurrence

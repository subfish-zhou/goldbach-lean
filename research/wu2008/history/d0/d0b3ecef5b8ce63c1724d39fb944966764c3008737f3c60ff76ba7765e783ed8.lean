import W14AcceptedCount

noncomputable section
open Real Set MeasureTheory
open scoped Interval

namespace WuTarget.E06Second
open Wu08OriginalFirstSteps Wu2008DoubleSieve.SharpLogRecurrence

theorem kernel_lower {u : ℝ} (hu : 2 ≤ u) (hu' : u ≤ 53/25) :
    (1250/2809 : ℝ) * (u-2) ≤ log (u-1)/u := by
  have hp : 0 < u := by linarith
  have hz : 0 ≤ ((u-2)/u)^3 := pow_nonneg (div_nonneg (by linarith) hp.le) 3
  have hl := log_lower (show 1 ≤ u-1 by linarith)
  dsimp [lowerLog] at hl
  rw [sub_add_cancel, show u-1-1 = u-2 by ring] at hl
  have hlog : 2*(u-2)/u ≤ log (u-1) := by
    calc
      2*(u-2)/u = 2*((u-2)/u) := by ring
      _ ≤ log (u-1) := by linarith only [hl, hz]
  have hs : u^2 ≤ (53/25 : ℝ)^2 := pow_le_pow_left₀ hp.le hu' 2
  calc
    (1250/2809 : ℝ)*(u-2) = 2*(u-2)/(53/25 : ℝ)^2 := by ring
    _ ≤ 2*(u-2)/u^2 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hp 2) hs
    _ = (2*(u-2)/u)/u := by ring
    _ ≤ log (u-1)/u := div_le_div_of_nonneg_right hlog hp.le

theorem linear_integral (t : ℝ) :
    (∫ u in (2:ℝ)..(t-1), (1250/2809 : ℝ)*(u-2)) =
      (625/2809 : ℝ)*(t-3)^2 := by
  have hi : IntervalIntegrable (fun u : ℝ => (1250/2809 : ℝ)*(u-2))
      volume 2 (t-1) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hd (u : ℝ) :
      HasDerivAt (fun u : ℝ => (625/2809 : ℝ)*(u-2)^2)
        ((1250/2809 : ℝ)*(u-2)) u := by
    convert (((hasDerivAt_id u).sub_const 2).pow 2).const_mul (625/2809 : ℝ) using 1 <;>
      first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  ring

theorem inner_lower {t : ℝ} (ht : 3 ≤ t) (ht' : t ≤ 78/25) :
    (625/2809 : ℝ)*(t-3)^2 ≤ B t := by
  rw [← linear_integral]
  apply intervalIntegral.integral_mono_on (show (2:ℝ) ≤ t-1 by linarith)
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
    (k_continuous.intervalIntegrable (μ := volume) _ _)
  intro u hu
  rw [k_literal hu.1]
  exact kernel_lower hu.1 (by change u ≤ 53/25; linarith [hu.2])

theorem outer_kernel_lower {t : ℝ} (ht : 3 ≤ t) (ht' : t ≤ 78/25) :
    (15625/219102 : ℝ)*(t-3)^2 ≤ B t/t := by
  have hp : 0 < t := by linarith
  calc
    (15625/219102 : ℝ)*(t-3)^2 = ((625/2809 : ℝ)*(t-3)^2)/(78/25) := by ring
    _ ≤ ((625/2809 : ℝ)*(t-3)^2)/t :=
      div_le_div_of_nonneg_left (by positivity) hp ht'
    _ ≤ B t/t := div_le_div_of_nonneg_right (inner_lower ht ht') hp.le

theorem quadratic_integral :
    (∫ t in (3:ℝ)..(78/25), (15625/219102 : ℝ)*(t-3)^2) = 3/73034 := by
  have hi : IntervalIntegrable (fun t : ℝ => (15625/219102 : ℝ)*(t-3)^2)
      volume 3 (78/25) :=
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => (15625/657306 : ℝ)*(t-3)^3)
        ((15625/219102 : ℝ)*(t-3)^2) t := by
    convert (((hasDerivAt_id t).sub_const 3).pow 3).const_mul (15625/657306 : ℝ) using 1 <;>
      first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  norm_num

theorem C_lower : (3/73034 : ℝ) ≤ C (103/25) := by
  rw [← quadratic_integral]
  change (∫ t in (3:ℝ)..(78/25), (15625/219102 : ℝ)*(t-3)^2) ≤
    ∫ t in (3:ℝ)..(103/25-1), B t/max 1 t
  norm_num only [show (103/25 : ℝ)-1 = 78/25 by norm_num]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _)
    ((div_continuous B_continuous).intervalIntegrable (μ := volume) _ _)
  intro t ht
  rw [max_eq_right (show (1:ℝ) ≤ t by linarith [ht.1])]
  exact outer_kernel_lower ht.1 ht.2

theorem original_double_integral :
    2*C (103/25) =
      2*(∫ t in (3:ℝ)..(78/25), (∫ u in (2:ℝ)..(t-1), log (u-1)/u)/t) := by
  rw [C_literal (by norm_num : (4:ℝ) ≤ 103/25)]
  norm_num

theorem second_slack_lower : (3/36517 : ℝ) ≤ 2*C (103/25) := by
  linarith only [C_lower]

theorem second_slack_strict : (1/12500 : ℝ) < 2*C (103/25) := by
  exact lt_of_lt_of_le (by norm_num) second_slack_lower

theorem double_integral_lower :
    (3/36517 : ℝ) ≤
      2*(∫ t in (3:ℝ)..(78/25), (∫ u in (2:ℝ)..(t-1), log (u-1)/u)/t) := by
  rw [← original_double_integral]
  exact second_slack_lower

end WuTarget.E06Second

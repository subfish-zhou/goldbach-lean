import E09JointMainRoot

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.E09JointMainMajor

def lowerLog (t : ℝ) : ℝ :=
  2 * ((t - 1) / (t + 1)) + 2 * ((t - 1) / (t + 1)) ^ 3 / 3 +
    2 * ((t - 1) / (t + 1)) ^ 5 / 5 + 2 * ((t - 1) / (t + 1)) ^ 7 / 7

def upperLog (t : ℝ) : ℝ :=
  lowerLog t + (t - 1) ^ 9 / (18 * t * (t + 1) ^ 7)

theorem lower_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => log t - lowerLog t)
      ((t - 1) ^ 8 / (t * (t + 1) ^ 8)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith
  have hq := ((hasDerivAt_id t).sub_const 1).div ((hasDerivAt_id t).add_const 1) ht1
  convert (hasDerivAt_log ht0).sub
    ((((hq.const_mul 2).add ((hq.pow 3).const_mul 2 |>.div_const 3)).add
      ((hq.pow 5).const_mul 2 |>.div_const 5)).add
      ((hq.pow 7).const_mul 2 |>.div_const 7)) using 1 <;>
    first | rfl | (dsimp; field_simp [ht0, ht1]; ring)

theorem upper_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => upperLog t - log t)
      ((t - 1) ^ 10 / (18 * t ^ 2 * (t + 1) ^ 8)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith
  have hd : 18 * t * (t + 1) ^ 7 ≠ 0 := by positivity
  have hn := (((hasDerivAt_id t).sub_const 1).pow 9).div
    (((hasDerivAt_id t).const_mul 18).mul (((hasDerivAt_id t).add_const 1).pow 7)) hd
  convert! hn.sub (lower_gap_derivative ht) using 1
  · funext x
    dsimp [upperLog]
    ring
  · dsimp
    field_simp [ht0, ht1]
    ring

theorem log_lower {t : ℝ} (ht : 1 ≤ t) : lowerLog t ≤ log t := by
  have h := SharpLogRecurrence.anchored_nonnegative
    (fun x hx => lower_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [lowerLog] at h
  exact h

theorem log_upper {t : ℝ} (ht : 1 ≤ t) : log t ≤ upperLog t := by
  have h := SharpLogRecurrence.anchored_nonnegative
    (fun x hx => upper_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [upperLog, lowerLog] at h
  exact h

def logPayment : ℝ := W11Credit.collected lowerLog upperLog

theorem logPayment_le_credit : logPayment ≤ W11.correlatedCredit := by
  have h0 := log_upper (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have h1 := log_lower (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have h2 := log_lower (by norm_num : (1 : ℝ) ≤ 5 / 4)
  have h3 := log_upper (by norm_num : (1 : ℝ) ≤ 327 / 200)
  have h4 := log_upper (by norm_num : (1 : ℝ) ≤ 527 / 327)
  have h5 := log_upper (by norm_num : (1 : ℝ) ≤ 727 / 527)
  have h6 := log_upper (by norm_num : (1 : ℝ) ≤ 1200 / 727)
  rw [W11Credit.credit_collected]
  unfold logPayment W11Credit.collected
  linarith only [h0, h1, h2, h3, h4, h5, h6]

theorem logPayment_gain :
    W11Credit.payment + (16 / 1000 : ℝ) < logPayment := by
  rw [W11Credit.payment_exact]
  norm_num [logPayment, W11Credit.collected, lowerLog, upperLog]

end WuTarget.E09JointMainMajor

import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

noncomputable section
namespace WuPaper.SourceLogRational
open Real Wu2008DoubleSieve

/-- Four terms of the positive odd-power logarithm expansion. -/
def lower (t : ℝ) : ℝ :=
  let z := (t-1)/(t+1)
  2*(z+z^3/3+z^5/5+z^7/7)

theorem lower_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ lower t := by
  have hz : 0 ≤ (t-1)/(t+1) := div_nonneg (by linarith) (by linarith)
  unfold lower
  positivity

theorem gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => log t-lower t) ((t-1)^8/(t*(t+1)^8)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hq := ((hasDerivAt_id t).sub_const 1).div ((hasDerivAt_id t).add_const 1) ht1
  have h := (hasDerivAt_log ht0).sub
    ((((hq.add ((hq.pow 3).div_const 3)).add ((hq.pow 5).div_const 5)).add
      ((hq.pow 7).div_const 7)).const_mul 2)
  change HasDerivAt (fun t => log t-lower t) _ t at h
  apply h.congr_deriv
  dsimp
  field_simp
  ring

theorem lower_le_log {t : ℝ} (ht : 1 ≤ t) : lower t ≤ log t := by
  have h := SharpLogRecurrence.anchored_nonnegative (fun x hx => gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [lower] at h
  exact h

end WuPaper.SourceLogRational
#print axioms WuPaper.SourceLogRational.lower_le_log

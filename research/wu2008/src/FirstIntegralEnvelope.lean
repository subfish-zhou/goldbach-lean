import FirstIntegralFlat

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve SharpLogRecurrence
namespace FirstIntegralRecovery

/-- Only the prescribed single multiplicative decomposition is used. -/
def splitL (x : ℝ) : ℝ := lowerLog ((1+x)/2)+lowerLog (2*x/(1+x))

theorem lowerLog_continuousOn : ContinuousOn lowerLog (Ici (1:ℝ)) := by
  unfold lowerLog
  have hd : ContinuousOn (fun x : ℝ => (x-1)/(x+1)) (Ici (1:ℝ)) :=
    (continuousOn_id.sub continuousOn_const).div
      (continuousOn_id.add continuousOn_const) (fun x hx => by change 1 ≤ x at hx; linarith)
  exact (continuousOn_const.mul hd).add ((continuousOn_const.mul (hd.pow 3)).div_const 3)

theorem lowerLog_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lowerLog x := by
  have h : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) (by linarith)
  unfold lowerLog
  positivity

theorem lowerLog_pos {x : ℝ} (hx : 1 < x) : 0 < lowerLog x := by
  have h : 0 < (x-1)/(x+1) := div_pos (by linarith) (by linarith)
  unfold lowerLog
  positivity

/-- Exact derivative of the existing cubic envelope error, not a new order. -/
theorem log_lower_gap_deriv {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun x : ℝ => log x-lowerLog x)
      ((x-1)^4/(x*(x+1)^4)) x := by
  have hn : x+1 ≠ 0 := by linarith
  have hn0 : x ≠ 0 := by linarith
  have hd := ((hasDerivAt_id x).sub_const 1).div ((hasDerivAt_id x).add_const 1) hn
  have h := (hasDerivAt_log hn0).sub
    ((hd.const_mul 2).add (((hd.pow 3).const_mul 2).div_const 3))
  convert h using 1 <;> first | rfl | (dsimp [lowerLog]; field_simp; ring)

theorem lowerLog_lt_log {x : ℝ} (hx : 1 < x) : lowerLog x < log x := by
  have hc : ContinuousOn (fun x : ℝ => log x-lowerLog x) (Ici (1:ℝ)) :=
    (continuousOn_id.log (fun x hx => by change 1 ≤ x at hx; change x ≠ 0; linarith)).sub lowerLog_continuousOn
  have hm := strictMonoOn_of_deriv_pos (convex_Ici (1:ℝ)) hc (fun y hy => by
    rw [interior_Ici] at hy
    change 1 < y at hy
    rw [(log_lower_gap_deriv (le_of_lt hy)).deriv]
    exact div_pos (pow_pos (sub_pos.mpr hy) _) (mul_pos (by linarith [hy]) (pow_pos (by linarith [hy]) _)))
  have h := hm (show (1:ℝ) ∈ Ici 1 by simp) (show x ∈ Ici 1 from hx.le) hx
  norm_num [lowerLog] at h
  exact h

theorem split_arguments {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ (1+x)/2 ∧ 1 ≤ 2*x/(1+x) := by
  constructor
  · linarith
  · apply (le_div_iff₀ (show 0 < 1+x by linarith)).2
    linarith

theorem splitL_continuousOn : ContinuousOn splitL (Ici (1:ℝ)) := by
  apply ContinuousOn.add
  · exact lowerLog_continuousOn.comp
      ((continuousOn_const.add continuousOn_id).div_const 2)
      (fun x hx => (split_arguments hx).1)
  · exact lowerLog_continuousOn.comp
      ((continuousOn_const.mul continuousOn_id).div
        (continuousOn_const.add continuousOn_id) (fun x hx => by change 1 ≤ x at hx; linarith))
      (fun x hx => (split_arguments hx).2)

theorem splitL_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitL x :=
  add_nonneg (lowerLog_nonneg (split_arguments hx).1) (lowerLog_nonneg (split_arguments hx).2)

theorem split_log_identity {x : ℝ} (hx : 1 ≤ x) :
    log x = log ((1+x)/2)+log (2*x/(1+x)) := by
  rw [← log_mul (show (1+x)/2 ≠ 0 by linarith)
    (ne_of_gt (div_pos (by linarith : 0 < 2*x) (by linarith : 0 < 1+x)))]
  congr 1
  field_simp

theorem splitL_le_log {x : ℝ} (hx : 1 ≤ x) : splitL x ≤ log x := by
  rw [split_log_identity hx]
  exact add_le_add (log_lower (split_arguments hx).1) (log_lower (split_arguments hx).2)

theorem splitL_lt_log {x : ℝ} (hx : 1 < x) : splitL x < log x := by
  rw [split_log_identity hx.le]
  exact add_lt_add_of_lt_of_le (lowerLog_lt_log (by linarith))
    (log_lower (split_arguments hx.le).2)

end FirstIntegralRecovery

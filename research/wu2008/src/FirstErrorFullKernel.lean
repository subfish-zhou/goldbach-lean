import OriginalFirstErrorRecovery

namespace FirstErrorFullPayment
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open Wu2008DoubleSieve SharpLogRecurrence
open scoped Interval
noncomputable section

/-- The original argument stays in the parent's proven interval on every first row. -/
def errorDensity (S t : ℝ) : ℝ :=
  (4/7)*(upperLog ((t+1)/(S-1))-lowerLog ((t+1)/(S-1)))/t

theorem corrected_le {S t : ℝ} (hS : 3≤S) (ht : S-2≤t) (ht3 : t≤3) :
    lowerLog ((t+1)/(S-1))/t+errorDensity S t ≤ log ((t+1)/(S-1))/t := by
  have hs0 : 0<S-1 := by linarith
  have ht0 : 0<t := by linarith
  have hx : 1≤(t+1)/(S-1) := (one_le_div hs0).mpr (by linarith)
  have hx2 : (t+1)/(S-1)≤2 := (div_le_iff₀ hs0).mpr (by linarith)
  have h := div_le_div_of_nonneg_right
    (OriginalFirstErrorRecovery.terminal_lower_error hx hx2) ht0.le
  unfold errorDensity
  rw [sub_div] at h
  linarith only [h]

def qa (S : ℝ) : ℝ := (2-S)^5/S^3
def qb (S : ℝ) : ℝ := (S-1)^2
def qc (S : ℝ) : ℝ := 9-8*S-qa S-qb S
def qd (S : ℝ) : ℝ := 16*(S-1)^3*(S+2)/S^2
def qe (S : ℝ) : ℝ := -32*(S-1)^4/S

def errorPrimitive (S t : ℝ) : ℝ :=
  (2/(21*(S-1)))*(t+qa S*log t+qb S*log (t+1)+qc S*log (t+S)-
    qd S/(t+S)-qe S/(2*(t+S)^2))

theorem errorDensity_laurent {S t : ℝ} (hS : 3≤S) (ht : 0<t) :
    errorDensity S t = (2/(21*(S-1)))*
      (1+qa S/t+qb S/(t+1)+qc S/(t+S)+qd S/(t+S)^2+qe S/(t+S)^3) := by
  have hs : S≠0 := by linarith
  have hs1 : S-1≠0 := by linarith
  have ht1 : t+1≠0 := by linarith
  have hts : t+S≠0 := by linarith
  have hx : 0<(t+1)/(S-1) := div_pos (by linarith) (by linarith)
  unfold errorDensity
  rw [OriginalFirstErrorRecovery.envelope_gap hx]
  have hsum : (t+1)/(S-1)+1=(t+S)/(S-1) := by field_simp; ring
  rw [hsum]
  dsimp [qa,qb,qc,qd,qe]
  field_simp [hs,hs1,ht1,hts,ht.ne']
  ring

theorem errorDensity_continuous {S a b : ℝ} (hS : 3≤S) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (errorDensity S) (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have hs0 : 0<S-1 := by linarith
  have hx0 : 0<(t+1)/(S-1) := by positivity
  unfold errorDensity upperLog lowerLog
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := first | positivity | linarith)

theorem errorPrimitive_deriv {S t : ℝ} (hS : 3≤S) (ht : 0<t) :
    HasDerivAt (errorPrimitive S) (errorDensity S t) t := by
  have ht1 : t+1≠0 := by linarith
  have hts : t+S≠0 := by linarith
  have dy := (hasDerivAt_id t).add_const S
  have dz := (hasDerivAt_id t).add_const 1
  have h := ((((((hasDerivAt_id t).add
    ((hasDerivAt_log ht.ne').const_mul (qa S))).add
    ((dz.log ht1).const_mul (qb S))).add
    ((dy.log hts).const_mul (qc S))).sub
    ((hasDerivAt_const t (qd S)).div dy hts)).sub
    ((hasDerivAt_const t (qe S)).div ((dy.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hts)))).const_mul (2/(21*(S-1)))
  convert h using 1 <;> first | rfl | skip
  rw [errorDensity_laurent hS ht]
  dsimp
  congr 1
  field_simp [ht.ne',ht1,hts]
  ring

theorem error_integral {S a b : ℝ} (hS : 3≤S) (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,errorDensity S t)=errorPrimitive S b-errorPrimitive S a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact errorPrimitive_deriv hS (ha.trans_le ht.1)
  · exact (errorDensity_continuous hS ha hab).intervalIntegrable

end
end FirstErrorFullPayment

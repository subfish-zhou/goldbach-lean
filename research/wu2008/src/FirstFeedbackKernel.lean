import NineOriginalTargets

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open SharpLogRecurrence Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- Partial fractions of the already allowed cubic L, not a new Taylor order. -/
def ea (S : ℝ) : ℝ := 8/3-4*(2*(S-1))/S+2*(2*(S-1))^2/S^2-
  2*(2*(S-1))^3/(3*S^3)
def eb (S : ℝ) : ℝ := 4*(2*(S-1))/S-2*(2*(S-1))^2/S^2+
  2*(2*(S-1))^3/(3*S^3)
def ec (S : ℝ) : ℝ := -2*(2*(S-1))^2/S+2*(2*(S-1))^3/(3*S^2)
def ed (S : ℝ) : ℝ := 2*(2*(S-1))^3/(3*S)
def ePrimitive (S t : ℝ) : ℝ :=
  ea S*log t+eb S*log (t+S)-ec S/(t+S)-ed S/(2*(t+S)^2)
def eCell (S a b : ℝ) : ℝ :=
  signedLow (ea S) (b/a)+signedLow (eb S) ((b+S)/(a+S))-
  ec S*(1/(b+S)-1/(a+S))-ed S/2*(1/(b+S)^2-1/(a+S)^2)

theorem ePrimitive_deriv {S t : ℝ} (hS : 3≤S) (ht : 0<t) :
    HasDerivAt (ePrimitive S) (lowerLog ((t+1)/(S-1))/t) t := by
  have hs : S≠0 := by linarith
  have hs1 : S-1≠0 := by linarith
  have hts : t+S≠0 := by linarith
  have dy := (hasDerivAt_id t).add_const S
  have h := ((((hasDerivAt_log ht.ne').const_mul (ea S)).add
    ((dy.log hts).const_mul (eb S))).sub
    ((hasDerivAt_const t (ec S)).div dy hts)).sub
    ((hasDerivAt_const t (ed S)).div ((dy.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hts)))
  convert h using 1 <;> first | rfl | skip
  rw [lowerLog, Wu04FactorJPrimitive.cayley_div hs1 (by linarith : t+1+(S-1)≠0)]
  dsimp [ea,eb,ec,ed]
  field_simp [hs,ht.ne',hts]
  ring

theorem lower_e_integrable {S a b : ℝ} (hS : 3≤S) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t => lowerLog ((t+1)/(S-1))/t) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have hs0 : 0<S-1 := by linarith
  have harg : (t+1)/(S-1)+1≠0 := ne_of_gt (by positivity)
  unfold lowerLog
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := first | assumption | positivity)

theorem eCell_paid {S a b : ℝ} (hS : 3≤S) (ha : S-2≤a) (hab : a≤b) :
    eCell S a b ≤ ∫ t in a..b, log ((t+1)/(S-1))/t := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := ha0.trans_le hab
  have has : 0<a+S := by linarith
  have hbs : 0<b+S := by linarith
  have he : (∫ t in a..b, lowerLog ((t+1)/(S-1))/t)=
      ePrimitive S b-ePrimitive S a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact ePrimitive_deriv hS (ha0.trans_le ht.1)
    · exact lower_e_integrable hS ha0 hab
  have hlogs : eCell S a b≤ePrimitive S b-ePrimitive S a := by
    have h1 := signed_bound (ea S) (div_pos hb0 ha0)
    have h2 := signed_bound (eb S) (div_pos hbs has)
    rw [log_div hb0.ne' ha0.ne'] at h1
    rw [log_div hbs.ne' has.ne'] at h2
    dsimp [eCell,ePrimitive]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf at h1 h2 ⊢
    linarith only [h1,h2]
  refine (hlogs.trans_eq he.symm).trans ?_
  apply intervalIntegral.integral_mono_on hab (lower_e_integrable hS ha0 hab)
  · apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht0 : 0<t := ha0.trans_le ht.1
    have hs0 : 0<S-1 := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  · intro t ht
    apply div_le_div_of_nonneg_right _ (ha0.trans_le ht.1).le
    apply log_lower
    exact (one_le_div (by linarith : 0<S-1)).mpr (by linarith [ht.1])

end
end FirstFeedbackIntegrals

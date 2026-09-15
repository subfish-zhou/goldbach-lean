import FirstActualRecovery

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence
namespace F1FullRecoveryPayment

/-- Recovery from the two existing envelopes; no series or new splitting. -/
def lowerGapPayment (x : ℝ) : ℝ :=
  (6*x/(x^2+8*x+1))*(upperLog x-lowerLog x)

/-- Original-domain derivative comparison for the already present lower error. -/
theorem lower_gap_comparison_deriv {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) :
    HasDerivAt (fun t => (log t-lowerLog t)-
      (6*x/(x^2+8*x+1))*((upperLog t-log t)+(log t-lowerLog t)))
      ((t-1)^4*(x-t)*(x*t-1)/(t^2*(t+1)^4*(x^2+8*x+1))) t := by
  have h := (lower_gap_derivative ht).sub
    (((upper_gap_derivative ht).add (lower_gap_derivative ht)).const_mul
      (6*x/(x^2+8*x+1)))
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hx0 : x^2+8*x+1 ≠ 0 := by positivity
  convert h using 1 <;> first | rfl | (field_simp [ht0,ht1,hx0]; ring)

/-- A quantitative payment of the true lower-envelope error on its full domain. -/
theorem lowerGapPayment_le {x : ℝ} (hx : 1 ≤ x) :
    lowerGapPayment x ≤ log x-lowerLog x := by
  let f : ℝ → ℝ := fun t => (log t-lowerLog t)-
    (6*x/(x^2+8*x+1))*((upperLog t-log t)+(log t-lowerLog t))
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) := lower_gap_comparison_deriv hx ht.1
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI := interior_subset ht
    have htt : 1 ≤ t ∧ t ≤ x := htI
    have hprod : 0 ≤ x*t-1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr htt.1)]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr htt.2)) hprod)
      (by positivity)
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  dsimp [f] at h
  norm_num [upperLog,lowerLog] at h
  simpa only [lowerGapPayment,upperLog,lowerLog] using h

end F1FullRecoveryPayment

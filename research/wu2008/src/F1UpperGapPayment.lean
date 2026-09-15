import F1LogRecoveryPayment

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence
namespace F1FullRecoveryPayment

/-- Integrates only the derivative of the existing V error on its original domain. -/
def upperGapPayment (x : ℝ) : ℝ := (x-1)^7/(70*x^2*(x+1)^4)

theorem upper_gap_deriv {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => JointLogTotalComparison.V t-log t)
      ((t-1)^6/(10*t^2*(t+1)^4)) t := by
  have h := (((upper_gap_derivative ht).const_mul 3).sub
    ((lower_gap_derivative ht).const_mul 2)).div_const 5
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  convert h using 1 <;> first
    | rfl
    | (funext z; dsimp [JointLogTotalComparison.V]; ring)
    | (field_simp [ht0,ht1]; ring)

theorem upper_gap_comparison_deriv {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) :
    HasDerivAt (fun t => (JointLogTotalComparison.V t-log t)-
      (t-1)^7/(70*x^2*(x+1)^4))
      ((t-1)^6/(10*t^2*(t+1)^4)-(t-1)^6/(10*x^2*(x+1)^4)) t := by
  have h := (upper_gap_deriv ht).sub
    ((((hasDerivAt_id t).sub_const 1).pow 7).div_const (70*x^2*(x+1)^4))
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  convert h using 1 <;> first | rfl | (dsimp; norm_num; field_simp [hx0,hx1]; ring)

/-- Full interval [1,x]; the only denominator bound is forced by its original endpoint. -/
theorem upperGapPayment_le {x : ℝ} (hx : 1 ≤ x) :
    upperGapPayment x ≤ JointLogTotalComparison.V x-log x := by
  let f : ℝ → ℝ := fun t => JointLogTotalComparison.V t-log t-
    (t-1)^7/(70*x^2*(x+1)^4)
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) := upper_gap_comparison_deriv hx ht.1
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI : t ∈ Icc 1 x := interior_subset ht
    have ht0 : 0 < t := by linarith [htI.1]
    have ht1 : 0 < t+1 := by linarith
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr <;> linarith [htI.2]
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hf : f 1 = 0 := by norm_num [f,JointLogTotalComparison.V,upperLog,lowerLog]
  rw [hf] at h
  exact sub_nonneg.mp h

end F1FullRecoveryPayment

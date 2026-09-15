import F1TailFixedWhole

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence
open F1JointFTC F1JointSplit F1FullRecoveryPayment
namespace F1SignedUpperFTC

/-- The derivative of the original high error, after its old payment was subtracted. -/
theorem high_error_deriv {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => high t-log t)
      ((t-1)^7*(3*t+1)/(35*t^3*(t+1)^5)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hp := ((((hasDerivAt_id t).sub_const 1).pow 7).div
    (((((hasDerivAt_id t).pow 2).const_mul 70).mul
      (((hasDerivAt_id t).add_const 1).pow 4))) (by positivity : 70*t^2*(t+1)^4 ≠ 0))
  have h := (upper_gap_deriv ht).sub hp
  convert h using 1 <;> first
    | rfl
    | (funext z; dsimp [high,upperGapPayment]; ring)
    | (dsimp; norm_num; field_simp [ht0,ht1]; ring)

/-- Only the forced numerator primitive; the original denominator is frozen at x. -/
def primitive (x t : ℝ) : ℝ := ((t-1)^8/2+(t-1)^9/3)/(35*x^3*(x+1)^5)

def payment (x : ℝ) : ℝ := primitive x x

theorem primitive_deriv (x t : ℝ) :
    HasDerivAt (primitive x) ((t-1)^7*(3*t+1)/(35*x^3*(x+1)^5)) t := by
  have h := (((((hasDerivAt_id t).sub_const 1).pow 8).div_const 2).add
    ((((hasDerivAt_id t).sub_const 1).pow 9).div_const 3)).div_const
      (35*x^3*(x+1)^5)
  convert h using 1 <;> first | rfl | (dsimp; ring)

/-- Full [1,x] comparison, with no further split, recurrence or series. -/
theorem payment_le_error {x : ℝ} (hx : 1 ≤ x) : payment x ≤ high x-log x := by
  let f : ℝ → ℝ := fun t => high t-log t-primitive x t
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    (high_error_deriv ht.1).sub (primitive_deriv x t)
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI : t ∈ Icc 1 x := interior_subset ht
    have ht0 : 0 < t := by linarith [htI.1]
    have ht1 : 0 < t+1 := by linarith
    have hn : 0 ≤ t-1 := sub_nonneg.mpr htI.1
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr <;> linarith [htI.2]
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hf : f 1 = 0 := by
    norm_num [f,high,upperGapPayment,primitive,JointLogTotalComparison.V,upperLog,lowerLog]
  rw [hf] at h
  exact sub_nonneg.mp h

theorem payment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ payment x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 ≤ x-1 := sub_nonneg.mpr hx
  unfold payment primitive
  positivity

theorem payment_pos {x : ℝ} (hx : 1 < x) : 0 < payment x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x-1 := sub_pos.mpr hx
  unfold payment primitive
  positivity

/-- Exactly the two arguments of the pre-existing splitHigh. -/
def splitPayment (x : ℝ) : ℝ := payment ((1+x)/2)+payment (2*x/(1+x))

theorem splitPayment_le_error {x : ℝ} (hx : 1 ≤ x) :
    splitPayment x ≤ splitHigh x-log x := by
  have ha := payment_le_error (FirstIntegralRecovery.split_arguments hx).1
  have hb := payment_le_error (FirstIntegralRecovery.split_arguments hx).2
  rw [FirstIntegralRecovery.split_log_identity hx]
  unfold splitPayment splitHigh
  linarith only [ha,hb]

theorem splitPayment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitPayment x :=
  add_nonneg (payment_nonneg (FirstIntegralRecovery.split_arguments hx).1)
    (payment_nonneg (FirstIntegralRecovery.split_arguments hx).2)

theorem splitPayment_pos {x : ℝ} (hx : 1 < x) : 0 < splitPayment x := by
  exact add_pos_of_pos_of_nonneg (payment_pos (by linarith : 1 < (1+x)/2))
    (payment_nonneg (FirstIntegralRecovery.split_arguments hx.le).2)

/-- A negative signed coefficient uses the remaining upper error, not a lower floor. -/
theorem negative_payment {c x : ℝ} (hc : c ≤ 0) (hx : 1 ≤ x) :
    c*splitHigh x+(-c)*splitPayment x ≤ c*log x := by
  have h := mul_le_mul_of_nonneg_left (splitPayment_le_error hx) (neg_nonneg.mpr hc)
  linarith only [h]

end F1SignedUpperFTC

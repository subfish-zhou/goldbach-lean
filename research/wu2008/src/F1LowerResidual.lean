import F1FixedSquareExtent

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment
namespace F1LowerResidual

def denom (x : ℝ) : ℝ := x^2*(x+1)^4*(x^2+8*x+1)
def primitive (x t : ℝ) : ℝ :=
  (x-1)^2*(t-1)^5/5+(x-1)^2*(t-1)^6/6-x*(t-1)^7/7
def payment (x : ℝ) : ℝ := (x-1)^7*(5*x+7)/(210*denom x)

theorem primitive_deriv (x t : ℝ) : HasDerivAt (primitive x)
    ((t-1)^4*(x-t)*(x*t-1)) t := by
  have h := (hasDerivAt_id t).sub_const 1
  convert ((((h.pow 5).const_mul ((x-1)^2)).div_const 5).add
    (((h.pow 6).const_mul ((x-1)^2)).div_const 6)).sub
    (((h.pow 7).const_mul x).div_const 7) using 1 <;>
    first | rfl | (dsimp [primitive]; ring)

theorem endpoint (x : ℝ) : primitive x x/denom x=payment x := by
  unfold primitive payment
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The original residual derivative is paid over its entire original interval. -/
theorem payment_le {x : ℝ} (hx : 1 ≤ x) :
    payment x ≤ log x-lowerLog x-lowerGapPayment x := by
  let f : ℝ → ℝ := fun t => (log t-lowerLog t)-
    (6*x/(x^2+8*x+1))*((upperLog t-log t)+(log t-lowerLog t))-
    primitive x t/denom x
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    (lower_gap_comparison_deriv hx ht.1).sub ((primitive_deriv x t).div_const (denom x))
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI : t ∈ Icc 1 x := interior_subset ht
    have ht0 : 0 < t := by linarith [htI.1]
    have hx0 : 0 < x := by linarith
    have hxt : 0 ≤ x*t-1 := by
      nlinarith [htI.1,mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr htI.1)]
    have hn : 0 ≤ (t-1)^4*(x-t)*(x*t-1) :=
      mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr htI.2)) hxt
    have hq : 0 < t^2*(t+1)^4*(x^2+8*x+1) := by positivity
    have hden : t^2*(t+1)^4*(x^2+8*x+1) ≤ denom x := by
      unfold denom
      gcongr <;> linarith [htI.1,htI.2]
    exact sub_nonneg.mpr (div_le_div_of_nonneg_left hn hq hden)
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hbase : f 1=0 := by norm_num [f,primitive,upperLog,lowerLog]
  have hend : f x=log x-lowerLog x-lowerGapPayment x-payment x := by
    dsimp only [f]
    rw [endpoint]
    unfold lowerGapPayment
    ring
  rw [hbase,hend] at h
  linarith only [h]

theorem payment_pos {x : ℝ} (hx : 1 < x) : 0 < payment x := by
  have hx0 : 0 < x := by linarith
  unfold payment denom
  exact div_pos (mul_pos (pow_pos (sub_pos.mpr hx) _) (by positivity)) (by positivity)

end F1LowerResidual

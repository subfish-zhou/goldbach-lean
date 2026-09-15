import Hf4FullOuterStrict

noncomputable section
namespace Hf4Outer
open Real Set Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment

/-- Quantitative unpaid upper error, not another whole log bound. -/
def upperPayment (x : ℝ) : ℝ := (x-1)^8/(560*x^3*(x+1)^4)

def upperPrimitive (x t : ℝ) : ℝ := (x-1)*(t-1)^7/7-(t-1)^8/8

theorem upperPrimitive_deriv (x t : ℝ) :
    HasDerivAt (upperPrimitive x) ((t-1)^6*(x-t)) t := by
  have h := (hasDerivAt_id t).sub_const 1
  convert (((h.pow 7).const_mul (x-1)).div_const 7).sub
    ((h.pow 8).div_const 8) using 1 <;>
    first | rfl | (dsimp [upperPrimitive]; ring)

/-- Keep the original endpoint denominator and pay its first discarded factor. -/
theorem upper_derivative_loss {x t : ℝ} (hx : 1 ≤ x) (ht : t ∈ Icc 1 x) :
    (t-1)^6/(10*x^2*(x+1)^4) +
      (t-1)^6*(x-t)/(10*x^3*(x+1)^4) ≤
    (t-1)^6/(10*t^2*(t+1)^4) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hn : 0 ≤ (t-1)^6 := by positivity
  have hs : 0 ≤ 2*x-t := by linarith [ht.2]
  have hsmall : t^2*(2*x-t) ≤ x^3 := by
    have h1 : t*(2*x-t) ≤ x^2 := by nlinarith only [sq_nonneg (x-t)]
    calc
      _ = t*(t*(2*x-t)) := by ring
      _ ≤ x*x^2 := mul_le_mul ht.2 h1 (mul_nonneg ht0.le hs) hx0.le
      _ = _ := by ring
  have hden : (10*t^2*(t+1)^4)*(2*x-t) ≤ 10*x^3*(x+1)^4 := by
    calc
      _ = 10*(t^2*(2*x-t))*(t+1)^4 := by ring
      _ ≤ 10*x^3*(x+1)^4 := by gcongr; exact ht.2
  calc
    _ = (t-1)^6*(2*x-t)/(10*x^3*(x+1)^4) := by
      field_simp
      ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < 10*x^3*(x+1)^4)
        (by positivity : 0 < 10*t^2*(t+1)^4)).mpr
      convert mul_le_mul_of_nonneg_left hden hn using 1
      ring

/-- The upper-minus-log orientation is essential for the negative outer coefficient. -/
theorem upperPayment_le {x : ℝ} (hx : 1 ≤ x) :
    upperPayment x ≤ RemainingHf.basicUpper x-log x := by
  let f : ℝ → ℝ := fun t => JointLogTotalComparison.V t-log t-
    (t-1)^7/(70*x^2*(x+1)^4)-upperPrimitive x t/(10*x^3*(x+1)^4)
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    (upper_gap_comparison_deriv hx ht.1).sub
      ((upperPrimitive_deriv x t).div_const (10*x^3*(x+1)^4))
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have h := upper_derivative_loss hx (interior_subset ht)
    linarith only [h]
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hb : f 1 = 0 := by
    norm_num [f, upperPrimitive, JointLogTotalComparison.V, upperLog, lowerLog]
  have he : f x = RemainingHf.basicUpper x-log x-upperPayment x := by
    dsimp only [f]
    unfold RemainingHf.basicUpper upperGapPayment upperPayment upperPrimitive
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hb,he] at h
  linarith only [h]

theorem upperPayment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ upperPayment x := by
  have hx0 : 0 < x := by linarith
  unfold upperPayment
  positivity

/-- Reuse the prescribed split once, leaving the right-factor upper loss unpaid. -/
theorem splitUpper_loss_lower {x : ℝ} (hx : 1 ≤ x) :
    upperPayment (Wu04FactorEnvelopes.leftFactor x) ≤
      RemainingHf.splitUpper x-log x := by
  have hl := upperPayment_le (Wu04FactorEnvelopes.factors hx).1
  have hr := RemainingHf.le_basicUpper (Wu04FactorEnvelopes.factors hx).2.1
  rw [Wu04FactorEnvelopes.exact_log hx]
  unfold RemainingHf.splitUpper
  linarith only [hl,hr]

end Hf4Outer

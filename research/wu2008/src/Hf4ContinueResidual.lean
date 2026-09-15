import Hf4RefineTerminal

noncomputable section
namespace Hf4Continue
open Real Set Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment

/-- The first frozen-denominator loss, on the same original log interval. -/
def denominatorPrimitive (x t : ℝ) : ℝ :=
  (x-1)^3*(t-1)^5/5 + (x-2)*(x-1)^2*(t-1)^6/6 +
    (x-1)*(1-2*x)*(t-1)^7/7 + x*(t-1)^8/8

def denominatorPayment (x : ℝ) : ℝ :=
  (x-1)^8*(5*x+8)/(840*x*F1LowerResidual.denom x)

theorem denominatorPrimitive_deriv (x t : ℝ) :
    HasDerivAt (denominatorPrimitive x) ((t-1)^4*(x-t)^2*(x*t-1)) t := by
  have h := (hasDerivAt_id t).sub_const 1
  convert (((((h.pow 5).const_mul ((x-1)^3)).div_const 5).add
    (((h.pow 6).const_mul ((x-2)*(x-1)^2)).div_const 6)).add
    (((h.pow 7).const_mul ((x-1)*(1-2*x))).div_const 7)).add
    (((h.pow 8).const_mul x).div_const 8) using 1 <;>
      first | rfl | (dsimp [denominatorPrimitive]; ring)

theorem denominatorPrimitive_endpoint (x : ℝ) :
    denominatorPrimitive x x/(x*F1LowerResidual.denom x) = denominatorPayment x := by
  unfold denominatorPrimitive denominatorPayment
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- This compares the remaining denominator error, not two whole lower bounds. -/
theorem denominator_loss_lower {x t : ℝ} (hx : 1 ≤ x) (ht : t ∈ Icc 1 x) :
    ((t-1)^4*(x-t)*(x*t-1))/F1LowerResidual.denom x +
      ((t-1)^4*(x-t)^2*(x*t-1))/(x*F1LowerResidual.denom x) ≤
    ((t-1)^4*(x-t)*(x*t-1))/(t^2*(t+1)^4*(x^2+8*x+1)) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hxt : 0 ≤ x*t-1 := by nlinarith [ht.1]
  have hn : 0 ≤ (t-1)^4*(x-t)*(x*t-1) := by
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr ht.2)) hxt
  have hq : 0 < t^2*(t+1)^4*(x^2+8*x+1) := by positivity
  have hD : 0 < F1LowerResidual.denom x := by unfold F1LowerResidual.denom; positivity
  have hs : 0 ≤ 2*x-t := by linarith [ht.2]
  have hsmall : t^2*(2*x-t) ≤ x^3 := by
    have h1 : t*(2*x-t) ≤ x^2 := by nlinarith only [sq_nonneg (x-t)]
    calc
      _ = t*(t*(2*x-t)) := by ring
      _ ≤ x*x^2 := mul_le_mul ht.2 h1 (mul_nonneg ht0.le hs) hx0.le
      _ = _ := by ring
  have hden : (t^2*(t+1)^4*(x^2+8*x+1))*(2*x-t) ≤ x*F1LowerResidual.denom x := by
    calc
      _ = (t^2*(2*x-t))*(t+1)^4*(x^2+8*x+1) := by ring
      _ ≤ x^3*(x+1)^4*(x^2+8*x+1) := by gcongr; exact ht.2
      _ = _ := by unfold F1LowerResidual.denom; ring
  calc
    _ = ((t-1)^4*(x-t)*(x*t-1))*(2*x-t)/(x*F1LowerResidual.denom x) := by
      field_simp
      ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos hx0 hD) hq).mpr
      convert mul_le_mul_of_nonneg_left hden hn using 1
      ring

/-- Pay a previously discarded part of log-basicLower; no envelope order changes. -/
theorem denominatorPayment_le {x : ℝ} (hx : 1 ≤ x) :
    denominatorPayment x ≤ log x-RemainingHf.basicLower x := by
  let f : ℝ → ℝ := fun t => (log t-lowerLog t)-
    (6*x/(x^2+8*x+1))*((upperLog t-log t)+(log t-lowerLog t))-
    F1LowerResidual.primitive x t/F1LowerResidual.denom x-
    denominatorPrimitive x t/(x*F1LowerResidual.denom x)
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    ((lower_gap_comparison_deriv hx ht.1).sub
      ((F1LowerResidual.primitive_deriv x t).div_const (F1LowerResidual.denom x))).sub
      ((denominatorPrimitive_deriv x t).div_const (x*F1LowerResidual.denom x))
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have h := denominator_loss_lower hx (interior_subset ht)
    linarith only [h]
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hb : f 1 = 0 := by
    norm_num [f, F1LowerResidual.primitive, denominatorPrimitive, upperLog, lowerLog]
  have he : f x = log x-RemainingHf.basicLower x-denominatorPayment x := by
    dsimp only [f]
    rw [F1LowerResidual.endpoint, denominatorPrimitive_endpoint]
    unfold RemainingHf.basicLower lowerGapPayment
    ring
  rw [hb,he] at h
  linarith only [h]

theorem denominatorPayment_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ denominatorPayment x := by
  have hx0 : 0 < x := by linarith
  unfold denominatorPayment F1LowerResidual.denom
  positivity

theorem denominatorPayment_pos {x : ℝ} (hx : 1 < x) : 0 < denominatorPayment x := by
  have hx0 : 0 < x := by linarith
  unfold denominatorPayment F1LowerResidual.denom
  exact div_pos (mul_pos (pow_pos (sub_pos.mpr hx) _) (by positivity)) (by positivity)

end Hf4Continue

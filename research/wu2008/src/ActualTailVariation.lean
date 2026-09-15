import WholeRationalPart

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment
namespace ActualTailVariation

/-- The denominator variation of the already fixed residual, not another series order. -/
def denominator (x : ℝ) : ℝ := x^4*(x+1)^4*(x^2+8*x+1)
def floor (x : ℝ) : ℝ := 2*(x-1)^8/(105*denominator x)
def innerPrimitive (x t : ℝ) : ℝ :=
  (2*(x-1)/denominator x)*
    ((x-1)^2*(t-1)^5/5-(x-1)*(t-1)^6/3+(t-1)^7/7)

theorem innerPrimitive_deriv (x t : ℝ) : HasDerivAt (innerPrimitive x)
    (2*(x-1)/denominator x*((t-1)^4*(x-t)^2)) t := by
  have h := (hasDerivAt_id t).sub_const 1
  convert (((((h.pow 5).const_mul ((x-1)^2)).div_const 5).sub
    (((h.pow 6).const_mul (x-1)).div_const 3)).add
    ((h.pow 7).div_const 7)).const_mul (2*(x-1)/denominator x) using 1 <;>
    first | rfl | (dsimp [innerPrimitive]; ring)

theorem innerEndpoint (x : ℝ) : innerPrimitive x x=floor x := by
  unfold innerPrimitive floor
  ring

theorem inverse_variation {x t : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    2*(x-t)/denominator x ≤
      1/(t^2*(t+1)^4*(x^2+8*x+1))-1/F1LowerResidual.denom x := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hq : 0 < x^2+8*x+1 := by positivity
  have hc : 0 < (x+1)^4*(x^2+8*x+1) := by positivity
  have hA : 1/(t^2*((x+1)^4*(x^2+8*x+1))) ≤
      1/(t^2*(t+1)^4*(x^2+8*x+1)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    calc
      t^2*(t+1)^4*(x^2+8*x+1) ≤ t^2*(x+1)^4*(x^2+8*x+1) := by
        gcongr
      _ = _ := by ring
  have hN : 0 ≤ (x-t)*(x^2*(x+t-2)+2*(x-t)*(x+t)) := by
    have hxt : 0 ≤ x-t := sub_nonneg.mpr htx
    have hsum : 0 ≤ x+t-2 := by linarith
    positivity
  have hid : 1/(t^2*((x+1)^4*(x^2+8*x+1)))-
      1/F1LowerResidual.denom x-2*(x-t)/denominator x =
      (x-t)*(x^2*(x+t-2)+2*(x-t)*(x+t))/
        (x^4*t^2*((x+1)^4*(x^2+8*x+1))) := by
    unfold F1LowerResidual.denom denominator
    field_simp
    ring
  have hn : 0 ≤ 1/(t^2*((x+1)^4*(x^2+8*x+1)))-
      1/F1LowerResidual.denom x-2*(x-t)/denominator x := by
    rw [hid]
    exact div_nonneg hN (by positivity)
  linarith only [hA,hn]

theorem derivative_payment {x t : ℝ} (hx : 1 ≤ x) (ht : t ∈ Icc 1 x) :
    2*(x-1)/denominator x*((t-1)^4*(x-t)^2) ≤
      (t-1)^4*(x-t)*(x*t-1)/(t^2*(t+1)^4*(x^2+8*x+1))-
      (t-1)^4*(x-t)*(x*t-1)/F1LowerResidual.denom x := by
  have hx0 : 0 < x := by linarith
  have hxt : 0 ≤ x-t := sub_nonneg.mpr ht.2
  have htm : 0 ≤ t-1 := sub_nonneg.mpr ht.1
  have hprod : x-1 ≤ x*t-1 := by nlinarith [mul_nonneg hx0.le htm]
  have hprod0 : 0 ≤ x*t-1 := by linarith
  have hN : 0 ≤ (t-1)^4*(x-t)*(x*t-1) := by positivity
  have h := mul_le_mul_of_nonneg_left (inverse_variation ht.1 ht.2) hN
  have hsmall := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2*(t-1)^4*(x-t)^2/denominator x by unfold denominator; positivity)
  calc
    _ = (2*(t-1)^4*(x-t)^2/denominator x)*(x-1) := by ring
    _ ≤ (2*(t-1)^4*(x-t)^2/denominator x)*(x*t-1) := hsmall
    _ = (t-1)^4*(x-t)*(x*t-1)*(2*(x-t)/denominator x) := by ring
    _ ≤ (t-1)^4*(x-t)*(x*t-1)*
        (1/(t^2*(t+1)^4*(x^2+8*x+1))-1/F1LowerResidual.denom x) := h
    _ = _ := by ring

/-- A quantitative bound for the true residual of the existing fixed payment. -/
theorem floor_le {x : ℝ} (hx : 1 ≤ x) :
    floor x ≤ log x-lowerLog x-lowerGapPayment x-F1LowerResidual.payment x := by
  let f : ℝ → ℝ := fun t => (log t-lowerLog t)-
    (6*x/(x^2+8*x+1))*((upperLog t-log t)+(log t-lowerLog t))-
    F1LowerResidual.primitive x t/F1LowerResidual.denom x-innerPrimitive x t
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :=
    ((lower_gap_comparison_deriv hx ht.1).sub
      ((F1LowerResidual.primitive_deriv x t).div_const (F1LowerResidual.denom x))).sub
      (innerPrimitive_deriv x t)
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (derivative_payment hx (interior_subset ht))
  have h := hm (show (1:ℝ) ∈ Icc 1 x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc 1 x from ⟨hx,le_rfl⟩) hx
  have hbase : f 1=0 := by
    norm_num [f,F1LowerResidual.primitive,innerPrimitive,upperLog,lowerLog]
  have hend : f x=log x-lowerLog x-lowerGapPayment x-F1LowerResidual.payment x-floor x := by
    dsimp only [f]
    rw [F1LowerResidual.endpoint,innerEndpoint]
    unfold lowerGapPayment
    ring
  rw [hbase,hend] at h
  linarith only [h]

theorem floor_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ floor x := by
  have hx0 : 0 < x := by linarith
  unfold floor denominator
  positivity

theorem floor_pos {x : ℝ} (hx : 1 < x) : 0 < floor x := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x-1 := sub_pos.mpr hx
  unfold floor denominator
  positivity
end ActualTailVariation

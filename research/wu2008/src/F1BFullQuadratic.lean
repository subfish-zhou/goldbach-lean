import F1BFullPartial

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1JointFTC
namespace F1BFullFTC

/-- The original radical primitive on its needed positive domain. -/
theorem quadratic_positive_deriv (f g : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (quadraticPrimitive f g) ((f*x+g)/(x^2+16*x+4)) x := by
  have hm : 0 < x+8-root := by linarith only [hx,root_lt_eight]
  have hp : 0 < x+8+root := by linarith only [hx,root_pos]
  have hq : 0 < x^2+16*x+4 := by positivity
  have hd : HasDerivAt (fun t : ℝ => t^2+16*t+4) (2*x+16) x := by
    convert (((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul 16)).add_const 4 using 1 <;>
      first | rfl | (dsimp; ring)
  have hl := (hasDerivAt_log hq.ne').comp x hd
  have hm' := (hasDerivAt_log hm.ne').comp x
    (((hasDerivAt_id x).add_const 8).sub_const root)
  have hp' := (hasDerivAt_log hp.ne').comp x
    (((hasDerivAt_id x).add_const 8).add_const root)
  have hr : (x+8-root)⁻¹-(x+8+root)⁻¹=2*root/(x^2+16*x+4) := by
    have he : x^2+16*x+4=(x+8-root)*(x+8+root) := by nlinarith only [root_sq]
    rw [he]
    field_simp
    ring
  convert (hl.const_mul (f/2)).add ((hm'.sub hp').const_mul ((g-8*f)/(2*root))) using 1 <;>
    first | rfl | skip
  simp only [mul_one,hr]
  field_simp [root_pos.ne']
  ring

def quadPrimitiveOne (f g u : ℝ) : ℝ := quadraticPrimitive
  (f/21) (g/(1127/200)-f/21-f/(1127/200)) (21*(u+1)/(1127/200)+1)

def quadPrimitiveTwo (f g u : ℝ) : ℝ := quadraticPrimitive
  f (g/(1127/200)-f-f/(1127/200)) ((u+1)/(1127/200)+1)

theorem quadPrimitiveOne_deriv (f g : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (quadPrimitiveOne f g) ((f*u+g)/quadOne u) u := by
  have hx : 0 < 21*(u+1)/((1127:ℝ)/200)+1 := by linarith
  have h := (quadratic_positive_deriv (f/21) (g/(1127/200)-f/21-f/(1127/200)) hx).comp u
    ((((hasDerivAt_id u).add_const 1).const_mul 21).div_const (1127/200) |>.add_const 1)
  have he : (21*(u+1)/((1127:ℝ)/200)+1)^2+16*(21*(u+1)/(1127/200)+1)+4 =
      (21/(1127/200)^2)*quadOne u := by unfold quadOne; ring
  convert h using 1 <;> first | rfl | skip
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem quadPrimitiveTwo_deriv (f g : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (quadPrimitiveTwo f g) ((f*u+g)/quadTwo u) u := by
  have hx : 0 < (u+1)/((1127:ℝ)/200)+1 := by linarith
  have h := (quadratic_positive_deriv f (g/(1127/200)-f-f/(1127/200)) hx).comp u
    ((((hasDerivAt_id u).add_const 1).div_const (1127/200)).add_const 1)
  have he : ((u+1)/((1127:ℝ)/200)+1)^2+16*((u+1)/(1127/200)+1)+4 =
      (1/(1127/200)^2)*quadTwo u := by unfold quadTwo; ring
  convert h using 1 <;> first | rfl | skip
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end F1BFullFTC

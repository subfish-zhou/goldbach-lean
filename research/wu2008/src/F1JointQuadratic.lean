import F1JointPartial

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open scoped Interval
namespace F1JointFTC

/-- The radical is forced by the original quadratic denominator, not a domain split. -/
def root : ℝ := sqrt 60

theorem root_pos : 0 < root := by unfold root; positivity

theorem root_sq : root^2 = 60 := by unfold root; exact sq_sqrt (by norm_num)

theorem root_lt_eight : root < 8 := by nlinarith only [root_sq,root_pos]

def quadraticPrimitive (f g u : ℝ) : ℝ :=
  (f/2)*log (u^2+16*u+4)+((g-8*f)/(2*root))*
    (log (u+8-root)-log (u+8+root))

theorem quadraticPrimitive_deriv (f g : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (quadraticPrimitive f g) ((f*u+g)/(u^2+16*u+4)) u := by
  have hm : 0 < u+8-root := by linarith only [hu,root_lt_eight]
  have hp : 0 < u+8+root := by linarith only [hu,root_pos]
  have hq : 0 < u^2+16*u+4 := by positivity
  have he : (u+8-root)*(u+8+root)=u^2+16*u+4 := by nlinarith only [root_sq]
  have hr : 1/(u+8-root)-1/(u+8+root)=2*root/(u^2+16*u+4) := by
    rw [← he]
    field_simp
    ring
  have hlog1 := (hasDerivAt_log hm.ne').comp u
    (((hasDerivAt_id u).add_const 8).sub_const root)
  have hlog2 := (hasDerivAt_log hp.ne').comp u
    (((hasDerivAt_id u).add_const 8).add_const root)
  have hdq : HasDerivAt (fun t : ℝ => t^2+16*t+4) (2*u+16) u := by
    convert (((hasDerivAt_id u).pow 2).add ((hasDerivAt_id u).const_mul 16)).add_const 4 using 1 <;>
      first | rfl | (dsimp; ring)
  have hlogq := (hasDerivAt_log hq.ne').comp u hdq
  have h := (hlogq.const_mul (f/2)).add ((hlog1.sub hlog2).const_mul ((g-8*f)/(2*root)))
  convert h using 1 <;> first | rfl | skip
  simp only [mul_one]
  simp only [one_div] at hr
  rw [hr]
  field_simp [root_pos.ne']
  ring

end F1JointFTC

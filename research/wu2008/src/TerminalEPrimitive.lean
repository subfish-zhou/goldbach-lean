import TerminalEDivided
import FirstCRationalFTCBase

noncomputable section
namespace TerminalE
open Real FirstCRationalPayment

def radical : ℝ := sqrt 15
theorem radical_pos : 0 < radical := by unfold radical; positivity
theorem radical_sq : radical^2=15 := by unfold radical; exact sq_sqrt (by norm_num)
theorem radical_lt_four : radical<4 := by nlinarith only [radical_pos,radical_sq]

def quadraticPrimitive (A B x : ℝ) : ℝ :=
  (A/2)*log (q x)+((B-4*A)/(2*radical))*(log (x+4-radical)-log (x+4+radical))

theorem quadraticPrimitive_deriv (A B : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (quadraticPrimitive A B) ((A*x+B)/q x) x := by
  have hm : 0 < x+4-radical := by linarith only [hx,radical_lt_four]
  have hp : 0 < x+4+radical := by linarith only [hx,radical_pos]
  have hq : 0 < q x := by unfold q; positivity
  have he : (x+4-radical)*(x+4+radical)=q x := by
    unfold q
    nlinarith only [radical_sq]
  have hr : 1/(x+4-radical)-1/(x+4+radical)=2*radical/q x := by
    rw [← he]
    field_simp
    ring
  have hlog1 := (hasDerivAt_log hm.ne').comp x
    (((hasDerivAt_id x).add_const 4).sub_const radical)
  have hlog2 := (hasDerivAt_log hp.ne').comp x
    (((hasDerivAt_id x).add_const 4).add_const radical)
  have hdq : HasDerivAt q (2*x+8) x := by
    convert (((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul 8)).add_const 1 using 1 <;>
      first | rfl | (dsimp; ring)
  have hlogq := (hasDerivAt_log hq.ne').comp x hdq
  have hd := (hlogq.const_mul (A/2)).add ((hlog1.sub hlog2).const_mul ((B-4*A)/(2*radical)))
  convert hd using 1 <;> first | rfl | skip
  simp only [mul_one]
  simp only [one_div] at hr
  rw [hr]
  field_simp [radical_pos.ne']
  ring

def primitive (p x : ℝ) : ℝ :=
  mainCoeff p*log (x-p)+polePrimitive 0 (zeroOne p) (zeroTwo p) 0 x+
    polePrimitive (-1) (negOne p) (negTwo p) (negThree p) x-
    negFour p/(3*(x+1)^3)+quadraticPrimitive (quadOne p) (quadZero p) x

/-- A full primitive, including the original order-four pole and quadratic. -/
theorem primitive_deriv {p x : ℝ} (hp : 0 < p) (hx : 1 ≤ x) (hxp : x-p ≠ 0) :
    HasDerivAt (primitive p) (RemainingHf.basicLower x/(x-p)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hm := ((hasDerivAt_log hxp).comp x ((hasDerivAt_id x).sub_const p)).const_mul (mainCoeff p)
  have hz := polePrimitive_hasDerivAt 0 (zeroOne p) (zeroTwo p) 0 x (by simpa using hx0)
  have hn := polePrimitive_hasDerivAt (-1) (negOne p) (negTwo p) (negThree p) x
    (by simpa using hx1)
  have hf := ((((hasDerivAt_id x).add_const 1).pow 3).inv (pow_ne_zero 3 hx1)).const_mul (negFour p/3)
  have hq := quadraticPrimitive_deriv (quadOne p) (quadZero p) hx
  rw [divided_partial hp hx hxp]
  convert (((hm.add hz).add hn).sub hf).add hq using 1 <;> first | rfl | skip
  · funext t
    dsimp [primitive]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp [dividedPartial,poleKernel]
    simp only [sub_zero,sub_neg_eq_add,zero_div,add_zero,mul_one]
    field_simp
    ring

end TerminalE

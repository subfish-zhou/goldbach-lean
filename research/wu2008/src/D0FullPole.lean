import TerminalEPrimitive

noncomputable section
namespace D0FullDensity
open Real TerminalE FirstCRationalPayment
local notation "te" => TerminalE.e

/-- The actual nonzero-pole domain, including the forced negative pole. -/
theorem divided_partial {p x : ℝ} (hp : p ≠ 0) (hp1 : p+1 ≠ 0)
    (hqp : q p ≠ 0) (hx : 1 ≤ x) (hxp : x-p ≠ 0) :
    RemainingHf.basicLower x/(x-p)=dividedPartial p x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hqx : q x ≠ 0 := by unfold q; positivity
  have hz := pole_division a b 0 0 p x hp hx0 hxp
  have hn := pole_division c d te f (p+1) (x+1) hp1 hx1
    (by simpa only [add_sub_add_right_eq_sub] using hxp)
  have hq := quadratic_division p x hqp hqx hxp
  rw [basic_partial hx]
  dsimp [basicPartial,dividedPartial,mainCoeff,zeroOne,zeroTwo,negOne,negTwo,negThree,negFour]
  simp only [add_sub_add_right_eq_sub,zero_div,add_zero,sub_zero] at hz hn
  simp only [add_div]
  linear_combination hz+hn+hq

theorem primitive_deriv {p x : ℝ} (hp : p ≠ 0) (hp1 : p+1 ≠ 0)
    (hqp : q p ≠ 0) (hx : 1 ≤ x) (hxp : x-p ≠ 0) :
    HasDerivAt (primitive p) (RemainingHf.basicLower x/(x-p)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hm := ((hasDerivAt_log hxp).comp x ((hasDerivAt_id x).sub_const p)).const_mul (mainCoeff p)
  have hz := polePrimitive_hasDerivAt 0 (zeroOne p) (zeroTwo p) 0 x (by simpa using hx0)
  have hn := polePrimitive_hasDerivAt (-1) (negOne p) (negTwo p) (negThree p) x
    (by simpa using hx1)
  have hf := ((((hasDerivAt_id x).add_const 1).pow 3).inv (pow_ne_zero 3 hx1)).const_mul (negFour p/3)
  have hq := quadraticPrimitive_deriv (quadOne p) (quadZero p) hx
  rw [divided_partial hp hp1 hqp hx hxp]
  convert (((hm.add hz).add hn).sub hf).add hq using 1 <;> first | rfl | skip
  · funext t
    dsimp [primitive]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp [dividedPartial,poleKernel]
    simp only [sub_zero,sub_neg_eq_add,zero_div,add_zero,mul_one]
    field_simp
    ring

/-- Coalescing the forced pole at zero retains the order-three principal part. -/
def zeroPartial (x : ℝ) : ℝ :=
  (k+c+d+te+f+h)/x+a/x^2+b/x^3+
  (-c-d-te-f)/(x+1)+(-d-te-f)/(x+1)^2+(-te-f)/(x+1)^3-f/(x+1)^4+
  ((-h)*x+(g-8*h))/q x

theorem zero_partial {x : ℝ} (hx : 1 ≤ x) :
    RemainingHf.basicLower x/x=zeroPartial x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hqx : q x ≠ 0 := by unfold q; positivity
  rw [basic_partial hx]
  unfold basicPartial zeroPartial
  field_simp
  unfold q
  ring

def zeroPrimitive (x : ℝ) : ℝ :=
  polePrimitive 0 (k+c+d+te+f+h) a b x+
  polePrimitive (-1) (-c-d-te-f) (-d-te-f) (-te-f) x+
  f/(3*(x+1)^3)+quadraticPrimitive (-h) (g-8*h) x

theorem zeroPrimitive_deriv {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt zeroPrimitive (RemainingHf.basicLower x/x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hz := polePrimitive_hasDerivAt 0 (k+c+d+te+f+h) a b x (by simpa using hx0)
  have hn := polePrimitive_hasDerivAt (-1) (-c-d-te-f) (-d-te-f) (-te-f) x
    (by simpa using hx1)
  have hf := ((((hasDerivAt_id x).add_const 1).pow 3).inv (pow_ne_zero 3 hx1)).const_mul (f/3)
  have hq := quadraticPrimitive_deriv (-h) (g-8*h) hx
  rw [zero_partial hx]
  convert (((hz.add hn).add hf).add hq) using 1 <;> first | rfl | skip
  · funext t
    dsimp [zeroPrimitive]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp [zeroPartial,poleKernel]
    simp only [sub_zero,sub_neg_eq_add,mul_one]
    field_simp
    ring

end D0FullDensity

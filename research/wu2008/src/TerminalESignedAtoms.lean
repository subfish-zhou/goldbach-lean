import TerminalECells

noncomputable section
namespace TerminalESigned
open Real TerminalE

def minusCoeff (p : ℝ) : ℝ := quadOne p/2+(quadZero p-4*quadOne p)/(2*radical)
def plusCoeff (p : ℝ) : ℝ := quadOne p/2-(quadZero p-4*quadOne p)/(2*radical)
def rationalPart (p x : ℝ) : ℝ :=
  -zeroTwo p/x-negTwo p/(x+1)-negThree p/(2*(x+1)^2)-negFour p/(3*(x+1)^3)

theorem quadratic_split {x : ℝ} (hx : 1 ≤ x) (A B : ℝ) :
    quadraticPrimitive A B x =
      (A/2+(B-4*A)/(2*radical))*log (x+4-radical)+
      (A/2-(B-4*A)/(2*radical))*log (x+4+radical) := by
  have hm : 0<x+4-radical := by linarith only [hx,radical_lt_four]
  have hp : 0<x+4+radical := by linarith only [hx,radical_pos]
  have he : q x=(x+4-radical)*(x+4+radical) := by
    unfold q
    nlinarith only [radical_sq]
  unfold quadraticPrimitive
  rw [he,log_mul hm.ne' hp.ne']
  ring

theorem primitive_expansion {x : ℝ} (hx : 1 ≤ x) (p : ℝ) :
    primitive p x = rationalPart p x+mainCoeff p*log (x-p)+zeroOne p*log x+
      negOne p*log (x+1)+minusCoeff p*log (x+4-radical)+
      plusCoeff p*log (x+4+radical) := by
  unfold primitive
  rw [quadratic_split hx]
  unfold rationalPart minusCoeff plusCoeff FirstCRationalPayment.polePrimitive
  simp only [sub_zero,sub_neg_eq_add,zero_div,sub_zero]
  ring

/-- Positive affine arguments give natural, forward endpoint quotients. -/
theorem affine_ratio {a b A B : ℝ} (ha : 0<A*a+B) (hA : 0≤A) (hab : a≤b) :
    0<A*b+B ∧ 1≤(A*b+B)/(A*a+B) := by
  have hm : A*a+B≤A*b+B := by nlinarith only [mul_nonneg hA (sub_nonneg.mpr hab)]
  exact ⟨ha.trans_le hm,(one_le_div ha).mpr hm⟩

/-- The pole at two is negative at both endpoints; its positive quotient decreases. -/
theorem right_negative_quotient {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    log (rightArg b-2)-log (rightArg a-2) = -log ((b+3)/(a+3)) := by
  have ha3 : a+3 ≠ 0 := by linarith
  have hb3 : b+3 ≠ 0 := by linarith
  have he (u : ℝ) (hu : u+3 ≠ 0) : rightArg u-2= -4/(u+3) := by
    unfold rightArg
    field_simp
    ring
  rw [he b hb3,he a ha3,log_div (by norm_num : (-4:ℝ) ≠ 0) hb3,
    log_div (by norm_num : (-4:ℝ) ≠ 0) ha3,log_div hb3 ha3]
  ring

/-- A reciprocal is used only to orient an existing endpoint quotient. -/
theorem signed_inverse {x : ℝ} (hx : 0<x) (hx1 : x≤1) (c : ℝ) :
    RemainingHf.signed (-c) x⁻¹ ≤ c*log x := by
  have hi : 1≤x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have h := RemainingHf.signed_le (-c) hi
  rw [log_inv] at h
  nlinarith only [h]
end TerminalESigned

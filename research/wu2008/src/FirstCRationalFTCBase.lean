import FirstIntegralRational

noncomputable section
open Real Set MeasureTheory
open scoped Interval
namespace FirstCRationalPayment

/-- Primitive of a principal part with the fixed maximal pole multiplicity three. -/
def polePrimitive (a c₁ c₂ c₃ u : ℝ) : ℝ :=
  c₁ * log (u-a) - c₂ / (u-a) - c₃ / (2*(u-a)^2)

def poleKernel (a c₁ c₂ c₃ u : ℝ) : ℝ :=
  c₁ / (u-a) + c₂ / (u-a)^2 + c₃ / (u-a)^3

theorem polePrimitive_hasDerivAt (a c₁ c₂ c₃ u : ℝ) (h : u-a ≠ 0) :
    HasDerivAt (polePrimitive a c₁ c₂ c₃) (poleKernel a c₁ c₂ c₃ u) u := by
  have hd := (hasDerivAt_id u).sub_const a
  have hl := (Real.hasDerivAt_log h).comp u hd
  have hi := hd.inv h
  have hp := (hd.pow 2).inv (pow_ne_zero 2 h)
  have hh := ((hl.const_mul c₁).sub (hi.const_mul c₂)).sub (hp.const_mul (c₃/2))
  convert hh using 1 <;> first
  | rfl
  | (funext x
     simp only [polePrimitive, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply,
       Function.comp_apply, id_eq, div_eq_mul_inv, mul_inv_rev]
     ring)
  | (dsimp [poleKernel]; field_simp; ring)

end FirstCRationalPayment

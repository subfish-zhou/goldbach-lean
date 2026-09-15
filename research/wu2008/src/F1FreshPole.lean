import F1FreshMass

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
namespace F1FreshFTC

/-- The fourth principal part is forced by the original residual density. -/
def pole4 (a c₁ c₂ c₃ c₄ u : ℝ) : ℝ :=
  polePrimitive a c₁ c₂ c₃ u-c₄/(3*(u-a)^3)

theorem pole4_deriv (a c₁ c₂ c₃ c₄ u : ℝ) (h : u-a ≠ 0) :
    HasDerivAt (pole4 a c₁ c₂ c₃ c₄)
      (poleKernel a c₁ c₂ c₃ u+c₄/(u-a)^4) u := by
  have hp := ((((hasDerivAt_id u).sub_const a).pow 3).inv (pow_ne_zero 3 h)).const_mul (c₄/3)
  convert (polePrimitive_hasDerivAt a c₁ c₂ c₃ u h).sub hp using 1 <;> first
  | rfl
  | (funext x; simp only [pole4, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply,
       id_eq, div_eq_mul_inv, mul_inv_rev]; ring)
  | (dsimp; field_simp; ring)

end F1FreshFTC

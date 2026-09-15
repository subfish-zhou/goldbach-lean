import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrimitiveRootNumberNorm

open Complex

namespace DirichletCharacter

/-- A multiplicative quadratic character is self-inverse. -/
theorem inv_eq_self_of_sq_eq_one {N : ℕ} {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) :
    χ⁻¹ = χ :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hquad)

variable {N : ℕ} [NeZero N]

/-- The primitive functional equation specialized to a quadratic character. -/
theorem IsPrimitive.completedLFunction_one_sub_quadratic
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hquad : χ ^ 2 = 1) (s : ℂ) :
    χ.completedLFunction (1 - s) =
      N ^ (s - 1 / 2) * χ.rootNumber * χ.completedLFunction s := by
  rw [hχ.completedLFunction_one_sub, inv_eq_self_of_sq_eq_one hquad]

/-- The root number in the primitive quadratic lane has norm one. -/
theorem IsPrimitive.norm_rootNumber_of_quadratic
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (_hquad : χ ^ 2 = 1) :
    ‖χ.rootNumber‖ = 1 :=
  hχ.norm_rootNumber

end DirichletCharacter
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex Finset ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-!
`gaussSum_mul_gaussSum_eq_card` in this pinned Mathlib is restricted to a finite-field
source, so it cannot be specialized to `ZMod N` for a general conductor. The following is
the exact `ZMod N` analogue needed here, obtained from `ZMod.dft_dft`; the proof of Fourier
inversion itself uses `ZMod.isPrimitive_stdAddChar`. Thus this pays the same Gauss-sum
cardinality identity without adding a primality hypothesis on `N`.
-/

private lemma primitive_gaussSum_mul_inv_eq_card
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  have hDFT := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) 1
  rw [ZMod.dft_apply] at hDFT
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum] at hDFT
  have hsum :
      (∑ j : ZMod N, stdAddChar (-j) * (χ⁻¹ (-j) * gaussSum χ stdAddChar)) =
        gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar := by
    calc
      _ = ∑ j : ZMod N, χ⁻¹ j * stdAddChar j * gaussSum χ stdAddChar := by
        refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j ↦ ?_
        simp only [Equiv.neg_apply]
        ring
      _ = (∑ j : ZMod N, χ⁻¹ j * stdAddChar j) * gaussSum χ stdAddChar := by
        rw [Finset.sum_mul]
      _ = gaussSum χ⁻¹ stdAddChar * gaussSum χ stdAddChar := rfl
      _ = _ := mul_comm _ _
  have hDFT' :
      (∑ j : ZMod N, stdAddChar (-j) * (χ⁻¹ (-j) * gaussSum χ stdAddChar)) =
        (N : ℂ) * χ (-1) := by
    simpa [smul_eq_mul] using hDFT
  rw [hsum] at hDFT'
  simpa [mul_comm] using hDFT'

private lemma primitive_norm_gaussSum_sq
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
  let g := gaussSum χ stdAddChar
  have hstar : star g = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [show star g = gaussSum χ⁻¹ stdAddChar⁻¹ by
      exact star_gaussSum_eq χ stdAddChar]
    rw [AddChar.inv_mulShift]
    simpa using
      (gaussSum_mulShift_eq χ⁻¹ stdAddChar (-1 : (ZMod N)ˣ))
  have hprod := primitive_gaussSum_mul_inv_eq_card hχ
  have hnormSq : Complex.normSq g = N := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    change star g * g = (N : ℂ)
    rw [hstar]
    calc
      χ (-1) * gaussSum χ⁻¹ stdAddChar * g =
          χ (-1) * (g * gaussSum χ⁻¹ stdAddChar) := by ring
      _ = χ (-1) * (χ (-1) * N) := by rw [hprod]
      _ = (χ (-1) * χ (-1)) * N := by ring
      _ = N := by rw [← map_mul]; norm_num
  rw [Complex.sq_norm, hnormSq]

/-- The functional-equation root number of a primitive Dirichlet character has norm one. -/
theorem IsPrimitive.norm_rootNumber {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖χ.rootNumber‖ = 1 := by
  rcases eq_or_ne N 1 with rfl | _hN
  · rw [rootNumber_modOne, norm_one]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hgauss_sq : ‖gaussSum χ stdAddChar‖ ^ 2 = (N : ℝ) :=
    primitive_norm_gaussSum_sq hχ
  have hgauss : ‖gaussSum χ stdAddChar‖ = Real.sqrt N := by
    nlinarith [Real.sq_sqrt (le_of_lt hNpos), norm_nonneg (gaussSum χ stdAddChar),
      Real.sqrt_nonneg (N : ℝ)]
  have hcpow : (N : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt N : ℂ) := by
    calc
      (N : ℂ) ^ (1 / 2 : ℂ) = (N : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by norm_num
      _ = (((N : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (le_of_lt hNpos) (1 / 2 : ℝ)).symm
      _ = (Real.sqrt N : ℂ) := by rw [Real.sqrt_eq_rpow]
  rw [rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, hcpow,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hgauss]
  field_simp [Real.sqrt_ne_zero'.mpr hNpos]

end DirichletCharacter

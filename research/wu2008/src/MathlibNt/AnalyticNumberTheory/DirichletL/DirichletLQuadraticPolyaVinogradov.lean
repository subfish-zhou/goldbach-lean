import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrimitiveRootNumberNorm
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Fourier completion for primitive quadratic character sums

This file records the finite Fourier identity underlying the quadratic
Pólya--Vinogradov estimate.  In particular, the Gauss factor is paid from the
proved primitive root-number norm, rather than postulated as an extra bound.
-/

open Complex Finset ZMod

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The Gauss sum of a primitive character modulo `q` has norm `sqrt q`.
This is extracted from the already proved unit norm of the root number. -/
theorem IsPrimitive.norm_gaussSum_stdAddChar
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (_hq : 1 < q) :
    ‖gaussSum χ stdAddChar‖ = Real.sqrt q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hpow : (q : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt q : ℂ) := by
    calc
      (q : ℂ) ^ (1 / 2 : ℂ) = (q : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by norm_num
      _ = (((q : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (le_of_lt hqpos) (1 / 2 : ℝ)).symm
      _ = (Real.sqrt q : ℂ) := by rw [Real.sqrt_eq_rpow]
  have hr := hχ.norm_rootNumber
  rw [rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow,
    hpow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hr
  have hsqrt : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hqpos
  field_simp [hsqrt] at hr
  exact hr

/-- Exact finite Fourier completion of a primitive character prefix.  The
zero frequency vanishes automatically through `χ⁻¹ 0 = 0`; retaining it makes
the identity canonical and avoids a choice of integer representatives. -/
theorem IsPrimitive.sum_range_fourier_completion
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (M : ℕ) :
    (∑ n ∈ range M, χ (n : ZMod q)) =
      (q : ℂ)⁻¹ * gaussSum χ stdAddChar *
        ∑ j : ZMod q, χ⁻¹ (-j) *
          ∑ n ∈ range M, stdAddChar (j * (n : ZMod q)) := by
  have hinv (n : ℕ) :
      χ (n : ZMod q) = (q : ℂ)⁻¹ *
        ∑ j : ZMod q, stdAddChar (j * (n : ZMod q)) *
          (χ⁻¹ (-j) * gaussSum χ stdAddChar) := by
    have hdft (j : ZMod q) :
        ZMod.dft (χ : ZMod q → ℂ) j = χ⁻¹ (-j) * gaussSum χ stdAddChar :=
      hχ.fourierTransform_eq_inv_mul_gaussSum j
    have hi := congrArg (fun f : ZMod q → ℂ => f (n : ZMod q))
      (ZMod.dft.symm_apply_apply (χ : ZMod q → ℂ))
    rw [ZMod.invDFT_apply] at hi
    simp only [hdft, smul_eq_mul] at hi
    exact hi.symm
  simp_rw [hinv]
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    (q : ℂ)⁻¹ * ∑ j : ZMod q, ∑ n ∈ range M,
        stdAddChar (j * (n : ZMod q)) * (χ⁻¹ (-j) * gaussSum χ stdAddChar) =
        (q : ℂ)⁻¹ * gaussSum χ stdAddChar *
          ∑ j : ZMod q, χ⁻¹ (-j) *
            ∑ n ∈ range M, stdAddChar (j * (n : ZMod q)) := by
      rw [mul_assoc]
      apply congrArg ((q : ℂ)⁻¹ * ·)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Norm form of Fourier completion.  This isolates the sole remaining
Pólya--Vinogradov input as the `L¹` norm of the finite geometric kernels; the
Gauss sum has already been replaced by `sqrt q`. -/
theorem IsPrimitive.norm_sum_range_le_sqrt_mul_fourierKernelL1
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤
      Real.sqrt q / q *
        ∑ j : ZMod q, ‖∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖ := by
  rw [hχ.sum_range_fourier_completion M, norm_mul, norm_mul,
    hχ.norm_gaussSum_stdAddChar hq]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqnorm : ‖((q : ℂ)⁻¹)‖ = ((q : ℝ)⁻¹) := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hqnorm]
  calc
    (q : ℝ)⁻¹ * Real.sqrt q *
        ‖∑ j : ZMod q, χ⁻¹ (-j) *
          ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖
        ≤ (q : ℝ)⁻¹ * Real.sqrt q *
          ∑ j : ZMod q, ‖χ⁻¹ (-j) *
            ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (q : ℝ)⁻¹ * Real.sqrt q *
          ∑ j : ZMod q, ‖∑ n ∈ range M,
            stdAddChar (j * (n : ZMod q))‖ := by
      gcongr
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (DirichletCharacter.norm_le_one χ⁻¹ (-j))
    _ = Real.sqrt q / q *
          ∑ j : ZMod q, ‖∑ n ∈ range M,
            stdAddChar (j * (n : ZMod q))‖ := by
      rw [div_eq_mul_inv]
      ring

end DirichletCharacter
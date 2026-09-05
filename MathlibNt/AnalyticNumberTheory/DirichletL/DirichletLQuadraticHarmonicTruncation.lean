import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConjugation

/-!
# Real harmonic truncations for quadratic Dirichlet L-values

This module turns the natural-order Abel theory into a finite, real-valued
approximation to `L(1, χ)`.  It is the first elementary reduction used in the
large-conductor Landau--Siegel argument: after this point the missing input is
a lower bound for an explicit finite quadratic-character harmonic sum.
-/

open Complex Finset

namespace DirichletCharacter

open DirichletLAbelWeightVariation DirichletLConditionalValueSeries

variable {q : ℕ} [NeZero q]

/-- The real harmonic truncation of a Dirichlet character at `m`.  Keeping the
finite sum in `cpowWeight` form makes its relation with the already established
natural-order conditional series literal. -/
noncomputable def quadraticHarmonicTruncation
    (χ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  (∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n).re

/-- A finite harmonic truncation of a quadratic character is itself real as a
complex number.  This uses the pointwise quadratic reality of the character,
not positivity of `L(1, χ)`. -/
theorem quadratic_harmonic_sum_im_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (m : ℕ) :
    (∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n).im = 0 := by
  let S : ℂ := ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n
  have hstar : starRingEnd ℂ S = S := by
    dsimp [S]
    simpa using
      (conj_sum_range_cpowWeight_character_of_sq_eq_one χ hquad (1 : ℂ) m)
  have him := congrArg Complex.im hstar
  rw [Complex.conj_im] at him
  linarith

/-- Abel truncation at the real point `1`: the error in approximating a
nonprincipal Dirichlet L-value by its first `m` natural terms is at most
`2q/m`. -/
theorem norm_LFunction_one_sub_harmonic_sum_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {m : ℕ} (hm : 1 ≤ m) :
    ‖χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n‖ ≤
      2 * (q : ℝ) / (m : ℝ) := by
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ hχ (1 : ℂ) (by norm_num) hm
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ (1 : ℂ) (by norm_num)] at htail
  calc
    _ ≤ (q : ℝ) * ((m : ℝ)⁻¹ + (m : ℝ)⁻¹) := by
      simpa [Real.rpow_neg_one] using htail
    _ = 2 * (q : ℝ) / (m : ℝ) := by
      rw [div_eq_mul_inv]
      ring

/-- Real form of the quadratic harmonic truncation theorem.  It exposes the
precise finite inequality that a classical large-conductor Siegel argument
must strengthen: any lower bound for the displayed finite sum transfers to
`Re L(1, χ)` with the explicit loss `2q/m`. -/
theorem abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
      2 * (q : ℝ) / (m : ℝ) := by
  have hnorm := norm_LFunction_one_sub_harmonic_sum_le χ hχ hm
  have hre := Complex.abs_re_le_norm
    (χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n)
  have hre' :
      |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
        ‖χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n‖ := by
    simpa [quadraticHarmonicTruncation] using hre
  exact hre'.trans hnorm

/-- One-sided transfer from a finite harmonic-sum estimate to `L(1, χ)`.
This is convenient for the next large-conductor lower-bound module. -/
theorem quadraticHarmonicTruncation_sub_error_le_LFunction_one_re
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    quadraticHarmonicTruncation χ m - 2 * (q : ℝ) / (m : ℝ) ≤
      (χ.LFunction 1).re := by
  have h := abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le
    χ hχ hm
  rw [abs_le] at h
  linarith

end DirichletCharacter
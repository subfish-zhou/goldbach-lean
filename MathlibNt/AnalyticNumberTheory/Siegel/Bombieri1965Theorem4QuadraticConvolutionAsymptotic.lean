import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelTotalDiscrepancy

/-!
# The actual one-character convolution main term

The floor-sum discrepancy and the genuine harmonic tail give a uniform
`O(q sqrt X)` error for the summatory convolution `1 * chi`. This is an
unconditional arithmetic input to the weighted positive-convolution route,
not a lower-bound assumption on `L(1, chi)`.
-/

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open Complex Finset DirichletCharacter

private theorem polyaVinogradov_budget_le_twentyfour_mul (q : ℕ) (hq : 1 ≤ q) :
    8 * Real.sqrt q * (1 + Real.log q) ≤ 24 * q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlogs := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (by positivity)] at hlogs
  have hsle : Real.sqrt (q : ℝ) ≤ q :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hsq := Real.sq_sqrt (Nat.cast_nonneg q)
  have hprod := mul_le_mul_of_nonneg_left
    (show 1 + Real.log (q : ℝ) ≤ 1 + 2 * Real.sqrt q by linarith) hs.le
  nlinarith

private theorem div_natSqrt_le_three_mul_sqrt {X : ℕ} (hX : 1 ≤ X) :
    (X : ℝ) / (X.sqrt : ℝ) ≤ 3 * Real.sqrt X := by
  have hm : 1 ≤ X.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hmR : (1 : ℝ) ≤ X.sqrt := by exact_mod_cast hm
  have hmsq : (X.sqrt : ℝ) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hmlt : (X : ℝ) ≤ (X.sqrt : ℝ) * X.sqrt + X.sqrt + X.sqrt := by
    exact_mod_cast Nat.sqrt_le_add X
  have hmle : (X.sqrt : ℝ) ≤ Real.sqrt X :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hmsq
  have hdiv : (X : ℝ) / (X.sqrt : ℝ) ≤ (X.sqrt : ℝ) + 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < X.sqrt)]
    nlinarith
  exact hdiv.trans (by nlinarith)

/-- Uniform main-term estimate for the real convolution summatory function.
Quadraticity is not needed for the error estimate itself; it makes the
coefficients nonnegative when this is used in the Siegel argument. -/
theorem IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (X : ℕ) :
    |quadraticSiegelConvolutionSummatory χ X - (X : ℝ) * (χ.LFunction 1).re| ≤
      79 * q * Real.sqrt X := by
  have hq : 1 < q := by
    have hq0 := NeZero.ne q
    have hq1 : q ≠ 1 := by
      rintro rfl
      exact hχ (Subsingleton.elim _ _)
    omega
  rcases X.eq_zero_or_pos with rfl | hX
  · simp [quadraticSiegelConvolutionSummatory]
  have hm : 1 ≤ X.sqrt := Nat.sqrt_pos.mpr hX
  have hdisc := hprim.abs_quadraticSiegelConvolutionDiscrepancy_le
    hq hm (Nat.sqrt_le_self X)
  have htail := abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le χ hχ hm
  have hPV := polyaVinogradov_budget_le_twentyfour_mul q (by omega)
  have hdiv := div_natSqrt_le_three_mul_sqrt (show 1 ≤ X by omega)
  have hmle : (X.sqrt : ℝ) ≤ Real.sqrt X :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by
      exact_mod_cast Nat.sqrt_le' X)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  calc
    _ = |quadraticSiegelConvolutionDiscrepancy χ X X.sqrt +
        (X : ℝ) * (quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re)| := by
      congr 1
      unfold quadraticSiegelConvolutionDiscrepancy
      ring
    _ ≤ |quadraticSiegelConvolutionDiscrepancy χ X X.sqrt| +
        (X : ℝ) * |quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re| := by
      simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X)] using
        abs_add_le (quadraticSiegelConvolutionDiscrepancy χ X X.sqrt)
          ((X : ℝ) * (quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re))
    _ ≤ (X.sqrt : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / X.sqrt : ℕ) : ℝ) +
        (X : ℝ) * (2 * (q : ℝ) / (X.sqrt : ℝ)) := by
      gcongr
      simpa only [abs_sub_comm] using htail
    _ ≤ Real.sqrt X + (24 * q) * ((X : ℝ) / (X.sqrt : ℝ)) +
        (X : ℝ) * (2 * (q : ℝ) / (X.sqrt : ℝ)) := by
      gcongr
      exact Nat.cast_div_le
    _ = Real.sqrt X + (26 * q) * ((X : ℝ) / (X.sqrt : ℝ)) := by ring
    _ ≤ Real.sqrt X + (26 * q) * (3 * Real.sqrt X) := by gcongr
    _ ≤ 79 * q * Real.sqrt X := by
      nlinarith [Real.sqrt_nonneg (X : ℝ)]

/-- Real-endpoint version, with the floor error paid by the actual harmonic
tail estimate at one. This is the summatory input for partial summation. -/
theorem IsPrimitive.abs_quadratic_convolution_floor_sub_LValue_main_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    |quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ - x * (χ.LFunction 1).re| ≤
      81 * q * Real.sqrt x := by
  have hmain := IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le χ hprim hχ ⌊x⌋₊
  have htail := norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := 1) (by norm_num)
  have hnorm : ‖χ.LFunction 1‖ ≤ 2 * q := by
    simpa [DirichletLAbelWeightVariation.cpowWeight] using htail
  have hL : |(χ.LFunction 1).re| ≤ 2 * q := (Complex.abs_re_le_norm _).trans hnorm
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have herror : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.lt_floor_add_one x]
  have hsqrt : Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hfloor
  have hsqrt1 : 1 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hx)
  calc
    _ = |(quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re) +
        ((⌊x⌋₊ : ℝ) - x) * (χ.LFunction 1).re| := by congr 1; ring
    _ ≤ |quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re| +
        |(⌊x⌋₊ : ℝ) - x| * |(χ.LFunction 1).re| := by
      simpa only [abs_mul] using
        abs_add_le (quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re)
          (((⌊x⌋₊ : ℝ) - x) * (χ.LFunction 1).re)
    _ ≤ 79 * q * Real.sqrt (⌊x⌋₊ : ℝ) + 1 * (2 * q) := by gcongr
    _ ≤ 79 * q * Real.sqrt x + 1 * (2 * q) := by gcongr
    _ ≤ 81 * q * Real.sqrt x := by nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

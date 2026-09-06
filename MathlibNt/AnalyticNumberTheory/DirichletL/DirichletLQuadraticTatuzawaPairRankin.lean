import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelRankinBarrier

/-!
# The two-character Rankin layer in Tatuzawa's argument

For quadratic characters `χ₁` and `χ₂` (possibly of different moduli), this
module forms the genuine Dirichlet-convolution coefficient sequence

`(ζ * χ₁) * (ζ * χ₂)`.

Its coefficients are nonnegative, every nonzero square has coefficient at
least one, and in `Re s > 1` its L-series factors exactly as

`(ζ(s)L(s,χ₁)) (ζ(s)L(s,χ₂))`.

Consequently the square support gives a source-free lower bound for the
product `|L(σ,χ₁)L(σ,χ₂)|`.  This is the two-character positivity/Rankin
bearing layer used before any Deuring--Heilbronn transfer to `s = 1`.
It deliberately does not postulate that missing transfer as a source.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped LSeries.notation BigOperators ComplexOrder Real

namespace DirichletCharacter

variable {q₁ q₂ : ℕ}

/-- The biquadratic Rankin coefficient sequence
`(ζ * χ₁) * (ζ * χ₂)`. -/
noncomputable def tatuzawaPairCoefficient
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    ArithmeticFunction ℂ :=
  χ₁.zetaMul * χ₂.zetaMul

private lemma zetaMul_one_pair (χ : DirichletCharacter ℂ q₁) :
    χ.zetaMul 1 = 1 := by
  rw [zetaMul, coe_zeta_mul_apply]
  norm_num [toArithmeticFunction]

/-- Quadraticity makes every coefficient of the two-character product
nonnegative in the real-axis order on `ℂ`. -/
theorem tatuzawaPairCoefficient_nonneg
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ tatuzawaPairCoefficient χ₁ χ₂ n := by
  rw [tatuzawaPairCoefficient, ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun d _ =>
    mul_nonneg (zetaMul_nonneg h₁ d.1) (zetaMul_nonneg h₂ d.2)

/-- Every nonzero square occurs with coefficient at least one.  The proof
retains the antidiagonal cell `(m²,1)` and uses the square lower bound in the
first quadratic factor. -/
theorem one_le_tatuzawaPairCoefficient_sq
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1)
    {m : ℕ} (hm : m ≠ 0) :
    (1 : ℂ) ≤ tatuzawaPairCoefficient χ₁ χ₂ (m ^ 2) := by
  rw [tatuzawaPairCoefficient, ArithmeticFunction.mul_apply]
  have hmem : (m ^ 2, 1) ∈ (m ^ 2).divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by simp, pow_ne_zero 2 hm⟩
  have hterm : χ₁.zetaMul (m ^ 2) * χ₂.zetaMul 1 = χ₁.zetaMul (m ^ 2) := by
    rw [zetaMul_one_pair]
    simp
  calc
    (1 : ℂ) ≤ χ₁.zetaMul (m ^ 2) := by
      rw [RCLike.le_iff_re_im]
      exact ⟨one_le_quadraticSiegelConvolution_sq h₁ hm,
        (zetaMul_im_eq_zero_of_sq_eq_one χ₁ h₁ _).symm⟩
    _ = χ₁.zetaMul (m ^ 2) * χ₂.zetaMul 1 := hterm.symm
    _ ≤ ∑ d ∈ (m ^ 2).divisorsAntidiagonal,
        χ₁.zetaMul d.1 * χ₂.zetaMul d.2 := by
      exact Finset.single_le_sum
        (fun d _ => mul_nonneg (zetaMul_nonneg h₁ d.1) (zetaMul_nonneg h₂ d.2)) hmem

/-- Absolute convergence of the two-character Rankin series in `Re s > 1`. -/
theorem tatuzawaPairCoefficient_summable
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (tatuzawaPairCoefficient χ₁ χ₂) s := by
  exact ArithmeticFunction.LSeriesSummable_mul
    (χ₁.LSeriesSummable_zetaMul hs) (χ₂.LSeriesSummable_zetaMul hs)

/-- Exact two-character factorization in the half-plane of absolute
convergence. -/
theorem tatuzawaPairCoefficient_factorization
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    [NeZero q₁] [NeZero q₂] {s : ℂ} (hs : 1 < s.re) :
    LSeries (tatuzawaPairCoefficient χ₁ χ₂) s =
      (riemannZeta s * χ₁.LFunction s) *
        (riemannZeta s * χ₂.LFunction s) := by
  rw [tatuzawaPairCoefficient, ArithmeticFunction.LSeries_mul'
    (χ₁.LSeriesSummable_zetaMul hs) (χ₂.LSeriesSummable_zetaMul hs)]
  rw [← riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ₁ hs,
    ← riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ₂ hs]

lemma tatuzawaPair_term_re_eq
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    {σ : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re =
      (tatuzawaPairCoefficient χ₁ χ₂ n).re / (n : ℝ) ^ σ := by
  rw [LSeries.term, if_neg hn]
  have hcpow : (n : ℂ) ^ (σ : ℂ) = ((n : ℝ) ^ σ : ℝ) := by
    symm
    exact Complex.ofReal_cpow (Nat.cast_nonneg n) σ
  rw [hcpow]
  simp

lemma tatuzawaPair_term_re_nonneg
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {σ : ℝ} (n : ℕ) :
    0 ≤ (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [tatuzawaPair_term_re_eq χ₁ χ₂ hn]
    have hc := tatuzawaPairCoefficient_nonneg χ₁ χ₂ h₁ h₂ n
    rw [RCLike.le_iff_re_im] at hc
    exact div_nonneg hc.1 (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- The finite square-support Rankin lower bound for the genuine pair
coefficient. -/
theorem tatuzawaPair_square_lower
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    [NeZero q₁] [NeZero q₂]
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1)
    (M : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ 2 : ℕ) : ℝ) ^ σ ≤
      (LSeries (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ)).re := by
  let X := M ^ 2
  have hsum := tatuzawaPairCoefficient_summable χ₁ χ₂
    (show 1 < (σ : ℂ).re by simpa using hσ)
  have hrealSum : Summable (fun n =>
      (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re) :=
    (hasSum_re hsum.LSeriesHasSum).summable
  have hpartial :
      (∑ n ∈ Icc 1 X,
        (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re) ≤
      (LSeries (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ)).re := by
    rw [← (hasSum_re hsum.LSeriesHasSum).tsum_eq]
    exact hrealSum.sum_le_tsum (Icc 1 X)
      (fun n _ => tatuzawaPair_term_re_nonneg χ₁ χ₂ h₁ h₂ n)
  have hSquares :
      (M : ℝ) / (X : ℝ) ^ σ ≤
        ∑ n ∈ Icc 1 X,
          (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re := by
    let S : Finset ℕ := (Icc 1 M).image (fun m => m ^ 2)
    have hsub : S ⊆ Icc 1 X := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
      rw [Finset.mem_Icc] at hm ⊢
      exact ⟨Nat.one_le_pow 2 m hm.1, Nat.pow_le_pow_left hm.2 2⟩
    calc
      (M : ℝ) / (X : ℝ) ^ σ = ∑ m ∈ Icc 1 M, (1 / (X : ℝ) ^ σ : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ m ∈ Icc 1 M,
          (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) (m ^ 2)).re := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hm_lower, hm_upper⟩ := Finset.mem_Icc.mp hm
        have hmpos : 0 < m := Nat.zero_lt_of_lt hm_lower
        have hmsqpos : 0 < ((m ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast pow_pos hmpos 2
        have hmsqle : ((m ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_left hm_upper 2
        rw [tatuzawaPair_term_re_eq χ₁ χ₂ (pow_ne_zero 2 hmpos.ne')]
        -- Bound the square's denominator by the cutoff denominator, while
        -- its coefficient is at least one.
        have hdenpos : 0 < ((m ^ 2 : ℕ) : ℝ) ^ σ :=
          Real.rpow_pos_of_pos hmsqpos σ
        have hdenle : ((m ^ 2 : ℕ) : ℝ) ^ σ ≤ (X : ℝ) ^ σ :=
          Real.rpow_le_rpow hmsqpos.le hmsqle (zero_lt_one.trans hσ).le
        have hcoeff : (1 : ℝ) ≤ (tatuzawaPairCoefficient χ₁ χ₂ (m ^ 2)).re := by
          have hc := one_le_tatuzawaPairCoefficient_sq χ₁ χ₂ h₁ h₂ hmpos.ne'
          rw [RCLike.le_iff_re_im] at hc
          exact hc.1
        calc
          1 / (X : ℝ) ^ σ ≤ 1 / ((m ^ 2 : ℕ) : ℝ) ^ σ :=
            div_le_div_of_nonneg_left zero_le_one hdenpos hdenle
          _ ≤ (tatuzawaPairCoefficient χ₁ χ₂ (m ^ 2)).re /
              ((m ^ 2 : ℕ) : ℝ) ^ σ :=
            div_le_div_of_nonneg_right hcoeff hdenpos.le
      _ = ∑ n ∈ S,
          (LSeries.term (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ) n).re := by
        symm
        exact Finset.sum_image
          (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)).injOn
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => tatuzawaPair_term_re_nonneg χ₁ χ₂ h₁ h₂ n)
  simpa [X] using hSquares.trans hpartial

/-- The load-bearing two-character value-product inequality in `σ > 1`.
It is unconditional and contains the exact zeta-pole loss that a subsequent
Deuring--Heilbronn argument must overcome when transferring to `s = 1`. -/
theorem tatuzawaPair_square_le_zeta_sq_mul_valueProduct
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    [NeZero q₁] [NeZero q₂]
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1)
    (M : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ 2 : ℕ) : ℝ) ^ σ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ 2 *
        (‖χ₁.LFunction (σ : ℂ)‖ * ‖χ₂.LFunction (σ : ℂ)‖) := by
  have hlower := tatuzawaPair_square_lower χ₁ χ₂ h₁ h₂ M hσ
  have hfac := tatuzawaPairCoefficient_factorization χ₁ χ₂
    (show 1 < (σ : ℂ).re by simpa using hσ)
  calc
    (M : ℝ) / ((M ^ 2 : ℕ) : ℝ) ^ σ ≤
        (LSeries (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ)).re := hlower
    _ ≤ ‖LSeries (tatuzawaPairCoefficient χ₁ χ₂) (σ : ℂ)‖ := Complex.re_le_norm _
    _ = ‖riemannZeta (σ : ℂ)‖ ^ 2 *
        (‖χ₁.LFunction (σ : ℂ)‖ * ‖χ₂.LFunction (σ : ℂ)‖) := by
      rw [hfac, norm_mul, norm_mul, norm_mul]
      ring

/-- The same pair lower bound after paying the elementary zeta-pole
majorant.  The right side now displays precisely the `(σ-1)⁻²` loss which a
genuine Deuring--Heilbronn/value-transfer step must beat. -/
theorem tatuzawaPair_square_le_zetaMajorant_sq_mul_valueProduct
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    [NeZero q₁] [NeZero q₂]
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1)
    (M : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ 2 : ℕ) : ℝ) ^ σ ≤
      (1 + 1 / (σ - 1)) ^ 2 *
        (‖χ₁.LFunction (σ : ℂ)‖ * ‖χ₂.LFunction (σ : ℂ)‖) := by
  have hpair := tatuzawaPair_square_le_zeta_sq_mul_valueProduct
    χ₁ χ₂ h₁ h₂ M hσ
  have hz : ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
    have h := AnalyticNumberTheory.LargeSieve.norm_dirichletLSeries_le
      (1 : DirichletCharacter ℂ 1) σ 0 hσ
    simp only [DirichletCharacter.modOne_eq_one, ofReal_zero, mul_zero, add_zero] at h
    rw [LSeries_one_eq_riemannZeta (show 1 < (σ : ℂ).re by simpa using hσ)] at h
    exact h
  exact hpair.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity))

end DirichletCharacter

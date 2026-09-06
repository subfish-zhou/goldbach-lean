import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelPowerAmplifier
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-!
# Rankin half-plane audit for the quadratic Siegel amplifier

This file independently carries the genuine high-convolution coefficients into
the absolute-convergence half-plane. It proves summability and the exact
factorization

`L((ζ * χ)^(r+1), σ) = (ζ(σ) L(σ,χ))^(r+1)`,

then combines coefficient nonnegativity with the existing perfect-power lower
bound. The resulting finite Rankin inequality and its elementary zeta-majorant
form contain no analytic source premise.

They also expose the obstruction to closing Landau--Siegel by this route alone.
At even exponent `e = r+1`, perfect-power support contributes only
`M / (M^e)^σ`. Thus `σ = 1 + 1/log X` does not preserve the finite summatory
lower `M` after Rankin weighting: it pays the full factor `X^σ`. The infinite
perfect-power subseries improves this only to a constant when `r` is fixed,
while division by the zeta pole still leaves an `L(σ,χ)` lower of order
`σ-1`. A derivative/Pólya--Vinogradov transfer of size
`(σ-1) * polylog(q)` can therefore swamp that lower. Consequently this file
deliberately proves the exact Rankin output, not a false eventual `q^{-η}`
endpoint; closure needs a stronger weighted lower or relative control not
present in the standard direct Rankin estimate.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped LSeries.notation BigOperators ComplexOrder Real

namespace DirichletCharacter

variable {q : ℕ}

lemma rankin_pow_succ_summable (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) (r : ℕ) :
    LSeriesSummable (fun n => (χ.zetaMul ^ (r + 1)) n) s := by
  induction r with
  | zero => simpa using χ.LSeriesSummable_zetaMul hs
  | succ r ih =>
      rw [pow_succ]
      exact ArithmeticFunction.LSeriesSummable_mul ih (χ.LSeriesSummable_zetaMul hs)

lemma rankin_pow_succ_factorization (χ : DirichletCharacter ℂ q) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) (r : ℕ) :
    LSeries (fun n => (χ.zetaMul ^ (r + 1)) n) s =
      (riemannZeta s * χ.LFunction s) ^ (r + 1) := by
  induction r with
  | zero =>
      simpa using (riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ hs).symm
  | succ r ih =>
      rw [pow_succ,
        ArithmeticFunction.LSeries_mul'
          (rankin_pow_succ_summable χ hs r) (χ.LSeriesSummable_zetaMul hs),
        ih, ← riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ hs, pow_succ]
      ring

lemma rankin_term_re_eq (χ : DirichletCharacter ℂ q)
    (r : ℕ) {σ : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re =
      (quadraticSiegelPowerCoefficient χ (r + 1) n).re / (n : ℝ) ^ σ := by
  rw [LSeries.term, if_neg hn, quadraticSiegelPowerCoefficient]
  have hcpow : (n : ℂ) ^ (σ : ℂ) = ((n : ℝ) ^ σ : ℝ) := by
    symm
    exact Complex.ofReal_cpow (Nat.cast_nonneg n) σ
  rw [hcpow]
  simp

lemma rankin_term_re_nonneg (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (r : ℕ) {σ : ℝ} (n : ℕ) :
    0 ≤ (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · subst n; simp [LSeries.term]
  · rw [rankin_term_re_eq χ r hn]
    exact div_nonneg (quadraticSiegelPowerCoefficient_re_nonneg χ hquad (r + 1) n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- Finite Rankin lower bound obtained from perfect-power support. -/
theorem rankin_perfectPower_lower (χ : DirichletCharacter ℂ q) [NeZero q]
    (hquad : χ ^ 2 = 1) (r : ℕ) {e M : ℕ} (hepos : 0 < e)
    (heven : ∃ t, e = 2 * t) (hM : 1 ≤ M) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ e : ℕ) : ℝ) ^ σ ≤
      (LSeries (fun n => (χ.zetaMul ^ (r + 1)) n) (σ : ℂ)).re := by
  let X := M ^ e
  have hX : 1 ≤ X := Nat.one_le_pow e M hM
  have hsum := rankin_pow_succ_summable χ (show 1 < (σ : ℂ).re by simpa using hσ) r
  have hrealSum : Summable (fun n =>
      (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re) :=
    (hasSum_re hsum.LSeriesHasSum).summable
  have hpartial :
      (∑ n ∈ Icc 1 X,
        (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re) ≤
      (LSeries (fun n => (χ.zetaMul ^ (r + 1)) n) (σ : ℂ)).re := by
    rw [← (hasSum_re hsum.LSeriesHasSum).tsum_eq]
    exact hrealSum.sum_le_tsum (Icc 1 X)
      (fun n _ => rankin_term_re_nonneg χ hquad r n)
  have hweight :
      quadraticSiegelPowerSummatory χ (r + 1) X / (X : ℝ) ^ σ ≤
      ∑ n ∈ Icc 1 X,
        (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re := by
    rw [quadraticSiegelPowerSummatory, Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hnpos, hnX⟩ := Finset.mem_Icc.mp hn
    rw [rankin_term_re_eq χ r (Nat.ne_of_gt hnpos)]
    apply div_le_div_of_nonneg_left
      (quadraticSiegelPowerCoefficient_re_nonneg χ hquad (r + 1) n)
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hnpos) σ
    · exact Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast hnX) (le_of_lt (zero_lt_one.trans hσ))
  calc
    (M : ℝ) / ((M ^ e : ℕ) : ℝ) ^ σ ≤
        quadraticSiegelPowerSummatory χ (r + 1) X / (X : ℝ) ^ σ := by
      apply div_le_div_of_nonneg_right
      · simpa [X] using le_quadraticSiegelPowerSummatory_pow χ hquad r hepos heven M
      · positivity
    _ ≤ ∑ n ∈ Icc 1 X,
        (LSeries.term (fun k => (χ.zetaMul ^ (r + 1)) k) (σ : ℂ) n).re := hweight
    _ ≤ _ := hpartial

/-- The exact Rankin product inequality.  This is the strongest direct output
of perfect-power support and absolute convergence before choosing parameters. -/
theorem rankin_perfectPower_le_zeta_mul_LFunction_pow
    (χ : DirichletCharacter ℂ q) [NeZero q]
    (hquad : χ ^ 2 = 1) (r : ℕ) {e M : ℕ} (hepos : 0 < e)
    (heven : ∃ t, e = 2 * t) (hM : 1 ≤ M) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ e : ℕ) : ℝ) ^ σ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ (r + 1) * ‖χ.LFunction (σ : ℂ)‖ ^ (r + 1) := by
  have hlower := rankin_perfectPower_lower χ hquad r hepos heven hM hσ
  have hfac := rankin_pow_succ_factorization χ (show 1 < (σ : ℂ).re by simpa using hσ) r
  calc
    (M : ℝ) / ((M ^ e : ℕ) : ℝ) ^ σ ≤
        (LSeries (fun n => (χ.zetaMul ^ (r + 1)) n) (σ : ℂ)).re := hlower
    _ ≤ ‖LSeries (fun n => (χ.zetaMul ^ (r + 1)) n) (σ : ℂ)‖ :=
      Complex.re_le_norm _
    _ = ‖riemannZeta (σ : ℂ) * χ.LFunction (σ : ℂ)‖ ^ (r + 1) := by
      rw [hfac, norm_pow]
    _ = _ := by rw [norm_mul, mul_pow]

/-- After the elementary zeta majorant, the weighted perfect-power lower has
only the displayed strength.  At `e = r+1` its numerator is overwhelmed by
`M^((r+1)σ)`; this records the quantitative Rankin barrier rather than hiding
it behind a source predicate. -/
theorem rankin_perfectPower_le_zetaMajorant_mul_LFunction_pow
    (χ : DirichletCharacter ℂ q) [NeZero q]
    (hquad : χ ^ 2 = 1) (r : ℕ) {e M : ℕ} (hepos : 0 < e)
    (heven : ∃ t, e = 2 * t) (hM : 1 ≤ M) {σ : ℝ} (hσ : 1 < σ) :
    (M : ℝ) / ((M ^ e : ℕ) : ℝ) ^ σ ≤
      (1 + 1 / (σ - 1)) ^ (r + 1) * ‖χ.LFunction (σ : ℂ)‖ ^ (r + 1) := by
  have hprod := rankin_perfectPower_le_zeta_mul_LFunction_pow
    χ hquad r hepos heven hM hσ
  have hz : ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
    have h := AnalyticNumberTheory.LargeSieve.norm_dirichletLSeries_le
      (1 : DirichletCharacter ℂ 1) σ 0 hσ
    simp only [DirichletCharacter.modOne_eq_one, ofReal_zero, mul_zero, add_zero] at h
    rw [LSeries_one_eq_riemannZeta (show 1 < (σ : ℂ).re by simpa using hσ)] at h
    exact h
  exact hprod.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hz (r + 1)) (by positivity))

end DirichletCharacter

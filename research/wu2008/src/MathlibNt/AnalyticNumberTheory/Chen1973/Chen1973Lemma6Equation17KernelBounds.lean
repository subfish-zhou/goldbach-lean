/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (17): kernel and scalar payments

This independent leaf records the literal `11/10` Perron scale, pointwise
Cauchy decay of the denominator on both source lines, its half-line integral,
and the elementary `alpha`/`beta`, reciprocal-log, and conductor-weight
payments.  All cutoffs and constants are explicit; no finite computation is
used.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The source scale is positive as soon as `x > 1`. -/
theorem chen1973Lemma6_eq17_perronScale_pos {x : ℕ} (hx : 1 < x) :
    0 < chen1973PerronScale (x : ℝ) := by
  unfold chen1973PerronScale
  exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hx)) _

/-- On the closed right half-plane, the complex Mellin factor has norm at
least one.  This is the step that permits decreasing the exact exponent `n+1`
to the first power. -/
theorem chen1973Lemma6_eq17_one_le_norm_one_add_div
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 ≤ s.re) :
    1 ≤ ‖1 + s / (A : ℂ)‖ := by
  have hre : 1 ≤ (1 + s / (A : ℂ)).re := by
    simpa using (le_add_of_nonneg_right (a := (1 : ℝ)) (div_nonneg hs hA.le))
  exact hre.trans (Complex.re_le_norm _)


/-- Exact Euclidean comparison between the first radial factor and the complex
factor.  Squaring reduces the claim to
`(A - ‖s‖)^2 + 4 A re(s) ≥ 0`. -/
theorem chen1973Lemma6_eq17_radial_le_sqrt_two_mul_complex
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 ≤ s.re) :
    1 + ‖s‖ / A ≤ Real.sqrt 2 * ‖1 + s / (A : ℂ)‖ := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hnormsq : ‖1 + s / (A : ℂ)‖ ^ 2 =
      (1 + s.re / A) ^ 2 + (s.im / A) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hs_norm_sq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hsq : (1 + ‖s‖ / A) ^ 2 ≤
      (Real.sqrt 2 * ‖1 + s / (A : ℂ)‖) ^ 2 := by
    rw [mul_pow, hsqrt_sq, hnormsq]
    field_simp [hA.ne']
    nlinarith only [hs_norm_sq, sq_nonneg (A - ‖s‖), mul_nonneg hA.le hs]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq


/-- The completely explicit cutoff `x ≥ 3` gives both one logarithm and one
unit of Perron order. -/
theorem chen1973Lemma6_eq17_one_le_log_and_order {x : ℕ} (hx : 3 ≤ x) :
    (1 : ℝ) ≤ Real.log x ∧ 1 ≤ chen1973PerronOrder (x : ℝ) := by
  have hxR : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : (1 : ℝ) < Real.log x := by
    exact (Real.lt_log_iff_exp_lt (by positivity)).2
      (Real.exp_one_lt_three.trans_le hxR)
  refine ⟨hlog.le, ?_⟩
  unfold chen1973PerronOrder
  have hcast : ((1 : ℕ) : ℝ) ≤ Real.log x := by simpa using hlog.le
  exact Nat.le_floor hcast

/-- At `x ≥ 3`, the literal scale `(log x)^(11/10)` is paid by `(log x)^2`. -/
theorem chen1973Lemma6_eq17_perronScale_le_log_sq {x : ℕ} (hx : 3 ≤ x) :
    chen1973PerronScale (x : ℝ) ≤ Real.log x ^ 2 := by
  have hL := (chen1973Lemma6_eq17_one_le_log_and_order hx).1
  unfold chen1973PerronScale
  rw [show Real.log (x : ℝ) ^ 2 = Real.log (x : ℝ) ^ (2 : ℝ) by
    simp]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (11 : ℝ) / 10 ≤ 2)

/-- Exact Euclidean norm on a real vertical line. -/
theorem chen1973Lemma6_eq17_vertical_norm_sq (σ v : ℝ) :
    ‖((σ : ℂ) + (v : ℂ) * I)‖ ^ 2 = σ ^ 2 + v ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]


/-- Pointwise Cauchy decay furnished by the radial equation-(17)
denominator.  The harmless factor `2` covers both source lines (`σ ≤ 2`) at
the explicit cutoff `x ≥ 3`. -/
theorem chen1973Lemma6_eq17_cauchy_le_kernel
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (_hσ : 0 < σ) (hσupper : σ ≤ 2) :
    (1 / 2 : ℝ) * σ *
        (1 + (v / chen1973PerronScale (x : ℝ)) ^ 2) ≤
      chen1973Lemma6Eq17Kernel x (σ + v * I) := by
  let a := chen1973PerronScale (x : ℝ)
  let r := ‖((σ : ℂ) + (v : ℂ) * I)‖
  have ha1 : 1 ≤ a := by
    dsimp [a, chen1973PerronScale]
    exact Real.one_le_rpow
      (chen1973Lemma6_eq17_one_le_log_and_order hx).1 (by norm_num)
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrsq : r ^ 2 = σ ^ 2 + v ^ 2 :=
    chen1973Lemma6_eq17_vertical_norm_sq σ v
  have hσr : σ ≤ r := by
    simpa [r] using Complex.re_le_norm ((σ : ℂ) + (v : ℂ) * I)
  have hvr : v ^ 2 ≤ r ^ 2 := by nlinarith only [hrsq, sq_nonneg σ]
  have hσa : σ ≤ 2 * a := hσupper.trans (by linarith only [ha1])
  have hpow : 1 + r / a ≤
      (1 + r / a) ^ (chen1973PerronOrder (x : ℝ) + 1) := by
    simpa using pow_le_pow_right₀
      (le_add_of_nonneg_right (div_nonneg hr0 ha.le))
      (by omega : 1 ≤ chen1973PerronOrder (x : ℝ) + 1)
  unfold chen1973Lemma6Eq17Kernel
  change (1 / 2 : ℝ) * σ * (1 + (v / a) ^ 2) ≤
    r * (1 + r / a) ^ (chen1973PerronOrder (x : ℝ) + 1)
  have hfirst : σ * a ^ 2 ≤ r * a ^ 2 :=
    mul_le_mul_of_nonneg_right hσr (sq_nonneg a)
  have hsecond : σ * v ^ 2 ≤ (2 * a) * r ^ 2 := by
    calc
      σ * v ^ 2 ≤ (2 * a) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hσa (sq_nonneg v)
      _ ≤ (2 * a) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hvr (by positivity)
  have hfirstPower : (1 / 2 : ℝ) * σ * (1 + (v / a) ^ 2) ≤
      r * (1 + r / a) := by
    field_simp [ha.ne']
    nlinarith only [hfirst, hsecond, mul_nonneg hr0 (sq_nonneg a)]
  exact hfirstPower.trans (mul_le_mul_of_nonneg_left hpow hr0)

/-- Every fixed natural radial power up to the source order is retained by
the exact equation-(17) kernel once `‖s‖ ≥ 1/2`.  This is the reusable tail
weakening; unlike the old definition it does not discard the source power. -/
theorem chen1973Lemma6_eq17_fixed_power_le_kernel
    {x p : ℕ} {s : ℂ} (hx : 1 < x) (hs : (1 / 2 : ℝ) ≤ ‖s‖)
    (hp0 : p ≠ 0) (hp : p ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (1 / 2 : ℝ) *
        (1 + (‖s‖ / chen1973PerronScale (x : ℝ)) ^ p) ≤
      chen1973Lemma6Eq17Kernel x s := by
  let A := chen1973PerronScale (x : ℝ)
  let u := ‖s‖ / A
  let N := chen1973PerronOrder (x : ℝ) + 1
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos hx
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hadd : 1 + u ^ p ≤ (1 + u) ^ p := by
    simpa using pow_add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu hp0
  have hmono : (1 + u) ^ p ≤ (1 + u) ^ N := by
    exact pow_le_pow_right₀ (le_add_of_nonneg_right hu) hp
  unfold chen1973Lemma6Eq17Kernel
  change (1 / 2 : ℝ) * (1 + u ^ p) ≤ ‖s‖ * (1 + u) ^ N
  calc
    (1 / 2 : ℝ) * (1 + u ^ p) ≤ (1 / 2 : ℝ) * (1 + u) ^ N := by
      gcongr
      exact hadd.trans hmono
    _ ≤ ‖s‖ * (1 + u) ^ N := by
      gcongr





/-- Exact source alpha exponent: `x^alpha = e*x`. -/
theorem chen1973Lemma6_eq17_rpow_alpha {x : ℕ} (hx : 1 < x) :
    (x : ℝ) ^ chen1973Lemma6Alpha x = Real.exp 1 * x := by
  have hxR : 0 < (x : ℝ) := by positivity
  have hlog : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hx)).ne'
  unfold chen1973Lemma6Alpha
  rw [Real.rpow_def_of_pos hxR]
  have he : Real.log (x : ℝ) * (1 + 1 / Real.log x) = Real.log x + 1 := by
    field_simp [hlog]
  rw [he, Real.exp_add, Real.exp_log hxR]
  ring

/-- Exact source beta exponent: `x^beta = e*sqrt x`. -/
theorem chen1973Lemma6_eq17_rpow_beta {x : ℕ} (hx : 1 < x) :
    (x : ℝ) ^ chen1973Lemma6Beta x = Real.exp 1 * Real.sqrt x := by
  have hxR : 0 < (x : ℝ) := by positivity
  have hlog : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hx)).ne'
  unfold chen1973Lemma6Beta
  rw [Real.rpow_def_of_pos hxR]
  have he : Real.log (x : ℝ) * (1 / 2 + 1 / Real.log x) =
      Real.log x / 2 + 1 := by
    field_simp [hlog]
  rw [he, Real.exp_add]
  rw [← Real.log_sqrt hxR.le, Real.exp_log (Real.sqrt_pos.2 hxR)]
  ring





/-- On squarefree conductors, the source's `3^ω` factor is bounded by the
square of the divisor count. -/
private theorem eq17_three_pow_primeFactors_card_le_divisors_card_sq
    {d : ℕ} (hd : Squarefree d) :
    (3 : ℝ) ^ d.primeFactors.card ≤ (d.divisors.card : ℝ) ^ 2 := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hcard : d.divisors.card = 2 ^ d.primeFactors.card := by
    rw [Nat.card_divisors hd0]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hd
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  rw [hcard]
  norm_cast
  rw [pow_two, ← mul_pow]
  exact pow_le_pow_left' (by norm_num : 3 ≤ 2 * 2) _


end AnalyticNumberTheory.LargeSieve

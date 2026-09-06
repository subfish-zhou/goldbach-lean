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

/-- Since `n+1 ≥ 1`, the exact Mellin power dominates its first factor on the
closed right half-plane. -/
theorem chen1973Lemma6_eq17_first_le_exact_power
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖1 + s / (A : ℂ)‖ ≤ ‖1 + s / (A : ℂ)‖ ^ (n + 1) := by
  have hbase := chen1973Lemma6_eq17_one_le_norm_one_add_div hA hs
  simpa using pow_le_pow_right₀ hbase (show 1 ≤ n + 1 by omega)

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

/-- Comparison of the exact complex Mellin denominator with the literal
source radial denominator.  The factor `sqrt 2 ^ N` is the honest cost of
replacing `‖1+s/A‖` by `1+‖s‖/A` at the full source exponent `N`. -/
theorem chen1973Lemma6_eq17_mellinKernel_norm_le_radial
    {x : ℕ} (hx : 1 < x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖chen1973MellinKernel (x : ℝ) s‖ ≤
      (Real.sqrt 2) ^ (chen1973PerronOrder (x : ℝ) + 1) /
        chen1973Lemma6Eq17Kernel x s := by
  let A := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos hx
  by_cases hs0 : s = 0
  · subst s
    simp [chen1973MellinKernel, chen1973Lemma6Eq17Kernel]
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hbase : 1 ≤ ‖1 + s / (A : ℂ)‖ :=
    chen1973Lemma6_eq17_one_le_norm_one_add_div hA hs
  have hradial : 1 + ‖s‖ / A ≤
      Real.sqrt 2 * ‖1 + s / (A : ℂ)‖ :=
    chen1973Lemma6_eq17_radial_le_sqrt_two_mul_complex hA hs
  have hpowpos : 0 < ‖1 + s / (A : ℂ)‖ ^ N :=
    pow_pos (zero_lt_one.trans_le hbase) _
  have hradpos : 0 < (1 + ‖s‖ / A) ^ N := pow_pos (by positivity) _
  unfold chen1973MellinKernel chen1973Lemma6Eq17Kernel
  rw [norm_div, norm_one, norm_mul, norm_pow]
  change 1 / (‖s‖ * ‖1 + s / (A : ℂ)‖ ^ N) ≤
    (Real.sqrt 2) ^ N / (‖s‖ * (1 + ‖s‖ / A) ^ N)
  rw [div_le_div_iff₀ (mul_pos hsNorm hpowpos) (mul_pos hsNorm hradpos)]
  calc
    1 * (‖s‖ * (1 + ‖s‖ / A) ^ N) ≤
        ‖s‖ * (Real.sqrt 2 * ‖1 + s / (A : ℂ)‖) ^ N := by
      rw [one_mul]
      apply mul_le_mul_of_nonneg_left _ hsNorm.le
      gcongr
    _ = (Real.sqrt 2) ^ N *
        (‖s‖ * ‖1 + s / (A : ℂ)‖ ^ N) := by
      rw [mul_pow]
      ring

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

/-- The source denominator is strictly positive on every positive vertical
line. -/
theorem chen1973Lemma6_eq17_kernel_pos {x : ℕ} (hx : 1 < x)
    {σ v : ℝ} (hσ : 0 < σ) :
    0 < chen1973Lemma6Eq17Kernel x (σ + v * I) := by
  unfold chen1973Lemma6Eq17Kernel
  have hs : 0 < ‖((σ : ℂ) + (v : ℂ) * I)‖ :=
    hσ.trans_le (by simpa using Complex.re_le_norm ((σ : ℂ) + (v : ℂ) * I))
  have ha := chen1973Lemma6_eq17_perronScale_pos hx
  exact mul_pos hs (by positivity)

/-- Pointwise Cauchy decay furnished by the radial equation-(17)
denominator.  The harmless factor `2` covers both source lines (`σ ≤ 2`) at
the explicit cutoff `x ≥ 3`. -/
theorem chen1973Lemma6_eq17_cauchy_le_kernel
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ) (hσupper : σ ≤ 2) :
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

/-- The fixed `v^(21/10)` tail weakening needed after the equation-(19)
second-moment bound.  The explicit order threshold is exactly `3 ≤ N`. -/
theorem chen1973Lemma6_eq17_rpow_21_div_10_le_kernel
    {x : ℕ} {s : ℂ} (hx : 1 < x) (hs : (1 / 2 : ℝ) ≤ ‖s‖)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (1 / 4 : ℝ) *
        (1 + (‖s‖ / chen1973PerronScale (x : ℝ)) ^ ((21 : ℝ) / 10)) ≤
      chen1973Lemma6Eq17Kernel x s := by
  let u := ‖s‖ / chen1973PerronScale (x : ℝ)
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _)
    (chen1973Lemma6_eq17_perronScale_pos hx).le
  have hthree := chen1973Lemma6_eq17_fixed_power_le_kernel
    (x := x) (p := 3) (s := s) hx hs (by norm_num) horder
  change (1 / 4 : ℝ) * (1 + u ^ ((21 : ℝ) / 10)) ≤ _
  change (1 / 2 : ℝ) * (1 + u ^ (3 : ℕ)) ≤ _ at hthree
  rcases le_total u 1 with hu1 | h1u
  · have hur : u ^ ((21 : ℝ) / 10) ≤ 1 :=
      Real.rpow_le_one hu hu1 (by norm_num)
    have hkernelHalf : (1 / 2 : ℝ) ≤ chen1973Lemma6Eq17Kernel x s := by
      have hone : (1 : ℝ) ≤ 1 + u ^ (3 : ℕ) :=
        le_add_of_nonneg_right (pow_nonneg hu _)
      nlinarith
    nlinarith
  · have hur : u ^ ((21 : ℝ) / 10) ≤ u ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1u (by norm_num)
    calc
      (1 / 4 : ℝ) * (1 + u ^ ((21 : ℝ) / 10)) ≤
          (1 / 4 : ℝ) * (1 + u ^ (3 : ℕ)) := by gcongr
      _ ≤ (1 / 2 : ℝ) * (1 + u ^ (3 : ℕ)) := by
        have := pow_nonneg hu 3
        nlinarith
      _ ≤ chen1973Lemma6Eq17Kernel x s := hthree

/-- The fixed fourth-power tail weakening needed for the equation-(20) fourth
moments, under the explicit threshold `4 ≤ N`. -/
theorem chen1973Lemma6_eq17_fourth_power_le_kernel
    {x : ℕ} {s : ℂ} (hx : 1 < x) (hs : (1 / 2 : ℝ) ≤ ‖s‖)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (1 / 2 : ℝ) *
        (1 + (‖s‖ / chen1973PerronScale (x : ℝ)) ^ 4) ≤
      chen1973Lemma6Eq17Kernel x s :=
  chen1973Lemma6_eq17_fixed_power_le_kernel hx hs (by norm_num) horder

/-- Reciprocal form of the pointwise Cauchy majorant. -/
theorem chen1973Lemma6_eq17_kernel_inv_le_cauchy
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ) (hσupper : σ ≤ 2) :
    (chen1973Lemma6Eq17Kernel x (σ + v * I))⁻¹ ≤
      2 * σ⁻¹ *
        (1 + (v / chen1973PerronScale (x : ℝ)) ^ 2)⁻¹ := by
  have hlow := chen1973Lemma6_eq17_cauchy_le_kernel
    (x := x) (σ := σ) (v := v) hx hσ hσupper
  have hcpos : 0 < (1 / 2 : ℝ) * σ *
      (1 + (v / chen1973PerronScale (x : ℝ)) ^ 2) := by positivity
  have hinv := inv_anti₀ hcpos hlow
  calc
    _ ≤ ((1 / 2 : ℝ) * σ *
      (1 + (v / chen1973PerronScale (x : ℝ)) ^ 2))⁻¹ := hinv
    _ = _ := by field_simp

/-- Exact half-line mass of the scalar Cauchy envelope. -/
theorem chen1973Lemma6_eq17_integral_cauchy_envelope
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    (∫ v in Ioi (0 : ℝ), σ⁻¹ * (1 + (v / a) ^ 2)⁻¹) =
      (Real.pi / 2) * a / σ := by
  rw [MeasureTheory.integral_const_mul]
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 (inv_pos.mpr ha)
  simp only [inv_mul_eq_div] at hscale
  have hbase : (∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹) = Real.pi / 2 := by simp
  simp only [zero_div] at hscale
  rw [hbase] at hscale
  rw [hscale]
  field_simp [ha.ne', hσ.ne']
  ring

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

/-- The alpha-line Cauchy mass is paid by the printed `x (log x)^2`
coefficient, with the explicit constant `6`. -/
theorem chen1973Lemma6_eq17_alpha_scalar_payment {x : ℕ} (hx : 3 ≤ x) :
    (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
        chen1973Lemma6Alpha x * (x : ℝ) ^ chen1973Lemma6Alpha x ≤
      6 * (x : ℝ) * Real.log x ^ 2 := by
  have hx1 : 1 < x := by omega
  have hscale := chen1973Lemma6_eq17_perronScale_le_log_sq hx
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    (Real.log_pos (by exact_mod_cast hx1)).le
  have hα : 1 ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have := one_div_nonneg.mpr hlog0
    linarith
  have hαpos : 0 < chen1973Lemma6Alpha x := zero_lt_one.trans_le hα
  have hscale0 : 0 ≤ chen1973PerronScale (x : ℝ) :=
    (chen1973Lemma6_eq17_perronScale_pos hx1).le
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  rw [chen1973Lemma6_eq17_rpow_alpha hx1]
  have hdiv : (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
      chen1973Lemma6Alpha x ≤ 2 * Real.log x ^ 2 := by
    calc
      _ ≤ 2 * Real.log x ^ 2 / chen1973Lemma6Alpha x := by
        gcongr
      _ ≤ 2 * Real.log x ^ 2 / 1 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hα
      _ = _ := by ring
  calc
    (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
        chen1973Lemma6Alpha x * (Real.exp 1 * x) ≤
      (2 * Real.log x ^ 2) * (3 * x) := by gcongr
    _ = 6 * (x : ℝ) * Real.log x ^ 2 := by ring

/-- At the same explicit cutoff, the beta-line Cauchy mass (including the
literal `11/10` scale) has the coarse auxiliary bound `x^(3/2)`. This is
not the printed `x^(1/2)` prefactor; the sharp beta comparison is proved in
`Equation17CorrectedAssembly`. The
constant `48` comes from `pi/2<2`, `beta≥1/2`, `e<3`, and
`log x ≤ 2 sqrt x`; no finite scan is used. -/
theorem chen1973Lemma6_eq17_beta_scalar_payment {x : ℕ} (hx : 3 ≤ x) :
    (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
        chen1973Lemma6Beta x * (x : ℝ) ^ chen1973Lemma6Beta x ≤
      48 * (x : ℝ) ^ ((3 : ℝ) / 2) := by
  have hx1 : 1 < x := by omega
  have hxR : 0 < (x : ℝ) := by positivity
  have hscale := chen1973Lemma6_eq17_perronScale_le_log_sq hx
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    (Real.log_pos (by exact_mod_cast hx1)).le
  have hβ : (1 / 2 : ℝ) ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have := one_div_nonneg.mpr hlog0
    linarith
  have hβpos : 0 < chen1973Lemma6Beta x := by linarith
  have hscale0 : 0 ≤ chen1973PerronScale (x : ℝ) :=
    (chen1973Lemma6_eq17_perronScale_pos hx1).le
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
  have hlogsqrt := Real.log_le_rpow_div (x := (x : ℝ)) (ε := (1 / 2 : ℝ))
    hxR.le (by norm_num)
  have hrpowhalf : (x : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
  rw [hrpowhalf] at hlogsqrt
  have hlogsq : Real.log (x : ℝ) ^ 2 ≤ 4 * x := by
    have hsqrt0 := Real.sqrt_nonneg (x : ℝ)
    have hsqrtSq := Real.sq_sqrt hxR.le
    nlinarith
  have hdiv : (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
      chen1973Lemma6Beta x ≤ 16 * x := by
    calc
      _ ≤ 2 * Real.log x ^ 2 / chen1973Lemma6Beta x := by gcongr
      _ ≤ 2 * (4 * x) / (1 / 2 : ℝ) := by
        exact div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hlogsq (by norm_num)) (by norm_num) hβ
      _ = 16 * x := by ring
  rw [chen1973Lemma6_eq17_rpow_beta hx1]
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hxsqrt : (x : ℝ) * Real.sqrt x = (x : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hxR,
      Real.rpow_one, hrpowhalf]
  calc
    (Real.pi / 2) * chen1973PerronScale (x : ℝ) /
        chen1973Lemma6Beta x * (Real.exp 1 * Real.sqrt x) ≤
      (16 * x) * (3 * Real.sqrt x) := by gcongr
    _ = 48 * (x : ℝ) ^ ((3 : ℝ) / 2) := by rw [← hxsqrt]; ring

/-- The reciprocal logarithm appearing in the pair polynomial has exactly the
expected complex norm when its source argument exceeds one. -/
theorem chen1973Lemma6_eq17_norm_reciprocal_log {y : ℝ} (hy : 1 < y) :
    ‖(((Real.log y)⁻¹ : ℝ) : ℂ)‖ = (Real.log y)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.log_pos hy))]

/-- Every literal conductor coefficient in (17) is nonnegative. -/
theorem chen1973Lemma6_eq17_conductorWeight_nonneg (d : ℕ) :
    0 ≤ |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d := by positivity

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

/-- Squarefree conductor weights are paid pointwise by the divisor-square
weight. -/
theorem chen1973Lemma6_eq17_conductorWeight_le_divisorSquare
    {d : ℕ} (hd : Squarefree d) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ d.primeFactors.card / d ≤
      (d.divisors.card : ℝ) ^ 2 / d := by
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd
  rw [hmu, one_mul]
  exact div_le_div_of_nonneg_right
    (eq17_three_pow_primeFactors_card_le_divisors_card_sq hd) (by positivity)

end AnalyticNumberTheory.LargeSieve

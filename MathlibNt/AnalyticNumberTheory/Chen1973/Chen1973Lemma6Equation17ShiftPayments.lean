/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17ContourShift
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation
import Mathlib.Tactic

noncomputable section

open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
open DirichletLAbelWeightVariation
open DirichletLConditionalDerivativeSeries
open DirichletLConditionalDerivativeAnalyticContinuation

namespace AnalyticNumberTheory.LargeSieve

/-- A deliberately crude, but global, vertical growth estimate.  The naturally
ordered Abel representation at cutoff one is enough: on `1/2 ≤ σ ≤ 2`, `L'`
has at most linear growth in the height. -/
theorem norm_deriv_LFunction_le_modulus_mul_linear_height
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ t : ℝ} (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2) :
    ‖deriv χ.LFunction (σ + I * t)‖ ≤
      (q : ℝ) * (2 + 4 * ‖(σ + I * t : ℂ)‖) := by
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hsre : 0 < (σ + I * t : ℂ).re := by simpa using hσpos
  have hprefix :
      (∑ k ∈ range 1, logCpowWeight (σ + I * t) k * χ k) = 0 := by
    simp [logCpowWeight, cpowWeight]
  have hseries := orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    χ hχ (σ + I * t) hsre
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le
    χ hχ (σ + I * t) hsre (m := 1) (by norm_num)
  have hinv : 1 / σ ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    linarith only [hσlower]
  have hinv2 : 1 / σ ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hσpos)]
    nlinarith only [hσlower]
  have hbudget : logVariationBudget (σ + I * t) 1 ≤
      2 + 4 * ‖(σ + I * t : ℂ)‖ := by
    rw [logVariationBudget]
    norm_num
    have hi : σ⁻¹ ≤ 2 := by simpa only [one_div] using hinv
    have hi2 : (σ ^ 2)⁻¹ ≤ 4 := by simpa only [one_div] using hinv2
    have hn : 0 ≤ ‖(σ + I * t : ℂ)‖ := norm_nonneg _
    nlinarith only [hi, hi2, hn]
  rw [← hseries]
  rw [hprefix, sub_zero] at htail
  calc
    ‖orderedLogDerivativeSeries χ hχ (σ + I * t) hsre‖ ≤
        (q : ℝ) * logVariationBudget (σ + I * t) 1 := by
      simpa [logCpowWeight, cpowWeight] using htail
    _ ≤ (q : ℝ) * (2 + 4 * ‖(σ + I * t : ℂ)‖) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)

/-- The finite Möbius polynomial is uniformly bounded on every vertical line
with nonnegative real part.  Keeping the literal finite coefficient mass avoids
any unnecessary arithmetic estimate. -/
private theorem norm_mobiusPartialSum_le_coeffMass
    {d H : ℕ} (χ : PrimitiveCharacter d) {σ t : ℝ} (hσ : 0 ≤ σ) :
    ‖chen1973Lemma6MobiusPartialSum H (σ + I * t) χ‖ ≤
      ∑ n ∈ Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖ := by
  unfold chen1973Lemma6MobiusPartialSum
  calc
    _ ≤ ∑ n ∈ Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d) /
          (n : ℂ) ^ (σ + I * t)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      rw [norm_div]
      change ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖ /
          ‖(((n : ℝ) : ℂ) ^ (σ + I * t))‖ ≤ _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero]
      have hp : 1 ≤ (n : ℝ) ^ σ := by
        exact Real.one_le_rpow (by exact_mod_cast hn1) hσ
      exact div_le_self (norm_nonneg _) (by simpa using hp)

private theorem norm_cpow_height_independent
    {y σ t : ℝ} (hy : 0 < y) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖(y : ℂ) ^ (σ + I * t)‖ ≤ Real.exp (2 * |Real.log y|) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero]
  rw [Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log y * σ ≤ |Real.log y| * 2 := by
    calc
      Real.log y * σ ≤ |Real.log y| * σ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hσ0
      _ ≤ |Real.log y| * 2 := mul_le_mul_of_nonneg_left hσ2 (abs_nonneg _)
  simpa only [add_zero, mul_comm] using hlog

private theorem eq17_kernel_pays_linear_growth
    {x : ℕ} (hx : 3 ≤ x) {σ t : ℝ}
    (hσlower : chen1973Lemma6Beta x ≤ σ) :
    (2 + 4 * ‖(σ + I * t : ℂ)‖) *
        ‖chen1973MellinKernel (x : ℝ) (σ + I * t)‖ ≤
      (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
        (2 / chen1973Lemma6Beta x + 4)) / (1 + t ^ 2) := by
  let A := chen1973PerronScale (x : ℝ)
  let n := chen1973PerronOrder (x : ℝ)
  let β := chen1973Lemma6Beta x
  let z : ℂ := σ + I * t
  let η : ℂ := (A + σ) + I * t
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    exact (Real.le_log_iff_exp_le (by positivity)).2
      (Real.exp_one_lt_three.le.trans (by exact_mod_cast hx))
  have hA : 1 ≤ A := by
    dsimp [A, chen1973PerronScale]
    exact Real.one_le_rpow hlog1 (by norm_num)
  have hβ : 0 < β := by
    dsimp [β, chen1973Lemma6Beta]
    have hl : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
    positivity
  have hσ : 0 < σ := hβ.trans_le hσlower
  have hn : 2 ≤ n + 1 := by
    dsimp [n, chen1973PerronOrder]
    have hf : 1 ≤ ⌊Real.log (x : ℝ)⌋₊ := Nat.le_floor (by simpa using hlog1)
    omega
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hηeq : 1 + z / A = η / A := by
    dsimp [z, η]
    field_simp [hApos.ne']
    ring
  have hnormz : β ≤ ‖z‖ :=
    hσlower.trans (by simpa [z] using Complex.re_le_norm z)
  have hnormηsq : ‖η‖ ^ 2 = (A + σ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [η, Complex.normSq_apply, pow_two]
  have hηre : 1 ≤ A + σ := hA.trans (le_add_of_nonneg_right hσ.le)
  have hηone : 1 ≤ ‖η‖ :=
    hηre.trans (by simpa [η] using Complex.re_le_norm η)
  have hηden : 1 + t ^ 2 ≤ ‖η‖ ^ (n + 1) := by
    calc
      1 + t ^ 2 ≤ ‖η‖ ^ 2 := by
        rw [hnormηsq]
        exact add_le_add (one_le_pow₀ hηre) le_rfl
      _ ≤ ‖η‖ ^ (n + 1) := pow_le_pow_right₀ hηone hn
  have hratio : (2 + 4 * ‖z‖) / ‖z‖ ≤ 2 / β + 4 := by
    have hzpos : 0 < ‖z‖ := hβ.trans_le hnormz
    calc
      (2 + 4 * ‖z‖) / ‖z‖ = 2 / ‖z‖ + 4 := by
        field_simp [hzpos.ne']
      _ ≤ 2 / β + 4 := by
        gcongr
  have hknorm :
      ‖chen1973MellinKernel (x : ℝ) z‖ =
        A ^ (n + 1) / (‖z‖ * ‖η‖ ^ (n + 1)) := by
    unfold chen1973MellinKernel
    rw [norm_div, norm_one, norm_mul, norm_pow, hηeq, norm_div, div_pow]
    simp [A, n, hApos.ne', abs_of_pos hApos,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  change (2 + 4 * ‖z‖) * ‖chen1973MellinKernel (x : ℝ) z‖ ≤ _
  rw [hknorm]
  have hzpos : 0 < ‖z‖ := hβ.trans_le hnormz
  have hηpos : 0 < ‖η‖ ^ (n + 1) := pow_pos (lt_of_lt_of_le zero_lt_one hηone) _
  have hdenpos : 0 < 1 + t ^ 2 := by positivity
  rw [show (2 + 4 * ‖z‖) * (A ^ (n + 1) / (‖z‖ * ‖η‖ ^ (n + 1))) =
      A ^ (n + 1) * ((2 + 4 * ‖z‖) / ‖z‖) / ‖η‖ ^ (n + 1) by
        field_simp [hzpos.ne', hηpos.ne']]
  change A ^ (n + 1) * ((2 + 4 * ‖z‖) / ‖z‖) / ‖η‖ ^ (n + 1) ≤
    A ^ (n + 1) * (2 / β + 4) / (1 + t ^ 2)
  calc
    _ ≤ A ^ (n + 1) * (2 / β + 4) / ‖η‖ ^ (n + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (pow_nonneg (zero_le_one.trans hA) _))
        (pow_nonneg (norm_nonneg η) _)
    _ ≤ A ^ (n + 1) * (2 / β + 4) / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (by positivity)
      · exact hdenpos
      · exact hηden

/-- A uniform `1/(1+t²)` majorant on the whole closed strip.  The
linear Abel growth of `L'` is cancelled by the explicit `s` in Chen's kernel;
the remaining kernel power has order at least two once `x ≥ 3`. -/
theorem norm_chen1973Lemma6Eq17ShiftIntegrand_le_inv_one_add_sq
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) {y σ t : ℝ} (hy : 0 < y)
    (hσlower : chen1973Lemma6Beta x ≤ σ)
    (hσupper : σ ≤ chen1973Lemma6Alpha x) :
    ‖chen1973Lemma6Eq17ShiftIntegrand x H y χ (σ + I * t)‖ ≤
      ((d : ℝ) *
        (∑ n ∈ Icc 1 H,
          ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖) *
        Real.exp (2 * |Real.log y|) *
        (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
          (2 / chen1973Lemma6Beta x + 4))) / (1 + t ^ 2) := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    exact (Real.le_log_iff_exp_le (by positivity)).2
      (Real.exp_one_lt_three.le.trans (by exact_mod_cast hx))
  have hβpos : 0 < chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have hl : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
    positivity
  have hσ0 : 0 ≤ σ := (hβpos.trans_le hσlower).le
  have hα2 : chen1973Lemma6Alpha x ≤ 2 := by
    unfold chen1973Lemma6Alpha
    have hl : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
    have hi : 1 / Real.log (x : ℝ) ≤ 1 := (div_le_one hl).2 hlog1
    linarith only [hi]
  have hd := norm_deriv_LFunction_le_modulus_mul_linear_height χ.1 hχ
    (σ := σ) (t := t) (by
      unfold chen1973Lemma6Beta at hσlower
      linarith [one_div_pos.mpr (lt_of_lt_of_le (by norm_num) hlog1)])
    (hσupper.trans hα2)
  have hS := norm_mobiusPartialSum_le_coeffMass (H := H) (t := t) χ hσ0
  have hyb := norm_cpow_height_independent (t := t) hy hσ0 (hσupper.trans hα2)
  have hk := eq17_kernel_pays_linear_growth hx hσlower (t := t)
  unfold chen1973Lemma6Eq17ShiftIntegrand
  simp only [norm_mul]
  let M : ℝ := ∑ n ∈ Icc 1 H,
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * ‖χ.1 (n : ZMod d)‖
  have hS' : ‖chen1973Lemma6MobiusPartialSum H (σ + I * t) χ‖ ≤ M := by
    simpa [M, norm_mul] using hS
  let Y : ℝ := Real.exp (2 * |Real.log y|)
  let P : ℝ := chen1973PerronScale (x : ℝ) ^
      (chen1973PerronOrder (x : ℝ) + 1) * (2 / chen1973Lemma6Beta x + 4)
  change ‖deriv χ.1.LFunction (σ + I * t)‖ *
      ‖chen1973Lemma6MobiusPartialSum H (σ + I * t) χ‖ *
      (‖(y : ℂ) ^ (σ + I * t)‖ *
        ‖chen1973MellinKernel (x : ℝ) (σ + I * t)‖) ≤
      ((d : ℝ) * M * Y * P) / (1 + t ^ 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  calc
    _ ≤ ((d : ℝ) * (2 + 4 * ‖(σ + I * t : ℂ)‖)) * M *
        (Y * ‖chen1973MellinKernel (x : ℝ) (σ + I * t)‖) := by
      gcongr
    _ = (d : ℝ) * M * Y *
        ((2 + 4 * ‖(σ + I * t : ℂ)‖) *
          ‖chen1973MellinKernel (x : ℝ) (σ + I * t)‖) := by ring
    _ ≤ (d : ℝ) * M * Y * (P / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hk
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hM) hY)
    _ = ((d : ℝ) * M * Y * P) / (1 + t ^ 2) := by ring

/-- Both boundary sections are Bochner integrable; in fact the same proof
works for every vertical line in the closed strip. -/
theorem integrable_chen1973Lemma6Eq17_verticalSection
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) {y σ : ℝ} (hy : 0 < y)
    (hσlower : chen1973Lemma6Beta x ≤ σ)
    (hσupper : σ ≤ chen1973Lemma6Alpha x) :
    Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) σ) := by
  let D : ℝ := (d : ℝ) *
    (∑ n ∈ Icc 1 H,
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖) *
    Real.exp (2 * |Real.log y|) *
    (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
      (2 / chen1973Lemma6Beta x + 4))
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hcontOn := (differentiableOn_chen1973Lemma6Eq17ShiftIntegrand_strip
    (H := H) χ hχ hx1 hy).continuousOn
  have hline : Continuous (fun t : ℝ => (σ + t * I : ℂ)) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ => (σ + t * I : ℂ)) univ
      {s : ℂ | chen1973Lemma6Beta x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x} := by
    intro t _
    simpa using And.intro hσlower hσupper
  have hmeas : AEStronglyMeasurable (chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) σ) := by
    have hc : Continuous (chen1973VerticalSection
        (chen1973Lemma6Eq17ShiftIntegrand x H y χ) σ) := by
      change Continuous (fun t : ℝ =>
        chen1973Lemma6Eq17ShiftIntegrand x H y χ (σ + t * I))
      exact continuousOn_univ.mp (hcontOn.comp hline.continuousOn hmaps)
    exact hc.aestronglyMeasurable
  have hdom : Integrable (fun t : ℝ => D * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  apply Integrable.mono' hdom hmeas
  filter_upwards with t
  unfold chen1973VerticalSection
  have hp := norm_chen1973Lemma6Eq17ShiftIntegrand_le_inv_one_add_sq
    (H := H) χ hχ hx hy hσlower hσupper (t := t)
  simpa [D, div_eq_mul_inv, mul_comm I] using hp

/-- Explicit horizontal-edge decay.  Each edge has length `α-β=1/2`;
the triangle inequality for their difference therefore costs exactly one copy
of the common pointwise majorant. -/
theorem norm_chen1973Lemma6Eq17_horizontalSection_le_inv_one_add_sq
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) {y T : ℝ} (hy : 0 < y) :
    ‖chen1973HorizontalSection (chen1973Lemma6Eq17ShiftIntegrand x H y χ)
      (chen1973Lemma6Beta x) (chen1973Lemma6Alpha x) T‖ ≤
      ((d : ℝ) *
        (∑ n ∈ Icc 1 H,
          ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖) *
        Real.exp (2 * |Real.log y|) *
        (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
          (2 / chen1973Lemma6Beta x + 4))) / (1 + T ^ 2) := by
  let D : ℝ := (d : ℝ) *
    (∑ n ∈ Icc 1 H,
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖) *
    Real.exp (2 * |Real.log y|) *
    (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
      (2 / chen1973Lemma6Beta x + 4))
  have hβα : chen1973Lemma6Beta x ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Beta chen1973Lemma6Alpha
    linarith
  have hedge (t : ℝ) (ht : t ^ 2 = T ^ 2) :
      ‖∫ u in chen1973Lemma6Beta x..chen1973Lemma6Alpha x,
        chen1973Lemma6Eq17ShiftIntegrand x H y χ (u + t * I)‖ ≤
        (D / (1 + T ^ 2)) *
          |chen1973Lemma6Alpha x - chen1973Lemma6Beta x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le hβα] at hu
    have hp := norm_chen1973Lemma6Eq17ShiftIntegrand_le_inv_one_add_sq
      (H := H) χ hχ hx hy hu.1.le hu.2 (t := t)
    rw [ht] at hp
    simpa only [D, mul_comm I] using hp
  unfold chen1973HorizontalSection
  calc
    _ ≤ ‖∫ u in chen1973Lemma6Beta x..chen1973Lemma6Alpha x,
          chen1973Lemma6Eq17ShiftIntegrand x H y χ (u + (-T) * I)‖ +
        ‖∫ u in chen1973Lemma6Beta x..chen1973Lemma6Alpha x,
          chen1973Lemma6Eq17ShiftIntegrand x H y χ (u + T * I)‖ := norm_sub_le _ _
    _ ≤ (D / (1 + T ^ 2)) *
          |chen1973Lemma6Alpha x - chen1973Lemma6Beta x| +
        (D / (1 + T ^ 2)) *
          |chen1973Lemma6Alpha x - chen1973Lemma6Beta x| :=
      add_le_add (by
        simpa only [ofReal_neg] using hedge (-T) (by ring)) (hedge T rfl)
    _ = D / (1 + T ^ 2) := by
      have hlen : |chen1973Lemma6Alpha x - chen1973Lemma6Beta x| = 1 / 2 := by
        unfold chen1973Lemma6Alpha chen1973Lemma6Beta
        norm_num
      rw [hlen]
      ring

/-- Unconditional equation-(17) contour shift for the actual nonprincipal
primitive `L'·S` kernel.  No integrability or horizontal-decay premise remains
at the call site. -/
theorem chen1973Lemma6_eq17_LDerivS_contour_shift_unconditional
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Alpha x) t) =
    ∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Beta x) t := by
  let C : ℝ := (d : ℝ) *
    (∑ n ∈ Icc 1 H,
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d)‖) *
    Real.exp (2 * |Real.log y|) *
    (chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) *
      (2 / chen1973Lemma6Beta x + 4))
  have hβpos : 0 < chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    positivity
  apply chen1973Lemma6_eq17_LDerivS_contour_shift χ hχ (by omega) hy
    (C := C)
  · dsimp [C]
    have hscale : 0 ≤ chen1973PerronScale (x : ℝ) ^
        (chen1973PerronOrder (x : ℝ) + 1) := by
      apply pow_nonneg
      unfold chen1973PerronScale
      exact Real.rpow_nonneg (by positivity) _
    have hfactor : 0 ≤ 2 / chen1973Lemma6Beta x + 4 := by positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
        (Real.exp_pos _).le)
      (mul_nonneg hscale hfactor)
  · exact integrable_chen1973Lemma6Eq17_verticalSection χ hχ hx hy le_rfl
      (by unfold chen1973Lemma6Beta chen1973Lemma6Alpha; linarith)
  · exact integrable_chen1973Lemma6Eq17_verticalSection χ hχ hx hy
      (by unfold chen1973Lemma6Beta chen1973Lemma6Alpha; linarith) le_rfl
  · intro T _hT
    simpa only [C] using
      (norm_chen1973Lemma6Eq17_horizontalSection_le_inv_one_add_sq χ hχ hx hy
        (T := T))

end AnalyticNumberTheory.LargeSieve

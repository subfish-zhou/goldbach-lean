/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17KernelBounds

/-!
# Chen 1973, equation (17): rigorous corrected-source kernel

The denominator printed in (17) remains
`|s| (1 + |s| / A)^N`.  The exact Mellin denominator does not dominate that
printed expression with an absolute constant: the direct comparison costs
`(sqrt 2)^N`.

This separate module therefore introduces the rigorous **corrected-source**
denominator

`|s| (1 + (|s| / A)^N)`.

For `Re s ≥ 0` and `N ≥ 2`, the exact complex Mellin denominator dominates this
corrected denominator with constant one.  The fixed-power estimates below are
coarse downstream weakenings and are not transcriptions of printed (17).
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The rigorous corrected-source radial denominator.  Unlike the printed
kernel, the high power applies only to `|s| / A`.  It has no conductor-level
parameter. -/
def chen1973Lemma6Eq17CorrectedKernel (x : ℕ) (s : ℂ) : ℝ :=
  ‖s‖ * (1 + (‖s‖ / chen1973PerronScale (x : ℝ)) ^
    (chen1973PerronOrder (x : ℝ) + 1))

/-- On the right half-plane, the exact complex power dominates the
corrected-source radial power once the integer exponent is at least two. -/
theorem chen1973Lemma6_eq17_one_add_radial_pow_le_complex_pow
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 ≤ s.re) {N : ℕ} (hN : 2 ≤ N) :
    1 + (‖s‖ / A) ^ N ≤ ‖1 + s / (A : ℂ)‖ ^ N := by
  let u := ‖s‖ / A
  let b := ‖1 + s / (A : ℂ)‖
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hb : 0 ≤ b := norm_nonneg _
  have hb_sq : b ^ 2 = 1 + 2 * s.re / A + u ^ 2 := by
    dsimp [b, u]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      add_zero, Complex.add_im, Complex.one_im, zero_add, Complex.div_im]
    have hs_sq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    field_simp [hA.ne']
    nlinarith
  have honeu : 1 + u ^ 2 ≤ b ^ 2 := by
    rw [hb_sq]
    have : 0 ≤ 2 * s.re / A := div_nonneg (mul_nonneg (by norm_num) hs) hA.le
    linarith
  have hub_sq : u ^ 2 ≤ b ^ 2 := le_trans (by linarith) honeu
  have hub : u ≤ b := (sq_le_sq₀ hu hb).mp hub_sq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [pow_add, pow_add]
  rcases le_total u 1 with hu1 | h1u
  · have huk : u ^ k ≤ 1 := pow_le_one₀ hu hu1
    have hubk : u ^ k ≤ b ^ k := pow_le_pow_left₀ hu hub k
    have hb1 : 1 ≤ b := by
      have hbase := chen1973Lemma6_eq17_one_le_norm_one_add_div hA hs
      simpa [b] using hbase
    have hbk1 : 1 ≤ b ^ k := one_le_pow₀ hb1
    calc
      1 + u ^ 2 * u ^ k ≤ 1 + u ^ 2 := by
        have hmul : u ^ 2 * u ^ k ≤ u ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left huk (sq_nonneg u)
        nlinarith
      _ ≤ b ^ 2 := honeu
      _ ≤ b ^ 2 * b ^ k := by
        nlinarith [sq_nonneg b]
  · have huk1 : 1 ≤ u ^ k := one_le_pow₀ h1u
    have hubk : u ^ k ≤ b ^ k := pow_le_pow_left₀ hu hub k
    calc
      1 + u ^ 2 * u ^ k ≤ (1 + u ^ 2) * u ^ k := by
        nlinarith [pow_nonneg hu k]
      _ ≤ b ^ 2 * b ^ k :=
        mul_le_mul honeu hubk (pow_nonneg hu k) (sq_nonneg b)

/-- The exact Mellin norm is bounded by the reciprocal corrected-source
denominator with explicit constant one. -/
theorem chen1973Lemma6_eq17_mellinKernel_norm_le_correctedKernel
    {x : ℕ} (hx : 1 < x) {s : ℂ} (hs : 0 ≤ s.re)
    (horder : 2 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    ‖chen1973MellinKernel (x : ℝ) s‖ ≤
      (chen1973Lemma6Eq17CorrectedKernel x s)⁻¹ := by
  by_cases hs0 : s = 0
  · subst s
    simp [chen1973MellinKernel, chen1973Lemma6Eq17CorrectedKernel]
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hA : 0 < chen1973PerronScale (x : ℝ) :=
    chen1973Lemma6_eq17_perronScale_pos hx
  have hpow := chen1973Lemma6_eq17_one_add_radial_pow_le_complex_pow
    hA hs horder
  have hcomplex : 0 < ‖1 + s / (chen1973PerronScale (x : ℝ) : ℂ)‖ ^
      (chen1973PerronOrder (x : ℝ) + 1) := by
    exact pow_pos (zero_lt_one.trans_le
      (chen1973Lemma6_eq17_one_le_norm_one_add_div hA hs)) _
  have hcorrected : 0 < 1 + (‖s‖ / chen1973PerronScale (x : ℝ)) ^
      (chen1973PerronOrder (x : ℝ) + 1) := by positivity
  unfold chen1973MellinKernel chen1973Lemma6Eq17CorrectedKernel
  rw [norm_div, norm_one, norm_mul, norm_pow]
  simpa [one_div] using inv_anti₀ (mul_pos hsNorm hcorrected)
    (mul_le_mul_of_nonneg_left hpow hsNorm.le)

/-- The corrected-source denominator is nonnegative everywhere. -/
theorem chen1973Lemma6_eq17_correctedKernel_nonneg
    {x : ℕ} (hx : 1 < x) (s : ℂ) :
    0 ≤ chen1973Lemma6Eq17CorrectedKernel x s := by
  unfold chen1973Lemma6Eq17CorrectedKernel
  have hA : 0 < chen1973PerronScale (x : ℝ) :=
    chen1973Lemma6_eq17_perronScale_pos hx
  exact mul_nonneg (norm_nonneg s)
    (add_nonneg zero_le_one
      (pow_nonneg (div_nonneg (norm_nonneg s) hA.le) _))

/-- The corrected-source denominator is positive on every positive vertical
line. -/
theorem chen1973Lemma6_eq17_correctedKernel_pos
    {x : ℕ} (hx : 1 < x) {σ v : ℝ} (hσ : 0 < σ) :
    0 < chen1973Lemma6Eq17CorrectedKernel x (σ + v * I) := by
  unfold chen1973Lemma6Eq17CorrectedKernel
  have hs : 0 < ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hA : 0 < chen1973PerronScale (x : ℝ) :=
    chen1973Lemma6_eq17_perronScale_pos hx
  exact mul_pos hs (by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (pow_nonneg (div_nonneg (norm_nonneg _) hA.le) _))

/-- Reflection symmetry of the corrected-source denominator on vertical lines. -/
theorem chen1973Lemma6Eq17CorrectedKernel_reflection
    (x : ℕ) (a v : ℝ) :
    chen1973Lemma6Eq17CorrectedKernel x (a + (-v) * I) =
      chen1973Lemma6Eq17CorrectedKernel x (a + v * I) := by
  unfold chen1973Lemma6Eq17CorrectedKernel
  have hs : ‖(a : ℂ) + -(v : ℂ) * I‖ = ‖(a : ℂ) + (v : ℂ) * I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  rw [hs]

/-- A normalized `21/10` weakening of the corrected high-power factor. -/
theorem chen1973Lemma6_eq17_correctedFactor_inv_le_rpow_21_div_10
    {u : ℝ} (hu : 0 ≤ u) {N : ℕ} (hN : 3 ≤ N) :
    (1 + u ^ N)⁻¹ ≤ 2 / (1 + u ^ ((21 : ℝ) / 10)) := by
  have hdenN : 0 < 1 + u ^ N := by positivity
  have hdenq : 0 < 1 + u ^ ((21 : ℝ) / 10) := by positivity
  rcases le_total u 1 with hu1 | h1u
  · have huq : u ^ ((21 : ℝ) / 10) ≤ 1 :=
      Real.rpow_le_one hu hu1 (by norm_num)
    have hinv : (1 + u ^ N)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hdenN]
      exact le_add_of_nonneg_right (pow_nonneg hu _)
    calc
      (1 + u ^ N)⁻¹ ≤ 1 := hinv
      _ ≤ 2 / (1 + u ^ ((21 : ℝ) / 10)) := by
        rw [le_div_iff₀ hdenq]
        linarith
  · have hq3 : u ^ ((21 : ℝ) / 10) ≤ u ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1u (by norm_num)
    have h3N : u ^ (3 : ℕ) ≤ u ^ N := pow_le_pow_right₀ h1u hN
    have hden : 1 + u ^ ((21 : ℝ) / 10) ≤ 1 + u ^ N := by linarith
    calc
      (1 + u ^ N)⁻¹ ≤ (1 + u ^ ((21 : ℝ) / 10))⁻¹ :=
        inv_anti₀ hdenq hden
      _ ≤ 2 / (1 + u ^ ((21 : ℝ) / 10)) := by
        rw [div_eq_mul_inv]
        exact le_mul_of_one_le_left (inv_nonneg.mpr hdenq.le) (by norm_num)

/-- A normalized fourth-power weakening of the corrected high-power factor. -/
theorem chen1973Lemma6_eq17_correctedFactor_inv_le_fourth_power
    {u : ℝ} (hu : 0 ≤ u) {N : ℕ} (hN : 4 ≤ N) :
    (1 + u ^ N)⁻¹ ≤ 2 / (1 + u ^ 4) := by
  have hdenN : 0 < 1 + u ^ N := by positivity
  have hden4 : 0 < 1 + u ^ 4 := by positivity
  rcases le_total u 1 with hu1 | h1u
  · have hu4 : u ^ 4 ≤ 1 := pow_le_one₀ hu hu1
    have hinv : (1 + u ^ N)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hdenN]
      exact le_add_of_nonneg_right (pow_nonneg hu _)
    calc
      (1 + u ^ N)⁻¹ ≤ 1 := hinv
      _ ≤ 2 / (1 + u ^ 4) := by
        rw [le_div_iff₀ hden4]
        linarith
  · have h4N : u ^ 4 ≤ u ^ N := pow_le_pow_right₀ h1u hN
    have hden : 1 + u ^ 4 ≤ 1 + u ^ N := by linarith
    calc
      (1 + u ^ N)⁻¹ ≤ (1 + u ^ 4)⁻¹ := inv_anti₀ hden4 hden
      _ ≤ 2 / (1 + u ^ 4) := by
        rw [div_eq_mul_inv]
        exact le_mul_of_one_le_left (inv_nonneg.mpr hden4.le) (by norm_num)

/-- On a vertical line, the corrected factor weakens to the printed downstream
`21/10` weight.  The scale payment is kept explicitly as
`A^(21/10) = (log x)^(231/100)`. -/
theorem chen1973Lemma6_eq17_correctedFactor_vertical_inv_le_21_div_10
    {x : ℕ} (hx : 3 ≤ x) (σ v : ℝ)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
      chen1973PerronScale (x : ℝ)) ^
        (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
      2 * Real.log x ^ ((231 : ℝ) / 100) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := by
  let A := chen1973PerronScale (x : ℝ)
  let u := ‖((σ : ℂ) + (v : ℂ) * I)‖ / A
  let z := |v| / A
  have hA1 : 1 ≤ A := by
    dsimp [A, chen1973PerronScale]
    exact Real.one_le_rpow (chen1973Lemma6_eq17_one_le_log_and_order hx).1
      (by norm_num)
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hz : 0 ≤ z := div_nonneg (abs_nonneg _) hA.le
  have hvnorm : |v| ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    calc
      |v| = |((σ : ℂ) + (v : ℂ) * I).im| := by simp
      _ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := Complex.abs_im_le_norm _
  have hzu : z ≤ u := div_le_div_of_nonneg_right hvnorm hA.le
  have hzq_uq : z ^ ((21 : ℝ) / 10) ≤ u ^ ((21 : ℝ) / 10) :=
    Real.rpow_le_rpow hz hzu (by norm_num)
  have hweak := chen1973Lemma6_eq17_correctedFactor_inv_le_rpow_21_div_10 hu horder
  have hmono : 2 / (1 + u ^ ((21 : ℝ) / 10)) ≤
      2 / (1 + z ^ ((21 : ℝ) / 10)) := by gcongr
  have hscale : 2 / (1 + z ^ ((21 : ℝ) / 10)) ≤
      2 * A ^ ((21 : ℝ) / 10) / (1 + |v| ^ ((21 : ℝ) / 10)) := by
    rw [show z ^ ((21 : ℝ) / 10) =
      |v| ^ ((21 : ℝ) / 10) / A ^ ((21 : ℝ) / 10) by
        dsimp [z]
        rw [Real.div_rpow (abs_nonneg _) hA.le]]
    have hAq : 1 ≤ A ^ ((21 : ℝ) / 10) :=
      Real.one_le_rpow hA1 (by norm_num)
    have hAqpos : 0 < A ^ ((21 : ℝ) / 10) := Real.rpow_pos_of_pos hA _
    have hvq : 0 ≤ |v| ^ ((21 : ℝ) / 10) :=
      Real.rpow_nonneg (abs_nonneg v) _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp [hAqpos.ne']
    nlinarith
  calc
    (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ / A) ^
        (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
        2 / (1 + u ^ ((21 : ℝ) / 10)) := by simpa [u] using hweak
    _ ≤ 2 / (1 + z ^ ((21 : ℝ) / 10)) := hmono
    _ ≤ 2 * A ^ ((21 : ℝ) / 10) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := hscale
    _ = 2 * Real.log x ^ ((231 : ℝ) / 100) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := by
      have hpay : A ^ ((21 : ℝ) / 10) =
          Real.log x ^ ((231 : ℝ) / 100) := by
        dsimp [A, chen1973PerronScale]
        rw [← Real.rpow_mul
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))]
        congr 1
        norm_num
      rw [hpay]

/-- On a vertical line, the corrected factor weakens to the printed downstream
fourth-power weight, with the explicit payment
`A^4 = (log x)^(22/5)`. -/
theorem chen1973Lemma6_eq17_correctedFactor_vertical_inv_le_fourth_power
    {x : ℕ} (hx : 3 ≤ x) (σ v : ℝ)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
      chen1973PerronScale (x : ℝ)) ^
        (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
      2 * Real.log x ^ ((22 : ℝ) / 5) / (1 + |v| ^ 4) := by
  let A := chen1973PerronScale (x : ℝ)
  let u := ‖((σ : ℂ) + (v : ℂ) * I)‖ / A
  let z := |v| / A
  have hA1 : 1 ≤ A := by
    dsimp [A, chen1973PerronScale]
    exact Real.one_le_rpow (chen1973Lemma6_eq17_one_le_log_and_order hx).1
      (by norm_num)
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hz : 0 ≤ z := div_nonneg (abs_nonneg _) hA.le
  have hvnorm : |v| ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    calc
      |v| = |((σ : ℂ) + (v : ℂ) * I).im| := by simp
      _ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := Complex.abs_im_le_norm _
  have hzu : z ≤ u := div_le_div_of_nonneg_right hvnorm hA.le
  have hz4_u4 : z ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ hz hzu 4
  have hweak := chen1973Lemma6_eq17_correctedFactor_inv_le_fourth_power hu horder
  have hmono : 2 / (1 + u ^ 4) ≤ 2 / (1 + z ^ 4) := by gcongr
  have hscale : 2 / (1 + z ^ 4) ≤ 2 * A ^ 4 / (1 + |v| ^ 4) := by
    dsimp [z]
    have hA4 : 1 ≤ A ^ 4 := one_le_pow₀ hA1
    rw [div_pow]
    have hv4 : 0 ≤ |v| ^ 4 := pow_nonneg (abs_nonneg _) _
    have hA4pos : 0 < A ^ 4 := pow_pos hA _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp [hA4pos.ne']
    nlinarith
  calc
    (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ / A) ^
        (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤ 2 / (1 + u ^ 4) := by
      simpa [u] using hweak
    _ ≤ 2 / (1 + z ^ 4) := hmono
    _ ≤ 2 * A ^ 4 / (1 + |v| ^ 4) := hscale
    _ = 2 * Real.log x ^ ((22 : ℝ) / 5) / (1 + |v| ^ 4) := by
      have hpay : A ^ 4 = Real.log x ^ ((22 : ℝ) / 5) := by
        dsimp [A, chen1973PerronScale]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))]
        congr 1
        norm_num
      rw [hpay]

end AnalyticNumberTheory.LargeSieve

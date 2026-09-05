import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticConvolutionContinuation

/-!
# Weighted quadratic convolution and its actual continued constant

This modern partial-summation argument keeps the finite sum and its tail
explicit. The constant is the actual continued product, not a free parameter.
-/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The finite weighted sum of the actual convolution coefficients. -/
noncomputable def quadraticConvolutionWeightedSum
    (χ : DirichletCharacter ℂ q) (β x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, quadraticSiegelConvolution χ n * (n : ℝ) ^ (-β)

omit [NeZero q] in
private theorem convolution_sum_from_zero (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Icc 0 N, quadraticSiegelConvolution χ n =
      quadraticSiegelConvolutionSummatory χ N := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
  simp [quadraticSiegelConvolution, quadraticSiegelConvolutionSummatory]

private theorem rpow_continuousOn (β x : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ β) (Set.Icc 1 x) := by
  intro t ht
  exact (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).continuousWithinAt

omit [NeZero q] in
/-- Exact Abel summation, valid for any real exponent. -/
theorem quadraticConvolutionWeightedSum_eq_abel
    (χ : DirichletCharacter ℂ q) (β x : ℝ) :
    quadraticConvolutionWeightedSum χ β x =
      x ^ (-β) * quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ +
        β * ∫ t in Set.Ioc (1 : ℝ) x,
          quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => t ^ (-β)) (-β * t ^ (-β - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-β))) (Set.Icc 1 x) :=
    (((rpow_continuousOn (-β - 1) x).const_mul (-β)).integrableOn_Icc).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (quadraticSiegelConvolution χ)
    (by simp [quadraticSiegelConvolution]) x (fun t ht => (hd t ht).differentiableAt) hint
  have hs :
      (∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-β) * quadraticSiegelConvolution χ n) =
        quadraticConvolutionWeightedSum χ β x := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊),
      sum_insert (by simp)]
    simp [quadraticSiegelConvolution, quadraticConvolutionWeightedSum, mul_comm]
  rw [hs, convolution_sum_from_zero] at h
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) x,
        deriv (fun t : ℝ => t ^ (-β)) t *
          ∑ n ∈ Icc 0 ⌊t⌋₊, quadraticSiegelConvolution χ n) =
      -β * ∫ t in Set.Ioc (1 : ℝ) x,
        quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, convolution_sum_from_zero]
    ring
  rw [hi] at h
  linarith

theorem quadraticConvolutionErrorKernel_ofReal
    (χ : DirichletCharacter ℂ q) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    quadraticConvolutionErrorKernel χ (β : ℂ) t =
      ((quadraticConvolutionError χ t * t ^ (-β - 1) : ℝ) : ℂ) := by
  rw [quadraticConvolutionErrorKernel, ofReal_mul, Complex.ofReal_cpow ht]
  congr 2
  push_cast
  ring

theorem IsPrimitive.integrableOn_real_quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : 1 / 2 < β) :
    IntegrableOn (fun t : ℝ => quadraticConvolutionError χ t * t ^ (-β - 1))
      (Set.Ioi (1 : ℝ)) := by
  have h := (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel χ hprim hχ
    (s := (β : ℂ)) hβ).re
  exact IntegrableOn.congr_fun h (fun t ht => by
    rw [quadraticConvolutionErrorKernel_ofReal χ β (le_of_lt (lt_trans zero_lt_one ht))]
    rfl) measurableSet_Ioi

/-- The real form of the Mellin constant identification. -/
theorem IsPrimitive.re_riemannZeta_mul_LFunction_eq_real_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) :
    (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re =
      (χ.LFunction 1).re * β / (β - 1) +
        β * ∫ t in Set.Ioi (1 : ℝ),
          quadraticConvolutionError χ t * t ^ (-β - 1) := by
  have h := IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral χ hprim hχ hquad
    (s := (β : ℂ)) hβ (by exact_mod_cast hβ1)
  have hI :
      (quadraticConvolutionErrorIntegral χ (β : ℂ)).re =
        ∫ t in Set.Ioi (1 : ℝ),
          quadraticConvolutionError χ t * t ^ (-β - 1) := by
    calc
      _ = ∫ t in Set.Ioi (1 : ℝ),
          (quadraticConvolutionErrorKernel χ (β : ℂ) t).re :=
        (integral_re (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel
          χ hprim hχ (s := (β : ℂ)) hβ)).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [quadraticConvolutionErrorKernel_ofReal χ β
          (le_of_lt (lt_trans zero_lt_one ht))]
        rfl
  have hmain :
      ((χ.LFunction 1).re : ℂ) * (β : ℂ) / ((β : ℂ) - 1) =
        (((χ.LFunction 1).re * β / (β - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [h, add_re, hmain, ofReal_re, re_ofReal_mul, hI]

private theorem sqrt_mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Real.sqrt t * t ^ (-β - 1) = t ^ (-β - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  congr 1
  ring

/-- Explicit tail payment for the actual summatory error. -/
theorem IsPrimitive.abs_quadraticConvolutionError_tail_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {β x : ℝ} (hβ : 1 / 2 < β) (hx : 1 ≤ x) :
    |∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| ≤
      81 * q * x ^ (1 / 2 - β) / (β - 1 / 2) := by
  have hp : -β - 1 / 2 < -1 := by linarith
  have hx0 : 0 < x := by linarith
  have hg := (integrableOn_Ioi_rpow_of_lt hp hx0).const_mul (81 * (q : ℝ))
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi x),
        ‖quadraticConvolutionError χ t * t ^ (-β - 1)‖ ≤
          81 * q * t ^ (-β - 1 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ (81 * q * Real.sqrt t) * t ^ (-β - 1) :=
        mul_le_mul_of_nonneg_right
          (IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ (hx.trans ht.le))
          (Real.rpow_nonneg ht0.le _)
      _ = _ := by rw [mul_assoc, sqrt_mul_weight ht0]
  have h := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt hp hx0] at h
  rw [show -β - 1 / 2 + 1 = -(β - 1 / 2) by ring,
    div_neg, neg_div, neg_neg] at h
  convert h using 1
  ring_nf

private theorem mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t * t ^ (-β - 1) = t ^ (-β) := by
  calc
    _ = t ^ (1 : ℝ) * t ^ (-β - 1) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

private theorem mul_weight_main {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-β) * t = t ^ (1 - β) := by
  calc
    _ = t ^ (-β) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

/-- Weighted finite expansion with the actual continued product as constant.
The error is exactly one endpoint term minus one convergent tail integral. -/
theorem IsPrimitive.quadraticConvolutionWeightedSum_eq_product_add_tail
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β x : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    quadraticConvolutionWeightedSum χ β x =
      (χ.LFunction 1).re * x ^ (1 - β) / (1 - β) +
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re +
        quadraticConvolutionError χ x * x ^ (-β) -
        β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hE := IsPrimitive.integrableOn_real_quadraticConvolutionErrorKernel χ hprim hχ hβ
  have hEI : IntegrableOn
      (fun t : ℝ => quadraticConvolutionError χ t * t ^ (-β - 1))
      (Set.Ioc 1 x) := hE.mono_set Set.Ioc_subset_Ioi_self
  have hP : IntegrableOn (fun t : ℝ => (χ.LFunction 1).re * t ^ (-β))
      (Set.Ioc 1 x) :=
    ((rpow_continuousOn (-β) x).const_mul _).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) x,
        quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1)) =
      (∫ t in Set.Ioc (1 : ℝ) x,
        quadraticConvolutionError χ t * t ^ (-β - 1)) +
      (χ.LFunction 1).re * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β) := by
    rw [← integral_const_mul, ← integral_add hEI hP]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    unfold quadraticConvolutionError
    rw [sub_mul, mul_assoc t _ _, mul_comm (χ.LFunction 1).re,
      ← mul_assoc t, mul_weight (lt_trans zero_lt_one ht.1)]
    ring
  have hpow :
      (∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β)) =
        (x ^ (1 - β) - 1) / (1 - β) := by
    rw [← intervalIntegral.integral_of_le hx]
    rw [integral_rpow (Or.inr ⟨fun h => hβ1 (by linarith), by
      rw [Set.uIcc_of_le hx]
      simp⟩)]
    simp only [Real.one_rpow]
    rw [show -β + 1 = 1 - β by ring]
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hE hx
  rw [intervalIntegral.integral_of_le hx] at htail
  have hend :
      x ^ (-β) * quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ =
        quadraticConvolutionError χ x * x ^ (-β) +
          (χ.LFunction 1).re * x ^ (1 - β) := by
    unfold quadraticConvolutionError
    rw [sub_mul, mul_assoc x _ _, mul_comm (χ.LFunction 1).re,
      ← mul_assoc x, mul_comm x (x ^ (-β)), mul_weight_main hx0]
    ring
  rw [quadraticConvolutionWeightedSum_eq_abel, hsplit, hpow, hend,
    IsPrimitive.re_riemannZeta_mul_LFunction_eq_real_errorIntegral χ hprim hχ hquad hβ hβ1,
    ← htail]
  have hden : 1 - β ≠ 0 := sub_ne_zero.mpr hβ1.symm
  have hden' : β - 1 ≠ 0 := sub_ne_zero.mpr hβ1
  field_simp
  ring

/-- Uniform explicit weighted asymptotic for every `β > 1/2`, except the pole.
All dependence on the exponent is displayed. -/
theorem IsPrimitive.abs_quadraticConvolutionWeightedSum_sub_main_sub_product_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β x : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    |quadraticConvolutionWeightedSum χ β x -
        (χ.LFunction 1).re * x ^ (1 - β) / (1 - β) -
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re| ≤
      81 * q * (1 + β / (β - 1 / 2)) * x ^ (1 / 2 - β) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβ0 : 0 ≤ β := by linarith
  have hend :
      |quadraticConvolutionError χ x * x ^ (-β)| ≤
        81 * q * x ^ (1 / 2 - β) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (81 * q * Real.sqrt x) * x ^ (-β) :=
        mul_le_mul_of_nonneg_right
          (IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ hx)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
        congr 2
  rw [IsPrimitive.quadraticConvolutionWeightedSum_eq_product_add_tail χ hprim hχ
    hquad hβ hβ1 hx]
  have htriangle := abs_add_le
    (quadraticConvolutionError χ x * x ^ (-β))
    (-(β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)))
  rw [abs_neg] at htriangle
  have htail :
      |β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| ≤
        β * (81 * q * x ^ (1 / 2 - β) / (β - 1 / 2)) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left
      (IsPrimitive.abs_quadraticConvolutionError_tail_le χ hprim hχ hβ hx) hβ0
  convert htriangle.trans (add_le_add hend htail) using 1
  · rfl
  · congr 1
    ring
  · ring

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

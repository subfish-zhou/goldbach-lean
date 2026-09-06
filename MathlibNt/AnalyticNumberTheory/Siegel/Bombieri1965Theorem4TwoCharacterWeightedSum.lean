import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterContinuation

/-!
# Weighted sums of the genuine two-character convolution

Modern Abel summation identifies the actual continued four-factor product as
the constant term. The summatory error supplies an explicit endpoint and tail
remainder. Positivity is used only for the lower bound on the finite sum.
No zero existence or uniform Siegel bound is assumed or asserted.
-/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The finite weighted sum of the real parts of the actual coefficients.
For two quadratic characters these are the coefficients themselves. -/
noncomputable def twoCharacterWeightedSum
    (χ ψ : DirichletCharacter ℂ q) (β x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (twoCharacterConvolution χ ψ n).re * (n : ℝ) ^ (-β)

omit [NeZero q] in
private theorem convolution_sum_from_zero (χ ψ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Icc 0 N, (twoCharacterConvolution χ ψ n).re =
      (twoCharacterSummatory χ ψ N).re := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
  simp [twoCharacterSummatory, Complex.re_sum]

private theorem rpow_continuousOn (β x : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ β) (Set.Icc 1 x) := by
  intro t ht
  exact (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).continuousWithinAt

omit [NeZero q] in
/-- Exact Abel summation, without any quadraticity hypothesis. -/
theorem twoCharacterWeightedSum_eq_abel
    (χ ψ : DirichletCharacter ℂ q) (β x : ℝ) :
    twoCharacterWeightedSum χ ψ β x =
      x ^ (-β) * (twoCharacterSummatory χ ψ ⌊x⌋₊).re +
        β * ∫ t in Set.Ioc (1 : ℝ) x,
          (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => t ^ (-β)) (-β * t ^ (-β - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-β))) (Set.Icc 1 x) :=
    (((rpow_continuousOn (-β - 1) x).const_mul (-β)).integrableOn_Icc).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (twoCharacterConvolution χ ψ n).re)
    (by simp) x (fun t ht => (hd t ht).differentiableAt) hint
  have hs :
      (∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-β) * (twoCharacterConvolution χ ψ n).re) =
        twoCharacterWeightedSum χ ψ β x := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊), sum_insert (by simp)]
    simp [twoCharacterWeightedSum, mul_comm]
  rw [hs, convolution_sum_from_zero] at h
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) x, deriv (fun t : ℝ => t ^ (-β)) t *
          ∑ n ∈ Icc 0 ⌊t⌋₊, (twoCharacterConvolution χ ψ n).re) =
      -β * ∫ t in Set.Ioc (1 : ℝ) x,
        (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, convolution_sum_from_zero]
    ring
  rw [hi] at h
  linarith

theorem re_twoCharacterErrorKernel_ofReal
    (χ ψ : DirichletCharacter ℂ q) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (twoCharacterErrorKernel χ ψ (β : ℂ) t).re =
      (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have hp : (t : ℂ) ^ (-((β : ℂ) + 1)) = ((t ^ (-β - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht]
    congr 1
    push_cast
    ring
  rw [twoCharacterErrorKernel, hp, re_mul_ofReal]

theorem integrableOn_re_twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 < β) :
    IntegrableOn (fun t : ℝ => (twoCharacterError χ ψ t).re * t ^ (-β - 1))
      (Set.Ioi (1 : ℝ)) := by
  have h := (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod
    (s := (β : ℂ)) hβ).re
  exact IntegrableOn.congr_fun h
    (fun t ht => re_twoCharacterErrorKernel_ofReal χ ψ β
      (le_of_lt (lt_trans zero_lt_one ht))) measurableSet_Ioi

/-- Real-part specialization of the actual continued constant. -/
theorem re_twoCharacter_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) :
    (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
        (χ * ψ).LFunction (β : ℂ)).re =
      (twoCharacterResidue χ ψ).re * β / (β - 1) +
        β * ∫ t in Set.Ioi (1 : ℝ), (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have h := twoCharacter_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod
    (s := (β : ℂ)) hβ (by exact_mod_cast hβ1)
  have hI :
      (twoCharacterErrorIntegral χ ψ (β : ℂ)).re =
        ∫ t in Set.Ioi (1 : ℝ), (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
    calc
      _ = ∫ t in Set.Ioi (1 : ℝ), (twoCharacterErrorKernel χ ψ (β : ℂ) t).re :=
        (integral_re
          (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod
            (s := (β : ℂ)) hβ)).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        re_twoCharacterErrorKernel_ofReal χ ψ β (le_of_lt (lt_trans zero_lt_one ht))
  rw [h, add_re, re_ofReal_mul, hI]
  congr 1
  rw [← ofReal_one, ← ofReal_sub, div_ofReal_re, re_mul_ofReal]

/-- The real-part error inherits the proved complex norm bound. -/
theorem abs_re_twoCharacterError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    |(twoCharacterError χ ψ t).re| ≤ 308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) :=
  (abs_re_le_norm _).trans (norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod ht)

private theorem rpow_mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (3 / 4 : ℝ) * t ^ (-β - 1) = t ^ (-β - 1 / 4) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- An explicit bound for the actual convergent error tail. -/
theorem abs_re_twoCharacterError_tail_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ} (hβ : 3 / 4 < β) (hx : 1 ≤ x) :
    |∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| ≤
      308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4) := by
  have hp : -β - 1 / 4 < -1 := by linarith
  have hx0 : 0 < x := by linarith
  have hg := (integrableOn_Ioi_rpow_of_lt hp hx0).const_mul (308 * (q : ℝ) ^ 3)
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi x),
        ‖(twoCharacterError χ ψ t).re * t ^ (-β - 1)‖ ≤
          308 * (q : ℝ) ^ 3 * t ^ (-β - 1 / 4) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ (308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ)) * t ^ (-β - 1) :=
        mul_le_mul_of_nonneg_right
          (abs_re_twoCharacterError_le χ ψ hχ hχquad hψ hprod (hx.trans ht.le))
          (Real.rpow_nonneg ht0.le _)
      _ = _ := by rw [mul_assoc, rpow_mul_weight ht0]
  have h := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt hp hx0] at h
  rw [show -β - 1 / 4 + 1 = -(β - 3 / 4) by ring,
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

/-- Exact finite expansion with the actual continued product as constant,
and with the endpoint and tail terms both displayed. -/
theorem twoCharacterWeightedSum_eq_product_add_tail
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ}
    (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    twoCharacterWeightedSum χ ψ β x =
      (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) +
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
          (χ * ψ).LFunction (β : ℂ)).re +
        (twoCharacterError χ ψ x).re * x ^ (-β) -
        β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hE := integrableOn_re_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod hβ
  have hEI : IntegrableOn
      (fun t : ℝ => (twoCharacterError χ ψ t).re * t ^ (-β - 1))
      (Set.Ioc 1 x) := hE.mono_set Set.Ioc_subset_Ioi_self
  have hP : IntegrableOn (fun t : ℝ => (twoCharacterResidue χ ψ).re * t ^ (-β))
      (Set.Ioc 1 x) :=
    ((rpow_continuousOn (-β) x).const_mul _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) x,
        (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1)) =
      (∫ t in Set.Ioc (1 : ℝ) x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)) +
      (twoCharacterResidue χ ψ).re * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β) := by
    rw [← integral_const_mul, ← integral_add hEI hP]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    simp only [twoCharacterError, sub_re, re_ofReal_mul]
    rw [sub_mul, mul_assoc t _ _, mul_comm (twoCharacterResidue χ ψ).re,
      ← mul_assoc t, mul_weight (lt_trans zero_lt_one ht.1)]
    ring
  have hpow :
      (∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β)) = (x ^ (1 - β) - 1) / (1 - β) := by
    rw [← intervalIntegral.integral_of_le hx]
    rw [integral_rpow (Or.inr ⟨fun h => hβ1 (by linarith), by
      rw [Set.uIcc_of_le hx]
      simp⟩)]
    simp only [Real.one_rpow]
    rw [show -β + 1 = 1 - β by ring]
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hE hx
  rw [intervalIntegral.integral_of_le hx] at htail
  have hend :
      x ^ (-β) * (twoCharacterSummatory χ ψ ⌊x⌋₊).re =
        (twoCharacterError χ ψ x).re * x ^ (-β) +
          (twoCharacterResidue χ ψ).re * x ^ (1 - β) := by
    simp only [twoCharacterError, sub_re, re_ofReal_mul]
    rw [sub_mul, mul_assoc x _ _, mul_comm (twoCharacterResidue χ ψ).re,
      ← mul_assoc x, mul_comm x (x ^ (-β)), mul_weight_main hx0]
    ring
  rw [twoCharacterWeightedSum_eq_abel, hsplit, hpow, hend,
    re_twoCharacter_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod hβ hβ1, ← htail]
  have hden : 1 - β ≠ 0 := sub_ne_zero.mpr hβ1.symm
  have hden' : β - 1 ≠ 0 := sub_ne_zero.mpr hβ1
  field_simp
  ring

/-- The explicit weighted asymptotic, valid for every `β > 3/4`, apart from the pole. -/
theorem abs_twoCharacterWeightedSum_sub_main_sub_product_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ}
    (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    |twoCharacterWeightedSum χ ψ β x -
        (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) -
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
          (χ * ψ).LFunction (β : ℂ)).re| ≤
      308 * (q : ℝ) ^ 3 * (1 + β / (β - 3 / 4)) * x ^ (3 / 4 - β) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβ0 : 0 ≤ β := by linarith
  have hend :
      |(twoCharacterError χ ψ x).re * x ^ (-β)| ≤
        308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 : ℝ)) * x ^ (-β) :=
        mul_le_mul_of_nonneg_right (abs_re_twoCharacterError_le χ ψ hχ hχquad hψ hprod hx)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hx0]
        congr 2
  have htail :
      |β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| ≤
        β * (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4)) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left
      (abs_re_twoCharacterError_tail_le χ ψ hχ hχquad hψ hprod hβ hx) hβ0
  rw [twoCharacterWeightedSum_eq_product_add_tail χ ψ hχ hχquad hψ hprod hβ hβ1 hx]
  calc
    _ = |(twoCharacterError χ ψ x).re * x ^ (-β) -
        β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| := by
      congr 1
      ring
    _ ≤ |(twoCharacterError χ ψ x).re * x ^ (-β)| +
        |β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| :=
      abs_sub _ _
    _ ≤ 308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) +
        β * (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4)) :=
      add_le_add hend htail
    _ = _ := by ring

omit [NeZero q] in
/-- Positivity of every actual coefficient, and the coefficient at one, imply
the finite weighted sum is at least one for every real exponent. -/
theorem one_le_twoCharacterWeightedSum
    (χ ψ : DirichletCharacter ℂ q) (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1)
    (β : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ twoCharacterWeightedSum χ ψ β x := by
  have hfloor : 1 ≤ ⌊x⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have h := Finset.single_le_sum
    (f := fun n : ℕ => (twoCharacterConvolution χ ψ n).re * (n : ℝ) ^ (-β))
    (s := Finset.Icc 1 ⌊x⌋₊) (a := 1)
    (fun n _ => mul_nonneg (twoCharacterConvolution_re_nonneg hχquad hψquad n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (by simp [hfloor])
  simpa [twoCharacterConvolution_one, twoCharacterWeightedSum] using h

/-- The explicit endpoint `(5000 q^3)^8` pays the entire error uniformly for
`β ≥ 7/8`. The proof uses monotonicity of real powers, not a finite scan. -/
theorem twoCharacter_weighted_error_at_large_endpoint_le
    {β : ℝ} (hβ : 7 / 8 ≤ β) :
    308 * (q : ℝ) ^ 3 * (1 + β / (β - 3 / 4)) *
        ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (3 / 4 - β) ≤ 1 / 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq
  have hbase : 1 ≤ 5000 * (q : ℝ) ^ 3 := by linarith
  have hx : 1 ≤ (5000 * (q : ℝ) ^ 3) ^ 8 := one_le_pow₀ hbase
  have hden : 0 < β - 3 / 4 := by linarith
  have hratio : 1 + β / (β - 3 / 4) ≤ 8 := by
    have hr : β / (β - 3 / 4) ≤ 7 := (div_le_iff₀ hden).mpr (by linarith)
    linarith
  have hpower :
      ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (3 / 4 - β) ≤
        (5000 * (q : ℝ) ^ 3)⁻¹ := by
    calc
      _ ≤ ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (-1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (308 * (q : ℝ) ^ 3 * 8) * (5000 * (q : ℝ) ^ 3)⁻¹ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hpower
        (by positivity) (by positivity)
    _ = 308 * 8 / 5000 := by
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ _ := by norm_num

/-- A residue lower bound conditional on an actual real zero of one of the
three L-functions. No zero existence is included in the statement. -/
theorem twoCharacterResidue_re_lower_bound_of_real_zero
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1) (hne : χ ≠ ψ)
    {β : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : χ.LFunction (β : ℂ) = 0 ∨ ψ.LFunction (β : ℂ) = 0 ∨
      (χ * ψ).LFunction (β : ℂ) = 0) :
    (1 - β) / (2 * ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (1 - β)) ≤
      (twoCharacterResidue χ ψ).re := by
  let x : ℝ := (5000 * (q : ℝ) ^ 3) ^ 8
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ 5000 * (q : ℝ) ^ 3 by linarith)
  have hprod := mul_ne_one_of_quadratic_ne hψquad hne
  have hconstant :
      (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
        (χ * ψ).LFunction (β : ℂ)).re = 0 := by
    rcases hzero with hzero | hzero | hzero <;> simp [hzero]
  have herr := abs_twoCharacterWeightedSum_sub_main_sub_product_le
    χ ψ hχ hχquad hψ hprod (show 3 / 4 < β by linarith) hβ1.ne hx
  rw [hconstant, sub_zero] at herr
  have herr' : |twoCharacterWeightedSum χ ψ β x -
      (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β)| ≤ 1 / 2 :=
    herr.trans (twoCharacter_weighted_error_at_large_endpoint_le (q := q) hβ)
  have hsum := one_le_twoCharacterWeightedSum χ ψ hχquad hψquad β hx
  have hmain : (1 / 2 : ℝ) ≤ (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) := by
    linarith [(abs_le.mp herr').2]
  have hd : 0 < 1 - β := by linarith
  have hp : 0 < x ^ (1 - β) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx) _
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hm := (le_div_iff₀ hd).mp hmain
  dsimp only [x] at hm ⊢
  nlinarith

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterPairSummatory
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticHarmonicTruncation
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelTotalDiscrepancy

/-!
# The unprimitive one-character input to the fourfold asymptotic

This modern hyperbola argument uses complete periods, rather than
Pólya--Vinogradov. Its constant is uniform in the actual common modulus.
-/

open Complex Finset
open scoped ComplexOrder

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Ioc_characterAF (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n) = ∑ n ∈ Ioc 0 N, χ n :=
  DirichletCharacter.sum_Ioc_characterArithmeticFunction χ N

private theorem sum_Ioc_zeta (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) = N := by
  calc
    _ = ∑ _n ∈ Ioc 0 N, (1 : ℂ) := by
      apply sum_congr rfl
      intro n hn
      simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
    _ = N := by simp

omit [NeZero q] in
/-- Hyperbola identity specialized to the genuine convolution `ζ * χ`. -/
theorem sum_Ioc_zetaMul_eq_sqrt_hyperbola (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, χ.zetaMul n) =
      (∑ a ∈ Ioc 0 N.sqrt, χ a * ((N / a : ℕ) : ℂ)) +
      (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
      (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) := by
  rw [zetaMul, sum_Ioc_convolution_eq_sqrt_hyperbola]
  simp_rw [sum_Ioc_characterAF, sum_Ioc_zeta]
  have hζ : (∑ a ∈ Ioc 0 N.sqrt,
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) a * ∑ b ∈ Ioc 0 (N / a), χ b) =
      ∑ a ∈ Ioc 0 N.sqrt, ∑ b ∈ Ioc 0 (N / a), χ b := by
    apply sum_congr rfl
    intro a ha
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp ha).1)]
  rw [hζ]
  have hχ : (∑ b ∈ Ioc 0 N.sqrt,
      toArithmeticFunction (χ ·) b * ((N / b : ℕ) : ℂ)) =
      ∑ b ∈ Ioc 0 N.sqrt, χ b * ((N / b : ℕ) : ℂ) := by
    apply sum_congr rfl
    intro b hb
    rw [← χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp hb).1)]
  rw [hχ, add_comm]

theorem norm_LFunction_one_sub_sum_Ioc_div_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 m, χ n / (n : ℂ)‖ ≤
      2 * q / (m + 1 : ℝ) := by
  have h := norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := m + 1) (by omega)
  have hsum : (∑ n ∈ range (m + 1),
      DirichletLAbelWeightVariation.cpowWeight (1 : ℂ) n * χ n) =
      ∑ n ∈ Ioc 0 m, χ n / (n : ℂ) := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m),
      sum_insert (by simp)]
    simp only [DirichletLAbelWeightVariation.cpowWeight, cpow_neg_one,
      Nat.cast_zero, ofReal_zero, inv_zero, zero_mul, zero_add, ofReal_natCast]
    rw [show Icc 1 m = Ioc 0 m from Icc_succ_left_eq_Ioc _ _]
    apply sum_congr rfl
    intro n _
    simp [div_eq_mul_inv, mul_comm]
  rw [hsum] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Complete-period control of the two short arms and the floor error. -/
theorem norm_sum_Ioc_zetaMul_sub_harmonic_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) -
      (N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ ≤
      3 * q * (N.sqrt : ℝ) := by
  have hfloor :
      ‖∑ a ∈ Ioc 0 N.sqrt,
        (χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)))‖ ≤ N.sqrt := by
    calc
      _ ≤ ∑ a ∈ Ioc 0 N.sqrt,
          ‖χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Ioc 0 N.sqrt, (1 : ℝ) := by
        apply sum_le_sum
        intro a ha
        have heq : χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)) =
            χ a * ((((N / a : ℕ) : ℝ) - (N : ℝ) / (a : ℝ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (norm_le_one χ a)
          (abs_natDiv_cast_sub_div_le_one N a (Nat.succ_le_of_lt (mem_Ioc.mp ha).1))
          (abs_nonneg _) (by norm_num)).trans (by norm_num)
      _ = N.sqrt := by simp
  have harm :
      ‖∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a‖ ≤
        (N.sqrt : ℝ) * q := by
    calc
      _ ≤ ∑ b ∈ Ioc 0 N.sqrt, ‖∑ a ∈ Ioc 0 (N / b), χ a‖ := norm_sum_le _ _
      _ ≤ ∑ _b ∈ Ioc 0 N.sqrt, (q : ℝ) := sum_le_sum fun _ _ =>
        (norm_sum_Ioc_character_le_min χ hχ _).trans (min_le_right _ _)
      _ = (N.sqrt : ℝ) * q := by simp
  have hoverlap : ‖(N.sqrt : ℂ) * ∑ a ∈ Ioc 0 N.sqrt, χ a‖ ≤
      (N.sqrt : ℝ) * q := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_Ioc_character_le_min χ hχ _).trans (min_le_right _ _)) (by positivity)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [sum_Ioc_zetaMul_eq_sqrt_hyperbola]
  have heq :
      (∑ a ∈ Ioc 0 N.sqrt, χ a * ((N / a : ℕ) : ℂ)) +
        (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
        (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) -
        (N : ℂ) * (∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)) =
      (∑ a ∈ Ioc 0 N.sqrt,
        (χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)))) +
        (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
        (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) := by
    rw [sum_sub_distrib, ← mul_sum]
    ring
  rw [heq]
  calc
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N.sqrt : ℝ) + (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q :=
      add_le_add (add_le_add hfloor harm) hoverlap
    _ ≤ 3 * q * (N.sqrt : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (Nat.cast_nonneg N.sqrt : (0 : ℝ) ≤ _)]

/-- A uniform, actual complex main term for every nonprincipal character,
including imprimitive characters at the common modulus. -/
theorem norm_sum_Ioc_zetaMul_sub_LFunction_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) - (N : ℂ) * χ.LFunction 1‖ ≤
      7 * q * Real.sqrt N := by
  have hdisc := norm_sum_Ioc_zetaMul_sub_harmonic_main_le χ hχ N
  have htail := norm_LFunction_one_sub_sum_Ioc_div_le χ hχ N.sqrt
  have hmsq : (N.sqrt : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hmle : (N.sqrt : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le hmsq
  have hN : (N : ℝ) ≤ (N.sqrt : ℝ) * N.sqrt + N.sqrt + N.sqrt := by
    exact_mod_cast Nat.sqrt_le_add N
  have hdiv : (N : ℝ) / ((N.sqrt : ℝ) + 1) ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmle)
      (show (0 : ℝ) ≤ (N.sqrt : ℝ) + 1 by positivity)]
  calc
    _ ≤ ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) -
        (N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ +
        (N : ℝ) * ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ := by
      simpa only [← mul_sub, norm_mul, Complex.norm_natCast, norm_sub_rev] using
        norm_sub_le_norm_sub_add_norm_sub
          (∑ n ∈ Ioc 0 N, χ.zetaMul n)
          ((N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ))
          ((N : ℂ) * χ.LFunction 1)
    _ ≤ 3 * q * (N.sqrt : ℝ) + (N : ℝ) * (2 * q / (N.sqrt + 1 : ℝ)) :=
      add_le_add hdisc (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = 3 * q * (N.sqrt : ℝ) + 2 * q * ((N : ℝ) / (N.sqrt + 1 : ℝ)) := by ring
    _ ≤ 3 * q * Real.sqrt N + 2 * q * (2 * Real.sqrt N) := by gcongr
    _ = 7 * q * Real.sqrt N := by ring

/-- A uniform bound on the actual L-value, also valid for imprimitive characters. -/
theorem norm_LFunction_one_le_two_mul_modulus
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 2 * q := by
  simpa [DirichletLAbelWeightVariation.cpowWeight] using
    norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := 1) (by norm_num)

/-- Linear growth of the positive quadratic coefficients with a uniform constant. -/
theorem sum_Ioc_norm_zetaMul_le_nine_mul_modulus
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖χ.zetaMul n‖) ≤ 9 * q * N := by
  have hn (n : ℕ) : ‖χ.zetaMul n‖ = (χ.zetaMul n).re := by
    exact (Complex.re_eq_norm.mpr (zetaMul_nonneg hquad n)).symm
  have hsum : (∑ n ∈ Ioc 0 N, ‖χ.zetaMul n‖) =
      ((∑ n ∈ Ioc 0 N, χ.zetaMul n) : ℂ).re := by simp only [hn, re_sum]
  rw [hsum]
  have h := norm_sum_Ioc_zetaMul_sub_LFunction_main_le χ hχ N
  have hL := norm_LFunction_one_le_two_mul_modulus χ hχ
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    by_cases hN : N = 0
    · simp [hN]
    · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
      exact Real.sqrt_le_self_iff.mpr (Or.inr hN')
  calc
    _ ≤ ‖∑ n ∈ Ioc 0 N, χ.zetaMul n‖ := Complex.re_le_norm _
    _ ≤ ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) - (N : ℂ) * χ.LFunction 1‖ +
        ‖(N : ℂ) * χ.LFunction 1‖ := by
      simpa only [add_comm] using norm_le_insert'
        (∑ n ∈ Ioc 0 N, χ.zetaMul n) ((N : ℂ) * χ.LFunction 1)
    _ ≤ 7 * q * Real.sqrt N + (N : ℝ) * (2 * q) := by
      rw [norm_mul, Complex.norm_natCast]
      exact add_le_add h (mul_le_mul_of_nonneg_left hL (by positivity))
    _ ≤ 7 * q * N + (N : ℝ) * (2 * q) := by gcongr
    _ = 9 * q * N := by ring

end DirichletCharacter

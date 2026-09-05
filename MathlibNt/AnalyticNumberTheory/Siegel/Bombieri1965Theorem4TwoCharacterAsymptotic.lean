import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterPairHarmonic
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterSingleAsymptotic
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterInduction

/-!
# A sublinear error for the genuine fourfold convolution

This modern hyperbola argument combines the actual one-character main term,
positivity, and the harmonic tail of the actual second pair.
-/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Icc_zero_norm_zetaMul (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ n ∈ Finset.Icc 0 m, ‖χ.zetaMul n‖) = ∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, norm_zero, zero_add]
  congr 1

/-- Partial summation of the positive coefficients with the square-root weight. -/
theorem sum_Ioc_norm_zetaMul_div_sqrt_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (m : ℕ) :
    (∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ / Real.sqrt n) ≤ 18 * q * Real.sqrt m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let S : ℝ → ℝ := fun t => ∑ n ∈ Ioc 0 ⌊t⌋₊, ‖χ.zetaMul n‖
  have hS (t : ℝ) (ht : 0 ≤ t) : S t ≤ 9 * q * t :=
    (sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad ⌊t⌋₊).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le ht) (by positivity))
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 (m : ℝ)) :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)))
      (Set.Icc 1 (m : ℝ)) := by
    change IntegrableOn (fun t => deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t)
      (Set.Icc 1 (m : ℝ))
    simp only [Real.deriv_rpow_const]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact ((Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1]))).const_mul
      (-1 / 2)).continuousWithinAt
  have hab := sum_mul_eq_sub_integral_mul₀' (c := fun n => ‖χ.zetaMul n‖)
    (by simp) m hdiff hint
  have hsum :
      (∑ n ∈ Finset.Icc 0 m, (n : ℝ) ^ (-1 / 2 : ℝ) * ‖χ.zetaMul n‖) =
        ∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ / Real.sqrt n := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, norm_zero, mul_zero, zero_add]
    have hI : Finset.Icc 1 m = Ioc 0 m := by ext n; simp; omega
    rw [hI]
    apply sum_congr rfl
    intro n _
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
    ring
  rw [hsum, sum_Icc_zero_norm_zetaMul] at hab
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) m,
        deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, ‖χ.zetaMul n‖) =
      -(∫ t in Set.Ioc (1 : ℝ) m, (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    rw [Real.deriv_rpow_const, sum_Icc_zero_norm_zetaMul]
    dsimp [S]
    norm_num
  rw [hi, sub_neg_eq_add] at hab
  have hSint : IntegrableOn (fun t => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t)
      (Set.Ioc (1 : ℝ) m) := by
    have hlocal := locallyIntegrableOn_mul_sum_Icc (fun n => ‖χ.zetaMul n‖)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (g := fun t : ℝ => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ)) (m := 0) ?_
    · have hc := hlocal.integrableOn_compact_subset
        (show Set.Icc 1 (m : ℝ) ⊆ Set.Ici 1 from fun _ ht => ht.1) isCompact_Icc
      have heq : (fun t => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, ‖χ.zetaMul n‖) =
          fun t => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t := by
        funext t
        rw [sum_Icc_zero_norm_zetaMul]
      rw [heq] at hc
      exact hc.mono_set Set.Ioc_subset_Icc_self
    · exact (show ContinuousOn (fun t : ℝ => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ))
        (Set.Ici 1) from fun t ht =>
          ((Real.continuousAt_rpow_const t _
            (Or.inl (by have : (1 : ℝ) ≤ t := ht; linarith))).const_mul
            (1 / 2)).continuousWithinAt).locallyIntegrableOn measurableSet_Ici
  have hInt :
      (∫ t in Set.Ioc (1 : ℝ) m, (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t) ≤
        9 * q * Real.sqrt m := by
    calc
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) m, (9 * q / 2 : ℝ) * t ^ (-1 / 2 : ℝ) := by
        apply setIntegral_mono_on hSint
          ((show ContinuousOn (fun t : ℝ => (9 * q / 2 : ℝ) * t ^ (-1 / 2 : ℝ))
              (Set.Icc 1 m) from fun t ht =>
            ((Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1]))).const_mul
              (9 * q / 2)).continuousWithinAt).integrableOn_Icc.mono_set
                Set.Ioc_subset_Icc_self) measurableSet_Ioc
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        calc
          _ ≤ (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * (9 * q * t) :=
            mul_le_mul_of_nonneg_left (hS t ht0.le) (by positivity)
          _ = _ := by
            rw [show (-1 / 2 : ℝ) = (-3 / 2 : ℝ) + 1 by norm_num,
              Real.rpow_add ht0, Real.rpow_one]
            ring
      _ = 9 * q * (Real.sqrt m - 1) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hmR,
          integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
        norm_num
        rw [← Real.sqrt_eq_rpow]
        ring
      _ ≤ 9 * q * Real.sqrt m :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hab]
  have hboundary :
      (m : ℝ) ^ (-1 / 2 : ℝ) * (∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖) ≤
        9 * q * Real.sqrt m := by
    calc
      _ ≤ (m : ℝ) ^ (-1 / 2 : ℝ) * (9 * q * m) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad m)
          (by positivity)
      _ = _ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
          Real.rpow_neg (Nat.cast_nonneg m), ← Real.sqrt_eq_rpow]
        have hs : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
        field_simp
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)]
  linarith

private theorem sqrt_natDiv_le (N b : ℕ) :
    Real.sqrt ((N / b : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt b := by
  rw [← Real.sqrt_div (Nat.cast_nonneg N)]
  exact Real.sqrt_le_sqrt Nat.cast_div_le

private theorem norm_sum_zetaMul_natDiv_sub_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N b : ℕ) (hb : 0 < b) :
    ‖(∑ n ∈ Ioc 0 (N / b), χ.zetaMul n) - (N : ℂ) / b * χ.LFunction 1‖ ≤
      7 * q * (Real.sqrt N / Real.sqrt b) + 2 * q := by
  have hmain := norm_sum_Ioc_zetaMul_sub_LFunction_main_le χ hχ (N / b)
  have hL := norm_LFunction_one_le_two_mul_modulus χ hχ
  have hfloor :
      ‖(((N / b : ℕ) : ℂ) - (N : ℂ) / b) * χ.LFunction 1‖ ≤ 2 * q := by
    rw [norm_mul]
    have hnorm : ‖((N / b : ℕ) : ℂ) - (N : ℂ) / b‖ ≤ 1 := by
      have h := abs_natDiv_cast_sub_div_le_one N b (by omega)
      simpa only [← ofReal_natCast, ← ofReal_div, ← ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using h
    exact (mul_le_mul hnorm hL (norm_nonneg _) (by norm_num)).trans (by simp)
  calc
    _ = ‖((∑ n ∈ Ioc 0 (N / b), χ.zetaMul n) -
        ((N / b : ℕ) : ℂ) * χ.LFunction 1) +
        (((N / b : ℕ) : ℂ) - (N : ℂ) / b) * χ.LFunction 1‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 7 * q * Real.sqrt ((N / b : ℕ) : ℝ) + 2 * q := add_le_add hmain hfloor
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sqrt_natDiv_le N b)
        (show (0 : ℝ) ≤ 7 * q by positivity)) le_rfl

omit [NeZero q] in
private theorem norm_pair_le_norm_zetaMul
    (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)) n‖ ≤
      ‖χ.zetaMul n‖ := by
  rw [character_mul_product_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_le_one ψ n) (norm_nonneg _)).trans (by simp)

set_option maxHeartbeats 800000 in
/-- A genuinely sublinear uniform error, with the actual product of three
L-values as main-term coefficient. The second character need not be
quadratic; its two pair factors must be nonprincipal. -/
theorem norm_sum_Ioc_twoCharacterConvolution_sub_residue_main_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, twoCharacterConvolution χ ψ n) -
      (N : ℂ) * twoCharacterResidue χ ψ‖ ≤ 300 * (q : ℝ) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  let m := N.sqrt
  let A : ArithmeticFunction ℂ := χ.zetaMul
  let B : ArithmeticFunction ℂ :=
    toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)
  let AS : ℕ → ℂ := fun n => ∑ a ∈ Ioc 0 n, A a
  let BS : ℕ → ℂ := fun n => ∑ a ∈ Ioc 0 n, B a
  let H : ℂ := ∑ b ∈ Ioc 0 m, B b / (b : ℂ)
  let U : ℂ := ∑ a ∈ Ioc 0 m, A a * BS (N / a)
  let V : ℂ := ∑ b ∈ Ioc 0 m, B b * AS (N / b)
  let T : ℂ := (N : ℂ) * χ.LFunction 1 * H
  have hI (n : ℕ) : Finset.Icc 1 n = Ioc 0 n := by ext a; simp; omega
  have hm : 1 ≤ m := Nat.sqrt_pos.mpr hN
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsm1 : 1 ≤ Real.sqrt (m : ℝ) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hmR)
  have hmle : (m : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  have hB (n : ℕ) : ‖B n‖ ≤ ‖A n‖ := norm_pair_le_norm_zetaMul χ ψ n
  have hAnorm : (∑ a ∈ Ioc 0 m, ‖A a‖) ≤ 9 * q * m :=
    sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad m
  have hBnorm : (∑ b ∈ Ioc 0 m, ‖B b‖) ≤ 9 * q * m :=
    (sum_le_sum fun b _ => hB b).trans hAnorm
  have hAweight : (∑ a ∈ Ioc 0 m, ‖A a‖ / Real.sqrt a) ≤ 18 * q * Real.sqrt m :=
    sum_Ioc_norm_zetaMul_div_sqrt_le χ hχ hquad m
  have hBweight : (∑ b ∈ Ioc 0 m, ‖B b‖ / Real.sqrt b) ≤ 18 * q * Real.sqrt m :=
    (sum_le_sum fun b _ =>
      div_le_div_of_nonneg_right (hB b) (Real.sqrt_nonneg _)).trans hAweight
  have hBS (n : ℕ) : ‖BS n‖ ≤ 3 * q * Real.sqrt n := by
    simpa only [hI] using
      norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ (χ * ψ) hψ hprod n
  have hU : ‖U‖ ≤ 54 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m := by
    calc
      _ ≤ ∑ a ∈ Ioc 0 m, ‖A a‖ * ‖BS (N / a)‖ := by
        simpa only [U, norm_mul] using norm_sum_le (Ioc 0 m) (fun a => A a * BS (N / a))
      _ ≤ ∑ a ∈ Ioc 0 m, ‖A a‖ * (3 * q * (Real.sqrt N / Real.sqrt a)) := by
        apply sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left
          ((hBS _).trans (mul_le_mul_of_nonneg_left (sqrt_natDiv_le N a) (by positivity)))
          (norm_nonneg _)
      _ = (3 * q * Real.sqrt N) * ∑ a ∈ Ioc 0 m, ‖A a‖ / Real.sqrt a := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
      _ ≤ (3 * q * Real.sqrt N) * (18 * q * Real.sqrt m) :=
        mul_le_mul_of_nonneg_left hAweight (by positivity)
      _ = _ := by ring
  have hV : ‖V - T‖ ≤
      126 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m + 18 * (q : ℝ) ^ 2 * m := by
    have heq : V - T =
        ∑ b ∈ Ioc 0 m, B b * (AS (N / b) - (N : ℂ) / b * χ.LFunction 1) := by
      dsimp [V, T, H]
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro b _
      ring
    rw [heq]
    calc
      _ ≤ ∑ b ∈ Ioc 0 m,
          ‖B b‖ * ‖AS (N / b) - (N : ℂ) / b * χ.LFunction 1‖ := by
        simpa only [norm_mul] using norm_sum_le (Ioc 0 m)
          (fun b => B b * (AS (N / b) - (N : ℂ) / b * χ.LFunction 1))
      _ ≤ ∑ b ∈ Ioc 0 m,
          ‖B b‖ * (7 * q * (Real.sqrt N / Real.sqrt b) + 2 * q) := by
        apply sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left
          (norm_sum_zetaMul_natDiv_sub_main_le χ hχ N b (mem_Ioc.mp hb).1) (norm_nonneg _)
      _ = (7 * q * Real.sqrt N) * (∑ b ∈ Ioc 0 m, ‖B b‖ / Real.sqrt b) +
          (2 * q) * (∑ b ∈ Ioc 0 m, ‖B b‖) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro b _
        ring
      _ ≤ (7 * q * Real.sqrt N) * (18 * q * Real.sqrt m) +
          (2 * q) * (9 * q * m) :=
        add_le_add (mul_le_mul_of_nonneg_left hBweight (by positivity))
          (mul_le_mul_of_nonneg_left hBnorm (by positivity))
      _ = _ := by ring
  have hT : ‖T - (N : ℂ) * twoCharacterResidue χ ψ‖ ≤
      18 * (q : ℝ) ^ 2 * ((N : ℝ) / Real.sqrt m) := by
    have htail : ‖H - ψ.LFunction 1 * (χ * ψ).LFunction 1‖ ≤
        9 * q / Real.sqrt m := by
      simpa only [hI, norm_sub_rev] using
        norm_LFunction_one_mul_sub_characterPair_harmonic_le ψ (χ * ψ) hψ hprod hm
    have heq : T - (N : ℂ) * twoCharacterResidue χ ψ =
        (N : ℂ) * χ.LFunction 1 * (H - ψ.LFunction 1 * (χ * ψ).LFunction 1) := by
      dsimp [T, twoCharacterResidue]
      ring
    rw [heq, norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((N : ℝ) * (2 * q)) * (9 * q / Real.sqrt m) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (norm_LFunction_one_le_two_mul_modulus χ hχ) (by positivity))
          htail (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hO : ‖AS m * BS m‖ ≤ 27 * (q : ℝ) ^ 2 * m * Real.sqrt m := by
    rw [norm_mul]
    calc
      _ ≤ (9 * q * m) * (3 * q * Real.sqrt m) :=
        mul_le_mul ((norm_sum_le _ _).trans hAnorm) (hBS m) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hNdiv : (N : ℝ) / Real.sqrt m ≤ 2 * Real.sqrt N * Real.sqrt m := by
    have hsN : Real.sqrt (N : ℝ) ≤ 2 * m := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have hNle : (N : ℝ) ≤ (m : ℝ) * m + m + m := by
        exact_mod_cast Nat.sqrt_le_add N
      nlinarith
    rw [div_le_iff₀ hsm]
    nlinarith [Real.sq_sqrt hN0.le, Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity),
      mul_le_mul_of_nonneg_left hsN (Real.sqrt_nonneg (N : ℝ))]
  have hmsmall : (m : ℝ) ≤ Real.sqrt N * Real.sqrt m := by
    nlinarith [mul_le_mul_of_nonneg_left hsm1 (show (0 : ℝ) ≤ m by positivity)]
  have hOm : (m : ℝ) * Real.sqrt m ≤ Real.sqrt N * Real.sqrt m :=
    mul_le_mul_of_nonneg_right hmle hsm.le
  have heq :
      (∑ n ∈ Ioc 0 N, twoCharacterConvolution χ ψ n) -
        (N : ℂ) * twoCharacterResidue χ ψ =
      U + (V - T) + (T - (N : ℂ) * twoCharacterResidue χ ψ) - AS m * BS m := by
    have hid := sum_Ioc_convolution_eq_sqrt_hyperbola A B N
    have hconv : twoCharacterConvolution χ ψ = A * B := by
      dsimp [twoCharacterConvolution, A, B]
      rw [mul_assoc]
    rw [hconv, hid]
    dsimp [U, V, AS, BS, m]
    ring
  have hpower : Real.sqrt N * Real.sqrt m ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmle) (Real.sqrt_nonneg _)
      _ = _ := by
        simp_rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        norm_num
  rw [heq]
  calc
    _ ≤ ‖U‖ + ‖V - T‖ + ‖T - (N : ℂ) * twoCharacterResidue χ ψ‖ + ‖AS m * BS m‖ :=
      (norm_sub_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (54 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m) +
        (126 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m + 18 * (q : ℝ) ^ 2 * m) +
        (18 * (q : ℝ) ^ 2 * ((N : ℝ) / Real.sqrt m)) +
        (27 * (q : ℝ) ^ 2 * m * Real.sqrt m) :=
      add_le_add (add_le_add (add_le_add hU hV) hT) hO
    _ ≤ 300 * (q : ℝ) ^ 2 * (Real.sqrt N * Real.sqrt m) := by
      nlinarith [mul_le_mul_of_nonneg_left hNdiv (show (0 : ℝ) ≤ 18 * (q : ℝ) ^ 2 by positivity),
        mul_le_mul_of_nonneg_left hmsmall (show (0 : ℝ) ≤ 18 * (q : ℝ) ^ 2 by positivity),
        mul_le_mul_of_nonneg_left hOm (show (0 : ℝ) ≤ 27 * (q : ℝ) ^ 2 by positivity),
        mul_nonneg (sq_nonneg (q : ℝ)) (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hsm.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

/-- The common-level, distinct quadratic case, with no primitive or coprime
conductor hypothesis. -/
theorem norm_sum_Icc_twoCharacterConvolution_sub_residue_main_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1) (hne : χ ≠ ψ) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, twoCharacterConvolution χ ψ n) -
      (N : ℂ) * twoCharacterResidue χ ψ‖ ≤
        300 * (q : ℝ) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hI : Finset.Icc 1 N = Ioc 0 N := by ext n; simp; omega
  rw [hI]
  exact norm_sum_Ioc_twoCharacterConvolution_sub_residue_main_le
    χ ψ hχ hχquad hψ (mul_ne_one_of_quadratic_ne hψquad hne) N

/-- A crude uniform norm bound for the actual residue, used only to pay
the change from a natural endpoint to a real endpoint. -/
theorem norm_twoCharacterResidue_le_eight_mul_modulus_cubed
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    ‖twoCharacterResidue χ ψ‖ ≤ 8 * (q : ℝ) ^ 3 := by
  rw [twoCharacterResidue, norm_mul, norm_mul]
  calc
    _ ≤ ((2 * (q : ℝ)) * (2 * q)) * (2 * q) :=
      mul_le_mul
        (mul_le_mul (norm_LFunction_one_le_two_mul_modulus χ hχ)
          (norm_LFunction_one_le_two_mul_modulus ψ hψ) (norm_nonneg _) (by positivity))
        (norm_LFunction_one_le_two_mul_modulus (χ * ψ) hprod) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Real-endpoint version of the genuine fourfold main term. The additional
power of the common modulus pays only the endpoint displacement. -/
theorem norm_sum_Icc_floor_twoCharacterConvolution_sub_residue_main_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1) (hne : χ ≠ ψ)
    {X : ℝ} (hX : 1 ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twoCharacterConvolution χ ψ n) -
      (X : ℂ) * twoCharacterResidue χ ψ‖ ≤
        308 * (q : ℝ) ^ 3 * X ^ (3 / 4 : ℝ) := by
  have hf := Nat.floor_le (show 0 ≤ X by linarith)
  have herror : |(⌊X⌋₊ : ℝ) - X| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.lt_floor_add_one X]
  have he : ‖((⌊X⌋₊ : ℂ) - (X : ℂ)) * twoCharacterResidue χ ψ‖ ≤
      8 * (q : ℝ) ^ 3 := by
    rw [norm_mul]
    have hc : ‖(⌊X⌋₊ : ℂ) - (X : ℂ)‖ ≤ 1 := by
      simpa only [← ofReal_natCast, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using herror
    exact (mul_le_mul hc
      (norm_twoCharacterResidue_le_eight_mul_modulus_cubed
        χ ψ hχ hψ (mul_ne_one_of_quadratic_ne hψquad hne))
      (norm_nonneg _) (by norm_num)).trans (by simp)
  have hp : (⌊X⌋₊ : ℝ) ^ (3 / 4 : ℝ) ≤ X ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hf (by norm_num)
  have hp1 : 1 ≤ X ^ (3 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hX
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqq : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hq)]
  calc
    _ = ‖((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twoCharacterConvolution χ ψ n) -
        (⌊X⌋₊ : ℂ) * twoCharacterResidue χ ψ) +
        ((⌊X⌋₊ : ℂ) - (X : ℂ)) * twoCharacterResidue χ ψ‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 300 * (q : ℝ) ^ 2 * (⌊X⌋₊ : ℝ) ^ (3 / 4 : ℝ) + 8 * (q : ℝ) ^ 3 :=
      add_le_add
        (norm_sum_Icc_twoCharacterConvolution_sub_residue_main_le χ ψ hχ hψ hχquad hψquad hne _)
        he
    _ ≤ 300 * (q : ℝ) ^ 3 * X ^ (3 / 4 : ℝ) +
        8 * (q : ℝ) ^ 3 * X ^ (3 / 4 : ℝ) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hqq (by norm_num)) hp (by positivity) (by positivity)
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp1 (show (0 : ℝ) ≤ 8 * (q : ℝ) ^ 3 by positivity)
    _ = _ := by ring

end DirichletCharacter

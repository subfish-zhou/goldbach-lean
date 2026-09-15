import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterPairContinuation

/-!
# The harmonic tail of the genuine character pair

This modern partial-summation argument combines square-root cancellation with
the proved Mellin continuation. The constant in the harmonic approximation
is the actual product of L-values at one.
-/

open Complex Finset Filter MeasureTheory Set
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Icc_zero_eq_sum_Icc_one (f : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), Finset.sum_insert]
  · simp
  · simp

omit [NeZero q] in
private theorem characterPair_abel (ψ η : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ n ∈ Finset.Icc 1 m,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ)) =
      characterPairSummatory ψ η m / (m : ℂ) +
        ∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t := by
  let c : ArithmeticFunction ℂ :=
    toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ)
  have hderiv (t : ℝ) (ht : 0 < t) :
      deriv f t = -((t : ℂ) ^ (-(1 + 1 : ℂ))) := by
    rw [show deriv f t = deriv (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) t from rfl,
      deriv_ofReal_cpow_const ht.ne' (by norm_num)]
    norm_num
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 (m : ℝ)) :
      DifferentiableAt ℝ f t :=
    differentiableAt_id.ofReal_cpow_const (by dsimp; linarith [ht.1]) (by norm_num)
  have hint : IntegrableOn (deriv f) (Set.Icc 1 (m : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr
      (f := fun t : ℝ => -((t : ℂ) ^ (-(1 + 1 : ℂ))))
    · intro t ht
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (by linarith [ht.1]))).neg.continuousWithinAt
    · intro t ht
      exact hderiv t (by linarith [ht.1])
  have h := sum_mul_eq_sub_integral_mul₀' (c := (c : ℕ → ℂ))
    c.map_zero m hdiff hint
  have hsum :
      (∑ n ∈ Finset.Icc 0 m, f n * c n) =
        ∑ n ∈ Finset.Icc 1 m, c n / (n : ℂ) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), Finset.sum_insert]
    · simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
      apply sum_congr rfl
      intro n _
      simp [f, cpow_neg_one, div_eq_mul_inv, mul_comm]
    · simp
  have hint_eq :
      (∫ t in Ioc (1 : ℝ) m, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hderiv t (by linarith [ht.1]), sum_Icc_zero_eq_sum_Icc_one]
    simp [characterPairKernel, characterPairSummatory, c, mul_comm]
  rw [hsum, sum_Icc_zero_eq_sum_Icc_one, hint_eq, sub_neg_eq_add] at h
  simpa only [f, cpow_neg_one, characterPairSummatory, Nat.floor_natCast, ofReal_natCast,
    div_eq_mul_inv, mul_comm, c] using h

/-- An exact tail identity with the actual product of L-values. -/
theorem LFunction_one_mul_sub_characterPair_harmonic_eq
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ψ.LFunction 1 * η.LFunction 1 -
      (∑ n ∈ Finset.Icc 1 m,
        (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ)) =
      (∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t) -
        characterPairSummatory ψ η m / (m : ℂ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hi := integrableOn_characterPairKernel ψ η hψ hη (s := 1) (by norm_num)
  have hsplit : characterPairIntegral ψ η 1 =
      (∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t) +
        ∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t := by
    have hunion : Ioc (1 : ℝ) m ∪ Ioi (m : ℝ) = Ioi (1 : ℝ) :=
      Ioc_union_Ioi_eq_Ioi hmR
    have hdisj : Disjoint (Ioc (1 : ℝ) m) (Ioi (m : ℝ)) :=
      Ioc_disjoint_Ioi_same
    unfold characterPairIntegral
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hi.mono_set fun _ ht => ht.1) (hi.mono_set (Ioi_subset_Ioi hmR))
  rw [LFunction_one_mul_eq_characterPairIntegral ψ η hψ hη,
    characterPair_abel ψ η, hsplit]
  ring

theorem norm_characterPairKernel_one_le (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {t : ℝ} (ht : 0 < t) :
    ‖characterPairKernel ψ η 1 t‖ ≤ 3 * q * t ^ (-3 / 2 : ℝ) := by
  rw [characterPairKernel, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
  have hb := norm_sum_Icc_floor_character_pair_convolution_le_three_mul_sqrt
    ψ η hψ hη ht.le
  calc
    _ ≤ (3 * q * Real.sqrt t) * t ^ (-(1 + 1 : ℂ)).re :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht.le _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht]
      norm_num

/-- The convergent integral tail costs at most `6 q / sqrt m`. -/
theorem norm_integral_Ioi_characterPairKernel_one_le
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖∫ t in Ioi x, characterPairKernel ψ η 1 t‖ ≤ 6 * q / Real.sqrt x := by
  calc
    _ ≤ ∫ t in Ioi x, 3 * (q : ℝ) * t ^ (-3 / 2 : ℝ) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hx).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_characterPairKernel_one_le ψ η hψ hη (hx.trans ht)
    _ = 6 * q / Real.sqrt x := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx]
      norm_num
      rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
      ring

/-- Quantitative conditional harmonic convergence to the actual L-value
product, uniform at the common modulus. -/
theorem norm_LFunction_one_mul_sub_characterPair_harmonic_le
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖ψ.LFunction 1 * η.LFunction 1 -
      (∑ n ∈ Finset.Icc 1 m,
        (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ))‖ ≤
      9 * q / Real.sqrt m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hb : ‖characterPairSummatory ψ η m / (m : ℂ)‖ ≤ 3 * q / Real.sqrt m := by
    rw [norm_div, Complex.norm_natCast]
    calc
      _ ≤ (3 * q * Real.sqrt m) / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        simpa [characterPairSummatory] using
          norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ η hψ hη m
      _ = 3 * q / Real.sqrt m := by
        rw [div_eq_div_iff (ne_of_gt hmR) (ne_of_gt hs)]
        nlinarith [Real.sq_sqrt hmR.le]
  rw [LFunction_one_mul_sub_characterPair_harmonic_eq ψ η hψ hη hm]
  calc
    _ ≤ ‖∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t‖ +
        ‖characterPairSummatory ψ η m / (m : ℂ)‖ := norm_sub_le _ _
    _ ≤ 6 * q / Real.sqrt m + 3 * q / Real.sqrt m :=
      add_le_add (norm_integral_Ioi_characterPairKernel_one_le ψ η hψ hη hmR) hb
    _ = 9 * q / Real.sqrt m := by ring

end DirichletCharacter

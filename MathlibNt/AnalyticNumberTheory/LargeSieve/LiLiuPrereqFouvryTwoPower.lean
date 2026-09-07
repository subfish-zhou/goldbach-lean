import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPowerRoots

/-!
# Primitive Kloosterman estimates at powers of two

The square-zero layer localizes the sum to unit quadratic roots modulo the
smaller half-power. Four roots and the exact size of the reduction fibers
suffice: the factor `k+1` absorbs the elementary stationary-phase constant.
No odd-characteristic Gauss-sum identity is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem two_power_layer_norm_le (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q ∣ r) (a d : ℤ) :
    ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
      (r : ℝ) * ((univ.filter fun v : ZMod q ↦
        IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)).card : ℝ) := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  let s := univ.filter fun v : ZMod q ↦
    IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)
  have ht : (r : ZMod (q * r)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨c, hc⟩ := hqr
    exact ⟨c, by rw [hc]; ring⟩
  have hloc := completeKloosterman_square_zero_localization (q * r)
    (a : ZMod (q * r)) (r : ZMod (q * r)) d ht
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero] at hloc
  have hnorm :
      ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
        ((univ.filter fun u : ZMod (q * r) ↦
          IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card : ℝ) := by
    rw [hloc]
    convert norm_sum_le univ (fun u : ZMod (q * r) ↦
      if IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)
      then ZMod.stdAddChar ((a : ZMod (q * r)) * u + (d : ZMod (q * r)) * u⁻¹)
      else 0) using 1
    simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]
  have hcard :
      (univ.filter fun u : ZMod (q * r) ↦
        IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card ≤ s.card * r := by
    rw [← zmod_reduction_preimage_card]
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact ⟨hu.1.map f, hu.2⟩
  exact hnorm.trans (by exact_mod_cast hcard.trans_eq (Nat.mul_comm s.card r))

private theorem two_power_stationary_bound (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (a d : ℤ) (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ (n + m)) (a : ZMod (2 ^ (n + m))) d‖ ≤
      4 * (2 : ℝ) ^ m := by
  have hroot :
      (univ.filter fun v : ZMod (2 ^ n) ↦
        IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card ≤ 4 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    convert! two_power_unit_quadratic_root_card_le_four j a d ha using 1
  have hl := two_power_layer_norm_le (2 ^ n) (2 ^ m) (pow_dvd_pow 2 hnm) a d
  suffices h : ‖completeKloosterman (2 ^ n * 2 ^ m)
      (a : ZMod (2 ^ n * 2 ^ m)) d‖ ≤ 4 * (2 : ℝ) ^ m by
    convert! h using 1
    exact congrArg norm (two_power_modulus_congr _ _ (pow_add 2 n m) a d)
  refine hl.trans ?_
  have hr : ((univ.filter fun v : ZMod (2 ^ n) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card : ℝ) ≤ 4 :=
    by exact_mod_cast hroot
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
    mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ (2 ^ m : ℕ) by positivity)

private theorem two_power_trivial_norm_le (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤ (q : ℝ) := by
  classical
  rw [completeKloosterman_eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _u : ZMod q, (1 : ℝ) := by
      apply sum_le_sum
      intro u _
      split_ifs <;> simp
    _ = (q : ℝ) := by simp

private theorem two_power_sqrt_even (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ n := by
  rw [mul_comm 2 n, pow_mul, Real.sqrt_sq (by positivity)]

private theorem two_power_sqrt_odd (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n + 1)) = (2 : ℝ) ^ n * Real.sqrt 2 := by
  rw [pow_succ, Real.sqrt_mul (by positivity), two_power_sqrt_even]

private theorem two_power_odd_coefficient_bound :
    (8 : ℝ) ≤ 6 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private theorem two_power_primitive_odd_left (k : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  by_cases hk : k < 4
  · have ht := two_power_trivial_norm_le (2 ^ k) a d
    have hs : (2 : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num only [pow_one, Nat.cast_add, Nat.cast_one]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_nonneg (2 : ℝ)
        nlinarith
      · norm_num [show Real.sqrt (4 : ℝ) = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ,
          pow_zero, one_mul]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
        have hp := Real.sqrt_nonneg (8 : ℝ)
        nlinarith
    exact ht.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs)
  · have hk4 : 4 ≤ k := by omega
    obtain ⟨n, he | ho⟩ := Nat.even_or_odd' k
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n n (by omega) le_rfl a d ha
      rw [show n + n = 2 * n by omega] at ht
      rw [two_power_sqrt_even]
      refine ht.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show 4 ≤ 2 * n + 1 by omega)
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n (n + 1) (by omega) (by omega) a d ha
      rw [show n + (n + 1) = 2 * n + 1 by omega] at ht
      rw [two_power_sqrt_odd]
      refine ht.trans ?_
      have hc : (6 : ℝ) ≤ ((2 * n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 2 * n + 1 + 1)
      have hcoef := two_power_odd_coefficient_bound.trans
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg 2))
      calc
        4 * (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 8 := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ n * (((2 * n + 1 + 1 : ℕ) : ℝ) * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = _ := by ring

/-- Primitive Weil-type bound at every power of two, including modulus one.
The elementary stationary bound is absorbed by the divisor factor `k+1`. -/
theorem completeKloosterman_two_power_primitive_weil (k : ℕ) (a d : ℤ)
    (hprimitive : ¬ (2 : ℤ) ∣ a ∨ ¬ (2 : ℤ) ∣ d) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  rcases hprimitive with ha | hd
  · exact two_power_primitive_odd_left k a d ha
  · rw [completeKloosterman_symm]
    exact two_power_primitive_odd_left k d a hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

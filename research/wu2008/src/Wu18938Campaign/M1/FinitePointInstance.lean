import Wu18938Campaign.M1.FourFactorPoint

namespace Wu18938Campaign.M1

private theorem lt_rpow_div_of_pow_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m n : ℕ} (hn : 0 < n) (h : x ^ n < y ^ m) :
    x < y ^ ((m : ℝ) / n) := by
  apply (Real.rpow_lt_rpow_iff hx (Real.rpow_nonneg hy _)
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  rw [← Real.rpow_mul hy, div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  simpa only [Real.rpow_natCast] using h

private theorem rpow_div_le_of_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m n : ℕ} (hn : 0 < n) (h : x ^ m ≤ y ^ n) :
    x ^ ((m : ℝ) / n) ≤ y := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hx _) hy
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  rw [← Real.rpow_mul hx, div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  simpa only [Real.rpow_natCast] using h

theorem finite_original_shape :
    FourFactorShape 392866 3 19 23 29 31
      ((392866 : ℝ) ^ (1 / 18 : ℝ))
      ((392866 : ℝ) ^ (5 / 19 : ℝ))
      ((392866 : ℝ) ^ (1 / 2 - 3 * (1 / 18 : ℝ)))
      ((392866 : ℝ) ^ (1 / 3 : ℝ))
      ((392866 : ℝ) ^ (1 / 2 - 2 * (1 / 18 : ℝ))) := by
  refine {
    primeIndex := by norm_num
    indexBound := by norm_num
    complement := by norm_num
    primeA := by norm_num
    primeB := by norm_num
    primeC := by norm_num
    primeD := by norm_num
    coprime := by norm_num
    ab := by norm_num
    bc := by norm_num
    cd := by norm_num
    za := ?_
    cw := ?_
    wd := ?_
    du := ?_
    uv := ?_
    crossing := ?_
  }
  · simpa only [Nat.cast_one, Nat.cast_ofNat] using rpow_div_le_of_pow_le
      (x := 392866) (y := 19) (m := 1) (n := 18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact lt_rpow_div_of_pow_lt (m := 5) (n := 19)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rpow_div_le_of_pow_le (m := 5) (n := 19)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [show (1 / 2 : ℝ) - 3 * (1 / 18) = 1 / 3 by norm_num]
    simpa only [Nat.cast_one, Nat.cast_ofNat] using lt_rpow_div_of_pow_lt
      (x := 31) (y := 392866) (m := 1) (n := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num
  · norm_num only [show (1 / 2 : ℝ) - 2 * (1 / 18) = 7 / 18 by norm_num]
    exact rpow_div_le_of_pow_le (m := 7) (n := 18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_original_parameters :
    let κ₁ : ℝ := 1 / 18
    let κ₂ : ℝ := 5 / 19
    4 ≤ (392866 : ℕ) ∧ Even (392866 : ℕ) ∧
      1 / 18 ≤ κ₁ ∧ κ₁ < κ₂ ∧
      3 * κ₁ + κ₂ < 1 / 2 ∧ 3 * κ₁ - κ₂ < 1 / 6 ∧
      2 ≤ (392866 : ℝ) ^ κ₁ := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (lt_rpow_div_of_pow_lt (x := 2) (y := 392866) (m := 1) (n := 18)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).le

theorem finite_original_point_residual_one :
    let z := (392866 : ℝ) ^ (1 / 18 : ℝ)
    let w := (392866 : ℝ) ^ (5 / 19 : ℝ)
    let u := (392866 : ℝ) ^ (1 / 2 - 3 * (1 / 18 : ℝ))
    let v := (392866 : ℝ) ^ (1 / 3 : ℝ)
    let V := (392866 : ℝ) ^ (1 / 2 - 2 * (1 / 18 : ℝ))
    pointExcess 392866 3 z w u V - pointGains 392866 3 z w u v = 1 :=
  finite_original_shape.full_signed_residual_one

theorem finite_original_point_payment_fails :
    let z := (392866 : ℝ) ^ (1 / 18 : ℝ)
    let w := (392866 : ℝ) ^ (5 / 19 : ℝ)
    let u := (392866 : ℝ) ^ (1 / 2 - 3 * (1 / 18 : ℝ))
    let v := (392866 : ℝ) ^ (1 / 3 : ℝ)
    let V := (392866 : ℝ) ^ (1 / 2 - 2 * (1 / 18 : ℝ))
    ¬pointExcess 392866 3 z w u V ≤ pointGains 392866 3 z w u v := by
  have h := finite_original_point_residual_one
  dsimp only at h ⊢
  omega

theorem not_universal_original_point_payment :
    ¬(∀ (N : ℕ) (κ₁ κ₂ : ℝ), 4 ≤ N → Even N →
      1 / 18 ≤ κ₁ → κ₁ < κ₂ → 3 * κ₁ + κ₂ < 1 / 2 →
      3 * κ₁ - κ₂ < 1 / 6 → 2 ≤ (N : ℝ) ^ κ₁ →
      ∀ p : ℕ, p ≤ N → p.Prime →
        let z := (N : ℝ) ^ κ₁
        let w := (N : ℝ) ^ κ₂
        let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
        let v := (N : ℝ) ^ (1 / 3 : ℝ)
        let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
        pointExcess N p z w u V ≤ pointGains N p z w u v) := by
  intro h
  obtain ⟨hN, he, hκ₁, hκ, hupper, hparam, hz⟩ := finite_original_parameters
  exact finite_original_point_payment_fails
    (h 392866 (1 / 18) (5 / 19) hN he hκ₁ hκ hupper hparam hz 3
      finite_original_shape.indexBound finite_original_shape.primeIndex)

end Wu18938Campaign.M1

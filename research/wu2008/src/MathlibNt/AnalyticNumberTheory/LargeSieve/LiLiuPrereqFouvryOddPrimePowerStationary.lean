import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerGauss

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem oddPrimePower_annihilator (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (z : ZMod q) :
    (n : ZMod q) * z = 0 ↔ ZMod.castHom h (ZMod m) z = 0 := by
  subst q
  exact zmod_mul_modulus_eq_zero_iff m n z

theorem oddPrimePower_localization (p m : ℕ) [NeZero p] [NeZero m] (a d : ℤ) :
    completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d =
      ∑ u : ZMod (p * (m * m)),
        if IsUnit u ∧ (a : ZMod m) *
          (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
            (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
          (d : ZMod (p * (m * m))) * u⁻¹) else 0 := by
  have ht : ((p * m : ℕ) : ZMod (p * (m * m))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact ⟨p, by ring⟩
  rw [completeKloosterman_square_zero_localization _ _ (p * m : ℕ) _ ht]
  simp only [oddPrimePower_annihilator _ m (p * m) (by ring)
    (show m ∣ p * (m * m) from ⟨p * m, by ring⟩),
    map_sub, map_mul, map_pow, map_intCast, sub_eq_zero]

theorem oddPrimePower_layer_cube_zero (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) : (m : ZMod (p * (m * m))) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨n, hn⟩ := hpm
  exact ⟨n, by rw [hn]; ring⟩

theorem oddPrimePower_stationary_shift (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) :
    (IsUnit (u + (m : ZMod (p * (m * m))) * t) ∧
      (a : ZMod m) *
        (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
          (u + (m : ZMod (p * (m * m))) * t)) ^ 2 = (d : ZMod m)) ↔
    (IsUnit u ∧ (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_isUnit_add_cube_zero _ _ ht]
  simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem oddPrimePower_stationary_linear_coefficient (p m : ℕ) [NeZero p] [NeZero m]
    (a d : ℤ) (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ∃ c : ℕ, (a : ZMod (p * (m * m))) - (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
      (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m))) := by
  let f := ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
  let L : ZMod (p * (m * m)) := (a : ZMod (p * (m * m))) -
    (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2
  have hi : f u * f u⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have hL : f L = 0 := by
    simp only [L, map_sub, map_mul, map_pow, map_intCast]
    change (a : ZMod m) * f u ^ 2 = (d : ZMod m) at hs
    linear_combination (f u⁻¹) ^ 2 * hs - (a : ZMod m) * (f u * f u⁻¹ + 1) * hi
  have hval : m ∣ L.val := by
    apply (ZMod.natCast_eq_zero_iff L.val m).mp
    rw [← map_natCast f, ZMod.natCast_zmod_val]
    exact hL
  obtain ⟨c, hc⟩ := hval
  refine ⟨c, ?_⟩
  change L = _
  rw [← ZMod.natCast_zmod_val L, hc, Nat.cast_mul]

theorem oddPrimePower_stationary_phase (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) (hu : IsUnit u)
    (c : ℕ) (hc : (a : ZMod (p * (m * m))) -
      (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
        (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m)))) :
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
      (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹) =
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar
      (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3) *
        (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) ^ 2 +
      (c : ZMod p) * ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_inv_add_cube_zero u _ hu ht]
  have he :
      (a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) *
          (u⁻¹ - ((m : ZMod (p * (m * m))) * t) * (u⁻¹) ^ 2 +
            ((m : ZMod (p * (m * m))) * t) ^ 2 * (u⁻¹) ^ 3) =
      ((a : ZMod (p * (m * m))) * u + (d : ZMod (p * (m * m))) * u⁻¹) +
        ((m * m : ℕ) : ZMod (p * (m * m))) *
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3 * t ^ 2 +
            (c : ZMod (p * (m * m))) * t) := by
    push_cast
    linear_combination (m : ZMod (p * (m * m))) * t * hc
  rw [he, AddChar.map_add_eq_mul, stdAddChar_mul_modulus_cast]
  simp only [map_add, map_mul, map_pow, map_natCast]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

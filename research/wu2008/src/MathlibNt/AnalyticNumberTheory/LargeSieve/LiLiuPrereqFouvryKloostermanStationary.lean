import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimePower

/-!
# Exact stationary-phase localization at square moduli

This is a finite cancellation identity, not a bound assumed on a remainder.
Translation by a square-zero layer removes every nonstationary residue.
The square-modulus specialization works for all positive moduli, including
powers of two, and leaves only the actual quadratic congruence.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem sum_localize_eigenvalue {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (F c : ι → ℂ) (hc : ∀ x, c (e x) = c x)
    (hF : ∀ x, F (e x) = c x * F x) :
    ∑ x, F x = ∑ x, if c x = 1 then F x else 0 := by
  classical
  let G : ι → ℂ := fun x ↦ if c x = 1 then 0 else F x / (c x - 1)
  have hg (x : ι) : G (e x) - G x = if c x = 1 then 0 else F x := by
    simp only [G, hc, hF]
    by_cases hx : c x = 1
    · simp [hx]
    · simp only [hx, if_false]
      field_simp
  have hz : (∑ x, if c x = 1 then 0 else F x) = 0 := by
    simp_rw [← hg]
    rw [sum_sub_distrib, Equiv.sum_comp, sub_self]
  calc
    _ = (∑ x, if c x = 1 then F x else 0) +
        (∑ x, if c x = 1 then 0 else F x) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by rw [hz, add_zero]

theorem completeKloosterman_square_zero_localization (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) :
    completeKloosterman q a d =
      ∑ u : ZMod q, if IsUnit u ∧ t * (a * u ^ 2 - (d : ZMod q)) = 0 then
        ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  let c : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) else 1
  have hc (u : ZMod q) : c (u + t) = c u := by
    simp only [c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      congr 1
      linear_combination (d : ZMod q) * (2 * (u⁻¹) ^ 3 - t * (u⁻¹) ^ 4) * ht
    · simp [hu]
  have hF (u : ZMod q) : F (u + t) = c u * F u := by
    simp only [F, c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [hu]
  have hchar (u : ZMod q) (hu : IsUnit u) :
      c u = 1 ↔ t * (a * u ^ 2 - (d : ZMod q)) = 0 := by
    simp only [c, hu, if_true]
    have hi := ZMod.mul_inv_of_unit u hu
    have hzero : ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) = 1 ↔
        t * (a - (d : ZMod q) * (u⁻¹) ^ 2) = 0 := by
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
        ZMod.injective_stdAddChar.eq_iff]
    rw [hzero]
    constructor
    · intro hh
      calc
        _ = (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) * u ^ 2 := by
          calc
            _ = t * (a * u ^ 2 - (d : ZMod q) * (u * u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
    · intro hh
      calc
        _ = (t * (a * u ^ 2 - (d : ZMod q))) * (u⁻¹) ^ 2 := by
          calc
            _ = t * (a * (u * u⁻¹) ^ 2 - (d : ZMod q) * (u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
  rw [completeKloosterman_eq]
  change (∑ u, F u) = _
  rw [sum_localize_eigenvalue (Equiv.addRight t) F c hc hF]
  apply sum_congr rfl
  intro u _
  by_cases hu : IsUnit u
  · simp only [hchar u hu, F, hu, if_true, true_and]
  · simp [F, hu]

theorem zmod_mul_modulus_eq_zero_iff (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    (r : ZMod (q * r)) * z = 0 ↔
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z = 0 := by
  have hq (x : ZMod q) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
      ZMod.injective_stdAddChar.eq_iff]
  have hqr (x : ZMod (q * r)) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q * r)),
      ZMod.injective_stdAddChar.eq_iff]
  rw [← hqr, stdAddChar_mul_modulus_cast, hq]

/-- The remaining stationary condition is the actual quadratic congruence
`a u^2 = d (mod m)`. No primality, oddness, or unit-frequency assumption. -/
theorem completeKloosterman_square_modulus_localization (m : ℕ) [NeZero m]
    (a d : ℤ) :
    completeKloosterman (m * m) (a : ZMod (m * m)) d =
      ∑ u : ZMod (m * m),
        if IsUnit u ∧ (a : ZMod m) *
            (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
        else 0 := by
  have ht : (m : ZMod (m * m)) ^ 2 = 0 := by
    rw [pow_two, ← Nat.cast_mul, ZMod.natCast_self]
  rw [completeKloosterman_square_zero_localization _ _ (m : ZMod (m * m)) _ ht]
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero]

theorem completeKloosterman_square_modulus_norm_le (m : ℕ) [NeZero m] (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      ((univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
        (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
          (d : ZMod m)).card : ℝ) := by
  classical
  rw [completeKloosterman_square_modulus_localization]
  convert norm_sum_le univ (fun u : ZMod (m * m) ↦
    if IsUnit u ∧ (a : ZMod m) *
        (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
    then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
    else 0) using 1
  simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

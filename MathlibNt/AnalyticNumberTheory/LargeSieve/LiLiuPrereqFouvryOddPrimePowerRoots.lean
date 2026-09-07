import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimeSquare

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_isUnit_of_reduction_ne_zero (p k : ℕ) [Fact p.Prime]
    (hk : 1 ≤ k) (x : ZMod (p ^ k))
    (hx : ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p) x ≠ 0) :
    IsUnit x := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
  intro hd
  apply hx
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

theorem oddPrimePower_intCast_isUnit (p k : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ k)) := by
  rcases k with _ | k
  · change IsUnit (a : ZMod 1)
    rw [Subsingleton.elim (a : ZMod 1) 1]
    exact isUnit_one
  apply oddPrimePower_isUnit_of_reduction_ne_zero p (k + 1) (by omega)
  intro hz
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp (by
    simpa only [map_intCast] using hz))

theorem oddPrimePower_sq_eq_sq (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (u v : ZMod (p ^ k)) (hu : IsUnit u)
    (he : u ^ 2 = v ^ 2) : u = v ∨ u = -v := by
  let f := ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)
  have hu0 : f u ≠ 0 := (hu.map f).ne_zero
  have hp0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hprod : (u - v) * (u + v) = 0 := by linear_combination he
  by_cases hs : f (u + v) = 0
  · have ht : f (u - v) ≠ 0 := by
      intro ht
      have hh : (2 : ZMod p) * f u = 0 := by
        simp only [map_add] at hs
        simp only [map_sub] at ht
        linear_combination hs + ht
      exact (mul_ne_zero hp0 hu0) hh
    have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u - v) ht
    right
    exact eq_neg_of_add_eq_zero_left ((hv.mul_right_eq_zero).mp hprod)
  · have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u + v) hs
    left
    exact sub_eq_zero.mp ((hv.mul_left_eq_zero).mp hprod)

theorem oddPrimePower_quadratic_root_card_le_two (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ZMod (p ^ k))
    (ha : IsUnit a) (hd : IsUnit d) :
    (univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d).card ≤ 2 := by
  classical
  let s := univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    have hv' : a * v ^ 2 = d := (mem_filter.mp hv).2
    have hsub : s ⊆ {v, -v} := by
      intro u hu
      have hu' := (mem_filter.mp hu).2
      have huunit : IsUnit u := by
        have : IsUnit (a * u ^ 2) := hu'.symm ▸ hd
        exact (isUnit_pow_iff (by omega : 2 ≠ 0)).mp (isUnit_of_mul_isUnit_right this)
      have he : u ^ 2 = v ^ 2 := ha.mul_left_cancel (hu'.trans hv'.symm)
      simpa only [mem_insert, mem_singleton] using
        oddPrimePower_sq_eq_sq p k hp2 hk u v huunit he
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · change s.card ≤ 2
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

theorem completeKloosterman_odd_even_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ r * p ^ r) (a : ZMod (p ^ r * p ^ r)) d‖ ≤
      2 * (p : ℝ) ^ r := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_square_modulus_norm_le_roots (p ^ r) a d).trans ?_
  simpa only [Nat.cast_pow, mul_comm] using
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (p ^ r) : (0 : ℝ) ≤ (p ^ r : ℕ))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

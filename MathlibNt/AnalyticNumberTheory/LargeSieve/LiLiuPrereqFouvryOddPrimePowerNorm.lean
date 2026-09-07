import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerStationary

/-!
Average the localized complete sum over translations by `m`. Each stationary
orbit has a genuine quadratic Gauss norm. This retains the square-root saving
at moduli `p * m²`, rather than estimating the orbit term by term.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_stationary_orbit_norm (p m : ℕ) [Fact p.Prime] [NeZero m]
    (hp2 : p ≠ 2) (hpm : p ∣ m) (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ‖∑ t : ZMod (p * (m * m)),
      ZMod.stdAddChar ((a : ZMod (p * (m * m))) *
        (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹)‖ =
      ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
  obtain ⟨c, hc⟩ := oddPrimePower_stationary_linear_coefficient p m a d u hu hs
  let f := ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
  let A : ZMod p := f ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3)
  have hui : IsUnit u⁻¹ := by
    obtain ⟨v, rfl⟩ := hu
    simpa only [ZMod.inv_coe_unit] using (v⁻¹).isUnit
  have hA : A ≠ 0 := by
    simp only [A, map_mul, map_pow, map_intCast]
    exact mul_ne_zero
      (fun h ↦ hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h))
      (pow_ne_zero _ ((hui.map f).ne_zero))
  simp_rw [oddPrimePower_stationary_phase p m hpm a d u _ hu c hc]
  change ‖∑ t : ZMod (p * (m * m)),
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar (A * f t ^ 2 + (c : ZMod p) * f t)‖ = _
  rw [← mul_sum, oddPrimePower_sum_reduction p (m * m)
    (fun t ↦ ZMod.stdAddChar (A * t ^ 2 + (c : ZMod p) * t))]
  rw [norm_mul, stdAddChar_norm, one_mul, norm_mul, Complex.norm_natCast,
    oddPrimePower_quadratic_gauss_norm p hp2 A (c : ZMod p) hA]

private theorem oddPrimePower_preimage_card (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (s : Finset (ZMod m)) :
    (univ.filter fun u : ZMod q ↦ ZMod.castHom h (ZMod m) u ∈ s).card = s.card * n := by
  subst q
  exact zmod_reduction_preimage_card m n s

theorem completeKloosterman_odd_square_layer_norm_le_roots (p m : ℕ)
    [Fact p.Prime] [NeZero m] (hp2 : p ≠ 2) (hpm : p ∣ m)
    (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d‖ ≤
      (m : ℝ) * Real.sqrt (p : ℝ) *
        ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)).card : ℝ) := by
  classical
  let q := p * (m * m)
  let f := ZMod.castHom (show m ∣ q from ⟨p * m, by dsimp [q]; ring⟩) (ZMod m)
  let S : ZMod q → Prop := fun u ↦ IsUnit u ∧ (a : ZMod m) * f u ^ 2 = (d : ZMod m)
  let F : ZMod q → ℂ := fun u ↦ if S u then
    ZMod.stdAddChar ((a : ZMod q) * u + (d : ZMod q) * u⁻¹) else 0
  let R := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hloc : completeKloosterman q (a : ZMod q) d = ∑ u, F u :=
    oddPrimePower_localization p m a d
  have hS (u t : ZMod q) : S (u + (m : ZMod q) * t) ↔ S u :=
    oddPrimePower_stationary_shift p m hpm a d u t
  have horbit (u : ZMod q) :
      ‖∑ t : ZMod q, F (u + (m : ZMod q) * t)‖ =
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0 := by
    simp only [F, hS]
    by_cases hu : S u
    · simp only [hu, if_true]
      exact oddPrimePower_stationary_orbit_norm p m hp2 hpm a d hd u hu.1 hu.2
    · simp only [hu, if_false, sum_const_zero, norm_zero]
  have havg : (q : ℂ) * completeKloosterman q (a : ZMod q) d =
      ∑ u : ZMod q, ∑ t : ZMod q, F (u + (m : ZMod q) * t) := by
    have ht (t : ZMod q) :
        ∑ u : ZMod q, F (u + (m : ZMod q) * t) =
          completeKloosterman q (a : ZMod q) d :=
      (Equiv.sum_comp (Equiv.addRight ((m : ZMod q) * t)) F).trans hloc.symm
    rw [sum_comm]
    simp only [ht, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
    have hn := norm_sum_le univ (fun u : ZMod q ↦ ∑ t : ZMod q,
      F (u + (m : ZMod q) * t))
    rw [← havg, norm_mul, Complex.norm_natCast] at hn
    simp_rw [horbit] at hn
    have he : (∑ u : ZMod q,
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0) =
        ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
      calc
        _ = (∑ u : ZMod q, if S u then (1 : ℝ) else 0) *
            (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro u _
          split_ifs <;> simp
        _ = _ := by rw [sum_boole]
    exact hn.trans_eq he
  have hcard : (univ.filter S).card ≤ R.card * (p * m) := by
    calc
      _ ≤ (univ.filter fun u : ZMod q ↦ f u ∈ R).card := by
        apply card_le_card
        intro u hu
        simp only [mem_filter, mem_univ, true_and, S, R] at hu ⊢
        exact hu.2
      _ = _ := oddPrimePower_preimage_card q m (p * m) (by dsimp [q]; ring) _ R
  have hbound : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q : ℝ) * ((m : ℝ) * Real.sqrt (p : ℝ) * (R.card : ℝ)) := by
    calc
      _ ≤ ((univ.filter S).card : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := hN
      _ ≤ ((R.card * (p * m) : ℕ) : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by dsimp [q]; push_cast; ring
  exact le_of_mul_le_mul_left hbound (show (0 : ℝ) < q by exact_mod_cast (NeZero.pos q))

theorem completeKloosterman_odd_odd_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (p ^ r * p ^ r)) (a : ZMod (p * (p ^ r * p ^ r))) d‖ ≤
      2 * (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_odd_square_layer_norm_le_roots p (p ^ r) hp2
    (dvd_pow_self p (by omega)) a d hd).trans ?_
  calc
    _ ≤ ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by push_cast; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

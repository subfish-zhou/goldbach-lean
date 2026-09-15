import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanCRT

/-!
# Common-frequency descent

Reduction of units is surjective even when the removed factor is not coprime
to the retained modulus. Its uniform fibers give a totient ratio, not in
general the removed factor. In particular the modulus-one endpoint is retained.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_eq_sum_units (q : ℕ) [NeZero q] (a : ZMod q) (d : ℤ) :
    completeKloosterman q a d =
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q) +
        (d : ZMod q) * (↑u⁻¹ : ZMod q)) := by
  classical
  rw [completeKloosterman_eq]
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro u hu
    have hn : ¬ IsUnit u := by
      rintro ⟨v, rfl⟩
      exact hu ⟨v, rfl⟩
    simp [hn]
  · intro u
    simp [u.isUnit, ZMod.inv_coe_unit]

private theorem sum_comp_surjective_mul_card {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℂ) :
    (Fintype.card H : ℂ) * (∑ x : G, F (f x)) =
      (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have shift (y : H) : ∑ x : G, F (y * f x) = ∑ x : G, F (f x) := by
    obtain ⟨v, rfl⟩ := hf y
    have ht := Equiv.sum_comp (Equiv.mulLeft v) (fun x : G ↦ F (f x))
    change ∑ x : G, F (f (v * x)) = _ at ht
    simpa only [map_mul] using ht
  have shiftR (x : H) : ∑ y : H, F (y * x) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight x) F
  calc
    _ = ∑ y : H, ∑ x : G, F (y * f x) := by simp only [shift, sum_const,
      card_univ, nsmul_eq_mul]
    _ = ∑ x : G, ∑ y : H, F (y * f x) := sum_comm
    _ = _ := by
      simp_rw [shiftR]
      simp

theorem stdAddChar_mul_modulus_cast (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * z) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective z
  simpa only [map_intCast] using stdAddChar_mul_modulus q r z

/-- Exact descent before division; valid also when `q=1` or either frequency vanishes. -/
theorem completeKloosterman_common_factor_mul (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    (q.totient : ℂ) *
        completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      ((q * r).totient : ℂ) * completeKloosterman q (a : ZMod q) d := by
  let h : q ∣ q * r := Nat.dvd_mul_right q r
  let f := ZMod.unitsMap h
  let F : (ZMod q)ˣ → ℂ := fun u ↦
    ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) + (d : ZMod q) * (↑u⁻¹ : ZMod q))
  have phase (u : (ZMod (q * r))ˣ) :
      ZMod.stdAddChar (((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) = F (f u) := by
    rw [show ((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r)) =
        (r : ZMod (q * r)) * ((a : ZMod (q * r)) * (↑u : ZMod (q * r)) +
          (d : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) by push_cast; ring]
    rw [stdAddChar_mul_modulus_cast]
    simp only [map_add, map_mul, map_intCast]
    rfl
  simp_rw [completeKloosterman_eq_sum_units, phase]
  simpa only [ZMod.card_units_eq_totient] using
    sum_comp_surjective_mul_card f (ZMod.unitsMap_surjective h) F

theorem completeKloosterman_common_factor (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      (((q * r).totient : ℂ) / (q.totient : ℂ)) *
        completeKloosterman q (a : ZMod q) d := by
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (mul_left_cancel₀ hq)
  rw [completeKloosterman_common_factor_mul]
  field_simp

/-- For a nontrivial retained prime power, every removed prime-power factor
contributes exactly its size. This includes `p=2` and `t=0`. -/
theorem completeKloosterman_prime_power_common_factor (p k t : ℕ) [Fact p.Prime]
    (a d : ℤ) :
    completeKloosterman (p ^ (k + 1) * p ^ t)
        ((p ^ t * a : ℤ) : ZMod (p ^ (k + 1) * p ^ t)) (p ^ t * d) =
      (p : ℂ) ^ t * completeKloosterman (p ^ (k + 1)) (a : ZMod (p ^ (k + 1))) d := by
  have hφ : (p ^ (k + 1) * p ^ t).totient = p ^ t * (p ^ (k + 1)).totient := by
    rw [← pow_add, show k + 1 + t = (k + t) + 1 by omega,
      Nat.totient_prime_pow_succ Fact.out, Nat.totient_prime_pow_succ Fact.out,
      pow_add]
    ring
  have hq : ((p ^ (k + 1)).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)).ne'
  have hh := completeKloosterman_common_factor (p ^ (k + 1)) (p ^ t) a d
  rw [hφ, Nat.cast_mul, mul_div_cancel_right₀ _ hq, Nat.cast_pow] at hh
  simpa only [Nat.cast_pow] using hh

/-- The fully degenerate endpoint has size `φ(q)`, not `q`. -/
theorem completeKloosterman_zero_zero (q : ℕ) [NeZero q] :
    completeKloosterman q 0 0 = q.totient := by
  rw [completeKloosterman_eq_sum_units]
  simp [ZMod.card_units_eq_totient]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

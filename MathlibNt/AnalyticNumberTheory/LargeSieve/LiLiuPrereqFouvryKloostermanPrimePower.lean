import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanDescent

/-!
# Elementary prime-power cancellation

Translation by the last nonzero prime-power layer preserves units. If just
one frequency is divisible by the prime, it multiplies the complete sum by
a nontrivial constant character, forcing the sum to vanish. The argument
works in characteristic two as well; it uses no quadratic Gauss-sum formula.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_symm (q : ℕ) [NeZero q] (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman q (d : ZMod q) a := by
  simp_rw [completeKloosterman_eq_sum_units]
  apply Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ)
  intro u
  change ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) +
      (d : ZMod q) * (↑u⁻¹ : ZMod q)) =
    ZMod.stdAddChar ((d : ZMod q) * (↑u⁻¹ : ZMod q) +
      (a : ZMod q) * (↑(u⁻¹)⁻¹ : ZMod q))
  rw [inv_inv, add_comm]

private theorem shifted_inverse_product {q : ℕ} (u t : ZMod q) (hu : IsUnit u)
    (ht : t ^ 2 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹) * hi - (u⁻¹) ^ 2 * ht

theorem zmod_isUnit_add_square_zero {q : ℕ} (u t : ZMod q) (ht : t ^ 2 = 0) :
    IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 2 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by simpa using ht)
  · intro hu
    exact step u t hu ht

theorem zmod_inv_add_square_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 2 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 := by
  have hs := shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t) ((zmod_isUnit_add_square_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2)) := by rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

theorem completeKloosterman_vanish_of_square_zero_shift (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) (hdt : (d : ZMod q) * t = 0)
    (hat : ZMod.stdAddChar (a * t) ≠ 1) :
    completeKloosterman q a d = 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  have shift (u : ZMod q) : F (u + t) = ZMod.stdAddChar (a * t) * F u := by
    dsimp only [F]
    simp only [zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      have he : a * (u + t) + (d : ZMod q) * (u⁻¹ - t * (u⁻¹) ^ 2) =
          a * t + (a * u + (d : ZMod q) * u⁻¹) := by
        linear_combination -(u⁻¹) ^ 2 * hdt
      rw [he, AddChar.map_add_eq_mul]
    · simp [hu]
  have hs : ∑ u : ZMod q, F (u + t) = ∑ u : ZMod q, F u :=
    Equiv.sum_comp (Equiv.addRight t) F
  simp_rw [shift, ← mul_sum] at hs
  have hz : (ZMod.stdAddChar (a * t) - 1) * (∑ u : ZMod q, F u) = 0 := by
    linear_combination hs
  rw [completeKloosterman_eq]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hat)

/-- For exponent at least two, unequal frequency valuations give zero after
common-factor descent. No odd-prime hypothesis is used. -/
theorem completeKloosterman_prime_power_vanish (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : ¬ (p : ℤ) ∣ a) (hd : (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  let t : ZMod (p * p ^ (k + 1)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    change ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1))) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨p ^ k, ?_⟩
    rw [pow_succ]
    ring
  have hdt : (d : ZMod (p * p ^ (k + 1))) * t = 0 := by
    obtain ⟨b, rfl⟩ := hd
    change ((p * b : ℤ) : ZMod (p * p ^ (k + 1))) * (p ^ (k + 1) : ℕ) = 0
    push_cast
    have hq : (p : ZMod (p * p ^ (k + 1))) * (p : ZMod (p * p ^ (k + 1))) ^ (k + 1) = 0 := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
    linear_combination (b : ZMod (p * p ^ (k + 1))) * hq
  apply completeKloosterman_vanish_of_square_zero_shift _ _ t d ht hdt
  change ZMod.stdAddChar ((a : ZMod (p * p ^ (k + 1))) *
    ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1)))) ≠ 1
  rw [mul_comm (a : ZMod (p * p ^ (k + 1))), stdAddChar_mul_modulus]
  intro hh
  have hz : (a : ZMod p) = 0 :=
    ZMod.injective_stdAddChar (hh.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)

theorem completeKloosterman_prime_power_vanish_left (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  rw [completeKloosterman_symm]
  exact completeKloosterman_prime_power_vanish p k d a hd ha

/-- At exponent one, a single zero frequency gives `-1`, not zero. -/
theorem completeKloosterman_prime_zero_frequency (p : ℕ) [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    completeKloosterman p a 0 = -1 := by
  classical
  have hs : ∑ u : ZMod p, ZMod.stdAddChar (a * u) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
  rw [completeKloosterman_eq]
  simp only [Int.cast_zero, zero_mul, add_zero]
  calc
    _ = ∑ u : ZMod p, (ZMod.stdAddChar (a * u) - if u = 0 then 1 else 0) := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u = 0 <;> simp [hu, isUnit_iff_ne_zero]
    _ = -1 := by rw [sum_sub_distrib, hs]; simp

theorem completeKloosterman_prime_zero_left (p : ℕ) [Fact p.Prime]
    (d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman p 0 d = -1 := by
  have he := completeKloosterman_symm p 0 d
  simp only [Int.cast_zero] at he
  rw [he]
  exact completeKloosterman_prime_zero_frequency p _ (fun hz ↦
    hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hz))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

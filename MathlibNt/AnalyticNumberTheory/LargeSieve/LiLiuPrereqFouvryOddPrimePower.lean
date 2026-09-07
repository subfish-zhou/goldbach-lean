import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerNorm
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPrimeWeil

/-!
# Primitive Weil bounds for every power of an odd prime

The prime endpoint uses the accepted prime Weil theorem. Higher even exponents
use square-zero localization and unit-root rigidity; higher odd exponents use
the proved quadratic Gauss cancellation. Unequal prime valuations vanish.
All frequencies are arbitrary signed integers.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem oddPrimePower_unit_frequencies_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hrpos : 1 ≤ r := by omega
    subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_add p r r) a d]
    have hs : Real.sqrt (((p ^ r * p ^ r : ℕ) : ℝ)) = (p : ℝ) ^ r := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
    rw [pow_add, hs]
    exact completeKloosterman_odd_even_power_norm_le p r hp2 hrpos a d ha hd
  · have hrpos : 1 ≤ r := by omega
    subst k
    have hq : p ^ (2 * r + 1) = p * (p ^ r * p ^ r) := by
      rw [pow_succ, mul_comm 2 r, pow_mul, pow_two]
      ring
    rw [oddPrimePower_modulus_congr _ _ hq a d]
    have hs : Real.sqrt (((p * (p ^ r * p ^ r) : ℕ) : ℝ)) =
        (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p),
        Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
      ring
    rw [hq, hs]
    simpa only [mul_assoc] using
      completeKloosterman_odd_odd_power_norm_le p r hp2 hrpos a d ha hd

/-- The sharp primitive local estimate at every positive exponent. -/
theorem completeKloosterman_odd_prime_power_primitive_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  by_cases hk1 : k = 1
  · subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_one p) a d]
    simpa only [pow_one] using completeKloosterman_prime_primitive_weil p a d hprimitive
  have hk2 : 2 ≤ k := by omega
  have hq : p ^ k = p * p ^ ((k - 2) + 1) := by
    rw [← pow_succ']
    congr 1
    omega
  by_cases ha : (p : ℤ) ∣ a
  · have hd := hprimitive.resolve_left (not_not.mpr ha)
    rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish_left p (k - 2) a d ha hd, norm_zero]
    positivity
  by_cases hd : (p : ℤ) ∣ d
  · rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish p (k - 2) a d ha hd, norm_zero]
    positivity
  exact oddPrimePower_unit_frequencies_sqrt p k hp2 hk2 a d ha hd

/-- The divisor-factor envelope, including the modulus-one endpoint `k = 0`.
This is the complete Kloosterman sum, not a conditional local-bound interface. -/
theorem completeKloosterman_odd_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases k with _ | k
  · rw [oddPrimePower_modulus_congr _ _ (pow_zero p) a d,
      completeKloosterman_modulus_one, norm_one]
    norm_num
  · refine (completeKloosterman_odd_prime_power_primitive_sqrt p (k + 1) hp2
      (by omega) a d hprimitive).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ k + 1 + 1 by omega))
      (Real.sqrt_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

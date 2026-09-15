import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanDescent
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Removing common prime factors from signed frequencies

The only analytic input is the primitive prime-power estimate. The descent
retains the totient correction at modulus one, so both zero frequencies and
arbitrary signed nonprimitive frequencies are included.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_completeKloosterman_congr_modulus (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

theorem localGlobal_completeKloosterman_one (a d : ℤ) :
    completeKloosterman 1 (a : ZMod 1) d = 1 := by
  rw [completeKloosterman_eq_sum_units]
  have hz (z : ZMod 1) : z = 0 := Subsingleton.elim _ _
  simp [hz]

theorem localGlobal_prime_power_descent_norm (p k : ℕ) [Fact p.Prime] (a d : ℤ) :
    ‖completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
        (p * d)‖ ≤
      (p : ℝ) * ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ := by
  have hp : p.Prime := Fact.out
  have hφ : (p ^ (k + 1)).totient ≤ p * (p ^ k).totient := by
    cases k with
    | zero => simpa using Nat.totient_le p
    | succ k =>
      rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp, pow_succ]
      exact le_of_eq (by ring)
  have hpos : (0 : ℝ) < (p ^ k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have hs : completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
      (p * d) = ((p ^ (k + 1)).totient : ℂ) / ((p ^ k).totient : ℂ) *
        completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d := by
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_succ p k),
      completeKloosterman_common_factor]
    rw [pow_succ]
  rw [hs, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ hpos).mpr
  exact_mod_cast hφ

theorem localGlobal_gcd_scale (p n : ℕ) (a d : ℤ) :
    (p * n).gcd ((p * a : ℤ).natAbs.gcd (p * d : ℤ).natAbs) =
      p * n.gcd (a.natAbs.gcd d.natAbs) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

theorem localGlobal_sqrt_scale (p n g : ℕ) :
    Real.sqrt (p * g : ℕ) * Real.sqrt (p * n : ℕ) =
      (p : ℝ) * Real.sqrt g * Real.sqrt n := by
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  calc
    _ = (Real.sqrt p * Real.sqrt p) * (Real.sqrt g * Real.sqrt n) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg p)]; ring

/-- Exact all-frequency prime-power reduction. The primitive input is explicit,
and is not being asserted as an unconditional analytic theorem here. -/
theorem completeKloosterman_prime_power_weil_of_primitive
    (p : ℕ) [Fact p.Prime]
    (hlocal : ∀ (k : ℕ) (a d : ℤ), (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (k : ℕ) (a d : ℤ) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k).gcd (a.natAbs.gcd d.natAbs)) *
        Real.sqrt (p ^ k : ℕ) := by
  induction k generalizing a d with
  | zero =>
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_zero p),
      localGlobal_completeKloosterman_one]
    simp
  | succ k ih =>
    by_cases hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d
    · apply (hlocal (k + 1) a d hprimitive).trans
      have hg : (1 : ℝ) ≤ Real.sqrt ((p ^ (k + 1)).gcd (a.natAbs.gcd d.natAbs)) :=
        Real.one_le_sqrt.mpr (by
          exact_mod_cast Nat.gcd_pos_of_pos_left (a.natAbs.gcd d.natAbs)
            (pow_pos (Fact.out : p.Prime).pos (k + 1)))
      have hs := mul_le_mul_of_nonneg_left hg
        (show (0 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) by positivity)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (p ^ (k + 1) : ℕ))
    · obtain ⟨a', rfl⟩ := (not_or.mp hprimitive).1 |> not_not.mp
      obtain ⟨d', rfl⟩ := (not_or.mp hprimitive).2 |> not_not.mp
      calc
        _ ≤ (p : ℝ) * ‖completeKloosterman (p ^ k) (a' : ZMod (p ^ k)) d'‖ :=
          localGlobal_prime_power_descent_norm p k a' d'
        _ ≤ (p : ℝ) * (((k + 1 : ℕ) : ℝ) *
            Real.sqrt ((p ^ k).gcd (a'.natAbs.gcd d'.natAbs)) *
            Real.sqrt (p ^ k : ℕ)) :=
          mul_le_mul_of_nonneg_left (ih a' d') (Nat.cast_nonneg p)
        _ = ((k + 1 : ℕ) : ℝ) *
            (Real.sqrt ((p ^ (k + 1)).gcd
              ((p * a' : ℤ).natAbs.gcd (p * d' : ℤ).natAbs)) *
              Real.sqrt (p ^ (k + 1) : ℕ)) := by
          rw [pow_succ', localGlobal_gcd_scale, localGlobal_sqrt_scale]
          ring
        _ ≤ _ := by
          rw [mul_assoc]
          gcongr
          exact_mod_cast Nat.le_succ k

theorem localGlobal_card_divisors_prime_power (p k : ℕ) [Fact p.Prime] :
    (p ^ k).divisors.card = k + 1 := by
  simp [Nat.divisors_prime_pow (Fact.out : p.Prime)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

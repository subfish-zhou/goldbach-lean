import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Clearing a positive denominator in a real-power inequality

Natural powers provide an exact arithmetic form of rational exponent bounds,
including when either base is zero.
-/

namespace MathlibNt

/-- Clear a positive denominator without assuming either base is positive. -/
theorem nat_pow_le_iff_le_rpow (r q m n : ℕ) (hn : 0 < n) :
    r ^ n ≤ q ^ m ↔ (r : ℝ) ≤ (q : ℝ) ^ ((m : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    r ^ n ≤ q ^ m ↔ (r : ℝ) ^ n ≤ (q : ℝ) ^ m := by norm_cast
    _ ↔ (r : ℝ) ≤ ((q : ℝ) ^ m) ^ ((n : ℝ)⁻¹) := by
      simpa only [Real.rpow_natCast] using
        (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg r)
          (pow_nonneg (Nat.cast_nonneg q) m) hnR).symm
    _ ↔ (r : ℝ) ≤ (q : ℝ) ^ ((m : ℝ) / n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), div_eq_mul_inv]

end MathlibNt

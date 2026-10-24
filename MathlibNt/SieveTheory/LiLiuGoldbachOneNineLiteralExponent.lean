import MathlibNt.Analysis.RationalPower
import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-- Exact real-exponent version of the integer-power carrier test, including zero inputs. -/
theorem oneNine_power_iff_source_exponent (r q : ℕ) :
    r^10 ≤ q^9 ↔ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  simpa only [Nat.cast_ofNat, show (9 : ℝ) / 10 = (19 / 10 : ℝ) - 1 by norm_num] using
    MathlibNt.nat_pow_le_iff_le_rpow r q 9 10 (by decide)

/-- The actual D19 carrier is positive exactly when the paper's literal proposition holds. -/
theorem D19_pos_iff_source_oneNine (N : ℕ) :
    0 < D19 N ↔ ∃ p r q : ℕ, p ≤ N ∧ p.Prime ∧
      (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p+r*q ∧
      (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  rw [D19_pos_iff]
  simp_rw [oneNine_power_iff_source_exponent]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine

import MathlibNt.Analysis.RationalPower
import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-- Exact real-exponent version of the integer-power carrier test, including zero inputs. -/
theorem oneNine_power_iff_source_exponent (r q : ℕ) :
    r^10 ≤ q^9 ↔ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  simpa only [Nat.cast_ofNat, show (9 : ℝ) / 10 = (19 / 10 : ℝ) - 1 by norm_num] using
    MathlibNt.nat_pow_le_iff_le_rpow r q 9 10 (by decide)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine

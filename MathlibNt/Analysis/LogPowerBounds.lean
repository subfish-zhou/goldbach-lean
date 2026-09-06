import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter

namespace MathlibNt.Analysis

/-- Along natural numbers, every positive real power eventually dominates
any fixed real power of the logarithm. -/
theorem eventually_nat_log_rpow_le_rpow (b d : ℝ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ b ≤ (N : ℝ) ^ d := by
  have h := (isLittleO_log_rpow_rpow_atTop b hd).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg hpos.le _), one_mul] using hN

end MathlibNt.Analysis
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

theorem eventually_log_mul_rpow_le (K : ℝ) (hK : 0 ≤ K) (B : ℕ)
    {b d : ℝ} (hbd : b < d) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ B * x ^ b ≤ x ^ d := by
  have hb := ((isLittleO_log_rpow_rpow_atTop (B : ℝ)
    (sub_pos.mpr hbd)).const_mul_left (K * 2 ^ B)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hb' : K * 2 ^ B * Real.log x ^ B ≤ x ^ (d - b) := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ K * 2 ^ B * Real.log x ^ B),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hx
  calc
    _ ≤ K * (2 * Real.log x) ^ B * x ^ b := by
      gcongr
      linarith
    _ = (K * 2 ^ B * Real.log x ^ B) * x ^ b := by rw [mul_pow]; ring
    _ ≤ x ^ (d - b) * x ^ b :=
      mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hx0.le _)
    _ = x ^ d := by rw [← Real.rpow_add hx0]; congr 1; ring

end MathlibNt.Analysis

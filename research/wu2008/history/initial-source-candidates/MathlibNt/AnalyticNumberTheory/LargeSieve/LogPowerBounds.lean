import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open Filter

theorem log_pow_le_sqrt_eventually (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  have hR := (Real.isLittleO_pow_log_id_atTop (n := 2 * k)).eventuallyLE
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hR
  filter_upwards [hN, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  apply Real.le_sqrt_of_sq_le
  simp only [id, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hlog
  rw [mul_comm, pow_mul] at hlog
  exact hlog

end AnalyticNumberTheory.LargeSieve
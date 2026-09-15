import AnalyticNumberTheory.Mertens.FinitePart

/-!
# Final reusable Mertens theorems

This module exposes the conventional Euler--Mascheroni form after the
finite-part module identifies the canonical constant.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Real

/-- Mertens' product formula with the exact Euler--Mascheroni constant and
`O(1 / log² n)` error. -/
theorem primeProduct_mertens_isBigO :
    (fun n : ℕ => primeProduct n -
      exp (-Real.eulerMascheroniConstant) / log (n : ℝ)) =O[atTop]
      fun n => 1 / (log (n : ℝ)) ^ 2 :=
  primeProduct_mertens_isBigO_of_constant_eq
    mertensConstant_eq_eulerMascheroni

/-- Uniform natural-number interface for Mertens' product formula. -/
theorem primeProduct_mertens_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeProduct n - exp (-Real.eulerMascheroniConstant) / log (n : ℝ)| ≤
        C / (log (n : ℝ)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    Asymptotics.bound_of_isBigO_nat_atTop primeProduct_mertens_isBigO
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < log (n : ℝ) := log_pos hn1
  have hne : 1 / (log (n : ℝ)) ^ 2 ≠ 0 := by positivity
  simpa [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hlog)),
    div_eq_mul_inv] using hbound hne

end AnalyticNumberTheory.Mertens

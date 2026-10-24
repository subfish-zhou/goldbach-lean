import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Rational budgets for the refinement loss

The bad-factor subtraction uses `8 * log (1 / (a - 1))`. These scalar
certificates cover the source exponent 1.8938 and the requested exponent
1.894 directly. They do not supply the ordinary-count lower bound needed
to pay either loss.
-/

namespace Wu2004MeanValue.RefinementLossBudget

/-- A sufficient coefficient for the source 1.8938 refinement. -/
theorem source_loss_lt : (8 * Real.log (5000/4469) : ℝ) < 4491/5000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (531/9469 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

/-- Directly targeting 1.894 permits the smaller coefficient 0.8964. -/
theorem one894_loss_lt : (8 * Real.log (500/447) : ℝ) < 2241/2500 := by
  have h := Real.log_div_le_sum_range_add
    (x := (53/947 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

end Wu2004MeanValue.RefinementLossBudget

import JointLogTotalComparison

noncomputable section
namespace Wu04BypassBudget
open Real Wu2008DoubleSieve

/-- Sufficient coefficient for the existing bad-factor subtraction route. -/
theorem target_lt_safe : (8 * log (5000/4469) : ℝ) < 4491/5000 := by
  have h := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hu : (8 : ℝ) * JointLogTotalComparison.V (5000/4469) < 4491/5000 := by
    norm_num [JointLogTotalComparison.V, SharpLogRecurrence.upperLog,
      SharpLogRecurrence.lowerLog]
  linarith only [h, hu]

theorem total_budget_iff (B g : ℝ) :
    8 * log (5000/4469) < (B+g)/4 ↔ 32*log (5000/4469)-B < g := by
  constructor <;> intro h <;> linarith only [h]

/-- Arithmetic implication only: the printed classical numerator is not certified here. -/
theorem printed_classical_budget_safe {g : ℝ} (hg : 80141/1000000 ≤ g) :
    8 * log (5000/4469) < (3512659/1000000+g)/4 := by
  exact target_lt_safe.trans_le (by linarith only [hg])

/-- Arithmetic scenario holding all the other printed bonuses fixed. -/
theorem printed_other_terms_budget_safe {g6 : ℝ} (hg : 24749/1000000 ≤ g6) :
    8 * log (5000/4469) < (3568051/1000000+g6)/4 := by
  exact target_lt_safe.trans_le (by linarith only [hg])

end Wu04BypassBudget

#print axioms Wu04BypassBudget.target_lt_safe
#print axioms Wu04BypassBudget.total_budget_iff
#print axioms Wu04BypassBudget.printed_classical_budget_safe
#print axioms Wu04BypassBudget.printed_other_terms_budget_safe

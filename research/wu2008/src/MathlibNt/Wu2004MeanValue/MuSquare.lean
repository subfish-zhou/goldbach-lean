import MathlibNt.Wu2004MeanValue.ActualResidueSup

/-! The manuscript's exact weight domination (1.3), after the full Wu norm
has been retained in the analytic producer. -/

namespace Wu2004MeanValue

open Finset
open scoped BigOperators
noncomputable section

theorem muSquare_sum_le_wu (T : Finset ℕ) (E : ℕ → ℝ)
    (hE : ∀ d ∈ T, 0 ≤ E d) :
    (∑ d ∈ T, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) * E d) ≤
      ∑ d ∈ T, wuModulusWeight d * E d := by
  apply sum_le_sum
  intro d hd
  unfold wuModulusWeight
  apply mul_le_mul_of_nonneg_right _ (hE d hd)
  have hpow : (1 : ℝ) ≤ 3 ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  nlinarith [sq_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]


end
end Wu2004MeanValue

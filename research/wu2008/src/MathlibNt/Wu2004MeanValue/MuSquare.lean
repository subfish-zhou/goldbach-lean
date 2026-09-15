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

theorem muSquare_actualAPResidueSup_le_wu (S : Finset ℕ) (f r : ℕ → ℝ) (Q : ℕ) :
    (∑ d ∈ Icc 1 Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
      actualAPResidueSup S f r d) ≤
      ∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPResidueSup S f r d := by
  apply muSquare_sum_le_wu
  intro d hd
  obtain ⟨b, _, _, heq, _⟩ := actualAPResidueSup_attained S f r d (mem_Icc.mp hd).1
  rw [heq]
  exact abs_nonneg _

end
end Wu2004MeanValue

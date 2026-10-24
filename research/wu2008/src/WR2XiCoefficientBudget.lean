import WR2XiCorrectedMatrix

/-! Rational Gamma5 budgets for entrywise certification of the corrected matrix. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory Wu2008DoubleSieve MotherPair
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

theorem gamma5CellLoss_bounds (r : Fin 4) :
    0 ≤ gamma5CellLoss r ∧ gamma5CellLoss r < rowDebit r/2 := by
  have hp : 0 < (rowParameters r).1 ∧ 1/3 ≤ (rowParameters r).2 ∧
      (rowParameters r).2 < 1/2 ∧
      5/4 ≤ (rowParameters r).1*(1-2*(rowParameters r).2) := by
    fin_cases r <;> norm_num [rowParameters]
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num : (1:ℝ) ≤ 3)
    intro v _
    exact generalKernel_nonneg hp.1 hp.2.1 hp.2.2.1 v
  · have hi := general_weighted_intervalIntegrable hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
      (fun _ => (1:ℝ)) measurable_const (fun _ _ => by norm_num)
    have h := original_row_triangle_budget r (fun _ => (1:ℝ)) (fun _ _ => by norm_num) hi
    simpa only [one_mul, gamma5CellLoss] using h

/-- Only the first column needs an extra budget when certifying the full original kernel. -/
theorem correctedCoefficient_lower_of_full (r : Fin 4) (k : Fin 9) {L : ℝ}
    (h : L + (if k = 0 then rowDebit r/2 else 0) ≤ Xi2Coefficient (gamma5OriginalRow r) k) :
    L ≤ Xi2CorrectedCoefficient r k := by
  by_cases hk : k = 0
  · have hb := (gamma5CellLoss_bounds r).2
    simp only [Xi2CorrectedCoefficient, if_pos hk] at h ⊢
    linarith only [h, hb]
  · simpa only [Xi2CorrectedCoefficient, if_neg hk, add_zero, sub_zero] using h

end WuPaper.R2Xi

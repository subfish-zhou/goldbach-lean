import Wu04RemainingStrongPublication

namespace Wu04RemainingStrongPaid
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open Wu04RemainingCore Wu04RemainingStrongCompleteCost Wu04RemainingStrongPublication
noncomputable section

/-- Full B minus twice C, on each unchanged original row. -/
theorem publication_budget_with_slack (i : Fin 3) :
    5*publication i+slack i≤classicalNumerator (row i)-2*coupledCostMass (row i) := by
  have hb := Wu04RemainingStrongClassical.complete_paid i
  have hc := complete_paid i
  unfold slack
  linarith only [hb,hc]

theorem publication_budget (i : Fin 3) :
    5*publication i≤classicalNumerator (row i)-2*coupledCostMass (row i) := by
  linarith only [publication_budget_with_slack i,slack_pos i]

theorem original_budgets :
    5*((15247971:ℝ)/1000000000)≤classicalNumerator SecondFunctionalParameters.row2-
      2*coupledCostMass SecondFunctionalParameters.row2 ∧
    5*((13898757:ℝ)/1000000000)≤classicalNumerator SecondFunctionalParameters.row3-
      2*coupledCostMass SecondFunctionalParameters.row3 ∧
    5*((11776059:ℝ)/1000000000)≤classicalNumerator SecondFunctionalParameters.row4-
      2*coupledCostMass SecondFunctionalParameters.row4 :=
  ⟨publication_budget 0,publication_budget 1,publication_budget 2⟩

/-- The exact positive-delta denominator is retained, not replaced by its zero-delta value. -/
def deltaDebit (i : Fin 3) (δ : ℝ) : ℝ := 4*δ*costCap i/(5*(1-2*δ))

theorem actual_with_slack (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    publication i+slack i/5-deltaDebit i δ+coupledFeedback (row i) (actualNine δ)≤
      wuImprovementLimit true δ (row i).s := by
  have he : publication i+slack i/5-deltaDebit i δ=
      Wu04RemainingStrongClassical.certificate (row i)/5-2*costCap i/(5*(1-2*δ)) := by
    unfold slack deltaDebit
    have hn : 1-2*δ≠0 := by linarith only [hh]
    field_simp
    ring
  rw [he]
  exact actual_remaining i hd hh

/-- All allowed positive deltas, with their genuine analytic debit. -/
theorem actual_publication (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    publication i-deltaDebit i δ+coupledFeedback (row i) (actualNine δ)≤
      wuImprovementLimit true δ (row i).s := by
  linarith only [actual_with_slack i hd hh,slack_pos i]

/-- A symbolic radius from the proved slack; no new numerical parameter or search. -/
def deltaRadius (i : Fin 3) : ℝ := min (1/10) (slack i/(8*(|costCap i|+slack i)))

theorem deltaRadius_pos (i : Fin 3) : 0<deltaRadius i := by
  apply lt_min (by norm_num)
  exact div_pos (slack_pos i) (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) (slack_pos i)))

theorem deltaDebit_le_slack (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hr : δ≤deltaRadius i) :
    deltaDebit i δ≤slack i/5 := by
  have hh : δ≤1/10 := hr.trans (min_le_left _ _)
  have hs := slack_pos i
  have hab : 0<8*(|costCap i|+slack i) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) hs)
  have hsmall := (le_div_iff₀ hab).mp (hr.trans (min_le_right _ _))
  have hcost := mul_le_mul_of_nonneg_left (le_abs_self (costCap i)) hd.le
  unfold deltaDebit
  apply (div_le_iff₀ (show 0<5*(1-2*δ) by linarith only [hh])).mpr
  nlinarith only [hsmall,hcost,mul_nonneg hd.le hs.le,mul_nonneg hd.le (abs_nonneg (costCap i))]

/-- Genuine publication target without debit for every sufficiently small positive delta. -/
theorem actual_small_delta (i : Fin 3) {δ : ℝ} (hd : 0<δ) (hr : δ≤deltaRadius i) :
    publication i+coupledFeedback (row i) (actualNine δ)≤wuImprovementLimit true δ (row i).s := by
  have hh : δ≤1/10 := hr.trans (min_le_left _ _)
  linarith only [actual_with_slack i hd hh,deltaDebit_le_slack i hd hr]

theorem positive_delta_consumer (i : Fin 3) : ∃ η : ℝ,0<η ∧ η≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤η →
      publication i+coupledFeedback (row i) (actualNine δ)≤wuImprovementLimit true δ (row i).s :=
  ⟨deltaRadius i,deltaRadius_pos i,min_le_left _ _,fun _ hd hr => actual_small_delta i hd hr⟩
end
end Wu04RemainingStrongPaid

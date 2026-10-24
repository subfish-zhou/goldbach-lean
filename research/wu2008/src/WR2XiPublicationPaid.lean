import WR2XiSecondPaid
import Wu04RemainingStrongFourRows

/-! Existing publication budgets consumed by the original Xi2 kernel, with the Gamma5 debit. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Wu2008DoubleSieve MotherPair ActualNineFeedback Wu08OriginalPsiRecovery
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

private theorem baseline_of_radius {B P C cap slack δ : ℝ}
    (hbudget : P + slack/5 ≤ B) (hcost : C ≤ cap) (hs : 0 < slack)
    (hd : 0 < δ) (hr : δ ≤ min (1/10) (slack/(8*(|cap|+slack)))) :
    P ≤ B - deltaLoss δ * (2*C/5) := by
  have hh : δ ≤ 1/10 := hr.trans (min_le_left _ _)
  have hp : 0 < 8*(|cap|+slack) := by positivity
  have hsmall := (le_div_iff₀ hp).mp (hr.trans (min_le_right _ _))
  have hc := mul_le_mul_of_nonneg_left (hcost.trans (le_abs_self cap)) hd.le
  have hdebit : 4*δ*C/(5*(1-2*δ)) ≤ slack/5 := by
    apply (div_le_iff₀ (show 0 < 5*(1-2*δ) by linarith)).mpr
    nlinarith only [hsmall,hc,mul_nonneg hd.le hs.le,mul_nonneg hd.le (abs_nonneg cap)]
  have he : deltaLoss δ * (2*C/5) = 4*δ*C/(5*(1-2*δ)) := by
    simp only [deltaLoss,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  linarith only [hbudget,hdebit]

private theorem first_publication_baseline {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04RemainingStrongFourRows.firstRadius) :
    Wu04CurvePaid.publication ≤ coupledBase SecondFunctionalParameters.row1 -
      deltaLoss δ * coupledLoss SecondFunctionalParameters.row1 := by
  apply baseline_of_radius (cap := Wu04CurveCost.costCap) (slack := Wu04CurvePaid.slack)
    (C := coupledCostMass SecondFunctionalParameters.row1) _
    Wu04CurveCost.complete_cost_paid Wu04CurvePaid.slack_pos hd hr
  have h := Wu04CurvePaid.publication_budget_with_slack
  have he := coupledBase_eq_original_logs (coupledRow_geometry 0)
  change coupledBase SecondFunctionalParameters.row1 =
    (classicalNumerator SecondFunctionalParameters.row1 -
      2*coupledCostMass SecondFunctionalParameters.row1)/5 at he
  rw [he]
  linarith only [h]

private theorem remaining_publication_baseline (i : Fin 3) {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04RemainingStrongPaid.deltaRadius i) :
    Wu04RemainingCore.publication i ≤ coupledBase (Wu04RemainingCore.row i) -
      deltaLoss δ * coupledLoss (Wu04RemainingCore.row i) := by
  apply baseline_of_radius (cap := Wu04RemainingStrongCompleteCost.costCap i)
    (slack := Wu04RemainingStrongPublication.slack i)
    (C := coupledCostMass (Wu04RemainingCore.row i)) _
    (Wu04RemainingStrongCompleteCost.complete_paid i)
    (Wu04RemainingStrongPublication.slack_pos i) hd hr
  have h := Wu04RemainingStrongPaid.publication_budget_with_slack i
  have he := coupledBase_eq_original_logs (coupledRow_geometry i.succ)
  change coupledBase (Wu04RemainingCore.row i) =
    (classicalNumerator (Wu04RemainingCore.row i) -
      2*coupledCostMass (Wu04RemainingCore.row i))/5 at he
  rw [he]
  linarith only [h]

/-- The unchanged original four constants, before the explicit Gamma5 debit. -/
def secondPublication (r : Fin 4) : ℝ :=
  Fin.cases Wu04CurvePaid.publication Wu04RemainingCore.publication r

/-- The explicit Gamma5 losses leave every baseline strictly above one hundredth. -/
theorem secondPublication_paid_gt_one_hundredth (r : Fin 4) :
    (1:ℝ)/100 < secondPublication r - rowDebit r/2 := by
  fin_cases r
  · change (1:ℝ)/100 < 15826357/1000000000 - (1/750)/2
    norm_num
  · change (1:ℝ)/100 < 15247971/1000000000 - (1/500)/2
    norm_num
  · change (1:ℝ)/100 < 13898757/1000000000 - (9/4000)/2
    norm_num
  · change (1:ℝ)/100 < 11776059/1000000000 - (1/1000)/2
    norm_num

/-- One original common radius pays all baseline delta losses. -/
theorem secondPublication_baseline (r : Fin 4) {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04RemainingStrongFourRows.commonRadius) :
    secondPublication r ≤ coupledBase (gamma5OriginalRow r) -
      deltaLoss δ * coupledLoss (gamma5OriginalRow r) := by
  refine Fin.cases ?_ (fun i => ?_) r
  · exact first_publication_baseline hd (hr.trans (min_le_left _ _))
  · exact remaining_publication_baseline i hd
      (hr.trans (Wu04RemainingStrongFourRows.commonRadius_le i))

/-- Published baseline constants with proved losses, for the literal original Xi2 kernel. -/
theorem Xi2_publication_paid (r : Fin 4) {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04RemainingStrongFourRows.commonRadius) :
    secondPublication r - rowDebit r/2 +
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have hh : δ ≤ 1/10 := hr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h := Xi2_four_rows_paid_base r hd hh
  have hb := secondPublication_baseline r hd hr
  linarith only [h,hb]

/-- A uniform positive baseline for all four original kernels on one positive radius. -/
theorem Xi2_four_rows_positive_baseline : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ r : Fin 4,
      (1:ℝ)/100 +
        (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) <
        wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  refine ⟨Wu04RemainingStrongFourRows.commonRadius,
    Wu04RemainingStrongFourRows.commonRadius_pos,
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro δ hd hr r
  have hp := Xi2_publication_paid r hd hr
  have hb := secondPublication_paid_gt_one_hundredth r
  linarith only [hp, hb]

end WuPaper.R2Xi

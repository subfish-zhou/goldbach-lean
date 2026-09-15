import WSrcSingleCoupledHigh

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve ActualNineFeedback Real Finset
open scoped BigOperators

def coupledForcing (δ : ℝ) (j : Fin 3) : ℝ :=
  Wu08OriginalPsiRecovery.classicalNumerator (Wu04RemainingCore.row j) / 5 -
    2 * coupledCostMass (Wu04RemainingCore.row j) / (5 * (1 - 2 * δ))

def psiForcing (δ : ℝ) : Fin 7 → ℝ :=
  Fin.addCases (m := 3) (n := 4) (coupledForcing δ)
    (fun j => firstFunctionalGainPsi δ (firstNode j.castSucc) (firstS j.castSucc))

def psiPublication : Fin 7 → ℝ :=
  Fin.addCases (m := 3) (n := 4) Wu04RemainingCore.publication
    (fun j => Wu04FirstCore.publication j.castSucc)

def sevenRadius : ℝ :=
  min (min (Wu04RemainingStrongPaid.deltaRadius 0)
      (min (Wu04RemainingStrongPaid.deltaRadius 1) (Wu04RemainingStrongPaid.deltaRadius 2)))
    Wu04FirstPaid.commonRadius

def psiSevenSource (δ : ℝ) : ℝ := 8 * ∑ j : Fin 7, psiLogWeight j * psiForcing δ j
def psiSevenPaid : ℝ := 8 * ∑ j : Fin 7, psiLogWeight j * psiPublication j

theorem coupled_forcing_identity {δ : ℝ} (hh : δ ≤ 1 / 10) (j : Fin 3) :
    coupledForcing δ j =
      (Wu08OriginalPsiRecovery.classicalNumerator (Wu04RemainingCore.row j) -
        2 * coupledCostMass (Wu04RemainingCore.row j)) / 5 -
        deltaLoss δ * (2 * coupledCostMass (Wu04RemainingCore.row j) / 5) := by
  unfold coupledForcing deltaLoss
  field_simp [show 1 - 2 * δ ≠ 0 by linarith]
  ring

theorem coupled_forcing_paid {δ : ℝ} (j : Fin 3)
    (hd : 0 < δ) (hr : δ ≤ Wu04RemainingStrongPaid.deltaRadius j) :
    Wu04RemainingCore.publication j ≤ coupledForcing δ j := by
  have hh : δ ≤ 1 / 10 := hr.trans (min_le_left _ _)
  have hloss : 0 ≤ deltaLoss δ := by
    unfold deltaLoss
    exact div_nonneg (by linarith) (by linarith)
  have hcost := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Wu04RemainingStrongCompleteCost.complete_paid j)
        (by norm_num : (0 : ℝ) ≤ 2)) (by norm_num : (0 : ℝ) ≤ 5)) hloss
  have he : deltaLoss δ * (2 * Wu04RemainingStrongCompleteCost.costCap j / 5) =
      Wu04RemainingStrongPaid.deltaDebit j δ := WuTarget.W09.remaining_debit_eq j δ
  rw [he] at hcost
  rw [coupled_forcing_identity hh]
  linarith only [hcost, Wu04RemainingStrongPaid.publication_budget_with_slack j,
    Wu04RemainingStrongPaid.deltaDebit_le_slack j hd hr]

theorem first_forcing_paid {δ : ℝ} (j : Fin 4)
    (hd : 0 < δ) (hr : δ ≤ Wu04FirstPaid.radius j) :
    Wu04FirstCore.publication j.castSucc ≤
      firstFunctionalGainPsi δ (firstNode j.castSucc) (firstS j.castSucc) := by
  have hh : δ ≤ 1 / 10 := hr.trans (min_le_left _ _)
  have hg := first_geometry j.castSucc
  rw [firstFunctionalGainPsi_eq_source_sub_penalty (by linarith : δ < 1 / 2)
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1]
  have hloss : 0 ≤ deltaLoss δ := by
    unfold deltaLoss
    exact div_nonneg (by linarith) (by linarith)
  have hcost := mul_le_mul_of_nonneg_left (Wu04FirstCertificate.cost_paid j.castSucc) hloss
  have hdebit := Wu04FirstPaid.debit_le_slack j hd hr
  have hbudget := Wu04FirstPaid.publication_with_slack j
  unfold deltaLoss at hcost hdebit
  linarith only [hcost, hdebit, hbudget]

theorem seven_radius_pos : 0 < sevenRadius :=
  lt_min (lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 0)
    (lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 1)
      (Wu04RemainingStrongPaid.deltaRadius_pos 2))) Wu04FirstPaid.commonRadius_pos

theorem seven_radius_coupled (j : Fin 3) :
    sevenRadius ≤ Wu04RemainingStrongPaid.deltaRadius j := by
  have h0 := (min_le_left _ _ :
    sevenRadius ≤ min (Wu04RemainingStrongPaid.deltaRadius 0)
      (min (Wu04RemainingStrongPaid.deltaRadius 1) (Wu04RemainingStrongPaid.deltaRadius 2)))
  have h1 := h0.trans (min_le_left _ _)
  have h23 := h0.trans (min_le_right _ _)
  have h2 := h23.trans (min_le_left _ _)
  have h3 := h23.trans (min_le_right _ _)
  fin_cases j
  · exact h1
  · exact h2
  · exact h3

theorem seven_radius_first (j : Fin 4) : sevenRadius ≤ Wu04FirstPaid.radius j :=
  (min_le_right _ _).trans (Wu04FirstPaid.commonRadius_le j)

theorem seven_forcing_paid {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ sevenRadius) (j : Fin 7) :
    psiPublication j ≤ psiForcing δ j := by
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · simpa only [psiPublication, psiForcing, Fin.addCases_left] using
      coupled_forcing_paid i hd (hr.trans (seven_radius_coupled i))
  · simpa only [psiPublication, psiForcing, Fin.addCases_right] using
      first_forcing_paid i hd (hr.trans (seven_radius_first i))

theorem seven_log_weights_nonneg (j : Fin 7) : 0 ≤ psiLogWeight j := by
  unfold psiLogWeight
  apply source_weight_nonneg
  all_goals fin_cases j <;>
    norm_num [psiNode, sourceNode, truncatedSixthLowerAlpha]

theorem seven_publication_positive (j : Fin 7) : 0 < psiPublication j := by
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · simp only [psiPublication, Fin.addCases_left]
    fin_cases i <;> norm_num [Wu04RemainingCore.publication]
  · simp only [psiPublication, Fin.addCases_right]
    fin_cases i <;> norm_num [Wu04FirstCore.publication]

theorem seven_weighted_forcing_paid {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ sevenRadius) :
    psiSevenPaid ≤ psiSevenSource δ := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (seven_forcing_paid hd hr j) (seven_log_weights_nonneg j)

#check @seven_forcing_paid
#check @seven_weighted_forcing_paid
#print axioms coupled_forcing_paid
#print axioms first_forcing_paid
#print axioms seven_weighted_forcing_paid
end WuSource.SrcSingle

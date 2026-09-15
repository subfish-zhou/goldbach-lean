import W09SeedV3

namespace WuTarget.W09
open Wu2008DoubleSieve ActualNineFeedback NodeExtension NineFeedbackStrength
open scoped BigOperators
noncomputable section

def paidCost (i : Fin 9) : ℝ :=
  Fin.addCases (m := 4) (n := 5) (motive := fun _ => ℝ)
    (fun j => Fin.cases (motive := fun _ => ℝ) (2 * Wu04CurveCost.costCap / 5)
      (fun k => 2 * Wu04RemainingStrongCompleteCost.costCap k / 5) j)
    (fun j => Fin.lastCases (motive := fun _ => ℝ) 0
      (fun k => Wu04FirstCertificate.costCap k.castSucc) j) i

theorem forcingSlack_coupled_succ (i : Fin 3) :
    forcingSlack (i.succ.castAdd 5) = Wu04RemainingStrongPublication.slack i / 5 := by
  simp [forcingSlack]

theorem forcingSlack_first (i : Fin 4) :
    forcingSlack (Fin.natAdd 4 i.castSucc) = Wu04FirstPublication.slack i := by
  simp [forcingSlack]

theorem paidCost_coupled_succ (i : Fin 3) :
    paidCost (i.succ.castAdd 5) = 2 * Wu04RemainingStrongCompleteCost.costCap i / 5 := by
  simp [paidCost]

theorem paidCost_first (i : Fin 4) :
    paidCost (Fin.natAdd 4 i.castSucc) = Wu04FirstCertificate.costCap i.castSucc := by
  simp [paidCost]

theorem terminal_cost : paidCost 8 = 0 := rfl

theorem curve_debit_eq (δ : ℝ) :
    deltaLoss δ * (2 * Wu04CurveCost.costCap / 5) = Wu04CurvePaid.deltaDebit δ := by
  unfold deltaLoss Wu04CurvePaid.deltaDebit
  ring

theorem remaining_debit_eq (i : Fin 3) (δ : ℝ) :
    deltaLoss δ * (2 * Wu04RemainingStrongCompleteCost.costCap i / 5) =
      Wu04RemainingStrongPaid.deltaDebit i δ := by
  unfold deltaLoss Wu04RemainingStrongPaid.deltaDebit
  ring

theorem actual_with_loss {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) (i : Fin 9) :
    publication i + forcingSlack i - deltaLoss δ * paidCost i +
      matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i := by
  change publication i + forcingSlack i - deltaLoss δ * paidCost i +
    (∑ k, feedbackMatrix i k * actualNine δ k) ≤ actualNine δ i
  rw [← feedback_expansion]
  refine Fin.addCases (m := 4) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [coupled_feedback_index]
    change _ ≤ wuImprovementLimit true δ (upperNode (j.castAdd 5))
    have hn : (coupledRow j).s = upperNode (j.castAdd 5) := by
      simpa only [upperNode, Fin.val_castAdd] using coupledRow_node j
    rw [← hn]
    refine Fin.cases ?_ (fun k => ?_) j
    · change Wu04CurvePaid.publication + Wu04CurvePaid.slack / 5 -
        deltaLoss δ * (2 * Wu04CurveCost.costCap / 5) +
        coupledFeedback SecondFunctionalParameters.row1 (actualNine δ) ≤ _
      rw [curve_debit_eq]
      exact Wu04CurvePaid.actual_with_slack hd hh
    · rw [publication_coupled_succ, forcingSlack_coupled_succ,
        paidCost_coupled_succ, remaining_debit_eq]
      exact Wu04RemainingStrongPaid.actual_with_slack k hd hh
  · rw [publication_first, first_feedback_index]
    change _ ≤ wuImprovementLimit true δ (upperNode (Fin.natAdd 4 j))
    rw [← first_node_index]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change Wu04FirstCore.publication 4 + 0 - deltaLoss δ * 0 +
        firstFeedback (actualNine δ) (firstNode 4) (firstS 4) ≤ _
      simpa only [add_zero, mul_zero, sub_zero] using Wu04FirstCore.terminal_actual hd hh
    · rw [forcingSlack_first, paidCost_first]
      exact Wu04FirstPaid.actual_with_slack k hd hh

end
end WuTarget.W09

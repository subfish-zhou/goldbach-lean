import WE09JointMainMajorAggregate

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.E09JointMainMajor
open Wu08TerminalAlignment

def payment : ℝ := 7 / 5
def netGain : ℝ := (payment - E09JointMain.payment) / 4

theorem target_lower :
    (7 / 5 : ℝ) ≤ 3 * firstMain - thirdMain - fourthMain :=
  aggregate_target.trans aggregatePayment_le_actual

theorem payment_le_actual :
    payment ≤ 3 * firstMain - thirdMain - fourthMain := target_lower

theorem payment_strict : E09JointMain.payment < payment := by
  rw [E09JointMain.payment_exact]
  norm_num [payment]

theorem netGain_exact :
    netGain = (7 / 5 -
      (83078419629618575238304346189387006860549400910521240176775087 : ℝ) /
        61155381611119450770290424186958629545268860216769067968750000) / 4 := by
  unfold netGain payment
  rw [E09JointMain.payment_exact]

theorem netGain_bounds : (1 / 100 : ℝ) < netGain ∧ netGain < 11 / 1000 := by
  rw [netGain_exact]
  norm_num

theorem netGain_pos : 0 < netGain := lt_trans (by norm_num) netGain_bounds.1

theorem payment_net :
    payment - E09JointMain.payment = 4 * netGain := by
  unfold netGain
  ring

theorem normalized_net :
    payment / 4 - E09JointMain.payment / 4 = netGain := by
  unfold netGain
  ring

theorem no_double_payment : E09JointMain.payment + 4 * netGain = payment := by
  unfold netGain
  ring

theorem complete_remaining_identity :
    3 * firstMain - thirdMain - fourthMain - payment =
      (AnalyticTotalThreshold.sharedLoss -
        (W11.sharedRecovery + E09JointMain.jointGain + middlePayment + highPayment)) +
      (W11.correlatedCredit - logPayment) + (aggregatePayment - payment) := by
  have h := E09JointMain.correlated_remaining_exact
  unfold aggregatePayment
  linarith only [h]

theorem remaining_components_nonneg :
    0 ≤ AnalyticTotalThreshold.sharedLoss -
      (W11.sharedRecovery + E09JointMain.jointGain + middlePayment + highPayment) ∧
    0 ≤ W11.correlatedCredit - logPayment ∧ 0 ≤ aggregatePayment - payment :=
  ⟨sub_nonneg.mpr aggregate_shared_paid, sub_nonneg.mpr logPayment_le_credit,
    sub_nonneg.mpr aggregate_target⟩

def selectedCredit : ℝ :=
  max E09JointMain.selectedCredit payment

theorem selectedCredit_le_actual :
    selectedCredit ≤ 3 * firstMain - thirdMain - fourthMain :=
  max_le E09JointMain.selectedCredit_le_actual payment_le_actual

theorem previous_selected_le : E09JointMain.selectedCredit ≤ selectedCredit := le_max_left _ _

end WuTarget.E09JointMainMajor

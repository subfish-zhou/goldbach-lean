import E09JointMainLow
import W11AcceptedCount

noncomputable section
open Wu2008DoubleSieve

namespace WuTarget.E09JointMain
open Wu08TerminalAlignment

def payment : ℝ := W11Credit.payment + jointGain

def netGain : ℝ := jointGain / 4

theorem payment_exact : payment =
    (83078419629618575238304346189387006860549400910521240176775087 : ℝ) /
      61155381611119450770290424186958629545268860216769067968750000 := by
  unfold payment
  rw [W11Credit.payment_exact, jointGain_exact]
  norm_num

theorem netGain_exact : netGain = (5000 / 15848361 : ℝ) := by
  unfold netGain
  rw [jointGain_exact]
  norm_num

theorem netGain_pos : 0 < netGain := div_pos jointGain_pos (by norm_num)

theorem payment_net : payment - W11Credit.payment = 20000 / 15848361 := by
  unfold payment
  linarith only [jointGain_exact]

theorem payment_strict : W11Credit.payment < payment := by
  unfold payment
  linarith only [jointGain_pos]

theorem payment_le_actual :
    payment ≤ 3 * firstMain - thirdMain - fourthMain := by
  unfold payment
  linarith only [W11Credit.payment_le_credit, correlated_gain_le_actual]

theorem actual_normalized_payment :
    payment / 4 ≤ (3 * firstMain - thirdMain - fourthMain) / 4 :=
  div_le_div_of_nonneg_right payment_le_actual (by norm_num)

theorem correlated_remaining_exact :
    3 * firstMain - thirdMain - fourthMain - (W11.correlatedCredit + jointGain) =
      AnalyticTotalThreshold.sharedLoss - (W11.sharedRecovery + jointGain) := by
  rw [← first_exact]
  unfold W11.correlatedCredit AnalyticTotalThreshold.sharedLoss thirdMain fourthMain
    FixedCoefficientUpperEnclosure.a FixedCoefficientUpperEnclosure.s
  ring

theorem payment_remaining_exact :
    3 * firstMain - thirdMain - fourthMain - payment =
      (AnalyticTotalThreshold.sharedLoss - (W11.sharedRecovery + jointGain)) +
        (W11.correlatedCredit - W11Credit.payment) := by
  rw [← correlated_remaining_exact]
  unfold payment
  ring

/-- Alternative payments of one signed block; the separate branch receives no extra gain. -/
def selectedCredit : ℝ :=
  max (3 * firstMain - W11.pairUpper) (W11.correlatedCredit + jointGain)

theorem selectedCredit_le_actual :
    selectedCredit ≤ 3 * firstMain - thirdMain - fourthMain := by
  apply max_le
  · linarith only [W11.actual_pair_upper]
  · exact correlated_gain_le_actual

theorem previous_selected_le : W11Accepted.selectedCredit ≤ selectedCredit := by
  apply max_le_max le_rfl
  exact le_add_of_nonneg_right jointGain_pos.le

theorem payment_le_selected : payment ≤ selectedCredit := by
  have h : W11.correlatedCredit + jointGain ≤ selectedCredit := le_max_right _ _
  unfold payment
  linarith only [W11Credit.payment_le_credit, h]

theorem first_lower_transport {f : ℝ} (hf : f ≤ firstMain) :
    max (3 * f - W11.pairUpper) (W11.correlatedCredit + jointGain) ≤ selectedCredit := by
  apply max_le_max _ le_rfl
  linarith only [hf]

end WuTarget.E09JointMain

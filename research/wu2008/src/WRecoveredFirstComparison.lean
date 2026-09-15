import W10Root
import WE09JointMainRoot

noncomputable section
namespace WuTarget.RecoveredFirstComparison
open Wu2008DoubleSieve Wu08TerminalAlignment

/-- Separate estimates of the same signed block, not a new independent income. -/
def separateCredit : ℝ := 3*W10.firstLower-W11.pairUpper

theorem separate_le_actual : separateCredit ≤ 3*firstMain-thirdMain-fourthMain := by
  unfold separateCredit
  linarith only [W10.firstMain_lower, W11.actual_pair_upper]

theorem separate_lt_current_payment : separateCredit < E09JointMain.payment := by
  unfold separateCredit W10.firstLower
  rw [W11.pairUpper_exact, E09JointMain.payment_exact]
  norm_num

theorem max_paid_eq_current :
    max separateCredit E09JointMain.payment = E09JointMain.payment :=
  max_eq_right separate_lt_current_payment.le

theorem max_paid_le_actual :
    max separateCredit E09JointMain.payment ≤ 3*firstMain-thirdMain-fourthMain :=
  max_le separate_le_actual E09JointMain.payment_le_actual

end WuTarget.RecoveredFirstComparison

import SigmaJJoint
import F1LowerResidual

namespace RemainingHf
open Real Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison Wu04FactorEnvelopes F1FullRecoveryPayment
noncomputable section

def basicLower (x : ℝ) : ℝ := lowerLog x+lowerGapPayment x+F1LowerResidual.payment x

def basicUpper (x : ℝ) : ℝ := V x-upperGapPayment x

theorem basicLower_le {x : ℝ} (hx : 1 ≤ x) : basicLower x ≤ log x := by
  have h := F1LowerResidual.payment_le hx
  unfold basicLower
  linarith only [h]

theorem le_basicUpper {x : ℝ} (hx : 1 ≤ x) : log x ≤ basicUpper x := by
  have h := upperGapPayment_le hx
  unfold basicUpper
  linarith only [h]

def splitLower (x : ℝ) : ℝ := basicLower (leftFactor x)+basicLower (rightFactor x)
def splitUpper (x : ℝ) : ℝ := basicUpper (leftFactor x)+basicUpper (rightFactor x)

theorem splitLower_le {x : ℝ} (hx : 1 ≤ x) : splitLower x ≤ log x := by
  rw [exact_log hx]
  exact add_le_add (basicLower_le (factors hx).1) (basicLower_le (factors hx).2.1)

theorem le_splitUpper {x : ℝ} (hx : 1 ≤ x) : log x ≤ splitUpper x := by
  rw [exact_log hx]
  exact add_le_add (le_basicUpper (factors hx).1) (le_basicUpper (factors hx).2.1)

end
end RemainingHf

import SigmaSignedCoupledForm
import TerminalEPrimitive

namespace SigmaCorrectionFTC
open Real Set MeasureTheory
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open SigmaSignedCells SigmaExistingLogError F1FullRecoveryPayment
noncomputable section

/-- Exact rational identity for the already existing lower remainder. -/
theorem lowerRemainder_rational {x : ℝ} (hx : 0<x) : lowerRemainder x =
    (6*x/(x^2+8*x+1)-4/7)*(x-1)^5/(6*x*(x+1)^3)+
    (x-1)^7*(5*x+7)/(210*x^2*(x+1)^4*(x^2+8*x+1)) := by
  have he := OriginalFirstErrorRecovery.envelope_gap hx
  unfold lowerRemainder RemainingHf.basicLower enhanced lowerGapPayment
    F1LowerResidual.payment F1LowerResidual.denom
  rw [show lowerLog x+6*x/(x^2+8*x+1)*(upperLog x-lowerLog x)+
      (x-1)^7*(5*x+7)/(210*(x^2*(x+1)^4*(x^2+8*x+1)))-
      (lowerLog x+4/7*(upperLog x-lowerLog x)) =
      (6*x/(x^2+8*x+1)-4/7)*(upperLog x-lowerLog x)+
      (x-1)^7*(5*x+7)/(210*(x^2*(x+1)^4*(x^2+8*x+1))) by ring]
  rw [he]
  ring

def qA (t : ℝ) : ℝ := t^2+28*t+61
def qB (t : ℝ) : ℝ := t^2+18*t+21

theorem qA_pos {t : ℝ} (ht : 0<t) : 0<qA t := by unfold qA; positivity
theorem qB_pos {t : ℝ} (ht : 0<t) : 0<qB t := by unfold qB; positivity

/-- The transformed original beta and lower residual have the same quadratic. -/
theorem original_quadratic_coincidence (t : ℝ) :
    ((t+1)/2)^2+8*((t+1)/2)+1 = qB t/4 := by unfold qB; ring

theorem original_quadratic_A (t : ℝ) :
    ((t+2)/3)^2+8*((t+2)/3)+1 = qA t/9 := by unfold qA; ring

/-- All four forced linear-pole orders, without dropping the fourth order. -/
def poleFour (p a b c d t : ℝ) : ℝ :=
  OriginalSigmaStrength.poleDensity p a b c t+d/(t+p)^4

end
end SigmaCorrectionFTC

import CubicOriginalProfilePayment
import F1LowerGapPayment

namespace OriginalFirstErrorRecovery
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment
open scoped Interval
noncomputable section

/-- Exact algebra for the two inherited envelopes, not an additional Taylor term. -/
theorem envelope_gap {x : ℝ} (hx : 0<x) :
    upperLog x-lowerLog x=(x-1)^5/(6*x*(x+1)^3) := by
  have h1 : x+1≠0 := by positivity
  unfold upperLog lowerLog
  field_simp
  ring

/-- The coefficient is forced by the original terminal argument range [1,2]. -/
theorem terminal_lower_error {x : ℝ} (hx : 1≤x) (hx2 : x≤2) :
    (4/7)*(upperLog x-lowerLog x) ≤ log x-lowerLog x := by
  have hx0 : 0<x := by linarith
  have hq : 0<x^2+8*x+1 := by positivity
  have hc : (4:ℝ)/7≤6*x/(x^2+8*x+1) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx2) (show 0≤2*x-1 by linarith)]
  have hg : 0≤upperLog x-lowerLog x := by
    rw [envelope_gap hx0]
    positivity
  exact (mul_le_mul_of_nonneg_right hc hg).trans (lowerGapPayment_le hx)

/-- The full E recovery on the unchanged terminal interval, using the parent's error comparison. -/
def errorWeight (t : ℝ) : ℝ := (4/7)*(upperLog ((t+1)/2)-lowerLog ((t+1)/2))/t

theorem errorWeight_le {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    lowerLog ((t+1)/2)/t+errorWeight t ≤ log ((t+1)/2)/t := by
  have ht0 : 0<t := by linarith
  have h := terminal_lower_error (x := (t+1)/2) (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_right h ht0.le
  unfold errorWeight
  rw [sub_div] at hdiv
  linarith only [hdiv]

end
end OriginalFirstErrorRecovery

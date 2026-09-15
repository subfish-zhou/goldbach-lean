import SigmaSignedInnerRemainder
namespace SigmaSignedCells
open Real Set MeasureTheory SigmaInnerPaid SigmaExistingLogError
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment
open OriginalSigmaCubicRestoration
open scoped Interval
noncomputable section

def correctionWeight (t : ℝ) : ℝ := innerCorrection t/t

theorem correctionWeight_continuousAt {t : ℝ} (ht : 0<t) :
    ContinuousAt correctionWeight t := by
  have hb : SigmaInnerEndpointRecovery.beta =ᶠ[nhds t]
      fun x : ℝ => 12*(x+1)/(x^2+18*x+21) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact SigmaInnerProfile.beta_rational hx
  have hbc : ContinuousAt SigmaInnerEndpointRecovery.beta t :=
    ContinuousAt.congr_of_eventuallyEq (by fun_prop (disch := positivity)) hb
  unfold correctionWeight innerCorrection lowerRemainder RemainingHf.basicLower
    enhanced lowerGapPayment upperGapPayment F1LowerResidual.payment F1LowerResidual.denom
    SigmaInnerPaid.aCoeff SigmaInnerPaid.bCoeff SigmaInnerPaid.cCoeff cb ca ua ub uc lowerLog upperLog
  fun_prop (disch := positivity)

theorem correctionWeight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn correctionWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  exact (correctionWeight_continuousAt (ha.trans_le ht.1)).continuousWithinAt

/-- Full original cell integral of the as-yet unliquidated rational remainder. -/
def correctionMass (a b : ℝ) : ℝ := ∫ t in a..b, correctionWeight t

theorem correctionMass_nonneg {a b : ℝ} (ha : 1≤a) (hab : a≤b) (hb : b≤3) :
    0 ≤ correctionMass a b := by
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  exact div_nonneg (innerCorrection_nonneg (ha.trans ht.1) (ht.2.trans hb)) (by linarith [ht.1])

theorem correctedCell_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) (hb : b≤3) :
    cellPaid a b+correctionMass a b ≤ SigmaInnerProfile.cellIntegral a b := by
  have he := cellPaid_le ha hab
  have hi : IntervalIntegrable SigmaInnerPaid.weight volume a b :=
    (SigmaInnerPaid.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have hj : IntervalIntegrable correctionWeight volume a b :=
    (correctionWeight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have hm : (∫ t in a..b,SigmaInnerPaid.weight t+correctionWeight t) ≤
      SigmaInnerProfile.cellIntegral a b := by
    apply intervalIntegral.integral_mono_on hab (hi.add hj)
      (SigmaInnerProfile.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
    intro t ht
    have h := div_le_div_of_nonneg_right
      (innerCorrection_le_gap (ha.trans ht.1) (ht.2.trans hb)) (by linarith [ht.1] : 0≤t)
    simpa only [add_div,SigmaInnerPaid.weight,correctionWeight,SigmaInnerProfile.weight] using h
  rw [intervalIntegral.integral_add hi hj,SigmaInnerPaid.weight_integral ha hab] at hm
  change cellPaid a b ≤ SigmaInnerPaid.primitive b-SigmaInnerPaid.primitive a at he
  change _+correctionMass a b ≤ _ at hm
  linarith only [he,hm]

end
end SigmaSignedCells

import SigmaSignedProfile
namespace SigmaSignedCells
open Real Set MeasureTheory SigmaInnerPaid SigmaExistingLogError
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment
open scoped Interval
noncomputable section

/-- The already proved variable lower-envelope correction beyond the old 4/7. -/
def lowerRemainder (x : ℝ) : ℝ := RemainingHf.basicLower x-enhanced x

theorem lowerRemainder_nonneg {x : ℝ} (hx : 1≤x) (hx2 : x≤2) :
    0≤lowerRemainder x := by
  have hc := SigmaJEndpoint.coefficient_antitone hx hx2
  norm_num [SigmaJEndpoint.coefficient] at hc
  have hg : 0≤upperLog x-lowerLog x := by
    rw [OriginalFirstErrorRecovery.envelope_gap (by linarith : 0<x)]
    positivity
  have hr : 0≤F1LowerResidual.payment x := by
    unfold F1LowerResidual.payment F1LowerResidual.denom
    positivity
  have hm := mul_le_mul_of_nonneg_right hc hg
  unfold lowerRemainder RemainingHf.basicLower enhanced lowerGapPayment
  linarith only [hm,hr]

/-- Actual remaining rational density, not a new approximation order or a new cut. -/
def innerCorrection (t : ℝ) : ℝ :=
  SigmaInnerPaid.aCoeff t*lowerRemainder ((t+2)/3)+
  SigmaInnerPaid.bCoeff t*lowerRemainder ((t+1)/2)-
  SigmaInnerPaid.cCoeff t*upperGapPayment ((2*t+2)/(t+3))

theorem innerCorrection_nonneg {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    0 ≤ innerCorrection t := by
  have ha := lowerRemainder_nonneg (x := (t+2)/3) (by linarith) (by linarith)
  have hb := lowerRemainder_nonneg (x := (t+1)/2) (by linarith) (by linarith)
  have hx : 1≤(2*t+2)/(t+3) := (one_le_div (by linarith : 0<t+3)).mpr (by linarith)
  have hc : 0≤upperGapPayment ((2*t+2)/(t+3)) := by
    unfold upperGapPayment
    positivity
  have h1 := mul_nonneg (SigmaInnerPaid.aCoeff_nonneg ht ht3) ha
  have h2 := mul_nonneg (SigmaInnerPaid.bCoeff_nonneg ht) hb
  have h3 := mul_nonpos_of_nonpos_of_nonneg (SigmaInnerPaid.cCoeff_nonpos ht) hc
  unfold innerCorrection
  linarith only [h1,h2,h3]

theorem innerCorrection_le_gap {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    SigmaInnerPaid.endpointPaid t+innerCorrection t ≤ SigmaInnerEndpointRecovery.kernel t := by
  have ha := mul_le_mul_of_nonneg_left
    (RemainingHf.basicLower_le (x := (t+2)/3) (by linarith))
    (SigmaInnerPaid.aCoeff_nonneg ht ht3)
  have hb := mul_le_mul_of_nonneg_left
    (RemainingHf.basicLower_le (x := (t+1)/2) (by linarith))
    (SigmaInnerPaid.bCoeff_nonneg ht)
  have hc := mul_le_mul_of_nonpos_left
    (RemainingHf.le_basicUpper ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3≤2*t+2)))
    (SigmaInnerPaid.cCoeff_nonpos ht)
  rw [SigmaInnerPaid.kernel_collected]
  unfold RemainingHf.basicUpper at hc
  unfold SigmaInnerPaid.endpointPaid innerCorrection lowerRemainder
  linarith only [ha,hb,hc]

end
end SigmaSignedCells

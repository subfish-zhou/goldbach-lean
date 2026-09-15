import SigmaExistingInner

namespace SigmaExistingLogError
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval
noncomputable section

/-- Collect coefficients before applying endpoint inequalities. -/
def aCoeff (t : ℝ) : ℝ := (3/7)*(2*(t+2)/t+(2/3)*ca t)+(4/7)*ua t
def bCoeff (t : ℝ) : ℝ := (4/7)*ub t
def cCoeff (t : ℝ) : ℝ := (3/7)*(-4*(t+1)/t+(2/3)*cb t)+(4/7)*uc t
def rationalPart (t : ℝ) : ℝ :=
  (2/7)*(-cc t*(1/(2*t+2)-1/(t+3))-cd t/2*(1/(2*t+2)^2-1/(t+3)^2))-
  (4/7)*(t-1)/(6*(t+1))

theorem innerKernel_collected (t : ℝ) : innerKernel t=
    aCoeff t*log ((t+2)/3)+bCoeff t*log ((t+1)/2)+
    cCoeff t*log ((2*t+2)/(t+3))+rationalPart t := by
  unfold innerKernel retainedKernel cubicKernel upperKernel aCoeff bCoeff cCoeff rationalPart
  ring

theorem aCoeff_nonneg {t : ℝ} (ht : 1≤t) (ht3 : t≤3) : 0≤aCoeff t := by
  have ht0 : 0<t := by linarith
  have hq : t^2-8*t-8≤0 := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht3)]
  have hu : 0≤ua t := by
    unfold ua
    apply div_nonneg _ (by positivity)
    nlinarith
  unfold aCoeff ca
  positivity

theorem bCoeff_nonneg {t : ℝ} (ht : 1≤t) : 0≤bCoeff t := by
  unfold bCoeff ub
  positivity

theorem cCoeff_nonpos {t : ℝ} (ht : 1≤t) : cCoeff t≤0 := by
  have ht0 : 0<t := by linarith
  have ha : 0≤ca t := by unfold ca; positivity
  have hb : cb t≤0 := by unfold cb; linarith only [ha]
  have hc : uc t≤0 := by
    unfold uc
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  have hn : -4*(t+1)/t≤0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  unfold cCoeff
  linarith only [hb,hc,hn]

/-- Inner recovery and endpoint recovery pay different errors of the same integral. -/
def endpointPaid (t : ℝ) : ℝ :=
  aCoeff t*enhanced ((t+2)/3)+bCoeff t*enhanced ((t+1)/2)+
    cCoeff t*V ((2*t+2)/(t+3))+rationalPart t

theorem endpointPaid_le_inner {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    endpointPaid t ≤ innerKernel t := by
  have h1 := mul_le_mul_of_nonneg_left
    (enhanced_le (x := (t+2)/3) (by linarith) (by linarith)) (aCoeff_nonneg ht ht3)
  have h2 := mul_le_mul_of_nonneg_left
    (enhanced_le (x := (t+1)/2) (by linarith) (by linarith)) (bCoeff_nonneg ht)
  have h3 := mul_le_mul_of_nonpos_left
    (log_le_V ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3≤2*t+2)))
    (cCoeff_nonpos ht)
  rw [innerKernel_collected]
  unfold endpointPaid
  linarith only [h1,h2,h3]

theorem endpointPaid_le_sigma {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    endpointPaid t ≤ sigma 3 (t+2) (t+1) :=
  (endpointPaid_le_inner ht ht3).trans (innerKernel_le_sigma ht ht3)

end
end SigmaExistingLogError

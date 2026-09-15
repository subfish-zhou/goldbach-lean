import SigmaInnerProfileBase

namespace SigmaInnerPaid
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison SigmaExistingLogError
open SigmaInnerEndpointRecovery
noncomputable section

theorem beta_nonneg {t : ℝ} (ht : 1≤t) : 0≤beta t := by
  rw [SigmaInnerProfile.beta_rational (by linarith : 0<t)]
  positivity

theorem beta_le_one {t : ℝ} (ht : 1≤t) : beta t≤1 := by
  rw [SigmaInnerProfile.beta_rational (by linarith : 0<t)]
  apply (div_le_one (by positivity : 0<t^2+18*t+21)).mpr
  nlinarith only [sq_nonneg (t+3)]

/-- Coefficients of the parent's parameter-dependent kernel, before endpoint payment. -/
def aCoeff (t : ℝ) : ℝ :=
  (1-beta t)*(2*(t+2)/t+(2/3)*ca t)+beta t*ua t
def bCoeff (t : ℝ) : ℝ := beta t*ub t
def cCoeff (t : ℝ) : ℝ :=
  (1-beta t)*(-4*(t+1)/t+(2/3)*cb t)+beta t*uc t
def rationalPart (t : ℝ) : ℝ :=
  (1-beta t)*(2/3)*(-cc t*(1/(2*t+2)-1/(t+3))-
    cd t/2*(1/(2*t+2)^2-1/(t+3)^2))-beta t*(t-1)/(6*(t+1))

theorem kernel_collected (t : ℝ) : kernel t =
    aCoeff t*log ((t+2)/3)+bCoeff t*log ((t+1)/2)+
      cCoeff t*log ((2*t+2)/(t+3))+rationalPart t := by
  unfold kernel retainedKernel cubicKernel upperKernel aCoeff bCoeff cCoeff rationalPart
  ring

theorem aCoeff_nonneg {t : ℝ} (ht : 1≤t) (ht3 : t≤3) : 0≤aCoeff t := by
  have ht0 : 0<t := by linarith
  have hq : t^2-8*t-8≤0 := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht3)]
  have hu : 0≤ua t := by
    unfold ua
    apply div_nonneg _ (by positivity)
    nlinarith
  have hb := beta_nonneg ht
  have hc := sub_nonneg.mpr (beta_le_one ht)
  unfold aCoeff ca
  positivity

theorem bCoeff_nonneg {t : ℝ} (ht : 1≤t) : 0≤bCoeff t := by
  have hb := beta_nonneg ht
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
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (beta_le_one ht))
    (by linarith only [hb,hn])) (mul_nonpos_of_nonneg_of_nonpos (beta_nonneg ht) hc)

/-- Only inherited enhanced/V envelopes at the three original arguments. -/
def endpointPaid (t : ℝ) : ℝ :=
  aCoeff t*enhanced ((t+2)/3)+bCoeff t*enhanced ((t+1)/2)+
    cCoeff t*V ((2*t+2)/(t+3))+rationalPart t

theorem endpointPaid_le_kernel {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    endpointPaid t ≤ kernel t := by
  have ha := mul_le_mul_of_nonneg_left
    (enhanced_le (x := (t+2)/3) (by linarith) (by linarith)) (aCoeff_nonneg ht ht3)
  have hb := mul_le_mul_of_nonneg_left
    (enhanced_le (x := (t+1)/2) (by linarith) (by linarith)) (bCoeff_nonneg ht)
  have hc := mul_le_mul_of_nonpos_left
    (log_le_V ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3≤2*t+2)))
    (cCoeff_nonpos ht)
  rw [kernel_collected]
  unfold endpointPaid
  linarith only [ha,hb,hc]

theorem endpointPaid_le_sigma {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    endpointPaid t ≤ sigma 3 (t+2) (t+1) :=
  (endpointPaid_le_kernel ht ht3).trans (kernel_le_sigma ht)

end
end SigmaInnerPaid

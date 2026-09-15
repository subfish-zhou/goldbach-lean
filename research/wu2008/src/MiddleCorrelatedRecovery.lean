import GammaFullActual

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison
open FixedCoefficientUpperEnclosure (a)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
open MiddleInitialEnvelope MiddleInitialFTC
namespace MiddleCorrelatedRecovery

/-- Retained error in the original initial primitive, without changing its order. -/
def delta : ℝ := log (3/2)-lowerLog (3/2)
def deltaLower : ℝ := lowerLog (5/4)+lowerLog (6/5)-lowerLog (3/2)

theorem delta_lower : deltaLower ≤ delta := by
  have he := log_mul (by norm_num : (5/4:ℝ) ≠ 0) (by norm_num : (6/5:ℝ) ≠ 0)
  norm_num at he
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 5/4)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 6/5)
  unfold delta deltaLower
  linarith only [he,h1,h2]

theorem deltaLower_pos : 0 < deltaLower := by norm_num [deltaLower,lowerLog]

/-- Opposite coefficients are combined before the existing L/V payment. -/
def correlatedPayment : ℝ :=
  54184986258433847/7671098066888025+
  (299524880/916839)*lowerLog (15/14)-
  (1766372040448/5150827583-299524880/916839)*V (7/6)-
  (8547286566790892748321251/2986096125885620562045000)*V (527/327)-
  (1151264258336/12882918447)*V (4/3)

theorem correlated_payment : correlatedPayment ≤ gainReal := by
  rw [MiddleInitialPayment.collected]
  have he := log_mul (by norm_num : (7/6:ℝ) ≠ 0) (by norm_num : (15/14:ℝ) ≠ 0)
  norm_num at he
  have h0 := log_lower (by norm_num : (1:ℝ) ≤ 15/14)
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ 7/6)
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  unfold correlatedPayment MiddleInitialPayment.paid
  linarith only [he,h0,h1,h2,h3]

/-- The complete original middle window, with the original weight. -/
def mass : ℝ := ∫ t in (c 5)..(c 4), SharedRationalEnvelope.weight t
def massLower : ℝ := 16*lowerLog (527/327)-8*V (5/4)

theorem mass_ftc : mass = 16*log (527/327)-8*log (5/4) := by
  have hf := ExactWeightTripleEnclosure.full_ftc 1 0 0 0 (c 5) (c 4)
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
  norm_num [ExactWeightTripleEnclosure.poly,ExactWeightTripleEnclosure.payment,
    ExactWeightTripleEnclosure.algebraic,c,a,truncatedSixthLowerAlpha] at hf
  norm_num [mass,c,a,truncatedSixthLowerAlpha]
  exact hf

theorem mass_lower : massLower ≤ mass := by
  rw [mass_ftc]
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 527/327)
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  unfold massLower
  linarith only [h1,h2]

theorem massLower_pos : 0 < massLower := by norm_num [massLower,lowerLog,V,upperLog]

theorem weight_integrable : IntervalIntegrable SharedRationalEnvelope.weight volume (c 5) (c 4) := by
  have hi := JointSharedTightEnclosure.weighted_integrable (fun _ => (1:ℝ))
    (by fun_prop) (show a ≤ c 5 by norm_num [a,c,truncatedSixthLowerAlpha])
    SharedRationalEnvelope.window_order.2.1
    (show c 5 ≤ c 4 by norm_num [a,c,truncatedSixthLowerAlpha])
  simpa using hi

theorem middle_pointwise {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    GConvexChord.C+GConvexChord.m*v-wuUpperCoefficient v ≤
      JointSharedTightEnclosure.middleHi v-gainDensity v-(8/3)*delta := by
  have h := original_domain_lower hv
  rw [rational_form hv.1] at h
  unfold JointSharedTightEnclosure.middleHi gainDensity oldLower delta GConvexChord.C GConvexChord.m
  linarith only [h]

/-- Integrate the signed density and the retained constant separately on the full original domain. -/
theorem middle_upper : BaseGSharedActualRecovery.middleKernel ≤
    ExactWeightTripleEnclosure.middleUpper-gainReal-(8/3)*delta*mass := by
  have hl : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hr := SharedRationalEnvelope.window_order.2.1
  have ho : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hk := BaseGSharedActualRecovery.kernel_integrable
    (fun v => GConvexChord.C+GConvexChord.m*v) hl hr ho (by fun_prop)
  have hi := JointSharedTightEnclosure.weighted_integrable JointSharedTightEnclosure.middleHi
    (by unfold JointSharedTightEnclosure.middleHi; fun_prop) hl hr ho
  have hc := weight_integrable.mul_const ((8/3)*delta)
  have hm := intervalIntegral.integral_mono_on ho hk ((hi.sub gain_integrable).sub hc) (fun t ht => by
    rw [HighSharedKernelMagnitude.kernel_density (fun v => GConvexChord.C+GConvexChord.m*v)]
    have hp := mul_le_mul_of_nonneg_left
      (middle_pointwise (JointSharedTightEnclosure.middle_geometry ht).2.2)
      (HighSharedKernelMagnitude.middle_weight ht).1
    simpa only [mul_sub] using hp)
  rw [intervalIntegral.integral_sub (hi.sub gain_integrable) hc,
    intervalIntegral.integral_sub hi gain_integrable,full_signed_ftc,
    intervalIntegral.integral_mul_const] at hm
  change BaseGSharedActualRecovery.middleKernel ≤
    JointSharedTightEnclosure.weighted JointSharedTightEnclosure.middleHi (c 5) (c 4)-gainReal-
      mass*((8/3)*delta) at hm
  rw [old_middle_integral] at hm
  nlinarith only [hm]

/-- The additional recovery relative to the already paid middle upper; divide by four once. -/
def extra : ℝ := (correlatedPayment-MiddleInitialPayment.gain+(8/3)*deltaLower*massLower)/4

theorem extra_exact : extra = 1801966742673539714200045699/1742820315223381016383826690625 := by
  rw [extra,MiddleInitialPayment.gain_exact]
  norm_num [correlatedPayment,deltaLower,massLower,lowerLog,V,upperLog]

theorem extra_pos : 0 < extra := by rw [extra_exact]; norm_num

theorem total_gain_lower : MiddleInitialPayment.gain+4*extra ≤ gainReal+(8/3)*delta*mass := by
  have hp := mul_le_mul delta_lower mass_lower massLower_pos.le (deltaLower_pos.le.trans delta_lower)
  have hg := correlated_payment
  unfold extra
  nlinarith only [hp,hg]

end MiddleCorrelatedRecovery

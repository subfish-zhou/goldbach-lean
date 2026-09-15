import F1JointIntegral

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1FixedSquareRecovery F1SecondLogRecovery
open scoped Interval
namespace F1JointFTC

/-- Replace the entire old first-kernel payment by its exact integral. -/
def cPayment : ℝ := (1+secondFactorRatio)*exactMass+secondPayment

theorem exactMass_covers_old : momentPayment+unpaidFactorPayment+combinedSquarePayment ≤
    (1+secondFactorRatio)*exactMass := by
  have hc := kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ) ≤ 927/200)
  have hp := oldPaidKernel_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hh (u : ℝ) (hu : u ∈ Icc 2 (927/200)) :
      oldPaidKernel u ≤ (1+secondFactorRatio)*kernel u := by
    exact mul_le_mul_of_nonneg_left (fixed_square_lower hu)
      (by linarith only [secondFactorRatio_pos])
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    hp (hc.const_mul (1+secondFactorRatio)) hh
  rw [oldPaidKernel_integral,intervalIntegral.integral_const_mul,kernel_integral] at h
  exact h

/-- The exact first integral and the paid second error share the same actual kernel. -/
theorem cPayment_le_actual : cPayment ≤ FirstActualRecovery.kernelRecovery := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hk := kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (2:ℝ) ≤ 927/200)
  have hp1 := polynomialOne_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hp2 := polynomialTwo_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hi := ((hk.const_mul (1+secondFactorRatio)).add hp1).add hp2
  have hh (u : ℝ) (hu : u ∈ Icc 2 (927/200)) :
      (1+secondFactorRatio)*kernel u+polynomialOne u+polynomialTwo u ≤
        cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
    have ha := augmented_retained hu
    have hb := polynomial_second_lower hu
    change (1+secondFactorRatio)*(2*momentWeight u/momentDenom u)+
      polynomialOne u+polynomialTwo u ≤ _
    linarith only [ha,hb]
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    hi (h1.sub h2) hh
  rw [intervalIntegral.integral_add ((hk.const_mul (1+secondFactorRatio)).add hp1) hp2,
    intervalIntegral.integral_add (hk.const_mul (1+secondFactorRatio)) hp1,
    intervalIntegral.integral_const_mul,kernel_integral,polynomialOne_integral,
    polynomialTwo_integral,intervalIntegral.integral_sub h1 h2] at h
  have he : FirstActualRecovery.kernelRecovery =
      (∫ u in (2:ℝ)..(927/200), cExactKernel (1327/200) u)-
        (∫ u in (2:ℝ)..(927/200), cLowerKernel (1327/200) u) := by
    unfold FirstActualRecovery.kernelRecovery
    rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
    norm_num [cLowerMass,cExactKernel]
  rw [← he] at h
  unfold cPayment secondPayment
  linarith only [h]

end F1JointFTC

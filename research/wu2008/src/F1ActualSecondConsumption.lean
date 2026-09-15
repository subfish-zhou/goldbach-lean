import F1ActualSecondIntegral

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1SecondLogRecovery
open scoped Interval
namespace F1ActualSecondFTC

theorem factor_identity (u : ℝ) :
    ((u-2)^5/((3*u-2)^3*(21*u^2-24*u+4)))/u *
      (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)) = kernel u := by
  unfold kernel momentWeight
  rw [show (1327:ℝ)/200+u=u+1327/200 by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem first_identity (u : ℝ) :
    ((u-2)^5/((u+2)^3*(u^2+16*u+4)))/u *
      (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)) = F1JointFTC.kernel u := by
  unfold F1JointFTC.kernel momentWeight momentDenom
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem kernel_covers_ratio {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    secondFactorRatio*F1JointFTC.kernel u ≤ kernel u := by
  have hw : 0 ≤ 2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u) :=
    div_nonneg (by linarith [hu.2]) (by linarith [hu.1])
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (second_factor_comparison hu) (show 0 ≤ u by linarith [hu.1])) hw
  rw [factor_identity,show secondFactorRatio*((u-2)^5/((u+2)^3*(u^2+16*u+4)))/u *
    (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)) =
      secondFactorRatio*(((u-2)^5/((u+2)^3*(u^2+16*u+4)))/u *
        (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u))) by ring,first_identity] at h
  exact h

theorem exactMass_covers_ratio : secondFactorRatio*F1JointFTC.exactMass ≤ exactMass := by
  have h1 := F1JointFTC.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have h2 := kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (h1.const_mul secondFactorRatio) h2 (fun _ hu => kernel_covers_ratio hu)
  rw [intervalIntegral.integral_const_mul,F1JointFTC.kernel_integral,kernel_integral] at h
  exact h

/-- Keep both actual split-factor errors in A and the original disjoint B residual. -/
theorem retained {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    F1JointFTC.kernel u+kernel u+secondExact u ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have herr : 0 ≤ (log (u-1)-splitL (u-1))/u :=
    div_nonneg (sub_nonneg.mpr (splitL_le_log (by linarith [hu.1]))) hu0.le
  have hlin : 0 ≤ 2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u) :=
    div_nonneg (by linarith [hu.2]) (by linarith [hu.1])
  have h := mul_le_mul (div_le_div_of_nonneg_right (both_split_errors hu.1) hu0.le)
    (ratio_log_payment hu') hlin herr
  rw [add_div,add_mul,first_identity,factor_identity] at h
  have heq : cExactKernel (1327/200) u-cLowerKernel (1327/200) u =
      (log (u-1)-splitL (u-1))/u*log (((1327:ℝ)/200-1)/(u+1))+secondExact u := by
    unfold cExactKernel cLowerKernel secondExact
    ring
  rw [heq]
  linarith only [h]

/-- This replaces the endpoint-compressed second factor, not an additional copy. -/
def cPayment : ℝ := F1JointFTC.exactMass+exactMass+secondPayment

theorem cPayment_ge_previous : F1JointFTC.cPayment ≤ cPayment := by
  unfold cPayment F1JointFTC.cPayment
  linarith only [exactMass_covers_ratio]

theorem cPayment_le_actual : cPayment ≤ FirstActualRecovery.kernelRecovery := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hk1 := F1JointFTC.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hk2 := kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hp1 := polynomialOne_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hp2 := polynomialTwo_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hh (u : ℝ) (hu : u ∈ Icc 2 (927/200)) :
      F1JointFTC.kernel u+kernel u+polynomialOne u+polynomialTwo u ≤
        cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
    linarith only [retained hu,polynomial_second_lower hu]
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (((hk1.add hk2).add hp1).add hp2) (h1.sub h2) hh
  rw [intervalIntegral.integral_add ((hk1.add hk2).add hp1) hp2,
    intervalIntegral.integral_add (hk1.add hk2) hp1,intervalIntegral.integral_add hk1 hk2,
    F1JointFTC.kernel_integral,kernel_integral,polynomialOne_integral,polynomialTwo_integral,
    intervalIntegral.integral_sub h1 h2] at h
  have he : FirstActualRecovery.kernelRecovery =
      (∫ u in (2:ℝ)..(927/200), cExactKernel (1327/200) u)-
        (∫ u in (2:ℝ)..(927/200), cLowerKernel (1327/200) u) := by
    unfold FirstActualRecovery.kernelRecovery
    rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
    norm_num [cLowerMass,cExactKernel]
  rw [← he] at h
  unfold cPayment secondPayment
  linarith only [h]

end F1ActualSecondFTC

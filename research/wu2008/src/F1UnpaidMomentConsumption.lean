import F1UnpaidSplitFactor

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery
open scoped Interval
namespace F1UnpaidRecovery

/-- The unpaid second-factor error is added inside the literal kernel, before integration. -/
theorem augmented_kernel {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*(2*momentWeight u/momentDenom u) ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr := ratio_ge_one hu'
  have hp := first_log_augmented hu
  have hl := ratio_log_payment hu'
  have hlin : 0 ≤ 2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u) := by
    apply div_nonneg (by linarith [hu.2]) (by linarith [hu.1])
  have herr : 0 ≤ (log (u-1)-splitL (u-1))/u :=
    div_nonneg (sub_nonneg.mpr (splitL_le_log hx)) hu0.le
  have hprod := mul_le_mul (div_le_div_of_nonneg_right hp hu0.le) hl hlin herr
  have hrest := mul_le_mul_of_nonneg_left (splitL_le_log hr)
    (div_nonneg (splitL_nonneg hx) hu0.le)
  have hid : ((1+secondFactorRatio)*((u-2)^5/((u+2)^3*(u^2+16*u+4))))/u *
      (2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)) =
      (1+secondFactorRatio)*(2*momentWeight u/momentDenom u) := by
    dsimp [momentWeight,momentDenom]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid] at hprod
  unfold cExactKernel cLowerKernel
  have hd : (log (u-1)-splitL (u-1))/u*log (((1327:ℝ)/200-1)/(u+1)) =
      log (u-1)/u*log (((1327:ℝ)/200-1)/(u+1)) -
        splitL (u-1)/u*log (((1327:ℝ)/200-1)/(u+1)) := by ring
  rw [hd] at hprod
  linarith only [hprod,hrest]

/-- Consume the father's existing weighted-square certificate, not a new moment fit. -/
theorem augmented_moment_pointwise {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*(4*momentA*momentWeight u-
      2*momentA^2*(momentWeight u*momentDenom u)) ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hw : 0 ≤ momentWeight u := by
    unfold momentWeight
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hu.1) _) (by linarith [hu.2])
  have hq : 0 < momentDenom u := by unfold momentDenom; positivity
  exact (mul_le_mul_of_nonneg_left (weighted_square_payment hw hq momentA)
    (by linarith [secondFactorRatio_pos])).trans (augmented_kernel hu)

/-- New strictly positive payment for the portion left after the original moment payment. -/
def unpaidFactorPayment : ℝ := secondFactorRatio*momentPayment

theorem unpaidFactorPayment_pos : 0 < unpaidFactorPayment := by
  unfold unpaidFactorPayment
  apply mul_pos secondFactorRatio_pos
  rw [momentPayment_exact]
  norm_num

theorem unpaid_factor_le_kernel_residual :
    unpaidFactorPayment ≤ FirstActualRecovery.kernelRecovery-momentPayment := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hw : Continuous momentWeight := by unfold momentWeight; fun_prop
  have hq : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  have hp := (hw.const_mul (4*momentA)).sub (hq.const_mul (2*momentA^2))
  have hm := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    ((hp.const_mul (1+secondFactorRatio)).intervalIntegrable 2 (927/200))
    (h1.sub h2) (fun _ hu => augmented_moment_pointwise hu)
  dsimp only [Pi.sub_apply] at hm
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((hw.const_mul (4*momentA)).intervalIntegrable 2 (927/200))
      ((hq.const_mul (2*momentA^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    momentW_integral,momentQ_integral,intervalIntegral.integral_sub h1 h2] at hm
  have hid : 4*momentA*momentW-2*momentA^2*momentQ = momentPayment := by
    norm_num [momentA,momentW,momentQ,momentPayment]
  rw [hid] at hm
  have hc : FirstActualRecovery.kernelRecovery =
      (∫ u in (2:ℝ)..(927/200), cExactKernel (1327/200) u)-
      (∫ u in (2:ℝ)..(927/200), cLowerKernel (1327/200) u) := by
    unfold FirstActualRecovery.kernelRecovery
    rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
    norm_num [cLowerMass,cExactKernel]
  rw [← hc] at hm
  unfold unpaidFactorPayment
  nlinarith only [hm]

end F1UnpaidRecovery

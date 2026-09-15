import F1FixedSquareFTC

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open scoped Interval
namespace F1FixedSquareRecovery

theorem squareLower_integral :
    (∫ u in (2:ℝ)..(927/200), squareLower u) = squarePayment := by
  have hw : Continuous momentWeight := by unfold momentWeight; fun_prop
  have hq : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  have hs : Continuous (fun u => momentWeight u*(momentDenom u)^2) := by
    unfold momentWeight momentDenom
    fun_prop
  have hid (u : ℝ) : squareLower u = (2/qEnd)*
      (momentWeight u-(2*momentA)*(momentWeight u*momentDenom u)+
        momentA^2*(momentWeight u*(momentDenom u)^2)) := by
    unfold squareLower
    ring
  have hdiff : IntervalIntegrable
      (fun u => momentWeight u-(2*momentA)*(momentWeight u*momentDenom u))
      volume 2 (927/200) :=
    (hw.sub (hq.const_mul (2*momentA))).intervalIntegrable 2 (927/200)
  simp_rw [hid]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hdiff
      ((hs.const_mul (momentA^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_sub (hw.intervalIntegrable 2 (927/200))
      ((hq.const_mul (2*momentA)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    momentW_integral,momentQ_integral,forcedSquareMass_integral]
  rfl

/-- A single augmented original kernel; neither lower bound is added a second time. -/
theorem square_augmented_kernel {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*
      ((4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u))+
        squareLower u) ≤ cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  exact (mul_le_mul_of_nonneg_left (fixed_square_lower hu)
    (by linarith only [secondFactorRatio_pos])).trans (augmented_kernel hu)

/-- The second factor is used exactly once, on the same recovered square. -/
def combinedSquarePayment : ℝ := (1+secondFactorRatio)*squarePayment

theorem combinedSquarePayment_pos : 0 < combinedSquarePayment := by
  exact mul_pos (by linarith only [secondFactorRatio_pos]) squarePayment_pos

/-- The recovered square pays the actual residual AFTER both existing kernel payments. -/
theorem square_le_unpaid_kernel_residual :
    combinedSquarePayment ≤
      FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hw : Continuous momentWeight := by unfold momentWeight; fun_prop
  have hq : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  have hs : Continuous squareLower := by
    unfold squareLower momentWeight momentDenom
    fun_prop
  have hp : Continuous (fun u =>
      4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u)) :=
    (hw.const_mul (4*momentA)).sub (hq.const_mul (2*momentA^2))
  have hm := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (((hp.add hs).const_mul (1+secondFactorRatio)).intervalIntegrable 2 (927/200))
    (h1.sub h2) (fun _ hu => square_augmented_kernel hu)
  dsimp only [Pi.sub_apply,Pi.add_apply] at hm
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hp.intervalIntegrable 2 (927/200))
      (hs.intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_sub
      ((hw.const_mul (4*momentA)).intervalIntegrable 2 (927/200))
      ((hq.const_mul (2*momentA^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    momentW_integral,momentQ_integral,squareLower_integral,
    intervalIntegral.integral_sub h1 h2] at hm
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
  unfold combinedSquarePayment unpaidFactorPayment
  nlinarith only [hm]

end F1FixedSquareRecovery

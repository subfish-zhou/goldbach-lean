import F1KernelMoments

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open scoped Interval
namespace F1RemainingRecovery

/-- Exact weighted-square inequality, not a series or a chosen expansion order. -/
theorem weighted_square_payment {w q : ℝ} (hw : 0 ≤ w) (hq : 0 < q) (a : ℝ) :
    4*a*w-2*a^2*(w*q) ≤ 2*w/q := by
  apply (le_div_iff₀ hq).mpr
  nlinarith only [mul_nonneg hw (sq_nonneg (1-a*q))]

theorem moment_pointwise {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u) ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hw : 0 ≤ momentWeight u := by
    unfold momentWeight
    exact mul_nonneg (pow_nonneg (by linarith [hu.1]) _) (by linarith [hu.2])
  have hq : 0 < momentDenom u := by unfold momentDenom; positivity
  apply (weighted_square_payment hw hq momentA).trans
  have h := exact_kernel_payment (s := (1327/200:ℝ))
    (u := u) (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  convert h using 1 <;> first
    | rfl
    | (simp only [momentWeight,momentDenom,div_eq_mul_inv,mul_inv_rev]; ring)

theorem momentPayment_le_kernelRecovery : momentPayment ≤ FirstActualRecovery.kernelRecovery := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hw : Continuous momentWeight := by unfold momentWeight; fun_prop
  have hq : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  have hp := ((hw.const_mul (4*momentA)).sub (hq.const_mul (2*momentA^2))).intervalIntegrable (μ := volume) 2 (927/200)
  have hm := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    hp (h1.sub h2) (fun _ hu => moment_pointwise hu)
  dsimp only [Pi.sub_apply] at hm
  rw [intervalIntegral.integral_sub
    ((hw.const_mul (4*momentA)).intervalIntegrable 2 (927/200))
    ((hq.const_mul (2*momentA^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    momentW_integral,momentQ_integral,
    intervalIntegral.integral_sub h1 h2] at hm
  have hid : 4*momentA*momentW-2*momentA^2*momentQ = momentPayment := by
    norm_num [momentA,momentW,momentQ,momentPayment]
  rw [hid] at hm
  unfold FirstActualRecovery.kernelRecovery
  rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
  convert hm using 1
  norm_num [cLowerMass,cExactKernel]

theorem momentPayment_exact : momentPayment =
    (3228794015609681005058:ℝ)/62016932245283845324426309 := by
  norm_num [momentPayment,momentW,momentQ]

theorem kernelPayment_lt_momentPayment : kernelPayment (1327/200) < momentPayment := by
  norm_num [kernelPayment,kernelDenom,momentPayment,momentW,momentQ]

end F1RemainingRecovery

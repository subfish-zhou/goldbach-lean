import F1SecondLogMomentTwo

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1FixedSquareRecovery
open scoped Interval
namespace F1SecondLogRecovery

def aOne : ℝ := massW/massQOne
def aTwo : ℝ := massW/massQTwo

def polynomialOne (u : ℝ) : ℝ := 16*aOne*weight u-8*aOne^2*(weight u*denomOne u)
def polynomialTwo (u : ℝ) : ℝ := 16*aTwo*weight u-8*aTwo^2*(weight u*denomTwo u)
def secondPayment : ℝ := 8*massW^2/massQOne+8*massW^2/massQTwo

theorem secondPayment_pos : 0 < secondPayment := by
  norm_num [secondPayment,massW,massQOne,massQTwo]

theorem polynomial_second_lower {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    polynomialOne u+polynomialTwo u ≤ secondExact u := by
  have hw : 0 ≤ weight u := by
    unfold weight
    exact mul_nonneg (sub_nonneg.mpr hu.1) (pow_nonneg (sub_nonneg.mpr hu.2) _)
  obtain ⟨_,_,hd1,hd2⟩ := denominators_pos hu.1
  have h1 := mul_le_mul_of_nonneg_left (weighted_square_payment hw hd1 aOne)
    (by norm_num : (0:ℝ) ≤ 4)
  have h2 := mul_le_mul_of_nonneg_left (weighted_square_payment hw hd2 aTwo)
    (by norm_num : (0:ℝ) ≤ 4)
  have hh := second_rational_lower hu
  unfold polynomialOne polynomialTwo
  simp only [mul_div_assoc] at h1 h2 hh
  linarith only [h1,h2,hh]

theorem polynomialOne_continuous : Continuous polynomialOne := by
  unfold polynomialOne weight denomOne errorDenomOne
  fun_prop

theorem polynomialTwo_continuous : Continuous polynomialTwo := by
  unfold polynomialTwo weight denomTwo errorDenomTwo
  fun_prop

theorem polynomialOne_integral :
    (∫ u in (2:ℝ)..(927/200), polynomialOne u) = 8*massW^2/massQOne := by
  have hw : Continuous weight := by unfold weight; fun_prop
  have hq : Continuous (fun u => weight u*denomOne u) := by
    unfold weight denomOne errorDenomOne
    fun_prop
  unfold polynomialOne
  rw [intervalIntegral.integral_sub
    ((hw.const_mul (16*aOne)).intervalIntegrable 2 (927/200))
    ((hq.const_mul (8*aOne^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    massW_integral,massQOne_integral]
  norm_num [aOne,massW,massQOne]

theorem polynomialTwo_integral :
    (∫ u in (2:ℝ)..(927/200), polynomialTwo u) = 8*massW^2/massQTwo := by
  have hw : Continuous weight := by unfold weight; fun_prop
  have hq : Continuous (fun u => weight u*denomTwo u) := by
    unfold weight denomTwo errorDenomTwo
    fun_prop
  unfold polynomialTwo
  rw [intervalIntegral.integral_sub
    ((hw.const_mul (16*aTwo)).intervalIntegrable 2 (927/200))
    ((hq.const_mul (8*aTwo^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    massW_integral,massQTwo_integral]
  norm_num [aTwo,massW,massQTwo]

/-- Name only the already paid polynomial, not a new lower bound added twice. -/
def oldPaidKernel (u : ℝ) : ℝ := (1+secondFactorRatio)*
  ((4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u))+squareLower u)

theorem oldPaidKernel_continuous : Continuous oldPaidKernel := by
  unfold oldPaidKernel squareLower momentWeight momentDenom
  fun_prop

theorem oldPaidKernel_integral :
    (∫ u in (2:ℝ)..(927/200), oldPaidKernel u) =
      momentPayment+unpaidFactorPayment+combinedSquarePayment := by
  have hw : Continuous momentWeight := by unfold momentWeight; fun_prop
  have hq : Continuous (fun u => momentWeight u*momentDenom u) := by
    unfold momentWeight momentDenom
    fun_prop
  have hs : Continuous squareLower := by unfold squareLower momentWeight momentDenom; fun_prop
  have hp : Continuous (fun u => 4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u)) :=
    (hw.const_mul (4*momentA)).sub (hq.const_mul (2*momentA^2))
  unfold oldPaidKernel
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hp.intervalIntegrable 2 (927/200))
      (hs.intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_sub
      ((hw.const_mul (4*momentA)).intervalIntegrable 2 (927/200))
      ((hq.const_mul (2*momentA^2)).intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    momentW_integral,momentQ_integral,squareLower_integral]
  have hid : 4*momentA*momentW-2*momentA^2*momentQ = momentPayment := by
    norm_num [momentA,momentW,momentQ,momentPayment]
  rw [hid]
  unfold unpaidFactorPayment combinedSquarePayment
  ring

/-- The new payment is charged only AFTER all three old original-kernel payments. -/
theorem secondPayment_le_actual_residual : secondPayment ≤
    FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment-combinedSquarePayment := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have hp := (oldPaidKernel_continuous.add polynomialOne_continuous).add polynomialTwo_continuous
  have hpoint {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
      oldPaidKernel u+polynomialOne u+polynomialTwo u ≤
        cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
    have ha := square_retained hu
    have hb := polynomial_second_lower hu
    unfold oldPaidKernel
    linarith only [ha,hb]
  have hm := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (hp.intervalIntegrable 2 (927/200)) (h1.sub h2) (fun _ hu => hpoint hu)
  dsimp only [Pi.sub_apply,Pi.add_apply] at hm
  have hsum : Continuous (fun u => oldPaidKernel u+polynomialOne u) :=
    oldPaidKernel_continuous.add polynomialOne_continuous
  rw [intervalIntegral.integral_add
    (hsum.intervalIntegrable 2 (927/200))
    (polynomialTwo_continuous.intervalIntegrable 2 (927/200)),
    intervalIntegral.integral_add (oldPaidKernel_continuous.intervalIntegrable 2 (927/200))
    (polynomialOne_continuous.intervalIntegrable 2 (927/200)),
    oldPaidKernel_integral,polynomialOne_integral,polynomialTwo_integral,
    intervalIntegral.integral_sub h1 h2] at hm
  have hc : FirstActualRecovery.kernelRecovery =
      (∫ u in (2:ℝ)..(927/200), cExactKernel (1327/200) u)-
      (∫ u in (2:ℝ)..(927/200), cLowerKernel (1327/200) u) := by
    unfold FirstActualRecovery.kernelRecovery
    rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
    norm_num [cLowerMass,cExactKernel]
  rw [← hc] at hm
  unfold secondPayment
  linarith only [hm]

end F1SecondLogRecovery

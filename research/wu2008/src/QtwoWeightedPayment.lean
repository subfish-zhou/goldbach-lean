import QtwoWeightedMoment

namespace QtwoWeightedPayment
open Real Set MeasureTheory Wu2008DoubleSieve QtwoWeightedMoment
open FixedCoefficientUpperEnclosure (a b)
open FifthLogTotalMagnitude (f0 slope)
noncomputable section

theorem natural_kernel {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    FifthLogTotalMagnitude.kernel (f0/a) (slope/a^2) x y+rate*P x y/(x*y) ≤
      FifthActualIntegralRecovery.logRegular x y := by
  have hx0 := params.1.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hz := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hh := GlobalLowerSlack.scalar_joint_gain hz.1 hz.2
  have hm := div_le_div_of_nonneg_right hh (mul_pos params.1 (mul_pos hx0 hy0)).le
  have he : (f0+slope*(truncatedSixthLowerS 0 x y-SharpMassBalance.s0)+
      GlobalLowerSlack.scalarRate*(truncatedSixthLowerS 0 x y-SharpMassBalance.s0)*
        (FifthClassicalShape.q-truncatedSixthLowerS 0 x y))/(a*(x*y)) =
      FifthLogTotalMagnitude.kernel (f0/a) (slope/a^2) x y+rate*P x y/(x*y) := by
    unfold FifthLogTotalMagnitude.kernel rate P truncatedSixthLowerS truncatedSixthLowerC
      SharpMassBalance.s0 FifthClassicalShape.q
    field_simp [truncatedSixthLower_parameters.1.ne',hx0.ne',hy0.ne']
    ring
  rw [he] at hm
  have hsum : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  calc
    _ ≤ log (truncatedSixthLowerS 0 x y-1)/truncatedSixthLowerS 0 x y/(a*(x*y)) := hm
    _ = _ := by
      rw [FifthActualIntegralRecovery.log_literal hx hxy hy]
      unfold truncatedSixthLowerS truncatedSixthLowerC
      field_simp [truncatedSixthLower_parameters.1.ne',hx0.ne',hy0.ne',hsum.ne']
      ring

theorem kernel_lower {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    FifthLogTotalMagnitude.kernel (f0/a) (slope/a^2) x y+density x y ≤
      FifthActualIntegralRecovery.logRegular x y := by
  have hx0 := params.1.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hP : 0 ≤ P x y := by
    unfold P
    exact mul_nonneg (by linarith [hxy.trans hy]) (by linarith)
  have hr : 0 ≤ rate := (div_pos GlobalLowerSlack.scalarRate_pos (pow_pos params.1 3)).le
  have ht := mul_le_mul_of_nonneg_left
    (reciprocal_tangent (mul_pos hx0 hy0) params.2.2.1) (mul_nonneg hr hP)
  have hn := natural_kernel hx hxy hy
  have ht' : density x y ≤ rate*P x y/(x*y) := by
    simpa only [density,mul_one_div] using ht
  linarith only [ht',hn]

theorem gain_paid : gain ≤ GlobalLowerSlack.fifthLogSlack := by
  let p := f0/a
  let k := slope/a^2
  have hc : Continuous (fun y : ℝ => ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hik (y : ℝ) (hy : a ≤ y) : IntervalIntegrable
      (fun x => FifthLogTotalMagnitude.kernel p k x y) volume a y := by
    apply ContinuousOn.intervalIntegrable
    unfold FifthLogTotalMagnitude.kernel
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le hy] at hx
    exact mul_ne_zero (params.1.trans_le hx.1).ne' (params.1.trans_le hy).ne'
  have hi : IntervalIntegrable (FifthLogTotalMagnitude.inner p k) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold FifthLogTotalMagnitude.inner
    have hlog : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) := by
      apply ContinuousOn.sub _ continuousOn_const
      apply ContinuousOn.log continuousOn_id
      intro y hy
      rw [uIcc_of_le params.2.1.le] at hy
      exact (params.1.trans_le hy.1).ne'
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hlog).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => by
        rw [uIcc_of_le params.2.1.le] at hy
        exact (params.1.trans_le hy.1).ne')
  have hid : Continuous innerDensity := by unfold innerDensity innerMoment GlobalLowerSlack.innerPoly; fun_prop
  have hp (y : ℝ) (hy : y ∈ Icc a b) :
      FifthLogTotalMagnitude.inner p k y+innerDensity y ≤
        ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y := by
    have hd : IntervalIntegrable (fun x => density x y) volume a y :=
      (by unfold density P; fun_prop : Continuous (fun x => density x y)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hy.1 ((hik y hy.1).add hd)
      ((FifthActualIntegralRecovery.log_continuous.comp (f := fun x : ℝ => (x,y))
        (by fun_prop)).intervalIntegrable a y) (fun x hx => kernel_lower hx.1 hx.2 hy.2)
    rw [intervalIntegral.integral_add (hik y hy.1) hd,
      FifthLogTotalMagnitude.inner_ftc p k hy.1,inner_density] at hm
    exact hm
  have hm := intervalIntegral.integral_mono_on params.2.1.le (hi.add (hid.intervalIntegrable _ _))
    (hc.intervalIntegrable _ _) hp
  rw [intervalIntegral.integral_add hi (hid.intervalIntegrable _ _)] at hm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => FifthLogTotalMagnitude.primitive_derivative p k (by
      rw [uIcc_of_le params.2.1.le] at hy; exact hy.1)) hi] at hm
  have hg := gain_ftc
  unfold GlobalLowerSlack.fifthLogSlack GlobalLowerSlack.fifthFloor
    FifthLogTotalMagnitude.endpoint FifthActualIntegralRecovery.logIntegral
  dsimp [FifthLogTotalMagnitude.primitive,p,k] at hm
  linarith only [hm,hg]

end
end QtwoWeightedPayment

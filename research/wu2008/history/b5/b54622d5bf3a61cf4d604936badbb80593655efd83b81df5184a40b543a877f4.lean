import E07FifthClassicalScalar

namespace WuTarget.FifthClassicalClosure
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def momentKernel (x y : ℝ) : ℝ := (x+y)^2/(x*y)
def momentInner (y : ℝ) : ℝ :=
  (y^2-a^2)/(2*y)+2*(y-a)+y*(log y-log a)
def momentPrimitive (y : ℝ) : ℝ :=
  (y-a)^2+(y^2-a^2)/2*(log y-log a)

theorem moment_inner_integrable {y : ℝ} (hy : a ≤ y) :
    IntervalIntegrable (fun x => momentKernel x y) volume a y := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  rw [uIcc_of_le hy] at hx
  exact mul_ne_zero (truncatedSixthLower_parameters.1.trans_le hx.1).ne'
    (truncatedSixthLower_parameters.1.trans_le hy).ne'

theorem moment_inner_ftc {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, momentKernel x y) = momentInner y := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le hy
  have hd (x : ℝ) (hx : x ∈ uIcc a y) :
      HasDerivAt (fun x => (x^2/2+2*y*x+y^2*log x)/y) (momentKernel x y) x := by
    rw [uIcc_of_le hy] at hx
    have hx0 := ha.trans_le hx.1
    have hh := ((((hasDerivAt_id x).pow 2).div_const 2).add
      ((hasDerivAt_id x).const_mul (2*y))).add
      ((hasDerivAt_log hx0.ne').const_mul (y^2))
    convert hh.div_const y using 1 <;> first | rfl |
      (simp only [momentKernel, id_eq]; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (moment_inner_integrable hy)]
  dsimp only [momentInner]
  field_simp [ha.ne', hy0.ne']
  ring

theorem moment_primitive_derivative {y : ℝ} (hy : a ≤ y) :
    HasDerivAt momentPrimitive (momentInner y) y := by
  have hy0 := truncatedSixthLower_parameters.1.trans_le hy
  have hd := (((hasDerivAt_id y).sub_const a).pow 2).add
    (((((hasDerivAt_id y).pow 2).sub_const (a^2)).div_const 2).mul
      ((hasDerivAt_log hy0.ne').sub_const (log a)))
  convert hd using 1 <;> first | rfl |
    (simp only [momentInner, Pi.pow_apply, id_eq]; ring)

def quadraticKernel (p k c x y : ℝ) : ℝ :=
  FifthLogTotalMagnitude.kernel (p+2*b*k) (-k) x y + c*momentKernel x y
def quadraticInner (p k c y : ℝ) : ℝ :=
  FifthLogTotalMagnitude.inner (p+2*b*k) (-k) y + c*momentInner y
def quadraticPrimitive (p k c y : ℝ) : ℝ :=
  FifthLogTotalMagnitude.primitive (p+2*b*k) (-k) y + c*momentPrimitive y
def quadraticEndpoint (p k c : ℝ) : ℝ :=
  2*p*(log b-log a)^2+
    (4*k*(b-a)+2*c*(b^2-a^2))*(log b-log a)+4*c*(b-a)^2

theorem quadratic_kernel_literal (p k c x y : ℝ) :
    quadraticKernel p k c x y = (p+k*(x+y)+c*(x+y)^2)/(x*y) := by
  unfold quadraticKernel FifthLogTotalMagnitude.kernel momentKernel
  ring

theorem affine_inner_integrable (p k : ℝ) {y : ℝ} (hy : a ≤ y) :
    IntervalIntegrable (fun x => FifthLogTotalMagnitude.kernel p k x y) volume a y := by
  apply ContinuousOn.intervalIntegrable
  unfold FifthLogTotalMagnitude.kernel
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  rw [uIcc_of_le hy] at hx
  exact mul_ne_zero (truncatedSixthLower_parameters.1.trans_le hx.1).ne'
    (truncatedSixthLower_parameters.1.trans_le hy).ne'

theorem quadratic_inner_integrable (p k c : ℝ) {y : ℝ} (hy : a ≤ y) :
    IntervalIntegrable (fun x => quadraticKernel p k c x y) volume a y :=
  (affine_inner_integrable (p+2*b*k) (-k) hy).add
    ((moment_inner_integrable hy).const_mul c)

theorem quadratic_inner_ftc (p k c : ℝ) {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, quadraticKernel p k c x y) = quadraticInner p k c y := by
  have hi := affine_inner_integrable (p+2*b*k) (-k) hy
  unfold quadraticKernel quadraticInner
  rw [intervalIntegral.integral_add hi ((moment_inner_integrable hy).const_mul c),
    intervalIntegral.integral_const_mul, FifthLogTotalMagnitude.inner_ftc _ _ hy,
    moment_inner_ftc hy]

theorem quadratic_primitive_derivative (p k c : ℝ) {y : ℝ} (hy : a ≤ y) :
    HasDerivAt (quadraticPrimitive p k c) (quadraticInner p k c y) y :=
  (FifthLogTotalMagnitude.primitive_derivative (p+2*b*k) (-k) hy).add
    ((moment_primitive_derivative hy).const_mul c)

theorem quadratic_outer_integrable (p k c : ℝ) :
    IntervalIntegrable (quadraticInner p k c) volume a b := by
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
    exact (truncatedSixthLower_parameters.1.trans_le hy.1).ne'
  have hl : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log hn).sub continuousOn_const
  apply ContinuousOn.intervalIntegrable
  unfold quadraticInner FifthLogTotalMagnitude.inner momentInner
  apply ContinuousOn.add
  · exact (((continuousOn_const.add (continuousOn_const.mul
        (continuousOn_const.sub continuousOn_id))).mul hl).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
        continuousOn_id hn
  · apply continuousOn_const.mul
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact ((continuousOn_id.pow 2).sub continuousOn_const).div
          (continuousOn_const.mul continuousOn_id)
          (fun y hy => mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (hn y hy))
      · fun_prop
    · exact continuousOn_id.mul hl

theorem quadratic_triangle_ftc (p k c : ℝ) :
    4*(∫ y in a..b, ∫ x in a..y, quadraticKernel p k c x y) =
      quadraticEndpoint p k c := by
  have hi : (∫ y in a..b, ∫ x in a..y, quadraticKernel p k c x y) =
      ∫ y in a..b, quadraticInner p k c y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
    exact quadratic_inner_ftc p k c hy.1
  rw [hi, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => quadratic_primitive_derivative p k c (by
      rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
      exact hy.1)) (quadratic_outer_integrable p k c)]
  unfold quadraticEndpoint quadraticPrimitive FifthLogTotalMagnitude.primitive momentPrimitive
  ring

theorem quadratic_endpoint_comparison (p k c : ℝ)
    (h : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      quadraticKernel p k c x y ≤ FifthActualIntegralRecovery.logRegular x y) :
    quadraticEndpoint p k c ≤ FifthActualIntegralRecovery.logIntegral := by
  have hp := truncatedSixthLower_parameters
  have hm : Continuous (fun y : ℝ => ∫ x in a..y,
      FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ =>
      FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp
        (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      quadraticInner p k c y ≤ ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y := by
    rw [← quadratic_inner_ftc p k c hy.1]
    exact intervalIntegral.integral_mono_on hy.1 (quadratic_inner_integrable p k c hy.1)
      ((FifthActualIntegralRecovery.log_continuous.comp
        (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (fun x hx => h x y hx.1 hx.2 hy.2)
  have hi := intervalIntegral.integral_mono_on hp.2.1.le
    (quadratic_outer_integrable p k c) (hm.intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => quadratic_primitive_derivative p k c (by
      rw [uIcc_of_le hp.2.1.le] at hy
      exact hy.1)) (quadratic_outer_integrable p k c)] at hi
  have he : 4*(quadraticPrimitive p k c b-quadraticPrimitive p k c a) =
      quadraticEndpoint p k c := by
    unfold quadraticPrimitive quadraticEndpoint FifthLogTotalMagnitude.primitive momentPrimitive
    ring
  unfold FifthActualIntegralRecovery.logIntegral
  linarith only [hi, he]

end
end WuTarget.FifthClassicalClosure

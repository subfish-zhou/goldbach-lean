import Wu18938Campaign.M3.Confirmed.FifthShape

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthMoments

open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open WuTarget.FifthClassicalClosure

def inner3 (y : ℝ) : ℝ :=
  (y^3-a^3)/(3*y)+(3/2)*(y^2-a^2)+3*y*(y-a)+y^2*(log y-log a)
def inner4 (y : ℝ) : ℝ :=
  (y^4-a^4)/(4*y)+(4/3)*(y^3-a^3)+3*y*(y^2-a^2)+
    4*y^2*(y-a)+y^3*(log y-log a)
def primitive3 (y : ℝ) : ℝ :=
  (y^3-a^3)/3*(log y-log a)+(3/2)*(y-a)*(y^2-a^2)
def primitive4 (y : ℝ) : ℝ :=
  (y^4-a^4)/4*(log y-log a)+(4/3)*(y-a)*(y^3-a^3)+(3/4)*(y^2-a^2)^2

theorem power_integrable (n : ℕ) {y : ℝ} (hy : a ≤ y) :
    IntervalIntegrable (fun x => (x+y)^n/(x*y)) volume a y := by
  apply ContinuousOn.intervalIntegrable
  exact (by fun_prop : ContinuousOn (fun x : ℝ => (x+y)^n) (uIcc a y)).div
    (by fun_prop) (fun x hx => by
      rw [uIcc_of_le hy] at hx
      exact mul_ne_zero (truncatedSixthLower_parameters.1.trans_le hx.1).ne'
        (truncatedSixthLower_parameters.1.trans_le hy).ne')

theorem inner3_ftc {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, (x+y)^3/(x*y)) = inner3 y := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le hy
  have hd (x : ℝ) (hx : x ∈ uIcc a y) : HasDerivAt
      (fun x => x^3/(3*y)+(3/2)*x^2+3*y*x+y^2*log x) ((x+y)^3/(x*y)) x := by
    rw [uIcc_of_le hy] at hx
    have hx0 := ha.trans_le hx.1
    convert! (((((hasDerivAt_id x).pow 3).div_const (3*y)).add
      (((hasDerivAt_id x).pow 2).const_mul (3/2))).add
      ((hasDerivAt_id x).const_mul (3*y))).add
      ((hasDerivAt_log hx0.ne').const_mul (y^2)) using 1
    dsimp
    field_simp [hx0.ne',hy0.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (power_integrable 3 hy)]
  unfold inner3
  ring

theorem inner4_ftc {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, (x+y)^4/(x*y)) = inner4 y := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le hy
  have hd (x : ℝ) (hx : x ∈ uIcc a y) : HasDerivAt
      (fun x => x^4/(4*y)+(4/3)*x^3+3*y*x^2+4*y^2*x+y^3*log x)
      ((x+y)^4/(x*y)) x := by
    rw [uIcc_of_le hy] at hx
    have hx0 := ha.trans_le hx.1
    convert! ((((((hasDerivAt_id x).pow 4).div_const (4*y)).add
      (((hasDerivAt_id x).pow 3).const_mul (4/3))).add
      (((hasDerivAt_id x).pow 2).const_mul (3*y))).add
      ((hasDerivAt_id x).const_mul (4*y^2))).add
      ((hasDerivAt_log hx0.ne').const_mul (y^3)) using 1
    dsimp
    field_simp [hx0.ne',hy0.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (power_integrable 4 hy)]
  unfold inner4
  ring

theorem primitive3_derivative {y : ℝ} (hy : a ≤ y) :
    HasDerivAt primitive3 (inner3 y) y := by
  have hy0 := truncatedSixthLower_parameters.1.trans_le hy
  convert! (((((hasDerivAt_id y).pow 3).sub_const (a^3)).div_const 3).mul
    ((hasDerivAt_log hy0.ne').sub_const (log a))).add
    ((((hasDerivAt_id y).sub_const a).const_mul (3/2)).mul
      (((hasDerivAt_id y).pow 2).sub_const (a^2))) using 1
  dsimp [inner3]
  ring

theorem primitive4_derivative {y : ℝ} (hy : a ≤ y) :
    HasDerivAt primitive4 (inner4 y) y := by
  have hy0 := truncatedSixthLower_parameters.1.trans_le hy
  convert! ((((((hasDerivAt_id y).pow 4).sub_const (a^4)).div_const 4).mul
    ((hasDerivAt_log hy0.ne').sub_const (log a))).add
    ((((hasDerivAt_id y).sub_const a).const_mul (4/3)).mul
      (((hasDerivAt_id y).pow 3).sub_const (a^3)))).add
    (((((hasDerivAt_id y).pow 2).sub_const (a^2)).pow 2).const_mul (3/4)) using 1
  dsimp [inner4]
  ring

def kernel (p k c d e x y : ℝ) : ℝ :=
  quadraticKernel p k c x y+d*((x+y)^3/(x*y))+e*((x+y)^4/(x*y))
def inner (p k c d e y : ℝ) : ℝ :=
  quadraticInner p k c y+d*inner3 y+e*inner4 y
def primitive (p k c d e y : ℝ) : ℝ :=
  quadraticPrimitive p k c y+d*primitive3 y+e*primitive4 y
def endpoint (p k c d e : ℝ) : ℝ :=
  quadraticEndpoint p k c+4*d*primitive3 b+4*e*primitive4 b

theorem inner_integrable (p k c d e : ℝ) {y : ℝ} (hy : a ≤ y) :
    IntervalIntegrable (fun x => kernel p k c d e x y) volume a y :=
  ((quadratic_inner_integrable p k c hy).add ((power_integrable 3 hy).const_mul d)).add
    ((power_integrable 4 hy).const_mul e)

theorem inner_ftc (p k c d e : ℝ) {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, kernel p k c d e x y) = inner p k c d e y := by
  unfold kernel inner
  rw [intervalIntegral.integral_add
    ((quadratic_inner_integrable p k c hy).add ((power_integrable 3 hy).const_mul d))
      ((power_integrable 4 hy).const_mul e),
    intervalIntegral.integral_add (quadratic_inner_integrable p k c hy)
      ((power_integrable 3 hy).const_mul d)]
  simp only [intervalIntegral.integral_const_mul,quadratic_inner_ftc p k c hy,
    inner3_ftc hy,inner4_ftc hy]

theorem outer_integrable (p k c d e : ℝ) :
    IntervalIntegrable (inner p k c d e) volume a b := by
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
    exact (truncatedSixthLower_parameters.1.trans_le hy.1).ne'
  have hl : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log hn).sub continuousOn_const
  have h3 : ContinuousOn inner3 (uIcc a b) := by
    unfold inner3
    exact (((((by fun_prop : ContinuousOn (fun y : ℝ => y^3-a^3) (uIcc a b)).div
      (by fun_prop) (fun y hy => mul_ne_zero (by norm_num) (hn y hy))).add
      (by fun_prop)).add (by fun_prop)).add
      ((by fun_prop : ContinuousOn (fun y : ℝ => y^2) (uIcc a b)).mul hl))
  have h4 : ContinuousOn inner4 (uIcc a b) := by
    unfold inner4
    exact ((((((by fun_prop : ContinuousOn (fun y : ℝ => y^4-a^4) (uIcc a b)).div
      (by fun_prop) (fun y hy => mul_ne_zero (by norm_num) (hn y hy))).add
      (by fun_prop)).add (by fun_prop)).add (by fun_prop)).add
      ((by fun_prop : ContinuousOn (fun y : ℝ => y^3) (uIcc a b)).mul hl))
  exact ((quadratic_outer_integrable p k c).add (h3.intervalIntegrable.const_mul d)).add
    (h4.intervalIntegrable.const_mul e)

theorem primitive_derivative (p k c d e : ℝ) {y : ℝ} (hy : a ≤ y) :
    HasDerivAt (primitive p k c d e) (inner p k c d e y) y :=
  ((quadratic_primitive_derivative p k c hy).add
    ((primitive3_derivative hy).const_mul d)).add ((primitive4_derivative hy).const_mul e)

theorem endpoint_comparison (p k c d e : ℝ)
    (h : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      kernel p k c d e x y ≤ FifthActualIntegralRecovery.logRegular x y) :
    endpoint p k c d e ≤ FifthActualIntegralRecovery.logIntegral := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun y : ℝ => ∫ x in a..y,
      FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ =>
      FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp
        (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hi := intervalIntegral.integral_mono_on hp.2.1.le
    (outer_integrable p k c d e) (hc.intervalIntegrable a b) (fun y hy => by
      rw [← inner_ftc p k c d e hy.1]
      exact intervalIntegral.integral_mono_on hy.1 (inner_integrable p k c d e hy.1)
        ((FifthActualIntegralRecovery.log_continuous.comp
          (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
        (fun x hx => h x y hx.1 hx.2 hy.2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => primitive_derivative p k c d e (by
      rw [uIcc_of_le hp.2.1.le] at hy
      exact hy.1)) (outer_integrable p k c d e)] at hi
  have he : 4*(primitive p k c d e b-primitive p k c d e a) = endpoint p k c d e := by
    unfold primitive endpoint quadraticPrimitive quadraticEndpoint
      FifthLogTotalMagnitude.primitive WuTarget.FifthClassicalClosure.momentPrimitive
      primitive3 primitive4
    ring
  unfold FifthActualIntegralRecovery.logIntegral
  linarith only [hi,he]

end Wu18938Campaign.M3.Confirmed.FifthMoments

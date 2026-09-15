import MathlibNt.Wu2008DoubleSieve.SharpMassBalance

namespace Wu2008DoubleSieve.PositiveSixthFTC
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open scoped Interval

noncomputable def innerPrimitive (x y : ℝ) : ℝ :=
  128*(-2*x*log y-y^2/x-4*y+(2*lam+1/4)*(y/x+log y)-lam*log y/(4*x))

noncomputable def logY : ℝ := log m-log b
noncomputable def outerPrimitive (x : ℝ) : ℝ :=
  128*(-x^2*logY-(m^2-b^2)*log x-4*(m-b)*x+
    (2*lam+1/4)*(logY*x+(m-b)*log x)-lam*logY*log x/4)

 theorem inner_derivative {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (innerPrimitive x) (polynomialKernel x y) y := by
  have hl := hasDerivAt_log hy
  have hi := hasDerivAt_id y
  have h := (((((hl.const_mul (-2*x)).sub ((hi.pow 2).div_const x)).sub
    (hi.const_mul 4)).add (((hi.div_const x).add hl).const_mul (2*lam+1/4))).sub
    ((hl.const_mul lam).div_const (4*x))).const_mul 128
  convert h using 1 <;> first | rfl | (dsimp [polynomialKernel]; field_simp; ring)

 theorem outer_derivative {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt outerPrimitive (innerPrimitive x m-innerPrimitive x b) x := by
  have hl := hasDerivAt_log hx
  have hi := hasDerivAt_id x
  have h := (((((((hi.pow 2).neg.mul_const logY).sub (hl.const_mul (m^2-b^2))).sub
    (hi.const_mul (4*(m-b)))).add (((hi.const_mul logY).add
    (hl.const_mul (m-b))).const_mul (2*lam+1/4))).sub
    ((hl.const_mul (lam*logY)).div_const 4)).const_mul 128)
  convert h using 1 <;> first | rfl | (dsimp [innerPrimitive,logY]; field_simp; ring)

 theorem geometry : 0 < a ∧ a ≤ b ∧ 0 < b ∧ b ≤ m ∧ m ≤ s := by
  norm_num [a,b,m,lam,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem polynomial_integrable (x : ℝ) :
    IntervalIntegrable (polynomialKernel x) volume b m := by
  apply ContinuousOn.intervalIntegrable
  have hn (y : ℝ) (hy : y ∈ uIcc b m) : y ≠ 0 := by
    rw [uIcc_of_le geometry.2.2.2.1] at hy
    exact (geometry.2.2.1.trans_le hy.1).ne'
  unfold polynomialKernel
  simp only [div_mul_eq_div_div]
  exact (by fun_prop : ContinuousOn (fun y : ℝ => 128*(lam-x-y)*(2*x+2*y-1/4)/x) (uIcc b m)).div continuousOn_id hn

 theorem inner_ftc {x : ℝ} (hx : 0 < x) :
    (∫ y in b..m, polynomialKernel x y) = innerPrimitive x m-innerPrimitive x b := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (polynomial_integrable x)
  intro y hy
  rw [uIcc_of_le geometry.2.2.2.1] at hy
  exact inner_derivative hx.ne' (geometry.2.2.1.trans_le hy.1).ne'

 theorem primitive_difference_integrable :
    IntervalIntegrable (fun x => innerPrimitive x m-innerPrimitive x b) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 := by
    rw [uIcc_of_le geometry.2.1] at hx
    exact (geometry.1.trans_le hx.1).ne'
  have hc (y : ℝ) : ContinuousOn (fun x => innerPrimitive x y) (uIcc a b) := by
    unfold innerPrimitive
    apply_rules [ContinuousOn.const_mul, ContinuousOn.sub, ContinuousOn.add,
      ContinuousOn.mul, continuousOn_const, continuousOn_id]
    · exact continuousOn_id.inv₀ hn
    · exact continuousOn_id.inv₀ hn
    · exact (continuousOn_id.const_mul 4).inv₀ (fun x hx => mul_ne_zero (by norm_num) (hn x hx))
  exact (hc m).sub (hc b)

 theorem rectangle_ftc :
    (4*∫ x in a..b, ∫ y in b..m, polynomialKernel x y) =
      4*(outerPrimitive b-outerPrimitive a) := by
  have he : (∫ x in a..b, ∫ y in b..m, polynomialKernel x y) =
      ∫ x in a..b, innerPrimitive x m-innerPrimitive x b := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le geometry.2.1] at hx
    exact inner_ftc (geometry.1.trans_le hx.1)
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt _ primitive_difference_integrable]
  intro x hx
  rw [uIcc_of_le geometry.2.1] at hx
  exact outer_derivative (geometry.1.trans_le hx.1).ne'

end Wu2008DoubleSieve.PositiveSixthFTC

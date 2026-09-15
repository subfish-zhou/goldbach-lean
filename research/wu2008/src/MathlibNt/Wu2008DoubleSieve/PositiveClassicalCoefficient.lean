import MathlibNt.Wu2008DoubleSieve.PositiveSixthFTC

namespace Wu2008DoubleSieve.PositiveClassicalCoefficient
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance PositiveSixthFTC
open scoped Interval

/-- The exact endpoint polynomial in the two genuine logarithms. -/
noncomputable def rectangleValue (X Y : ℝ) : ℝ :=
  512*(-(b^2-a^2)*Y-(m^2-b^2)*X-4*(b-a)*(m-b)+
    (2*lam+1/4)*((b-a)*Y+(m-b)*X)-(lam/4)*X*Y)

/-- Fixed rational signed payment, with no sampling or quadrature. -/
noncomputable def rectangleBound : ℝ :=
  512*(-(b^2-a^2)*upperLog (m/b)-(m^2-b^2)*upperLog (b/a)-4*(b-a)*(m-b)+
    (2*lam+1/4)*((b-a)*lowerLog (m/b)+(m-b)*lowerLog (b/a))-
    (lam/4)*upperLog (b/a)*upperLog (m/b))

 theorem rectangle_endpoint :
    4*(outerPrimitive b-outerPrimitive a) = rectangleValue (log (b/a)) (log (m/b)) := by
  rw [log_div geometry.2.2.1.ne' geometry.1.ne',
    log_div (geometry.2.2.1.trans_le geometry.2.2.2.1).ne' geometry.2.2.1.ne']
  unfold outerPrimitive rectangleValue logY
  ring

 theorem rectangle_bound : rectangleBound ≤ rectangleValue (log (b/a)) (log (m/b)) := by
  have hx : 1 ≤ b/a := by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hy : 1 ≤ m/b := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hxl := log_lower hx
  have hxu := log_upper hx
  have hyl := log_lower hy
  have hyu := log_upper hy
  have hx0 : 0 ≤ log (b/a) := log_nonneg hx
  have hyu0 : 0 ≤ upperLog (m/b) := (log_nonneg hy).trans hyu
  have hxy := mul_le_mul hxu hyu (log_nonneg hy)
    ((log_nonneg hx).trans hxu)
  unfold rectangleBound rectangleValue
  norm_num [a,b,m,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog,upperLog] at hxl hxu hyl hyu hxy ⊢
  nlinarith

 theorem rectangle_bound_gt_sixteen_fifths : (16/5 : ℝ) < rectangleBound := by
  norm_num [rectangleBound,a,b,m,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog,upperLog]

/-- The full original sixth integral, including its nonnegative omitted complement. -/
 theorem actual_sixth_ge_rectangle :
    rectangleValue (log (b/a)) (log (m/b)) ≤ truncatedSixthLowerF6lin := by
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      innerPrimitive x m-innerPrimitive x b ≤
        ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.2.2.1
      (polynomial_integrable x) (hc1.intervalIntegrable b m)
      (fun y hy => sixth_polynomial_lower hx hy)
    rw [inner_ftc (geometry.1.trans_le hx.1)] at hi
    have hn : 0 ≤ ∫ y in m..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg geometry.2.2.2.2
        (fun y hy => ClassicalPositiveBounds.sixth_regular_nonneg hx
          ⟨geometry.2.2.2.1.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b m) (hc1.intervalIntegrable m s)
    simp only [Function.comp_apply] at hi he
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    primitive_difference_integrable (hinner.intervalIntegrable a b) hpoint
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :=
    outer_derivative (geometry.1.trans_le ((uIcc_of_le geometry.2.1 ▸ hx).1)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd primitive_difference_integrable] at hi
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  rw [← rectangle_endpoint]
  linarith

 theorem actual_sixth_ge_rational : rectangleBound ≤ truncatedSixthLowerF6lin :=
  rectangle_bound.trans actual_sixth_ge_rectangle

 theorem actual_sixth_gt_sixteen_fifths : (16/5 : ℝ) < truncatedSixthLowerF6lin :=
  rectangle_bound_gt_sixteen_fifths.trans_le actual_sixth_ge_rational

 theorem actual_sixth_gt_three : (3 : ℝ) < truncatedSixthLowerF6lin := by
  linarith [actual_sixth_gt_sixteen_fifths]

/-- Preserve the full rational rectangle payment in the original eleven-term coefficient. -/
 theorem complete_coefficient_gt_exact_balance :
    54035471/1012500 + 3/2 + rectangleBound + 47/481250 - 179/4 - 12 - 21/20 <
      TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SharpSingleBalance.base_sharp_lower
  have hg := SharpSingleBalance.G_pair_lt_179_quarters
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := four_weighted_lt_21_twentieths
  have hp := fifth_gt_three_halves
  have hq := actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3) +
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma < 179/4 at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient
  linarith

 theorem complete_coefficient_gt_quantitative :
    (20930131/77962500 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have h := complete_coefficient_gt_exact_balance
  have hq := rectangle_bound_gt_sixteen_fifths
  linarith

 theorem complete_coefficient_gt_twentieth :
    (1/20 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  linarith [complete_coefficient_gt_quantitative]

 theorem complete_coefficient_positive :
    0 < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  linarith [complete_coefficient_gt_quantitative]

/-- Literal original weights, domains and truncated sixth are all retained. -/
 theorem literal_coefficient_gt_quantitative :
    (20930131/77962500 : ℝ) <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
      truncatedSixthLowerF6lin + 47/481250 -
      SingleUpperClassicalLimit.Glin (1/3) -
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma - 8*J9 -
      16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
      8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_quantitative

end Wu2008DoubleSieve.PositiveClassicalCoefficient

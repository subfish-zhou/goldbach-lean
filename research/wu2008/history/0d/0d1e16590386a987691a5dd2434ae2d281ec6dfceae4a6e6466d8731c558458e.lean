import E07FifthClassicalMoments

namespace WuTarget.FifthClassicalClosure
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
noncomputable section

def sumCenter : ℝ := 1/(2*a)-4
def shapeConstant : ℝ :=
  (logCenter/4+shapeSlope*sumCenter-shapeCurvature*sumCenter^2)/a
def shapeLinear : ℝ := (-shapeSlope+2*shapeCurvature*sumCenter)/a^2
def shapeSquare : ℝ := -shapeCurvature/a^3
def endpointLinear : ℝ := 4*shapeLinear*(b-a)+2*shapeSquare*(b^2-a^2)
def ratioLower : ℝ :=
  SharpLogRecurrence.lowerLog (4/3)+SharpLogRecurrence.lowerLog (3*b/(4*a))
def rationalLower : ℝ :=
  2*shapeConstant*ratioLower^2+endpointLinear*ratioLower+4*shapeSquare*(b-a)^2

theorem shape_kernel_identity (x y : ℝ) :
    quadraticKernel shapeConstant shapeLinear shapeSquare x y =
      scalarShape ((1/2-x-y)/a)/(a*x*y) := by
  rw [quadratic_kernel_literal]
  unfold shapeConstant shapeLinear shapeSquare scalarShape sumCenter
  field_simp [show a ≠ 0 from truncatedSixthLower_parameters.1.ne']
  ring

theorem original_kernel_lower {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    quadraticKernel shapeConstant shapeLinear shapeSquare x y ≤
      FifthActualIntegralRecovery.logRegular x y := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hp := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hs : 17/5 ≤ truncatedSixthLowerS 0 x y := by
    have h0 : (17/5 : ℝ) ≤ s0 := by
      norm_num [s0, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
    exact h0.trans hp.1
  have hh := div_le_div_of_nonneg_right (scalar_shape_lower hs)
    (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b, truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  rw [FifthActualIntegralRecovery.log_literal hx hxy hy, shape_kernel_identity]
  convert hh using 1 <;> first | rfl |
    (simp only [truncatedSixthLowerS, truncatedSixthLowerC, sub_zero, a]
     field_simp [ha.ne', hx0.ne', hy0.ne', hz.ne'])

theorem original_integral_lower :
    quadraticEndpoint shapeConstant shapeLinear shapeSquare ≤ Wu08TerminalAlignment.fifthMain := by
  have h := quadratic_endpoint_comparison shapeConstant shapeLinear shapeSquare
    (fun _ _ hx hxy hy => original_kernel_lower hx hxy hy)
  have hd := FifthActualIntegralRecovery.integral_distance.1
  change quadraticEndpoint shapeConstant shapeLinear shapeSquare ≤ fifthPairFlin
  linarith only [h, hd]

theorem ratio_lower : ratioLower ≤ log b-log a := by
  have h1 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 4/3)
  have h2 := SharpLogRecurrence.log_lower
    (show (1 : ℝ) ≤ 3*b/(4*a) by
      norm_num [a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta])
  have ha : a ≠ 0 := truncatedSixthLower_parameters.1.ne'
  have hb : b ≠ 0 :=
    (truncatedSixthLower_parameters.1.trans truncatedSixthLower_parameters.2.1).ne'
  have he : log (4/3 : ℝ)+log (3*b/(4*a)) = log b-log a := by
    rw [← log_mul (by norm_num : (4/3 : ℝ) ≠ 0)
      (div_ne_zero (mul_ne_zero (by norm_num) hb) (mul_ne_zero (by norm_num) ha))]
    rw [show (4/3 : ℝ)*(3*b/(4*a))=b/a by ring]
    exact log_div hb ha
  unfold ratioLower
  linarith only [h1, h2, he]

theorem rational_signs :
    0 ≤ shapeConstant ∧ 0 ≤ endpointLinear ∧ 0 ≤ ratioLower := by
  norm_num [shapeConstant, endpointLinear, shapeLinear, shapeSquare, sumCenter,
    shapeSlope, shapeCurvature, logCenter, ratioLower, SharpLogRecurrence.lowerLog,
    a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem rational_lower_le_endpoint :
    rationalLower ≤ quadraticEndpoint shapeConstant shapeLinear shapeSquare := by
  have hs := rational_signs
  have hq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.2.2 ratio_lower 2)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.1)
  have hl := mul_le_mul_of_nonneg_left ratio_lower hs.2.1
  unfold rationalLower quadraticEndpoint endpointLinear at *
  linarith only [hq, hl]

theorem rational_lower : rationalLower ≤ Wu08TerminalAlignment.fifthMain :=
  rational_lower_le_endpoint.trans original_integral_lower

theorem target_le_rational : (33/20 : ℝ) ≤ rationalLower := by
  norm_num [rationalLower, shapeConstant, endpointLinear, shapeLinear, shapeSquare, sumCenter,
    shapeSlope, shapeCurvature, logCenter, ratioLower, SharpLogRecurrence.lowerLog,
    a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem fifth_main_lower : (33/20 : ℝ) ≤ Wu08TerminalAlignment.fifthMain :=
  target_le_rational.trans rational_lower

end
end WuTarget.FifthClassicalClosure

import E07FifthClassicalConsumer

namespace WuTarget.FifthClassicalClosure
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

theorem fifth_main_original_integral :
    Wu08TerminalAlignment.fifthMain =
      4*(∫ y in a..b, ∫ x in a..y,
        wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y))) := by
  change fifthPairFlin = _
  rw [FifthActualIntegralRecovery.actual_triangle]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hy.1] at hx
  simpa only [truncatedSixthLowerS, truncatedSixthLowerC, sub_zero, a] using
    ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2

theorem final_target : (33/20 : ℝ) ≤ Wu08TerminalAlignment.fifthMain :=
  fifth_main_lower

theorem final_original_target :
    (33/20 : ℝ) ≤ 4*(∫ y in a..b, ∫ x in a..y,
      wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y))) := by
  rw [← fifth_main_original_integral]
  exact final_target

set_option pp.fullNames true

#check @log_remainder_derivative
#print axioms log_remainder_derivative
#check @log_remainder_nonneg
#print axioms log_remainder_nonneg
#check @log_center_lower
#print axioms log_center_lower
#check @scalar_shape_lower
#print axioms scalar_shape_lower
#check @moment_inner_integrable
#print axioms moment_inner_integrable
#check @moment_inner_ftc
#print axioms moment_inner_ftc
#check @moment_primitive_derivative
#print axioms moment_primitive_derivative
#check @quadratic_kernel_literal
#print axioms quadratic_kernel_literal
#check @affine_inner_integrable
#print axioms affine_inner_integrable
#check @quadratic_inner_integrable
#print axioms quadratic_inner_integrable
#check @quadratic_inner_ftc
#print axioms quadratic_inner_ftc
#check @quadratic_primitive_derivative
#print axioms quadratic_primitive_derivative
#check @quadratic_outer_integrable
#print axioms quadratic_outer_integrable
#check @quadratic_triangle_ftc
#print axioms quadratic_triangle_ftc
#check @quadratic_endpoint_comparison
#print axioms quadratic_endpoint_comparison
#check @shape_kernel_identity
#print axioms shape_kernel_identity
#check @original_kernel_lower
#print axioms original_kernel_lower
#check @original_integral_lower
#print axioms original_integral_lower
#check @ratio_lower
#print axioms ratio_lower
#check @rational_signs
#print axioms rational_signs
#check @rational_lower_le_endpoint
#print axioms rational_lower_le_endpoint
#check @rational_lower
#print axioms rational_lower
#check @target_le_rational
#print axioms target_le_rational
#check @fifth_main_lower
#print axioms fifth_main_lower
#check @net_credit_exact
#print axioms net_credit_exact
#check @net_credit_pos
#print axioms net_credit_pos
#check @net_credit_lower
#print axioms net_credit_lower
#check @net_accounting_identity
#print axioms net_accounting_identity
#check @exact_block_replacement
#print axioms exact_block_replacement
#check @block_lower_replaced_retained
#print axioms block_lower_replaced_retained
#check @block_lower_replaced
#print axioms block_lower_replaced
#check @block_with_retained_slack
#print axioms block_with_retained_slack
#check @credited_lt_previous
#print axioms credited_lt_previous
#check @credited_lt_actual
#print axioms credited_lt_actual
#check @credited_identity
#print axioms credited_identity
#check @enhanced_P2_paid
#print axioms enhanced_P2_paid
#check @fifth_main_original_integral
#print axioms fifth_main_original_integral
#check @final_target
#print axioms final_target
#check @final_original_target
#print axioms final_original_target

end
end WuTarget.FifthClassicalClosure

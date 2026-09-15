import E07FifthSourceErrorTransport

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

theorem source_formula_to_fifthMain :
    (8*∫ t in a..b, ∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a),
      wuLowerCoefficient u/(t*u*(1-2*t-2*a*u))) = Wu08TerminalAlignment.fifthMain :=
  paper_classical_eq_fifthMain

theorem source_a_formula_to_fifthMain :
    (8*∫ t in a..b, ∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a),
      paperA u/(t*u*(1-2*t-2*a*u))) = Wu08TerminalAlignment.fifthMain := by
  rw [← paper_a_original_integral]
  exact paper_classical_eq_fifthMain

set_option pp.fullNames true

#print wuLowerCoefficient
#check @paperKernel
#print axioms paperKernel
#check @paperClassical
#print axioms paperClassical
#check @parameters_exact
#print axioms parameters_exact
#check @coefficient_initial
#print axioms coefficient_initial
#check @coefficient_recurrence
#print axioms coefficient_recurrence
#check @parameter_range
#print axioms parameter_range
#check @triangle_outer_first
#print axioms triangle_outer_first
#check @paper_inner_substitution
#print axioms paper_inner_substitution
#check @paper_classical_eq_fifthMain
#print axioms paper_classical_eq_fifthMain
#check @sumShear
#print axioms sumShear
#check @sumKernel
#print axioms sumKernel
#check @sliceLower
#print axioms sliceLower
#check @reducedKernel
#print axioms reducedKernel
#check @sum_shear_preserving
#print axioms sum_shear_preserving
#check @sum_kernel_integrable
#print axioms sum_kernel_integrable
#check @sum_kernel_integral
#print axioms sum_kernel_integral
#check @slice_geometry
#print axioms slice_geometry
#check @sum_region_iff
#print axioms sum_region_iff
#check @pair_reciprocal_ftc
#print axioms pair_reciprocal_ftc
#check @sum_inner_integral
#print axioms sum_inner_integral
#check @fifth_main_one_dimensional
#print axioms fifth_main_one_dimensional
#check @paperA
#print axioms paperA
#check @geometricSplit
#print axioms geometricSplit
#check @lowerBranch
#print axioms lowerBranch
#check @upperBranch
#print axioms upperBranch
#check @scalarReduced
#print axioms scalarReduced
#check @paper_a_eq
#print axioms paper_a_eq
#check @paper_kernel_literal
#print axioms paper_kernel_literal
#check @paper_a_original_integral
#print axioms paper_a_original_integral
#check @fixed_breakpoints
#print axioms fixed_breakpoints
#check @scalar_reduced_literal
#print axioms scalar_reduced_literal
#check @scalar_parameter_transport
#print axioms scalar_parameter_transport
#check @source_finite_cover
#print axioms source_finite_cover
#check @scalar_geometry
#print axioms scalar_geometry
#check @scalar_reduced_continuous
#print axioms scalar_reduced_continuous
#check @scalar_interval_integrable
#print axioms scalar_interval_integrable
#check @upper_branch_literal
#print axioms upper_branch_literal
#check @lower_branch_literal
#print axioms lower_branch_literal
#check @source_three_integrals
#print axioms source_three_integrals
#check @initial_branch_formula
#print axioms initial_branch_formula
#check @recurrence_lower_formula
#print axioms recurrence_lower_formula
#check @recurrence_upper_formula
#print axioms recurrence_upper_formula
#check @paper_classical_actual_count
#print axioms paper_classical_actual_count
#check @recurrenceIntegrand
#print axioms recurrenceIntegrand
#check @B_derivative
#print axioms B_derivative
#check @recurrence_one_dimensional
#print axioms recurrence_one_dimensional
#check @coefficient_single_recurrence
#print axioms coefficient_single_recurrence
#check @recurrence_integrand_nonneg
#print axioms recurrence_integrand_nonneg
#check @reducedWeight
#print axioms reducedWeight
#check @reduced_weight_bounds
#print axioms reduced_weight_bounds
#check @reduced_weight_continuous
#print axioms reduced_weight_continuous
#check @scalar_weight_identity
#print axioms scalar_weight_identity
#check @coefficient_error_transport
#print axioms coefficient_error_transport
#check @source_formula_to_fifthMain
#print axioms source_formula_to_fifthMain
#check @source_a_formula_to_fifthMain
#print axioms source_a_formula_to_fifthMain

end
end WuTarget.Wu08FifthSource

import E10FourMajorBudget

namespace WuTarget.E10FourMajor

set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.fixed_geometry_major
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.slope_pos
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.crossCap_pos
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.recipCoeff_pos
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.pairCap_lt_target
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.exp_cubic_remainder
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.reciprocal_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.cross_tangent
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.kernel_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.inner10_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.inner11_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.middle_pair_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.middleTerm_integral
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.outer_pair_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.weighted_amount_identity
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.original_pair_le_moments
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.momentTerm_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.original_pair_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.original_pair_lt_target
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.original_pair_target
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.replacement_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.replacement_strict
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.additionalCredit_lower
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.totalCredit_lower
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.additionalCredit_exact
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.totalCredit_exact
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.no_double_payment
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_relative_first
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_gain_identity
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_gain
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_exact
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_lt_actual
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.actual_pair_upper
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.ordinary_P2_paid
set_option pp.fullNames true in
#check @WuTarget.E10FourMajor.paid_threshold_iff

#print Wu08OriginalFourWeights.original
#print Wu08OriginalFourWeights.original10
#print Wu08OriginalFourWeights.original11
#print WuTarget.E10FourMajor.z0
#print WuTarget.E10FourMajor.slope
#print WuTarget.E10FourMajor.crossCap
#print WuTarget.E10FourMajor.recipCoeff
#print WuTarget.E10FourMajor.capTerm
#print WuTarget.E10FourMajor.pairCap
#print WuTarget.E10FourMajor.replacementCap
#print WuTarget.E10FourMajor.additionalCredit
#print WuTarget.E10FourMajor.totalCredit
#print WuTarget.E10FourMajor.paidCoefficient

#print axioms WuTarget.E10FourMajor.fixed_geometry_major
#print axioms WuTarget.E10FourMajor.slope_pos
#print axioms WuTarget.E10FourMajor.crossCap_pos
#print axioms WuTarget.E10FourMajor.recipCoeff_pos
#print axioms WuTarget.E10FourMajor.pairCap_lt_target
#print axioms WuTarget.E10FourMajor.exp_cubic_remainder
#print axioms WuTarget.E10FourMajor.reciprocal_upper
#print axioms WuTarget.E10FourMajor.cross_tangent
#print axioms WuTarget.E10FourMajor.kernel_upper
#print axioms WuTarget.E10FourMajor.inner10_upper
#print axioms WuTarget.E10FourMajor.inner11_upper
#print axioms WuTarget.E10FourMajor.middle_pair_upper
#print axioms WuTarget.E10FourMajor.middleTerm_integral
#print axioms WuTarget.E10FourMajor.outer_pair_upper
#print axioms WuTarget.E10FourMajor.weighted_amount_identity
#print axioms WuTarget.E10FourMajor.original_pair_le_moments
#print axioms WuTarget.E10FourMajor.momentTerm_upper
#print axioms WuTarget.E10FourMajor.original_pair_upper
#print axioms WuTarget.E10FourMajor.original_pair_lt_target
#print axioms WuTarget.E10FourMajor.original_pair_target
#print axioms WuTarget.E10FourMajor.replacement_upper
#print axioms WuTarget.E10FourMajor.replacement_strict
#print axioms WuTarget.E10FourMajor.additionalCredit_lower
#print axioms WuTarget.E10FourMajor.totalCredit_lower
#print axioms WuTarget.E10FourMajor.additionalCredit_exact
#print axioms WuTarget.E10FourMajor.totalCredit_exact
#print axioms WuTarget.E10FourMajor.no_double_payment
#print axioms WuTarget.E10FourMajor.paid_relative_first
#print axioms WuTarget.E10FourMajor.paid_gain_identity
#print axioms WuTarget.E10FourMajor.paid_gain
#print axioms WuTarget.E10FourMajor.paid_exact
#print axioms WuTarget.E10FourMajor.paid_lt_actual
#print axioms WuTarget.E10FourMajor.actual_pair_upper
#print axioms WuTarget.E10FourMajor.ordinary_P2_paid
#print axioms WuTarget.E10FourMajor.paid_threshold_iff

end WuTarget.E10FourMajor

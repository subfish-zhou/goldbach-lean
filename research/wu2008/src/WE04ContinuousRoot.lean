import WE04ContinuousPayment

namespace WuTarget.E04Continuous

set_option pp.fullNames true
set_option pp.funBinderTypes true
#print WuTarget.E04Continuous.certifiedAmount
#print WuTarget.E04Continuous.netCredit
#print WuTarget.E04Continuous.replacementCoefficient
#print WuTarget.E04Continuous.replacementPaidCoefficient
#print WuTarget.W01Continuous.continuousCoefficient

#check @WuTarget.E04Continuous.first_cell_surplus
#check @WuTarget.E04Continuous.rectangle_geometry
#check @WuTarget.E04Continuous.rectangle_kernel_surplus
#check @WuTarget.E04Continuous.rectangle_volume
#check @WuTarget.E04Continuous.net_integral
#check @WuTarget.E04Continuous.surplus_linear
#check @WuTarget.E04Continuous.enhanced_zero_lower
#check @WuTarget.E04Continuous.enhanced_surplus_linear
#check @WuTarget.E04Continuous.enhanced_surplus_rational
#check @WuTarget.E04Continuous.certifiedAmount_pos
#check @WuTarget.E04Continuous.certifiedAmount_le_netCredit
#check @WuTarget.E04Continuous.netCredit_gt_display
#check @WuTarget.E04Continuous.netCredit_pos
#check @WuTarget.E04Continuous.replacement_identity
#check @WuTarget.E04Continuous.netCredit_identity
#check @WuTarget.E04Continuous.replacement_gain_strict
#check @WuTarget.E04Continuous.replacementPaid_net_identity
#check @WuTarget.E04Continuous.replacementPaid_lt_actual
#check @WuTarget.E04Continuous.enhanced_continuous_Hadm
#check @WuTarget.E04Continuous.enhanced_continuous_ordinary_P2
#check @WuTarget.E04Continuous.replacement_paid_ordinary_P2
#check @WuTarget.E04Continuous.replacement_threshold_iff
#check @WuTarget.E04Continuous.replacement_refined_target

#print axioms WuTarget.E04Continuous.first_cell_surplus
#print axioms WuTarget.E04Continuous.rectangle_geometry
#print axioms WuTarget.E04Continuous.rectangle_kernel_surplus
#print axioms WuTarget.E04Continuous.rectangle_volume
#print axioms WuTarget.E04Continuous.net_integral
#print axioms WuTarget.E04Continuous.surplus_linear
#print axioms WuTarget.E04Continuous.enhanced_zero_lower
#print axioms WuTarget.E04Continuous.enhanced_surplus_linear
#print axioms WuTarget.E04Continuous.enhanced_surplus_rational
#print axioms WuTarget.E04Continuous.certifiedAmount_pos
#print axioms WuTarget.E04Continuous.certifiedAmount_le_netCredit
#print axioms WuTarget.E04Continuous.netCredit_gt_display
#print axioms WuTarget.E04Continuous.netCredit_pos
#print axioms WuTarget.E04Continuous.replacement_identity
#print axioms WuTarget.E04Continuous.netCredit_identity
#print axioms WuTarget.E04Continuous.replacement_gain_strict
#print axioms WuTarget.E04Continuous.replacementPaid_net_identity
#print axioms WuTarget.E04Continuous.replacementPaid_lt_actual
#print axioms WuTarget.E04Continuous.enhanced_continuous_Hadm
#print axioms WuTarget.E04Continuous.enhanced_continuous_ordinary_P2
#print axioms WuTarget.E04Continuous.replacement_paid_ordinary_P2
#print axioms WuTarget.E04Continuous.replacement_threshold_iff
#print axioms WuTarget.E04Continuous.replacement_refined_target

end WuTarget.E04Continuous

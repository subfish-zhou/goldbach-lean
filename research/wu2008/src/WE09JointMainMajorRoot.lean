import WE09JointMainMajorBudget

namespace WuTarget.E09JointMainMajor

set_option pp.fullNames true

#check @lowerLog
#print axioms lowerLog
#check @upperLog
#print axioms upperLog
#check @lower_gap_derivative
#print axioms lower_gap_derivative
#check @upper_gap_derivative
#print axioms upper_gap_derivative
#check @log_lower
#print axioms log_lower
#check @log_upper
#print axioms log_upper
#check @logPayment_le_credit
#print axioms logPayment_le_credit
#check @logPayment_gain
#print axioms logPayment_gain
#check @logPayment
#print axioms logPayment

#check @log_three_upper
#print axioms log_three_upper
#check @log_tangent_quadratic
#print axioms log_tangent_quadratic
#check @curvaturePolynomial
#print axioms curvaturePolynomial
#check @variable_curvature
#print axioms variable_curvature
#check @curvaturePrimitive
#print axioms curvaturePrimitive
#check @curvatureSlope
#print axioms curvatureSlope
#check @curvaturePrimitive_derivative
#print axioms curvaturePrimitive_derivative
#check @curvatureSlope_derivative
#print axioms curvatureSlope_derivative
#check @correctedUpper
#print axioms correctedUpper
#check @correctedDensity
#print axioms correctedDensity
#check @correctedUpper_derivative
#print axioms correctedUpper_derivative
#check @correctedDensity_derivative
#print axioms correctedDensity_derivative
#check @correctedDensity_monotone
#print axioms correctedDensity_monotone
#check @correctedUpper_convex
#print axioms correctedUpper_convex
#check @chordDefect
#print axioms chordDefect
#check @variable_chord_defect
#print axioms variable_chord_defect

#check @upperFour
#print axioms upperFour
#check @upperFive
#print axioms upperFive
#check @upperFour_paid
#print axioms upperFour_paid
#check @upperFive_paid
#print axioms upperFive_paid
#check @middleSurplus
#print axioms middleSurplus
#check @middle_pointwise
#print axioms middle_pointwise
#check @middleGain
#print axioms middleGain
#check @middle_gain_paid
#print axioms middle_gain_paid

#check @polePolynomial
#print axioms polePolynomial
#check @polePrimitive
#print axioms polePrimitive
#check @polePrimitive_zero
#print axioms polePrimitive_zero
#check @polePrimitive_succ
#print axioms polePrimitive_succ
#check @polePrimitive_derivative
#print axioms polePrimitive_derivative
#check @middleCoordinate
#print axioms middleCoordinate
#check @middlePole
#print axioms middlePole
#check @weightedMonomialPrimitive
#print axioms weightedMonomialPrimitive
#check @weightedMonomial_derivative
#print axioms weightedMonomial_derivative
#check @monomialEndpoint
#print axioms monomialEndpoint
#check @weightedMonomial_ftc
#print axioms weightedMonomial_ftc

#check @middleCoefficients
#print axioms middleCoefficients
#check @middle_polynomial
#print axioms middle_polynomial
#check @middleGain_ftc
#print axioms middleGain_ftc
#check @middleLogA
#print axioms middleLogA
#check @middleLogB
#print axioms middleLogB
#check @middleRational
#print axioms middleRational
#check @middle_collection
#print axioms middle_collection
#check @signedLog
#print axioms signedLog
#check @signedLog_le
#print axioms signedLog_le
#check @middlePayment
#print axioms middlePayment
#check @middlePayment_le_gain
#print axioms middlePayment_le_gain
#check @middlePayment_pos
#print axioms middlePayment_pos

#check @log_lower_quadratic
#print axioms log_lower_quadratic
#check @initial_upper_quadratic
#print axioms initial_upper_quadratic
#check @lower_delayed_upper
#print axioms lower_delayed_upper
#check @log_three_cubic
#print axioms log_three_cubic
#check @logThreeCap
#print axioms logThreeCap
#check @highA0
#print axioms highA0
#check @highA1
#print axioms highA1
#check @highA2
#print axioms highA2
#check @highA3
#print axioms highA3
#check @highDensity
#print axioms highDensity
#check @highIncrement
#print axioms highIncrement
#check @logThreeCap_paid
#print axioms logThreeCap_paid
#check @delayed_density_upper
#print axioms delayed_density_upper
#check @highIncrement_derivative
#print axioms highIncrement_derivative
#check @upper_delayed_high
#print axioms upper_delayed_high
#check @highSurplus
#print axioms highSurplus
#check @high_pointwise
#print axioms high_pointwise
#check @highGain
#print axioms highGain
#check @high_gain_paid
#print axioms high_gain_paid

#check @weightedMonomial_high_derivative
#print axioms weightedMonomial_high_derivative
#check @highMonomialEndpoint
#print axioms highMonomialEndpoint
#check @weightedMonomial_high_ftc
#print axioms weightedMonomial_high_ftc
#check @highCoefficients
#print axioms highCoefficients
#check @high_polynomial
#print axioms high_polynomial
#check @highGain_ftc
#print axioms highGain_ftc
#check @highLogA
#print axioms highLogA
#check @highLogB
#print axioms highLogB
#check @highRational
#print axioms highRational
#check @high_collection
#print axioms high_collection
#check @highPayment
#print axioms highPayment
#check @highPayment_le_gain
#print axioms highPayment_le_gain
#check @highPayment_pos
#print axioms highPayment_pos

#check @aggregatePayment
#print axioms aggregatePayment
#check @aggregate_shared_paid
#print axioms aggregate_shared_paid
#check @aggregatePayment_le_actual
#print axioms aggregatePayment_le_actual
#check @aggregate_strict
#print axioms aggregate_strict
#check @aggregate_target
#print axioms aggregate_target

#check @payment
#print axioms payment
#check @netGain
#print axioms netGain
#check @target_lower
#print axioms target_lower
#check @payment_le_actual
#print axioms payment_le_actual
#check @payment_strict
#print axioms payment_strict
#check @netGain_exact
#print axioms netGain_exact
#check @netGain_bounds
#print axioms netGain_bounds
#check @netGain_pos
#print axioms netGain_pos
#check @payment_net
#print axioms payment_net
#check @normalized_net
#print axioms normalized_net
#check @no_double_payment
#print axioms no_double_payment
#check @complete_remaining_identity
#print axioms complete_remaining_identity
#check @remaining_components_nonneg
#print axioms remaining_components_nonneg
#check @selectedCredit
#print axioms selectedCredit
#check @selectedCredit_le_actual
#print axioms selectedCredit_le_actual
#check @previous_selected_le
#print axioms previous_selected_le

#check @new_w11_le_actual_core
#print axioms new_w11_le_actual_core
#check @paidCoefficient
#print axioms paidCoefficient
#check @paid_net
#print axioms paid_net
#check @paid_strict
#print axioms paid_strict
#check @paid_exact
#print axioms paid_exact
#check @paid_lt_actual
#print axioms paid_lt_actual
#check @ordinary_P2_paid
#print axioms ordinary_P2_paid
#check @ordinary_P2
#print axioms ordinary_P2

#print payment
#print netGain
#print aggregatePayment
#print paidCoefficient

end WuTarget.E09JointMainMajor

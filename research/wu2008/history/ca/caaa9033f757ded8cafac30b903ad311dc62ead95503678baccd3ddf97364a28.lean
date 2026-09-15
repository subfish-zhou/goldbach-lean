import SrcFifthGainRoot
import SrcFifthGainAnalyticActual

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve
set_option pp.fullNames true

#print denominator
#print lowerSlope
#print upperSlope
#print lowerMass
#print upperMass
#print analyticMass
#print weightNumerator
#print rationalWeight
#print realWeight
#print rationalGain
#print massGain

#check @log_ratio_lower
#print axioms log_ratio_lower
#check @parameter_bounds
#print axioms parameter_bounds
#check @denominator_pos
#print axioms denominator_pos
#check @denominator_antitone
#print axioms denominator_antitone
#check @low_log_lower
#print axioms low_log_lower
#check @high_log_lower
#print axioms high_log_lower
#check @lower_envelope
#print axioms lower_envelope
#check @upper_envelope
#print axioms upper_envelope
#check @linear_left_integral
#print axioms linear_left_integral
#check @linear_right_integral
#print axioms linear_right_integral
#check @lower_mass_le
#print axioms lower_mass_le
#check @upper_mass_le
#print axioms upper_mass_le
#check @analytic_mass_le
#print axioms analytic_mass_le
#check @rational_weight_pos
#print axioms rational_weight_pos
#check @rational_weight_le_mass
#print axioms rational_weight_le_mass
#check @thirteen_rational_weights
#print axioms thirteen_rational_weights
#check @thirteen_positive_weights
#print axioms thirteen_positive_weights
#check @thirteen_original_indices
#print axioms thirteen_original_indices
#check @first_rational_weight
#print axioms first_rational_weight
#check @crossing_rational_weight
#print axioms crossing_rational_weight
#check @last_rational_weight
#print axioms last_rational_weight
#check @rational_gain_literal
#print axioms rational_gain_literal
#check @rational_gain_le_mass
#print axioms rational_gain_le_mass
#check @mass_gain_le_grid
#print axioms mass_gain_le_grid
#check @rational_gain_le_grid
#print axioms rational_gain_le_grid
#check @rational_gain_nonneg
#print axioms rational_gain_nonneg
#check @rational_gain_source
#print axioms rational_gain_source
#check @rational_gain_moving
#print axioms rational_gain_moving
#check @mass_gain_count
#print axioms mass_gain_count
#check @rational_gain_count
#print axioms rational_gain_count
#check @parameter_nodes_count
#print axioms parameter_nodes_count
#check @rational_gain_replaces_fixed
#print axioms rational_gain_replaces_fixed
#check @actual_nodes_nonneg
#print axioms actual_nodes_nonneg
#check @actual_rational_source
#print axioms actual_rational_source
#check @actual_mass_source
#print axioms actual_mass_source
#check @actual_rational_count
#print axioms actual_rational_count

#print WuSource.SrcFifthGain.cellWeight
#print WuSource.SrcFifthGain.sourceGain
#print WuSource.SrcFifthGain.sourceKernel
#print WuSource.SrcFifthGain.weight
#check @WuSource.SrcFifthGain.cell_weight_cross
#print axioms WuSource.SrcFifthGain.cell_weight_cross
#check @WuSource.SrcFifthGain.certified_g5_count
#print axioms WuSource.SrcFifthGain.certified_g5_count
#check @WuTarget.E09JointMainMajor.log_lower
#print axioms WuTarget.E09JointMainMajor.log_lower
#check @fifthH_actual_Fdelta_lower
#print axioms fifthH_actual_Fdelta_lower
#print wuImprovementLimit
#print fifthPairCount

end WuSource.SrcFifthGain.Analytic

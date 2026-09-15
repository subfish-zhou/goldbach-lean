import WSrcFifthGainSource
import WSrcFifthGainSmallDelta

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve
set_option pp.fullNames true

#print sourceKernel
#print sourceGain
#print profileKernel
#print triangleGain
#print weight
#print scalarGain
#print lowerWeight
#print upperWeight
#print node
#print cellLower
#print cellUpper
#print cell
#print cellWeight
#print staircase
#print gridGain
#print directedGain

#check @triangle_parameter
#print axioms triangle_parameter
#check @parameter_in_core
#print axioms parameter_in_core
#check @zero_denominator_pos
#print axioms zero_denominator_pos
#check @profile_kernel_measurable
#print axioms profile_kernel_measurable
#check @profile_kernel_integrable
#print axioms profile_kernel_integrable
#check @profile_kernel_le_actual
#print axioms profile_kernel_le_actual
#check @triangle_gain_uniform
#print axioms triangle_gain_uniform
#check @profile_count
#print axioms profile_count
#check @source_inner_substitution
#print axioms source_inner_substitution
#check @triangle_outer
#print axioms triangle_outer
#check @source_eq_triangle
#print axioms source_eq_triangle
#check @sheared_inner
#print axioms sheared_inner
#check @triangle_reduced
#print axioms triangle_reduced
#check @source_eq_scalar
#print axioms source_eq_scalar
#check @source_profile_count
#print axioms source_profile_count
#check @weight_bounds
#print axioms weight_bounds
#check @weight_continuous
#print axioms weight_continuous
#check @weight_integrable
#print axioms weight_integrable
#check @weight_integrable_sub
#print axioms weight_integrable_sub
#check @weight_lower
#print axioms weight_lower
#check @weight_upper
#print axioms weight_upper
#check @lower_integral_literal
#print axioms lower_integral_literal
#check @upper_integral_literal
#print axioms upper_integral_literal
#check @weight_integral_nonneg
#print axioms weight_integral_nonneg
#check @weight_integral_directed
#print axioms weight_integral_directed
#check @cell_geometry
#print axioms cell_geometry
#check @cell_edges
#print axioms cell_edges
#check @adjacent_cover
#print axioms adjacent_cover
#check @thirteen_cell_cover
#print axioms thirteen_cell_cover
#check @cells_ordered
#print axioms cells_ordered
#check @cell_unique
#print axioms cell_unique
#check @first_cell
#print axioms first_cell
#check @last_cell
#print axioms last_cell
#check @cross_cell
#print axioms cross_cell
#check @cell_weight_nonneg
#print axioms cell_weight_nonneg
#check @cell_weight_integrable
#print axioms cell_weight_integrable
#check @cell_weight_first
#print axioms cell_weight_first
#check @cell_weight_lower
#print axioms cell_weight_lower
#check @cell_weight_cross
#print axioms cell_weight_cross
#check @cell_weight_upper
#print axioms cell_weight_upper
#check @cell_weight_last
#print axioms cell_weight_last
#check @staircase_measurable
#print axioms staircase_measurable
#check @staircase_bound
#print axioms staircase_bound
#check @staircase_kernel_integrable
#print axioms staircase_kernel_integrable
#check @staircase_nonneg
#print axioms staircase_nonneg
#check @staircase_on_cell
#print axioms staircase_on_cell
#check @staircase_off_cells
#print axioms staircase_off_cells
#check @staircase_le_actual
#print axioms staircase_le_actual
#check @weighted_cell_integrable
#print axioms weighted_cell_integrable
#check @weighted_cell_integral
#print axioms weighted_cell_integral
#check @scalar_staircase_eq_grid
#print axioms scalar_staircase_eq_grid
#check @source_staircase_eq_grid
#print axioms source_staircase_eq_grid
#check @grid_gain_uniform
#print axioms grid_gain_uniform
#check @directed_gain_le_grid
#print axioms directed_gain_le_grid
#check @grid_count
#print axioms grid_count
#check @directed_threshold_count
#print axioms directed_threshold_count
#check @actual_kernel_integrable
#print axioms actual_kernel_integrable
#check @actual_source_scalar
#print axioms actual_source_scalar
#check @actual_source_le_moving
#print axioms actual_source_le_moving
#check @grid_le_actual_source
#print axioms grid_le_actual_source
#check @original_h_thirteen_nodes
#print axioms original_h_thirteen_nodes
#check @actual_source_count
#print axioms actual_source_count
#check @suggested_threshold_count
#print axioms suggested_threshold_count
#check @weighted_profile_integrable
#print axioms weighted_profile_integrable
#check @source_two_branches
#print axioms source_two_branches
#check @actual_weighted_integrable
#print axioms actual_weighted_integrable
#check @actual_source_two_branches
#print axioms actual_source_two_branches
#check @grid_original_indices
#print axioms grid_original_indices
#check @cell_weight_directed
#print axioms cell_weight_directed
#check @cell_weight_error_lower
#print axioms cell_weight_error_lower
#check @fifth_delta_close_below
#print axioms fifth_delta_close_below
#check @grid_count_below
#print axioms grid_count_below
#check @certified_g5_count
#print axioms certified_g5_count
#check @replacement_coefficient
#print axioms replacement_coefficient
#check @replacement_quarter
#print axioms replacement_quarter

#print wuImprovementLimit
#print wuImprovementAtInfinity
#print wuEventualImprovements
#print wuAdmissibleImprovements
#print wuBoxPhi
#print convolutionSieveCount
#print sourceSieveCount
#print sourceSieveCarrier
#print fifthPairRegion
#print truncatedSixthLowerS
#print truncatedSixthLowerC
#print fifthHOnlyKernel
#print fifthHOnlyIntegral
#print fifthPairCount
#print PositiveCoreResume.fifthProfile
#print PositiveCoreResume.fifthGain
#check @fifthH_actual_Fdelta_lower
#print axioms fifthH_actual_Fdelta_lower
#check @fifthH_actual_integral_split
#print axioms fifthH_actual_integral_split
#check @fifthPair_Fdelta_right_limit
#print axioms fifthPair_Fdelta_right_limit
#check @wuImprovementLimit_lower_antitone
#print axioms wuImprovementLimit_lower_antitone

end WuSource.SrcFifthGain

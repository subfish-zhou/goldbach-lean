import WSrcFifthGainSource
import WSrcFifthGainSmallDelta

namespace WuPaper.RMapMFifth

set_option pp.fullNames true

#check @WuTarget.Wu08FifthSource.parameters_exact
#print axioms WuTarget.Wu08FifthSource.parameters_exact
#check @WuTarget.Wu08FifthSource.parameter_range
#print axioms WuTarget.Wu08FifthSource.parameter_range
#check @WuTarget.Wu08FifthSource.coefficient_initial
#print axioms WuTarget.Wu08FifthSource.coefficient_initial
#check @WuTarget.Wu08FifthSource.coefficient_recurrence
#print axioms WuTarget.Wu08FifthSource.coefficient_recurrence
#check @WuTarget.Wu08FifthSource.paper_classical_eq_fifthMain
#print axioms WuTarget.Wu08FifthSource.paper_classical_eq_fifthMain
#check @WuTarget.Wu08FifthSource.source_three_integrals
#print axioms WuTarget.Wu08FifthSource.source_three_integrals
#check @WuTarget.Wu08FifthSource.coefficient_error_transport
#print axioms WuTarget.Wu08FifthSource.coefficient_error_transport
#check @WuTarget.Wu08FifthSource.fixed_breakpoints
#print axioms WuTarget.Wu08FifthSource.fixed_breakpoints
#check @WuTarget.Wu08FifthSource.B_derivative
#print axioms WuTarget.Wu08FifthSource.B_derivative
#check @WuTarget.Wu08OriginalFirstSteps.k_continuous
#print axioms WuTarget.Wu08OriginalFirstSteps.k_continuous
#check @WuSource.SrcFifthGain.source_inner_substitution
#print axioms WuSource.SrcFifthGain.source_inner_substitution
#check @WuSource.SrcFifthGain.source_eq_scalar
#print axioms WuSource.SrcFifthGain.source_eq_scalar
#check @WuSource.SrcFifthGain.source_two_branches
#print axioms WuSource.SrcFifthGain.source_two_branches
#check @WuSource.SrcFifthGain.thirteen_cell_cover
#print axioms WuSource.SrcFifthGain.thirteen_cell_cover
#check @WuSource.SrcFifthGain.cell_weight_first
#print axioms WuSource.SrcFifthGain.cell_weight_first
#check @WuSource.SrcFifthGain.cell_weight_lower
#print axioms WuSource.SrcFifthGain.cell_weight_lower
#check @WuSource.SrcFifthGain.cell_weight_cross
#print axioms WuSource.SrcFifthGain.cell_weight_cross
#check @WuSource.SrcFifthGain.cell_weight_upper
#print axioms WuSource.SrcFifthGain.cell_weight_upper
#check @WuSource.SrcFifthGain.cell_weight_last
#print axioms WuSource.SrcFifthGain.cell_weight_last
#check @WuSource.SrcFifthGain.actual_source_two_branches
#print axioms WuSource.SrcFifthGain.actual_source_two_branches
#check @WuSource.SrcFifthGain.original_h_thirteen_nodes
#print axioms WuSource.SrcFifthGain.original_h_thirteen_nodes
#check @WuSource.SrcFifthGain.grid_original_indices
#print axioms WuSource.SrcFifthGain.grid_original_indices
#check @WuSource.SrcFifthGain.cell_weight_error_lower
#print axioms WuSource.SrcFifthGain.cell_weight_error_lower
#check @WuSource.SrcFifthGain.certified_g5_count
#print axioms WuSource.SrcFifthGain.certified_g5_count

end WuPaper.RMapMFifth

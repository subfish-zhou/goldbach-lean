import RMapMSixthErrors
import RMapMSixthGainCells

noncomputable section
namespace WuPaper.RMapMSixth
open Real Set MeasureTheory QuarterTrim Wu2008DoubleSieve NodeExtension
open WuSource.SrcSixthGain
open scoped Interval BigOperators

theorem original_sixth_analytic_lower {w : Fin 21 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    Wu08TerminalAlignment.sixthMain+8*(∑ j : Fin 21, g6Weight j*w j) ≤
      paperC6 wuLowerCoefficient+paperG6 (wuImprovementLimit false delta) := by
  have h := g6_twentyone_chain hd hdhi hw
  rw [c6_eq_existing_classical]
  exact add_le_add le_rfl (h.1.trans h.2)

#check @original_sixth_analytic_lower
#print axioms original_sixth_analytic_lower

#check @c6_domain_iff
#check @c6_parameter_range
#check @c6_a_eq
#check @c6_literal_complete
#check @c6_eq_existing_classical
#check @c6_actual_inner_integrable
#check @c6_actual_outer_integrable
#check @c6_layered_lower
#check @g6_raw_density_integral
#check @g6_original_reduced_split
#check @g6_original_reduced_le_whole
#check @g6_kernel_nonnegative
#check @g6_cells_cover
#check @g6_twentyone_chain
#check @g6_directed_weight_node_errors
#check @g6_fifteenth_error
#print axioms c6_domain_iff
#print axioms c6_parameter_range
#print axioms c6_a_eq
#print axioms c6_literal_complete
#print axioms c6_eq_existing_classical
#print axioms c6_actual_inner_integrable
#print axioms c6_actual_outer_integrable
#print axioms c6_layered_lower
#print axioms g6_raw_density_integral
#print axioms g6_original_reduced_split
#print axioms g6_original_reduced_le_whole
#print axioms g6_kernel_nonnegative
#print axioms g6_cells_cover
#print axioms g6_twentyone_chain
#print axioms g6_directed_weight_node_errors
#print axioms g6_fifteenth_error

#check @WuSource.SrcSixthGain.paperG6
#check @WuSource.SrcSixthGain.paper_eq_rectangles
#check @WuSource.SrcSixthGain.source_reduced_domain
#check @WuSource.SrcSixthGain.breakpoints
#check @WuSource.SrcSixthGain.lowerKernel
#check @WuSource.SrcSixthGain.upperKernel
#check @WuSource.SrcSixthGain.cell_intersection
#check @WuSource.SrcSixthGain.weight_nonneg
#check @WuSource.SrcSixthGain.first_fourteen
#check @WuSource.SrcSixthGain.fifteenth_crossing
#check @WuSource.SrcSixthGain.middle_five
#check @WuSource.SrcSixthGain.last_truncated
#check @WuSource.SrcSixthGain.original_reduced_lower
#check @WuSource.SrcSixthGain.original_whole_source_lower
#check @Wu2008DoubleSieve.truncatedSixthZeroDelta_full_rectangle
#check @WuTarget.Wu08FifthSource.coefficient_initial
#check @WuTarget.Wu08FifthSource.coefficient_recurrence
#print axioms WuSource.SrcSixthGain.paperG6
#print axioms WuSource.SrcSixthGain.paper_eq_rectangles
#print axioms WuSource.SrcSixthGain.source_reduced_domain
#print axioms WuSource.SrcSixthGain.breakpoints
#print axioms WuSource.SrcSixthGain.lowerKernel
#print axioms WuSource.SrcSixthGain.upperKernel
#print axioms WuSource.SrcSixthGain.cell_intersection
#print axioms WuSource.SrcSixthGain.weight_nonneg
#print axioms WuSource.SrcSixthGain.first_fourteen
#print axioms WuSource.SrcSixthGain.fifteenth_crossing
#print axioms WuSource.SrcSixthGain.middle_five
#print axioms WuSource.SrcSixthGain.last_truncated
#print axioms WuSource.SrcSixthGain.original_reduced_lower
#print axioms WuSource.SrcSixthGain.original_whole_source_lower
#print axioms Wu2008DoubleSieve.truncatedSixthZeroDelta_full_rectangle
#print axioms WuTarget.Wu08FifthSource.coefficient_initial
#print axioms WuTarget.Wu08FifthSource.coefficient_recurrence
end WuPaper.RMapMSixth

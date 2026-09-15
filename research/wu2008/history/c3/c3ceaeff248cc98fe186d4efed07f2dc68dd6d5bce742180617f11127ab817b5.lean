import SrcFourEnclosureResult

namespace WuSource.SrcFourEnclosure

theorem exact_budget_comparison :
    (7/10 : ℝ)-851/1250 = 12/625 ∧
      ((7/10 : ℝ)-851/1250)/4 = 3/625 ∧
      ((851/1250 : ℝ)-648163/1000000)/4 = 32637/4000000 := by norm_num

set_option pp.fullNames true

#check @SrcFour.original_pair_source
#check @SrcFour.ten_complement_empty
#check @SrcFour.eleven_complement_location
#check @SrcFour.eleven_complement_nonempty
#check @merged_parameter
#check @original_pair_uniform
#check @G_derivative
#check @H_derivative
#check @mass_one_dimensional
#check @small_derivatives
#check @large_derivatives
#check @cell_coverage
#check @midpoint_coverage
#check @mass_midpoint_enclosure
#check @small_node_enclosure
#check @large_node_enclosure
#check @small_certificate
#check @large_certificate
#check @mass_package_enclosure
#check @massLower_exact
#check @massUpper_exact
#check @mass_rational_enclosure
#check @tailGeom_upper
#check @original_pair_mass_tail
#check @SrcBuchstab.buchstab_le_source_fine
#check @original_pair_upper
#check @original_pair_lower56
#check @original_pair_conditional_enclosure
#check @enclosure_width
#check @original_pair_unconditional_enclosure
#check @printedPair_exact
#check @printed_gap_upper
#check @printed_gap_conditional
#check @printed_pair_not_upper_conditional
#check @actual_pair_upper
#check @enclosedCoefficient_exact
#check @ordinary_P2_enclosed
#check @exact_budget_comparison

#print Wu08OriginalFourWeights.original
#print Wu08OriginalFourWeights.original10
#print Wu08OriginalFourWeights.original11
#print clamp
#print cross
#print density
#print G
#print H
#print outerMass
#print mass
#print smallW
#print smallQ
#print largeW
#print largeQ
#print smallF
#print largeF
#print point
#print midpoint
#print midpointSum
#print error
#print logLo
#print logHi
#print massLower
#print massUpper
#print tailGeom
#print printedPair
#print enclosedCoefficient

#print axioms SrcFour.original_pair_source
#print axioms SrcFour.ten_complement_empty
#print axioms SrcFour.eleven_complement_location
#print axioms SrcFour.eleven_complement_nonempty
#print axioms merged_parameter
#print axioms original_pair_uniform
#print axioms G_derivative
#print axioms H_derivative
#print axioms mass_one_dimensional
#print axioms small_derivatives
#print axioms large_derivatives
#print axioms cell_coverage
#print axioms midpoint_coverage
#print axioms mass_midpoint_enclosure
#print axioms small_node_enclosure
#print axioms large_node_enclosure
#print axioms small_certificate
#print axioms large_certificate
#print axioms mass_package_enclosure
#print axioms massLower_exact
#print axioms massUpper_exact
#print axioms mass_rational_enclosure
#print axioms tailGeom_upper
#print axioms original_pair_mass_tail
#print axioms SrcBuchstab.buchstab_le_source_fine
#print axioms original_pair_upper
#print axioms original_pair_lower56
#print axioms original_pair_conditional_enclosure
#print axioms enclosure_width
#print axioms original_pair_unconditional_enclosure
#print axioms printedPair_exact
#print axioms printed_gap_upper
#print axioms printed_gap_conditional
#print axioms printed_pair_not_upper_conditional
#print axioms actual_pair_upper
#print axioms enclosedCoefficient_exact
#print axioms ordinary_P2_enclosed
#print axioms exact_budget_comparison

end WuSource.SrcFourEnclosure

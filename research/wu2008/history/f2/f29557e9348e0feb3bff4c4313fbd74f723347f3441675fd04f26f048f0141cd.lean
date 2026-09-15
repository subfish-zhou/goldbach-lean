import WSourceRevisedClosureBudget

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.deepTerms true

#check @WuSource.SrcFourEnclosure.clamp
#print axioms WuSource.SrcFourEnclosure.clamp
#check @WuSource.SrcFourEnclosure.cross
#print axioms WuSource.SrcFourEnclosure.cross
#check @WuSource.SrcFourEnclosure.density
#print axioms WuSource.SrcFourEnclosure.density
#check @WuSource.SrcFourEnclosure.G
#print axioms WuSource.SrcFourEnclosure.G
#check @WuSource.SrcFourEnclosure.H
#print axioms WuSource.SrcFourEnclosure.H
#check @WuSource.SrcFourEnclosure.outerMass
#print axioms WuSource.SrcFourEnclosure.outerMass
#check @WuSource.SrcFourEnclosure.mass
#print axioms WuSource.SrcFourEnclosure.mass
#check @WuSource.SrcFourEnclosure.geometry
#print axioms WuSource.SrcFourEnclosure.geometry
#check @WuSource.SrcFourEnclosure.clamp_mem
#print axioms WuSource.SrcFourEnclosure.clamp_mem
#check @WuSource.SrcFourEnclosure.clamp_eq
#print axioms WuSource.SrcFourEnclosure.clamp_eq
#check @WuSource.SrcFourEnclosure.clamp_pos
#print axioms WuSource.SrcFourEnclosure.clamp_pos
#check @WuSource.SrcFourEnclosure.clamp_continuous
#print axioms WuSource.SrcFourEnclosure.clamp_continuous
#check @WuSource.SrcFourEnclosure.density_continuous
#print axioms WuSource.SrcFourEnclosure.density_continuous
#check @WuSource.SrcFourEnclosure.density_eq
#print axioms WuSource.SrcFourEnclosure.density_eq
#check @WuSource.SrcFourEnclosure.G_derivative
#print axioms WuSource.SrcFourEnclosure.G_derivative
#check @WuSource.SrcFourEnclosure.G_continuous
#print axioms WuSource.SrcFourEnclosure.G_continuous
#check @WuSource.SrcFourEnclosure.H_integrand_continuous
#print axioms WuSource.SrcFourEnclosure.H_integrand_continuous
#check @WuSource.SrcFourEnclosure.H_derivative
#print axioms WuSource.SrcFourEnclosure.H_derivative
#check @WuSource.SrcFourEnclosure.H_continuous
#print axioms WuSource.SrcFourEnclosure.H_continuous
#check @WuSource.SrcFourEnclosure.outerMass_continuous
#print axioms WuSource.SrcFourEnclosure.outerMass_continuous
#check @WuSource.SrcFourEnclosure.cross_nonneg
#print axioms WuSource.SrcFourEnclosure.cross_nonneg
#check @WuSource.SrcFourEnclosure.density_nonneg
#print axioms WuSource.SrcFourEnclosure.density_nonneg
#check @WuSource.SrcFourEnclosure.G_nonneg
#print axioms WuSource.SrcFourEnclosure.G_nonneg
#check @WuSource.SrcFourEnclosure.H_nonneg
#print axioms WuSource.SrcFourEnclosure.H_nonneg
#check @WuSource.SrcFourEnclosure.outerMass_nonneg
#print axioms WuSource.SrcFourEnclosure.outerMass_nonneg
#check @WuSource.SrcFourEnclosure.mass_nonneg
#print axioms WuSource.SrcFourEnclosure.mass_nonneg
#check @WuSource.SrcFourEnclosure.merged_kernel_bounds
#print axioms WuSource.SrcFourEnclosure.merged_kernel_bounds
#check @WuSource.SrcFourEnclosure.merged_parameter
#print axioms WuSource.SrcFourEnclosure.merged_parameter
#check @WuSource.SrcFourEnclosure.inner_bounds
#print axioms WuSource.SrcFourEnclosure.inner_bounds
#check @WuSource.SrcFourEnclosure.middle_bounds
#print axioms WuSource.SrcFourEnclosure.middle_bounds
#check @WuSource.SrcFourEnclosure.outer_bounds
#print axioms WuSource.SrcFourEnclosure.outer_bounds
#check @WuSource.SrcFourEnclosure.weighted_mono
#print axioms WuSource.SrcFourEnclosure.weighted_mono
#check @WuSource.SrcFourEnclosure.original_const_mul
#print axioms WuSource.SrcFourEnclosure.original_const_mul
#check @WuSource.SrcFourEnclosure.original_pair_add
#print axioms WuSource.SrcFourEnclosure.original_pair_add
#check @WuSource.SrcFourEnclosure.original_pair_uniform
#print axioms WuSource.SrcFourEnclosure.original_pair_uniform
#check @WuSource.SrcFourEnclosure.original_pair_lower
#print axioms WuSource.SrcFourEnclosure.original_pair_lower
#check @WuSource.SrcFourEnclosure.cut
#print axioms WuSource.SrcFourEnclosure.cut
#check @WuSource.SrcFourEnclosure.smallW
#print axioms WuSource.SrcFourEnclosure.smallW
#check @WuSource.SrcFourEnclosure.smallQ
#print axioms WuSource.SrcFourEnclosure.smallQ
#check @WuSource.SrcFourEnclosure.largeW
#print axioms WuSource.SrcFourEnclosure.largeW
#check @WuSource.SrcFourEnclosure.largeQ
#print axioms WuSource.SrcFourEnclosure.largeQ
#check @WuSource.SrcFourEnclosure.smallF
#print axioms WuSource.SrcFourEnclosure.smallF
#check @WuSource.SrcFourEnclosure.largeF
#print axioms WuSource.SrcFourEnclosure.largeF
#check @WuSource.SrcFourEnclosure.smallW_derivative
#print axioms WuSource.SrcFourEnclosure.smallW_derivative
#check @WuSource.SrcFourEnclosure.smallQ_derivative
#print axioms WuSource.SrcFourEnclosure.smallQ_derivative
#check @WuSource.SrcFourEnclosure.largeW_derivative
#print axioms WuSource.SrcFourEnclosure.largeW_derivative
#check @WuSource.SrcFourEnclosure.largeQ_derivative
#print axioms WuSource.SrcFourEnclosure.largeQ_derivative
#check @WuSource.SrcFourEnclosure.primitives_boundary
#print axioms WuSource.SrcFourEnclosure.primitives_boundary
#check @WuSource.SrcFourEnclosure.reduction_piece
#print axioms WuSource.SrcFourEnclosure.reduction_piece
#check @WuSource.SrcFourEnclosure.mass_one_dimensional
#print axioms WuSource.SrcFourEnclosure.mass_one_dimensional
#check @WuSource.SrcFourEnclosure.endpoint_logs
#print axioms WuSource.SrcFourEnclosure.endpoint_logs
#check @WuSource.SrcFourEnclosure.monotone_of_derivative
#print axioms WuSource.SrcFourEnclosure.monotone_of_derivative
#check @WuSource.SrcFourEnclosure.smallW_mono
#print axioms WuSource.SrcFourEnclosure.smallW_mono
#check @WuSource.SrcFourEnclosure.largeW_mono
#print axioms WuSource.SrcFourEnclosure.largeW_mono
#check @WuSource.SrcFourEnclosure.W_bounds
#print axioms WuSource.SrcFourEnclosure.W_bounds
#check @WuSource.SrcFourEnclosure.smallQ_mono
#print axioms WuSource.SrcFourEnclosure.smallQ_mono
#check @WuSource.SrcFourEnclosure.largeQ_mono
#print axioms WuSource.SrcFourEnclosure.largeQ_mono
#check @WuSource.SrcFourEnclosure.Q_bounds
#print axioms WuSource.SrcFourEnclosure.Q_bounds
#check @WuSource.SrcFourEnclosure.elementary_bounds
#print axioms WuSource.SrcFourEnclosure.elementary_bounds
#check @WuSource.SrcFourEnclosure.w_bounds
#print axioms WuSource.SrcFourEnclosure.w_bounds
#check @WuSource.SrcFourEnclosure.D
#print axioms WuSource.SrcFourEnclosure.D
#check @WuSource.SrcFourEnclosure.D1
#print axioms WuSource.SrcFourEnclosure.D1
#check @WuSource.SrcFourEnclosure.D2
#print axioms WuSource.SrcFourEnclosure.D2
#check @WuSource.SrcFourEnclosure.F1
#print axioms WuSource.SrcFourEnclosure.F1
#check @WuSource.SrcFourEnclosure.F2
#print axioms WuSource.SrcFourEnclosure.F2
#check @WuSource.SrcFourEnclosure.cross_derivative
#print axioms WuSource.SrcFourEnclosure.cross_derivative
#check @WuSource.SrcFourEnclosure.D_derivative
#print axioms WuSource.SrcFourEnclosure.D_derivative
#check @WuSource.SrcFourEnclosure.D1_derivative
#print axioms WuSource.SrcFourEnclosure.D1_derivative
#check @WuSource.SrcFourEnclosure.F_derivative
#print axioms WuSource.SrcFourEnclosure.F_derivative
#check @WuSource.SrcFourEnclosure.F1_derivative
#print axioms WuSource.SrcFourEnclosure.F1_derivative
#check @WuSource.SrcFourEnclosure.D_bounds
#print axioms WuSource.SrcFourEnclosure.D_bounds
#check @WuSource.SrcFourEnclosure.F2_bound
#print axioms WuSource.SrcFourEnclosure.F2_bound
#check @WuSource.SrcFourEnclosure.small_derivatives
#print axioms WuSource.SrcFourEnclosure.small_derivatives
#check @WuSource.SrcFourEnclosure.large_derivatives
#print axioms WuSource.SrcFourEnclosure.large_derivatives
#check @WuSource.SrcFourEnclosure.minimum_of_second
#print axioms WuSource.SrcFourEnclosure.minimum_of_second
#check @WuSource.SrcFourEnclosure.taylor_two_sided
#print axioms WuSource.SrcFourEnclosure.taylor_two_sided
#check @WuSource.SrcFourEnclosure.polynomial_integral
#print axioms WuSource.SrcFourEnclosure.polynomial_integral
#check @WuSource.SrcFourEnclosure.midpoint_cell
#print axioms WuSource.SrcFourEnclosure.midpoint_cell
#check @WuSource.SrcFourEnclosure.point
#print axioms WuSource.SrcFourEnclosure.point
#check @WuSource.SrcFourEnclosure.midpoint
#print axioms WuSource.SrcFourEnclosure.midpoint
#check @WuSource.SrcFourEnclosure.midpointSum
#print axioms WuSource.SrcFourEnclosure.midpointSum
#check @WuSource.SrcFourEnclosure.error
#print axioms WuSource.SrcFourEnclosure.error
#check @WuSource.SrcFourEnclosure.cell_coverage
#print axioms WuSource.SrcFourEnclosure.cell_coverage
#check @WuSource.SrcFourEnclosure.midpoint_coverage
#print axioms WuSource.SrcFourEnclosure.midpoint_coverage
#check @WuSource.SrcFourEnclosure.midpoint_64
#print axioms WuSource.SrcFourEnclosure.midpoint_64
#check @WuSource.SrcFourEnclosure.mass_midpoint_enclosure
#print axioms WuSource.SrcFourEnclosure.mass_midpoint_enclosure
#check @WuSource.SrcFourEnclosure.logLo
#print axioms WuSource.SrcFourEnclosure.logLo
#check @WuSource.SrcFourEnclosure.logHi
#print axioms WuSource.SrcFourEnclosure.logHi
#check @WuSource.SrcFourEnclosure.log_bounds
#print axioms WuSource.SrcFourEnclosure.log_bounds
#check @WuSource.SrcFourEnclosure.smallWLo
#print axioms WuSource.SrcFourEnclosure.smallWLo
#check @WuSource.SrcFourEnclosure.smallWHi
#print axioms WuSource.SrcFourEnclosure.smallWHi
#check @WuSource.SrcFourEnclosure.smallQLo
#print axioms WuSource.SrcFourEnclosure.smallQLo
#check @WuSource.SrcFourEnclosure.smallQHi
#print axioms WuSource.SrcFourEnclosure.smallQHi
#check @WuSource.SrcFourEnclosure.largeQLo
#print axioms WuSource.SrcFourEnclosure.largeQLo
#check @WuSource.SrcFourEnclosure.largeQHi
#print axioms WuSource.SrcFourEnclosure.largeQHi
#check @WuSource.SrcFourEnclosure.smallLo
#print axioms WuSource.SrcFourEnclosure.smallLo
#check @WuSource.SrcFourEnclosure.smallHi
#print axioms WuSource.SrcFourEnclosure.smallHi
#check @WuSource.SrcFourEnclosure.largeLo
#print axioms WuSource.SrcFourEnclosure.largeLo
#check @WuSource.SrcFourEnclosure.largeHi
#print axioms WuSource.SrcFourEnclosure.largeHi
#check @WuSource.SrcFourEnclosure.smallW_log_bounds
#print axioms WuSource.SrcFourEnclosure.smallW_log_bounds
#check @WuSource.SrcFourEnclosure.smallQ_log_bounds
#print axioms WuSource.SrcFourEnclosure.smallQ_log_bounds
#check @WuSource.SrcFourEnclosure.largeQ_formula
#print axioms WuSource.SrcFourEnclosure.largeQ_formula
#check @WuSource.SrcFourEnclosure.largeQ_log_bounds
#print axioms WuSource.SrcFourEnclosure.largeQ_log_bounds
#check @WuSource.SrcFourEnclosure.cross_log_bounds
#print axioms WuSource.SrcFourEnclosure.cross_log_bounds
#check @WuSource.SrcFourEnclosure.small_node_enclosure
#print axioms WuSource.SrcFourEnclosure.small_node_enclosure
#check @WuSource.SrcFourEnclosure.large_node_enclosure
#print axioms WuSource.SrcFourEnclosure.large_node_enclosure
#check @WuSource.SrcFourEnclosure.mass_rational_sums
#print axioms WuSource.SrcFourEnclosure.mass_rational_sums
#check @WuSource.SrcFourEnclosure.smallLower
#print axioms WuSource.SrcFourEnclosure.smallLower
#check @WuSource.SrcFourEnclosure.smallUpper
#print axioms WuSource.SrcFourEnclosure.smallUpper
#check @WuSource.SrcFourEnclosure.largeLower
#print axioms WuSource.SrcFourEnclosure.largeLower
#check @WuSource.SrcFourEnclosure.largeUpper
#print axioms WuSource.SrcFourEnclosure.largeUpper
#check @WuSource.SrcFourEnclosure.cell_small_00
#print axioms WuSource.SrcFourEnclosure.cell_small_00
#check @WuSource.SrcFourEnclosure.cell_small_01
#print axioms WuSource.SrcFourEnclosure.cell_small_01
#check @WuSource.SrcFourEnclosure.cell_small_02
#print axioms WuSource.SrcFourEnclosure.cell_small_02
#check @WuSource.SrcFourEnclosure.cell_small_03
#print axioms WuSource.SrcFourEnclosure.cell_small_03
#check @WuSource.SrcFourEnclosure.cell_small_04
#print axioms WuSource.SrcFourEnclosure.cell_small_04
#check @WuSource.SrcFourEnclosure.cell_small_05
#print axioms WuSource.SrcFourEnclosure.cell_small_05
#check @WuSource.SrcFourEnclosure.cell_small_06
#print axioms WuSource.SrcFourEnclosure.cell_small_06
#check @WuSource.SrcFourEnclosure.cell_small_07
#print axioms WuSource.SrcFourEnclosure.cell_small_07
#check @WuSource.SrcFourEnclosure.cell_small_08
#print axioms WuSource.SrcFourEnclosure.cell_small_08
#check @WuSource.SrcFourEnclosure.cell_small_09
#print axioms WuSource.SrcFourEnclosure.cell_small_09
#check @WuSource.SrcFourEnclosure.cell_small_10
#print axioms WuSource.SrcFourEnclosure.cell_small_10
#check @WuSource.SrcFourEnclosure.cell_small_11
#print axioms WuSource.SrcFourEnclosure.cell_small_11
#check @WuSource.SrcFourEnclosure.cell_small_12
#print axioms WuSource.SrcFourEnclosure.cell_small_12
#check @WuSource.SrcFourEnclosure.cell_small_13
#print axioms WuSource.SrcFourEnclosure.cell_small_13
#check @WuSource.SrcFourEnclosure.cell_small_14
#print axioms WuSource.SrcFourEnclosure.cell_small_14
#check @WuSource.SrcFourEnclosure.cell_small_15
#print axioms WuSource.SrcFourEnclosure.cell_small_15
#check @WuSource.SrcFourEnclosure.cell_small_16
#print axioms WuSource.SrcFourEnclosure.cell_small_16
#check @WuSource.SrcFourEnclosure.cell_small_17
#print axioms WuSource.SrcFourEnclosure.cell_small_17
#check @WuSource.SrcFourEnclosure.cell_small_18
#print axioms WuSource.SrcFourEnclosure.cell_small_18
#check @WuSource.SrcFourEnclosure.cell_small_19
#print axioms WuSource.SrcFourEnclosure.cell_small_19
#check @WuSource.SrcFourEnclosure.cell_small_20
#print axioms WuSource.SrcFourEnclosure.cell_small_20
#check @WuSource.SrcFourEnclosure.cell_small_21
#print axioms WuSource.SrcFourEnclosure.cell_small_21
#check @WuSource.SrcFourEnclosure.cell_small_22
#print axioms WuSource.SrcFourEnclosure.cell_small_22
#check @WuSource.SrcFourEnclosure.cell_small_23
#print axioms WuSource.SrcFourEnclosure.cell_small_23
#check @WuSource.SrcFourEnclosure.cell_small_24
#print axioms WuSource.SrcFourEnclosure.cell_small_24
#check @WuSource.SrcFourEnclosure.cell_small_25
#print axioms WuSource.SrcFourEnclosure.cell_small_25
#check @WuSource.SrcFourEnclosure.cell_small_26
#print axioms WuSource.SrcFourEnclosure.cell_small_26
#check @WuSource.SrcFourEnclosure.cell_small_27
#print axioms WuSource.SrcFourEnclosure.cell_small_27
#check @WuSource.SrcFourEnclosure.cell_small_28
#print axioms WuSource.SrcFourEnclosure.cell_small_28
#check @WuSource.SrcFourEnclosure.cell_small_29
#print axioms WuSource.SrcFourEnclosure.cell_small_29
#check @WuSource.SrcFourEnclosure.cell_small_30
#print axioms WuSource.SrcFourEnclosure.cell_small_30
#check @WuSource.SrcFourEnclosure.cell_small_31
#print axioms WuSource.SrcFourEnclosure.cell_small_31
#check @WuSource.SrcFourEnclosure.cell_small_32
#print axioms WuSource.SrcFourEnclosure.cell_small_32
#check @WuSource.SrcFourEnclosure.cell_small_33
#print axioms WuSource.SrcFourEnclosure.cell_small_33
#check @WuSource.SrcFourEnclosure.cell_small_34
#print axioms WuSource.SrcFourEnclosure.cell_small_34
#check @WuSource.SrcFourEnclosure.cell_small_35
#print axioms WuSource.SrcFourEnclosure.cell_small_35
#check @WuSource.SrcFourEnclosure.cell_small_36
#print axioms WuSource.SrcFourEnclosure.cell_small_36
#check @WuSource.SrcFourEnclosure.cell_small_37
#print axioms WuSource.SrcFourEnclosure.cell_small_37
#check @WuSource.SrcFourEnclosure.cell_small_38
#print axioms WuSource.SrcFourEnclosure.cell_small_38
#check @WuSource.SrcFourEnclosure.cell_small_39
#print axioms WuSource.SrcFourEnclosure.cell_small_39
#check @WuSource.SrcFourEnclosure.cell_small_40
#print axioms WuSource.SrcFourEnclosure.cell_small_40
#check @WuSource.SrcFourEnclosure.cell_small_41
#print axioms WuSource.SrcFourEnclosure.cell_small_41
#check @WuSource.SrcFourEnclosure.cell_small_42
#print axioms WuSource.SrcFourEnclosure.cell_small_42
#check @WuSource.SrcFourEnclosure.cell_small_43
#print axioms WuSource.SrcFourEnclosure.cell_small_43
#check @WuSource.SrcFourEnclosure.cell_small_44
#print axioms WuSource.SrcFourEnclosure.cell_small_44
#check @WuSource.SrcFourEnclosure.cell_small_45
#print axioms WuSource.SrcFourEnclosure.cell_small_45
#check @WuSource.SrcFourEnclosure.cell_small_46
#print axioms WuSource.SrcFourEnclosure.cell_small_46
#check @WuSource.SrcFourEnclosure.cell_small_47
#print axioms WuSource.SrcFourEnclosure.cell_small_47
#check @WuSource.SrcFourEnclosure.cell_small_48
#print axioms WuSource.SrcFourEnclosure.cell_small_48
#check @WuSource.SrcFourEnclosure.cell_small_49
#print axioms WuSource.SrcFourEnclosure.cell_small_49
#check @WuSource.SrcFourEnclosure.cell_small_50
#print axioms WuSource.SrcFourEnclosure.cell_small_50
#check @WuSource.SrcFourEnclosure.cell_small_51
#print axioms WuSource.SrcFourEnclosure.cell_small_51
#check @WuSource.SrcFourEnclosure.cell_small_52
#print axioms WuSource.SrcFourEnclosure.cell_small_52
#check @WuSource.SrcFourEnclosure.cell_small_53
#print axioms WuSource.SrcFourEnclosure.cell_small_53
#check @WuSource.SrcFourEnclosure.cell_small_54
#print axioms WuSource.SrcFourEnclosure.cell_small_54
#check @WuSource.SrcFourEnclosure.cell_small_55
#print axioms WuSource.SrcFourEnclosure.cell_small_55
#check @WuSource.SrcFourEnclosure.cell_small_56
#print axioms WuSource.SrcFourEnclosure.cell_small_56
#check @WuSource.SrcFourEnclosure.cell_small_57
#print axioms WuSource.SrcFourEnclosure.cell_small_57
#check @WuSource.SrcFourEnclosure.cell_small_58
#print axioms WuSource.SrcFourEnclosure.cell_small_58
#check @WuSource.SrcFourEnclosure.cell_small_59
#print axioms WuSource.SrcFourEnclosure.cell_small_59
#check @WuSource.SrcFourEnclosure.cell_small_60
#print axioms WuSource.SrcFourEnclosure.cell_small_60
#check @WuSource.SrcFourEnclosure.cell_small_61
#print axioms WuSource.SrcFourEnclosure.cell_small_61
#check @WuSource.SrcFourEnclosure.cell_small_62
#print axioms WuSource.SrcFourEnclosure.cell_small_62
#check @WuSource.SrcFourEnclosure.cell_small_63
#print axioms WuSource.SrcFourEnclosure.cell_small_63
#check @WuSource.SrcFourEnclosure.cell_large_00
#print axioms WuSource.SrcFourEnclosure.cell_large_00
#check @WuSource.SrcFourEnclosure.cell_large_01
#print axioms WuSource.SrcFourEnclosure.cell_large_01
#check @WuSource.SrcFourEnclosure.cell_large_02
#print axioms WuSource.SrcFourEnclosure.cell_large_02
#check @WuSource.SrcFourEnclosure.cell_large_03
#print axioms WuSource.SrcFourEnclosure.cell_large_03
#check @WuSource.SrcFourEnclosure.cell_large_04
#print axioms WuSource.SrcFourEnclosure.cell_large_04
#check @WuSource.SrcFourEnclosure.cell_large_05
#print axioms WuSource.SrcFourEnclosure.cell_large_05
#check @WuSource.SrcFourEnclosure.cell_large_06
#print axioms WuSource.SrcFourEnclosure.cell_large_06
#check @WuSource.SrcFourEnclosure.cell_large_07
#print axioms WuSource.SrcFourEnclosure.cell_large_07
#check @WuSource.SrcFourEnclosure.cell_large_08
#print axioms WuSource.SrcFourEnclosure.cell_large_08
#check @WuSource.SrcFourEnclosure.cell_large_09
#print axioms WuSource.SrcFourEnclosure.cell_large_09
#check @WuSource.SrcFourEnclosure.cell_large_10
#print axioms WuSource.SrcFourEnclosure.cell_large_10
#check @WuSource.SrcFourEnclosure.cell_large_11
#print axioms WuSource.SrcFourEnclosure.cell_large_11
#check @WuSource.SrcFourEnclosure.cell_large_12
#print axioms WuSource.SrcFourEnclosure.cell_large_12
#check @WuSource.SrcFourEnclosure.cell_large_13
#print axioms WuSource.SrcFourEnclosure.cell_large_13
#check @WuSource.SrcFourEnclosure.cell_large_14
#print axioms WuSource.SrcFourEnclosure.cell_large_14
#check @WuSource.SrcFourEnclosure.cell_large_15
#print axioms WuSource.SrcFourEnclosure.cell_large_15
#check @WuSource.SrcFourEnclosure.cell_large_16
#print axioms WuSource.SrcFourEnclosure.cell_large_16
#check @WuSource.SrcFourEnclosure.cell_large_17
#print axioms WuSource.SrcFourEnclosure.cell_large_17
#check @WuSource.SrcFourEnclosure.cell_large_18
#print axioms WuSource.SrcFourEnclosure.cell_large_18
#check @WuSource.SrcFourEnclosure.cell_large_19
#print axioms WuSource.SrcFourEnclosure.cell_large_19
#check @WuSource.SrcFourEnclosure.cell_large_20
#print axioms WuSource.SrcFourEnclosure.cell_large_20
#check @WuSource.SrcFourEnclosure.cell_large_21
#print axioms WuSource.SrcFourEnclosure.cell_large_21
#check @WuSource.SrcFourEnclosure.cell_large_22
#print axioms WuSource.SrcFourEnclosure.cell_large_22
#check @WuSource.SrcFourEnclosure.cell_large_23
#print axioms WuSource.SrcFourEnclosure.cell_large_23
#check @WuSource.SrcFourEnclosure.cell_large_24
#print axioms WuSource.SrcFourEnclosure.cell_large_24
#check @WuSource.SrcFourEnclosure.cell_large_25
#print axioms WuSource.SrcFourEnclosure.cell_large_25
#check @WuSource.SrcFourEnclosure.cell_large_26
#print axioms WuSource.SrcFourEnclosure.cell_large_26
#check @WuSource.SrcFourEnclosure.cell_large_27
#print axioms WuSource.SrcFourEnclosure.cell_large_27
#check @WuSource.SrcFourEnclosure.cell_large_28
#print axioms WuSource.SrcFourEnclosure.cell_large_28
#check @WuSource.SrcFourEnclosure.cell_large_29
#print axioms WuSource.SrcFourEnclosure.cell_large_29
#check @WuSource.SrcFourEnclosure.cell_large_30
#print axioms WuSource.SrcFourEnclosure.cell_large_30
#check @WuSource.SrcFourEnclosure.cell_large_31
#print axioms WuSource.SrcFourEnclosure.cell_large_31
#check @WuSource.SrcFourEnclosure.cell_large_32
#print axioms WuSource.SrcFourEnclosure.cell_large_32
#check @WuSource.SrcFourEnclosure.cell_large_33
#print axioms WuSource.SrcFourEnclosure.cell_large_33
#check @WuSource.SrcFourEnclosure.cell_large_34
#print axioms WuSource.SrcFourEnclosure.cell_large_34
#check @WuSource.SrcFourEnclosure.cell_large_35
#print axioms WuSource.SrcFourEnclosure.cell_large_35
#check @WuSource.SrcFourEnclosure.cell_large_36
#print axioms WuSource.SrcFourEnclosure.cell_large_36
#check @WuSource.SrcFourEnclosure.cell_large_37
#print axioms WuSource.SrcFourEnclosure.cell_large_37
#check @WuSource.SrcFourEnclosure.cell_large_38
#print axioms WuSource.SrcFourEnclosure.cell_large_38
#check @WuSource.SrcFourEnclosure.cell_large_39
#print axioms WuSource.SrcFourEnclosure.cell_large_39
#check @WuSource.SrcFourEnclosure.cell_large_40
#print axioms WuSource.SrcFourEnclosure.cell_large_40
#check @WuSource.SrcFourEnclosure.cell_large_41
#print axioms WuSource.SrcFourEnclosure.cell_large_41
#check @WuSource.SrcFourEnclosure.cell_large_42
#print axioms WuSource.SrcFourEnclosure.cell_large_42
#check @WuSource.SrcFourEnclosure.cell_large_43
#print axioms WuSource.SrcFourEnclosure.cell_large_43
#check @WuSource.SrcFourEnclosure.cell_large_44
#print axioms WuSource.SrcFourEnclosure.cell_large_44
#check @WuSource.SrcFourEnclosure.cell_large_45
#print axioms WuSource.SrcFourEnclosure.cell_large_45
#check @WuSource.SrcFourEnclosure.cell_large_46
#print axioms WuSource.SrcFourEnclosure.cell_large_46
#check @WuSource.SrcFourEnclosure.cell_large_47
#print axioms WuSource.SrcFourEnclosure.cell_large_47
#check @WuSource.SrcFourEnclosure.cell_large_48
#print axioms WuSource.SrcFourEnclosure.cell_large_48
#check @WuSource.SrcFourEnclosure.cell_large_49
#print axioms WuSource.SrcFourEnclosure.cell_large_49
#check @WuSource.SrcFourEnclosure.cell_large_50
#print axioms WuSource.SrcFourEnclosure.cell_large_50
#check @WuSource.SrcFourEnclosure.cell_large_51
#print axioms WuSource.SrcFourEnclosure.cell_large_51
#check @WuSource.SrcFourEnclosure.cell_large_52
#print axioms WuSource.SrcFourEnclosure.cell_large_52
#check @WuSource.SrcFourEnclosure.cell_large_53
#print axioms WuSource.SrcFourEnclosure.cell_large_53
#check @WuSource.SrcFourEnclosure.cell_large_54
#print axioms WuSource.SrcFourEnclosure.cell_large_54
#check @WuSource.SrcFourEnclosure.cell_large_55
#print axioms WuSource.SrcFourEnclosure.cell_large_55
#check @WuSource.SrcFourEnclosure.cell_large_56
#print axioms WuSource.SrcFourEnclosure.cell_large_56
#check @WuSource.SrcFourEnclosure.cell_large_57
#print axioms WuSource.SrcFourEnclosure.cell_large_57
#check @WuSource.SrcFourEnclosure.cell_large_58
#print axioms WuSource.SrcFourEnclosure.cell_large_58
#check @WuSource.SrcFourEnclosure.cell_large_59
#print axioms WuSource.SrcFourEnclosure.cell_large_59
#check @WuSource.SrcFourEnclosure.cell_large_60
#print axioms WuSource.SrcFourEnclosure.cell_large_60
#check @WuSource.SrcFourEnclosure.cell_large_61
#print axioms WuSource.SrcFourEnclosure.cell_large_61
#check @WuSource.SrcFourEnclosure.cell_large_62
#print axioms WuSource.SrcFourEnclosure.cell_large_62
#check @WuSource.SrcFourEnclosure.cell_large_63
#print axioms WuSource.SrcFourEnclosure.cell_large_63
#check @WuSource.SrcFourEnclosure.small_certificate
#print axioms WuSource.SrcFourEnclosure.small_certificate
#check @WuSource.SrcFourEnclosure.large_certificate
#print axioms WuSource.SrcFourEnclosure.large_certificate
#check @WuSource.SrcFourEnclosure.sum_four_blocks
#print axioms WuSource.SrcFourEnclosure.sum_four_blocks
#check @WuSource.SrcFourEnclosure.smallLower_sum_0
#print axioms WuSource.SrcFourEnclosure.smallLower_sum_0
#check @WuSource.SrcFourEnclosure.smallLower_sum_16
#print axioms WuSource.SrcFourEnclosure.smallLower_sum_16
#check @WuSource.SrcFourEnclosure.smallLower_sum_32
#print axioms WuSource.SrcFourEnclosure.smallLower_sum_32
#check @WuSource.SrcFourEnclosure.smallLower_sum_48
#print axioms WuSource.SrcFourEnclosure.smallLower_sum_48
#check @WuSource.SrcFourEnclosure.smallLower_sum
#print axioms WuSource.SrcFourEnclosure.smallLower_sum
#check @WuSource.SrcFourEnclosure.smallUpper_sum_0
#print axioms WuSource.SrcFourEnclosure.smallUpper_sum_0
#check @WuSource.SrcFourEnclosure.smallUpper_sum_16
#print axioms WuSource.SrcFourEnclosure.smallUpper_sum_16
#check @WuSource.SrcFourEnclosure.smallUpper_sum_32
#print axioms WuSource.SrcFourEnclosure.smallUpper_sum_32
#check @WuSource.SrcFourEnclosure.smallUpper_sum_48
#print axioms WuSource.SrcFourEnclosure.smallUpper_sum_48
#check @WuSource.SrcFourEnclosure.smallUpper_sum
#print axioms WuSource.SrcFourEnclosure.smallUpper_sum
#check @WuSource.SrcFourEnclosure.largeLower_sum_0
#print axioms WuSource.SrcFourEnclosure.largeLower_sum_0
#check @WuSource.SrcFourEnclosure.largeLower_sum_16
#print axioms WuSource.SrcFourEnclosure.largeLower_sum_16
#check @WuSource.SrcFourEnclosure.largeLower_sum_32
#print axioms WuSource.SrcFourEnclosure.largeLower_sum_32
#check @WuSource.SrcFourEnclosure.largeLower_sum_48
#print axioms WuSource.SrcFourEnclosure.largeLower_sum_48
#check @WuSource.SrcFourEnclosure.largeLower_sum
#print axioms WuSource.SrcFourEnclosure.largeLower_sum
#check @WuSource.SrcFourEnclosure.largeUpper_sum_0
#print axioms WuSource.SrcFourEnclosure.largeUpper_sum_0
#check @WuSource.SrcFourEnclosure.largeUpper_sum_16
#print axioms WuSource.SrcFourEnclosure.largeUpper_sum_16
#check @WuSource.SrcFourEnclosure.largeUpper_sum_32
#print axioms WuSource.SrcFourEnclosure.largeUpper_sum_32
#check @WuSource.SrcFourEnclosure.largeUpper_sum_48
#print axioms WuSource.SrcFourEnclosure.largeUpper_sum_48
#check @WuSource.SrcFourEnclosure.largeUpper_sum
#print axioms WuSource.SrcFourEnclosure.largeUpper_sum
#check @WuSource.SrcFourEnclosure.massLower
#print axioms WuSource.SrcFourEnclosure.massLower
#check @WuSource.SrcFourEnclosure.massUpper
#print axioms WuSource.SrcFourEnclosure.massUpper
#check @WuSource.SrcFourEnclosure.mass_package_enclosure
#print axioms WuSource.SrcFourEnclosure.mass_package_enclosure
#check @WuSource.SrcFourEnclosure.massLower_exact
#print axioms WuSource.SrcFourEnclosure.massLower_exact
#check @WuSource.SrcFourEnclosure.massUpper_exact
#print axioms WuSource.SrcFourEnclosure.massUpper_exact
#check @WuSource.SrcFourEnclosure.mass_rational_enclosure
#print axioms WuSource.SrcFourEnclosure.mass_rational_enclosure
#check @WuSource.SrcFourEnclosure.tailGeom
#print axioms WuSource.SrcFourEnclosure.tailGeom
#check @WuSource.SrcFourEnclosure.tail_inverse
#print axioms WuSource.SrcFourEnclosure.tail_inverse
#check @WuSource.SrcFourEnclosure.density_upper
#print axioms WuSource.SrcFourEnclosure.density_upper
#check @WuSource.SrcFourEnclosure.G_upper
#print axioms WuSource.SrcFourEnclosure.G_upper
#check @WuSource.SrcFourEnclosure.tail_linear_integral
#print axioms WuSource.SrcFourEnclosure.tail_linear_integral
#check @WuSource.SrcFourEnclosure.tail_square_integral
#print axioms WuSource.SrcFourEnclosure.tail_square_integral
#check @WuSource.SrcFourEnclosure.H_tail_upper
#print axioms WuSource.SrcFourEnclosure.H_tail_upper
#check @WuSource.SrcFourEnclosure.outerMass_tail_upper
#print axioms WuSource.SrcFourEnclosure.outerMass_tail_upper
#check @WuSource.SrcFourEnclosure.tailGeom_upper
#print axioms WuSource.SrcFourEnclosure.tailGeom_upper
#check @WuSource.SrcFourEnclosure.outer_uniform_upper
#print axioms WuSource.SrcFourEnclosure.outer_uniform_upper
#check @WuSource.SrcFourEnclosure.outer_fine_upper
#print axioms WuSource.SrcFourEnclosure.outer_fine_upper
#check @WuSource.SrcFourEnclosure.original_pair_mass_tail
#print axioms WuSource.SrcFourEnclosure.original_pair_mass_tail
#check @WuSource.SrcFourEnclosure.original_pair_upper
#print axioms WuSource.SrcFourEnclosure.original_pair_upper
#check @WuSource.SrcFourEnclosure.original_pair_nonneg
#print axioms WuSource.SrcFourEnclosure.original_pair_nonneg
#check @WuSource.SrcFourEnclosure.printedPair
#print axioms WuSource.SrcFourEnclosure.printedPair
#check @WuSource.SrcFourEnclosure.printedPair_exact
#print axioms WuSource.SrcFourEnclosure.printedPair_exact
#check @WuSource.SrcFourEnclosure.original_pair_lower56
#print axioms WuSource.SrcFourEnclosure.original_pair_lower56
#check @WuSource.SrcFourEnclosure.original_pair_conditional_enclosure
#print axioms WuSource.SrcFourEnclosure.original_pair_conditional_enclosure
#check @WuSource.SrcFourEnclosure.enclosure_width
#print axioms WuSource.SrcFourEnclosure.enclosure_width
#check @WuSource.SrcFourEnclosure.original_pair_unconditional_enclosure
#print axioms WuSource.SrcFourEnclosure.original_pair_unconditional_enclosure
#check @WuSource.SrcFourEnclosure.printed_gap_upper
#print axioms WuSource.SrcFourEnclosure.printed_gap_upper
#check @WuSource.SrcFourEnclosure.printed_gap_conditional
#print axioms WuSource.SrcFourEnclosure.printed_gap_conditional
#check @WuSource.SrcFourEnclosure.printed_pair_not_upper_conditional
#print axioms WuSource.SrcFourEnclosure.printed_pair_not_upper_conditional
#check @WuSource.SrcFourEnclosure.actual_pair_upper
#print axioms WuSource.SrcFourEnclosure.actual_pair_upper
#check @WuSource.SrcFourEnclosure.enclosedCoefficient
#print axioms WuSource.SrcFourEnclosure.enclosedCoefficient
#check @WuSource.SrcFourEnclosure.enclosedCoefficient_exact
#print axioms WuSource.SrcFourEnclosure.enclosedCoefficient_exact
#check @WuSource.SrcFourEnclosure.ordinary_P2_enclosed
#print axioms WuSource.SrcFourEnclosure.ordinary_P2_enclosed
#check @WuSource.SrcFourEnclosure.exact_budget_comparison
#print axioms WuSource.SrcFourEnclosure.exact_budget_comparison
#check @WuTarget.SourceFourAccepted.original_pair_enclosure
#print axioms WuTarget.SourceFourAccepted.original_pair_enclosure
#check @WuTarget.SourceFourAccepted.printed_pair_gap
#print axioms WuTarget.SourceFourAccepted.printed_pair_gap
#check @WuTarget.SourceFourAccepted.old_budget_impossible
#print axioms WuTarget.SourceFourAccepted.old_budget_impossible
#check @WuTarget.SourceRevisedClosureBudget.sufficient_source_budget
#print axioms WuTarget.SourceRevisedClosureBudget.sufficient_source_budget
#check @WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget
#print axioms WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget

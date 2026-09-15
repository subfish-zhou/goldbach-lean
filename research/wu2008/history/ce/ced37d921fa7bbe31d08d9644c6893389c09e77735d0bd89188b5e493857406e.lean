import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalUpper

/-!
# Actual compiler type and axiom evidence for Gamma5 classical

Every authored declaration is printed below. No estimate is introduced as
an axiom, and the two count endpoints are checked directly.
-/

set_option pp.fullNames true
set_option pp.universes true
set_option pp.width 120

open Wu2008DoubleSieve

#print Gamma5ClassicalLabel
#print gamma5ClassicalS
#print gamma5ClassicalB
#print gamma5ClassicalProduct
#print gamma5ClassicalLabels
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print gamma5ClassicalRemainder
#print gamma5ClassicalAlpha
#print gamma5ClassicalZeta
#print gamma5ClassicalLevel
#print gamma5ClassicalCutoff
#print gamma5ClassicalLargePrimes
#print Gamma5ClassicalGeometry

#check @gamma5ClassicalCount_eq_nat_count
#check @gamma5Classical_sifted_mul_prime
#check @gamma5Classical_source_count_eq
#check @gamma5Classical_source_count_antitone
#check @gamma5Classical_AP_expansion
#check @gamma5Classical_masked_remainder_le
#check @gamma5Classical_exponents_pos
#check @gamma5Classical_ratio_coordinates
#check @gamma5Classical_ratio_constants
#check @gamma5Classical_pair_geometry
#check @gamma5Classical_ratio2_cutoff_bridge
#check @gamma5Classical_ratio_mul_log
#check @gamma5Classical_label_geometry
#check @gamma5Classical_polynomial_envelope
#check @gamma5Classical_mem_labels_iff
#check @gamma5Classical_windows_eventually
#check @gamma5Classical_masked_bombieri_vinogradov
#check @gamma5Classical_remainder_relative
#check @gamma5Classical_density_eventually
#check @gamma5Classical_label_finite_upper
#check @gamma5Classical_mask_upper
#check @gamma5Classical_full_upper

#check @Gamma5ClassicalGeometry.mk
#check @Gamma5ClassicalGeometry.product_pos
#check @Gamma5ClassicalGeometry.product_le
#check @Gamma5ClassicalGeometry.level_gt_one
#check @Gamma5ClassicalGeometry.cutoff_gt_one
#check @Gamma5ClassicalGeometry.cutoff_le_level
#check @Gamma5ClassicalGeometry.cutoff_lower
#check @Gamma5ClassicalGeometry.prime_lower
#check @Gamma5ClassicalGeometry.ratio_eq
#check @Gamma5ClassicalGeometry.ratio_lower
#check @Gamma5ClassicalGeometry.ratio_upper
#check @Gamma5ClassicalGeometry.original_ratio_lower
#check @Gamma5ClassicalGeometry.original_ratio_upper

#print axioms Gamma5ClassicalLabel
#print axioms gamma5ClassicalS
#print axioms gamma5ClassicalB
#print axioms gamma5ClassicalProduct
#print axioms gamma5ClassicalLabels
#print axioms gamma5ClassicalCount
#print axioms gamma5ClassicalMainMass
#print axioms gamma5ClassicalRemainder
#print axioms gamma5ClassicalAlpha
#print axioms gamma5ClassicalZeta
#print axioms gamma5ClassicalLevel
#print axioms gamma5ClassicalCutoff
#print axioms gamma5ClassicalLargePrimes
#print axioms Gamma5ClassicalGeometry
#print axioms gamma5ClassicalCount_eq_nat_count
#print axioms gamma5Classical_sifted_mul_prime
#print axioms gamma5Classical_source_count_eq
#print axioms gamma5Classical_source_count_antitone
#print axioms gamma5Classical_AP_expansion
#print axioms gamma5Classical_masked_remainder_le
#print axioms gamma5Classical_exponents_pos
#print axioms gamma5Classical_ratio_coordinates
#print axioms gamma5Classical_ratio_constants
#print axioms gamma5Classical_pair_geometry
#print axioms gamma5Classical_ratio2_cutoff_bridge
#print axioms gamma5Classical_ratio_mul_log
#print axioms gamma5Classical_label_geometry
#print axioms gamma5Classical_polynomial_envelope
#print axioms gamma5Classical_mem_labels_iff
#print axioms gamma5Classical_windows_eventually
#print axioms gamma5Classical_masked_bombieri_vinogradov
#print axioms gamma5Classical_remainder_relative
#print axioms gamma5Classical_density_eventually
#print axioms gamma5Classical_label_finite_upper
#print axioms gamma5Classical_mask_upper
#print axioms gamma5Classical_full_upper
#print axioms Gamma5ClassicalGeometry.mk
#print axioms Gamma5ClassicalGeometry.product_pos
#print axioms Gamma5ClassicalGeometry.product_le
#print axioms Gamma5ClassicalGeometry.level_gt_one
#print axioms Gamma5ClassicalGeometry.cutoff_gt_one
#print axioms Gamma5ClassicalGeometry.cutoff_le_level
#print axioms Gamma5ClassicalGeometry.cutoff_lower
#print axioms Gamma5ClassicalGeometry.prime_lower
#print axioms Gamma5ClassicalGeometry.ratio_eq
#print axioms Gamma5ClassicalGeometry.ratio_lower
#print axioms Gamma5ClassicalGeometry.ratio_upper
#print axioms Gamma5ClassicalGeometry.original_ratio_lower
#print axioms Gamma5ClassicalGeometry.original_ratio_upper

#check @convolution_bombieri_vinogradov
#check @ordinaryRosserWeight_support
#check @ordinaryRosserWeight_abs_le_one
#check @sourceSequenceRemainder_eq_AP
#check @ordinaryRosserRemainder_le_AP
#check @ordinaryRosser_upper_finite
#check @ordinaryRosser_upper_density_canonical_bounded_local
#check @eventually_localSieveProduct_relative
#check @canonical_upper_normalization_budget
#check @wu_boxTheta_lower
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral
#print boxTheta

#print axioms convolution_bombieri_vinogradov
#print axioms ordinaryRosserWeight_support
#print axioms ordinaryRosserWeight_abs_le_one
#print axioms sourceSequenceRemainder_eq_AP
#print axioms ordinaryRosserRemainder_le_AP
#print axioms ordinaryRosser_upper_finite
#print axioms ordinaryRosser_upper_density_canonical_bounded_local
#print axioms eventually_localSieveProduct_relative
#print axioms canonical_upper_normalization_budget
#print axioms wu_boxTheta_lower

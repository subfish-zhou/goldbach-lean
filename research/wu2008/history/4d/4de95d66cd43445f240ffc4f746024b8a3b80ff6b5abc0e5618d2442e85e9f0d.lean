import WR2OmegaHighRoot
import WSrcSingleOriginalLedger
import WR2SixthCountRoot
import Lean
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#check @WuPaper.R2OmegaHigh.index
#print axioms WuPaper.R2OmegaHigh.index
#print WuPaper.R2OmegaHigh.index
#check @WuPaper.R2OmegaHigh.windows
#print axioms WuPaper.R2OmegaHigh.windows
#print WuPaper.R2OmegaHigh.windows
#check @WuPaper.R2OmegaHigh.theta
#print axioms WuPaper.R2OmegaHigh.theta
#print WuPaper.R2OmegaHigh.theta
#check @WuPaper.R2OmegaHigh.lowerIntegral
#print axioms WuPaper.R2OmegaHigh.lowerIntegral
#print WuPaper.R2OmegaHigh.lowerIntegral
#check @WuPaper.R2OmegaHigh.support
#print axioms WuPaper.R2OmegaHigh.support
#check @WuPaper.R2OmegaHigh.weighted_sum
#print axioms WuPaper.R2OmegaHigh.weighted_sum
#check @WuPaper.R2OmegaHigh.geometry
#print axioms WuPaper.R2OmegaHigh.geometry
#check @WuPaper.R2OmegaHigh.prime_geometry
#print axioms WuPaper.R2OmegaHigh.prime_geometry
#check @WuPaper.R2OmegaHigh.support_geometry
#print axioms WuPaper.R2OmegaHigh.support_geometry
#check @WuPaper.R2OmegaHigh.scale_nonneg
#print axioms WuPaper.R2OmegaHigh.scale_nonneg
#check @WuPaper.R2OmegaHigh.theta_nonneg
#print axioms WuPaper.R2OmegaHigh.theta_nonneg
#check @WuPaper.R2OmegaHigh.theta_total_mass
#print axioms WuPaper.R2OmegaHigh.theta_total_mass
#check @WuPaper.R2OmegaHigh.actual_AP_paid
#print axioms WuPaper.R2OmegaHigh.actual_AP_paid
#check @WuPaper.R2OmegaHigh.omega1_upper
#print axioms WuPaper.R2OmegaHigh.omega1_upper
#check @WuPaper.R2OmegaHigh.actual_R1_paid
#print axioms WuPaper.R2OmegaHigh.actual_R1_paid
#check @WuPaper.R2OmegaHigh.actual_R2_paid
#print axioms WuPaper.R2OmegaHigh.actual_R2_paid
#check @WuPaper.R2OmegaHigh.density_slack_choice
#print axioms WuPaper.R2OmegaHigh.density_slack_choice
#check @WuPaper.R2OmegaHigh.omega3_upper_at
#print axioms WuPaper.R2OmegaHigh.omega3_upper_at
#check @WuPaper.R2OmegaHigh.omega3_upper
#print axioms WuPaper.R2OmegaHigh.omega3_upper
#check @WuPaper.R2OmegaHigh.outer_support
#print axioms WuPaper.R2OmegaHigh.outer_support
#check @WuPaper.R2OmegaHigh.inner_geometry
#print axioms WuPaper.R2OmegaHigh.inner_geometry
#check @WuPaper.R2OmegaHigh.theta_sum
#print axioms WuPaper.R2OmegaHigh.theta_sum
#check @WuPaper.R2OmegaHigh.theta_atom_nonneg
#print axioms WuPaper.R2OmegaHigh.theta_atom_nonneg
#check @WuPaper.R2OmegaHigh.actual_atom_lower
#print axioms WuPaper.R2OmegaHigh.actual_atom_lower
#check @WuPaper.R2OmegaHigh.omega2_lower
#print axioms WuPaper.R2OmegaHigh.omega2_lower
#check @WuPaper.R2OmegaHigh.psi_coefficient
#print axioms WuPaper.R2OmegaHigh.psi_coefficient
#check @WuPaper.R2OmegaHigh.raw_mother_upper
#print axioms WuPaper.R2OmegaHigh.raw_mother_upper
#check @WuPaper.R2OmegaHigh.actual_psi_theta_upper
#print axioms WuPaper.R2OmegaHigh.actual_psi_theta_upper
#check @WuPaper.R2OmegaHigh.outerIntegral
#print axioms WuPaper.R2OmegaHigh.outerIntegral
#print WuPaper.R2OmegaHigh.outerIntegral
#check @WuPaper.R2OmegaHigh.closedPrimes
#print axioms WuPaper.R2OmegaHigh.closedPrimes
#print WuPaper.R2OmegaHigh.closedPrimes
#check @WuPaper.R2OmegaHigh.reciprocalMain
#print axioms WuPaper.R2OmegaHigh.reciprocalMain
#print WuPaper.R2OmegaHigh.reciprocalMain
#check @WuPaper.R2OmegaHigh.subTwoMain
#print axioms WuPaper.R2OmegaHigh.subTwoMain
#print WuPaper.R2OmegaHigh.subTwoMain
#check @WuPaper.R2OmegaHigh.outer_closed
#print axioms WuPaper.R2OmegaHigh.outer_closed
#check @WuPaper.R2OmegaHigh.closed_coordinate
#print axioms WuPaper.R2OmegaHigh.closed_coordinate
#check @WuPaper.R2OmegaHigh.prime_weight_bounds
#print axioms WuPaper.R2OmegaHigh.prime_weight_bounds
#check @WuPaper.R2OmegaHigh.prime_weight_eq_single
#print axioms WuPaper.R2OmegaHigh.prime_weight_eq_single
#check @WuPaper.R2OmegaHigh.closed_prime_integral
#print axioms WuPaper.R2OmegaHigh.closed_prime_integral
#check @WuPaper.R2OmegaHigh.missing_card
#print axioms WuPaper.R2OmegaHigh.missing_card
#check @WuPaper.R2OmegaHigh.reciprocal_mask_error
#print axioms WuPaper.R2OmegaHigh.reciprocal_mask_error
#check @WuPaper.R2OmegaHigh.reciprocal_integral
#print axioms WuPaper.R2OmegaHigh.reciprocal_integral
#check @WuPaper.R2OmegaHigh.subTwo_integral
#print axioms WuPaper.R2OmegaHigh.subTwo_integral
#check @WuPaper.R2OmegaHigh.fixedCoefficient
#print axioms WuPaper.R2OmegaHigh.fixedCoefficient
#print WuPaper.R2OmegaHigh.fixedCoefficient
#check @WuPaper.R2OmegaHigh.theta_exact
#print axioms WuPaper.R2OmegaHigh.theta_exact
#check @WuPaper.R2OmegaHigh.theta_integral_error
#print axioms WuPaper.R2OmegaHigh.theta_integral_error
#check @WuPaper.R2OmegaHigh.raw_fixed_integral_upper
#print axioms WuPaper.R2OmegaHigh.raw_fixed_integral_upper
#check @WuPaper.R2OmegaHigh.previousNode
#print axioms WuPaper.R2OmegaHigh.previousNode
#print WuPaper.R2OmegaHigh.previousNode
#check @WuPaper.R2OmegaHigh.paperCoefficient
#print axioms WuPaper.R2OmegaHigh.paperCoefficient
#print WuPaper.R2OmegaHigh.paperCoefficient
#check @WuPaper.R2OmegaHigh.window_endpoints
#print axioms WuPaper.R2OmegaHigh.window_endpoints
#check @WuPaper.R2OmegaHigh.initial_upper
#print axioms WuPaper.R2OmegaHigh.initial_upper
#check @WuPaper.R2OmegaHigh.outer_integral_zero
#print axioms WuPaper.R2OmegaHigh.outer_integral_zero
#check @WuPaper.R2OmegaHigh.paper_coefficient_log
#print axioms WuPaper.R2OmegaHigh.paper_coefficient_log
#check @WuPaper.R2OmegaHigh.psi_zero_eq_source
#print axioms WuPaper.R2OmegaHigh.psi_zero_eq_source
#check @WuPaper.R2OmegaHigh.fixed_zero_eq_paper
#print axioms WuPaper.R2OmegaHigh.fixed_zero_eq_paper
#check @WuPaper.R2OmegaHigh.regularOuter
#print axioms WuPaper.R2OmegaHigh.regularOuter
#print WuPaper.R2OmegaHigh.regularOuter
#check @WuPaper.R2OmegaHigh.regular_outer_eq
#print axioms WuPaper.R2OmegaHigh.regular_outer_eq
#check @WuPaper.R2OmegaHigh.regular_outer_continuous
#print axioms WuPaper.R2OmegaHigh.regular_outer_continuous
#check @WuPaper.R2OmegaHigh.outer_continuousAt_zero
#print axioms WuPaper.R2OmegaHigh.outer_continuousAt_zero
#check @WuPaper.R2OmegaHigh.fixed_continuousAt_zero
#print axioms WuPaper.R2OmegaHigh.fixed_continuousAt_zero
#check @WuPaper.R2OmegaHigh.coefficient_close
#print axioms WuPaper.R2OmegaHigh.coefficient_close
#check @WuPaper.R2OmegaHigh.common_coefficient_radius
#print axioms WuPaper.R2OmegaHigh.common_coefficient_radius
#check @WuPaper.R2OmegaHigh.original_four_windows
#print axioms WuPaper.R2OmegaHigh.original_four_windows
#check @WuPaper.R2OmegaHigh.publicationCoefficient
#print axioms WuPaper.R2OmegaHigh.publicationCoefficient
#print WuPaper.R2OmegaHigh.publicationCoefficient
#check @WuPaper.R2OmegaHigh.fourClassical
#print axioms WuPaper.R2OmegaHigh.fourClassical
#print WuPaper.R2OmegaHigh.fourClassical
#check @WuPaper.R2OmegaHigh.fourSourceGain
#print axioms WuPaper.R2OmegaHigh.fourSourceGain
#print WuPaper.R2OmegaHigh.fourSourceGain
#check @WuPaper.R2OmegaHigh.fourPaidGain
#print axioms WuPaper.R2OmegaHigh.fourPaidGain
#print WuPaper.R2OmegaHigh.fourPaidGain
#check @WuPaper.R2OmegaHigh.existing_publication_identity
#print axioms WuPaper.R2OmegaHigh.existing_publication_identity
#check @WuPaper.R2OmegaHigh.publication_le_original
#print axioms WuPaper.R2OmegaHigh.publication_le_original
#check @WuPaper.R2OmegaHigh.publication_le_actual
#print axioms WuPaper.R2OmegaHigh.publication_le_actual
#check @WuPaper.R2OmegaHigh.paper_coefficient_le_publication
#print axioms WuPaper.R2OmegaHigh.paper_coefficient_le_publication
#check @WuPaper.R2OmegaHigh.four_gain_paid
#print axioms WuPaper.R2OmegaHigh.four_gain_paid
#check @WuPaper.R2OmegaHigh.sum_paper_coefficient
#print axioms WuPaper.R2OmegaHigh.sum_paper_coefficient
#check @WuPaper.R2OmegaHigh.sum_publication_coefficient
#print axioms WuPaper.R2OmegaHigh.sum_publication_coefficient
#check @WuPaper.R2OmegaHigh.original_small_delta_four_windows
#print axioms WuPaper.R2OmegaHigh.original_small_delta_four_windows
#check @WuPaper.R2OmegaHigh.actual_four_publications
#print axioms WuPaper.R2OmegaHigh.actual_four_publications
#check @WuPaper.R2OmegaHigh.four_actual_original_gain
#print axioms WuPaper.R2OmegaHigh.four_actual_original_gain
#check @WuPaper.R2OmegaHigh.four_actual_publication_gain
#print axioms WuPaper.R2OmegaHigh.four_actual_publication_gain
#check @WuPaper.R2OmegaHigh.uniform_omega_and_theta
#print axioms WuPaper.R2OmegaHigh.uniform_omega_and_theta
#check @WuPaper.R2OmegaHigh.proposition44_four_actual
#print axioms WuPaper.R2OmegaHigh.proposition44_four_actual
#check @WuPaper.R2OmegaHigh.E02_four_original
#print axioms WuPaper.R2OmegaHigh.E02_four_original

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for root in [`WuPaper.R2OmegaHigh.E02_four_original,
      `WuPaper.R2OmegaHigh.four_actual_publication_gain] do
    let mut todo := [root]
    let mut seen : Std.HashSet Name := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        todo := ci.type.getUsedConstants.toList ++ todo
        if let some v := ci.value? (allowOpaque := true) then
          todo := v.getUsedConstants.toList ++ todo
    for n in [`WuPaper.R2OmegaHigh.omega1_upper,
        `WuPaper.R2OmegaHigh.omega2_lower,
        `WuPaper.R2OmegaHigh.omega3_upper,
        `WuPaper.R2OmegaHigh.theta_integral_error,
        `WuPaper.R2OmegaHigh.actual_AP_paid,
        `WuPaper.R2OmegaHigh.actual_R1_paid,
        `WuPaper.R2OmegaHigh.actual_R2_paid,
        `WuPaper.R2OmegaHigh.paper_coefficient_log,
        `WuSource.SrcSingle.seven_raw_source_count] do
      unless seen.contains n do throwError "Missing consumer edge {root} -> {n}"
      logInfo m!"PARENT_REACHED {root} -> {n}"
    for n in [`sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler] do
      if seen.contains n then throwError "Unadmitted trust {root} -> {n}"
  logInfo "PARENT_FOUR_WINDOW_CONSUMER_PASS"

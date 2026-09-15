import WE10MajorAcceptedTotal
import Lean
open Lean Elab Command

elab "#e10_major_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E10FourMajor.original_pair_upper, `WuTarget.E10FourMajor.reciprocal_upper,
      `WuTarget.EveningFourTotal.joint_pair_payment_le_core, `WuTarget.EveningFourTotal.ordinary_P2_display] do
    let mut todo := #[root]
    let mut seen : Std.HashSet Name := {}
    let mut missing : Array Name := #[]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if !seen.contains n then
        seen := seen.insert n
        if seen.size == 200000 then logInfo "expanded consumer exceeds old diagnostic-size cutoff; continuing full finite visited-set traversal"
        match env.checked.get.find? n with
        | none => missing := missing.push n
        | some ci =>
          todo := todo ++ ci.type.getUsedConstants
          match ci with
          | .defnInfo v => todo := todo ++ v.value.getUsedConstants
          | .thmInfo v => todo := todo ++ v.value.getUsedConstants
          | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
          | .inductInfo v => todo := todo ++ v.ctors.toArray
          | _ => pure ()
    let names := seen.toArray.map Name.toString
    let watched := names.filter fun n =>
      n.endsWith ".Cinf" || n.endsWith ".Ainf" || n.endsWith ".originalH" ||
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".C_tendsto" ||
      n.endsWith ".Ainf_le_supersolution" || n.endsWith ".subsolution_le_Ainf" ||
      n.endsWith ".actual_comparison_same_delta"
    let forbidden := names.filter fun n =>
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".Ainf_le_supersolution" ||
      n.endsWith ".subsolution_le_Ainf" || n.endsWith ".actual_comparison_same_delta"
    let out ← IO.getStdout
    out.putStrLn <| (Json.mkObj [("root", toJson root.toString),
      ("visited", toJson seen.size), ("missing", toJson (missing.map Name.toString)),
      ("watched", toJson watched), ("forbidden", toJson forbidden)]).compress
    out.flush
    unless missing.isEmpty && forbidden.isEmpty do throwError "method audit failed"

#e10_major_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E10Four.cross
#print axioms WuTarget.E10Four.cross
#check @WuTarget.E10Four.kappa
#print axioms WuTarget.E10Four.kappa
#check @WuTarget.E10Four.crossLoss
#print axioms WuTarget.E10Four.crossLoss
#check @WuTarget.E10Four.rebateCoeff
#print axioms WuTarget.E10Four.rebateCoeff
#check @WuTarget.E10Four.rebate
#print axioms WuTarget.E10Four.rebate
#check @WuTarget.E10Four.cross_geometry
#print axioms WuTarget.E10Four.cross_geometry
#check @WuTarget.E10Four.cross_nonneg
#print axioms WuTarget.E10Four.cross_nonneg
#check @WuTarget.E10Four.crossLoss_nonneg
#print axioms WuTarget.E10Four.crossLoss_nonneg
#check @WuTarget.E10Four.cross_correlation
#print axioms WuTarget.E10Four.cross_correlation
#check @WuTarget.E10Four.inner11_correlated
#print axioms WuTarget.E10Four.inner11_correlated
#check @WuTarget.E10Four.middle11_correlated
#print axioms WuTarget.E10Four.middle11_correlated
#check @WuTarget.E10Four.outer11_correlated
#print axioms WuTarget.E10Four.outer11_correlated
#check @WuTarget.E10Four.rebateCoeff_pos
#print axioms WuTarget.E10Four.rebateCoeff_pos
#check @WuTarget.E10Four.rebate_nonneg
#print axioms WuTarget.E10Four.rebate_nonneg
#check @WuTarget.E10Four.outer11_rebate
#print axioms WuTarget.E10Four.outer11_rebate
#check @WuTarget.E10Four.outer_pair_rebate
#print axioms WuTarget.E10Four.outer_pair_rebate
#check @WuTarget.E10Four.rebate_eq
#print axioms WuTarget.E10Four.rebate_eq
#check @WuTarget.E10Four.rebate_integrable
#print axioms WuTarget.E10Four.rebate_integrable
#check @WuTarget.E10Four.rebate_integral
#print axioms WuTarget.E10Four.rebate_integral
#check @WuTarget.E10Four.original_pair_rebate
#print axioms WuTarget.E10Four.original_pair_rebate
#check @WuTarget.E10Four.recovery
#print axioms WuTarget.E10Four.recovery
#check @WuTarget.E10Four.pairUpper
#print axioms WuTarget.E10Four.pairUpper
#check @WuTarget.E10Four.netCredit
#print axioms WuTarget.E10Four.netCredit
#check @WuTarget.E10Four.recovery_pos
#print axioms WuTarget.E10Four.recovery_pos
#check @WuTarget.E10Four.recovery_paid
#print axioms WuTarget.E10Four.recovery_paid
#check @WuTarget.E10Four.original_pair_upper
#print axioms WuTarget.E10Four.original_pair_upper
#check @WuTarget.E10Four.pair_strict
#print axioms WuTarget.E10Four.pair_strict
#check @WuTarget.E10Four.netCredit_pos
#print axioms WuTarget.E10Four.netCredit_pos
#check @WuTarget.E10Four.exact_recovery
#print axioms WuTarget.E10Four.exact_recovery
#check @WuTarget.E10Four.net_identity
#print axioms WuTarget.E10Four.net_identity
#check @WuTarget.E10Four.kappa_exact
#print axioms WuTarget.E10Four.kappa_exact
#check @WuTarget.E10Four.recovery_exact
#print axioms WuTarget.E10Four.recovery_exact
#check @WuTarget.E10Four.netCredit_exact
#print axioms WuTarget.E10Four.netCredit_exact
#check @WuTarget.E10Four.pairUpper_exact
#print axioms WuTarget.E10Four.pairUpper_exact
#check @WuTarget.E10Four.recovery_bounds
#print axioms WuTarget.E10Four.recovery_bounds
#check @WuTarget.E10Four.netCredit_bounds
#print axioms WuTarget.E10Four.netCredit_bounds
#check @WuTarget.E10Four.pairUpper_lt_display
#print axioms WuTarget.E10Four.pairUpper_lt_display
#check @WuTarget.E10Four.original_pair_lt_display
#print axioms WuTarget.E10Four.original_pair_lt_display
#check @WuTarget.E10Four.paidCoefficient
#print axioms WuTarget.E10Four.paidCoefficient
#check @WuTarget.E10Four.remainingCoefficient
#print axioms WuTarget.E10Four.remainingCoefficient
#check @WuTarget.E10Four.paid_exact
#print axioms WuTarget.E10Four.paid_exact
#check @WuTarget.E10Four.paid_gain_identity
#print axioms WuTarget.E10Four.paid_gain_identity
#check @WuTarget.E10Four.paid_gain
#print axioms WuTarget.E10Four.paid_gain
#check @WuTarget.E10Four.paid_lt_actual
#print axioms WuTarget.E10Four.paid_lt_actual
#check @WuTarget.E10Four.actual_pair_upper
#print axioms WuTarget.E10Four.actual_pair_upper
#check @WuTarget.E10Four.ordinary_P2_paid
#print axioms WuTarget.E10Four.ordinary_P2_paid
#check @WuTarget.E10Four.paid_threshold_iff
#print axioms WuTarget.E10Four.paid_threshold_iff
#check @WuTarget.E10Four.refined_target
#print axioms WuTarget.E10Four.refined_target
#check @WuTarget.E10FourMajor.z0
#print axioms WuTarget.E10FourMajor.z0
#check @WuTarget.E10FourMajor.slope
#print axioms WuTarget.E10FourMajor.slope
#check @WuTarget.E10FourMajor.crossCap
#print axioms WuTarget.E10FourMajor.crossCap
#check @WuTarget.E10FourMajor.recipCoeff
#print axioms WuTarget.E10FourMajor.recipCoeff
#check @WuTarget.E10FourMajor.capTerm
#print axioms WuTarget.E10FourMajor.capTerm
#check @WuTarget.E10FourMajor.pairCap
#print axioms WuTarget.E10FourMajor.pairCap
#check @WuTarget.E10FourMajor.fixed_geometry_major
#print axioms WuTarget.E10FourMajor.fixed_geometry_major
#check @WuTarget.E10FourMajor.slope_pos
#print axioms WuTarget.E10FourMajor.slope_pos
#check @WuTarget.E10FourMajor.crossCap_pos
#print axioms WuTarget.E10FourMajor.crossCap_pos
#check @WuTarget.E10FourMajor.recipCoeff_pos
#print axioms WuTarget.E10FourMajor.recipCoeff_pos
#check @WuTarget.E10FourMajor.pairCap_lt_target
#print axioms WuTarget.E10FourMajor.pairCap_lt_target
#check @WuTarget.E10FourMajor.anchored_nonneg
#print axioms WuTarget.E10FourMajor.anchored_nonneg
#check @WuTarget.E10FourMajor.exp_cubic_remainder
#print axioms WuTarget.E10FourMajor.exp_cubic_remainder
#check @WuTarget.E10FourMajor.reciprocalCap
#print axioms WuTarget.E10FourMajor.reciprocalCap
#check @WuTarget.E10FourMajor.reciprocal_upper
#print axioms WuTarget.E10FourMajor.reciprocal_upper
#check @WuTarget.E10FourMajor.cross_tangent
#print axioms WuTarget.E10FourMajor.cross_tangent
#check @WuTarget.E10FourMajor.kernel_upper
#print axioms WuTarget.E10FourMajor.kernel_upper
#check @WuTarget.E10FourMajor.inner10_upper
#print axioms WuTarget.E10FourMajor.inner10_upper
#check @WuTarget.E10FourMajor.inner11_upper
#print axioms WuTarget.E10FourMajor.inner11_upper
#check @WuTarget.E10FourMajor.middle_pair_upper
#print axioms WuTarget.E10FourMajor.middle_pair_upper
#check @WuTarget.E10FourMajor.middleTerm
#print axioms WuTarget.E10FourMajor.middleTerm
#check @WuTarget.E10FourMajor.coefA
#print axioms WuTarget.E10FourMajor.coefA
#check @WuTarget.E10FourMajor.coefB
#print axioms WuTarget.E10FourMajor.coefB
#check @WuTarget.E10FourMajor.profileTerm
#print axioms WuTarget.E10FourMajor.profileTerm
#check @WuTarget.E10FourMajor.profile
#print axioms WuTarget.E10FourMajor.profile
#check @WuTarget.E10FourMajor.coefficients_pos
#print axioms WuTarget.E10FourMajor.coefficients_pos
#check @WuTarget.E10FourMajor.middle_sum_identity
#print axioms WuTarget.E10FourMajor.middle_sum_identity
#check @WuTarget.E10FourMajor.middle_le_sum
#print axioms WuTarget.E10FourMajor.middle_le_sum
#check @WuTarget.E10FourMajor.middleTerm_eq
#print axioms WuTarget.E10FourMajor.middleTerm_eq
#check @WuTarget.E10FourMajor.middleTerm_integrable
#print axioms WuTarget.E10FourMajor.middleTerm_integrable
#check @WuTarget.E10FourMajor.middleTerm_integral
#print axioms WuTarget.E10FourMajor.middleTerm_integral
#check @WuTarget.E10FourMajor.outer_pair_upper
#print axioms WuTarget.E10FourMajor.outer_pair_upper
#check @WuTarget.E10FourMajor.momentTerm
#print axioms WuTarget.E10FourMajor.momentTerm
#check @WuTarget.E10FourMajor.profileTerm_integrable
#print axioms WuTarget.E10FourMajor.profileTerm_integrable
#check @WuTarget.E10FourMajor.profile_integrable
#print axioms WuTarget.E10FourMajor.profile_integrable
#check @WuTarget.E10FourMajor.weighted_profileTerm_integrable
#print axioms WuTarget.E10FourMajor.weighted_profileTerm_integrable
#check @WuTarget.E10FourMajor.weighted_profile_integrable
#print axioms WuTarget.E10FourMajor.weighted_profile_integrable
#check @WuTarget.E10FourMajor.profile_integral
#print axioms WuTarget.E10FourMajor.profile_integral
#check @WuTarget.E10FourMajor.weighted_profile_integral
#print axioms WuTarget.E10FourMajor.weighted_profile_integral
#check @WuTarget.E10FourMajor.weighted_amount_identity
#print axioms WuTarget.E10FourMajor.weighted_amount_identity
#check @WuTarget.E10FourMajor.original_pair_le_moments
#print axioms WuTarget.E10FourMajor.original_pair_le_moments
#check @WuTarget.E10FourMajor.momentTerm_upper
#print axioms WuTarget.E10FourMajor.momentTerm_upper
#check @WuTarget.E10FourMajor.original_pair_upper
#print axioms WuTarget.E10FourMajor.original_pair_upper
#check @WuTarget.E10FourMajor.original_pair_lt_target
#print axioms WuTarget.E10FourMajor.original_pair_lt_target
#check @WuTarget.E10FourMajor.original_pair_target
#print axioms WuTarget.E10FourMajor.original_pair_target
#check @WuTarget.E10FourMajor.replacementCap
#print axioms WuTarget.E10FourMajor.replacementCap
#check @WuTarget.E10FourMajor.additionalCredit
#print axioms WuTarget.E10FourMajor.additionalCredit
#check @WuTarget.E10FourMajor.totalCredit
#print axioms WuTarget.E10FourMajor.totalCredit
#check @WuTarget.E10FourMajor.paidCoefficient
#print axioms WuTarget.E10FourMajor.paidCoefficient
#check @WuTarget.E10FourMajor.remainingCoefficient
#print axioms WuTarget.E10FourMajor.remainingCoefficient
#check @WuTarget.E10FourMajor.replacement_upper
#print axioms WuTarget.E10FourMajor.replacement_upper
#check @WuTarget.E10FourMajor.replacement_strict
#print axioms WuTarget.E10FourMajor.replacement_strict
#check @WuTarget.E10FourMajor.additionalCredit_lower
#print axioms WuTarget.E10FourMajor.additionalCredit_lower
#check @WuTarget.E10FourMajor.totalCredit_lower
#print axioms WuTarget.E10FourMajor.totalCredit_lower
#check @WuTarget.E10FourMajor.totalCredit_exact
#print axioms WuTarget.E10FourMajor.totalCredit_exact
#check @WuTarget.E10FourMajor.additionalCredit_exact
#print axioms WuTarget.E10FourMajor.additionalCredit_exact
#check @WuTarget.E10FourMajor.no_double_payment
#print axioms WuTarget.E10FourMajor.no_double_payment
#check @WuTarget.E10FourMajor.paid_relative_first
#print axioms WuTarget.E10FourMajor.paid_relative_first
#check @WuTarget.E10FourMajor.paid_gain_identity
#print axioms WuTarget.E10FourMajor.paid_gain_identity
#check @WuTarget.E10FourMajor.paid_gain
#print axioms WuTarget.E10FourMajor.paid_gain
#check @WuTarget.E10FourMajor.paid_exact
#print axioms WuTarget.E10FourMajor.paid_exact
#check @WuTarget.E10FourMajor.paid_lt_actual
#print axioms WuTarget.E10FourMajor.paid_lt_actual
#check @WuTarget.E10FourMajor.actual_pair_upper
#print axioms WuTarget.E10FourMajor.actual_pair_upper
#check @WuTarget.E10FourMajor.ordinary_P2_paid
#print axioms WuTarget.E10FourMajor.ordinary_P2_paid
#check @WuTarget.E10FourMajor.paid_threshold_iff
#print axioms WuTarget.E10FourMajor.paid_threshold_iff
#check @WuTarget.EveningFourTotal.netGain
#print axioms WuTarget.EveningFourTotal.netGain
#check @WuTarget.EveningFourTotal.paidCoefficient
#print axioms WuTarget.EveningFourTotal.paidCoefficient
#check @WuTarget.EveningFourTotal.coefficient
#print axioms WuTarget.EveningFourTotal.coefficient
#check @WuTarget.EveningFourTotal.no_double_payment
#print axioms WuTarget.EveningFourTotal.no_double_payment
#check @WuTarget.EveningFourTotal.full_cap_improves_display
#print axioms WuTarget.EveningFourTotal.full_cap_improves_display
#check @WuTarget.EveningFourTotal.joint_pair_payment_le_core
#print axioms WuTarget.EveningFourTotal.joint_pair_payment_le_core
#check @WuTarget.EveningFourTotal.raw_paid_lt_actual
#print axioms WuTarget.EveningFourTotal.raw_paid_lt_actual
#check @WuTarget.EveningFourTotal.paid_lt_actual
#print axioms WuTarget.EveningFourTotal.paid_lt_actual
#check @WuTarget.EveningFourTotal.coefficient_le_paid
#print axioms WuTarget.EveningFourTotal.coefficient_le_paid
#check @WuTarget.EveningFourTotal.coefficient_lt_actual
#print axioms WuTarget.EveningFourTotal.coefficient_lt_actual
#check @WuTarget.EveningFourTotal.netGain_bounds
#print axioms WuTarget.EveningFourTotal.netGain_bounds
#check @WuTarget.EveningFourTotal.coefficient_bounds
#print axioms WuTarget.EveningFourTotal.coefficient_bounds
#check @WuTarget.EveningFourTotal.certificate_gap_bounds
#print axioms WuTarget.EveningFourTotal.certificate_gap_bounds
#check @WuTarget.EveningFourTotal.ordinary_P2
#print axioms WuTarget.EveningFourTotal.ordinary_P2
#check @WuTarget.EveningFourTotal.ordinary_P2_display
#print axioms WuTarget.EveningFourTotal.ordinary_P2_display

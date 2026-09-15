import WE05MajorAcceptedTotal
import Lean
open Lean Elab Command

elab "#e05_major_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E05SixthMajor.majorLower_le_actual, `WuTarget.E05SixthMajor.original_domain_preserved,
      `WuTarget.EveningSixthTotal.net_gain_identity, `WuTarget.EveningSixthTotal.ordinary_P2_display] do
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

#e05_major_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E05Sixth.fifthLogTerm
#print axioms WuTarget.E05Sixth.fifthLogTerm
#check @WuTarget.E05Sixth.fifth_gap_derivative
#print axioms WuTarget.E05Sixth.fifth_gap_derivative
#check @WuTarget.E05Sixth.log_fifth_lower
#print axioms WuTarget.E05Sixth.log_fifth_lower
#check @WuTarget.E05Sixth.weighted_power_decreasing
#print axioms WuTarget.E05Sixth.weighted_power_decreasing
#check @WuTarget.E05Sixth.denominatorCap
#print axioms WuTarget.E05Sixth.denominatorCap
#check @WuTarget.E05Sixth.correctionKernel
#print axioms WuTarget.E05Sixth.correctionKernel
#check @WuTarget.E05Sixth.correctionInner
#print axioms WuTarget.E05Sixth.correctionInner
#check @WuTarget.E05Sixth.sixthCredit
#print axioms WuTarget.E05Sixth.sixthCredit
#check @WuTarget.E05Sixth.denominatorCap_pos
#print axioms WuTarget.E05Sixth.denominatorCap_pos
#check @WuTarget.E05Sixth.denominator_bound
#print axioms WuTarget.E05Sixth.denominator_bound
#check @WuTarget.E05Sixth.fifth_kernel_identity
#print axioms WuTarget.E05Sixth.fifth_kernel_identity
#check @WuTarget.E05Sixth.corrected_kernel_le_log
#print axioms WuTarget.E05Sixth.corrected_kernel_le_log
#check @WuTarget.E05Sixth.correction_inner_ftc
#print axioms WuTarget.E05Sixth.correction_inner_ftc
#check @WuTarget.E05Sixth.correction_outer_ftc
#print axioms WuTarget.E05Sixth.correction_outer_ftc
#check @WuTarget.E05Sixth.corrected_inner_le_log
#print axioms WuTarget.E05Sixth.corrected_inner_le_log
#check @WuTarget.E05Sixth.endpoint_add_credit_le_log
#print axioms WuTarget.E05Sixth.endpoint_add_credit_le_log
#check @WuTarget.E05Sixth.newSixth_add_credit_le_log
#print axioms WuTarget.E05Sixth.newSixth_add_credit_le_log
#check @WuTarget.E05Sixth.newSixth_add_credit_le_actual
#print axioms WuTarget.E05Sixth.newSixth_add_credit_le_actual
#check @WuTarget.E05Sixth.sixthCredit_exact
#print axioms WuTarget.E05Sixth.sixthCredit_exact
#check @WuTarget.E05Sixth.sixthCredit_bounds
#print axioms WuTarget.E05Sixth.sixthCredit_bounds
#check @WuTarget.E05Sixth.ordinaryCredit
#print axioms WuTarget.E05Sixth.ordinaryCredit
#check @WuTarget.E05Sixth.ordinaryCredit_eq
#print axioms WuTarget.E05Sixth.ordinaryCredit_eq
#check @WuTarget.E05Sixth.ordinaryCredit_bounds
#print axioms WuTarget.E05Sixth.ordinaryCredit_bounds
#check @WuTarget.E05Sixth.sixthLower
#print axioms WuTarget.E05Sixth.sixthLower
#check @WuTarget.E05Sixth.sixthLower_exact
#print axioms WuTarget.E05Sixth.sixthLower_exact
#check @WuTarget.E05Sixth.sixthLower_bounds
#print axioms WuTarget.E05Sixth.sixthLower_bounds
#check @WuTarget.E05Sixth.baseline_strictly_preserved
#print axioms WuTarget.E05Sixth.baseline_strictly_preserved
#check @WuTarget.E05Sixth.fixed_parameters
#print axioms WuTarget.E05Sixth.fixed_parameters
#check @WuTarget.E05Sixth.old_certificate_reused
#print axioms WuTarget.E05Sixth.old_certificate_reused
#check @WuTarget.E05Sixth.actual_sixth_lower
#print axioms WuTarget.E05Sixth.actual_sixth_lower
#check @WuTarget.E05Sixth.actual_new_income
#print axioms WuTarget.E05Sixth.actual_new_income
#check @WuTarget.E05Sixth.actual_rational_floor
#print axioms WuTarget.E05Sixth.actual_rational_floor
#check @WuTarget.E05Sixth.actual_sixth_remainder_nonnegative
#print axioms WuTarget.E05Sixth.actual_sixth_remainder_nonnegative
#check @WuTarget.E05Sixth.sixth_net_identity
#print axioms WuTarget.E05Sixth.sixth_net_identity
#check @WuTarget.E05Sixth.coefficientWithSixth
#print axioms WuTarget.E05Sixth.coefficientWithSixth
#check @WuTarget.E05Sixth.full_terminal_identity
#print axioms WuTarget.E05Sixth.full_terminal_identity
#check @WuTarget.E05Sixth.full_terminal_lower
#print axioms WuTarget.E05Sixth.full_terminal_lower
#check @WuTarget.E05Sixth.full_terminal_net_identity
#print axioms WuTarget.E05Sixth.full_terminal_net_identity
#check @WuTarget.E05Sixth.full_terminal_new_income
#print axioms WuTarget.E05Sixth.full_terminal_new_income
#check @WuTarget.E05Sixth.recurrence_unspent
#print axioms WuTarget.E05Sixth.recurrence_unspent
#check @WuTarget.E05SixthMajor.seventhLogTerm
#print axioms WuTarget.E05SixthMajor.seventhLogTerm
#check @WuTarget.E05SixthMajor.seventh_gap_derivative
#print axioms WuTarget.E05SixthMajor.seventh_gap_derivative
#check @WuTarget.E05SixthMajor.log_seventh_lower
#print axioms WuTarget.E05SixthMajor.log_seventh_lower
#check @WuTarget.E05SixthMajor.fifth_product_max
#print axioms WuTarget.E05SixthMajor.fifth_product_max
#check @WuTarget.E05SixthMajor.z0
#print axioms WuTarget.E05SixthMajor.z0
#check @WuTarget.E05SixthMajor.innerDenom1
#print axioms WuTarget.E05SixthMajor.innerDenom1
#check @WuTarget.E05SixthMajor.innerDenom2
#print axioms WuTarget.E05SixthMajor.innerDenom2
#check @WuTarget.E05SixthMajor.fixed_positive
#print axioms WuTarget.E05SixthMajor.fixed_positive
#check @WuTarget.E05SixthMajor.S_derivative
#print axioms WuTarget.E05SixthMajor.S_derivative
#check @WuTarget.E05SixthMajor.S_antitone
#print axioms WuTarget.E05SixthMajor.S_antitone
#check @WuTarget.E05SixthMajor.S_lower
#print axioms WuTarget.E05SixthMajor.S_lower
#check @WuTarget.E05SixthMajor.innerRate
#print axioms WuTarget.E05SixthMajor.innerRate
#check @WuTarget.E05SixthMajor.innerCorrection
#print axioms WuTarget.E05SixthMajor.innerCorrection
#check @WuTarget.E05SixthMajor.innerCredit
#print axioms WuTarget.E05SixthMajor.innerCredit
#check @WuTarget.E05SixthMajor.ratio_fifth
#print axioms WuTarget.E05SixthMajor.ratio_fifth
#check @WuTarget.E05SixthMajor.inner_denominators
#print axioms WuTarget.E05SixthMajor.inner_denominators
#check @WuTarget.E05SixthMajor.inner_correction_le_gaps
#print axioms WuTarget.E05SixthMajor.inner_correction_le_gaps
#check @WuTarget.E05SixthMajor.inner_correction_paid
#print axioms WuTarget.E05SixthMajor.inner_correction_paid
#check @WuTarget.E05SixthMajor.inner_correction_ftc
#print axioms WuTarget.E05SixthMajor.inner_correction_ftc
#check @WuTarget.E05SixthMajor.strengthened_denominator
#print axioms WuTarget.E05SixthMajor.strengthened_denominator
#check @WuTarget.E05SixthMajor.eighth_denominator
#print axioms WuTarget.E05SixthMajor.eighth_denominator
#check @WuTarget.E05SixthMajor.densityCorrection
#print axioms WuTarget.E05SixthMajor.densityCorrection
#check @WuTarget.E05SixthMajor.correction_le_terms
#print axioms WuTarget.E05SixthMajor.correction_le_terms
#check @WuTarget.E05SixthMajor.seventh_kernel_identity
#print axioms WuTarget.E05SixthMajor.seventh_kernel_identity
#check @WuTarget.E05SixthMajor.density_correction_paid
#print axioms WuTarget.E05SixthMajor.density_correction_paid
#check @WuTarget.E05SixthMajor.densityInner
#print axioms WuTarget.E05SixthMajor.densityInner
#check @WuTarget.E05SixthMajor.fifthExtraCredit
#print axioms WuTarget.E05SixthMajor.fifthExtraCredit
#check @WuTarget.E05SixthMajor.seventhCredit
#print axioms WuTarget.E05SixthMajor.seventhCredit
#check @WuTarget.E05SixthMajor.density_inner_ftc
#print axioms WuTarget.E05SixthMajor.density_inner_ftc
#check @WuTarget.E05SixthMajor.density_outer_ftc
#print axioms WuTarget.E05SixthMajor.density_outer_ftc
#check @WuTarget.E05SixthMajor.outerCredit
#print axioms WuTarget.E05SixthMajor.outerCredit
#check @WuTarget.E05SixthMajor.endpoint_payment
#print axioms WuTarget.E05SixthMajor.endpoint_payment
#check @WuTarget.E05SixthMajor.full_inner_payment
#print axioms WuTarget.E05SixthMajor.full_inner_payment
#check @WuTarget.E05SixthMajor.full_endpoint_payment
#print axioms WuTarget.E05SixthMajor.full_endpoint_payment
#check @WuTarget.E05SixthMajor.newCredit
#print axioms WuTarget.E05SixthMajor.newCredit
#check @WuTarget.E05SixthMajor.majorLower
#print axioms WuTarget.E05SixthMajor.majorLower
#check @WuTarget.E05SixthMajor.majorLower_le_log
#print axioms WuTarget.E05SixthMajor.majorLower_le_log
#check @WuTarget.E05SixthMajor.majorLower_le_actual
#print axioms WuTarget.E05SixthMajor.majorLower_le_actual
#check @WuTarget.E05SixthMajor.target_arithmetic
#print axioms WuTarget.E05SixthMajor.target_arithmetic
#check @WuTarget.E05SixthMajor.target_paid_locally
#print axioms WuTarget.E05SixthMajor.target_paid_locally
#check @WuTarget.E05SixthMajor.netOrdinaryCredit
#print axioms WuTarget.E05SixthMajor.netOrdinaryCredit
#check @WuTarget.E05SixthMajor.displayCredit
#print axioms WuTarget.E05SixthMajor.displayCredit
#check @WuTarget.E05SixthMajor.fullCoefficient
#print axioms WuTarget.E05SixthMajor.fullCoefficient
#check @WuTarget.E05SixthMajor.displayedCoefficient
#print axioms WuTarget.E05SixthMajor.displayedCoefficient
#check @WuTarget.E05SixthMajor.strict_target_arithmetic
#print axioms WuTarget.E05SixthMajor.strict_target_arithmetic
#check @WuTarget.E05SixthMajor.majorLower_above_target
#print axioms WuTarget.E05SixthMajor.majorLower_above_target
#check @WuTarget.E05SixthMajor.newCredit_positive
#print axioms WuTarget.E05SixthMajor.newCredit_positive
#check @WuTarget.E05SixthMajor.netOrdinaryCredit_lower
#print axioms WuTarget.E05SixthMajor.netOrdinaryCredit_lower
#check @WuTarget.E05SixthMajor.displayCredit_bounds
#print axioms WuTarget.E05SixthMajor.displayCredit_bounds
#check @WuTarget.E05SixthMajor.displayCredit_exact
#print axioms WuTarget.E05SixthMajor.displayCredit_exact
#check @WuTarget.E05SixthMajor.correction_no_double_payment
#print axioms WuTarget.E05SixthMajor.correction_no_double_payment
#check @WuTarget.E05SixthMajor.first_round_net_identity
#print axioms WuTarget.E05SixthMajor.first_round_net_identity
#check @WuTarget.E05SixthMajor.actual_remaining_identity
#print axioms WuTarget.E05SixthMajor.actual_remaining_identity
#check @WuTarget.E05SixthMajor.actual_remaining_nonnegative
#print axioms WuTarget.E05SixthMajor.actual_remaining_nonnegative
#check @WuTarget.E05SixthMajor.fullCoefficient_le_actual
#print axioms WuTarget.E05SixthMajor.fullCoefficient_le_actual
#check @WuTarget.E05SixthMajor.full_signed_net_identity
#print axioms WuTarget.E05SixthMajor.full_signed_net_identity
#check @WuTarget.E05SixthMajor.displayed_signed_net_identity
#print axioms WuTarget.E05SixthMajor.displayed_signed_net_identity
#check @WuTarget.E05SixthMajor.displayed_slack_identity
#print axioms WuTarget.E05SixthMajor.displayed_slack_identity
#check @WuTarget.E05SixthMajor.ordinary_P2_full
#print axioms WuTarget.E05SixthMajor.ordinary_P2_full
#check @WuTarget.E05SixthMajor.ordinary_P2_display
#print axioms WuTarget.E05SixthMajor.ordinary_P2_display
#check @WuTarget.E05SixthMajor.original_domain_preserved
#print axioms WuTarget.E05SixthMajor.original_domain_preserved
#check @WuTarget.E05SixthMajor.recurrence_not_spent
#print axioms WuTarget.E05SixthMajor.recurrence_not_spent
#check @WuTarget.E05SixthMajor.actual_sixth_target
#print axioms WuTarget.E05SixthMajor.actual_sixth_target
#check @WuTarget.E05SixthMajor.original_log_target
#print axioms WuTarget.E05SixthMajor.original_log_target
#check @WuTarget.E05SixthMajor.actual_net_improvement
#print axioms WuTarget.E05SixthMajor.actual_net_improvement
#check @WuTarget.EveningSixthTotal.netGain
#print axioms WuTarget.EveningSixthTotal.netGain
#check @WuTarget.EveningSixthTotal.base
#print axioms WuTarget.EveningSixthTotal.base
#check @WuTarget.EveningSixthTotal.coefficient
#print axioms WuTarget.EveningSixthTotal.coefficient
#check @WuTarget.EveningSixthTotal.net_gain_identity
#print axioms WuTarget.EveningSixthTotal.net_gain_identity
#check @WuTarget.EveningSixthTotal.base_le_residual
#print axioms WuTarget.EveningSixthTotal.base_le_residual
#check @WuTarget.EveningSixthTotal.coefficient_identity
#print axioms WuTarget.EveningSixthTotal.coefficient_identity
#check @WuTarget.EveningSixthTotal.coefficient_lt_actual
#print axioms WuTarget.EveningSixthTotal.coefficient_lt_actual
#check @WuTarget.EveningSixthTotal.netGain_bounds
#print axioms WuTarget.EveningSixthTotal.netGain_bounds
#check @WuTarget.EveningSixthTotal.coefficient_bounds
#print axioms WuTarget.EveningSixthTotal.coefficient_bounds
#check @WuTarget.EveningSixthTotal.certificate_gap_bounds
#print axioms WuTarget.EveningSixthTotal.certificate_gap_bounds
#check @WuTarget.EveningSixthTotal.ordinary_P2
#print axioms WuTarget.EveningSixthTotal.ordinary_P2
#check @WuTarget.EveningSixthTotal.ordinary_P2_display
#print axioms WuTarget.EveningSixthTotal.ordinary_P2_display

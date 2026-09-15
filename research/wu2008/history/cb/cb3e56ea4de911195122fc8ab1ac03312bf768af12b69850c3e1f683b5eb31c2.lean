import WE09JointMainMajorRoot
import Lean
open Lean Elab Command

elab "#we09majorparentaudit_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E09JointMainMajor.aggregatePayment_le_actual, `WuTarget.E09JointMainMajor.target_lower, `WuTarget.E09JointMainMajor.new_w11_le_actual_core, `WuTarget.E09JointMainMajor.ordinary_P2] do
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

#we09majorparentaudit_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E09JointMainMajor.lowerLog
#print axioms WuTarget.E09JointMainMajor.lowerLog
#check @WuTarget.E09JointMainMajor.upperLog
#print axioms WuTarget.E09JointMainMajor.upperLog
#check @WuTarget.E09JointMainMajor.lower_gap_derivative
#print axioms WuTarget.E09JointMainMajor.lower_gap_derivative
#check @WuTarget.E09JointMainMajor.upper_gap_derivative
#print axioms WuTarget.E09JointMainMajor.upper_gap_derivative
#check @WuTarget.E09JointMainMajor.log_lower
#print axioms WuTarget.E09JointMainMajor.log_lower
#check @WuTarget.E09JointMainMajor.log_upper
#print axioms WuTarget.E09JointMainMajor.log_upper
#check @WuTarget.E09JointMainMajor.logPayment
#print axioms WuTarget.E09JointMainMajor.logPayment
#check @WuTarget.E09JointMainMajor.logPayment_le_credit
#print axioms WuTarget.E09JointMainMajor.logPayment_le_credit
#check @WuTarget.E09JointMainMajor.logPayment_gain
#print axioms WuTarget.E09JointMainMajor.logPayment_gain
#check @WuTarget.E09JointMainMajor.log_three_upper
#print axioms WuTarget.E09JointMainMajor.log_three_upper
#check @WuTarget.E09JointMainMajor.log_tangent_quadratic
#print axioms WuTarget.E09JointMainMajor.log_tangent_quadratic
#check @WuTarget.E09JointMainMajor.curvaturePolynomial
#print axioms WuTarget.E09JointMainMajor.curvaturePolynomial
#check @WuTarget.E09JointMainMajor.variable_curvature
#print axioms WuTarget.E09JointMainMajor.variable_curvature
#check @WuTarget.E09JointMainMajor.curvaturePrimitive
#print axioms WuTarget.E09JointMainMajor.curvaturePrimitive
#check @WuTarget.E09JointMainMajor.curvatureSlope
#print axioms WuTarget.E09JointMainMajor.curvatureSlope
#check @WuTarget.E09JointMainMajor.curvaturePrimitive_derivative
#print axioms WuTarget.E09JointMainMajor.curvaturePrimitive_derivative
#check @WuTarget.E09JointMainMajor.curvatureSlope_derivative
#print axioms WuTarget.E09JointMainMajor.curvatureSlope_derivative
#check @WuTarget.E09JointMainMajor.correctedUpper
#print axioms WuTarget.E09JointMainMajor.correctedUpper
#check @WuTarget.E09JointMainMajor.correctedDensity
#print axioms WuTarget.E09JointMainMajor.correctedDensity
#check @WuTarget.E09JointMainMajor.correctedUpper_derivative
#print axioms WuTarget.E09JointMainMajor.correctedUpper_derivative
#check @WuTarget.E09JointMainMajor.correctedDensity_derivative
#print axioms WuTarget.E09JointMainMajor.correctedDensity_derivative
#check @WuTarget.E09JointMainMajor.correctedDensity_monotone
#print axioms WuTarget.E09JointMainMajor.correctedDensity_monotone
#check @WuTarget.E09JointMainMajor.correctedUpper_convex
#print axioms WuTarget.E09JointMainMajor.correctedUpper_convex
#check @WuTarget.E09JointMainMajor.chordDefect
#print axioms WuTarget.E09JointMainMajor.chordDefect
#check @WuTarget.E09JointMainMajor.variable_chord_defect
#print axioms WuTarget.E09JointMainMajor.variable_chord_defect
#check @WuTarget.E09JointMainMajor.upperFour
#print axioms WuTarget.E09JointMainMajor.upperFour
#check @WuTarget.E09JointMainMajor.upperFive
#print axioms WuTarget.E09JointMainMajor.upperFive
#check @WuTarget.E09JointMainMajor.upperFour_paid
#print axioms WuTarget.E09JointMainMajor.upperFour_paid
#check @WuTarget.E09JointMainMajor.upperFive_paid
#print axioms WuTarget.E09JointMainMajor.upperFive_paid
#check @WuTarget.E09JointMainMajor.middleSurplus
#print axioms WuTarget.E09JointMainMajor.middleSurplus
#check @WuTarget.E09JointMainMajor.middle_pointwise
#print axioms WuTarget.E09JointMainMajor.middle_pointwise
#check @WuTarget.E09JointMainMajor.middleGain
#print axioms WuTarget.E09JointMainMajor.middleGain
#check @WuTarget.E09JointMainMajor.middle_gain_paid
#print axioms WuTarget.E09JointMainMajor.middle_gain_paid
#check @WuTarget.E09JointMainMajor.polePolynomial
#print axioms WuTarget.E09JointMainMajor.polePolynomial
#check @WuTarget.E09JointMainMajor.polePrimitive
#print axioms WuTarget.E09JointMainMajor.polePrimitive
#check @WuTarget.E09JointMainMajor.polePrimitive_zero
#print axioms WuTarget.E09JointMainMajor.polePrimitive_zero
#check @WuTarget.E09JointMainMajor.polePrimitive_succ
#print axioms WuTarget.E09JointMainMajor.polePrimitive_succ
#check @WuTarget.E09JointMainMajor.polePrimitive_derivative
#print axioms WuTarget.E09JointMainMajor.polePrimitive_derivative
#check @WuTarget.E09JointMainMajor.middleCoordinate
#print axioms WuTarget.E09JointMainMajor.middleCoordinate
#check @WuTarget.E09JointMainMajor.middlePole
#print axioms WuTarget.E09JointMainMajor.middlePole
#check @WuTarget.E09JointMainMajor.weightedMonomialPrimitive
#print axioms WuTarget.E09JointMainMajor.weightedMonomialPrimitive
#check @WuTarget.E09JointMainMajor.weightedMonomial_derivative
#print axioms WuTarget.E09JointMainMajor.weightedMonomial_derivative
#check @WuTarget.E09JointMainMajor.monomialEndpoint
#print axioms WuTarget.E09JointMainMajor.monomialEndpoint
#check @WuTarget.E09JointMainMajor.weightedMonomial_ftc
#print axioms WuTarget.E09JointMainMajor.weightedMonomial_ftc
#check @WuTarget.E09JointMainMajor.middleCoefficients
#print axioms WuTarget.E09JointMainMajor.middleCoefficients
#check @WuTarget.E09JointMainMajor.middle_polynomial
#print axioms WuTarget.E09JointMainMajor.middle_polynomial
#check @WuTarget.E09JointMainMajor.middleGain_ftc
#print axioms WuTarget.E09JointMainMajor.middleGain_ftc
#check @WuTarget.E09JointMainMajor.middleLogA
#print axioms WuTarget.E09JointMainMajor.middleLogA
#check @WuTarget.E09JointMainMajor.middleLogB
#print axioms WuTarget.E09JointMainMajor.middleLogB
#check @WuTarget.E09JointMainMajor.middleRational
#print axioms WuTarget.E09JointMainMajor.middleRational
#check @WuTarget.E09JointMainMajor.middle_collection
#print axioms WuTarget.E09JointMainMajor.middle_collection
#check @WuTarget.E09JointMainMajor.signedLog
#print axioms WuTarget.E09JointMainMajor.signedLog
#check @WuTarget.E09JointMainMajor.signedLog_le
#print axioms WuTarget.E09JointMainMajor.signedLog_le
#check @WuTarget.E09JointMainMajor.middlePayment
#print axioms WuTarget.E09JointMainMajor.middlePayment
#check @WuTarget.E09JointMainMajor.middlePayment_le_gain
#print axioms WuTarget.E09JointMainMajor.middlePayment_le_gain
#check @WuTarget.E09JointMainMajor.middlePayment_pos
#print axioms WuTarget.E09JointMainMajor.middlePayment_pos
#check @WuTarget.E09JointMainMajor.log_lower_quadratic
#print axioms WuTarget.E09JointMainMajor.log_lower_quadratic
#check @WuTarget.E09JointMainMajor.initial_upper_quadratic
#print axioms WuTarget.E09JointMainMajor.initial_upper_quadratic
#check @WuTarget.E09JointMainMajor.lower_delayed_upper
#print axioms WuTarget.E09JointMainMajor.lower_delayed_upper
#check @WuTarget.E09JointMainMajor.log_three_cubic
#print axioms WuTarget.E09JointMainMajor.log_three_cubic
#check @WuTarget.E09JointMainMajor.logThreeCap
#print axioms WuTarget.E09JointMainMajor.logThreeCap
#check @WuTarget.E09JointMainMajor.highA0
#print axioms WuTarget.E09JointMainMajor.highA0
#check @WuTarget.E09JointMainMajor.highA1
#print axioms WuTarget.E09JointMainMajor.highA1
#check @WuTarget.E09JointMainMajor.highA2
#print axioms WuTarget.E09JointMainMajor.highA2
#check @WuTarget.E09JointMainMajor.highA3
#print axioms WuTarget.E09JointMainMajor.highA3
#check @WuTarget.E09JointMainMajor.highDensity
#print axioms WuTarget.E09JointMainMajor.highDensity
#check @WuTarget.E09JointMainMajor.highIncrement
#print axioms WuTarget.E09JointMainMajor.highIncrement
#check @WuTarget.E09JointMainMajor.logThreeCap_paid
#print axioms WuTarget.E09JointMainMajor.logThreeCap_paid
#check @WuTarget.E09JointMainMajor.delayed_density_upper
#print axioms WuTarget.E09JointMainMajor.delayed_density_upper
#check @WuTarget.E09JointMainMajor.highIncrement_derivative
#print axioms WuTarget.E09JointMainMajor.highIncrement_derivative
#check @WuTarget.E09JointMainMajor.upper_delayed_high
#print axioms WuTarget.E09JointMainMajor.upper_delayed_high
#check @WuTarget.E09JointMainMajor.highSurplus
#print axioms WuTarget.E09JointMainMajor.highSurplus
#check @WuTarget.E09JointMainMajor.high_pointwise
#print axioms WuTarget.E09JointMainMajor.high_pointwise
#check @WuTarget.E09JointMainMajor.highGain
#print axioms WuTarget.E09JointMainMajor.highGain
#check @WuTarget.E09JointMainMajor.high_gain_paid
#print axioms WuTarget.E09JointMainMajor.high_gain_paid
#check @WuTarget.E09JointMainMajor.weightedMonomial_high_derivative
#print axioms WuTarget.E09JointMainMajor.weightedMonomial_high_derivative
#check @WuTarget.E09JointMainMajor.highMonomialEndpoint
#print axioms WuTarget.E09JointMainMajor.highMonomialEndpoint
#check @WuTarget.E09JointMainMajor.weightedMonomial_high_ftc
#print axioms WuTarget.E09JointMainMajor.weightedMonomial_high_ftc
#check @WuTarget.E09JointMainMajor.highCoefficients
#print axioms WuTarget.E09JointMainMajor.highCoefficients
#check @WuTarget.E09JointMainMajor.high_polynomial
#print axioms WuTarget.E09JointMainMajor.high_polynomial
#check @WuTarget.E09JointMainMajor.highGain_ftc
#print axioms WuTarget.E09JointMainMajor.highGain_ftc
#check @WuTarget.E09JointMainMajor.highLogA
#print axioms WuTarget.E09JointMainMajor.highLogA
#check @WuTarget.E09JointMainMajor.highLogB
#print axioms WuTarget.E09JointMainMajor.highLogB
#check @WuTarget.E09JointMainMajor.highRational
#print axioms WuTarget.E09JointMainMajor.highRational
#check @WuTarget.E09JointMainMajor.high_collection
#print axioms WuTarget.E09JointMainMajor.high_collection
#check @WuTarget.E09JointMainMajor.highPayment
#print axioms WuTarget.E09JointMainMajor.highPayment
#check @WuTarget.E09JointMainMajor.highPayment_le_gain
#print axioms WuTarget.E09JointMainMajor.highPayment_le_gain
#check @WuTarget.E09JointMainMajor.highPayment_pos
#print axioms WuTarget.E09JointMainMajor.highPayment_pos
#check @WuTarget.E09JointMainMajor.aggregatePayment
#print axioms WuTarget.E09JointMainMajor.aggregatePayment
#check @WuTarget.E09JointMainMajor.aggregate_shared_paid
#print axioms WuTarget.E09JointMainMajor.aggregate_shared_paid
#check @WuTarget.E09JointMainMajor.aggregatePayment_le_actual
#print axioms WuTarget.E09JointMainMajor.aggregatePayment_le_actual
#check @WuTarget.E09JointMainMajor.aggregate_strict
#print axioms WuTarget.E09JointMainMajor.aggregate_strict
#check @WuTarget.E09JointMainMajor.aggregate_target
#print axioms WuTarget.E09JointMainMajor.aggregate_target
#check @WuTarget.E09JointMainMajor.payment
#print axioms WuTarget.E09JointMainMajor.payment
#check @WuTarget.E09JointMainMajor.netGain
#print axioms WuTarget.E09JointMainMajor.netGain
#check @WuTarget.E09JointMainMajor.target_lower
#print axioms WuTarget.E09JointMainMajor.target_lower
#check @WuTarget.E09JointMainMajor.payment_le_actual
#print axioms WuTarget.E09JointMainMajor.payment_le_actual
#check @WuTarget.E09JointMainMajor.payment_strict
#print axioms WuTarget.E09JointMainMajor.payment_strict
#check @WuTarget.E09JointMainMajor.netGain_exact
#print axioms WuTarget.E09JointMainMajor.netGain_exact
#check @WuTarget.E09JointMainMajor.netGain_bounds
#print axioms WuTarget.E09JointMainMajor.netGain_bounds
#check @WuTarget.E09JointMainMajor.netGain_pos
#print axioms WuTarget.E09JointMainMajor.netGain_pos
#check @WuTarget.E09JointMainMajor.payment_net
#print axioms WuTarget.E09JointMainMajor.payment_net
#check @WuTarget.E09JointMainMajor.normalized_net
#print axioms WuTarget.E09JointMainMajor.normalized_net
#check @WuTarget.E09JointMainMajor.no_double_payment
#print axioms WuTarget.E09JointMainMajor.no_double_payment
#check @WuTarget.E09JointMainMajor.complete_remaining_identity
#print axioms WuTarget.E09JointMainMajor.complete_remaining_identity
#check @WuTarget.E09JointMainMajor.remaining_components_nonneg
#print axioms WuTarget.E09JointMainMajor.remaining_components_nonneg
#check @WuTarget.E09JointMainMajor.selectedCredit
#print axioms WuTarget.E09JointMainMajor.selectedCredit
#check @WuTarget.E09JointMainMajor.selectedCredit_le_actual
#print axioms WuTarget.E09JointMainMajor.selectedCredit_le_actual
#check @WuTarget.E09JointMainMajor.previous_selected_le
#print axioms WuTarget.E09JointMainMajor.previous_selected_le
#check @WuTarget.E09JointMainMajor.new_w11_le_actual_core
#print axioms WuTarget.E09JointMainMajor.new_w11_le_actual_core
#check @WuTarget.E09JointMainMajor.paidCoefficient
#print axioms WuTarget.E09JointMainMajor.paidCoefficient
#check @WuTarget.E09JointMainMajor.paid_net
#print axioms WuTarget.E09JointMainMajor.paid_net
#check @WuTarget.E09JointMainMajor.paid_strict
#print axioms WuTarget.E09JointMainMajor.paid_strict
#check @WuTarget.E09JointMainMajor.paid_exact
#print axioms WuTarget.E09JointMainMajor.paid_exact
#check @WuTarget.E09JointMainMajor.paid_lt_actual
#print axioms WuTarget.E09JointMainMajor.paid_lt_actual
#check @WuTarget.E09JointMainMajor.ordinary_P2_paid
#print axioms WuTarget.E09JointMainMajor.ordinary_P2_paid
#check @WuTarget.E09JointMainMajor.ordinary_P2
#print axioms WuTarget.E09JointMainMajor.ordinary_P2

import WE07FifthClassicalRoot
import Lean
open Lean Elab Command

elab "#fifth_classical_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.FifthClassicalClosure.final_target, `WuTarget.FifthClassicalClosure.fifth_main_original_integral,
      `WuTarget.FifthClassicalClosure.net_accounting_identity, `WuTarget.FifthClassicalClosure.enhanced_P2_paid] do
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

#fifth_classical_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.FifthClassicalClosure.logCenter
#print axioms WuTarget.FifthClassicalClosure.logCenter
#check @WuTarget.FifthClassicalClosure.shapeSlope
#print axioms WuTarget.FifthClassicalClosure.shapeSlope
#check @WuTarget.FifthClassicalClosure.shapeCurvature
#print axioms WuTarget.FifthClassicalClosure.shapeCurvature
#check @WuTarget.FifthClassicalClosure.scalarShape
#print axioms WuTarget.FifthClassicalClosure.scalarShape
#check @WuTarget.FifthClassicalClosure.logRemainder
#print axioms WuTarget.FifthClassicalClosure.logRemainder
#check @WuTarget.FifthClassicalClosure.log_remainder_derivative
#print axioms WuTarget.FifthClassicalClosure.log_remainder_derivative
#check @WuTarget.FifthClassicalClosure.log_remainder_nonneg
#print axioms WuTarget.FifthClassicalClosure.log_remainder_nonneg
#check @WuTarget.FifthClassicalClosure.log_center_lower
#print axioms WuTarget.FifthClassicalClosure.log_center_lower
#check @WuTarget.FifthClassicalClosure.scalar_shape_lower
#print axioms WuTarget.FifthClassicalClosure.scalar_shape_lower
#check @WuTarget.FifthClassicalClosure.momentKernel
#print axioms WuTarget.FifthClassicalClosure.momentKernel
#check @WuTarget.FifthClassicalClosure.momentInner
#print axioms WuTarget.FifthClassicalClosure.momentInner
#check @WuTarget.FifthClassicalClosure.momentPrimitive
#print axioms WuTarget.FifthClassicalClosure.momentPrimitive
#check @WuTarget.FifthClassicalClosure.moment_inner_integrable
#print axioms WuTarget.FifthClassicalClosure.moment_inner_integrable
#check @WuTarget.FifthClassicalClosure.moment_inner_ftc
#print axioms WuTarget.FifthClassicalClosure.moment_inner_ftc
#check @WuTarget.FifthClassicalClosure.moment_primitive_derivative
#print axioms WuTarget.FifthClassicalClosure.moment_primitive_derivative
#check @WuTarget.FifthClassicalClosure.quadraticKernel
#print axioms WuTarget.FifthClassicalClosure.quadraticKernel
#check @WuTarget.FifthClassicalClosure.quadraticInner
#print axioms WuTarget.FifthClassicalClosure.quadraticInner
#check @WuTarget.FifthClassicalClosure.quadraticPrimitive
#print axioms WuTarget.FifthClassicalClosure.quadraticPrimitive
#check @WuTarget.FifthClassicalClosure.quadraticEndpoint
#print axioms WuTarget.FifthClassicalClosure.quadraticEndpoint
#check @WuTarget.FifthClassicalClosure.quadratic_kernel_literal
#print axioms WuTarget.FifthClassicalClosure.quadratic_kernel_literal
#check @WuTarget.FifthClassicalClosure.affine_inner_integrable
#print axioms WuTarget.FifthClassicalClosure.affine_inner_integrable
#check @WuTarget.FifthClassicalClosure.quadratic_inner_integrable
#print axioms WuTarget.FifthClassicalClosure.quadratic_inner_integrable
#check @WuTarget.FifthClassicalClosure.quadratic_inner_ftc
#print axioms WuTarget.FifthClassicalClosure.quadratic_inner_ftc
#check @WuTarget.FifthClassicalClosure.quadratic_primitive_derivative
#print axioms WuTarget.FifthClassicalClosure.quadratic_primitive_derivative
#check @WuTarget.FifthClassicalClosure.quadratic_outer_integrable
#print axioms WuTarget.FifthClassicalClosure.quadratic_outer_integrable
#check @WuTarget.FifthClassicalClosure.quadratic_triangle_ftc
#print axioms WuTarget.FifthClassicalClosure.quadratic_triangle_ftc
#check @WuTarget.FifthClassicalClosure.quadratic_endpoint_comparison
#print axioms WuTarget.FifthClassicalClosure.quadratic_endpoint_comparison
#check @WuTarget.FifthClassicalClosure.sumCenter
#print axioms WuTarget.FifthClassicalClosure.sumCenter
#check @WuTarget.FifthClassicalClosure.shapeConstant
#print axioms WuTarget.FifthClassicalClosure.shapeConstant
#check @WuTarget.FifthClassicalClosure.shapeLinear
#print axioms WuTarget.FifthClassicalClosure.shapeLinear
#check @WuTarget.FifthClassicalClosure.shapeSquare
#print axioms WuTarget.FifthClassicalClosure.shapeSquare
#check @WuTarget.FifthClassicalClosure.endpointLinear
#print axioms WuTarget.FifthClassicalClosure.endpointLinear
#check @WuTarget.FifthClassicalClosure.ratioLower
#print axioms WuTarget.FifthClassicalClosure.ratioLower
#check @WuTarget.FifthClassicalClosure.rationalLower
#print axioms WuTarget.FifthClassicalClosure.rationalLower
#check @WuTarget.FifthClassicalClosure.shape_kernel_identity
#print axioms WuTarget.FifthClassicalClosure.shape_kernel_identity
#check @WuTarget.FifthClassicalClosure.original_kernel_lower
#print axioms WuTarget.FifthClassicalClosure.original_kernel_lower
#check @WuTarget.FifthClassicalClosure.original_integral_lower
#print axioms WuTarget.FifthClassicalClosure.original_integral_lower
#check @WuTarget.FifthClassicalClosure.ratio_lower
#print axioms WuTarget.FifthClassicalClosure.ratio_lower
#check @WuTarget.FifthClassicalClosure.rational_signs
#print axioms WuTarget.FifthClassicalClosure.rational_signs
#check @WuTarget.FifthClassicalClosure.rational_lower_le_endpoint
#print axioms WuTarget.FifthClassicalClosure.rational_lower_le_endpoint
#check @WuTarget.FifthClassicalClosure.rational_lower
#print axioms WuTarget.FifthClassicalClosure.rational_lower
#check @WuTarget.FifthClassicalClosure.target_le_rational
#print axioms WuTarget.FifthClassicalClosure.target_le_rational
#check @WuTarget.FifthClassicalClosure.fifth_main_lower
#print axioms WuTarget.FifthClassicalClosure.fifth_main_lower
#check @WuTarget.FifthClassicalClosure.netCredit
#print axioms WuTarget.FifthClassicalClosure.netCredit
#check @WuTarget.FifthClassicalClosure.creditedCoefficient
#print axioms WuTarget.FifthClassicalClosure.creditedCoefficient
#check @WuTarget.FifthClassicalClosure.net_credit_exact
#print axioms WuTarget.FifthClassicalClosure.net_credit_exact
#check @WuTarget.FifthClassicalClosure.net_credit_pos
#print axioms WuTarget.FifthClassicalClosure.net_credit_pos
#check @WuTarget.FifthClassicalClosure.net_credit_lower
#print axioms WuTarget.FifthClassicalClosure.net_credit_lower
#check @WuTarget.FifthClassicalClosure.net_accounting_identity
#print axioms WuTarget.FifthClassicalClosure.net_accounting_identity
#check @WuTarget.FifthClassicalClosure.exact_block_replacement
#print axioms WuTarget.FifthClassicalClosure.exact_block_replacement
#check @WuTarget.FifthClassicalClosure.block_lower_replaced_retained
#print axioms WuTarget.FifthClassicalClosure.block_lower_replaced_retained
#check @WuTarget.FifthClassicalClosure.block_lower_replaced
#print axioms WuTarget.FifthClassicalClosure.block_lower_replaced
#check @WuTarget.FifthClassicalClosure.block_with_retained_slack
#print axioms WuTarget.FifthClassicalClosure.block_with_retained_slack
#check @WuTarget.FifthClassicalClosure.credited_lt_previous
#print axioms WuTarget.FifthClassicalClosure.credited_lt_previous
#check @WuTarget.FifthClassicalClosure.credited_lt_actual
#print axioms WuTarget.FifthClassicalClosure.credited_lt_actual
#check @WuTarget.FifthClassicalClosure.credited_identity
#print axioms WuTarget.FifthClassicalClosure.credited_identity
#check @WuTarget.FifthClassicalClosure.enhanced_P2_paid
#print axioms WuTarget.FifthClassicalClosure.enhanced_P2_paid
#check @WuTarget.FifthClassicalClosure.fifth_main_original_integral
#print axioms WuTarget.FifthClassicalClosure.fifth_main_original_integral
#check @WuTarget.FifthClassicalClosure.final_target
#print axioms WuTarget.FifthClassicalClosure.final_target
#check @WuTarget.FifthClassicalClosure.final_original_target
#print axioms WuTarget.FifthClassicalClosure.final_original_target

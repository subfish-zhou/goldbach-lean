import WE07AcceptedBudget
import Lean
open Lean Elab Command

elab "#e07_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E07Fifth.final_lower, `WuTarget.E07Fifth.net_accounting_identity,
      `WuTarget.E07Accepted.scalar_ordinary_P2, `WuTarget.E07Accepted.refined_target] do
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

#e07_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E07Fifth.profileBase
#print axioms WuTarget.E07Fifth.profileBase
#check @WuTarget.E07Fifth.profileY
#print axioms WuTarget.E07Fifth.profileY
#check @WuTarget.E07Fifth.polynomialMinorant
#print axioms WuTarget.E07Fifth.polynomialMinorant
#check @WuTarget.E07Fifth.polynomialPrimitive
#print axioms WuTarget.E07Fifth.polynomialPrimitive
#check @WuTarget.E07Fifth.netCredit
#print axioms WuTarget.E07Fifth.netCredit
#check @WuTarget.E07Fifth.capped_parameter_upper
#print axioms WuTarget.E07Fifth.capped_parameter_upper
#check @WuTarget.E07Fifth.profileY_nonneg
#print axioms WuTarget.E07Fifth.profileY_nonneg
#check @WuTarget.E07Fifth.profileY_lower
#print axioms WuTarget.E07Fifth.profileY_lower
#check @WuTarget.E07Fifth.polynomial_integrable
#print axioms WuTarget.E07Fifth.polynomial_integrable
#check @WuTarget.E07Fifth.polynomial_le_original
#print axioms WuTarget.E07Fifth.polynomial_le_original
#check @WuTarget.E07Fifth.polynomial_derivative
#print axioms WuTarget.E07Fifth.polynomial_derivative
#check @WuTarget.E07Fifth.polynomial_integral
#print axioms WuTarget.E07Fifth.polynomial_integral
#check @WuTarget.E07Fifth.polynomial_gain_lower
#print axioms WuTarget.E07Fifth.polynomial_gain_lower
#check @WuTarget.E07Fifth.polynomial_gain_exact
#print axioms WuTarget.E07Fifth.polynomial_gain_exact
#check @WuTarget.E07Fifth.net_identity
#print axioms WuTarget.E07Fifth.net_identity
#check @WuTarget.E07Fifth.netCredit_pos
#print axioms WuTarget.E07Fifth.netCredit_pos
#check @WuTarget.E07Fifth.fifth_balance_lower
#print axioms WuTarget.E07Fifth.fifth_balance_lower
#check @WuTarget.E07Fifth.final_lower
#print axioms WuTarget.E07Fifth.final_lower
#check @WuTarget.E07Fifth.final_positive
#print axioms WuTarget.E07Fifth.final_positive
#check @WuTarget.E07Fifth.paid_exact
#print axioms WuTarget.E07Fifth.paid_exact
#check @WuTarget.E07Fifth.net_amount_exact
#print axioms WuTarget.E07Fifth.net_amount_exact
#check @WuTarget.E07Fifth.net_accounting_identity
#print axioms WuTarget.E07Fifth.net_accounting_identity
#check @WuTarget.E07Fifth.original_profile_identity
#print axioms WuTarget.E07Fifth.original_profile_identity
#check @WuTarget.E07Fifth.original_profile_balance_lower
#print axioms WuTarget.E07Fifth.original_profile_balance_lower
#check @WuTarget.E07Accepted.fifthBalance
#print axioms WuTarget.E07Accepted.fifthBalance
#check @WuTarget.E07Accepted.otherRemaining
#print axioms WuTarget.E07Accepted.otherRemaining
#check @WuTarget.E07Accepted.fifth_paid
#print axioms WuTarget.E07Accepted.fifth_paid
#check @WuTarget.E07Accepted.display_paid
#print axioms WuTarget.E07Accepted.display_paid
#check @WuTarget.E07Accepted.remaining_lower
#print axioms WuTarget.E07Accepted.remaining_lower
#check @WuTarget.E07Accepted.scalar_paid_le
#print axioms WuTarget.E07Accepted.scalar_paid_le
#check @WuTarget.E07Accepted.scalar_ordinary_P2
#print axioms WuTarget.E07Accepted.scalar_ordinary_P2
#check @WuTarget.E07Accepted.refined_target
#print axioms WuTarget.E07Accepted.refined_target

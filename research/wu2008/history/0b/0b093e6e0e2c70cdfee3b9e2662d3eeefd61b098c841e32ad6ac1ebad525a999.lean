import WE06AcceptedBudget
import Lean
open Lean Elab Command

elab "#e06_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E06Second.second_slack_lower, `WuTarget.E06Second.retained_slack_split,
      `WuTarget.EveningSecondAccepted.remaining_lower, `WuTarget.EveningSecondAccepted.refined_target] do
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

#e06_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E06Second.kernel_lower
#print axioms WuTarget.E06Second.kernel_lower
#check @WuTarget.E06Second.linear_integral
#print axioms WuTarget.E06Second.linear_integral
#check @WuTarget.E06Second.inner_lower
#print axioms WuTarget.E06Second.inner_lower
#check @WuTarget.E06Second.outer_kernel_lower
#print axioms WuTarget.E06Second.outer_kernel_lower
#check @WuTarget.E06Second.quadratic_integral
#print axioms WuTarget.E06Second.quadratic_integral
#check @WuTarget.E06Second.C_lower
#print axioms WuTarget.E06Second.C_lower
#check @WuTarget.E06Second.original_double_integral
#print axioms WuTarget.E06Second.original_double_integral
#check @WuTarget.E06Second.second_slack_lower
#print axioms WuTarget.E06Second.second_slack_lower
#check @WuTarget.E06Second.second_slack_strict
#print axioms WuTarget.E06Second.second_slack_strict
#check @WuTarget.E06Second.double_integral_lower
#print axioms WuTarget.E06Second.double_integral_lower
#check @WuTarget.E06Second.second_credit_positive
#print axioms WuTarget.E06Second.second_credit_positive
#check @WuTarget.E06Second.second_remainder_nonneg
#print axioms WuTarget.E06Second.second_remainder_nonneg
#check @WuTarget.E06Second.recurrence_normalization
#print axioms WuTarget.E06Second.recurrence_normalization
#check @WuTarget.E06Second.second_main_unpaid_lower
#print axioms WuTarget.E06Second.second_main_unpaid_lower
#check @WuTarget.E06Second.second_main_normalized_lower
#print axioms WuTarget.E06Second.second_main_normalized_lower
#check @WuTarget.E06Second.retained_slack_split
#print axioms WuTarget.E06Second.retained_slack_split
#check @WuTarget.E06Second.retained_slack_net_identity
#print axioms WuTarget.E06Second.retained_slack_net_identity
#check @WuTarget.E06Second.retained_slack_lower_with_fifth_unchanged
#print axioms WuTarget.E06Second.retained_slack_lower_with_fifth_unchanged
#check @WuTarget.E06Second.retained_slack_lower
#print axioms WuTarget.E06Second.retained_slack_lower
#check @WuTarget.E06Second.retained_slack_strict
#print axioms WuTarget.E06Second.retained_slack_strict
#check @WuTarget.EveningSecondAccepted.tableGain
#print axioms WuTarget.EveningSecondAccepted.tableGain
#check @WuTarget.EveningSecondAccepted.certifiedCredits
#print axioms WuTarget.EveningSecondAccepted.certifiedCredits
#check @WuTarget.EveningSecondAccepted.otherRemaining
#print axioms WuTarget.EveningSecondAccepted.otherRemaining
#check @WuTarget.EveningSecondAccepted.remaining_lower
#print axioms WuTarget.EveningSecondAccepted.remaining_lower
#check @WuTarget.EveningSecondAccepted.scalar_paid_le
#print axioms WuTarget.EveningSecondAccepted.scalar_paid_le
#check @WuTarget.EveningSecondAccepted.ordinary_P2
#print axioms WuTarget.EveningSecondAccepted.ordinary_P2
#check @WuTarget.EveningSecondAccepted.refined_target
#print axioms WuTarget.EveningSecondAccepted.refined_target

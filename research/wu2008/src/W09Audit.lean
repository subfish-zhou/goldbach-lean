import W09ActualV2
import Lean

namespace WuTarget.W09
open Lean Elab Command

#check @seedQ
#print axioms seedQ
#check @seed
#print axioms seed
#check @increment
#print axioms increment
#check @forcingSlack
#print axioms forcingSlack
#check @curve_increment_paid
#print axioms curve_increment_paid
#check @remaining_increment_zero
#print axioms remaining_increment_zero
#check @remaining_increment_one
#print axioms remaining_increment_one
#check @remaining_increment_two
#print axioms remaining_increment_two
#check @first_increment_zero
#print axioms first_increment_zero
#check @first_increment_one
#print axioms first_increment_one
#check @first_increment_two
#print axioms first_increment_two
#check @first_increment_three
#print axioms first_increment_three
#check @seed_eq_publication_add_increment
#print axioms seed_eq_publication_add_increment
#check @increment_le_half_slack
#print axioms increment_le_half_slack
#check @increment_pos
#print axioms increment_pos
#check @forcingSlack_pos
#print axioms forcingSlack_pos
#check @seed_strictly_stronger
#print axioms seed_strictly_stronger
#check @seed_nonneg
#print axioms seed_nonneg
#check @terminal_seed
#print axioms terminal_seed
#check @terminal_slack
#print axioms terminal_slack
#check @paidCost
#print axioms paidCost
#check @forcingSlack_coupled_succ
#print axioms forcingSlack_coupled_succ
#check @forcingSlack_first
#print axioms forcingSlack_first
#check @paidCost_coupled_succ
#print axioms paidCost_coupled_succ
#check @paidCost_first
#print axioms paidCost_first
#check @terminal_cost
#print axioms terminal_cost
#check @curve_debit_eq
#print axioms curve_debit_eq
#check @remaining_debit_eq
#print axioms remaining_debit_eq
#check @actual_with_loss
#print axioms actual_with_loss
#check @radius
#print axioms radius
#check @radius_pos
#print axioms radius_pos
#check @radius_cap
#print axioms radius_cap
#check @debit_le_half_slack
#print axioms debit_le_half_slack
#check @commonRadius
#print axioms commonRadius
#check @commonRadius_pos
#print axioms commonRadius_pos
#check @commonRadius_le
#print axioms commonRadius_le
#check @commonRadius_cap
#print axioms commonRadius_cap
#check @common_debit_le_half_slack
#print axioms common_debit_le_half_slack
#check @seed_feedback_actual
#print axioms seed_feedback_actual
#check @seed_actual_same_delta
#print axioms seed_actual_same_delta
#check @seed_le_actual
#print axioms seed_le_actual
#check @seed_paid_update
#print axioms seed_paid_update
#check @seed_twentyone_actual
#print axioms seed_twentyone_actual

#print seedQ
#print radius
#print commonRadius

run_cmd do
  let env := (← getEnv).setExporting false
  let mut todo : Array Name := #[`WuTarget.W09.seed_actual_same_delta,
    `WuTarget.W09.seed_paid_update, `WuTarget.W09.seed_twentyone_actual,
    `WuTarget.W09.seed_strictly_stronger, `WuTarget.W09.seed_nonneg, `WuTarget.W09.terminal_seed]
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !seen.contains n then
      seen := seen.insert n
      if seen.size > 200000 then throwError "W09 dependency audit cap exceeded"
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
  let banned : Array Name := #[`NineFeedbackStrength.originalH, `FeedbackLimit.Ainf,
    `NineFeedbackStrength.subsolution_le_Ainf, `NineFeedbackStrength.actual_comparison_same_delta,
    `sorryAx, `Lean.ofReduceBool]
  let found := banned.filter (fun n => seen.contains n)
  let out ← IO.getStdout
  out.putStrLn <| (Json.mkObj [("visited", toJson seen.size),
    ("missing", toJson (missing.map Name.toString)),
    ("forbiddenDependencies", toJson (found.map Name.toString))]).compress
  out.flush
  unless found.isEmpty && missing.isEmpty do throwError "W09 dependency audit failed"

end WuTarget.W09

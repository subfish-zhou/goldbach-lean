import WE09AcceptedBudget
import Lean
open Lean Elab Command

elab "#e09_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E09JointMain.low_gain_paid, `WuTarget.E09JointMain.payment_le_actual,
      `WuTarget.EveningJointMainAccepted.paid_lt_actual, `WuTarget.EveningJointMainAccepted.refined_target] do
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

#e09_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E09JointMain.jointGain
#print axioms WuTarget.E09JointMain.jointGain
#check @WuTarget.E09JointMain.surplusDensity
#print axioms WuTarget.E09JointMain.surplusDensity
#check @WuTarget.E09JointMain.lowDensity
#print axioms WuTarget.E09JointMain.lowDensity
#check @WuTarget.E09JointMain.lowDensity_exact
#print axioms WuTarget.E09JointMain.lowDensity_exact
#check @WuTarget.E09JointMain.low_density_paid
#print axioms WuTarget.E09JointMain.low_density_paid
#check @WuTarget.E09JointMain.surplus_ftc
#print axioms WuTarget.E09JointMain.surplus_ftc
#check @WuTarget.E09JointMain.low_ftc
#print axioms WuTarget.E09JointMain.low_ftc
#check @WuTarget.E09JointMain.low_gain_paid
#print axioms WuTarget.E09JointMain.low_gain_paid
#check @WuTarget.E09JointMain.jointGain_exact
#print axioms WuTarget.E09JointMain.jointGain_exact
#check @WuTarget.E09JointMain.jointGain_pos
#print axioms WuTarget.E09JointMain.jointGain_pos
#check @WuTarget.E09JointMain.shared_recovery_paid
#print axioms WuTarget.E09JointMain.shared_recovery_paid
#check @WuTarget.E09JointMain.correlated_gain_le_actual
#print axioms WuTarget.E09JointMain.correlated_gain_le_actual
#check @WuTarget.E09JointMain.payment
#print axioms WuTarget.E09JointMain.payment
#check @WuTarget.E09JointMain.netGain
#print axioms WuTarget.E09JointMain.netGain
#check @WuTarget.E09JointMain.payment_exact
#print axioms WuTarget.E09JointMain.payment_exact
#check @WuTarget.E09JointMain.netGain_exact
#print axioms WuTarget.E09JointMain.netGain_exact
#check @WuTarget.E09JointMain.netGain_pos
#print axioms WuTarget.E09JointMain.netGain_pos
#check @WuTarget.E09JointMain.payment_net
#print axioms WuTarget.E09JointMain.payment_net
#check @WuTarget.E09JointMain.payment_strict
#print axioms WuTarget.E09JointMain.payment_strict
#check @WuTarget.E09JointMain.payment_le_actual
#print axioms WuTarget.E09JointMain.payment_le_actual
#check @WuTarget.E09JointMain.actual_normalized_payment
#print axioms WuTarget.E09JointMain.actual_normalized_payment
#check @WuTarget.E09JointMain.correlated_remaining_exact
#print axioms WuTarget.E09JointMain.correlated_remaining_exact
#check @WuTarget.E09JointMain.payment_remaining_exact
#print axioms WuTarget.E09JointMain.payment_remaining_exact
#check @WuTarget.E09JointMain.selectedCredit
#print axioms WuTarget.E09JointMain.selectedCredit
#check @WuTarget.E09JointMain.selectedCredit_le_actual
#print axioms WuTarget.E09JointMain.selectedCredit_le_actual
#check @WuTarget.E09JointMain.previous_selected_le
#print axioms WuTarget.E09JointMain.previous_selected_le
#check @WuTarget.E09JointMain.payment_le_selected
#print axioms WuTarget.E09JointMain.payment_le_selected
#check @WuTarget.E09JointMain.first_lower_transport
#print axioms WuTarget.E09JointMain.first_lower_transport
#check @WuTarget.E09JointMain.shifted_w11_le_actual_core
#print axioms WuTarget.E09JointMain.shifted_w11_le_actual_core
#check @WuTarget.E09JointMain.shifted_w13_lt_actual
#print axioms WuTarget.E09JointMain.shifted_w13_lt_actual
#check @WuTarget.E09JointMain.paidCoefficient
#print axioms WuTarget.E09JointMain.paidCoefficient
#check @WuTarget.E09JointMain.remainingCoefficient
#print axioms WuTarget.E09JointMain.remainingCoefficient
#check @WuTarget.E09JointMain.paid_net
#print axioms WuTarget.E09JointMain.paid_net
#check @WuTarget.E09JointMain.remaining_net
#print axioms WuTarget.E09JointMain.remaining_net
#check @WuTarget.E09JointMain.paid_strict
#print axioms WuTarget.E09JointMain.paid_strict
#check @WuTarget.E09JointMain.paid_lt_actual
#print axioms WuTarget.E09JointMain.paid_lt_actual
#check @WuTarget.E09JointMain.paid_exact
#print axioms WuTarget.E09JointMain.paid_exact
#check @WuTarget.E09JointMain.ordinary_P2_paid
#print axioms WuTarget.E09JointMain.ordinary_P2_paid
#check @WuTarget.E09JointMain.paid_threshold_iff
#print axioms WuTarget.E09JointMain.paid_threshold_iff
#check @WuTarget.E09JointMain.old_remaining_threshold_iff
#print axioms WuTarget.E09JointMain.old_remaining_threshold_iff
#check @WuTarget.E09JointMain.refined_target
#print axioms WuTarget.E09JointMain.refined_target
#check @WuTarget.E09JointMain.actual_rational_payment
#print axioms WuTarget.E09JointMain.actual_rational_payment
#check @WuTarget.E09JointMain.actual_coefficient_gain
#print axioms WuTarget.E09JointMain.actual_coefficient_gain
#check @WuTarget.EveningJointMainAccepted.tableGain
#print axioms WuTarget.EveningJointMainAccepted.tableGain
#check @WuTarget.EveningJointMainAccepted.otherRemaining
#print axioms WuTarget.EveningJointMainAccepted.otherRemaining
#check @WuTarget.EveningJointMainAccepted.certifiedCredits
#print axioms WuTarget.EveningJointMainAccepted.certifiedCredits
#check @WuTarget.EveningJointMainAccepted.paidCoefficient
#print axioms WuTarget.EveningJointMainAccepted.paidCoefficient
#check @WuTarget.EveningJointMainAccepted.paid_lt_actual
#print axioms WuTarget.EveningJointMainAccepted.paid_lt_actual
#check @WuTarget.EveningJointMainAccepted.scalar_paid_le
#print axioms WuTarget.EveningJointMainAccepted.scalar_paid_le
#check @WuTarget.EveningJointMainAccepted.ordinary_P2
#print axioms WuTarget.EveningJointMainAccepted.ordinary_P2
#check @WuTarget.EveningJointMainAccepted.refined_target
#print axioms WuTarget.EveningJointMainAccepted.refined_target

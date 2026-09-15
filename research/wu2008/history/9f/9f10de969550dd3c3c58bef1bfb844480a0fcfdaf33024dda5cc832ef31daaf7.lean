import WE02RankOneAcceptedBudget
import Lean
open Lean Elab Command

elab "#e02_rankone_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E02JointCredit.sigma_le_addedMatrix, `WuTarget.E02JointCredit.rankOne_actual_jointCredit_lower,
      `WuTarget.EveningRankOneAccepted.upgrade_identity, `WuTarget.EveningRankOneAccepted.refined_target] do
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

#e02_rankone_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E02JointCredit.rankOneSigmaMass
#print axioms WuTarget.E02JointCredit.rankOneSigmaMass
#check @WuTarget.E02JointCredit.rankOneRows
#print axioms WuTarget.E02JointCredit.rankOneRows
#check @WuTarget.E02JointCredit.rankOneSigmaMass_nonneg
#print axioms WuTarget.E02JointCredit.rankOneSigmaMass_nonneg
#check @WuTarget.E02JointCredit.rankOneRows_nonneg
#print axioms WuTarget.E02JointCredit.rankOneRows_nonneg
#check @WuTarget.E02JointCredit.sigma_le_addedMatrix
#print axioms WuTarget.E02JointCredit.sigma_le_addedMatrix
#check @WuTarget.E02JointCredit.rankOne_apply
#print axioms WuTarget.E02JointCredit.rankOne_apply
#check @WuTarget.E02JointCredit.rankOneRows_le_difference
#print axioms WuTarget.E02JointCredit.rankOneRows_le_difference
#check @WuTarget.E02JointCredit.rankOne_remainder_eq
#print axioms WuTarget.E02JointCredit.rankOne_remainder_eq
#check @WuTarget.E02JointCredit.rankOne_remainder_nonneg
#print axioms WuTarget.E02JointCredit.rankOne_remainder_nonneg
#check @WuTarget.E02JointCredit.rankOne_rational_payment
#print axioms WuTarget.E02JointCredit.rankOne_rational_payment
#check @WuTarget.E02JointCredit.rankOneSigmaMass_exact
#print axioms WuTarget.E02JointCredit.rankOneSigmaMass_exact
#check @WuTarget.E02JointCredit.rankOneRowLower
#print axioms WuTarget.E02JointCredit.rankOneRowLower
#check @WuTarget.E02JointCredit.rankOneRowLower_pos
#print axioms WuTarget.E02JointCredit.rankOneRowLower_pos
#check @WuTarget.E02JointCredit.rankOneRowLower_le
#print axioms WuTarget.E02JointCredit.rankOneRowLower_le
#check @WuTarget.E02JointCredit.rankOneRowLower_le_difference
#print axioms WuTarget.E02JointCredit.rankOneRowLower_le_difference
#check @WuTarget.E02JointCredit.rankOneQTransfer
#print axioms WuTarget.E02JointCredit.rankOneQTransfer
#check @WuTarget.E02JointCredit.rankOneQTransfer_cast
#print axioms WuTarget.E02JointCredit.rankOneQTransfer_cast
#check @WuTarget.E02JointCredit.rankOneQTransfer_le
#print axioms WuTarget.E02JointCredit.rankOneQTransfer_le
#check @WuTarget.E02JointCredit.rankOneTransferLower
#print axioms WuTarget.E02JointCredit.rankOneTransferLower
#check @WuTarget.E02JointCredit.rankOneTransferLower_pos
#print axioms WuTarget.E02JointCredit.rankOneTransferLower_pos
#check @WuTarget.E02JointCredit.rankOneTransferLower_le_q
#print axioms WuTarget.E02JointCredit.rankOneTransferLower_le_q
#check @WuTarget.E02JointCredit.rankOneTransferLower_le_rational
#print axioms WuTarget.E02JointCredit.rankOneTransferLower_le_rational
#check @WuTarget.E02JointCredit.rankOneTransferLower_le_actual
#print axioms WuTarget.E02JointCredit.rankOneTransferLower_le_actual
#check @WuTarget.E02JointCredit.rankOneWeightedPayment
#print axioms WuTarget.E02JointCredit.rankOneWeightedPayment
#check @WuTarget.E02JointCredit.rankOneWeightedPayment_le
#print axioms WuTarget.E02JointCredit.rankOneWeightedPayment_le
#check @WuTarget.E02JointCredit.rankOneAmount
#print axioms WuTarget.E02JointCredit.rankOneAmount
#check @WuTarget.E02JointCredit.rankOneAmount_paid
#print axioms WuTarget.E02JointCredit.rankOneAmount_paid
#check @WuTarget.E02JointCredit.rankOneAmount_le_jointCredit
#print axioms WuTarget.E02JointCredit.rankOneAmount_le_jointCredit
#check @WuTarget.E02JointCredit.rankOneAmount_improves_old
#print axioms WuTarget.E02JointCredit.rankOneAmount_improves_old
#check @WuTarget.E02JointCredit.rankOneAmount_preserves_old
#print axioms WuTarget.E02JointCredit.rankOneAmount_preserves_old
#check @WuTarget.E02JointCredit.rankOneUpgrade
#print axioms WuTarget.E02JointCredit.rankOneUpgrade
#check @WuTarget.E02JointCredit.rankOneUpgrade_pos
#print axioms WuTarget.E02JointCredit.rankOneUpgrade_pos
#check @WuTarget.E02JointCredit.rankOneUpgrade_lower
#print axioms WuTarget.E02JointCredit.rankOneUpgrade_lower
#check @WuTarget.E02JointCredit.rankOneUpgrade_paid
#print axioms WuTarget.E02JointCredit.rankOneUpgrade_paid
#check @WuTarget.E02JointCredit.rankOne_net_identity
#print axioms WuTarget.E02JointCredit.rankOne_net_identity
#check @WuTarget.E02JointCredit.rankOne_net_remainder_nonneg
#print axioms WuTarget.E02JointCredit.rankOne_net_remainder_nonneg
#check @WuTarget.E02JointCredit.rankOne_actual_jointCredit_lower
#print axioms WuTarget.E02JointCredit.rankOne_actual_jointCredit_lower
#check @WuTarget.E02JointCredit.rankOne_actual_lowGain_difference_lower
#print axioms WuTarget.E02JointCredit.rankOne_actual_lowGain_difference_lower
#check @WuTarget.E02JointCredit.rankOne_actual_coefficient_gain
#print axioms WuTarget.E02JointCredit.rankOne_actual_coefficient_gain
#check @WuTarget.E02JointCredit.rankOne_paid_budget_gain
#print axioms WuTarget.E02JointCredit.rankOne_paid_budget_gain
#check @WuTarget.E02JointCredit.rankOne_remaining_budget_gain
#print axioms WuTarget.E02JointCredit.rankOne_remaining_budget_gain
#check @WuTarget.E02JointCredit.rankOneUpgrade_exact
#print axioms WuTarget.E02JointCredit.rankOneUpgrade_exact
#check @WuTarget.E02JointCredit.rankOne_remaining_net_identity
#print axioms WuTarget.E02JointCredit.rankOne_remaining_net_identity
#check @WuTarget.E02JointCredit.rankOne_coefficient_net_identity
#print axioms WuTarget.E02JointCredit.rankOne_coefficient_net_identity
#check @WuTarget.E02JointCredit.ordinary_P2_rankOne_amount
#print axioms WuTarget.E02JointCredit.ordinary_P2_rankOne_amount
#check @WuTarget.E02JointCredit.ordinary_P2_rankOne_budget
#print axioms WuTarget.E02JointCredit.ordinary_P2_rankOne_budget
#check @WuTarget.EveningRankOneAccepted.tableGain
#print axioms WuTarget.EveningRankOneAccepted.tableGain
#check @WuTarget.EveningRankOneAccepted.otherRemaining
#print axioms WuTarget.EveningRankOneAccepted.otherRemaining
#check @WuTarget.EveningRankOneAccepted.certifiedCredits
#print axioms WuTarget.EveningRankOneAccepted.certifiedCredits
#check @WuTarget.EveningRankOneAccepted.upgrade_identity
#print axioms WuTarget.EveningRankOneAccepted.upgrade_identity
#check @WuTarget.EveningRankOneAccepted.remaining_lower
#print axioms WuTarget.EveningRankOneAccepted.remaining_lower
#check @WuTarget.EveningRankOneAccepted.scalar_paid_le
#print axioms WuTarget.EveningRankOneAccepted.scalar_paid_le
#check @WuTarget.EveningRankOneAccepted.ordinary_P2
#print axioms WuTarget.EveningRankOneAccepted.ordinary_P2
#check @WuTarget.EveningRankOneAccepted.refined_target
#print axioms WuTarget.EveningRankOneAccepted.refined_target

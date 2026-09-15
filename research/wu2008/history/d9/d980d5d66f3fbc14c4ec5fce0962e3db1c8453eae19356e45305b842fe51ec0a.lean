import WE03AcceptedBudget
import Lean
open Lean Elab Command

elab "#e03_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E03Sigma.sigma_integral_identity, `WuTarget.E03Sigma.table_weighted_plus_credit,
      `WuTarget.EveningAccepted.remaining_lower, `WuTarget.EveningAccepted.refined_target] do
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

#e03_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E03Sigma.logTerm
#print axioms WuTarget.E03Sigma.logTerm
#check @WuTarget.E03Sigma.logTerm_le
#print axioms WuTarget.E03Sigma.logTerm_le
#check @WuTarget.E03Sigma.sigmaTerm_nonneg
#print axioms WuTarget.E03Sigma.sigmaTerm_nonneg
#check @WuTarget.E03Sigma.sigmaStart
#print axioms WuTarget.E03Sigma.sigmaStart
#check @WuTarget.E03Sigma.weightLower
#print axioms WuTarget.E03Sigma.weightLower
#check @WuTarget.E03Sigma.weightLower_nonneg
#print axioms WuTarget.E03Sigma.weightLower_nonneg
#check @WuTarget.E03Sigma.weightLower_le
#print axioms WuTarget.E03Sigma.weightLower_le
#check @WuTarget.E03Sigma.amplitudeLower
#print axioms WuTarget.E03Sigma.amplitudeLower
#check @WuTarget.E03Sigma.amplitudeLower_eq
#print axioms WuTarget.E03Sigma.amplitudeLower_eq
#check @WuTarget.E03Sigma.amplitudeLower_pos
#print axioms WuTarget.E03Sigma.amplitudeLower_pos
#check @WuTarget.E03Sigma.amplitudeLower_le
#print axioms WuTarget.E03Sigma.amplitudeLower_le
#check @WuTarget.E03Sigma.sum11_eq
#print axioms WuTarget.E03Sigma.sum11_eq
#check @WuTarget.E03Sigma.sum12_eq
#print axioms WuTarget.E03Sigma.sum12_eq
#check @WuTarget.E03Sigma.weightLower_eq
#print axioms WuTarget.E03Sigma.weightLower_eq
#check @WuTarget.E03Sigma.weightedLower
#print axioms WuTarget.E03Sigma.weightedLower
#check @WuTarget.E03Sigma.weightedLower_eq
#print axioms WuTarget.E03Sigma.weightedLower_eq
#check @WuTarget.E03Sigma.weightedLower_pos
#print axioms WuTarget.E03Sigma.weightedLower_pos
#check @WuTarget.E03Sigma.exactGain
#print axioms WuTarget.E03Sigma.exactGain
#check @WuTarget.E03Sigma.ordinaryCredit
#print axioms WuTarget.E03Sigma.ordinaryCredit
#check @WuTarget.E03Sigma.exactGain_eq
#print axioms WuTarget.E03Sigma.exactGain_eq
#check @WuTarget.E03Sigma.ordinaryCredit_pos
#print axioms WuTarget.E03Sigma.ordinaryCredit_pos
#check @WuTarget.E03Sigma.ordinaryCredit_le_exact
#print axioms WuTarget.E03Sigma.ordinaryCredit_le_exact
#check @WuTarget.E03Sigma.rationalNodes
#print axioms WuTarget.E03Sigma.rationalNodes
#check @WuTarget.E03Sigma.sigmaNodes
#print axioms WuTarget.E03Sigma.sigmaNodes
#check @WuTarget.E03Sigma.rationalGain
#print axioms WuTarget.E03Sigma.rationalGain
#check @WuTarget.E03Sigma.sigmaGain
#print axioms WuTarget.E03Sigma.sigmaGain
#check @WuTarget.E03Sigma.rationalNodes_nonneg
#print axioms WuTarget.E03Sigma.rationalNodes_nonneg
#check @WuTarget.E03Sigma.sigmaNodes_nonneg
#print axioms WuTarget.E03Sigma.sigmaNodes_nonneg
#check @WuTarget.E03Sigma.nodeGain_split
#print axioms WuTarget.E03Sigma.nodeGain_split
#check @WuTarget.E03Sigma.sigma_net_identity
#print axioms WuTarget.E03Sigma.sigma_net_identity
#check @WuTarget.E03Sigma.sigma_integral_identity
#print axioms WuTarget.E03Sigma.sigma_integral_identity
#check @WuTarget.E03Sigma.sigmaNodes_lower
#print axioms WuTarget.E03Sigma.sigmaNodes_lower
#check @WuTarget.E03Sigma.exactGain_le_sigmaGain
#print axioms WuTarget.E03Sigma.exactGain_le_sigmaGain
#check @WuTarget.E03Sigma.exactGain_le_original_difference
#print axioms WuTarget.E03Sigma.exactGain_le_original_difference
#check @WuTarget.E03Sigma.ordinaryCredit_le_original_difference
#print axioms WuTarget.E03Sigma.ordinaryCredit_le_original_difference
#check @WuTarget.E03Sigma.rationalGain_plus_exactGain
#print axioms WuTarget.E03Sigma.rationalGain_plus_exactGain
#check @WuTarget.E03Sigma.rational_weighted_plus_credit
#print axioms WuTarget.E03Sigma.rational_weighted_plus_credit
#check @WuTarget.E03Sigma.table_le_rationalNodes
#print axioms WuTarget.E03Sigma.table_le_rationalNodes
#check @WuTarget.E03Sigma.table_weighted_plus_credit
#print axioms WuTarget.E03Sigma.table_weighted_plus_credit
#check @WuTarget.E03Sigma.rationalPaidCoefficient
#print axioms WuTarget.E03Sigma.rationalPaidCoefficient
#check @WuTarget.E03Sigma.paidCoefficient_net_identity
#print axioms WuTarget.E03Sigma.paidCoefficient_net_identity
#check @WuTarget.E03Sigma.paidCoefficient_credit
#print axioms WuTarget.E03Sigma.paidCoefficient_credit
#check @WuTarget.EveningAccepted.tableGain
#print axioms WuTarget.EveningAccepted.tableGain
#check @WuTarget.EveningAccepted.certifiedCredits
#print axioms WuTarget.EveningAccepted.certifiedCredits
#check @WuTarget.EveningAccepted.otherRemaining
#print axioms WuTarget.EveningAccepted.otherRemaining
#check @WuTarget.EveningAccepted.remaining_lower
#print axioms WuTarget.EveningAccepted.remaining_lower
#check @WuTarget.EveningAccepted.scalar_paid_le
#print axioms WuTarget.EveningAccepted.scalar_paid_le
#check @WuTarget.EveningAccepted.ordinary_P2
#print axioms WuTarget.EveningAccepted.ordinary_P2
#check @WuTarget.EveningAccepted.refined_target
#print axioms WuTarget.EveningAccepted.refined_target

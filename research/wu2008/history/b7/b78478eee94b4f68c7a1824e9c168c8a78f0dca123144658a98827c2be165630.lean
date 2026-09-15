import WE08AcceptedTotal
import Lean
open Lean Elab Command

elab "#e08_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E08Debit.weightedDebit_le_tightenedCap, `WuTarget.EveningDebitTotal.base_le_residual,
      `WuTarget.EveningDebitTotal.coefficient_lt_actual, `WuTarget.EveningDebitTotal.ordinary_P2_display] do
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

#e08_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E08Debit.splitLower
#print axioms WuTarget.E08Debit.splitLower
#check @WuTarget.E08Debit.splitUpper
#print axioms WuTarget.E08Debit.splitUpper
#check @WuTarget.E08Debit.split_log
#print axioms WuTarget.E08Debit.split_log
#check @WuTarget.E08Debit.split_bounds
#print axioms WuTarget.E08Debit.split_bounds
#check @WuTarget.E08Debit.jointConstant
#print axioms WuTarget.E08Debit.jointConstant
#check @WuTarget.E08Debit.commonCoefficient
#print axioms WuTarget.E08Debit.commonCoefficient
#check @WuTarget.E08Debit.jointPacket
#print axioms WuTarget.E08Debit.jointPacket
#check @WuTarget.E08Debit.joint_collection
#print axioms WuTarget.E08Debit.joint_collection
#check @WuTarget.E08Debit.commonCoefficient_pos
#print axioms WuTarget.E08Debit.commonCoefficient_pos
#check @WuTarget.E08Debit.joint_payment
#print axioms WuTarget.E08Debit.joint_payment
#check @WuTarget.E08Debit.jointCap
#print axioms WuTarget.E08Debit.jointCap
#check @WuTarget.E08Debit.mixture_le_jointCap
#print axioms WuTarget.E08Debit.mixture_le_jointCap
#check @WuTarget.E08Debit.jointConstant_exact
#print axioms WuTarget.E08Debit.jointConstant_exact
#check @WuTarget.E08Debit.smallWeightLower
#print axioms WuTarget.E08Debit.smallWeightLower
#check @WuTarget.E08Debit.smallSlope
#print axioms WuTarget.E08Debit.smallSlope
#check @WuTarget.E08Debit.smallMomentLower
#print axioms WuTarget.E08Debit.smallMomentLower
#check @WuTarget.E08Debit.smallGain
#print axioms WuTarget.E08Debit.smallGain
#check @WuTarget.E08Debit.small_weight_lower
#print axioms WuTarget.E08Debit.small_weight_lower
#check @WuTarget.E08Debit.small_log_affine
#print axioms WuTarget.E08Debit.small_log_affine
#check @WuTarget.E08Debit.small_denominator
#print axioms WuTarget.E08Debit.small_denominator
#check @WuTarget.E08Debit.small_moment_pointwise
#print axioms WuTarget.E08Debit.small_moment_pointwise
#check @WuTarget.E08Debit.small_quadratic_integral
#print axioms WuTarget.E08Debit.small_quadratic_integral
#check @WuTarget.E08Debit.small_gain_lower
#print axioms WuTarget.E08Debit.small_gain_lower
#check @WuTarget.E08Debit.smallGain_exact
#print axioms WuTarget.E08Debit.smallGain_exact
#check @WuTarget.E08Debit.smallGain_improves
#print axioms WuTarget.E08Debit.smallGain_improves
#check @WuTarget.E08Debit.tightenedCap
#print axioms WuTarget.E08Debit.tightenedCap
#check @WuTarget.E08Debit.oldSlack
#print axioms WuTarget.E08Debit.oldSlack
#check @WuTarget.E08Debit.netGain
#print axioms WuTarget.E08Debit.netGain
#check @WuTarget.E08Debit.jointNet
#print axioms WuTarget.E08Debit.jointNet
#check @WuTarget.E08Debit.smallNet
#print axioms WuTarget.E08Debit.smallNet
#check @WuTarget.E08Debit.certifiedSlack
#print axioms WuTarget.E08Debit.certifiedSlack
#check @WuTarget.E08Debit.analyticUpper_le_tightenedCap
#print axioms WuTarget.E08Debit.analyticUpper_le_tightenedCap
#check @WuTarget.E08Debit.weightedDebit_le_tightenedCap
#print axioms WuTarget.E08Debit.weightedDebit_le_tightenedCap
#check @WuTarget.E08Debit.jointCap_exact
#print axioms WuTarget.E08Debit.jointCap_exact
#check @WuTarget.E08Debit.tightenedCap_exact
#print axioms WuTarget.E08Debit.tightenedCap_exact
#check @WuTarget.E08Debit.tightenedCap_lt
#print axioms WuTarget.E08Debit.tightenedCap_lt
#check @WuTarget.E08Debit.netGain_gt
#print axioms WuTarget.E08Debit.netGain_gt
#check @WuTarget.E08Debit.jointNet_gt
#print axioms WuTarget.E08Debit.jointNet_gt
#check @WuTarget.E08Debit.smallNet_gt
#print axioms WuTarget.E08Debit.smallNet_gt
#check @WuTarget.E08Debit.netGain_identity
#print axioms WuTarget.E08Debit.netGain_identity
#check @WuTarget.E08Debit.cap_accounting
#print axioms WuTarget.E08Debit.cap_accounting
#check @WuTarget.E08Debit.certifiedSlack_identity
#print axioms WuTarget.E08Debit.certifiedSlack_identity
#check @WuTarget.E08Debit.debitSlack_identity
#print axioms WuTarget.E08Debit.debitSlack_identity
#check @WuTarget.E08Debit.certifiedSlack_le_debitSlack
#print axioms WuTarget.E08Debit.certifiedSlack_le_debitSlack
#check @WuTarget.E08Debit.debitSlack_gt
#print axioms WuTarget.E08Debit.debitSlack_gt
#check @WuTarget.E08Debit.debitSlack_net_improvement
#print axioms WuTarget.E08Debit.debitSlack_net_improvement
#check @WuTarget.E08Debit.tightenedCap_improves_rationalUpper
#print axioms WuTarget.E08Debit.tightenedCap_improves_rationalUpper
#check @WuTarget.E08Debit.analyticUpper_lt
#print axioms WuTarget.E08Debit.analyticUpper_lt
#check @WuTarget.E08Debit.weightedDebit_lt
#print axioms WuTarget.E08Debit.weightedDebit_lt
#check @WuTarget.E08Debit.original_domains_cap
#print axioms WuTarget.E08Debit.original_domains_cap
#check @WuTarget.E08Debit.debitSlack_full_identity
#print axioms WuTarget.E08Debit.debitSlack_full_identity
#check @WuTarget.E08Debit.unpaid_residuals_nonnegative
#print axioms WuTarget.E08Debit.unpaid_residuals_nonnegative
#check @WuTarget.E08Debit.ledger_improvement
#print axioms WuTarget.E08Debit.ledger_improvement
#check @WuTarget.E08Debit.certifiedCoefficient
#print axioms WuTarget.E08Debit.certifiedCoefficient
#check @WuTarget.E08Debit.coefficient_net_identity
#print axioms WuTarget.E08Debit.coefficient_net_identity
#check @WuTarget.E08Debit.coefficient_le_paid
#print axioms WuTarget.E08Debit.coefficient_le_paid
#check @WuTarget.E08Debit.certified_ordinary_P2
#print axioms WuTarget.E08Debit.certified_ordinary_P2
#check @WuTarget.EveningDebitTotal.base
#print axioms WuTarget.EveningDebitTotal.base
#check @WuTarget.EveningDebitTotal.coefficient
#print axioms WuTarget.EveningDebitTotal.coefficient
#check @WuTarget.EveningDebitTotal.base_le_residual
#print axioms WuTarget.EveningDebitTotal.base_le_residual
#check @WuTarget.EveningDebitTotal.coefficient_identity
#print axioms WuTarget.EveningDebitTotal.coefficient_identity
#check @WuTarget.EveningDebitTotal.coefficient_lt_actual
#print axioms WuTarget.EveningDebitTotal.coefficient_lt_actual
#check @WuTarget.EveningDebitTotal.net_upper
#print axioms WuTarget.EveningDebitTotal.net_upper
#check @WuTarget.EveningDebitTotal.coefficient_bounds
#print axioms WuTarget.EveningDebitTotal.coefficient_bounds
#check @WuTarget.EveningDebitTotal.certificate_gap_bounds
#print axioms WuTarget.EveningDebitTotal.certificate_gap_bounds
#check @WuTarget.EveningDebitTotal.ordinary_P2
#print axioms WuTarget.EveningDebitTotal.ordinary_P2
#check @WuTarget.EveningDebitTotal.ordinary_P2_display
#print axioms WuTarget.EveningDebitTotal.ordinary_P2_display

import WE01CurrentTotal
import Lean
open Lean Elab Command

elab "#e01_total_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E01Baseline.remaining_strict, `WuTarget.EveningTotal.residual_exact,
      `WuTarget.EveningTotal.coefficient_bounds, `WuTarget.EveningTotal.ordinary_P2_display] do
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

#e01_total_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.E01Baseline.sixthLower
#print axioms WuTarget.E01Baseline.sixthLower
#check @WuTarget.E01Baseline.sixth_exact
#print axioms WuTarget.E01Baseline.sixth_exact
#check @WuTarget.E01Baseline.gammaLower
#print axioms WuTarget.E01Baseline.gammaLower
#check @WuTarget.E01Baseline.gamma_exact
#print axioms WuTarget.E01Baseline.gamma_exact
#check @WuTarget.E01Baseline.paymentLower
#print axioms WuTarget.E01Baseline.paymentLower
#check @WuTarget.E01Baseline.fourLower
#print axioms WuTarget.E01Baseline.fourLower
#check @WuTarget.E01Baseline.debitLower
#print axioms WuTarget.E01Baseline.debitLower
#check @WuTarget.E01Baseline.payment_exact
#print axioms WuTarget.E01Baseline.payment_exact
#check @WuTarget.E01Baseline.four_exact
#print axioms WuTarget.E01Baseline.four_exact
#check @WuTarget.E01Baseline.debit_exact
#print axioms WuTarget.E01Baseline.debit_exact
#check @WuTarget.E01Baseline.exactRemaining
#print axioms WuTarget.E01Baseline.exactRemaining
#check @WuTarget.E01Baseline.exactPaid
#print axioms WuTarget.E01Baseline.exactPaid
#check @WuTarget.E01Baseline.total_exact
#print axioms WuTarget.E01Baseline.total_exact
#check @WuTarget.E01Baseline.original_packet_exact
#print axioms WuTarget.E01Baseline.original_packet_exact
#check @WuTarget.E01Baseline.remaining_rational_bounds
#print axioms WuTarget.E01Baseline.remaining_rational_bounds
#check @WuTarget.E01Baseline.paid_rational_bounds
#print axioms WuTarget.E01Baseline.paid_rational_bounds
#check @WuTarget.E01Baseline.certificate_below_targets
#print axioms WuTarget.E01Baseline.certificate_below_targets
#check @WuTarget.E01Baseline.exact_gap_identity
#print axioms WuTarget.E01Baseline.exact_gap_identity
#check @WuTarget.E01Baseline.exact_gap_value
#print axioms WuTarget.E01Baseline.exact_gap_value
#check @WuTarget.E01Baseline.exact_gap_bounds
#print axioms WuTarget.E01Baseline.exact_gap_bounds
#check @WuTarget.E01Baseline.short_gap_identity
#print axioms WuTarget.E01Baseline.short_gap_identity
#check @WuTarget.E01Baseline.sixth_lower
#print axioms WuTarget.E01Baseline.sixth_lower
#check @WuTarget.E01Baseline.node_lower
#print axioms WuTarget.E01Baseline.node_lower
#check @WuTarget.E01Baseline.debit_strict
#print axioms WuTarget.E01Baseline.debit_strict
#check @WuTarget.E01Baseline.remaining_strict
#print axioms WuTarget.E01Baseline.remaining_strict
#check @WuTarget.E01Baseline.paid_net_identity
#print axioms WuTarget.E01Baseline.paid_net_identity
#check @WuTarget.E01Baseline.paid_strict
#print axioms WuTarget.E01Baseline.paid_strict
#check @WuTarget.E01Baseline.actual_strict
#print axioms WuTarget.E01Baseline.actual_strict
#check @WuTarget.E01Baseline.literal_baseline
#print axioms WuTarget.E01Baseline.literal_baseline
#check @WuTarget.E01Baseline.remaining_surplus_identity
#print axioms WuTarget.E01Baseline.remaining_surplus_identity
#check @WuTarget.E01Baseline.surplus_strict
#print axioms WuTarget.E01Baseline.surplus_strict
#check @WuTarget.E01Baseline.actual_gap_identity
#print axioms WuTarget.E01Baseline.actual_gap_identity
#check @WuTarget.E01Baseline.certificate_gap_is_not_actual_gap
#print axioms WuTarget.E01Baseline.certificate_gap_is_not_actual_gap
#check @WuTarget.E01Baseline.ordinary_P2_exact
#print axioms WuTarget.E01Baseline.ordinary_P2_exact
#check @WuTarget.E01Baseline.ordinary_P2_baseline
#print axioms WuTarget.E01Baseline.ordinary_P2_baseline
#check @WuTarget.EveningTotal.base
#print axioms WuTarget.EveningTotal.base
#check @WuTarget.EveningTotal.credits
#print axioms WuTarget.EveningTotal.credits
#check @WuTarget.EveningTotal.coefficient
#print axioms WuTarget.EveningTotal.coefficient
#check @WuTarget.EveningTotal.residual_exact
#print axioms WuTarget.EveningTotal.residual_exact
#check @WuTarget.EveningTotal.base_lt_residual
#print axioms WuTarget.EveningTotal.base_lt_residual
#check @WuTarget.EveningTotal.table_exact
#print axioms WuTarget.EveningTotal.table_exact
#check @WuTarget.EveningTotal.coefficient_exact
#print axioms WuTarget.EveningTotal.coefficient_exact
#check @WuTarget.EveningTotal.credits_exact
#print axioms WuTarget.EveningTotal.credits_exact
#check @WuTarget.EveningTotal.coefficient_bounds
#print axioms WuTarget.EveningTotal.coefficient_bounds
#check @WuTarget.EveningTotal.certificate_gap_bounds
#print axioms WuTarget.EveningTotal.certificate_gap_bounds
#check @WuTarget.EveningTotal.ordinary_P2
#print axioms WuTarget.EveningTotal.ordinary_P2
#check @WuTarget.EveningTotal.ordinary_P2_display
#print axioms WuTarget.EveningTotal.ordinary_P2_display

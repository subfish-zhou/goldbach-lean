import WRecoveredFirstComparison
import Lean
open Lean Elab Command

elab "#recovered_first_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.W10.firstMain_lower, `WuTarget.W10.first_actual_numeric_count,
      `WuTarget.RecoveredFirstComparison.separate_lt_current_payment, `WuTarget.RecoveredFirstComparison.max_paid_le_actual] do
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

#recovered_first_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.W10.paidFirst
#print axioms WuTarget.W10.paidFirst
#check @WuTarget.W10.firstLower
#print axioms WuTarget.W10.firstLower
#check @WuTarget.W10.firstUpper
#print axioms WuTarget.W10.firstUpper
#check @WuTarget.W10.paidFirst_bounds
#print axioms WuTarget.W10.paidFirst_bounds
#check @WuTarget.W10.complete_max_preserved
#print axioms WuTarget.W10.complete_max_preserved
#check @WuTarget.W10.guaranteed_preserved
#print axioms WuTarget.W10.guaranteed_preserved
#check @WuTarget.W10.old_first_strictly_improved
#print axioms WuTarget.W10.old_first_strictly_improved
#check @WuTarget.W10.paidFirst_exact
#print axioms WuTarget.W10.paidFirst_exact
#check @WuTarget.W10.paidFirst_le_actual
#print axioms WuTarget.W10.paidFirst_le_actual
#check @WuTarget.W10.firstMain_lower
#print axioms WuTarget.W10.firstMain_lower
#check @WuTarget.W10.first_actual_paid_count
#print axioms WuTarget.W10.first_actual_paid_count
#check @WuTarget.W10.first_actual_numeric_count
#print axioms WuTarget.W10.first_actual_numeric_count
#check @WuTarget.W10.first_weighted_count
#print axioms WuTarget.W10.first_weighted_count
#check @WuTarget.W10.mother_first_lower
#print axioms WuTarget.W10.mother_first_lower
#check @WuTarget.W10.otherNumerator
#print axioms WuTarget.W10.otherNumerator
#check @WuTarget.W10.qFirstLower
#print axioms WuTarget.W10.qFirstLower
#check @WuTarget.W10.original_mother_exact
#print axioms WuTarget.W10.original_mother_exact
#check @WuTarget.W10.original_mother_lower
#print axioms WuTarget.W10.original_mother_lower
#check @WuTarget.W10.original_mother_first_contribution
#print axioms WuTarget.W10.original_mother_first_contribution
#check @WuTarget.W10.printed_comparison
#print axioms WuTarget.W10.printed_comparison
#check @WuTarget.RecoveredFirstComparison.separateCredit
#print axioms WuTarget.RecoveredFirstComparison.separateCredit
#check @WuTarget.RecoveredFirstComparison.separate_le_actual
#print axioms WuTarget.RecoveredFirstComparison.separate_le_actual
#check @WuTarget.RecoveredFirstComparison.separate_lt_current_payment
#print axioms WuTarget.RecoveredFirstComparison.separate_lt_current_payment
#check @WuTarget.RecoveredFirstComparison.max_paid_eq_current
#print axioms WuTarget.RecoveredFirstComparison.max_paid_eq_current
#check @WuTarget.RecoveredFirstComparison.max_paid_le_actual
#print axioms WuTarget.RecoveredFirstComparison.max_paid_le_actual

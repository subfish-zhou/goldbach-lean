import WSrcFourBudgetVerified
import Lean
open Lean Elab Command

elab "#four_verified_budget_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuSource.SrcBuchstabLower.buchstab_lower56, `WuSource.FourBudgetVerified.actual_pair_gt_065, `WuSource.FourBudgetVerified.printed_pair_cannot_both_be_upper, `WuSource.FourBudgetVerified.actual_pair_bracket] do
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

#four_verified_budget_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuSource.SrcBuchstabLower.buchstab_lower56_seed
#print axioms WuSource.SrcBuchstabLower.buchstab_lower56_seed
#check @WuSource.SrcBuchstabLower.buchstab_lower56
#print axioms WuSource.SrcBuchstabLower.buchstab_lower56
#check @WuSource.SrcBuchstabLower.weighted_buchstab_lower56
#print axioms WuSource.SrcBuchstabLower.weighted_buchstab_lower56
#check @WuSource.FourBudgetVerified.source_parameters
#print axioms WuSource.FourBudgetVerified.source_parameters
#check @WuSource.FourBudgetVerified.actual_pair_lower
#print axioms WuSource.FourBudgetVerified.actual_pair_lower
#check @WuSource.FourBudgetVerified.actual_pair_gt_065
#print axioms WuSource.FourBudgetVerified.actual_pair_gt_065
#check @WuSource.FourBudgetVerified.target_065_impossible
#print axioms WuSource.FourBudgetVerified.target_065_impossible
#check @WuSource.FourBudgetVerified.printed_pair_cannot_both_be_upper
#print axioms WuSource.FourBudgetVerified.printed_pair_cannot_both_be_upper
#check @WuSource.FourBudgetVerified.actual_pair_bracket
#print axioms WuSource.FourBudgetVerified.actual_pair_bracket

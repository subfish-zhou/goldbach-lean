import WSrcFourBuchstabBridge
import Lean
open Lean Elab Command

elab "#wsrcfourparentaudit_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuSource.SrcFour.original_pair_source, `WuSource.SrcFour.original_pair_gt_target_of_lower, `WuSource.FourBuchstabAccepted.original_pair_lt_688, `WuSource.FourBuchstabAccepted.ordinary_P2] do
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

#wsrcfourparentaudit_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuSource.SrcFour.TenDomain
#print axioms WuSource.SrcFour.TenDomain
#check @WuSource.SrcFour.ElevenDomain
#print axioms WuSource.SrcFour.ElevenDomain
#check @WuSource.SrcFour.threshold
#print axioms WuSource.SrcFour.threshold
#check @WuSource.SrcFour.outerCut
#print axioms WuSource.SrcFour.outerCut
#check @WuSource.SrcFour.geometry
#print axioms WuSource.SrcFour.geometry
#check @WuSource.SrcFour.fine_iff
#print axioms WuSource.SrcFour.fine_iff
#check @WuSource.SrcFour.complement_iff
#print axioms WuSource.SrcFour.complement_iff
#check @WuSource.SrcFour.ten_fine
#print axioms WuSource.SrcFour.ten_fine
#check @WuSource.SrcFour.ten_complement_empty
#print axioms WuSource.SrcFour.ten_complement_empty
#check @WuSource.SrcFour.eleven_complement_location
#print axioms WuSource.SrcFour.eleven_complement_location
#check @WuSource.SrcFour.eleven_fine_of_outer
#print axioms WuSource.SrcFour.eleven_fine_of_outer
#check @WuSource.SrcFour.eleven_complement_nonempty
#print axioms WuSource.SrcFour.eleven_complement_nonempty
#check @WuSource.SrcFour.kernel_source_ten
#print axioms WuSource.SrcFour.kernel_source_ten
#check @WuSource.SrcFour.kernel_source_eleven
#print axioms WuSource.SrcFour.kernel_source_eleven
#check @WuSource.SrcFour.fine_kernel
#print axioms WuSource.SrcFour.fine_kernel
#check @WuSource.SrcFour.scale
#print axioms WuSource.SrcFour.scale
#check @WuSource.SrcFour.inner10_fine
#print axioms WuSource.SrcFour.inner10_fine
#check @WuSource.SrcFour.inner11_fine
#print axioms WuSource.SrcFour.inner11_fine
#check @WuSource.SrcFour.middle_fine
#print axioms WuSource.SrcFour.middle_fine
#check @WuSource.SrcFour.middle_scaled
#print axioms WuSource.SrcFour.middle_scaled
#check @WuSource.SrcFour.outer_fine
#print axioms WuSource.SrcFour.outer_fine
#check @WuSource.SrcFour.tailAmount
#print axioms WuSource.SrcFour.tailAmount
#check @WuSource.SrcFour.tailLogCap
#print axioms WuSource.SrcFour.tailLogCap
#check @WuSource.SrcFour.tailCap
#print axioms WuSource.SrcFour.tailCap
#check @WuSource.SrcFour.fineCap
#print axioms WuSource.SrcFour.fineCap
#check @WuSource.SrcFour.outerCut_pos
#print axioms WuSource.SrcFour.outerCut_pos
#check @WuSource.SrcFour.tail_log_bounds
#print axioms WuSource.SrcFour.tail_log_bounds
#check @WuSource.SrcFour.tail_exact
#print axioms WuSource.SrcFour.tail_exact
#check @WuSource.SrcFour.tail_upper
#print axioms WuSource.SrcFour.tail_upper
#check @WuSource.SrcFour.original_pair_split
#print axioms WuSource.SrcFour.original_pair_split
#check @WuSource.SrcFour.original_pair_fineCap
#print axioms WuSource.SrcFour.original_pair_fineCap
#check @WuSource.SrcFour.tailCap_nonneg
#print axioms WuSource.SrcFour.tailCap_nonneg
#check @WuSource.SrcFour.tailCap_small
#print axioms WuSource.SrcFour.tailCap_small
#check @WuSource.SrcFour.fineCap_5616_upper
#print axioms WuSource.SrcFour.fineCap_5616_upper
#check @WuSource.SrcFour.scaled_parentCap_exceeds_target
#print axioms WuSource.SrcFour.scaled_parentCap_exceeds_target
#check @WuSource.SrcFour.fineCap_5616_exceeds_target
#print axioms WuSource.SrcFour.fineCap_5616_exceeds_target
#check @WuSource.SrcFour.original_pair_5616_conditional
#print axioms WuSource.SrcFour.original_pair_5616_conditional
#check @WuSource.SrcFour.conditional_budget_difference
#print axioms WuSource.SrcFour.conditional_budget_difference
#check @WuSource.SrcFour.crossFloor
#print axioms WuSource.SrcFour.crossFloor
#check @WuSource.SrcFour.slopeFloor
#print axioms WuSource.SrcFour.slopeFloor
#check @WuSource.SrcFour.lowerCoeff
#print axioms WuSource.SrcFour.lowerCoeff
#check @WuSource.SrcFour.lower_constants
#print axioms WuSource.SrcFour.lower_constants
#check @WuSource.SrcFour.lowerCoeff_pos
#print axioms WuSource.SrcFour.lowerCoeff_pos
#check @WuSource.SrcFour.eleven_three
#print axioms WuSource.SrcFour.eleven_three
#check @WuSource.SrcFour.cross_lower
#print axioms WuSource.SrcFour.cross_lower
#check @WuSource.SrcFour.exp_cubic_lower
#print axioms WuSource.SrcFour.exp_cubic_lower
#check @WuSource.SrcFour.reciprocal_lower
#print axioms WuSource.SrcFour.reciprocal_lower
#check @WuSource.SrcFour.kernel_lower
#print axioms WuSource.SrcFour.kernel_lower
#check @WuSource.SrcFour.integral_ge_two_tails
#print axioms WuSource.SrcFour.integral_ge_two_tails
#check @WuSource.SrcFour.inner10_lower
#print axioms WuSource.SrcFour.inner10_lower
#check @WuSource.SrcFour.inner11_lower
#print axioms WuSource.SrcFour.inner11_lower
#check @WuSource.SrcFour.lowerMiddleTerm
#print axioms WuSource.SrcFour.lowerMiddleTerm
#check @WuSource.SrcFour.lowerA
#print axioms WuSource.SrcFour.lowerA
#check @WuSource.SrcFour.lowerB
#print axioms WuSource.SrcFour.lowerB
#check @WuSource.SrcFour.lowerProfileTerm
#print axioms WuSource.SrcFour.lowerProfileTerm
#check @WuSource.SrcFour.lowerProfile
#print axioms WuSource.SrcFour.lowerProfile
#check @WuSource.SrcFour.weightFloor
#print axioms WuSource.SrcFour.weightFloor
#check @WuSource.SrcFour.lowerAmount
#print axioms WuSource.SrcFour.lowerAmount
#check @WuSource.SrcFour.lower_coefficients_nonneg
#print axioms WuSource.SrcFour.lower_coefficients_nonneg
#check @WuSource.SrcFour.middle_lower
#print axioms WuSource.SrcFour.middle_lower
#check @WuSource.SrcFour.lower_middle_sum
#print axioms WuSource.SrcFour.lower_middle_sum
#check @WuSource.SrcFour.lower_sum_le_middle
#print axioms WuSource.SrcFour.lower_sum_le_middle
#check @WuSource.SrcFour.lowerMiddleTerm_eq
#print axioms WuSource.SrcFour.lowerMiddleTerm_eq
#check @WuSource.SrcFour.lowerMiddleTerm_integrable
#print axioms WuSource.SrcFour.lowerMiddleTerm_integrable
#check @WuSource.SrcFour.lowerMiddleTerm_integral
#print axioms WuSource.SrcFour.lowerMiddleTerm_integral
#check @WuSource.SrcFour.lowerProfile_le_outer
#print axioms WuSource.SrcFour.lowerProfile_le_outer
#check @WuSource.SrcFour.lowerProfileTerm_integrable
#print axioms WuSource.SrcFour.lowerProfileTerm_integrable
#check @WuSource.SrcFour.lowerProfile_integrable
#print axioms WuSource.SrcFour.lowerProfile_integrable
#check @WuSource.SrcFour.lowerProfile_integral
#print axioms WuSource.SrcFour.lowerProfile_integral
#check @WuSource.SrcFour.weightFloor_bounds
#print axioms WuSource.SrcFour.weightFloor_bounds
#check @WuSource.SrcFour.original_weight_floor
#print axioms WuSource.SrcFour.original_weight_floor
#check @WuSource.SrcFour.lowerAmount_le_integral
#print axioms WuSource.SrcFour.lowerAmount_le_integral
#check @WuSource.SrcFour.original_pair_lowerAmount
#print axioms WuSource.SrcFour.original_pair_lowerAmount
#check @WuSource.SrcFour.lowerAmount_56_exceeds_target
#print axioms WuSource.SrcFour.lowerAmount_56_exceeds_target
#check @WuSource.SrcFour.original_pair_gt_target_of_lower
#print axioms WuSource.SrcFour.original_pair_gt_target_of_lower
#check @WuSource.SrcFour.target_incompatible_with_lower
#print axioms WuSource.SrcFour.target_incompatible_with_lower
#check @WuSource.SrcFour.inner_pair_merged
#print axioms WuSource.SrcFour.inner_pair_merged
#check @WuSource.SrcFour.middle_pair_merged
#print axioms WuSource.SrcFour.middle_pair_merged
#check @WuSource.SrcFour.outer_pair_merged
#print axioms WuSource.SrcFour.outer_pair_merged
#check @WuSource.SrcFour.original_pair_source
#print axioms WuSource.SrcFour.original_pair_source
#check @WuSource.SrcFour.actual_pair_fineCap
#print axioms WuSource.SrcFour.actual_pair_fineCap
#check @WuSource.SrcFour.replacementCoefficient
#print axioms WuSource.SrcFour.replacementCoefficient
#check @WuSource.SrcFour.replacementCoefficient_exact
#print axioms WuSource.SrcFour.replacementCoefficient_exact
#check @WuSource.SrcFour.ordinary_P2_conditional
#print axioms WuSource.SrcFour.ordinary_P2_conditional
#check @WuSource.FourBuchstabAccepted.sourceCap
#print axioms WuSource.FourBuchstabAccepted.sourceCap
#check @WuSource.FourBuchstabAccepted.original_pair_upper
#print axioms WuSource.FourBuchstabAccepted.original_pair_upper
#check @WuSource.FourBuchstabAccepted.original_pair_lt_688
#print axioms WuSource.FourBuchstabAccepted.original_pair_lt_688
#check @WuSource.FourBuchstabAccepted.actual_pair_upper
#print axioms WuSource.FourBuchstabAccepted.actual_pair_upper
#check @WuSource.FourBuchstabAccepted.ordinary_P2
#print axioms WuSource.FourBuchstabAccepted.ordinary_P2

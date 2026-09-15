import W17JointSplit
import W17JointSymbolicActual

namespace WuTarget.W17Joint

#check @paidCell_le_eRemainder
#print axioms paidCell_le_eRemainder
#check @rationalJ_le_jRemainder
#print axioms rationalJ_le_jRemainder
#check @remainderMatrix
#print axioms remainderMatrix
#check @remainderMatrix_nonneg
#print axioms remainderMatrix_nonneg
#check @remainderMatrix_le
#print axioms remainderMatrix_le
#check @eWeightLower
#print axioms eWeightLower
#check @jWeightLower
#print axioms jWeightLower
#check @eWeightLower_bounds
#print axioms eWeightLower_bounds
#check @jWeightLower_bounds
#print axioms jWeightLower_bounds
#check @rowWeightLower
#print axioms rowWeightLower
#check @rowWeightLower_bounds
#print axioms rowWeightLower_bounds
#check @rationalSigmaMatrix
#print axioms rationalSigmaMatrix
#check @rationalSigmaMatrix_nonneg
#print axioms rationalSigmaMatrix_nonneg
#check @rationalSigmaMatrix_le
#print axioms rationalSigmaMatrix_le
#check @jointMatrix
#print axioms jointMatrix
#check @jointMatrix_nonneg
#print axioms jointMatrix_nonneg
#check @jointMatrix_le_feedbackMatrix
#print axioms jointMatrix_le_feedbackMatrix
#check @baseline_le_jointMatrix
#print axioms baseline_le_jointMatrix

#check @symbolic_matrix_bounds
#print axioms symbolic_matrix_bounds
#check @symbolic_apply_le_feedback
#print axioms symbolic_apply_le_feedback
#check @symbolic_seed_nonneg
#print axioms symbolic_seed_nonneg
#check @symbolic_seed_stronger
#print axioms symbolic_seed_stronger
#check @symbolic_actual_with_seed
#print axioms symbolic_actual_with_seed
#check @symbolic_seed_le_actual
#print axioms symbolic_seed_le_actual
#check @symbolic_same_delta_system
#print axioms symbolic_same_delta_system
#check @symbolic_paid_update
#print axioms symbolic_paid_update

#check @W04.clippedCell_le_eKernel
#print axioms W04.clippedCell_le_eKernel
#check @W05.rationalJCoefficients_paid
#print axioms W05.rationalJCoefficients_paid
#check @W06.feedbackMatrix_split
#print axioms W06.feedbackMatrix_split
#check @W06.sigmaMatrix_add_nonSigma_le
#print axioms W06.sigmaMatrix_add_nonSigma_le
#check @W07.paidTable_le_densityEntry
#print axioms W07.paidTable_le_densityEntry
#check @W08.paidCells_le_kernel
#print axioms W08.paidCells_le_kernel
#check @W09.seed_feedback_actual
#print axioms W09.seed_feedback_actual
#check @W09.commonRadius_pos
#print axioms W09.commonRadius_pos
#check @W09.commonRadius_cap
#print axioms W09.commonRadius_cap

#print jointMatrix
#print remainderMatrix
#print rowWeightLower
#print W09.seedQ
#print W09.commonRadius

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut pending := #[``symbolic_matrix_bounds, ``symbolic_seed_stronger,
    ``symbolic_same_delta_system, ``symbolic_paid_update]
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    match env.checked.get.find? name with
    | none => missing := missing.push name
    | some info =>
      pending := pending ++ info.type.getUsedConstants
      match info with
      | .defnInfo v => pending := pending ++ v.value.getUsedConstants
      | .thmInfo v => pending := pending ++ v.value.getUsedConstants
      | .opaqueInfo v => pending := pending ++ v.value.getUsedConstants
      | .inductInfo v => pending := pending ++ v.ctors.toArray
      | _ => pure ()
  let banned := #[`NineFeedbackStrength.originalH, `FeedbackLimit.Ainf,
    `NineFeedbackStrength.subsolution_le_Ainf, `NineFeedbackStrength.actual_comparison_same_delta,
    `sorryAx, `Lean.ofReduceBool]
  let found := banned.filter (fun name => seen.contains name)
  logInfo m!"W17 recovery cone: {seen.size} constants; missing={missing}; forbidden={found}"
  unless missing.isEmpty && found.isEmpty do
    throwError "W17 recovery dependency audit failed"

end WuTarget.W17Joint

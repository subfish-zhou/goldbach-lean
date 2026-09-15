import W06Consumers
import Lean

namespace WuTarget.W06
open Lean Elab Command

elab (name := auditCone) "#w06_cone" : command => do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[`WuTarget.W06.sigmaLower_le_aProfile,
    `WuTarget.W06.sigmaCoeff_le_aProfile, `WuTarget.W06.eProfile_sigma_lower,
    `WuTarget.W06.profileJ_sigma_lower, `WuTarget.W06.firstFeedback_sigma_lower,
    `WuTarget.W06.coupledFeedback_sigma_lower, `WuTarget.W06.first_multipliers,
    `WuTarget.W06.first_J_multiplier_pos, `WuTarget.W06.terminal_J_multiplier,
    `WuTarget.W06.coupled_multipliers, `WuTarget.W06.sigmaMatrix_pos,
    `WuTarget.W06.nonSigmaMatrix_nonneg, `WuTarget.W06.nonSigmaMatrix_apply,
    `WuTarget.W06.feedbackMatrix_split, `WuTarget.W06.add_nonSigma_payment,
    `WuTarget.W06.actual_sigma_feedback, `WuTarget.W06.actual_sigma_matrix_feedback]
  let mut todo := roots
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !seen.contains n then
      seen := seen.insert n
      if seen.size > 200000 then throwError "dependency audit cap exceeded"
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
  out.putStrLn <| (Json.mkObj [("roots", toJson (roots.map Name.toString)),
    ("visited", toJson seen.size), ("missing", toJson (missing.map Name.toString)),
    ("forbiddenDependencies", toJson (found.map Name.toString))]).compress
  out.flush
  unless found.isEmpty && missing.isEmpty do throwError "method dependency audit failed"

#w06_cone
#check auditCone
#print axioms auditCone

end WuTarget.W06

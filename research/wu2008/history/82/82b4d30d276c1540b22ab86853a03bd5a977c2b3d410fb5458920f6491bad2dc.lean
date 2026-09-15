import WSrcNineCertificate

namespace WuSource.SrcNine

#check @actual_coordinates
#check @coupled_qualified
#check @first_qualified
#check @coupled_source_cost
#check @coupled_source_actual
#check @lower_matrix_bounds
#check @actual_paid_system
#check @certified_lower_subsolution
#check @all_rows
#check @z_eq_cast
#check @z_positive
#check @z_stronger_than_seed
#check @actual_nine_lower
#check @actual_H_lower
#check @explicit_certificate
#check @preferred_target_not_met
#check @exact_target_deficits
#check @certified_uniform_target_error
#check @actual_H_with_uniform_target_error

#print axioms actual_coordinates
#print axioms coupled_qualified
#print axioms first_qualified
#print axioms coupled_source_cost
#print axioms coupled_source_actual
#print axioms lower_matrix_bounds
#print axioms actual_paid_system
#print axioms certified_lower_subsolution
#print axioms all_rows
#print axioms z_eq_cast
#print axioms z_positive
#print axioms z_stronger_than_seed
#print axioms actual_nine_lower
#print axioms actual_H_lower
#print axioms explicit_certificate
#print axioms preferred_target_not_met
#print axioms exact_target_deficits
#print axioms certified_uniform_target_error
#print axioms actual_H_with_uniform_target_error

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut pending := #[``actual_nine_lower, ``actual_H_lower, ``explicit_certificate]
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
    `NineFeedbackStrength.subsolution_le_Ainf, `Wu04Bypass.v8,
    `sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler]
  let found := banned.filter (fun name => seen.contains name)
  logInfo m!"SrcNine actual certificate cone: {seen.size} constants; missing={missing}; forbidden={found}"
  unless missing.isEmpty && found.isEmpty do
    throwError "SrcNine actual certificate dependency audit failed"

end WuSource.SrcNine

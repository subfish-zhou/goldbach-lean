import W04ClippedCells
import W04CoupledMatrix
import W04ExactMatrix

namespace WuTarget.W04

#check eKernel
#print axioms eKernel
#check clippedCell
#print axioms clippedCell
#check upperLeft_le_upperNode
#print axioms upperLeft_le_upperNode
#check basis_profile
#print axioms basis_profile
#check kernel_integrand_nonneg
#print axioms kernel_integrand_nonneg
#check eKernel_nonneg
#print axioms eKernel_nonneg
#check eKernel_zero_of_right_le
#print axioms eKernel_zero_of_right_le
#check clippedCell_zero_of_right_le
#print axioms clippedCell_zero_of_right_le
#check clippedCell_nonneg
#print axioms clippedCell_nonneg
#check clippedCell_le_eKernel
#print axioms clippedCell_le_eKernel
#check eKernel_le_eProfile
#print axioms eKernel_le_eProfile
#check clippedCell_le_eProfile
#print axioms clippedCell_le_eProfile

#check coupledExtra
#print axioms coupledExtra
#check extraMatrix
#print axioms extraMatrix
#check augmentedMatrix
#print axioms augmentedMatrix
#check coupledExtra_nonneg
#print axioms coupledExtra_nonneg
#check extraMatrix_nonneg
#print axioms extraMatrix_nonneg
#check coupledExtra_le_kernel
#print axioms coupledExtra_le_kernel
#check old_cells_add_extra_le_coupled
#print axioms old_cells_add_extra_le_coupled
#check elementary_add_extra_le_feedbackMatrix
#print axioms elementary_add_extra_le_feedbackMatrix
#check oldMatrix_le_elementary
#print axioms oldMatrix_le_elementary
#check augmentedMatrix_le_feedbackMatrix
#print axioms augmentedMatrix_le_feedbackMatrix
#check oldMatrix_le_augmentedMatrix
#print axioms oldMatrix_le_augmentedMatrix
#check augmentedMatrix_eq_old_of_first
#print axioms augmentedMatrix_eq_old_of_first
#check augmented_apply_le_feedback
#print axioms augmented_apply_le_feedback
#check actual_augmented_system
#print axioms actual_augmented_system
#check augmented_same_delta
#print axioms augmented_same_delta
#check augmented_paid_update
#print axioms augmented_paid_update

#check extraTable
#print axioms extraTable
#check extra_row0
#print axioms extra_row0
#check extra_row1
#print axioms extra_row1
#check extra_row2
#print axioms extra_row2
#check extra_row3
#print axioms extra_row3
#check coupledExtra_eq_table
#print axioms coupledExtra_eq_table
#check extraMatrix_eq_table
#print axioms extraMatrix_eq_table
#check extraTable_le_kernel
#print axioms extraTable_le_kernel
#check explicit_augmentedMatrix_le
#print axioms explicit_augmentedMatrix_le
#check coupledExtra_terminal_pos
#print axioms coupledExtra_terminal_pos
#check coupled_rows_strictly_improve
#print axioms coupled_rows_strictly_improve

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending := #[
    ``extraTable_le_kernel,
    ``explicit_augmentedMatrix_le,
    ``actual_augmented_system,
    ``augmented_same_delta,
    ``augmented_paid_update,
    ``coupled_rows_strictly_improve,
    ``eKernel_zero_of_right_le]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    if (name.toString.splitOn ".").any
        (fun part => part.startsWith "originalH" || part.startsWith "Ainf") then
      throwError "Forbidden method dependency: {name}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? then
        pending := pending ++ value.getUsedConstants
  logInfo m!"W04 method cone: {seen.size} constants; no originalH/Ainf dependency."

end WuTarget.W04

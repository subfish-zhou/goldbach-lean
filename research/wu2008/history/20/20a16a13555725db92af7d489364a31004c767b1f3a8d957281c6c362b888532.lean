import W07Root
import Lean

namespace WuTarget.W07

#check @densityEntry
#print axioms densityEntry
#check @densityMoment_eq_sum
#print axioms densityMoment_eq_sum
#check @densityEntry_eq_basis
#print axioms densityEntry_eq_basis
#check @densityEntry_nonneg
#print axioms densityEntry_nonneg
#check @embedFour
#print axioms embedFour
#check @legacy_cell
#print axioms legacy_cell
#check @densityEntry_eq_legacy
#print axioms densityEntry_eq_legacy
#check @legacy_matrix_eq_density
#print axioms legacy_matrix_eq_density
#check @logEntry
#print axioms logEntry
#check @logEntry_le_densityEntry
#print axioms logEntry_le_densityEntry
#check @logEntry_sum_le
#print axioms logEntry_sum_le
#check @rationalKernel
#print axioms rationalKernel
#check @rationalKernel_bounds
#print axioms rationalKernel_bounds
#check @rationalDensity
#print axioms rationalDensity
#check @rationalDensity_bounds
#print axioms rationalDensity_bounds
#check @rationalInterval
#print axioms rationalInterval
#check @rationalInterval_bounds
#print axioms rationalInterval_bounds
#check @rationalEntry
#print axioms rationalEntry
#check @rationalEntry_bounds
#print axioms rationalEntry_bounds
#check @rationalEntry_le_densityEntry
#print axioms rationalEntry_le_densityEntry
#check @rationalEntry_sum_le
#print axioms rationalEntry_sum_le
#check @paidTable
#print axioms paidTable
#check @table_probe
#print axioms table_probe
#check @paidTable_row0
#print axioms paidTable_row0
#check @paidTable_row1
#print axioms paidTable_row1
#check @paidTable_row2_rest
#print axioms paidTable_row2_rest
#check @paidTable_row3_first
#print axioms paidTable_row3_first
#check @paidTable_row3_rest
#print axioms paidTable_row3_rest
#check @paidTable_eq_rationalEntry
#print axioms paidTable_eq_rationalEntry
#check @paidTable_nonneg
#print axioms paidTable_nonneg
#check @paidTable_le_logEntry
#print axioms paidTable_le_logEntry
#check @paidTable_le_densityEntry
#print axioms paidTable_le_densityEntry
#check @paidTable_sum_le
#print axioms paidTable_sum_le
#check @densityMatrix
#print axioms densityMatrix
#check @paidMatrix
#print axioms paidMatrix
#check @logMatrix
#print axioms logMatrix
#check @retainedCoupled
#print axioms retainedCoupled
#check @coupledFeedback_split
#print axioms coupledFeedback_split
#check @retainedFeedback
#print axioms retainedFeedback
#check @retainedMatrix
#print axioms retainedMatrix
#check @feedbackMatrix_split
#print axioms feedbackMatrix_split
#check @legacy_matrix_eq_principal
#print axioms legacy_matrix_eq_principal
#check @paidMatrix_nonneg
#print axioms paidMatrix_nonneg
#check @paidMatrix_le_logMatrix
#print axioms paidMatrix_le_logMatrix
#check @logMatrix_le_densityMatrix
#print axioms logMatrix_le_densityMatrix
#check @paidMatrix_le_densityMatrix
#print axioms paidMatrix_le_densityMatrix
#check @first_rows_zero
#print axioms first_rows_zero
#check @coupled_paid_le
#print axioms coupled_paid_le
#check @coupled_log_le
#print axioms coupled_log_le
#check @cells_add_density_le_coupled
#print axioms cells_add_density_le_coupled
#check @elementary_add_density_le
#print axioms elementary_add_density_le
#check @elementary_add_log_le
#print axioms elementary_add_log_le
#check @elementary_add_paid_le
#print axioms elementary_add_paid_le
#check @baseline_le_elementary
#print axioms baseline_le_elementary
#check @baseline_add_paid_le
#print axioms baseline_add_paid_le
#check @baseline_add_log_le
#print axioms baseline_add_log_le
#check @paid_actual
#print axioms paid_actual
#check @paid_v8_actual
#print axioms paid_v8_actual
#check @coupled_paid_actual
#print axioms coupled_paid_actual
#check @paid_v8_gain
#print axioms paid_v8_gain
#check @density_v8_gain
#print axioms density_v8_gain
#check @paid_v8_matrix
#print axioms paid_v8_matrix
#check @paid_v8_actual_with_gain
#print axioms paid_v8_actual_with_gain

#print paidTable
#print rationalKernel
#print retainedCoupled

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[
    ``densityEntry, ``densityMoment_eq_sum, ``densityEntry_eq_basis, ``densityEntry_nonneg,
    ``embedFour, ``legacy_cell, ``densityEntry_eq_legacy, ``legacy_matrix_eq_density,
    ``logEntry, ``logEntry_le_densityEntry, ``logEntry_sum_le,
    ``rationalKernel, ``rationalKernel_bounds, ``rationalDensity, ``rationalDensity_bounds,
    ``rationalInterval, ``rationalInterval_bounds, ``rationalEntry, ``rationalEntry_bounds,
    ``rationalEntry_le_densityEntry, ``rationalEntry_sum_le, ``paidTable, ``table_probe,
    ``paidTable_row0, ``paidTable_row1, ``paidTable_row2_rest, ``paidTable_row3_first,
    ``paidTable_row3_rest, ``paidTable_eq_rationalEntry, ``paidTable_nonneg,
    ``paidTable_le_logEntry, ``paidTable_le_densityEntry, ``paidTable_sum_le,
    ``densityMatrix, ``paidMatrix, ``logMatrix, ``retainedCoupled, ``coupledFeedback_split,
    ``retainedFeedback, ``retainedMatrix, ``feedbackMatrix_split, ``legacy_matrix_eq_principal,
    ``paidMatrix_nonneg, ``paidMatrix_le_logMatrix, ``logMatrix_le_densityMatrix,
    ``paidMatrix_le_densityMatrix, ``first_rows_zero, ``coupled_paid_le, ``coupled_log_le,
    ``cells_add_density_le_coupled, ``elementary_add_density_le, ``elementary_add_log_le,
    ``elementary_add_paid_le, ``baseline_le_elementary, ``baseline_add_paid_le,
    ``baseline_add_log_le, ``paid_actual, ``paid_v8_actual, ``coupled_paid_actual,
    ``paid_v8_gain, ``density_v8_gain, ``paid_v8_matrix, ``paid_v8_actual_with_gain]
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
  out.putStrLn <| (Json.mkObj [("roots", toJson roots.size), ("visited", toJson seen.size),
    ("missing", toJson (missing.map Name.toString)),
    ("forbiddenDependencies", toJson (found.map Name.toString))]).compress
  out.flush
  unless found.isEmpty && missing.isEmpty do throwError "W07 method dependency audit failed"

end WuTarget.W07

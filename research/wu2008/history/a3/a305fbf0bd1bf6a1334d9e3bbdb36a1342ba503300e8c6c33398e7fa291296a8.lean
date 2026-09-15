import W05JTableConsumer
import Lean

namespace WuTarget.W05

#check @WuTarget.W05.jCoefficient
#print axioms WuTarget.W05.jCoefficient
#check @WuTarget.W05.jCoefficient_basis
#print axioms WuTarget.W05.jCoefficient_basis
#check @WuTarget.W05.jRest_expansion
#print axioms WuTarget.W05.jRest_expansion
#check @WuTarget.W05.jCoefficient_paid
#print axioms WuTarget.W05.jCoefficient_paid
#check @WuTarget.W05.jCoefficients_paid
#print axioms WuTarget.W05.jCoefficients_paid
#check @WuTarget.W05.jStart_bounds
#print axioms WuTarget.W05.jStart_bounds
#check @WuTarget.W05.j_domain_denominators
#print axioms WuTarget.W05.j_domain_denominators
#check @WuTarget.W05.lowerLog_nonneg
#print axioms WuTarget.W05.lowerLog_nonneg
#check @WuTarget.W05.recoveryKernel_nonneg
#print axioms WuTarget.W05.recoveryKernel_nonneg
#check @WuTarget.W05.jCoefficient_nonneg
#print axioms WuTarget.W05.jCoefficient_nonneg
#check @WuTarget.W05.first_coefficients_paid
#print axioms WuTarget.W05.first_coefficients_paid
#check @WuTarget.W05.coupled_coefficients_paid
#print axioms WuTarget.W05.coupled_coefficients_paid
#check @WuTarget.W05.terminal_coefficient_zero
#print axioms WuTarget.W05.terminal_coefficient_zero
#check @WuTarget.W05.elementary_le_lowerLog
#print axioms WuTarget.W05.elementary_le_lowerLog
#check @WuTarget.W05.rationalCell
#print axioms WuTarget.W05.rationalCell
#check @WuTarget.W05.rationalCell_nonneg
#print axioms WuTarget.W05.rationalCell_nonneg
#check @WuTarget.W05.rationalKernel_le
#print axioms WuTarget.W05.rationalKernel_le
#check @WuTarget.W05.rationalCell_le
#print axioms WuTarget.W05.rationalCell_le
#check @WuTarget.W05.rationalJCoefficient
#print axioms WuTarget.W05.rationalJCoefficient
#check @WuTarget.W05.endpoint_log_lower
#print axioms WuTarget.W05.endpoint_log_lower
#check @WuTarget.W05.rationalJCoefficient_le
#print axioms WuTarget.W05.rationalJCoefficient_le
#check @WuTarget.W05.rationalJCoefficient_nonneg
#print axioms WuTarget.W05.rationalJCoefficient_nonneg
#check @WuTarget.W05.rationalJCoefficients_paid
#print axioms WuTarget.W05.rationalJCoefficients_paid
#check @WuTarget.W05.rational_terminal_zero
#print axioms WuTarget.W05.rational_terminal_zero
#check @WuTarget.W05.assembleJ
#print axioms WuTarget.W05.assembleJ
#check @WuTarget.W05.jMatrix
#print axioms WuTarget.W05.jMatrix
#check @WuTarget.W05.rationalJMatrix
#print axioms WuTarget.W05.rationalJMatrix
#check @WuTarget.W05.jSigmaWeight
#print axioms WuTarget.W05.jSigmaWeight
#check @WuTarget.W05.otherFeedback
#print axioms WuTarget.W05.otherFeedback
#check @WuTarget.W05.assembleJ_apply
#print axioms WuTarget.W05.assembleJ_apply
#check @WuTarget.W05.assembleJ_mono
#print axioms WuTarget.W05.assembleJ_mono
#check @WuTarget.W05.assembleJ_nonneg
#print axioms WuTarget.W05.assembleJ_nonneg
#check @WuTarget.W05.rationalJMatrix_le
#print axioms WuTarget.W05.rationalJMatrix_le
#check @WuTarget.W05.rationalJMatrix_nonneg
#print axioms WuTarget.W05.rationalJMatrix_nonneg
#check @WuTarget.W05.jMatrix_nonneg
#print axioms WuTarget.W05.jMatrix_nonneg
#check @WuTarget.W05.jSigmaWeight_nonneg
#print axioms WuTarget.W05.jSigmaWeight_nonneg
#check @WuTarget.W05.feedback_separated_payment
#print axioms WuTarget.W05.feedback_separated_payment
#check @WuTarget.W05.matrix_separated_payment
#print axioms WuTarget.W05.matrix_separated_payment
#check @WuTarget.W05.elementary_le_other
#print axioms WuTarget.W05.elementary_le_other
#check @WuTarget.W05.elementary_add_jMatrix_le
#print axioms WuTarget.W05.elementary_add_jMatrix_le
#check @WuTarget.W05.baselineM_le_elementary
#print axioms WuTarget.W05.baselineM_le_elementary
#check @WuTarget.W05.paidMatrix
#print axioms WuTarget.W05.paidMatrix
#check @WuTarget.W05.paidMatrix_le
#print axioms WuTarget.W05.paidMatrix_le
#check @WuTarget.W05.paidMatrix_preserves_baseline
#print axioms WuTarget.W05.paidMatrix_preserves_baseline
#check @WuTarget.W05.paid_feedback
#print axioms WuTarget.W05.paid_feedback
#check @WuTarget.W05.paid_actual
#print axioms WuTarget.W05.paid_actual
#check @WuTarget.W05.v8_paid_actual
#print axioms WuTarget.W05.v8_paid_actual
#check @WuTarget.W05.terminal_jMatrix_zero
#print axioms WuTarget.W05.terminal_jMatrix_zero
#check @WuTarget.W05.terminal_rationalJMatrix_zero
#print axioms WuTarget.W05.terminal_rationalJMatrix_zero
#check @WuTarget.W05.coupledTable0_s
#print axioms WuTarget.W05.coupledTable0_s
#check @WuTarget.W05.coupledTable0_s_exact
#print axioms WuTarget.W05.coupledTable0_s_exact
#check @WuTarget.W05.coupledTable0_kappa2
#print axioms WuTarget.W05.coupledTable0_kappa2
#check @WuTarget.W05.coupledTable0_kappa2_exact
#print axioms WuTarget.W05.coupledTable0_kappa2_exact
#check @WuTarget.W05.coupledTable0_kappa3
#print axioms WuTarget.W05.coupledTable0_kappa3
#check @WuTarget.W05.coupledTable0_kappa3_exact
#print axioms WuTarget.W05.coupledTable0_kappa3_exact
#check @WuTarget.W05.coupledTable1_s
#print axioms WuTarget.W05.coupledTable1_s
#check @WuTarget.W05.coupledTable1_s_exact
#print axioms WuTarget.W05.coupledTable1_s_exact
#check @WuTarget.W05.coupledTable1_kappa2
#print axioms WuTarget.W05.coupledTable1_kappa2
#check @WuTarget.W05.coupledTable1_kappa2_exact
#print axioms WuTarget.W05.coupledTable1_kappa2_exact
#check @WuTarget.W05.coupledTable1_kappa3
#print axioms WuTarget.W05.coupledTable1_kappa3
#check @WuTarget.W05.coupledTable1_kappa3_exact
#print axioms WuTarget.W05.coupledTable1_kappa3_exact
#check @WuTarget.W05.coupledTable2_s
#print axioms WuTarget.W05.coupledTable2_s
#check @WuTarget.W05.coupledTable2_s_exact
#print axioms WuTarget.W05.coupledTable2_s_exact
#check @WuTarget.W05.coupledTable2_kappa2
#print axioms WuTarget.W05.coupledTable2_kappa2
#check @WuTarget.W05.coupledTable2_kappa2_exact
#print axioms WuTarget.W05.coupledTable2_kappa2_exact
#check @WuTarget.W05.coupledTable2_kappa3
#print axioms WuTarget.W05.coupledTable2_kappa3
#check @WuTarget.W05.coupledTable2_kappa3_exact
#print axioms WuTarget.W05.coupledTable2_kappa3_exact
#check @WuTarget.W05.coupledTable3_s
#print axioms WuTarget.W05.coupledTable3_s
#check @WuTarget.W05.coupledTable3_s_exact
#print axioms WuTarget.W05.coupledTable3_s_exact
#check @WuTarget.W05.coupledTable3_kappa2
#print axioms WuTarget.W05.coupledTable3_kappa2
#check @WuTarget.W05.coupledTable3_kappa2_exact
#print axioms WuTarget.W05.coupledTable3_kappa2_exact
#check @WuTarget.W05.coupledTable3_kappa3
#print axioms WuTarget.W05.coupledTable3_kappa3
#check @WuTarget.W05.coupledTable3_kappa3_exact
#print axioms WuTarget.W05.coupledTable3_kappa3_exact
#check @WuTarget.W05.firstTable0
#print axioms WuTarget.W05.firstTable0
#check @WuTarget.W05.firstTable0_exact
#print axioms WuTarget.W05.firstTable0_exact
#check @WuTarget.W05.firstTable1
#print axioms WuTarget.W05.firstTable1
#check @WuTarget.W05.firstTable1_exact
#print axioms WuTarget.W05.firstTable1_exact
#check @WuTarget.W05.firstTable2
#print axioms WuTarget.W05.firstTable2
#check @WuTarget.W05.firstTable2_exact
#print axioms WuTarget.W05.firstTable2_exact
#check @WuTarget.W05.firstTable3
#print axioms WuTarget.W05.firstTable3
#check @WuTarget.W05.firstTable3_exact
#print axioms WuTarget.W05.firstTable3_exact
#check @WuTarget.W05.firstTable4
#print axioms WuTarget.W05.firstTable4
#check @WuTarget.W05.firstTable4_exact
#print axioms WuTarget.W05.firstTable4_exact
#check @WuTarget.W05.jTable
#print axioms WuTarget.W05.jTable
#check @WuTarget.W05.jTable_eq
#print axioms WuTarget.W05.jTable_eq
#check @WuTarget.W05.jTable_nonneg
#print axioms WuTarget.W05.jTable_nonneg
#check @WuTarget.W05.table_separated_payment
#print axioms WuTarget.W05.table_separated_payment
#check @WuTarget.W05.table_matrix_paid
#print axioms WuTarget.W05.table_matrix_paid
#check @WuTarget.W05.table_feedback_paid
#print axioms WuTarget.W05.table_feedback_paid
#check @WuTarget.W05.v8_table_actual
#print axioms WuTarget.W05.v8_table_actual
#check @WuTarget.W05.first_row_last_coefficient
#print axioms WuTarget.W05.first_row_last_coefficient
#check @WuTarget.W05.first_row_strict_increment
#print axioms WuTarget.W05.first_row_strict_increment
#check @WuTarget.W05.terminal_table_zero
#print axioms WuTarget.W05.terminal_table_zero

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[
    `WuTarget.W05.jCoefficient,
    `WuTarget.W05.jCoefficient_basis,
    `WuTarget.W05.jRest_expansion,
    `WuTarget.W05.jCoefficient_paid,
    `WuTarget.W05.jCoefficients_paid,
    `WuTarget.W05.jStart_bounds,
    `WuTarget.W05.j_domain_denominators,
    `WuTarget.W05.lowerLog_nonneg,
    `WuTarget.W05.recoveryKernel_nonneg,
    `WuTarget.W05.jCoefficient_nonneg,
    `WuTarget.W05.first_coefficients_paid,
    `WuTarget.W05.coupled_coefficients_paid,
    `WuTarget.W05.terminal_coefficient_zero,
    `WuTarget.W05.elementary_le_lowerLog,
    `WuTarget.W05.rationalCell,
    `WuTarget.W05.rationalCell_nonneg,
    `WuTarget.W05.rationalKernel_le,
    `WuTarget.W05.rationalCell_le,
    `WuTarget.W05.rationalJCoefficient,
    `WuTarget.W05.endpoint_log_lower,
    `WuTarget.W05.rationalJCoefficient_le,
    `WuTarget.W05.rationalJCoefficient_nonneg,
    `WuTarget.W05.rationalJCoefficients_paid,
    `WuTarget.W05.rational_terminal_zero,
    `WuTarget.W05.assembleJ,
    `WuTarget.W05.jMatrix,
    `WuTarget.W05.rationalJMatrix,
    `WuTarget.W05.jSigmaWeight,
    `WuTarget.W05.otherFeedback,
    `WuTarget.W05.assembleJ_apply,
    `WuTarget.W05.assembleJ_mono,
    `WuTarget.W05.assembleJ_nonneg,
    `WuTarget.W05.rationalJMatrix_le,
    `WuTarget.W05.rationalJMatrix_nonneg,
    `WuTarget.W05.jMatrix_nonneg,
    `WuTarget.W05.jSigmaWeight_nonneg,
    `WuTarget.W05.feedback_separated_payment,
    `WuTarget.W05.matrix_separated_payment,
    `WuTarget.W05.elementary_le_other,
    `WuTarget.W05.elementary_add_jMatrix_le,
    `WuTarget.W05.baselineM_le_elementary,
    `WuTarget.W05.paidMatrix,
    `WuTarget.W05.paidMatrix_le,
    `WuTarget.W05.paidMatrix_preserves_baseline,
    `WuTarget.W05.paid_feedback,
    `WuTarget.W05.paid_actual,
    `WuTarget.W05.v8_paid_actual,
    `WuTarget.W05.terminal_jMatrix_zero,
    `WuTarget.W05.terminal_rationalJMatrix_zero,
    `WuTarget.W05.coupledTable0_s,
    `WuTarget.W05.coupledTable0_s_exact,
    `WuTarget.W05.coupledTable0_kappa2,
    `WuTarget.W05.coupledTable0_kappa2_exact,
    `WuTarget.W05.coupledTable0_kappa3,
    `WuTarget.W05.coupledTable0_kappa3_exact,
    `WuTarget.W05.coupledTable1_s,
    `WuTarget.W05.coupledTable1_s_exact,
    `WuTarget.W05.coupledTable1_kappa2,
    `WuTarget.W05.coupledTable1_kappa2_exact,
    `WuTarget.W05.coupledTable1_kappa3,
    `WuTarget.W05.coupledTable1_kappa3_exact,
    `WuTarget.W05.coupledTable2_s,
    `WuTarget.W05.coupledTable2_s_exact,
    `WuTarget.W05.coupledTable2_kappa2,
    `WuTarget.W05.coupledTable2_kappa2_exact,
    `WuTarget.W05.coupledTable2_kappa3,
    `WuTarget.W05.coupledTable2_kappa3_exact,
    `WuTarget.W05.coupledTable3_s,
    `WuTarget.W05.coupledTable3_s_exact,
    `WuTarget.W05.coupledTable3_kappa2,
    `WuTarget.W05.coupledTable3_kappa2_exact,
    `WuTarget.W05.coupledTable3_kappa3,
    `WuTarget.W05.coupledTable3_kappa3_exact,
    `WuTarget.W05.firstTable0,
    `WuTarget.W05.firstTable0_exact,
    `WuTarget.W05.firstTable1,
    `WuTarget.W05.firstTable1_exact,
    `WuTarget.W05.firstTable2,
    `WuTarget.W05.firstTable2_exact,
    `WuTarget.W05.firstTable3,
    `WuTarget.W05.firstTable3_exact,
    `WuTarget.W05.firstTable4,
    `WuTarget.W05.firstTable4_exact,
    `WuTarget.W05.jTable,
    `WuTarget.W05.jTable_eq,
    `WuTarget.W05.jTable_nonneg,
    `WuTarget.W05.table_separated_payment,
    `WuTarget.W05.table_matrix_paid,
    `WuTarget.W05.table_feedback_paid,
    `WuTarget.W05.v8_table_actual,
    `WuTarget.W05.first_row_last_coefficient,
    `WuTarget.W05.first_row_strict_increment,
    `WuTarget.W05.terminal_table_zero]
  let mut todo := roots
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  let mut badAxioms : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !seen.contains n then
      seen := seen.insert n
      if seen.size > 200000 then throwError "W05 dependency audit cap exceeded"
      match env.checked.get.find? n with
      | none => missing := missing.push n
      | some ci =>
        todo := todo ++ ci.type.getUsedConstants
        match ci with
        | .defnInfo v => todo := todo ++ v.value.getUsedConstants
        | .thmInfo v => todo := todo ++ v.value.getUsedConstants
        | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
        | .inductInfo v => todo := todo ++ v.ctors.toArray
        | .axiomInfo _ =>
          unless n == `propext || n == `Classical.choice || n == `Quot.sound do
            badAxioms := badAxioms.push n
        | _ => pure ()
  let banned : Array Name := #[`NineFeedbackStrength.originalH, `FeedbackLimit.Ainf,
    `NineFeedbackStrength.subsolution_le_Ainf,
    `NineFeedbackStrength.actual_comparison_same_delta, `sorryAx, `Lean.ofReduceBool]
  let found := banned.filter (fun n => seen.contains n)
  let out ← IO.getStdout
  out.putStrLn <| (Json.mkObj [("roots", toJson roots.size),
    ("visited", toJson seen.size), ("missing", toJson (missing.map Name.toString)),
    ("forbiddenDependencies", toJson (found.map Name.toString)),
    ("unexpectedAxioms", toJson (badAxioms.map Name.toString))]).compress
  out.flush
  unless found.isEmpty && missing.isEmpty && badAxioms.isEmpty do
    throwError "W05 method dependency audit failed"

end WuTarget.W05

import SrcSingleOriginalLedger

namespace WuSource.SrcSingle
open Wu2008DoubleSieve

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "WuSource.SrcSingle." &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" then
      logInfo m!"{n} : {c.type}"

#check @BaseLowerCounts.fixed_delta_li_with_h
#check @HighSixLowHJoin.actual_pair_integral_psi_upper
#check @SecondFunctionalCoupledFeedback.mother
#check @secondFunctionalMother_masked
#check @secondFunctionalMother_restore_windows
#print wuImprovementLimit
#print wuBoxPhi
#print sourceSieveCarrier

#print axioms second_transfer_to_actual
#print axioms second_original_count
#print axioms windowGain_eq_fourthSource
#print axioms fourth_truncated_le_source
#print axioms source_kernel_integral
#print axioms fourth_nodes_to_source
#print axioms seven_source_rows
#print axioms seven_cutoff_geometry
#print axioms seven_not_direct_source_box
#print axioms seven_finite_omega_consumer
#print axioms coupled_high_actual_finite
#print axioms seven_forcing_paid
#print axioms seven_weighted_forcing_paid
#print axioms seven_actual_partition
#print axioms third_fourth_finite_ledger
#print axioms original_Hh_input_to_count
#print axioms full_Hh_one_psi_count
#print axioms all_seven_raw_source_to_actual_pair
#print axioms original_node_inputs_to_ledger
#print axioms original_log_Hh_input_to_count
end WuSource.SrcSingle

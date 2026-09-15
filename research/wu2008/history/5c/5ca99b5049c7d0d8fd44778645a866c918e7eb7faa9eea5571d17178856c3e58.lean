import E01BaselineBudget

namespace WuTarget.E01Baseline
set_option pp.fullNames true

#print WuTarget.E01Baseline.exactRemaining
#print WuTarget.E01Baseline.exactPaid
#check @WuTarget.E01Baseline.sixth_exact
#check @WuTarget.E01Baseline.gamma_exact
#check @WuTarget.E01Baseline.payment_exact
#check @WuTarget.E01Baseline.four_exact
#check @WuTarget.E01Baseline.debit_exact
#check @WuTarget.E01Baseline.original_packet_exact
#check @WuTarget.E01Baseline.sixth_lower
#check @WuTarget.E01Baseline.node_lower
#check @WuTarget.E01Baseline.debit_strict
#check @WuTarget.E01Baseline.remaining_strict
#check @WuTarget.E01Baseline.paid_strict
#check @WuTarget.E01Baseline.actual_strict
#check @WuTarget.E01Baseline.literal_baseline
#check @WuTarget.E01Baseline.paid_net_identity
#check @WuTarget.E01Baseline.remaining_surplus_identity
#check @WuTarget.E01Baseline.surplus_strict
#check @WuTarget.E01Baseline.exact_gap_identity
#check @WuTarget.E01Baseline.exact_gap_value
#check @WuTarget.E01Baseline.exact_gap_bounds
#check @WuTarget.E01Baseline.short_gap_identity
#check @WuTarget.E01Baseline.certificate_below_targets
#check @WuTarget.E01Baseline.actual_gap_identity
#check @WuTarget.E01Baseline.certificate_gap_is_not_actual_gap
#check @WuTarget.E01Baseline.ordinary_P2_exact
#check @WuTarget.E01Baseline.ordinary_P2_baseline
#check @WuTarget.W17Accepted.refined_target

#print axioms WuTarget.W03.paid_weights_consumer
#print axioms WuTarget.E01Baseline.sixth_lower
#print axioms WuTarget.E01Baseline.node_lower
#print axioms WuTarget.E01Baseline.debit_strict
#print axioms WuTarget.E01Baseline.original_packet_exact
#print axioms WuTarget.E01Baseline.remaining_strict
#print axioms WuTarget.E01Baseline.paid_strict
#print axioms WuTarget.E01Baseline.actual_strict
#print axioms WuTarget.E01Baseline.literal_baseline
#print axioms WuTarget.E01Baseline.remaining_surplus_identity
#print axioms WuTarget.E01Baseline.exact_gap_value
#print axioms WuTarget.E01Baseline.certificate_gap_is_not_actual_gap
#print axioms WuTarget.E01Baseline.ordinary_P2_exact
#print axioms WuTarget.E01Baseline.ordinary_P2_baseline
#print axioms WuTarget.W17Accepted.refined_target

end WuTarget.E01Baseline

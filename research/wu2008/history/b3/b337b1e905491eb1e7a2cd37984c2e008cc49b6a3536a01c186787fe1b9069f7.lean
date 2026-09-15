import W11CreditExpression
import W11CreditPayment
import W11CreditConsumer

namespace WuTarget.W11Credit

#check endpointPacket
#print axioms endpointPacket
#check alphaPacket
#print axioms alphaPacket
#check gPacket
#print axioms gPacket
#check packet
#print axioms packet
#check log_three_identity
#print axioms log_three_identity
#check alpha_exact
#print axioms alpha_exact
#check g_exact
#print axioms g_exact
#check shared_exact
#print axioms shared_exact
#check credit_exact
#print axioms credit_exact
#check collected
#print axioms collected
#check packet_collection
#print axioms packet_collection
#check credit_collected
#print axioms credit_collected
#check payment
#print axioms payment
#check payment_le_credit
#print axioms payment_le_credit
#check payment_exact
#print axioms payment_exact
#check payment_bounds
#print axioms payment_bounds
#check creditLower
#print axioms creditLower
#check creditLower_lt_credit
#print axioms creditLower_lt_credit
#check payment_le_actual
#print axioms payment_le_actual
#check actual_credit_lower
#print axioms actual_credit_lower
#check actual_normalized_credit_lower
#print axioms actual_normalized_credit_lower
#check qScalar
#print axioms qScalar
#check scalar_budget_exact
#print axioms scalar_budget_exact
#check qScalar_lt_correlated
#print axioms qScalar_lt_correlated
#check qScalar_lt_original
#print axioms qScalar_lt_original
#check full_budget_exact
#print axioms full_budget_exact
#check remaining_safe_budget
#print axioms remaining_safe_budget
#check ordinary_P2_parameters
#print axioms ordinary_P2_parameters
#check ordinary_P2
#print axioms ordinary_P2

#print endpointPacket
#print alphaPacket
#print gPacket
#print packet
#print collected
#print payment
#print creditLower
#print qScalar
#print WuTarget.W11.correlatedCredit
#print WuTarget.W11.sharedRecovery
#print WuTarget.W11.otherNumerator
#print axioms WuTarget.W11.actual_correlated_lower
#print axioms WuTarget.W11.ordinary_P2_parameters
#print axioms Wu2008DoubleSieve.TotalEndpointComparison.shared_log_endpoint
#print axioms Wu2008DoubleSieve.JointLogTotalComparison.log_le_V
#print axioms Wu2008DoubleSieve.SharpLogRecurrence.log_lower

end WuTarget.W11Credit

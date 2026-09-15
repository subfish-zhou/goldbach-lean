import W12WeightedDebit
import W12RationalPayment
import W12QoriginalConsumer

namespace WuTarget.W12

set_option pp.fullNames true

#check weightedDebit
#print axioms weightedDebit
#check weightedDebit_eq_J
#print axioms weightedDebit_eq_J
#check weightedDebit_original_domains
#print axioms weightedDebit_original_domains
#check analyticUpper
#print axioms analyticUpper
#check rationalJUpper
#print axioms rationalJUpper
#check rationalUpper
#print axioms rationalUpper
#check weightedDebit_le_analyticUpper
#print axioms weightedDebit_le_analyticUpper
#check mixture_le_rationalJUpper
#print axioms mixture_le_rationalJUpper
#check weightedJ_le_rationalJUpper
#print axioms weightedJ_le_rationalJUpper
#check analyticUpper_le_rationalUpper
#print axioms analyticUpper_le_rationalUpper
#check weightedDebit_le_rationalUpper
#print axioms weightedDebit_le_rationalUpper

#check paymentEndpoint
#print axioms paymentEndpoint
#check rationalUpper_lt_paymentEndpoint
#print axioms rationalUpper_lt_paymentEndpoint
#check paymentEndpoint_exact
#print axioms paymentEndpoint_exact
#check debitCeiling
#print axioms debitCeiling
#check paymentEndpoint_lt_debitCeiling
#print axioms paymentEndpoint_lt_debitCeiling
#check rationalUpper_lt_debitCeiling
#print axioms rationalUpper_lt_debitCeiling
#check weightedDebit_lt_debitCeiling
#print axioms weightedDebit_lt_debitCeiling
#check quarterDebit_lt
#print axioms quarterDebit_lt

#check otherNumerator
#print axioms otherNumerator
#check paidCoefficient
#print axioms paidCoefficient
#check ceilingCoefficient
#print axioms ceilingCoefficient
#check Qoriginal_exact
#print axioms Qoriginal_exact
#check paidCoefficient_le_Qoriginal
#print axioms paidCoefficient_le_Qoriginal
#check ceilingCoefficient_lt_paidCoefficient
#print axioms ceilingCoefficient_lt_paidCoefficient
#check ceilingCoefficient_lt_Qoriginal
#print axioms ceilingCoefficient_lt_Qoriginal
#check ceilingCoefficient_exact
#print axioms ceilingCoefficient_exact
#check remaining_budget_suffices
#print axioms remaining_budget_suffices
#check paid_ordinary_P2_parameters
#print axioms paid_ordinary_P2_parameters
#check paid_ordinary_P2
#print axioms paid_ordinary_P2
#check ceiling_ordinary_P2
#print axioms ceiling_ordinary_P2

#print weightedDebit
#print analyticUpper
#print rationalJUpper
#print rationalUpper
#print paymentEndpoint
#print debitCeiling
#print otherNumerator
#print paidCoefficient
#print ceilingCoefficient

#check JJointEnvelope.complete_mixture
#print axioms JJointEnvelope.complete_mixture
#check JJointPayment.lower_payment
#print axioms JJointPayment.lower_payment
#check U8ActualThreshold.exact_weight_gain_bounds
#print axioms U8ActualThreshold.exact_weight_gain_bounds
#check Wu08FourMother.ordinary_P2_parameters
#print axioms Wu08FourMother.ordinary_P2_parameters

end WuTarget.W12

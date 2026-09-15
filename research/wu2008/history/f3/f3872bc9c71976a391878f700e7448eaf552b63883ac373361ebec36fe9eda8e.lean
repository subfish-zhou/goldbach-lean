import JJointPayment
import Wu08FourMotherTerminal

namespace WuTarget.W12

#check JJointEnvelope.complete_mixture
#check JJointEnvelope.gain_packet_identity
#check JJointPayment.lower_payment
#check JJointPayment.gain_bounds
#check Wu2008DoubleSieve.GlobalSignedActualComparison.log_two
#check Wu2008DoubleSieve.JointLogTotalComparison.log_le_V
#check U8ActualThreshold.exact_weight_gain_bounds
#check U8ActualThreshold.gainLower_exact
#check Wu08FourMother.ordinary_P2_parameters
#check Wu08FourMother.ordinary_P2
#print Wu08TerminalAlignment.eighthMain
#print Wu2008DoubleSieve.UnroundedPayments.weightedJUpper
#print Wu2008DoubleSieve.UnroundedPayments.j7Upper
#print Wu2008DoubleSieve.UnroundedPayments.j8Upper
#print Wu2008DoubleSieve.UnroundedPayments.j9Upper
#print axioms JJointEnvelope.complete_mixture
#print axioms JJointPayment.lower_payment
#print axioms U8ActualThreshold.exact_weight_gain_bounds
#print axioms Wu08FourMother.ordinary_P2

end WuTarget.W12

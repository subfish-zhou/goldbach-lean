import JJointPayment
import Wu08FourMotherTerminal

namespace WuTarget.W12

#check JJointEnvelope.complete_mixture
#check JJointEnvelope.gain_packet_identity
#check JJointPayment.lower_payment
#check JJointPayment.gain_bounds
#check Wu2008DoubleSieve.GlobalSignedActualComparison.log_two
#check Wu2008DoubleSieve.JointLogTotalComparison.log_le_V
#check Wu2008DoubleSieve.U8ActualThreshold.exact_weight_gain_bounds
#check U8CanonicalMother.improved_gain_certificate
#check Wu08FourMother.ordinary_P2
#check Wu08FourMother.Qoriginal
#print Wu08TerminalAlignment.eighthMain
#print axioms JJointEnvelope.complete_mixture
#print axioms JJointPayment.lower_payment
#print axioms U8CanonicalMother.improved_gain_certificate
#print axioms Wu08FourMother.ordinary_P2

end WuTarget.W12

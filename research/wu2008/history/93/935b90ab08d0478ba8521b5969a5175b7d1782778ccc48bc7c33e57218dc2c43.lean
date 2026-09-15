import WE10FourMajorWeighted

namespace WuSource.SrcFour
open Wu2008DoubleSieve FourRoughClosedMass
#print truncatedSixthLowerAlpha
#print truncatedSixthLowerBeta
#print truncatedSixthLowerLambda
#print regularKernel
#print regularInner10
#print regularInner11
#print regularMiddle10
#print regularMiddle11
#print regularOuter10
#print regularOuter11
#check @regularKernel_continuous
#check @Wu08FourMother.original_pair_paid
#check @WuTarget.W13Tight.moment_upper
#check @intervalIntegral.integral_mono_on
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#print axioms WuTarget.E10FourMajor.original_pair_upper
end WuSource.SrcFour

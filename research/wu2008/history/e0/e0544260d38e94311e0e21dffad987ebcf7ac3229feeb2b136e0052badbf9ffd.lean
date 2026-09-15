import WSrcSingleGridInstance
import WSrcFifthGridInstance
import WSrcSixthGridInstance
import WSourceRevisedClosureBudget

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000

#check @WuTarget.SourceNodeInstance.uniform_certificate
#check @WuTarget.SourceSingleInstance.actual_single_count
#check @WuTarget.SourceFifthInstance.actual_fifth_count
#check @WuTarget.SourceSixthInstance.actual_sixth_count
#check @WuTarget.SourceFourAccepted.original_pair_enclosure
#check @WuSource.SrcFourEnclosure.actual_pair_upper
#check @WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget
#print WuTarget.SourceNodeInstance.H
#print WuTarget.SourceNodeInstance.h
#print WuTarget.SourceSingleInstance.amount
#print WuTarget.SourceFifthInstance.amount
#print WuTarget.SourceSixthInstance.amount
#print axioms WuTarget.SourceNodeInstance.uniform_certificate
#print axioms WuTarget.SourceSingleInstance.actual_single_count
#print axioms WuTarget.SourceFifthInstance.actual_fifth_count
#print axioms WuTarget.SourceSixthInstance.actual_sixth_count
#print axioms WuTarget.SourceFourAccepted.original_pair_enclosure
#print axioms WuSource.SrcFourEnclosure.actual_pair_upper
#print axioms WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget

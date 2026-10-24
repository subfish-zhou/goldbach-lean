import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint140
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_140 (j : Fin 64) (hj : 64*140+j.val < 10541) :
    OuterPoint (64*140+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8960
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8961
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8962
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8963
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8964
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8965
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8966
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8967
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8968
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8969
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8970
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8971
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8972
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8973
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8974
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8975
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8976
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8977
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8978
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8979
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8980
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8981
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8982
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8983
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8984
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8985
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8986
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8987
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8988
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8989
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8990
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8991
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8992
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8993
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8994
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8995
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8996
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8997
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8998
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8999
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9000
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9001
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9002
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9003
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9004
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9005
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9006
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9007
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9008
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9009
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9010
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9011
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9012
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9013
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9014
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9015
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9016
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9017
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9018
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9019
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9020
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9021
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9022
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_140

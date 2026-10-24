import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay140
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_140 (j : Fin 64) (hj : 64*140+j.val < 10540) :
    OuterPay (64*140+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8960
  · exact WuPaper.ClassicalFourthNat.outerPay_8961
  · exact WuPaper.ClassicalFourthNat.outerPay_8962
  · exact WuPaper.ClassicalFourthNat.outerPay_8963
  · exact WuPaper.ClassicalFourthNat.outerPay_8964
  · exact WuPaper.ClassicalFourthNat.outerPay_8965
  · exact WuPaper.ClassicalFourthNat.outerPay_8966
  · exact WuPaper.ClassicalFourthNat.outerPay_8967
  · exact WuPaper.ClassicalFourthNat.outerPay_8968
  · exact WuPaper.ClassicalFourthNat.outerPay_8969
  · exact WuPaper.ClassicalFourthNat.outerPay_8970
  · exact WuPaper.ClassicalFourthNat.outerPay_8971
  · exact WuPaper.ClassicalFourthNat.outerPay_8972
  · exact WuPaper.ClassicalFourthNat.outerPay_8973
  · exact WuPaper.ClassicalFourthNat.outerPay_8974
  · exact WuPaper.ClassicalFourthNat.outerPay_8975
  · exact WuPaper.ClassicalFourthNat.outerPay_8976
  · exact WuPaper.ClassicalFourthNat.outerPay_8977
  · exact WuPaper.ClassicalFourthNat.outerPay_8978
  · exact WuPaper.ClassicalFourthNat.outerPay_8979
  · exact WuPaper.ClassicalFourthNat.outerPay_8980
  · exact WuPaper.ClassicalFourthNat.outerPay_8981
  · exact WuPaper.ClassicalFourthNat.outerPay_8982
  · exact WuPaper.ClassicalFourthNat.outerPay_8983
  · exact WuPaper.ClassicalFourthNat.outerPay_8984
  · exact WuPaper.ClassicalFourthNat.outerPay_8985
  · exact WuPaper.ClassicalFourthNat.outerPay_8986
  · exact WuPaper.ClassicalFourthNat.outerPay_8987
  · exact WuPaper.ClassicalFourthNat.outerPay_8988
  · exact WuPaper.ClassicalFourthNat.outerPay_8989
  · exact WuPaper.ClassicalFourthNat.outerPay_8990
  · exact WuPaper.ClassicalFourthNat.outerPay_8991
  · exact WuPaper.ClassicalFourthNat.outerPay_8992
  · exact WuPaper.ClassicalFourthNat.outerPay_8993
  · exact WuPaper.ClassicalFourthNat.outerPay_8994
  · exact WuPaper.ClassicalFourthNat.outerPay_8995
  · exact WuPaper.ClassicalFourthNat.outerPay_8996
  · exact WuPaper.ClassicalFourthNat.outerPay_8997
  · exact WuPaper.ClassicalFourthNat.outerPay_8998
  · exact WuPaper.ClassicalFourthNat.outerPay_8999
  · exact WuPaper.ClassicalFourthNat.outerPay_9000
  · exact WuPaper.ClassicalFourthNat.outerPay_9001
  · exact WuPaper.ClassicalFourthNat.outerPay_9002
  · exact WuPaper.ClassicalFourthNat.outerPay_9003
  · exact WuPaper.ClassicalFourthNat.outerPay_9004
  · exact WuPaper.ClassicalFourthNat.outerPay_9005
  · exact WuPaper.ClassicalFourthNat.outerPay_9006
  · exact WuPaper.ClassicalFourthNat.outerPay_9007
  · exact WuPaper.ClassicalFourthNat.outerPay_9008
  · exact WuPaper.ClassicalFourthNat.outerPay_9009
  · exact WuPaper.ClassicalFourthNat.outerPay_9010
  · exact WuPaper.ClassicalFourthNat.outerPay_9011
  · exact WuPaper.ClassicalFourthNat.outerPay_9012
  · exact WuPaper.ClassicalFourthNat.outerPay_9013
  · exact WuPaper.ClassicalFourthNat.outerPay_9014
  · exact WuPaper.ClassicalFourthNat.outerPay_9015
  · exact WuPaper.ClassicalFourthNat.outerPay_9016
  · exact WuPaper.ClassicalFourthNat.outerPay_9017
  · exact WuPaper.ClassicalFourthNat.outerPay_9018
  · exact WuPaper.ClassicalFourthNat.outerPay_9019
  · exact WuPaper.ClassicalFourthNat.outerPay_9020
  · exact WuPaper.ClassicalFourthNat.outerPay_9021
  · exact WuPaper.ClassicalFourthNat.outerPay_9022
  · exact WuPaper.ClassicalFourthNat.outerPay_9023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_140

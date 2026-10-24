import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay140
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_140 (j : Fin 64) (hj : 64*140+j.val < 10540) :
    BPay (64*140+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8960
  · exact WuPaper.ClassicalFourthNat.BPay_8961
  · exact WuPaper.ClassicalFourthNat.BPay_8962
  · exact WuPaper.ClassicalFourthNat.BPay_8963
  · exact WuPaper.ClassicalFourthNat.BPay_8964
  · exact WuPaper.ClassicalFourthNat.BPay_8965
  · exact WuPaper.ClassicalFourthNat.BPay_8966
  · exact WuPaper.ClassicalFourthNat.BPay_8967
  · exact WuPaper.ClassicalFourthNat.BPay_8968
  · exact WuPaper.ClassicalFourthNat.BPay_8969
  · exact WuPaper.ClassicalFourthNat.BPay_8970
  · exact WuPaper.ClassicalFourthNat.BPay_8971
  · exact WuPaper.ClassicalFourthNat.BPay_8972
  · exact WuPaper.ClassicalFourthNat.BPay_8973
  · exact WuPaper.ClassicalFourthNat.BPay_8974
  · exact WuPaper.ClassicalFourthNat.BPay_8975
  · exact WuPaper.ClassicalFourthNat.BPay_8976
  · exact WuPaper.ClassicalFourthNat.BPay_8977
  · exact WuPaper.ClassicalFourthNat.BPay_8978
  · exact WuPaper.ClassicalFourthNat.BPay_8979
  · exact WuPaper.ClassicalFourthNat.BPay_8980
  · exact WuPaper.ClassicalFourthNat.BPay_8981
  · exact WuPaper.ClassicalFourthNat.BPay_8982
  · exact WuPaper.ClassicalFourthNat.BPay_8983
  · exact WuPaper.ClassicalFourthNat.BPay_8984
  · exact WuPaper.ClassicalFourthNat.BPay_8985
  · exact WuPaper.ClassicalFourthNat.BPay_8986
  · exact WuPaper.ClassicalFourthNat.BPay_8987
  · exact WuPaper.ClassicalFourthNat.BPay_8988
  · exact WuPaper.ClassicalFourthNat.BPay_8989
  · exact WuPaper.ClassicalFourthNat.BPay_8990
  · exact WuPaper.ClassicalFourthNat.BPay_8991
  · exact WuPaper.ClassicalFourthNat.BPay_8992
  · exact WuPaper.ClassicalFourthNat.BPay_8993
  · exact WuPaper.ClassicalFourthNat.BPay_8994
  · exact WuPaper.ClassicalFourthNat.BPay_8995
  · exact WuPaper.ClassicalFourthNat.BPay_8996
  · exact WuPaper.ClassicalFourthNat.BPay_8997
  · exact WuPaper.ClassicalFourthNat.BPay_8998
  · exact WuPaper.ClassicalFourthNat.BPay_8999
  · exact WuPaper.ClassicalFourthNat.BPay_9000
  · exact WuPaper.ClassicalFourthNat.BPay_9001
  · exact WuPaper.ClassicalFourthNat.BPay_9002
  · exact WuPaper.ClassicalFourthNat.BPay_9003
  · exact WuPaper.ClassicalFourthNat.BPay_9004
  · exact WuPaper.ClassicalFourthNat.BPay_9005
  · exact WuPaper.ClassicalFourthNat.BPay_9006
  · exact WuPaper.ClassicalFourthNat.BPay_9007
  · exact WuPaper.ClassicalFourthNat.BPay_9008
  · exact WuPaper.ClassicalFourthNat.BPay_9009
  · exact WuPaper.ClassicalFourthNat.BPay_9010
  · exact WuPaper.ClassicalFourthNat.BPay_9011
  · exact WuPaper.ClassicalFourthNat.BPay_9012
  · exact WuPaper.ClassicalFourthNat.BPay_9013
  · exact WuPaper.ClassicalFourthNat.BPay_9014
  · exact WuPaper.ClassicalFourthNat.BPay_9015
  · exact WuPaper.ClassicalFourthNat.BPay_9016
  · exact WuPaper.ClassicalFourthNat.BPay_9017
  · exact WuPaper.ClassicalFourthNat.BPay_9018
  · exact WuPaper.ClassicalFourthNat.BPay_9019
  · exact WuPaper.ClassicalFourthNat.BPay_9020
  · exact WuPaper.ClassicalFourthNat.BPay_9021
  · exact WuPaper.ClassicalFourthNat.BPay_9022
  · exact WuPaper.ClassicalFourthNat.BPay_9023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_140

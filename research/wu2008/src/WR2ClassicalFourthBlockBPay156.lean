import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay156
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_156 (j : Fin 64) (hj : 64*156+j.val < 10540) :
    BPay (64*156+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9984
  · exact WuPaper.ClassicalFourthNat.BPay_9985
  · exact WuPaper.ClassicalFourthNat.BPay_9986
  · exact WuPaper.ClassicalFourthNat.BPay_9987
  · exact WuPaper.ClassicalFourthNat.BPay_9988
  · exact WuPaper.ClassicalFourthNat.BPay_9989
  · exact WuPaper.ClassicalFourthNat.BPay_9990
  · exact WuPaper.ClassicalFourthNat.BPay_9991
  · exact WuPaper.ClassicalFourthNat.BPay_9992
  · exact WuPaper.ClassicalFourthNat.BPay_9993
  · exact WuPaper.ClassicalFourthNat.BPay_9994
  · exact WuPaper.ClassicalFourthNat.BPay_9995
  · exact WuPaper.ClassicalFourthNat.BPay_9996
  · exact WuPaper.ClassicalFourthNat.BPay_9997
  · exact WuPaper.ClassicalFourthNat.BPay_9998
  · exact WuPaper.ClassicalFourthNat.BPay_9999
  · exact WuPaper.ClassicalFourthNat.BPay_10000
  · exact WuPaper.ClassicalFourthNat.BPay_10001
  · exact WuPaper.ClassicalFourthNat.BPay_10002
  · exact WuPaper.ClassicalFourthNat.BPay_10003
  · exact WuPaper.ClassicalFourthNat.BPay_10004
  · exact WuPaper.ClassicalFourthNat.BPay_10005
  · exact WuPaper.ClassicalFourthNat.BPay_10006
  · exact WuPaper.ClassicalFourthNat.BPay_10007
  · exact WuPaper.ClassicalFourthNat.BPay_10008
  · exact WuPaper.ClassicalFourthNat.BPay_10009
  · exact WuPaper.ClassicalFourthNat.BPay_10010
  · exact WuPaper.ClassicalFourthNat.BPay_10011
  · exact WuPaper.ClassicalFourthNat.BPay_10012
  · exact WuPaper.ClassicalFourthNat.BPay_10013
  · exact WuPaper.ClassicalFourthNat.BPay_10014
  · exact WuPaper.ClassicalFourthNat.BPay_10015
  · exact WuPaper.ClassicalFourthNat.BPay_10016
  · exact WuPaper.ClassicalFourthNat.BPay_10017
  · exact WuPaper.ClassicalFourthNat.BPay_10018
  · exact WuPaper.ClassicalFourthNat.BPay_10019
  · exact WuPaper.ClassicalFourthNat.BPay_10020
  · exact WuPaper.ClassicalFourthNat.BPay_10021
  · exact WuPaper.ClassicalFourthNat.BPay_10022
  · exact WuPaper.ClassicalFourthNat.BPay_10023
  · exact WuPaper.ClassicalFourthNat.BPay_10024
  · exact WuPaper.ClassicalFourthNat.BPay_10025
  · exact WuPaper.ClassicalFourthNat.BPay_10026
  · exact WuPaper.ClassicalFourthNat.BPay_10027
  · exact WuPaper.ClassicalFourthNat.BPay_10028
  · exact WuPaper.ClassicalFourthNat.BPay_10029
  · exact WuPaper.ClassicalFourthNat.BPay_10030
  · exact WuPaper.ClassicalFourthNat.BPay_10031
  · exact WuPaper.ClassicalFourthNat.BPay_10032
  · exact WuPaper.ClassicalFourthNat.BPay_10033
  · exact WuPaper.ClassicalFourthNat.BPay_10034
  · exact WuPaper.ClassicalFourthNat.BPay_10035
  · exact WuPaper.ClassicalFourthNat.BPay_10036
  · exact WuPaper.ClassicalFourthNat.BPay_10037
  · exact WuPaper.ClassicalFourthNat.BPay_10038
  · exact WuPaper.ClassicalFourthNat.BPay_10039
  · exact WuPaper.ClassicalFourthNat.BPay_10040
  · exact WuPaper.ClassicalFourthNat.BPay_10041
  · exact WuPaper.ClassicalFourthNat.BPay_10042
  · exact WuPaper.ClassicalFourthNat.BPay_10043
  · exact WuPaper.ClassicalFourthNat.BPay_10044
  · exact WuPaper.ClassicalFourthNat.BPay_10045
  · exact WuPaper.ClassicalFourthNat.BPay_10046
  · exact WuPaper.ClassicalFourthNat.BPay_10047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_156

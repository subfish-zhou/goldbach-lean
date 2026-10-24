import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay078
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_078 (j : Fin 64) (hj : 64*78+j.val < 10540) :
    BPay (64*78+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4992
  · exact WuPaper.ClassicalFourthNat.BPay_4993
  · exact WuPaper.ClassicalFourthNat.BPay_4994
  · exact WuPaper.ClassicalFourthNat.BPay_4995
  · exact WuPaper.ClassicalFourthNat.BPay_4996
  · exact WuPaper.ClassicalFourthNat.BPay_4997
  · exact WuPaper.ClassicalFourthNat.BPay_4998
  · exact WuPaper.ClassicalFourthNat.BPay_4999
  · exact WuPaper.ClassicalFourthNat.BPay_5000
  · exact WuPaper.ClassicalFourthNat.BPay_5001
  · exact WuPaper.ClassicalFourthNat.BPay_5002
  · exact WuPaper.ClassicalFourthNat.BPay_5003
  · exact WuPaper.ClassicalFourthNat.BPay_5004
  · exact WuPaper.ClassicalFourthNat.BPay_5005
  · exact WuPaper.ClassicalFourthNat.BPay_5006
  · exact WuPaper.ClassicalFourthNat.BPay_5007
  · exact WuPaper.ClassicalFourthNat.BPay_5008
  · exact WuPaper.ClassicalFourthNat.BPay_5009
  · exact WuPaper.ClassicalFourthNat.BPay_5010
  · exact WuPaper.ClassicalFourthNat.BPay_5011
  · exact WuPaper.ClassicalFourthNat.BPay_5012
  · exact WuPaper.ClassicalFourthNat.BPay_5013
  · exact WuPaper.ClassicalFourthNat.BPay_5014
  · exact WuPaper.ClassicalFourthNat.BPay_5015
  · exact WuPaper.ClassicalFourthNat.BPay_5016
  · exact WuPaper.ClassicalFourthNat.BPay_5017
  · exact WuPaper.ClassicalFourthNat.BPay_5018
  · exact WuPaper.ClassicalFourthNat.BPay_5019
  · exact WuPaper.ClassicalFourthNat.BPay_5020
  · exact WuPaper.ClassicalFourthNat.BPay_5021
  · exact WuPaper.ClassicalFourthNat.BPay_5022
  · exact WuPaper.ClassicalFourthNat.BPay_5023
  · exact WuPaper.ClassicalFourthNat.BPay_5024
  · exact WuPaper.ClassicalFourthNat.BPay_5025
  · exact WuPaper.ClassicalFourthNat.BPay_5026
  · exact WuPaper.ClassicalFourthNat.BPay_5027
  · exact WuPaper.ClassicalFourthNat.BPay_5028
  · exact WuPaper.ClassicalFourthNat.BPay_5029
  · exact WuPaper.ClassicalFourthNat.BPay_5030
  · exact WuPaper.ClassicalFourthNat.BPay_5031
  · exact WuPaper.ClassicalFourthNat.BPay_5032
  · exact WuPaper.ClassicalFourthNat.BPay_5033
  · exact WuPaper.ClassicalFourthNat.BPay_5034
  · exact WuPaper.ClassicalFourthNat.BPay_5035
  · exact WuPaper.ClassicalFourthNat.BPay_5036
  · exact WuPaper.ClassicalFourthNat.BPay_5037
  · exact WuPaper.ClassicalFourthNat.BPay_5038
  · exact WuPaper.ClassicalFourthNat.BPay_5039
  · exact WuPaper.ClassicalFourthNat.BPay_5040
  · exact WuPaper.ClassicalFourthNat.BPay_5041
  · exact WuPaper.ClassicalFourthNat.BPay_5042
  · exact WuPaper.ClassicalFourthNat.BPay_5043
  · exact WuPaper.ClassicalFourthNat.BPay_5044
  · exact WuPaper.ClassicalFourthNat.BPay_5045
  · exact WuPaper.ClassicalFourthNat.BPay_5046
  · exact WuPaper.ClassicalFourthNat.BPay_5047
  · exact WuPaper.ClassicalFourthNat.BPay_5048
  · exact WuPaper.ClassicalFourthNat.BPay_5049
  · exact WuPaper.ClassicalFourthNat.BPay_5050
  · exact WuPaper.ClassicalFourthNat.BPay_5051
  · exact WuPaper.ClassicalFourthNat.BPay_5052
  · exact WuPaper.ClassicalFourthNat.BPay_5053
  · exact WuPaper.ClassicalFourthNat.BPay_5054
  · exact WuPaper.ClassicalFourthNat.BPay_5055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_078

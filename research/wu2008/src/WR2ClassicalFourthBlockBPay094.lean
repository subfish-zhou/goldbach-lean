import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay094
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_094 (j : Fin 64) (hj : 64*94+j.val < 10540) :
    BPay (64*94+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6016
  · exact WuPaper.ClassicalFourthNat.BPay_6017
  · exact WuPaper.ClassicalFourthNat.BPay_6018
  · exact WuPaper.ClassicalFourthNat.BPay_6019
  · exact WuPaper.ClassicalFourthNat.BPay_6020
  · exact WuPaper.ClassicalFourthNat.BPay_6021
  · exact WuPaper.ClassicalFourthNat.BPay_6022
  · exact WuPaper.ClassicalFourthNat.BPay_6023
  · exact WuPaper.ClassicalFourthNat.BPay_6024
  · exact WuPaper.ClassicalFourthNat.BPay_6025
  · exact WuPaper.ClassicalFourthNat.BPay_6026
  · exact WuPaper.ClassicalFourthNat.BPay_6027
  · exact WuPaper.ClassicalFourthNat.BPay_6028
  · exact WuPaper.ClassicalFourthNat.BPay_6029
  · exact WuPaper.ClassicalFourthNat.BPay_6030
  · exact WuPaper.ClassicalFourthNat.BPay_6031
  · exact WuPaper.ClassicalFourthNat.BPay_6032
  · exact WuPaper.ClassicalFourthNat.BPay_6033
  · exact WuPaper.ClassicalFourthNat.BPay_6034
  · exact WuPaper.ClassicalFourthNat.BPay_6035
  · exact WuPaper.ClassicalFourthNat.BPay_6036
  · exact WuPaper.ClassicalFourthNat.BPay_6037
  · exact WuPaper.ClassicalFourthNat.BPay_6038
  · exact WuPaper.ClassicalFourthNat.BPay_6039
  · exact WuPaper.ClassicalFourthNat.BPay_6040
  · exact WuPaper.ClassicalFourthNat.BPay_6041
  · exact WuPaper.ClassicalFourthNat.BPay_6042
  · exact WuPaper.ClassicalFourthNat.BPay_6043
  · exact WuPaper.ClassicalFourthNat.BPay_6044
  · exact WuPaper.ClassicalFourthNat.BPay_6045
  · exact WuPaper.ClassicalFourthNat.BPay_6046
  · exact WuPaper.ClassicalFourthNat.BPay_6047
  · exact WuPaper.ClassicalFourthNat.BPay_6048
  · exact WuPaper.ClassicalFourthNat.BPay_6049
  · exact WuPaper.ClassicalFourthNat.BPay_6050
  · exact WuPaper.ClassicalFourthNat.BPay_6051
  · exact WuPaper.ClassicalFourthNat.BPay_6052
  · exact WuPaper.ClassicalFourthNat.BPay_6053
  · exact WuPaper.ClassicalFourthNat.BPay_6054
  · exact WuPaper.ClassicalFourthNat.BPay_6055
  · exact WuPaper.ClassicalFourthNat.BPay_6056
  · exact WuPaper.ClassicalFourthNat.BPay_6057
  · exact WuPaper.ClassicalFourthNat.BPay_6058
  · exact WuPaper.ClassicalFourthNat.BPay_6059
  · exact WuPaper.ClassicalFourthNat.BPay_6060
  · exact WuPaper.ClassicalFourthNat.BPay_6061
  · exact WuPaper.ClassicalFourthNat.BPay_6062
  · exact WuPaper.ClassicalFourthNat.BPay_6063
  · exact WuPaper.ClassicalFourthNat.BPay_6064
  · exact WuPaper.ClassicalFourthNat.BPay_6065
  · exact WuPaper.ClassicalFourthNat.BPay_6066
  · exact WuPaper.ClassicalFourthNat.BPay_6067
  · exact WuPaper.ClassicalFourthNat.BPay_6068
  · exact WuPaper.ClassicalFourthNat.BPay_6069
  · exact WuPaper.ClassicalFourthNat.BPay_6070
  · exact WuPaper.ClassicalFourthNat.BPay_6071
  · exact WuPaper.ClassicalFourthNat.BPay_6072
  · exact WuPaper.ClassicalFourthNat.BPay_6073
  · exact WuPaper.ClassicalFourthNat.BPay_6074
  · exact WuPaper.ClassicalFourthNat.BPay_6075
  · exact WuPaper.ClassicalFourthNat.BPay_6076
  · exact WuPaper.ClassicalFourthNat.BPay_6077
  · exact WuPaper.ClassicalFourthNat.BPay_6078
  · exact WuPaper.ClassicalFourthNat.BPay_6079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_094

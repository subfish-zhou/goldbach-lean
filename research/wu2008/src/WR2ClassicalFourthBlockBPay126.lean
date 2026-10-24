import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay126
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_126 (j : Fin 64) (hj : 64*126+j.val < 10540) :
    BPay (64*126+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8064
  · exact WuPaper.ClassicalFourthNat.BPay_8065
  · exact WuPaper.ClassicalFourthNat.BPay_8066
  · exact WuPaper.ClassicalFourthNat.BPay_8067
  · exact WuPaper.ClassicalFourthNat.BPay_8068
  · exact WuPaper.ClassicalFourthNat.BPay_8069
  · exact WuPaper.ClassicalFourthNat.BPay_8070
  · exact WuPaper.ClassicalFourthNat.BPay_8071
  · exact WuPaper.ClassicalFourthNat.BPay_8072
  · exact WuPaper.ClassicalFourthNat.BPay_8073
  · exact WuPaper.ClassicalFourthNat.BPay_8074
  · exact WuPaper.ClassicalFourthNat.BPay_8075
  · exact WuPaper.ClassicalFourthNat.BPay_8076
  · exact WuPaper.ClassicalFourthNat.BPay_8077
  · exact WuPaper.ClassicalFourthNat.BPay_8078
  · exact WuPaper.ClassicalFourthNat.BPay_8079
  · exact WuPaper.ClassicalFourthNat.BPay_8080
  · exact WuPaper.ClassicalFourthNat.BPay_8081
  · exact WuPaper.ClassicalFourthNat.BPay_8082
  · exact WuPaper.ClassicalFourthNat.BPay_8083
  · exact WuPaper.ClassicalFourthNat.BPay_8084
  · exact WuPaper.ClassicalFourthNat.BPay_8085
  · exact WuPaper.ClassicalFourthNat.BPay_8086
  · exact WuPaper.ClassicalFourthNat.BPay_8087
  · exact WuPaper.ClassicalFourthNat.BPay_8088
  · exact WuPaper.ClassicalFourthNat.BPay_8089
  · exact WuPaper.ClassicalFourthNat.BPay_8090
  · exact WuPaper.ClassicalFourthNat.BPay_8091
  · exact WuPaper.ClassicalFourthNat.BPay_8092
  · exact WuPaper.ClassicalFourthNat.BPay_8093
  · exact WuPaper.ClassicalFourthNat.BPay_8094
  · exact WuPaper.ClassicalFourthNat.BPay_8095
  · exact WuPaper.ClassicalFourthNat.BPay_8096
  · exact WuPaper.ClassicalFourthNat.BPay_8097
  · exact WuPaper.ClassicalFourthNat.BPay_8098
  · exact WuPaper.ClassicalFourthNat.BPay_8099
  · exact WuPaper.ClassicalFourthNat.BPay_8100
  · exact WuPaper.ClassicalFourthNat.BPay_8101
  · exact WuPaper.ClassicalFourthNat.BPay_8102
  · exact WuPaper.ClassicalFourthNat.BPay_8103
  · exact WuPaper.ClassicalFourthNat.BPay_8104
  · exact WuPaper.ClassicalFourthNat.BPay_8105
  · exact WuPaper.ClassicalFourthNat.BPay_8106
  · exact WuPaper.ClassicalFourthNat.BPay_8107
  · exact WuPaper.ClassicalFourthNat.BPay_8108
  · exact WuPaper.ClassicalFourthNat.BPay_8109
  · exact WuPaper.ClassicalFourthNat.BPay_8110
  · exact WuPaper.ClassicalFourthNat.BPay_8111
  · exact WuPaper.ClassicalFourthNat.BPay_8112
  · exact WuPaper.ClassicalFourthNat.BPay_8113
  · exact WuPaper.ClassicalFourthNat.BPay_8114
  · exact WuPaper.ClassicalFourthNat.BPay_8115
  · exact WuPaper.ClassicalFourthNat.BPay_8116
  · exact WuPaper.ClassicalFourthNat.BPay_8117
  · exact WuPaper.ClassicalFourthNat.BPay_8118
  · exact WuPaper.ClassicalFourthNat.BPay_8119
  · exact WuPaper.ClassicalFourthNat.BPay_8120
  · exact WuPaper.ClassicalFourthNat.BPay_8121
  · exact WuPaper.ClassicalFourthNat.BPay_8122
  · exact WuPaper.ClassicalFourthNat.BPay_8123
  · exact WuPaper.ClassicalFourthNat.BPay_8124
  · exact WuPaper.ClassicalFourthNat.BPay_8125
  · exact WuPaper.ClassicalFourthNat.BPay_8126
  · exact WuPaper.ClassicalFourthNat.BPay_8127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_126

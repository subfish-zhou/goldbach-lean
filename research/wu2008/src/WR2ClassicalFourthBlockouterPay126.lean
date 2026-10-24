import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay126
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_126 (j : Fin 64) (hj : 64*126+j.val < 10540) :
    OuterPay (64*126+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8064
  · exact WuPaper.ClassicalFourthNat.outerPay_8065
  · exact WuPaper.ClassicalFourthNat.outerPay_8066
  · exact WuPaper.ClassicalFourthNat.outerPay_8067
  · exact WuPaper.ClassicalFourthNat.outerPay_8068
  · exact WuPaper.ClassicalFourthNat.outerPay_8069
  · exact WuPaper.ClassicalFourthNat.outerPay_8070
  · exact WuPaper.ClassicalFourthNat.outerPay_8071
  · exact WuPaper.ClassicalFourthNat.outerPay_8072
  · exact WuPaper.ClassicalFourthNat.outerPay_8073
  · exact WuPaper.ClassicalFourthNat.outerPay_8074
  · exact WuPaper.ClassicalFourthNat.outerPay_8075
  · exact WuPaper.ClassicalFourthNat.outerPay_8076
  · exact WuPaper.ClassicalFourthNat.outerPay_8077
  · exact WuPaper.ClassicalFourthNat.outerPay_8078
  · exact WuPaper.ClassicalFourthNat.outerPay_8079
  · exact WuPaper.ClassicalFourthNat.outerPay_8080
  · exact WuPaper.ClassicalFourthNat.outerPay_8081
  · exact WuPaper.ClassicalFourthNat.outerPay_8082
  · exact WuPaper.ClassicalFourthNat.outerPay_8083
  · exact WuPaper.ClassicalFourthNat.outerPay_8084
  · exact WuPaper.ClassicalFourthNat.outerPay_8085
  · exact WuPaper.ClassicalFourthNat.outerPay_8086
  · exact WuPaper.ClassicalFourthNat.outerPay_8087
  · exact WuPaper.ClassicalFourthNat.outerPay_8088
  · exact WuPaper.ClassicalFourthNat.outerPay_8089
  · exact WuPaper.ClassicalFourthNat.outerPay_8090
  · exact WuPaper.ClassicalFourthNat.outerPay_8091
  · exact WuPaper.ClassicalFourthNat.outerPay_8092
  · exact WuPaper.ClassicalFourthNat.outerPay_8093
  · exact WuPaper.ClassicalFourthNat.outerPay_8094
  · exact WuPaper.ClassicalFourthNat.outerPay_8095
  · exact WuPaper.ClassicalFourthNat.outerPay_8096
  · exact WuPaper.ClassicalFourthNat.outerPay_8097
  · exact WuPaper.ClassicalFourthNat.outerPay_8098
  · exact WuPaper.ClassicalFourthNat.outerPay_8099
  · exact WuPaper.ClassicalFourthNat.outerPay_8100
  · exact WuPaper.ClassicalFourthNat.outerPay_8101
  · exact WuPaper.ClassicalFourthNat.outerPay_8102
  · exact WuPaper.ClassicalFourthNat.outerPay_8103
  · exact WuPaper.ClassicalFourthNat.outerPay_8104
  · exact WuPaper.ClassicalFourthNat.outerPay_8105
  · exact WuPaper.ClassicalFourthNat.outerPay_8106
  · exact WuPaper.ClassicalFourthNat.outerPay_8107
  · exact WuPaper.ClassicalFourthNat.outerPay_8108
  · exact WuPaper.ClassicalFourthNat.outerPay_8109
  · exact WuPaper.ClassicalFourthNat.outerPay_8110
  · exact WuPaper.ClassicalFourthNat.outerPay_8111
  · exact WuPaper.ClassicalFourthNat.outerPay_8112
  · exact WuPaper.ClassicalFourthNat.outerPay_8113
  · exact WuPaper.ClassicalFourthNat.outerPay_8114
  · exact WuPaper.ClassicalFourthNat.outerPay_8115
  · exact WuPaper.ClassicalFourthNat.outerPay_8116
  · exact WuPaper.ClassicalFourthNat.outerPay_8117
  · exact WuPaper.ClassicalFourthNat.outerPay_8118
  · exact WuPaper.ClassicalFourthNat.outerPay_8119
  · exact WuPaper.ClassicalFourthNat.outerPay_8120
  · exact WuPaper.ClassicalFourthNat.outerPay_8121
  · exact WuPaper.ClassicalFourthNat.outerPay_8122
  · exact WuPaper.ClassicalFourthNat.outerPay_8123
  · exact WuPaper.ClassicalFourthNat.outerPay_8124
  · exact WuPaper.ClassicalFourthNat.outerPay_8125
  · exact WuPaper.ClassicalFourthNat.outerPay_8126
  · exact WuPaper.ClassicalFourthNat.outerPay_8127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_126

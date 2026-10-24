import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay095
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_095 (j : Fin 64) (hj : 64*95+j.val < 10540) :
    OuterPay (64*95+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6080
  · exact WuPaper.ClassicalFourthNat.outerPay_6081
  · exact WuPaper.ClassicalFourthNat.outerPay_6082
  · exact WuPaper.ClassicalFourthNat.outerPay_6083
  · exact WuPaper.ClassicalFourthNat.outerPay_6084
  · exact WuPaper.ClassicalFourthNat.outerPay_6085
  · exact WuPaper.ClassicalFourthNat.outerPay_6086
  · exact WuPaper.ClassicalFourthNat.outerPay_6087
  · exact WuPaper.ClassicalFourthNat.outerPay_6088
  · exact WuPaper.ClassicalFourthNat.outerPay_6089
  · exact WuPaper.ClassicalFourthNat.outerPay_6090
  · exact WuPaper.ClassicalFourthNat.outerPay_6091
  · exact WuPaper.ClassicalFourthNat.outerPay_6092
  · exact WuPaper.ClassicalFourthNat.outerPay_6093
  · exact WuPaper.ClassicalFourthNat.outerPay_6094
  · exact WuPaper.ClassicalFourthNat.outerPay_6095
  · exact WuPaper.ClassicalFourthNat.outerPay_6096
  · exact WuPaper.ClassicalFourthNat.outerPay_6097
  · exact WuPaper.ClassicalFourthNat.outerPay_6098
  · exact WuPaper.ClassicalFourthNat.outerPay_6099
  · exact WuPaper.ClassicalFourthNat.outerPay_6100
  · exact WuPaper.ClassicalFourthNat.outerPay_6101
  · exact WuPaper.ClassicalFourthNat.outerPay_6102
  · exact WuPaper.ClassicalFourthNat.outerPay_6103
  · exact WuPaper.ClassicalFourthNat.outerPay_6104
  · exact WuPaper.ClassicalFourthNat.outerPay_6105
  · exact WuPaper.ClassicalFourthNat.outerPay_6106
  · exact WuPaper.ClassicalFourthNat.outerPay_6107
  · exact WuPaper.ClassicalFourthNat.outerPay_6108
  · exact WuPaper.ClassicalFourthNat.outerPay_6109
  · exact WuPaper.ClassicalFourthNat.outerPay_6110
  · exact WuPaper.ClassicalFourthNat.outerPay_6111
  · exact WuPaper.ClassicalFourthNat.outerPay_6112
  · exact WuPaper.ClassicalFourthNat.outerPay_6113
  · exact WuPaper.ClassicalFourthNat.outerPay_6114
  · exact WuPaper.ClassicalFourthNat.outerPay_6115
  · exact WuPaper.ClassicalFourthNat.outerPay_6116
  · exact WuPaper.ClassicalFourthNat.outerPay_6117
  · exact WuPaper.ClassicalFourthNat.outerPay_6118
  · exact WuPaper.ClassicalFourthNat.outerPay_6119
  · exact WuPaper.ClassicalFourthNat.outerPay_6120
  · exact WuPaper.ClassicalFourthNat.outerPay_6121
  · exact WuPaper.ClassicalFourthNat.outerPay_6122
  · exact WuPaper.ClassicalFourthNat.outerPay_6123
  · exact WuPaper.ClassicalFourthNat.outerPay_6124
  · exact WuPaper.ClassicalFourthNat.outerPay_6125
  · exact WuPaper.ClassicalFourthNat.outerPay_6126
  · exact WuPaper.ClassicalFourthNat.outerPay_6127
  · exact WuPaper.ClassicalFourthNat.outerPay_6128
  · exact WuPaper.ClassicalFourthNat.outerPay_6129
  · exact WuPaper.ClassicalFourthNat.outerPay_6130
  · exact WuPaper.ClassicalFourthNat.outerPay_6131
  · exact WuPaper.ClassicalFourthNat.outerPay_6132
  · exact WuPaper.ClassicalFourthNat.outerPay_6133
  · exact WuPaper.ClassicalFourthNat.outerPay_6134
  · exact WuPaper.ClassicalFourthNat.outerPay_6135
  · exact WuPaper.ClassicalFourthNat.outerPay_6136
  · exact WuPaper.ClassicalFourthNat.outerPay_6137
  · exact WuPaper.ClassicalFourthNat.outerPay_6138
  · exact WuPaper.ClassicalFourthNat.outerPay_6139
  · exact WuPaper.ClassicalFourthNat.outerPay_6140
  · exact WuPaper.ClassicalFourthNat.outerPay_6141
  · exact WuPaper.ClassicalFourthNat.outerPay_6142
  · exact WuPaper.ClassicalFourthNat.outerPay_6143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_095

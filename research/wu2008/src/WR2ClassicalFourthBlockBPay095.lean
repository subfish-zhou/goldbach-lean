import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay095
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_095 (j : Fin 64) (hj : 64*95+j.val < 10540) :
    BPay (64*95+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6080
  · exact WuPaper.ClassicalFourthNat.BPay_6081
  · exact WuPaper.ClassicalFourthNat.BPay_6082
  · exact WuPaper.ClassicalFourthNat.BPay_6083
  · exact WuPaper.ClassicalFourthNat.BPay_6084
  · exact WuPaper.ClassicalFourthNat.BPay_6085
  · exact WuPaper.ClassicalFourthNat.BPay_6086
  · exact WuPaper.ClassicalFourthNat.BPay_6087
  · exact WuPaper.ClassicalFourthNat.BPay_6088
  · exact WuPaper.ClassicalFourthNat.BPay_6089
  · exact WuPaper.ClassicalFourthNat.BPay_6090
  · exact WuPaper.ClassicalFourthNat.BPay_6091
  · exact WuPaper.ClassicalFourthNat.BPay_6092
  · exact WuPaper.ClassicalFourthNat.BPay_6093
  · exact WuPaper.ClassicalFourthNat.BPay_6094
  · exact WuPaper.ClassicalFourthNat.BPay_6095
  · exact WuPaper.ClassicalFourthNat.BPay_6096
  · exact WuPaper.ClassicalFourthNat.BPay_6097
  · exact WuPaper.ClassicalFourthNat.BPay_6098
  · exact WuPaper.ClassicalFourthNat.BPay_6099
  · exact WuPaper.ClassicalFourthNat.BPay_6100
  · exact WuPaper.ClassicalFourthNat.BPay_6101
  · exact WuPaper.ClassicalFourthNat.BPay_6102
  · exact WuPaper.ClassicalFourthNat.BPay_6103
  · exact WuPaper.ClassicalFourthNat.BPay_6104
  · exact WuPaper.ClassicalFourthNat.BPay_6105
  · exact WuPaper.ClassicalFourthNat.BPay_6106
  · exact WuPaper.ClassicalFourthNat.BPay_6107
  · exact WuPaper.ClassicalFourthNat.BPay_6108
  · exact WuPaper.ClassicalFourthNat.BPay_6109
  · exact WuPaper.ClassicalFourthNat.BPay_6110
  · exact WuPaper.ClassicalFourthNat.BPay_6111
  · exact WuPaper.ClassicalFourthNat.BPay_6112
  · exact WuPaper.ClassicalFourthNat.BPay_6113
  · exact WuPaper.ClassicalFourthNat.BPay_6114
  · exact WuPaper.ClassicalFourthNat.BPay_6115
  · exact WuPaper.ClassicalFourthNat.BPay_6116
  · exact WuPaper.ClassicalFourthNat.BPay_6117
  · exact WuPaper.ClassicalFourthNat.BPay_6118
  · exact WuPaper.ClassicalFourthNat.BPay_6119
  · exact WuPaper.ClassicalFourthNat.BPay_6120
  · exact WuPaper.ClassicalFourthNat.BPay_6121
  · exact WuPaper.ClassicalFourthNat.BPay_6122
  · exact WuPaper.ClassicalFourthNat.BPay_6123
  · exact WuPaper.ClassicalFourthNat.BPay_6124
  · exact WuPaper.ClassicalFourthNat.BPay_6125
  · exact WuPaper.ClassicalFourthNat.BPay_6126
  · exact WuPaper.ClassicalFourthNat.BPay_6127
  · exact WuPaper.ClassicalFourthNat.BPay_6128
  · exact WuPaper.ClassicalFourthNat.BPay_6129
  · exact WuPaper.ClassicalFourthNat.BPay_6130
  · exact WuPaper.ClassicalFourthNat.BPay_6131
  · exact WuPaper.ClassicalFourthNat.BPay_6132
  · exact WuPaper.ClassicalFourthNat.BPay_6133
  · exact WuPaper.ClassicalFourthNat.BPay_6134
  · exact WuPaper.ClassicalFourthNat.BPay_6135
  · exact WuPaper.ClassicalFourthNat.BPay_6136
  · exact WuPaper.ClassicalFourthNat.BPay_6137
  · exact WuPaper.ClassicalFourthNat.BPay_6138
  · exact WuPaper.ClassicalFourthNat.BPay_6139
  · exact WuPaper.ClassicalFourthNat.BPay_6140
  · exact WuPaper.ClassicalFourthNat.BPay_6141
  · exact WuPaper.ClassicalFourthNat.BPay_6142
  · exact WuPaper.ClassicalFourthNat.BPay_6143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_095

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay080
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_080 (j : Fin 64) (hj : 64*80+j.val < 10540) :
    BPay (64*80+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5120
  · exact WuPaper.ClassicalFourthNat.BPay_5121
  · exact WuPaper.ClassicalFourthNat.BPay_5122
  · exact WuPaper.ClassicalFourthNat.BPay_5123
  · exact WuPaper.ClassicalFourthNat.BPay_5124
  · exact WuPaper.ClassicalFourthNat.BPay_5125
  · exact WuPaper.ClassicalFourthNat.BPay_5126
  · exact WuPaper.ClassicalFourthNat.BPay_5127
  · exact WuPaper.ClassicalFourthNat.BPay_5128
  · exact WuPaper.ClassicalFourthNat.BPay_5129
  · exact WuPaper.ClassicalFourthNat.BPay_5130
  · exact WuPaper.ClassicalFourthNat.BPay_5131
  · exact WuPaper.ClassicalFourthNat.BPay_5132
  · exact WuPaper.ClassicalFourthNat.BPay_5133
  · exact WuPaper.ClassicalFourthNat.BPay_5134
  · exact WuPaper.ClassicalFourthNat.BPay_5135
  · exact WuPaper.ClassicalFourthNat.BPay_5136
  · exact WuPaper.ClassicalFourthNat.BPay_5137
  · exact WuPaper.ClassicalFourthNat.BPay_5138
  · exact WuPaper.ClassicalFourthNat.BPay_5139
  · exact WuPaper.ClassicalFourthNat.BPay_5140
  · exact WuPaper.ClassicalFourthNat.BPay_5141
  · exact WuPaper.ClassicalFourthNat.BPay_5142
  · exact WuPaper.ClassicalFourthNat.BPay_5143
  · exact WuPaper.ClassicalFourthNat.BPay_5144
  · exact WuPaper.ClassicalFourthNat.BPay_5145
  · exact WuPaper.ClassicalFourthNat.BPay_5146
  · exact WuPaper.ClassicalFourthNat.BPay_5147
  · exact WuPaper.ClassicalFourthNat.BPay_5148
  · exact WuPaper.ClassicalFourthNat.BPay_5149
  · exact WuPaper.ClassicalFourthNat.BPay_5150
  · exact WuPaper.ClassicalFourthNat.BPay_5151
  · exact WuPaper.ClassicalFourthNat.BPay_5152
  · exact WuPaper.ClassicalFourthNat.BPay_5153
  · exact WuPaper.ClassicalFourthNat.BPay_5154
  · exact WuPaper.ClassicalFourthNat.BPay_5155
  · exact WuPaper.ClassicalFourthNat.BPay_5156
  · exact WuPaper.ClassicalFourthNat.BPay_5157
  · exact WuPaper.ClassicalFourthNat.BPay_5158
  · exact WuPaper.ClassicalFourthNat.BPay_5159
  · exact WuPaper.ClassicalFourthNat.BPay_5160
  · exact WuPaper.ClassicalFourthNat.BPay_5161
  · exact WuPaper.ClassicalFourthNat.BPay_5162
  · exact WuPaper.ClassicalFourthNat.BPay_5163
  · exact WuPaper.ClassicalFourthNat.BPay_5164
  · exact WuPaper.ClassicalFourthNat.BPay_5165
  · exact WuPaper.ClassicalFourthNat.BPay_5166
  · exact WuPaper.ClassicalFourthNat.BPay_5167
  · exact WuPaper.ClassicalFourthNat.BPay_5168
  · exact WuPaper.ClassicalFourthNat.BPay_5169
  · exact WuPaper.ClassicalFourthNat.BPay_5170
  · exact WuPaper.ClassicalFourthNat.BPay_5171
  · exact WuPaper.ClassicalFourthNat.BPay_5172
  · exact WuPaper.ClassicalFourthNat.BPay_5173
  · exact WuPaper.ClassicalFourthNat.BPay_5174
  · exact WuPaper.ClassicalFourthNat.BPay_5175
  · exact WuPaper.ClassicalFourthNat.BPay_5176
  · exact WuPaper.ClassicalFourthNat.BPay_5177
  · exact WuPaper.ClassicalFourthNat.BPay_5178
  · exact WuPaper.ClassicalFourthNat.BPay_5179
  · exact WuPaper.ClassicalFourthNat.BPay_5180
  · exact WuPaper.ClassicalFourthNat.BPay_5181
  · exact WuPaper.ClassicalFourthNat.BPay_5182
  · exact WuPaper.ClassicalFourthNat.BPay_5183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_080

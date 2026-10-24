import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay080
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_080 (j : Fin 64) (hj : 64*80+j.val < 10540) :
    OuterPay (64*80+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_5120
  · exact WuPaper.ClassicalFourthNat.outerPay_5121
  · exact WuPaper.ClassicalFourthNat.outerPay_5122
  · exact WuPaper.ClassicalFourthNat.outerPay_5123
  · exact WuPaper.ClassicalFourthNat.outerPay_5124
  · exact WuPaper.ClassicalFourthNat.outerPay_5125
  · exact WuPaper.ClassicalFourthNat.outerPay_5126
  · exact WuPaper.ClassicalFourthNat.outerPay_5127
  · exact WuPaper.ClassicalFourthNat.outerPay_5128
  · exact WuPaper.ClassicalFourthNat.outerPay_5129
  · exact WuPaper.ClassicalFourthNat.outerPay_5130
  · exact WuPaper.ClassicalFourthNat.outerPay_5131
  · exact WuPaper.ClassicalFourthNat.outerPay_5132
  · exact WuPaper.ClassicalFourthNat.outerPay_5133
  · exact WuPaper.ClassicalFourthNat.outerPay_5134
  · exact WuPaper.ClassicalFourthNat.outerPay_5135
  · exact WuPaper.ClassicalFourthNat.outerPay_5136
  · exact WuPaper.ClassicalFourthNat.outerPay_5137
  · exact WuPaper.ClassicalFourthNat.outerPay_5138
  · exact WuPaper.ClassicalFourthNat.outerPay_5139
  · exact WuPaper.ClassicalFourthNat.outerPay_5140
  · exact WuPaper.ClassicalFourthNat.outerPay_5141
  · exact WuPaper.ClassicalFourthNat.outerPay_5142
  · exact WuPaper.ClassicalFourthNat.outerPay_5143
  · exact WuPaper.ClassicalFourthNat.outerPay_5144
  · exact WuPaper.ClassicalFourthNat.outerPay_5145
  · exact WuPaper.ClassicalFourthNat.outerPay_5146
  · exact WuPaper.ClassicalFourthNat.outerPay_5147
  · exact WuPaper.ClassicalFourthNat.outerPay_5148
  · exact WuPaper.ClassicalFourthNat.outerPay_5149
  · exact WuPaper.ClassicalFourthNat.outerPay_5150
  · exact WuPaper.ClassicalFourthNat.outerPay_5151
  · exact WuPaper.ClassicalFourthNat.outerPay_5152
  · exact WuPaper.ClassicalFourthNat.outerPay_5153
  · exact WuPaper.ClassicalFourthNat.outerPay_5154
  · exact WuPaper.ClassicalFourthNat.outerPay_5155
  · exact WuPaper.ClassicalFourthNat.outerPay_5156
  · exact WuPaper.ClassicalFourthNat.outerPay_5157
  · exact WuPaper.ClassicalFourthNat.outerPay_5158
  · exact WuPaper.ClassicalFourthNat.outerPay_5159
  · exact WuPaper.ClassicalFourthNat.outerPay_5160
  · exact WuPaper.ClassicalFourthNat.outerPay_5161
  · exact WuPaper.ClassicalFourthNat.outerPay_5162
  · exact WuPaper.ClassicalFourthNat.outerPay_5163
  · exact WuPaper.ClassicalFourthNat.outerPay_5164
  · exact WuPaper.ClassicalFourthNat.outerPay_5165
  · exact WuPaper.ClassicalFourthNat.outerPay_5166
  · exact WuPaper.ClassicalFourthNat.outerPay_5167
  · exact WuPaper.ClassicalFourthNat.outerPay_5168
  · exact WuPaper.ClassicalFourthNat.outerPay_5169
  · exact WuPaper.ClassicalFourthNat.outerPay_5170
  · exact WuPaper.ClassicalFourthNat.outerPay_5171
  · exact WuPaper.ClassicalFourthNat.outerPay_5172
  · exact WuPaper.ClassicalFourthNat.outerPay_5173
  · exact WuPaper.ClassicalFourthNat.outerPay_5174
  · exact WuPaper.ClassicalFourthNat.outerPay_5175
  · exact WuPaper.ClassicalFourthNat.outerPay_5176
  · exact WuPaper.ClassicalFourthNat.outerPay_5177
  · exact WuPaper.ClassicalFourthNat.outerPay_5178
  · exact WuPaper.ClassicalFourthNat.outerPay_5179
  · exact WuPaper.ClassicalFourthNat.outerPay_5180
  · exact WuPaper.ClassicalFourthNat.outerPay_5181
  · exact WuPaper.ClassicalFourthNat.outerPay_5182
  · exact WuPaper.ClassicalFourthNat.outerPay_5183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_080

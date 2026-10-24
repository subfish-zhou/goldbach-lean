import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay127
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_127 (j : Fin 64) (hj : 64*127+j.val < 10540) :
    OuterPay (64*127+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8128
  · exact WuPaper.ClassicalFourthNat.outerPay_8129
  · exact WuPaper.ClassicalFourthNat.outerPay_8130
  · exact WuPaper.ClassicalFourthNat.outerPay_8131
  · exact WuPaper.ClassicalFourthNat.outerPay_8132
  · exact WuPaper.ClassicalFourthNat.outerPay_8133
  · exact WuPaper.ClassicalFourthNat.outerPay_8134
  · exact WuPaper.ClassicalFourthNat.outerPay_8135
  · exact WuPaper.ClassicalFourthNat.outerPay_8136
  · exact WuPaper.ClassicalFourthNat.outerPay_8137
  · exact WuPaper.ClassicalFourthNat.outerPay_8138
  · exact WuPaper.ClassicalFourthNat.outerPay_8139
  · exact WuPaper.ClassicalFourthNat.outerPay_8140
  · exact WuPaper.ClassicalFourthNat.outerPay_8141
  · exact WuPaper.ClassicalFourthNat.outerPay_8142
  · exact WuPaper.ClassicalFourthNat.outerPay_8143
  · exact WuPaper.ClassicalFourthNat.outerPay_8144
  · exact WuPaper.ClassicalFourthNat.outerPay_8145
  · exact WuPaper.ClassicalFourthNat.outerPay_8146
  · exact WuPaper.ClassicalFourthNat.outerPay_8147
  · exact WuPaper.ClassicalFourthNat.outerPay_8148
  · exact WuPaper.ClassicalFourthNat.outerPay_8149
  · exact WuPaper.ClassicalFourthNat.outerPay_8150
  · exact WuPaper.ClassicalFourthNat.outerPay_8151
  · exact WuPaper.ClassicalFourthNat.outerPay_8152
  · exact WuPaper.ClassicalFourthNat.outerPay_8153
  · exact WuPaper.ClassicalFourthNat.outerPay_8154
  · exact WuPaper.ClassicalFourthNat.outerPay_8155
  · exact WuPaper.ClassicalFourthNat.outerPay_8156
  · exact WuPaper.ClassicalFourthNat.outerPay_8157
  · exact WuPaper.ClassicalFourthNat.outerPay_8158
  · exact WuPaper.ClassicalFourthNat.outerPay_8159
  · exact WuPaper.ClassicalFourthNat.outerPay_8160
  · exact WuPaper.ClassicalFourthNat.outerPay_8161
  · exact WuPaper.ClassicalFourthNat.outerPay_8162
  · exact WuPaper.ClassicalFourthNat.outerPay_8163
  · exact WuPaper.ClassicalFourthNat.outerPay_8164
  · exact WuPaper.ClassicalFourthNat.outerPay_8165
  · exact WuPaper.ClassicalFourthNat.outerPay_8166
  · exact WuPaper.ClassicalFourthNat.outerPay_8167
  · exact WuPaper.ClassicalFourthNat.outerPay_8168
  · exact WuPaper.ClassicalFourthNat.outerPay_8169
  · exact WuPaper.ClassicalFourthNat.outerPay_8170
  · exact WuPaper.ClassicalFourthNat.outerPay_8171
  · exact WuPaper.ClassicalFourthNat.outerPay_8172
  · exact WuPaper.ClassicalFourthNat.outerPay_8173
  · exact WuPaper.ClassicalFourthNat.outerPay_8174
  · exact WuPaper.ClassicalFourthNat.outerPay_8175
  · exact WuPaper.ClassicalFourthNat.outerPay_8176
  · exact WuPaper.ClassicalFourthNat.outerPay_8177
  · exact WuPaper.ClassicalFourthNat.outerPay_8178
  · exact WuPaper.ClassicalFourthNat.outerPay_8179
  · exact WuPaper.ClassicalFourthNat.outerPay_8180
  · exact WuPaper.ClassicalFourthNat.outerPay_8181
  · exact WuPaper.ClassicalFourthNat.outerPay_8182
  · exact WuPaper.ClassicalFourthNat.outerPay_8183
  · exact WuPaper.ClassicalFourthNat.outerPay_8184
  · exact WuPaper.ClassicalFourthNat.outerPay_8185
  · exact WuPaper.ClassicalFourthNat.outerPay_8186
  · exact WuPaper.ClassicalFourthNat.outerPay_8187
  · exact WuPaper.ClassicalFourthNat.outerPay_8188
  · exact WuPaper.ClassicalFourthNat.outerPay_8189
  · exact WuPaper.ClassicalFourthNat.outerPay_8190
  · exact WuPaper.ClassicalFourthNat.outerPay_8191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_127

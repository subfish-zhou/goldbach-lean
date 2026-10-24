import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay096
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_096 (j : Fin 64) (hj : 64*96+j.val < 10540) :
    OuterPay (64*96+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6144
  · exact WuPaper.ClassicalFourthNat.outerPay_6145
  · exact WuPaper.ClassicalFourthNat.outerPay_6146
  · exact WuPaper.ClassicalFourthNat.outerPay_6147
  · exact WuPaper.ClassicalFourthNat.outerPay_6148
  · exact WuPaper.ClassicalFourthNat.outerPay_6149
  · exact WuPaper.ClassicalFourthNat.outerPay_6150
  · exact WuPaper.ClassicalFourthNat.outerPay_6151
  · exact WuPaper.ClassicalFourthNat.outerPay_6152
  · exact WuPaper.ClassicalFourthNat.outerPay_6153
  · exact WuPaper.ClassicalFourthNat.outerPay_6154
  · exact WuPaper.ClassicalFourthNat.outerPay_6155
  · exact WuPaper.ClassicalFourthNat.outerPay_6156
  · exact WuPaper.ClassicalFourthNat.outerPay_6157
  · exact WuPaper.ClassicalFourthNat.outerPay_6158
  · exact WuPaper.ClassicalFourthNat.outerPay_6159
  · exact WuPaper.ClassicalFourthNat.outerPay_6160
  · exact WuPaper.ClassicalFourthNat.outerPay_6161
  · exact WuPaper.ClassicalFourthNat.outerPay_6162
  · exact WuPaper.ClassicalFourthNat.outerPay_6163
  · exact WuPaper.ClassicalFourthNat.outerPay_6164
  · exact WuPaper.ClassicalFourthNat.outerPay_6165
  · exact WuPaper.ClassicalFourthNat.outerPay_6166
  · exact WuPaper.ClassicalFourthNat.outerPay_6167
  · exact WuPaper.ClassicalFourthNat.outerPay_6168
  · exact WuPaper.ClassicalFourthNat.outerPay_6169
  · exact WuPaper.ClassicalFourthNat.outerPay_6170
  · exact WuPaper.ClassicalFourthNat.outerPay_6171
  · exact WuPaper.ClassicalFourthNat.outerPay_6172
  · exact WuPaper.ClassicalFourthNat.outerPay_6173
  · exact WuPaper.ClassicalFourthNat.outerPay_6174
  · exact WuPaper.ClassicalFourthNat.outerPay_6175
  · exact WuPaper.ClassicalFourthNat.outerPay_6176
  · exact WuPaper.ClassicalFourthNat.outerPay_6177
  · exact WuPaper.ClassicalFourthNat.outerPay_6178
  · exact WuPaper.ClassicalFourthNat.outerPay_6179
  · exact WuPaper.ClassicalFourthNat.outerPay_6180
  · exact WuPaper.ClassicalFourthNat.outerPay_6181
  · exact WuPaper.ClassicalFourthNat.outerPay_6182
  · exact WuPaper.ClassicalFourthNat.outerPay_6183
  · exact WuPaper.ClassicalFourthNat.outerPay_6184
  · exact WuPaper.ClassicalFourthNat.outerPay_6185
  · exact WuPaper.ClassicalFourthNat.outerPay_6186
  · exact WuPaper.ClassicalFourthNat.outerPay_6187
  · exact WuPaper.ClassicalFourthNat.outerPay_6188
  · exact WuPaper.ClassicalFourthNat.outerPay_6189
  · exact WuPaper.ClassicalFourthNat.outerPay_6190
  · exact WuPaper.ClassicalFourthNat.outerPay_6191
  · exact WuPaper.ClassicalFourthNat.outerPay_6192
  · exact WuPaper.ClassicalFourthNat.outerPay_6193
  · exact WuPaper.ClassicalFourthNat.outerPay_6194
  · exact WuPaper.ClassicalFourthNat.outerPay_6195
  · exact WuPaper.ClassicalFourthNat.outerPay_6196
  · exact WuPaper.ClassicalFourthNat.outerPay_6197
  · exact WuPaper.ClassicalFourthNat.outerPay_6198
  · exact WuPaper.ClassicalFourthNat.outerPay_6199
  · exact WuPaper.ClassicalFourthNat.outerPay_6200
  · exact WuPaper.ClassicalFourthNat.outerPay_6201
  · exact WuPaper.ClassicalFourthNat.outerPay_6202
  · exact WuPaper.ClassicalFourthNat.outerPay_6203
  · exact WuPaper.ClassicalFourthNat.outerPay_6204
  · exact WuPaper.ClassicalFourthNat.outerPay_6205
  · exact WuPaper.ClassicalFourthNat.outerPay_6206
  · exact WuPaper.ClassicalFourthNat.outerPay_6207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_096

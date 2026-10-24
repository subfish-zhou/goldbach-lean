import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay096
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_096 (j : Fin 64) (hj : 64*96+j.val < 10540) :
    BPay (64*96+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6144
  · exact WuPaper.ClassicalFourthNat.BPay_6145
  · exact WuPaper.ClassicalFourthNat.BPay_6146
  · exact WuPaper.ClassicalFourthNat.BPay_6147
  · exact WuPaper.ClassicalFourthNat.BPay_6148
  · exact WuPaper.ClassicalFourthNat.BPay_6149
  · exact WuPaper.ClassicalFourthNat.BPay_6150
  · exact WuPaper.ClassicalFourthNat.BPay_6151
  · exact WuPaper.ClassicalFourthNat.BPay_6152
  · exact WuPaper.ClassicalFourthNat.BPay_6153
  · exact WuPaper.ClassicalFourthNat.BPay_6154
  · exact WuPaper.ClassicalFourthNat.BPay_6155
  · exact WuPaper.ClassicalFourthNat.BPay_6156
  · exact WuPaper.ClassicalFourthNat.BPay_6157
  · exact WuPaper.ClassicalFourthNat.BPay_6158
  · exact WuPaper.ClassicalFourthNat.BPay_6159
  · exact WuPaper.ClassicalFourthNat.BPay_6160
  · exact WuPaper.ClassicalFourthNat.BPay_6161
  · exact WuPaper.ClassicalFourthNat.BPay_6162
  · exact WuPaper.ClassicalFourthNat.BPay_6163
  · exact WuPaper.ClassicalFourthNat.BPay_6164
  · exact WuPaper.ClassicalFourthNat.BPay_6165
  · exact WuPaper.ClassicalFourthNat.BPay_6166
  · exact WuPaper.ClassicalFourthNat.BPay_6167
  · exact WuPaper.ClassicalFourthNat.BPay_6168
  · exact WuPaper.ClassicalFourthNat.BPay_6169
  · exact WuPaper.ClassicalFourthNat.BPay_6170
  · exact WuPaper.ClassicalFourthNat.BPay_6171
  · exact WuPaper.ClassicalFourthNat.BPay_6172
  · exact WuPaper.ClassicalFourthNat.BPay_6173
  · exact WuPaper.ClassicalFourthNat.BPay_6174
  · exact WuPaper.ClassicalFourthNat.BPay_6175
  · exact WuPaper.ClassicalFourthNat.BPay_6176
  · exact WuPaper.ClassicalFourthNat.BPay_6177
  · exact WuPaper.ClassicalFourthNat.BPay_6178
  · exact WuPaper.ClassicalFourthNat.BPay_6179
  · exact WuPaper.ClassicalFourthNat.BPay_6180
  · exact WuPaper.ClassicalFourthNat.BPay_6181
  · exact WuPaper.ClassicalFourthNat.BPay_6182
  · exact WuPaper.ClassicalFourthNat.BPay_6183
  · exact WuPaper.ClassicalFourthNat.BPay_6184
  · exact WuPaper.ClassicalFourthNat.BPay_6185
  · exact WuPaper.ClassicalFourthNat.BPay_6186
  · exact WuPaper.ClassicalFourthNat.BPay_6187
  · exact WuPaper.ClassicalFourthNat.BPay_6188
  · exact WuPaper.ClassicalFourthNat.BPay_6189
  · exact WuPaper.ClassicalFourthNat.BPay_6190
  · exact WuPaper.ClassicalFourthNat.BPay_6191
  · exact WuPaper.ClassicalFourthNat.BPay_6192
  · exact WuPaper.ClassicalFourthNat.BPay_6193
  · exact WuPaper.ClassicalFourthNat.BPay_6194
  · exact WuPaper.ClassicalFourthNat.BPay_6195
  · exact WuPaper.ClassicalFourthNat.BPay_6196
  · exact WuPaper.ClassicalFourthNat.BPay_6197
  · exact WuPaper.ClassicalFourthNat.BPay_6198
  · exact WuPaper.ClassicalFourthNat.BPay_6199
  · exact WuPaper.ClassicalFourthNat.BPay_6200
  · exact WuPaper.ClassicalFourthNat.BPay_6201
  · exact WuPaper.ClassicalFourthNat.BPay_6202
  · exact WuPaper.ClassicalFourthNat.BPay_6203
  · exact WuPaper.ClassicalFourthNat.BPay_6204
  · exact WuPaper.ClassicalFourthNat.BPay_6205
  · exact WuPaper.ClassicalFourthNat.BPay_6206
  · exact WuPaper.ClassicalFourthNat.BPay_6207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_096

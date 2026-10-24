import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay112
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_112 (j : Fin 64) (hj : 64*112+j.val < 10540) :
    BPay (64*112+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7168
  · exact WuPaper.ClassicalFourthNat.BPay_7169
  · exact WuPaper.ClassicalFourthNat.BPay_7170
  · exact WuPaper.ClassicalFourthNat.BPay_7171
  · exact WuPaper.ClassicalFourthNat.BPay_7172
  · exact WuPaper.ClassicalFourthNat.BPay_7173
  · exact WuPaper.ClassicalFourthNat.BPay_7174
  · exact WuPaper.ClassicalFourthNat.BPay_7175
  · exact WuPaper.ClassicalFourthNat.BPay_7176
  · exact WuPaper.ClassicalFourthNat.BPay_7177
  · exact WuPaper.ClassicalFourthNat.BPay_7178
  · exact WuPaper.ClassicalFourthNat.BPay_7179
  · exact WuPaper.ClassicalFourthNat.BPay_7180
  · exact WuPaper.ClassicalFourthNat.BPay_7181
  · exact WuPaper.ClassicalFourthNat.BPay_7182
  · exact WuPaper.ClassicalFourthNat.BPay_7183
  · exact WuPaper.ClassicalFourthNat.BPay_7184
  · exact WuPaper.ClassicalFourthNat.BPay_7185
  · exact WuPaper.ClassicalFourthNat.BPay_7186
  · exact WuPaper.ClassicalFourthNat.BPay_7187
  · exact WuPaper.ClassicalFourthNat.BPay_7188
  · exact WuPaper.ClassicalFourthNat.BPay_7189
  · exact WuPaper.ClassicalFourthNat.BPay_7190
  · exact WuPaper.ClassicalFourthNat.BPay_7191
  · exact WuPaper.ClassicalFourthNat.BPay_7192
  · exact WuPaper.ClassicalFourthNat.BPay_7193
  · exact WuPaper.ClassicalFourthNat.BPay_7194
  · exact WuPaper.ClassicalFourthNat.BPay_7195
  · exact WuPaper.ClassicalFourthNat.BPay_7196
  · exact WuPaper.ClassicalFourthNat.BPay_7197
  · exact WuPaper.ClassicalFourthNat.BPay_7198
  · exact WuPaper.ClassicalFourthNat.BPay_7199
  · exact WuPaper.ClassicalFourthNat.BPay_7200
  · exact WuPaper.ClassicalFourthNat.BPay_7201
  · exact WuPaper.ClassicalFourthNat.BPay_7202
  · exact WuPaper.ClassicalFourthNat.BPay_7203
  · exact WuPaper.ClassicalFourthNat.BPay_7204
  · exact WuPaper.ClassicalFourthNat.BPay_7205
  · exact WuPaper.ClassicalFourthNat.BPay_7206
  · exact WuPaper.ClassicalFourthNat.BPay_7207
  · exact WuPaper.ClassicalFourthNat.BPay_7208
  · exact WuPaper.ClassicalFourthNat.BPay_7209
  · exact WuPaper.ClassicalFourthNat.BPay_7210
  · exact WuPaper.ClassicalFourthNat.BPay_7211
  · exact WuPaper.ClassicalFourthNat.BPay_7212
  · exact WuPaper.ClassicalFourthNat.BPay_7213
  · exact WuPaper.ClassicalFourthNat.BPay_7214
  · exact WuPaper.ClassicalFourthNat.BPay_7215
  · exact WuPaper.ClassicalFourthNat.BPay_7216
  · exact WuPaper.ClassicalFourthNat.BPay_7217
  · exact WuPaper.ClassicalFourthNat.BPay_7218
  · exact WuPaper.ClassicalFourthNat.BPay_7219
  · exact WuPaper.ClassicalFourthNat.BPay_7220
  · exact WuPaper.ClassicalFourthNat.BPay_7221
  · exact WuPaper.ClassicalFourthNat.BPay_7222
  · exact WuPaper.ClassicalFourthNat.BPay_7223
  · exact WuPaper.ClassicalFourthNat.BPay_7224
  · exact WuPaper.ClassicalFourthNat.BPay_7225
  · exact WuPaper.ClassicalFourthNat.BPay_7226
  · exact WuPaper.ClassicalFourthNat.BPay_7227
  · exact WuPaper.ClassicalFourthNat.BPay_7228
  · exact WuPaper.ClassicalFourthNat.BPay_7229
  · exact WuPaper.ClassicalFourthNat.BPay_7230
  · exact WuPaper.ClassicalFourthNat.BPay_7231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_112

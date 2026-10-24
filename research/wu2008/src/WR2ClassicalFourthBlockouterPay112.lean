import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay112
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_112 (j : Fin 64) (hj : 64*112+j.val < 10540) :
    OuterPay (64*112+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_7168
  · exact WuPaper.ClassicalFourthNat.outerPay_7169
  · exact WuPaper.ClassicalFourthNat.outerPay_7170
  · exact WuPaper.ClassicalFourthNat.outerPay_7171
  · exact WuPaper.ClassicalFourthNat.outerPay_7172
  · exact WuPaper.ClassicalFourthNat.outerPay_7173
  · exact WuPaper.ClassicalFourthNat.outerPay_7174
  · exact WuPaper.ClassicalFourthNat.outerPay_7175
  · exact WuPaper.ClassicalFourthNat.outerPay_7176
  · exact WuPaper.ClassicalFourthNat.outerPay_7177
  · exact WuPaper.ClassicalFourthNat.outerPay_7178
  · exact WuPaper.ClassicalFourthNat.outerPay_7179
  · exact WuPaper.ClassicalFourthNat.outerPay_7180
  · exact WuPaper.ClassicalFourthNat.outerPay_7181
  · exact WuPaper.ClassicalFourthNat.outerPay_7182
  · exact WuPaper.ClassicalFourthNat.outerPay_7183
  · exact WuPaper.ClassicalFourthNat.outerPay_7184
  · exact WuPaper.ClassicalFourthNat.outerPay_7185
  · exact WuPaper.ClassicalFourthNat.outerPay_7186
  · exact WuPaper.ClassicalFourthNat.outerPay_7187
  · exact WuPaper.ClassicalFourthNat.outerPay_7188
  · exact WuPaper.ClassicalFourthNat.outerPay_7189
  · exact WuPaper.ClassicalFourthNat.outerPay_7190
  · exact WuPaper.ClassicalFourthNat.outerPay_7191
  · exact WuPaper.ClassicalFourthNat.outerPay_7192
  · exact WuPaper.ClassicalFourthNat.outerPay_7193
  · exact WuPaper.ClassicalFourthNat.outerPay_7194
  · exact WuPaper.ClassicalFourthNat.outerPay_7195
  · exact WuPaper.ClassicalFourthNat.outerPay_7196
  · exact WuPaper.ClassicalFourthNat.outerPay_7197
  · exact WuPaper.ClassicalFourthNat.outerPay_7198
  · exact WuPaper.ClassicalFourthNat.outerPay_7199
  · exact WuPaper.ClassicalFourthNat.outerPay_7200
  · exact WuPaper.ClassicalFourthNat.outerPay_7201
  · exact WuPaper.ClassicalFourthNat.outerPay_7202
  · exact WuPaper.ClassicalFourthNat.outerPay_7203
  · exact WuPaper.ClassicalFourthNat.outerPay_7204
  · exact WuPaper.ClassicalFourthNat.outerPay_7205
  · exact WuPaper.ClassicalFourthNat.outerPay_7206
  · exact WuPaper.ClassicalFourthNat.outerPay_7207
  · exact WuPaper.ClassicalFourthNat.outerPay_7208
  · exact WuPaper.ClassicalFourthNat.outerPay_7209
  · exact WuPaper.ClassicalFourthNat.outerPay_7210
  · exact WuPaper.ClassicalFourthNat.outerPay_7211
  · exact WuPaper.ClassicalFourthNat.outerPay_7212
  · exact WuPaper.ClassicalFourthNat.outerPay_7213
  · exact WuPaper.ClassicalFourthNat.outerPay_7214
  · exact WuPaper.ClassicalFourthNat.outerPay_7215
  · exact WuPaper.ClassicalFourthNat.outerPay_7216
  · exact WuPaper.ClassicalFourthNat.outerPay_7217
  · exact WuPaper.ClassicalFourthNat.outerPay_7218
  · exact WuPaper.ClassicalFourthNat.outerPay_7219
  · exact WuPaper.ClassicalFourthNat.outerPay_7220
  · exact WuPaper.ClassicalFourthNat.outerPay_7221
  · exact WuPaper.ClassicalFourthNat.outerPay_7222
  · exact WuPaper.ClassicalFourthNat.outerPay_7223
  · exact WuPaper.ClassicalFourthNat.outerPay_7224
  · exact WuPaper.ClassicalFourthNat.outerPay_7225
  · exact WuPaper.ClassicalFourthNat.outerPay_7226
  · exact WuPaper.ClassicalFourthNat.outerPay_7227
  · exact WuPaper.ClassicalFourthNat.outerPay_7228
  · exact WuPaper.ClassicalFourthNat.outerPay_7229
  · exact WuPaper.ClassicalFourthNat.outerPay_7230
  · exact WuPaper.ClassicalFourthNat.outerPay_7231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_112

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay128
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_128 (j : Fin 64) (hj : 64*128+j.val < 10540) :
    OuterPay (64*128+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8192
  · exact WuPaper.ClassicalFourthNat.outerPay_8193
  · exact WuPaper.ClassicalFourthNat.outerPay_8194
  · exact WuPaper.ClassicalFourthNat.outerPay_8195
  · exact WuPaper.ClassicalFourthNat.outerPay_8196
  · exact WuPaper.ClassicalFourthNat.outerPay_8197
  · exact WuPaper.ClassicalFourthNat.outerPay_8198
  · exact WuPaper.ClassicalFourthNat.outerPay_8199
  · exact WuPaper.ClassicalFourthNat.outerPay_8200
  · exact WuPaper.ClassicalFourthNat.outerPay_8201
  · exact WuPaper.ClassicalFourthNat.outerPay_8202
  · exact WuPaper.ClassicalFourthNat.outerPay_8203
  · exact WuPaper.ClassicalFourthNat.outerPay_8204
  · exact WuPaper.ClassicalFourthNat.outerPay_8205
  · exact WuPaper.ClassicalFourthNat.outerPay_8206
  · exact WuPaper.ClassicalFourthNat.outerPay_8207
  · exact WuPaper.ClassicalFourthNat.outerPay_8208
  · exact WuPaper.ClassicalFourthNat.outerPay_8209
  · exact WuPaper.ClassicalFourthNat.outerPay_8210
  · exact WuPaper.ClassicalFourthNat.outerPay_8211
  · exact WuPaper.ClassicalFourthNat.outerPay_8212
  · exact WuPaper.ClassicalFourthNat.outerPay_8213
  · exact WuPaper.ClassicalFourthNat.outerPay_8214
  · exact WuPaper.ClassicalFourthNat.outerPay_8215
  · exact WuPaper.ClassicalFourthNat.outerPay_8216
  · exact WuPaper.ClassicalFourthNat.outerPay_8217
  · exact WuPaper.ClassicalFourthNat.outerPay_8218
  · exact WuPaper.ClassicalFourthNat.outerPay_8219
  · exact WuPaper.ClassicalFourthNat.outerPay_8220
  · exact WuPaper.ClassicalFourthNat.outerPay_8221
  · exact WuPaper.ClassicalFourthNat.outerPay_8222
  · exact WuPaper.ClassicalFourthNat.outerPay_8223
  · exact WuPaper.ClassicalFourthNat.outerPay_8224
  · exact WuPaper.ClassicalFourthNat.outerPay_8225
  · exact WuPaper.ClassicalFourthNat.outerPay_8226
  · exact WuPaper.ClassicalFourthNat.outerPay_8227
  · exact WuPaper.ClassicalFourthNat.outerPay_8228
  · exact WuPaper.ClassicalFourthNat.outerPay_8229
  · exact WuPaper.ClassicalFourthNat.outerPay_8230
  · exact WuPaper.ClassicalFourthNat.outerPay_8231
  · exact WuPaper.ClassicalFourthNat.outerPay_8232
  · exact WuPaper.ClassicalFourthNat.outerPay_8233
  · exact WuPaper.ClassicalFourthNat.outerPay_8234
  · exact WuPaper.ClassicalFourthNat.outerPay_8235
  · exact WuPaper.ClassicalFourthNat.outerPay_8236
  · exact WuPaper.ClassicalFourthNat.outerPay_8237
  · exact WuPaper.ClassicalFourthNat.outerPay_8238
  · exact WuPaper.ClassicalFourthNat.outerPay_8239
  · exact WuPaper.ClassicalFourthNat.outerPay_8240
  · exact WuPaper.ClassicalFourthNat.outerPay_8241
  · exact WuPaper.ClassicalFourthNat.outerPay_8242
  · exact WuPaper.ClassicalFourthNat.outerPay_8243
  · exact WuPaper.ClassicalFourthNat.outerPay_8244
  · exact WuPaper.ClassicalFourthNat.outerPay_8245
  · exact WuPaper.ClassicalFourthNat.outerPay_8246
  · exact WuPaper.ClassicalFourthNat.outerPay_8247
  · exact WuPaper.ClassicalFourthNat.outerPay_8248
  · exact WuPaper.ClassicalFourthNat.outerPay_8249
  · exact WuPaper.ClassicalFourthNat.outerPay_8250
  · exact WuPaper.ClassicalFourthNat.outerPay_8251
  · exact WuPaper.ClassicalFourthNat.outerPay_8252
  · exact WuPaper.ClassicalFourthNat.outerPay_8253
  · exact WuPaper.ClassicalFourthNat.outerPay_8254
  · exact WuPaper.ClassicalFourthNat.outerPay_8255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_128

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay128
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_128 (j : Fin 64) (hj : 64*128+j.val < 10540) :
    BPay (64*128+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8192
  · exact WuPaper.ClassicalFourthNat.BPay_8193
  · exact WuPaper.ClassicalFourthNat.BPay_8194
  · exact WuPaper.ClassicalFourthNat.BPay_8195
  · exact WuPaper.ClassicalFourthNat.BPay_8196
  · exact WuPaper.ClassicalFourthNat.BPay_8197
  · exact WuPaper.ClassicalFourthNat.BPay_8198
  · exact WuPaper.ClassicalFourthNat.BPay_8199
  · exact WuPaper.ClassicalFourthNat.BPay_8200
  · exact WuPaper.ClassicalFourthNat.BPay_8201
  · exact WuPaper.ClassicalFourthNat.BPay_8202
  · exact WuPaper.ClassicalFourthNat.BPay_8203
  · exact WuPaper.ClassicalFourthNat.BPay_8204
  · exact WuPaper.ClassicalFourthNat.BPay_8205
  · exact WuPaper.ClassicalFourthNat.BPay_8206
  · exact WuPaper.ClassicalFourthNat.BPay_8207
  · exact WuPaper.ClassicalFourthNat.BPay_8208
  · exact WuPaper.ClassicalFourthNat.BPay_8209
  · exact WuPaper.ClassicalFourthNat.BPay_8210
  · exact WuPaper.ClassicalFourthNat.BPay_8211
  · exact WuPaper.ClassicalFourthNat.BPay_8212
  · exact WuPaper.ClassicalFourthNat.BPay_8213
  · exact WuPaper.ClassicalFourthNat.BPay_8214
  · exact WuPaper.ClassicalFourthNat.BPay_8215
  · exact WuPaper.ClassicalFourthNat.BPay_8216
  · exact WuPaper.ClassicalFourthNat.BPay_8217
  · exact WuPaper.ClassicalFourthNat.BPay_8218
  · exact WuPaper.ClassicalFourthNat.BPay_8219
  · exact WuPaper.ClassicalFourthNat.BPay_8220
  · exact WuPaper.ClassicalFourthNat.BPay_8221
  · exact WuPaper.ClassicalFourthNat.BPay_8222
  · exact WuPaper.ClassicalFourthNat.BPay_8223
  · exact WuPaper.ClassicalFourthNat.BPay_8224
  · exact WuPaper.ClassicalFourthNat.BPay_8225
  · exact WuPaper.ClassicalFourthNat.BPay_8226
  · exact WuPaper.ClassicalFourthNat.BPay_8227
  · exact WuPaper.ClassicalFourthNat.BPay_8228
  · exact WuPaper.ClassicalFourthNat.BPay_8229
  · exact WuPaper.ClassicalFourthNat.BPay_8230
  · exact WuPaper.ClassicalFourthNat.BPay_8231
  · exact WuPaper.ClassicalFourthNat.BPay_8232
  · exact WuPaper.ClassicalFourthNat.BPay_8233
  · exact WuPaper.ClassicalFourthNat.BPay_8234
  · exact WuPaper.ClassicalFourthNat.BPay_8235
  · exact WuPaper.ClassicalFourthNat.BPay_8236
  · exact WuPaper.ClassicalFourthNat.BPay_8237
  · exact WuPaper.ClassicalFourthNat.BPay_8238
  · exact WuPaper.ClassicalFourthNat.BPay_8239
  · exact WuPaper.ClassicalFourthNat.BPay_8240
  · exact WuPaper.ClassicalFourthNat.BPay_8241
  · exact WuPaper.ClassicalFourthNat.BPay_8242
  · exact WuPaper.ClassicalFourthNat.BPay_8243
  · exact WuPaper.ClassicalFourthNat.BPay_8244
  · exact WuPaper.ClassicalFourthNat.BPay_8245
  · exact WuPaper.ClassicalFourthNat.BPay_8246
  · exact WuPaper.ClassicalFourthNat.BPay_8247
  · exact WuPaper.ClassicalFourthNat.BPay_8248
  · exact WuPaper.ClassicalFourthNat.BPay_8249
  · exact WuPaper.ClassicalFourthNat.BPay_8250
  · exact WuPaper.ClassicalFourthNat.BPay_8251
  · exact WuPaper.ClassicalFourthNat.BPay_8252
  · exact WuPaper.ClassicalFourthNat.BPay_8253
  · exact WuPaper.ClassicalFourthNat.BPay_8254
  · exact WuPaper.ClassicalFourthNat.BPay_8255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_128

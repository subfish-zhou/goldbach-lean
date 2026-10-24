import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay113
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_113 (j : Fin 64) (hj : 64*113+j.val < 10540) :
    BPay (64*113+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7232
  · exact WuPaper.ClassicalFourthNat.BPay_7233
  · exact WuPaper.ClassicalFourthNat.BPay_7234
  · exact WuPaper.ClassicalFourthNat.BPay_7235
  · exact WuPaper.ClassicalFourthNat.BPay_7236
  · exact WuPaper.ClassicalFourthNat.BPay_7237
  · exact WuPaper.ClassicalFourthNat.BPay_7238
  · exact WuPaper.ClassicalFourthNat.BPay_7239
  · exact WuPaper.ClassicalFourthNat.BPay_7240
  · exact WuPaper.ClassicalFourthNat.BPay_7241
  · exact WuPaper.ClassicalFourthNat.BPay_7242
  · exact WuPaper.ClassicalFourthNat.BPay_7243
  · exact WuPaper.ClassicalFourthNat.BPay_7244
  · exact WuPaper.ClassicalFourthNat.BPay_7245
  · exact WuPaper.ClassicalFourthNat.BPay_7246
  · exact WuPaper.ClassicalFourthNat.BPay_7247
  · exact WuPaper.ClassicalFourthNat.BPay_7248
  · exact WuPaper.ClassicalFourthNat.BPay_7249
  · exact WuPaper.ClassicalFourthNat.BPay_7250
  · exact WuPaper.ClassicalFourthNat.BPay_7251
  · exact WuPaper.ClassicalFourthNat.BPay_7252
  · exact WuPaper.ClassicalFourthNat.BPay_7253
  · exact WuPaper.ClassicalFourthNat.BPay_7254
  · exact WuPaper.ClassicalFourthNat.BPay_7255
  · exact WuPaper.ClassicalFourthNat.BPay_7256
  · exact WuPaper.ClassicalFourthNat.BPay_7257
  · exact WuPaper.ClassicalFourthNat.BPay_7258
  · exact WuPaper.ClassicalFourthNat.BPay_7259
  · exact WuPaper.ClassicalFourthNat.BPay_7260
  · exact WuPaper.ClassicalFourthNat.BPay_7261
  · exact WuPaper.ClassicalFourthNat.BPay_7262
  · exact WuPaper.ClassicalFourthNat.BPay_7263
  · exact WuPaper.ClassicalFourthNat.BPay_7264
  · exact WuPaper.ClassicalFourthNat.BPay_7265
  · exact WuPaper.ClassicalFourthNat.BPay_7266
  · exact WuPaper.ClassicalFourthNat.BPay_7267
  · exact WuPaper.ClassicalFourthNat.BPay_7268
  · exact WuPaper.ClassicalFourthNat.BPay_7269
  · exact WuPaper.ClassicalFourthNat.BPay_7270
  · exact WuPaper.ClassicalFourthNat.BPay_7271
  · exact WuPaper.ClassicalFourthNat.BPay_7272
  · exact WuPaper.ClassicalFourthNat.BPay_7273
  · exact WuPaper.ClassicalFourthNat.BPay_7274
  · exact WuPaper.ClassicalFourthNat.BPay_7275
  · exact WuPaper.ClassicalFourthNat.BPay_7276
  · exact WuPaper.ClassicalFourthNat.BPay_7277
  · exact WuPaper.ClassicalFourthNat.BPay_7278
  · exact WuPaper.ClassicalFourthNat.BPay_7279
  · exact WuPaper.ClassicalFourthNat.BPay_7280
  · exact WuPaper.ClassicalFourthNat.BPay_7281
  · exact WuPaper.ClassicalFourthNat.BPay_7282
  · exact WuPaper.ClassicalFourthNat.BPay_7283
  · exact WuPaper.ClassicalFourthNat.BPay_7284
  · exact WuPaper.ClassicalFourthNat.BPay_7285
  · exact WuPaper.ClassicalFourthNat.BPay_7286
  · exact WuPaper.ClassicalFourthNat.BPay_7287
  · exact WuPaper.ClassicalFourthNat.BPay_7288
  · exact WuPaper.ClassicalFourthNat.BPay_7289
  · exact WuPaper.ClassicalFourthNat.BPay_7290
  · exact WuPaper.ClassicalFourthNat.BPay_7291
  · exact WuPaper.ClassicalFourthNat.BPay_7292
  · exact WuPaper.ClassicalFourthNat.BPay_7293
  · exact WuPaper.ClassicalFourthNat.BPay_7294
  · exact WuPaper.ClassicalFourthNat.BPay_7295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_113

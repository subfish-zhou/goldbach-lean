import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay082
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_082 (j : Fin 64) (hj : 64*82+j.val < 10540) :
    BPay (64*82+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5248
  · exact WuPaper.ClassicalFourthNat.BPay_5249
  · exact WuPaper.ClassicalFourthNat.BPay_5250
  · exact WuPaper.ClassicalFourthNat.BPay_5251
  · exact WuPaper.ClassicalFourthNat.BPay_5252
  · exact WuPaper.ClassicalFourthNat.BPay_5253
  · exact WuPaper.ClassicalFourthNat.BPay_5254
  · exact WuPaper.ClassicalFourthNat.BPay_5255
  · exact WuPaper.ClassicalFourthNat.BPay_5256
  · exact WuPaper.ClassicalFourthNat.BPay_5257
  · exact WuPaper.ClassicalFourthNat.BPay_5258
  · exact WuPaper.ClassicalFourthNat.BPay_5259
  · exact WuPaper.ClassicalFourthNat.BPay_5260
  · exact WuPaper.ClassicalFourthNat.BPay_5261
  · exact WuPaper.ClassicalFourthNat.BPay_5262
  · exact WuPaper.ClassicalFourthNat.BPay_5263
  · exact WuPaper.ClassicalFourthNat.BPay_5264
  · exact WuPaper.ClassicalFourthNat.BPay_5265
  · exact WuPaper.ClassicalFourthNat.BPay_5266
  · exact WuPaper.ClassicalFourthNat.BPay_5267
  · exact WuPaper.ClassicalFourthNat.BPay_5268
  · exact WuPaper.ClassicalFourthNat.BPay_5269
  · exact WuPaper.ClassicalFourthNat.BPay_5270
  · exact WuPaper.ClassicalFourthNat.BPay_5271
  · exact WuPaper.ClassicalFourthNat.BPay_5272
  · exact WuPaper.ClassicalFourthNat.BPay_5273
  · exact WuPaper.ClassicalFourthNat.BPay_5274
  · exact WuPaper.ClassicalFourthNat.BPay_5275
  · exact WuPaper.ClassicalFourthNat.BPay_5276
  · exact WuPaper.ClassicalFourthNat.BPay_5277
  · exact WuPaper.ClassicalFourthNat.BPay_5278
  · exact WuPaper.ClassicalFourthNat.BPay_5279
  · exact WuPaper.ClassicalFourthNat.BPay_5280
  · exact WuPaper.ClassicalFourthNat.BPay_5281
  · exact WuPaper.ClassicalFourthNat.BPay_5282
  · exact WuPaper.ClassicalFourthNat.BPay_5283
  · exact WuPaper.ClassicalFourthNat.BPay_5284
  · exact WuPaper.ClassicalFourthNat.BPay_5285
  · exact WuPaper.ClassicalFourthNat.BPay_5286
  · exact WuPaper.ClassicalFourthNat.BPay_5287
  · exact WuPaper.ClassicalFourthNat.BPay_5288
  · exact WuPaper.ClassicalFourthNat.BPay_5289
  · exact WuPaper.ClassicalFourthNat.BPay_5290
  · exact WuPaper.ClassicalFourthNat.BPay_5291
  · exact WuPaper.ClassicalFourthNat.BPay_5292
  · exact WuPaper.ClassicalFourthNat.BPay_5293
  · exact WuPaper.ClassicalFourthNat.BPay_5294
  · exact WuPaper.ClassicalFourthNat.BPay_5295
  · exact WuPaper.ClassicalFourthNat.BPay_5296
  · exact WuPaper.ClassicalFourthNat.BPay_5297
  · exact WuPaper.ClassicalFourthNat.BPay_5298
  · exact WuPaper.ClassicalFourthNat.BPay_5299
  · exact WuPaper.ClassicalFourthNat.BPay_5300
  · exact WuPaper.ClassicalFourthNat.BPay_5301
  · exact WuPaper.ClassicalFourthNat.BPay_5302
  · exact WuPaper.ClassicalFourthNat.BPay_5303
  · exact WuPaper.ClassicalFourthNat.BPay_5304
  · exact WuPaper.ClassicalFourthNat.BPay_5305
  · exact WuPaper.ClassicalFourthNat.BPay_5306
  · exact WuPaper.ClassicalFourthNat.BPay_5307
  · exact WuPaper.ClassicalFourthNat.BPay_5308
  · exact WuPaper.ClassicalFourthNat.BPay_5309
  · exact WuPaper.ClassicalFourthNat.BPay_5310
  · exact WuPaper.ClassicalFourthNat.BPay_5311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_082

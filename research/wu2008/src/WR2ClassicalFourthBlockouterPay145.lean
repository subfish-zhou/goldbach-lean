import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay145
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_145 (j : Fin 64) (hj : 64*145+j.val < 10540) :
    OuterPay (64*145+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_9280
  · exact WuPaper.ClassicalFourthNat.outerPay_9281
  · exact WuPaper.ClassicalFourthNat.outerPay_9282
  · exact WuPaper.ClassicalFourthNat.outerPay_9283
  · exact WuPaper.ClassicalFourthNat.outerPay_9284
  · exact WuPaper.ClassicalFourthNat.outerPay_9285
  · exact WuPaper.ClassicalFourthNat.outerPay_9286
  · exact WuPaper.ClassicalFourthNat.outerPay_9287
  · exact WuPaper.ClassicalFourthNat.outerPay_9288
  · exact WuPaper.ClassicalFourthNat.outerPay_9289
  · exact WuPaper.ClassicalFourthNat.outerPay_9290
  · exact WuPaper.ClassicalFourthNat.outerPay_9291
  · exact WuPaper.ClassicalFourthNat.outerPay_9292
  · exact WuPaper.ClassicalFourthNat.outerPay_9293
  · exact WuPaper.ClassicalFourthNat.outerPay_9294
  · exact WuPaper.ClassicalFourthNat.outerPay_9295
  · exact WuPaper.ClassicalFourthNat.outerPay_9296
  · exact WuPaper.ClassicalFourthNat.outerPay_9297
  · exact WuPaper.ClassicalFourthNat.outerPay_9298
  · exact WuPaper.ClassicalFourthNat.outerPay_9299
  · exact WuPaper.ClassicalFourthNat.outerPay_9300
  · exact WuPaper.ClassicalFourthNat.outerPay_9301
  · exact WuPaper.ClassicalFourthNat.outerPay_9302
  · exact WuPaper.ClassicalFourthNat.outerPay_9303
  · exact WuPaper.ClassicalFourthNat.outerPay_9304
  · exact WuPaper.ClassicalFourthNat.outerPay_9305
  · exact WuPaper.ClassicalFourthNat.outerPay_9306
  · exact WuPaper.ClassicalFourthNat.outerPay_9307
  · exact WuPaper.ClassicalFourthNat.outerPay_9308
  · exact WuPaper.ClassicalFourthNat.outerPay_9309
  · exact WuPaper.ClassicalFourthNat.outerPay_9310
  · exact WuPaper.ClassicalFourthNat.outerPay_9311
  · exact WuPaper.ClassicalFourthNat.outerPay_9312
  · exact WuPaper.ClassicalFourthNat.outerPay_9313
  · exact WuPaper.ClassicalFourthNat.outerPay_9314
  · exact WuPaper.ClassicalFourthNat.outerPay_9315
  · exact WuPaper.ClassicalFourthNat.outerPay_9316
  · exact WuPaper.ClassicalFourthNat.outerPay_9317
  · exact WuPaper.ClassicalFourthNat.outerPay_9318
  · exact WuPaper.ClassicalFourthNat.outerPay_9319
  · exact WuPaper.ClassicalFourthNat.outerPay_9320
  · exact WuPaper.ClassicalFourthNat.outerPay_9321
  · exact WuPaper.ClassicalFourthNat.outerPay_9322
  · exact WuPaper.ClassicalFourthNat.outerPay_9323
  · exact WuPaper.ClassicalFourthNat.outerPay_9324
  · exact WuPaper.ClassicalFourthNat.outerPay_9325
  · exact WuPaper.ClassicalFourthNat.outerPay_9326
  · exact WuPaper.ClassicalFourthNat.outerPay_9327
  · exact WuPaper.ClassicalFourthNat.outerPay_9328
  · exact WuPaper.ClassicalFourthNat.outerPay_9329
  · exact WuPaper.ClassicalFourthNat.outerPay_9330
  · exact WuPaper.ClassicalFourthNat.outerPay_9331
  · exact WuPaper.ClassicalFourthNat.outerPay_9332
  · exact WuPaper.ClassicalFourthNat.outerPay_9333
  · exact WuPaper.ClassicalFourthNat.outerPay_9334
  · exact WuPaper.ClassicalFourthNat.outerPay_9335
  · exact WuPaper.ClassicalFourthNat.outerPay_9336
  · exact WuPaper.ClassicalFourthNat.outerPay_9337
  · exact WuPaper.ClassicalFourthNat.outerPay_9338
  · exact WuPaper.ClassicalFourthNat.outerPay_9339
  · exact WuPaper.ClassicalFourthNat.outerPay_9340
  · exact WuPaper.ClassicalFourthNat.outerPay_9341
  · exact WuPaper.ClassicalFourthNat.outerPay_9342
  · exact WuPaper.ClassicalFourthNat.outerPay_9343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_145

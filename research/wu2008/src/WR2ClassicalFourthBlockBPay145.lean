import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay145
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_145 (j : Fin 64) (hj : 64*145+j.val < 10540) :
    BPay (64*145+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9280
  · exact WuPaper.ClassicalFourthNat.BPay_9281
  · exact WuPaper.ClassicalFourthNat.BPay_9282
  · exact WuPaper.ClassicalFourthNat.BPay_9283
  · exact WuPaper.ClassicalFourthNat.BPay_9284
  · exact WuPaper.ClassicalFourthNat.BPay_9285
  · exact WuPaper.ClassicalFourthNat.BPay_9286
  · exact WuPaper.ClassicalFourthNat.BPay_9287
  · exact WuPaper.ClassicalFourthNat.BPay_9288
  · exact WuPaper.ClassicalFourthNat.BPay_9289
  · exact WuPaper.ClassicalFourthNat.BPay_9290
  · exact WuPaper.ClassicalFourthNat.BPay_9291
  · exact WuPaper.ClassicalFourthNat.BPay_9292
  · exact WuPaper.ClassicalFourthNat.BPay_9293
  · exact WuPaper.ClassicalFourthNat.BPay_9294
  · exact WuPaper.ClassicalFourthNat.BPay_9295
  · exact WuPaper.ClassicalFourthNat.BPay_9296
  · exact WuPaper.ClassicalFourthNat.BPay_9297
  · exact WuPaper.ClassicalFourthNat.BPay_9298
  · exact WuPaper.ClassicalFourthNat.BPay_9299
  · exact WuPaper.ClassicalFourthNat.BPay_9300
  · exact WuPaper.ClassicalFourthNat.BPay_9301
  · exact WuPaper.ClassicalFourthNat.BPay_9302
  · exact WuPaper.ClassicalFourthNat.BPay_9303
  · exact WuPaper.ClassicalFourthNat.BPay_9304
  · exact WuPaper.ClassicalFourthNat.BPay_9305
  · exact WuPaper.ClassicalFourthNat.BPay_9306
  · exact WuPaper.ClassicalFourthNat.BPay_9307
  · exact WuPaper.ClassicalFourthNat.BPay_9308
  · exact WuPaper.ClassicalFourthNat.BPay_9309
  · exact WuPaper.ClassicalFourthNat.BPay_9310
  · exact WuPaper.ClassicalFourthNat.BPay_9311
  · exact WuPaper.ClassicalFourthNat.BPay_9312
  · exact WuPaper.ClassicalFourthNat.BPay_9313
  · exact WuPaper.ClassicalFourthNat.BPay_9314
  · exact WuPaper.ClassicalFourthNat.BPay_9315
  · exact WuPaper.ClassicalFourthNat.BPay_9316
  · exact WuPaper.ClassicalFourthNat.BPay_9317
  · exact WuPaper.ClassicalFourthNat.BPay_9318
  · exact WuPaper.ClassicalFourthNat.BPay_9319
  · exact WuPaper.ClassicalFourthNat.BPay_9320
  · exact WuPaper.ClassicalFourthNat.BPay_9321
  · exact WuPaper.ClassicalFourthNat.BPay_9322
  · exact WuPaper.ClassicalFourthNat.BPay_9323
  · exact WuPaper.ClassicalFourthNat.BPay_9324
  · exact WuPaper.ClassicalFourthNat.BPay_9325
  · exact WuPaper.ClassicalFourthNat.BPay_9326
  · exact WuPaper.ClassicalFourthNat.BPay_9327
  · exact WuPaper.ClassicalFourthNat.BPay_9328
  · exact WuPaper.ClassicalFourthNat.BPay_9329
  · exact WuPaper.ClassicalFourthNat.BPay_9330
  · exact WuPaper.ClassicalFourthNat.BPay_9331
  · exact WuPaper.ClassicalFourthNat.BPay_9332
  · exact WuPaper.ClassicalFourthNat.BPay_9333
  · exact WuPaper.ClassicalFourthNat.BPay_9334
  · exact WuPaper.ClassicalFourthNat.BPay_9335
  · exact WuPaper.ClassicalFourthNat.BPay_9336
  · exact WuPaper.ClassicalFourthNat.BPay_9337
  · exact WuPaper.ClassicalFourthNat.BPay_9338
  · exact WuPaper.ClassicalFourthNat.BPay_9339
  · exact WuPaper.ClassicalFourthNat.BPay_9340
  · exact WuPaper.ClassicalFourthNat.BPay_9341
  · exact WuPaper.ClassicalFourthNat.BPay_9342
  · exact WuPaper.ClassicalFourthNat.BPay_9343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_145

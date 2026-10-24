import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay083
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_083 (j : Fin 64) (hj : 64*83+j.val < 10540) :
    BPay (64*83+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5312
  · exact WuPaper.ClassicalFourthNat.BPay_5313
  · exact WuPaper.ClassicalFourthNat.BPay_5314
  · exact WuPaper.ClassicalFourthNat.BPay_5315
  · exact WuPaper.ClassicalFourthNat.BPay_5316
  · exact WuPaper.ClassicalFourthNat.BPay_5317
  · exact WuPaper.ClassicalFourthNat.BPay_5318
  · exact WuPaper.ClassicalFourthNat.BPay_5319
  · exact WuPaper.ClassicalFourthNat.BPay_5320
  · exact WuPaper.ClassicalFourthNat.BPay_5321
  · exact WuPaper.ClassicalFourthNat.BPay_5322
  · exact WuPaper.ClassicalFourthNat.BPay_5323
  · exact WuPaper.ClassicalFourthNat.BPay_5324
  · exact WuPaper.ClassicalFourthNat.BPay_5325
  · exact WuPaper.ClassicalFourthNat.BPay_5326
  · exact WuPaper.ClassicalFourthNat.BPay_5327
  · exact WuPaper.ClassicalFourthNat.BPay_5328
  · exact WuPaper.ClassicalFourthNat.BPay_5329
  · exact WuPaper.ClassicalFourthNat.BPay_5330
  · exact WuPaper.ClassicalFourthNat.BPay_5331
  · exact WuPaper.ClassicalFourthNat.BPay_5332
  · exact WuPaper.ClassicalFourthNat.BPay_5333
  · exact WuPaper.ClassicalFourthNat.BPay_5334
  · exact WuPaper.ClassicalFourthNat.BPay_5335
  · exact WuPaper.ClassicalFourthNat.BPay_5336
  · exact WuPaper.ClassicalFourthNat.BPay_5337
  · exact WuPaper.ClassicalFourthNat.BPay_5338
  · exact WuPaper.ClassicalFourthNat.BPay_5339
  · exact WuPaper.ClassicalFourthNat.BPay_5340
  · exact WuPaper.ClassicalFourthNat.BPay_5341
  · exact WuPaper.ClassicalFourthNat.BPay_5342
  · exact WuPaper.ClassicalFourthNat.BPay_5343
  · exact WuPaper.ClassicalFourthNat.BPay_5344
  · exact WuPaper.ClassicalFourthNat.BPay_5345
  · exact WuPaper.ClassicalFourthNat.BPay_5346
  · exact WuPaper.ClassicalFourthNat.BPay_5347
  · exact WuPaper.ClassicalFourthNat.BPay_5348
  · exact WuPaper.ClassicalFourthNat.BPay_5349
  · exact WuPaper.ClassicalFourthNat.BPay_5350
  · exact WuPaper.ClassicalFourthNat.BPay_5351
  · exact WuPaper.ClassicalFourthNat.BPay_5352
  · exact WuPaper.ClassicalFourthNat.BPay_5353
  · exact WuPaper.ClassicalFourthNat.BPay_5354
  · exact WuPaper.ClassicalFourthNat.BPay_5355
  · exact WuPaper.ClassicalFourthNat.BPay_5356
  · exact WuPaper.ClassicalFourthNat.BPay_5357
  · exact WuPaper.ClassicalFourthNat.BPay_5358
  · exact WuPaper.ClassicalFourthNat.BPay_5359
  · exact WuPaper.ClassicalFourthNat.BPay_5360
  · exact WuPaper.ClassicalFourthNat.BPay_5361
  · exact WuPaper.ClassicalFourthNat.BPay_5362
  · exact WuPaper.ClassicalFourthNat.BPay_5363
  · exact WuPaper.ClassicalFourthNat.BPay_5364
  · exact WuPaper.ClassicalFourthNat.BPay_5365
  · exact WuPaper.ClassicalFourthNat.BPay_5366
  · exact WuPaper.ClassicalFourthNat.BPay_5367
  · exact WuPaper.ClassicalFourthNat.BPay_5368
  · exact WuPaper.ClassicalFourthNat.BPay_5369
  · exact WuPaper.ClassicalFourthNat.BPay_5370
  · exact WuPaper.ClassicalFourthNat.BPay_5371
  · exact WuPaper.ClassicalFourthNat.BPay_5372
  · exact WuPaper.ClassicalFourthNat.BPay_5373
  · exact WuPaper.ClassicalFourthNat.BPay_5374
  · exact WuPaper.ClassicalFourthNat.BPay_5375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_083

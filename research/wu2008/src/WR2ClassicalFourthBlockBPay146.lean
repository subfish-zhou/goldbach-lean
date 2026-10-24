import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay146
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_146 (j : Fin 64) (hj : 64*146+j.val < 10540) :
    BPay (64*146+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9344
  · exact WuPaper.ClassicalFourthNat.BPay_9345
  · exact WuPaper.ClassicalFourthNat.BPay_9346
  · exact WuPaper.ClassicalFourthNat.BPay_9347
  · exact WuPaper.ClassicalFourthNat.BPay_9348
  · exact WuPaper.ClassicalFourthNat.BPay_9349
  · exact WuPaper.ClassicalFourthNat.BPay_9350
  · exact WuPaper.ClassicalFourthNat.BPay_9351
  · exact WuPaper.ClassicalFourthNat.BPay_9352
  · exact WuPaper.ClassicalFourthNat.BPay_9353
  · exact WuPaper.ClassicalFourthNat.BPay_9354
  · exact WuPaper.ClassicalFourthNat.BPay_9355
  · exact WuPaper.ClassicalFourthNat.BPay_9356
  · exact WuPaper.ClassicalFourthNat.BPay_9357
  · exact WuPaper.ClassicalFourthNat.BPay_9358
  · exact WuPaper.ClassicalFourthNat.BPay_9359
  · exact WuPaper.ClassicalFourthNat.BPay_9360
  · exact WuPaper.ClassicalFourthNat.BPay_9361
  · exact WuPaper.ClassicalFourthNat.BPay_9362
  · exact WuPaper.ClassicalFourthNat.BPay_9363
  · exact WuPaper.ClassicalFourthNat.BPay_9364
  · exact WuPaper.ClassicalFourthNat.BPay_9365
  · exact WuPaper.ClassicalFourthNat.BPay_9366
  · exact WuPaper.ClassicalFourthNat.BPay_9367
  · exact WuPaper.ClassicalFourthNat.BPay_9368
  · exact WuPaper.ClassicalFourthNat.BPay_9369
  · exact WuPaper.ClassicalFourthNat.BPay_9370
  · exact WuPaper.ClassicalFourthNat.BPay_9371
  · exact WuPaper.ClassicalFourthNat.BPay_9372
  · exact WuPaper.ClassicalFourthNat.BPay_9373
  · exact WuPaper.ClassicalFourthNat.BPay_9374
  · exact WuPaper.ClassicalFourthNat.BPay_9375
  · exact WuPaper.ClassicalFourthNat.BPay_9376
  · exact WuPaper.ClassicalFourthNat.BPay_9377
  · exact WuPaper.ClassicalFourthNat.BPay_9378
  · exact WuPaper.ClassicalFourthNat.BPay_9379
  · exact WuPaper.ClassicalFourthNat.BPay_9380
  · exact WuPaper.ClassicalFourthNat.BPay_9381
  · exact WuPaper.ClassicalFourthNat.BPay_9382
  · exact WuPaper.ClassicalFourthNat.BPay_9383
  · exact WuPaper.ClassicalFourthNat.BPay_9384
  · exact WuPaper.ClassicalFourthNat.BPay_9385
  · exact WuPaper.ClassicalFourthNat.BPay_9386
  · exact WuPaper.ClassicalFourthNat.BPay_9387
  · exact WuPaper.ClassicalFourthNat.BPay_9388
  · exact WuPaper.ClassicalFourthNat.BPay_9389
  · exact WuPaper.ClassicalFourthNat.BPay_9390
  · exact WuPaper.ClassicalFourthNat.BPay_9391
  · exact WuPaper.ClassicalFourthNat.BPay_9392
  · exact WuPaper.ClassicalFourthNat.BPay_9393
  · exact WuPaper.ClassicalFourthNat.BPay_9394
  · exact WuPaper.ClassicalFourthNat.BPay_9395
  · exact WuPaper.ClassicalFourthNat.BPay_9396
  · exact WuPaper.ClassicalFourthNat.BPay_9397
  · exact WuPaper.ClassicalFourthNat.BPay_9398
  · exact WuPaper.ClassicalFourthNat.BPay_9399
  · exact WuPaper.ClassicalFourthNat.BPay_9400
  · exact WuPaper.ClassicalFourthNat.BPay_9401
  · exact WuPaper.ClassicalFourthNat.BPay_9402
  · exact WuPaper.ClassicalFourthNat.BPay_9403
  · exact WuPaper.ClassicalFourthNat.BPay_9404
  · exact WuPaper.ClassicalFourthNat.BPay_9405
  · exact WuPaper.ClassicalFourthNat.BPay_9406
  · exact WuPaper.ClassicalFourthNat.BPay_9407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_146

import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay068
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_068 (j : Fin 64) (hj : 64*68+j.val < 10540) :
    BPay (64*68+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4352
  · exact WuPaper.ClassicalFourthNat.BPay_4353
  · exact WuPaper.ClassicalFourthNat.BPay_4354
  · exact WuPaper.ClassicalFourthNat.BPay_4355
  · exact WuPaper.ClassicalFourthNat.BPay_4356
  · exact WuPaper.ClassicalFourthNat.BPay_4357
  · exact WuPaper.ClassicalFourthNat.BPay_4358
  · exact WuPaper.ClassicalFourthNat.BPay_4359
  · exact WuPaper.ClassicalFourthNat.BPay_4360
  · exact WuPaper.ClassicalFourthNat.BPay_4361
  · exact WuPaper.ClassicalFourthNat.BPay_4362
  · exact WuPaper.ClassicalFourthNat.BPay_4363
  · exact WuPaper.ClassicalFourthNat.BPay_4364
  · exact WuPaper.ClassicalFourthNat.BPay_4365
  · exact WuPaper.ClassicalFourthNat.BPay_4366
  · exact WuPaper.ClassicalFourthNat.BPay_4367
  · exact WuPaper.ClassicalFourthNat.BPay_4368
  · exact WuPaper.ClassicalFourthNat.BPay_4369
  · exact WuPaper.ClassicalFourthNat.BPay_4370
  · exact WuPaper.ClassicalFourthNat.BPay_4371
  · exact WuPaper.ClassicalFourthNat.BPay_4372
  · exact WuPaper.ClassicalFourthNat.BPay_4373
  · exact WuPaper.ClassicalFourthNat.BPay_4374
  · exact WuPaper.ClassicalFourthNat.BPay_4375
  · exact WuPaper.ClassicalFourthNat.BPay_4376
  · exact WuPaper.ClassicalFourthNat.BPay_4377
  · exact WuPaper.ClassicalFourthNat.BPay_4378
  · exact WuPaper.ClassicalFourthNat.BPay_4379
  · exact WuPaper.ClassicalFourthNat.BPay_4380
  · exact WuPaper.ClassicalFourthNat.BPay_4381
  · exact WuPaper.ClassicalFourthNat.BPay_4382
  · exact WuPaper.ClassicalFourthNat.BPay_4383
  · exact WuPaper.ClassicalFourthNat.BPay_4384
  · exact WuPaper.ClassicalFourthNat.BPay_4385
  · exact WuPaper.ClassicalFourthNat.BPay_4386
  · exact WuPaper.ClassicalFourthNat.BPay_4387
  · exact WuPaper.ClassicalFourthNat.BPay_4388
  · exact WuPaper.ClassicalFourthNat.BPay_4389
  · exact WuPaper.ClassicalFourthNat.BPay_4390
  · exact WuPaper.ClassicalFourthNat.BPay_4391
  · exact WuPaper.ClassicalFourthNat.BPay_4392
  · exact WuPaper.ClassicalFourthNat.BPay_4393
  · exact WuPaper.ClassicalFourthNat.BPay_4394
  · exact WuPaper.ClassicalFourthNat.BPay_4395
  · exact WuPaper.ClassicalFourthNat.BPay_4396
  · exact WuPaper.ClassicalFourthNat.BPay_4397
  · exact WuPaper.ClassicalFourthNat.BPay_4398
  · exact WuPaper.ClassicalFourthNat.BPay_4399
  · exact WuPaper.ClassicalFourthNat.BPay_4400
  · exact WuPaper.ClassicalFourthNat.BPay_4401
  · exact WuPaper.ClassicalFourthNat.BPay_4402
  · exact WuPaper.ClassicalFourthNat.BPay_4403
  · exact WuPaper.ClassicalFourthNat.BPay_4404
  · exact WuPaper.ClassicalFourthNat.BPay_4405
  · exact WuPaper.ClassicalFourthNat.BPay_4406
  · exact WuPaper.ClassicalFourthNat.BPay_4407
  · exact WuPaper.ClassicalFourthNat.BPay_4408
  · exact WuPaper.ClassicalFourthNat.BPay_4409
  · exact WuPaper.ClassicalFourthNat.BPay_4410
  · exact WuPaper.ClassicalFourthNat.BPay_4411
  · exact WuPaper.ClassicalFourthNat.BPay_4412
  · exact WuPaper.ClassicalFourthNat.BPay_4413
  · exact WuPaper.ClassicalFourthNat.BPay_4414
  · exact WuPaper.ClassicalFourthNat.BPay_4415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_068

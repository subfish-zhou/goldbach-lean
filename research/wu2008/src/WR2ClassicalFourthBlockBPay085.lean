import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay085
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_085 (j : Fin 64) (hj : 64*85+j.val < 10540) :
    BPay (64*85+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5440
  · exact WuPaper.ClassicalFourthNat.BPay_5441
  · exact WuPaper.ClassicalFourthNat.BPay_5442
  · exact WuPaper.ClassicalFourthNat.BPay_5443
  · exact WuPaper.ClassicalFourthNat.BPay_5444
  · exact WuPaper.ClassicalFourthNat.BPay_5445
  · exact WuPaper.ClassicalFourthNat.BPay_5446
  · exact WuPaper.ClassicalFourthNat.BPay_5447
  · exact WuPaper.ClassicalFourthNat.BPay_5448
  · exact WuPaper.ClassicalFourthNat.BPay_5449
  · exact WuPaper.ClassicalFourthNat.BPay_5450
  · exact WuPaper.ClassicalFourthNat.BPay_5451
  · exact WuPaper.ClassicalFourthNat.BPay_5452
  · exact WuPaper.ClassicalFourthNat.BPay_5453
  · exact WuPaper.ClassicalFourthNat.BPay_5454
  · exact WuPaper.ClassicalFourthNat.BPay_5455
  · exact WuPaper.ClassicalFourthNat.BPay_5456
  · exact WuPaper.ClassicalFourthNat.BPay_5457
  · exact WuPaper.ClassicalFourthNat.BPay_5458
  · exact WuPaper.ClassicalFourthNat.BPay_5459
  · exact WuPaper.ClassicalFourthNat.BPay_5460
  · exact WuPaper.ClassicalFourthNat.BPay_5461
  · exact WuPaper.ClassicalFourthNat.BPay_5462
  · exact WuPaper.ClassicalFourthNat.BPay_5463
  · exact WuPaper.ClassicalFourthNat.BPay_5464
  · exact WuPaper.ClassicalFourthNat.BPay_5465
  · exact WuPaper.ClassicalFourthNat.BPay_5466
  · exact WuPaper.ClassicalFourthNat.BPay_5467
  · exact WuPaper.ClassicalFourthNat.BPay_5468
  · exact WuPaper.ClassicalFourthNat.BPay_5469
  · exact WuPaper.ClassicalFourthNat.BPay_5470
  · exact WuPaper.ClassicalFourthNat.BPay_5471
  · exact WuPaper.ClassicalFourthNat.BPay_5472
  · exact WuPaper.ClassicalFourthNat.BPay_5473
  · exact WuPaper.ClassicalFourthNat.BPay_5474
  · exact WuPaper.ClassicalFourthNat.BPay_5475
  · exact WuPaper.ClassicalFourthNat.BPay_5476
  · exact WuPaper.ClassicalFourthNat.BPay_5477
  · exact WuPaper.ClassicalFourthNat.BPay_5478
  · exact WuPaper.ClassicalFourthNat.BPay_5479
  · exact WuPaper.ClassicalFourthNat.BPay_5480
  · exact WuPaper.ClassicalFourthNat.BPay_5481
  · exact WuPaper.ClassicalFourthNat.BPay_5482
  · exact WuPaper.ClassicalFourthNat.BPay_5483
  · exact WuPaper.ClassicalFourthNat.BPay_5484
  · exact WuPaper.ClassicalFourthNat.BPay_5485
  · exact WuPaper.ClassicalFourthNat.BPay_5486
  · exact WuPaper.ClassicalFourthNat.BPay_5487
  · exact WuPaper.ClassicalFourthNat.BPay_5488
  · exact WuPaper.ClassicalFourthNat.BPay_5489
  · exact WuPaper.ClassicalFourthNat.BPay_5490
  · exact WuPaper.ClassicalFourthNat.BPay_5491
  · exact WuPaper.ClassicalFourthNat.BPay_5492
  · exact WuPaper.ClassicalFourthNat.BPay_5493
  · exact WuPaper.ClassicalFourthNat.BPay_5494
  · exact WuPaper.ClassicalFourthNat.BPay_5495
  · exact WuPaper.ClassicalFourthNat.BPay_5496
  · exact WuPaper.ClassicalFourthNat.BPay_5497
  · exact WuPaper.ClassicalFourthNat.BPay_5498
  · exact WuPaper.ClassicalFourthNat.BPay_5499
  · exact WuPaper.ClassicalFourthNat.BPay_5500
  · exact WuPaper.ClassicalFourthNat.BPay_5501
  · exact WuPaper.ClassicalFourthNat.BPay_5502
  · exact WuPaper.ClassicalFourthNat.BPay_5503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_085

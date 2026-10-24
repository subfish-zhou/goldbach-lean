import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay132
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_132 (j : Fin 64) (hj : 64*132+j.val < 10540) :
    BPay (64*132+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8448
  · exact WuPaper.ClassicalFourthNat.BPay_8449
  · exact WuPaper.ClassicalFourthNat.BPay_8450
  · exact WuPaper.ClassicalFourthNat.BPay_8451
  · exact WuPaper.ClassicalFourthNat.BPay_8452
  · exact WuPaper.ClassicalFourthNat.BPay_8453
  · exact WuPaper.ClassicalFourthNat.BPay_8454
  · exact WuPaper.ClassicalFourthNat.BPay_8455
  · exact WuPaper.ClassicalFourthNat.BPay_8456
  · exact WuPaper.ClassicalFourthNat.BPay_8457
  · exact WuPaper.ClassicalFourthNat.BPay_8458
  · exact WuPaper.ClassicalFourthNat.BPay_8459
  · exact WuPaper.ClassicalFourthNat.BPay_8460
  · exact WuPaper.ClassicalFourthNat.BPay_8461
  · exact WuPaper.ClassicalFourthNat.BPay_8462
  · exact WuPaper.ClassicalFourthNat.BPay_8463
  · exact WuPaper.ClassicalFourthNat.BPay_8464
  · exact WuPaper.ClassicalFourthNat.BPay_8465
  · exact WuPaper.ClassicalFourthNat.BPay_8466
  · exact WuPaper.ClassicalFourthNat.BPay_8467
  · exact WuPaper.ClassicalFourthNat.BPay_8468
  · exact WuPaper.ClassicalFourthNat.BPay_8469
  · exact WuPaper.ClassicalFourthNat.BPay_8470
  · exact WuPaper.ClassicalFourthNat.BPay_8471
  · exact WuPaper.ClassicalFourthNat.BPay_8472
  · exact WuPaper.ClassicalFourthNat.BPay_8473
  · exact WuPaper.ClassicalFourthNat.BPay_8474
  · exact WuPaper.ClassicalFourthNat.BPay_8475
  · exact WuPaper.ClassicalFourthNat.BPay_8476
  · exact WuPaper.ClassicalFourthNat.BPay_8477
  · exact WuPaper.ClassicalFourthNat.BPay_8478
  · exact WuPaper.ClassicalFourthNat.BPay_8479
  · exact WuPaper.ClassicalFourthNat.BPay_8480
  · exact WuPaper.ClassicalFourthNat.BPay_8481
  · exact WuPaper.ClassicalFourthNat.BPay_8482
  · exact WuPaper.ClassicalFourthNat.BPay_8483
  · exact WuPaper.ClassicalFourthNat.BPay_8484
  · exact WuPaper.ClassicalFourthNat.BPay_8485
  · exact WuPaper.ClassicalFourthNat.BPay_8486
  · exact WuPaper.ClassicalFourthNat.BPay_8487
  · exact WuPaper.ClassicalFourthNat.BPay_8488
  · exact WuPaper.ClassicalFourthNat.BPay_8489
  · exact WuPaper.ClassicalFourthNat.BPay_8490
  · exact WuPaper.ClassicalFourthNat.BPay_8491
  · exact WuPaper.ClassicalFourthNat.BPay_8492
  · exact WuPaper.ClassicalFourthNat.BPay_8493
  · exact WuPaper.ClassicalFourthNat.BPay_8494
  · exact WuPaper.ClassicalFourthNat.BPay_8495
  · exact WuPaper.ClassicalFourthNat.BPay_8496
  · exact WuPaper.ClassicalFourthNat.BPay_8497
  · exact WuPaper.ClassicalFourthNat.BPay_8498
  · exact WuPaper.ClassicalFourthNat.BPay_8499
  · exact WuPaper.ClassicalFourthNat.BPay_8500
  · exact WuPaper.ClassicalFourthNat.BPay_8501
  · exact WuPaper.ClassicalFourthNat.BPay_8502
  · exact WuPaper.ClassicalFourthNat.BPay_8503
  · exact WuPaper.ClassicalFourthNat.BPay_8504
  · exact WuPaper.ClassicalFourthNat.BPay_8505
  · exact WuPaper.ClassicalFourthNat.BPay_8506
  · exact WuPaper.ClassicalFourthNat.BPay_8507
  · exact WuPaper.ClassicalFourthNat.BPay_8508
  · exact WuPaper.ClassicalFourthNat.BPay_8509
  · exact WuPaper.ClassicalFourthNat.BPay_8510
  · exact WuPaper.ClassicalFourthNat.BPay_8511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_132

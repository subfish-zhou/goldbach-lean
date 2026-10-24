import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay132
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_132 (j : Fin 64) (hj : 64*132+j.val < 10540) :
    OuterPay (64*132+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8448
  · exact WuPaper.ClassicalFourthNat.outerPay_8449
  · exact WuPaper.ClassicalFourthNat.outerPay_8450
  · exact WuPaper.ClassicalFourthNat.outerPay_8451
  · exact WuPaper.ClassicalFourthNat.outerPay_8452
  · exact WuPaper.ClassicalFourthNat.outerPay_8453
  · exact WuPaper.ClassicalFourthNat.outerPay_8454
  · exact WuPaper.ClassicalFourthNat.outerPay_8455
  · exact WuPaper.ClassicalFourthNat.outerPay_8456
  · exact WuPaper.ClassicalFourthNat.outerPay_8457
  · exact WuPaper.ClassicalFourthNat.outerPay_8458
  · exact WuPaper.ClassicalFourthNat.outerPay_8459
  · exact WuPaper.ClassicalFourthNat.outerPay_8460
  · exact WuPaper.ClassicalFourthNat.outerPay_8461
  · exact WuPaper.ClassicalFourthNat.outerPay_8462
  · exact WuPaper.ClassicalFourthNat.outerPay_8463
  · exact WuPaper.ClassicalFourthNat.outerPay_8464
  · exact WuPaper.ClassicalFourthNat.outerPay_8465
  · exact WuPaper.ClassicalFourthNat.outerPay_8466
  · exact WuPaper.ClassicalFourthNat.outerPay_8467
  · exact WuPaper.ClassicalFourthNat.outerPay_8468
  · exact WuPaper.ClassicalFourthNat.outerPay_8469
  · exact WuPaper.ClassicalFourthNat.outerPay_8470
  · exact WuPaper.ClassicalFourthNat.outerPay_8471
  · exact WuPaper.ClassicalFourthNat.outerPay_8472
  · exact WuPaper.ClassicalFourthNat.outerPay_8473
  · exact WuPaper.ClassicalFourthNat.outerPay_8474
  · exact WuPaper.ClassicalFourthNat.outerPay_8475
  · exact WuPaper.ClassicalFourthNat.outerPay_8476
  · exact WuPaper.ClassicalFourthNat.outerPay_8477
  · exact WuPaper.ClassicalFourthNat.outerPay_8478
  · exact WuPaper.ClassicalFourthNat.outerPay_8479
  · exact WuPaper.ClassicalFourthNat.outerPay_8480
  · exact WuPaper.ClassicalFourthNat.outerPay_8481
  · exact WuPaper.ClassicalFourthNat.outerPay_8482
  · exact WuPaper.ClassicalFourthNat.outerPay_8483
  · exact WuPaper.ClassicalFourthNat.outerPay_8484
  · exact WuPaper.ClassicalFourthNat.outerPay_8485
  · exact WuPaper.ClassicalFourthNat.outerPay_8486
  · exact WuPaper.ClassicalFourthNat.outerPay_8487
  · exact WuPaper.ClassicalFourthNat.outerPay_8488
  · exact WuPaper.ClassicalFourthNat.outerPay_8489
  · exact WuPaper.ClassicalFourthNat.outerPay_8490
  · exact WuPaper.ClassicalFourthNat.outerPay_8491
  · exact WuPaper.ClassicalFourthNat.outerPay_8492
  · exact WuPaper.ClassicalFourthNat.outerPay_8493
  · exact WuPaper.ClassicalFourthNat.outerPay_8494
  · exact WuPaper.ClassicalFourthNat.outerPay_8495
  · exact WuPaper.ClassicalFourthNat.outerPay_8496
  · exact WuPaper.ClassicalFourthNat.outerPay_8497
  · exact WuPaper.ClassicalFourthNat.outerPay_8498
  · exact WuPaper.ClassicalFourthNat.outerPay_8499
  · exact WuPaper.ClassicalFourthNat.outerPay_8500
  · exact WuPaper.ClassicalFourthNat.outerPay_8501
  · exact WuPaper.ClassicalFourthNat.outerPay_8502
  · exact WuPaper.ClassicalFourthNat.outerPay_8503
  · exact WuPaper.ClassicalFourthNat.outerPay_8504
  · exact WuPaper.ClassicalFourthNat.outerPay_8505
  · exact WuPaper.ClassicalFourthNat.outerPay_8506
  · exact WuPaper.ClassicalFourthNat.outerPay_8507
  · exact WuPaper.ClassicalFourthNat.outerPay_8508
  · exact WuPaper.ClassicalFourthNat.outerPay_8509
  · exact WuPaper.ClassicalFourthNat.outerPay_8510
  · exact WuPaper.ClassicalFourthNat.outerPay_8511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_132

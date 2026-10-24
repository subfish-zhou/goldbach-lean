import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint132
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_132 (j : Fin 64) (hj : 64*132+j.val < 10541) :
    OuterPoint (64*132+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8448
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8449
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8450
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8451
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8452
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8453
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8454
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8455
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8456
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8457
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8458
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8459
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8460
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8461
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8462
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8463
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8464
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8465
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8466
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8467
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8468
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8469
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8470
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8471
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8472
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8473
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8474
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8475
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8476
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8477
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8478
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8479
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8480
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8481
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8482
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8483
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8484
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8485
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8486
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8487
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8488
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8489
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8490
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8491
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8492
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8493
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8494
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8495
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8496
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8497
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8498
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8499
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8500
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8501
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8502
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8503
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8504
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8505
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8506
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8507
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8508
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8509
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8510
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_132

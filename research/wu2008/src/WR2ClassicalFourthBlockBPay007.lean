import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_007 (j : Fin 64) (hj : 64*7+j.val < 10540) :
    BPay (64*7+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_448
  · exact WuPaper.ClassicalFourthNat.BPay_449
  · exact WuPaper.ClassicalFourthNat.BPay_450
  · exact WuPaper.ClassicalFourthNat.BPay_451
  · exact WuPaper.ClassicalFourthNat.BPay_452
  · exact WuPaper.ClassicalFourthNat.BPay_453
  · exact WuPaper.ClassicalFourthNat.BPay_454
  · exact WuPaper.ClassicalFourthNat.BPay_455
  · exact WuPaper.ClassicalFourthNat.BPay_456
  · exact WuPaper.ClassicalFourthNat.BPay_457
  · exact WuPaper.ClassicalFourthNat.BPay_458
  · exact WuPaper.ClassicalFourthNat.BPay_459
  · exact WuPaper.ClassicalFourthNat.BPay_460
  · exact WuPaper.ClassicalFourthNat.BPay_461
  · exact WuPaper.ClassicalFourthNat.BPay_462
  · exact WuPaper.ClassicalFourthNat.BPay_463
  · exact WuPaper.ClassicalFourthNat.BPay_464
  · exact WuPaper.ClassicalFourthNat.BPay_465
  · exact WuPaper.ClassicalFourthNat.BPay_466
  · exact WuPaper.ClassicalFourthNat.BPay_467
  · exact WuPaper.ClassicalFourthNat.BPay_468
  · exact WuPaper.ClassicalFourthNat.BPay_469
  · exact WuPaper.ClassicalFourthNat.BPay_470
  · exact WuPaper.ClassicalFourthNat.BPay_471
  · exact WuPaper.ClassicalFourthNat.BPay_472
  · exact WuPaper.ClassicalFourthNat.BPay_473
  · exact WuPaper.ClassicalFourthNat.BPay_474
  · exact WuPaper.ClassicalFourthNat.BPay_475
  · exact WuPaper.ClassicalFourthNat.BPay_476
  · exact WuPaper.ClassicalFourthNat.BPay_477
  · exact WuPaper.ClassicalFourthNat.BPay_478
  · exact WuPaper.ClassicalFourthNat.BPay_479
  · exact WuPaper.ClassicalFourthNat.BPay_480
  · exact WuPaper.ClassicalFourthNat.BPay_481
  · exact WuPaper.ClassicalFourthNat.BPay_482
  · exact WuPaper.ClassicalFourthNat.BPay_483
  · exact WuPaper.ClassicalFourthNat.BPay_484
  · exact WuPaper.ClassicalFourthNat.BPay_485
  · exact WuPaper.ClassicalFourthNat.BPay_486
  · exact WuPaper.ClassicalFourthNat.BPay_487
  · exact WuPaper.ClassicalFourthNat.BPay_488
  · exact WuPaper.ClassicalFourthNat.BPay_489
  · exact WuPaper.ClassicalFourthNat.BPay_490
  · exact WuPaper.ClassicalFourthNat.BPay_491
  · exact WuPaper.ClassicalFourthNat.BPay_492
  · exact WuPaper.ClassicalFourthNat.BPay_493
  · exact WuPaper.ClassicalFourthNat.BPay_494
  · exact WuPaper.ClassicalFourthNat.BPay_495
  · exact WuPaper.ClassicalFourthNat.BPay_496
  · exact WuPaper.ClassicalFourthNat.BPay_497
  · exact WuPaper.ClassicalFourthNat.BPay_498
  · exact WuPaper.ClassicalFourthNat.BPay_499
  · exact WuPaper.ClassicalFourthNat.BPay_500
  · exact WuPaper.ClassicalFourthNat.BPay_501
  · exact WuPaper.ClassicalFourthNat.BPay_502
  · exact WuPaper.ClassicalFourthNat.BPay_503
  · exact WuPaper.ClassicalFourthNat.BPay_504
  · exact WuPaper.ClassicalFourthNat.BPay_505
  · exact WuPaper.ClassicalFourthNat.BPay_506
  · exact WuPaper.ClassicalFourthNat.BPay_507
  · exact WuPaper.ClassicalFourthNat.BPay_508
  · exact WuPaper.ClassicalFourthNat.BPay_509
  · exact WuPaper.ClassicalFourthNat.BPay_510
  · exact WuPaper.ClassicalFourthNat.BPay_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_007

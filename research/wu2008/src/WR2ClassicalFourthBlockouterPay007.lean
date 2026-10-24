import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_007 (j : Fin 64) (hj : 64*7+j.val < 10540) :
    OuterPay (64*7+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_448
  · exact WuPaper.ClassicalFourthNat.outerPay_449
  · exact WuPaper.ClassicalFourthNat.outerPay_450
  · exact WuPaper.ClassicalFourthNat.outerPay_451
  · exact WuPaper.ClassicalFourthNat.outerPay_452
  · exact WuPaper.ClassicalFourthNat.outerPay_453
  · exact WuPaper.ClassicalFourthNat.outerPay_454
  · exact WuPaper.ClassicalFourthNat.outerPay_455
  · exact WuPaper.ClassicalFourthNat.outerPay_456
  · exact WuPaper.ClassicalFourthNat.outerPay_457
  · exact WuPaper.ClassicalFourthNat.outerPay_458
  · exact WuPaper.ClassicalFourthNat.outerPay_459
  · exact WuPaper.ClassicalFourthNat.outerPay_460
  · exact WuPaper.ClassicalFourthNat.outerPay_461
  · exact WuPaper.ClassicalFourthNat.outerPay_462
  · exact WuPaper.ClassicalFourthNat.outerPay_463
  · exact WuPaper.ClassicalFourthNat.outerPay_464
  · exact WuPaper.ClassicalFourthNat.outerPay_465
  · exact WuPaper.ClassicalFourthNat.outerPay_466
  · exact WuPaper.ClassicalFourthNat.outerPay_467
  · exact WuPaper.ClassicalFourthNat.outerPay_468
  · exact WuPaper.ClassicalFourthNat.outerPay_469
  · exact WuPaper.ClassicalFourthNat.outerPay_470
  · exact WuPaper.ClassicalFourthNat.outerPay_471
  · exact WuPaper.ClassicalFourthNat.outerPay_472
  · exact WuPaper.ClassicalFourthNat.outerPay_473
  · exact WuPaper.ClassicalFourthNat.outerPay_474
  · exact WuPaper.ClassicalFourthNat.outerPay_475
  · exact WuPaper.ClassicalFourthNat.outerPay_476
  · exact WuPaper.ClassicalFourthNat.outerPay_477
  · exact WuPaper.ClassicalFourthNat.outerPay_478
  · exact WuPaper.ClassicalFourthNat.outerPay_479
  · exact WuPaper.ClassicalFourthNat.outerPay_480
  · exact WuPaper.ClassicalFourthNat.outerPay_481
  · exact WuPaper.ClassicalFourthNat.outerPay_482
  · exact WuPaper.ClassicalFourthNat.outerPay_483
  · exact WuPaper.ClassicalFourthNat.outerPay_484
  · exact WuPaper.ClassicalFourthNat.outerPay_485
  · exact WuPaper.ClassicalFourthNat.outerPay_486
  · exact WuPaper.ClassicalFourthNat.outerPay_487
  · exact WuPaper.ClassicalFourthNat.outerPay_488
  · exact WuPaper.ClassicalFourthNat.outerPay_489
  · exact WuPaper.ClassicalFourthNat.outerPay_490
  · exact WuPaper.ClassicalFourthNat.outerPay_491
  · exact WuPaper.ClassicalFourthNat.outerPay_492
  · exact WuPaper.ClassicalFourthNat.outerPay_493
  · exact WuPaper.ClassicalFourthNat.outerPay_494
  · exact WuPaper.ClassicalFourthNat.outerPay_495
  · exact WuPaper.ClassicalFourthNat.outerPay_496
  · exact WuPaper.ClassicalFourthNat.outerPay_497
  · exact WuPaper.ClassicalFourthNat.outerPay_498
  · exact WuPaper.ClassicalFourthNat.outerPay_499
  · exact WuPaper.ClassicalFourthNat.outerPay_500
  · exact WuPaper.ClassicalFourthNat.outerPay_501
  · exact WuPaper.ClassicalFourthNat.outerPay_502
  · exact WuPaper.ClassicalFourthNat.outerPay_503
  · exact WuPaper.ClassicalFourthNat.outerPay_504
  · exact WuPaper.ClassicalFourthNat.outerPay_505
  · exact WuPaper.ClassicalFourthNat.outerPay_506
  · exact WuPaper.ClassicalFourthNat.outerPay_507
  · exact WuPaper.ClassicalFourthNat.outerPay_508
  · exact WuPaper.ClassicalFourthNat.outerPay_509
  · exact WuPaper.ClassicalFourthNat.outerPay_510
  · exact WuPaper.ClassicalFourthNat.outerPay_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_007
